(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Maps.
Require Import Compopts.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import ExprEval Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Lattice.
Require Import Kildall.
Require Import Registers.
Require Import Op.
Require Import RTL.
Require Import ValueDomain.
Require Import ValueAOp.
Require Import Liveness.

(** * The dataflow analysis *)

Definition areg (ae: aenv) (r: reg) : aval := AE.get r ae.

Definition aregs (ae: aenv) (rl: list reg) : list aval := List.map (areg ae) rl.

Definition mafter_public_call : amem := mtop.

Definition mafter_private_call (am_before: amem) : amem :=
  {| am_stack := am_before.(am_stack);
     am_glob := PTree.empty _;
     am_nonstack := Nonstack;
     am_top := eplub (ab_summary (am_stack am_before)) Nonstack |}.

Axiom trace_calls : bool -> unit.

Definition print (printer: bool -> unit) (b: bool) (v: VA.t') : VA.t' :=
  let unused := printer b in v.

Definition transfer_call (ae: aenv) (am: amem) (args: list reg) (res: reg) :=
  if epincl am.(am_nonstack) Nonstack
  && forallb (fun r => epincl (provenance (areg ae r)) Nonstack) args
  then
    print trace_calls true
          (VA.State (AE.set res (Ptr Nonstack) ae) (mafter_private_call am))
  else
    print trace_calls false 
          (VA.State (AE.set res Vtop ae) mafter_public_call).

Inductive builtin_kind : Type :=
  | Builtin_vload (chunk: memory_chunk) (aaddr: aval)
  | Builtin_vstore (chunk: memory_chunk) (aaddr av: aval)
  | Builtin_memcpy (sz al: Z) (adst asrc: aval)
  | Builtin_annot
  | Builtin_annot_val (av: aval)
  | Builtin_default
  (* | Builtin_ignored  *).


Definition classify_builtin (ef: external_function) (args: list reg) (ae: aenv) :=
  match ef, args with
  | EF_vload chunk, a1::nil => Builtin_vload chunk (areg ae a1)
  | EF_vload_global chunk id ofs, nil => Builtin_vload chunk (Ptr (Gl id ofs))
  | EF_vstore chunk, a1::a2::nil => Builtin_vstore chunk (areg ae a1) (areg ae a2)
  | EF_vstore_global chunk id ofs, a1::nil => Builtin_vstore chunk (Ptr (Gl id ofs)) (areg ae a1)
  | EF_memcpy sz al, a1::a2::nil => Builtin_memcpy sz al (areg ae a1) (areg ae a2)
  | EF_annot _ _, _ => Builtin_annot
  | EF_annot_val _ _, a1::nil => Builtin_annot_val (areg ae a1)
  | _, _ => Builtin_default
  end.

Definition transfer_builtin (ae: aenv) (am: amem) (rm: romem) (ef: external_function) (args: list reg) (res: reg) :=
  match classify_builtin ef args ae with
  | Builtin_vload chunk aaddr => 
      let a :=
        if va_strict tt
        then evlub (loadv chunk rm am aaddr) (vnormalize chunk (Ptr Glob))
        else vnormalize chunk Vtop in
      VA.State (AE.set res a ae) am
  | Builtin_vstore chunk aaddr av =>
      let am' := storev chunk am aaddr av in
      VA.State (AE.set res Vtop ae) (mlub am am')
  | Builtin_memcpy sz al adst asrc =>
    if zlt 0 sz
    then 
      let p := loadbytes am rm (aptr_of_aval asrc) in
      let am' := storebytes am (aptr_of_aval adst) sz p in
      VA.State (AE.set res Vtop ae) am'
    else VA.State (AE.set res Vtop ae) am
  | Builtin_annot =>
      VA.State (AE.set res Vtop ae) am
  | Builtin_annot_val av =>
      VA.State (AE.set res av ae) am
  | Builtin_default =>
      transfer_call ae am args res
  end.

Definition transfer (f: function)  (rm: romem) (pc: node) (ae: aenv) (am: amem) : VA.t :=
  match f.(fn_code)!pc with
  | None =>
      VA.Bot
  | Some(Inop s) =>
      VA.State ae am
  | Some(Iop op args res s) =>
      let a := eval_static_operation  op (aregs ae args) in
      VA.State (AE.set res a ae) am
  | Some(Iload chunk addr args dst s) =>
      let a := loadv chunk rm am (eval_static_addressing addr (aregs ae args)) in
      VA.State (AE.set dst a ae) am
  | Some(Istore chunk addr args src s) =>
      let am' := storev chunk am (eval_static_addressing addr (aregs ae args)) (areg ae src) in
      VA.State ae am'
  | Some(Icall sig ros args res s) =>
      transfer_call ae am args res
  | Some(Itailcall sig ros args) =>
      VA.Bot
  | Some(Ibuiltin ef args res s) =>
      transfer_builtin ae am rm ef args res
  | Some(Icond cond args s1 s2) =>
      VA.State ae am
  | Some(Ijumptable arg tbl) =>
      VA.State ae am
  | Some(Ireturn arg) =>
      VA.Bot
  end.

Definition transfer' (f: function) (lastuses: PTree.t (list reg))  (rm: romem)
                     (pc: node) (before: VA.t) : VA.t :=
  match before with
  | VA.Bot => VA.Bot
  | VA.State ae am =>
      match transfer f  rm pc ae am with
      | VA.Bot => VA.Bot
      | VA.State ae' am' =>
          let ae'' :=
            match lastuses!pc with
            | None => ae'
            | Some regs => eforget regs ae'
            end in
          VA.State ae'' am'
     end
  end.

Module DS := Dataflow_Solver(VA)(NodeSetForward).

Definition mfunction_entry :=
  {| am_stack := ablock_init Pcst; (* Undef *)
     am_glob := PTree.empty _;
     am_nonstack := Nonstack;
     am_top := Nonstack |}.

Definition set_print (v: unit -> VA.t) (p: PMap.t VA.t) :=
  let _ := v tt in p.

Definition analyze  (rm: romem) (f: function): PMap.t VA.t :=
  let lu := Liveness.last_uses f in
  let entry := VA.State (einit_regs f.(fn_params)) mfunction_entry in
  match DS.fixpoint f.(fn_code) successors_instr (transfer' f lu  rm)
                    f.(fn_entrypoint) entry with
  | None => PMap.init (VA.State AE.top mtop)
  | Some res =>
    set_print (fun (_: unit) => PTree.fold (fun (acc: VA.t) (pc: positive) (va: VA.t) =>
                                           (transfer' f lu rm pc va))
                                        (snd res) VA.Bot) res
  end.

(** Constructing the approximation of read-only globals *)

Definition store_init_data (ab: ablock) (p: Z) (id: init_data) : ablock :=
  match id with
  | Init_int8 n => ablock_store Mint8unsigned ab p (I n)
  | Init_int16 n => ablock_store Mint16unsigned ab p (I n)
  | Init_int32 n => ablock_store Mint32 ab p (I n)
  | Init_int64 n => ablock_store Mint64 ab p (L n)
  | Init_float32 n => ablock_store Mfloat32 ab p  (FS n)
  | Init_float64 n => ablock_store Mfloat64 ab p (F n)
  | Init_addrof symb ofs => ablock_store Mint32 ab p (Ptr (Gl symb ofs))
  | Init_space n _ => ab
  end.

Fixpoint store_init_data_list (ab: ablock) (p: Z) (idl: list init_data)
                              {struct idl}: ablock :=
  match idl with
  | nil => ab
  | id :: idl' => store_init_data_list (store_init_data ab p id) (p + Genv.init_data_size id) idl'
  end.

Definition alloc_global (rm: romem) (idg: ident * globdef fundef unit): romem :=
  match idg with
  | (id, Gfun f) => 
      PTree.remove id rm
  | (id, Gvar v) =>
      if v.(gvar_readonly) && negb v.(gvar_volatile)
      then PTree.set id (store_init_data_list (ablock_init Pcst) 0 v.(gvar_init)) rm
      else PTree.remove id rm
  end.

Definition romem_for_program (p: program) : romem :=
  List.fold_left alloc_global p.(prog_defs) (PTree.empty _).

(** * Soundness proof *)

(** Properties of the dataflow solution. *)

Lemma analyze_entrypoint:
  forall rm  f vl m bc 
  ,
    (forall v, In v vl -> evmatch bc  v (Ptr Nonstack)) ->
  mmatch bc m mfunction_entry ->
  exists ae am,
     (analyze rm f)!!(fn_entrypoint f) = VA.State ae am
  /\ ematch bc  (init_regs vl (fn_params f)) ae
  /\ mmatch bc m am.
Proof.
  intros. 
  unfold analyze. 
  set (lu := Liveness.last_uses f).
  set (entry := VA.State (einit_regs f.(fn_params)) mfunction_entry).
  destruct (DS.fixpoint (fn_code f) successors_instr (transfer' f lu rm )
                        (fn_entrypoint f) entry) as [res|] eqn:FIX.
- assert (A: VA.ge res!!(fn_entrypoint f) entry) by (eapply DS.fixpoint_entry; eauto).
  unfold set_print.
  destruct (res!!(fn_entrypoint f)) as [ | ae am ]; simpl in A. contradiction.
  destruct A as [A1 A2]. 
  exists ae, am. 
  split. auto. 
  split. eapply ematch_ge; eauto. apply ematch_init; auto. 
  auto.
- exists AE.top, mtop.
  split. apply PMap.gi. 
  split. apply ematch_ge with (einit_regs (fn_params f)). 
  apply ematch_init; auto. apply AE.ge_top. 
  eapply mmatch_top'; eauto. 
Qed.
  
Lemma analyze_successor:
  forall f  n ae am instr s rm ae' am',
  (analyze  rm f)!!n = VA.State ae am ->
  f.(fn_code)!n = Some instr ->
  In s (successors_instr instr) ->
  transfer f  rm n ae am = VA.State ae' am' ->
  VA.ge (analyze  rm f)!!s (transfer f  rm n ae am).
Proof.
  unfold analyze; intros.
  set (lu := Liveness.last_uses f) in *.
  set (entry := VA.State (einit_regs f.(fn_params)) mfunction_entry) in *.
  destruct (DS.fixpoint (fn_code f) successors_instr (transfer' f lu  rm)
                        (fn_entrypoint f) entry) as [res|] eqn:FIX.
- assert (A: VA.ge res!!s (transfer' f lu  rm n res#n)).
  { eapply DS.fixpoint_solution; eauto with coqlib.
    intros. unfold transfer'. simpl. auto. }
  unfold set_print in *.
  rewrite H in A. unfold transfer' in A. rewrite H2 in A. rewrite H2.  
  destruct lu!n.
  eapply VA.ge_trans. eauto. split; auto. apply eforget_ge. 
  auto.
- rewrite H2. rewrite PMap.gi. split; intros. apply AE.ge_top. eapply mmatch_top'; eauto.
Qed.

Lemma analyze_succ:
  forall e   m rm f n ae am instr s ae' am' bc
  ,
  (analyze  rm f)!!n = VA.State ae am ->
  f.(fn_code)!n = Some instr ->
  In s (successors_instr instr) ->
  transfer f rm n ae am = VA.State ae' am' ->
  ematch bc  e ae' ->
  mmatch bc m am' ->
  exists ae'' am'',
     (analyze  rm f)!!s = VA.State ae'' am''
  /\ ematch bc  e ae''
  /\ mmatch bc m am''.
Proof.
  intros. exploit analyze_successor; eauto. rewrite H2. 
  destruct (analyze  rm f)#s as [ | ae'' am'']; simpl; try tauto. intros [A B].
  exists ae'', am''.
  split. auto. 
  split. eapply ematch_ge; eauto. eauto. 
Qed.

(** Classification of builtin functions *)

Lemma classify_builtin_sound:
  forall bc e ae ef (ge: genv) args m t res m',
  ematch bc e ae ->
  genv_match bc ge ->
  external_call ef ge e##args m t res m' ->
  match classify_builtin ef args ae with
  | Builtin_vload chunk aaddr =>
      exists addr,
      volatile_load_sem chunk ge (addr::nil) m t res m' /\ evmatch bc addr aaddr
  | Builtin_vstore chunk aaddr av =>
      exists addr v,
      volatile_store_sem chunk ge (addr::v::nil) m t res m'
      /\ evmatch bc addr aaddr /\ evmatch bc v av
  | Builtin_memcpy sz al adst asrc =>
      exists dst, exists src,
      extcall_memcpy_sem sz al ge (dst::src::nil) m t res m'
      /\ evmatch bc dst adst /\ evmatch bc src asrc
  | Builtin_annot => m' = m /\ is_constant Vundef res
  | Builtin_annot_val av => m' = m /\ evmatch bc res av
  | Builtin_default => True
  end.
Proof.
  intros. unfold classify_builtin; destruct ef; auto.
  - (* vload *)
    destruct args; auto. destruct args; auto.
    exists (e#p); split; eauto.
  - (* vstore *)
    destruct args; auto. destruct args; auto. destruct args; auto.
    exists (e#p), (e#p0); eauto.
  - (* vload global *)
    destruct args; auto. simpl in H1. 
    rewrite volatile_load_global_charact in H1. destruct H1 as (b & A & B).
    exists (Values_symbolictype.Eval(Vptr b ofs)); split; auto.
    econstructor ; eauto. econstructor.  eapply H0; eauto. repeat intro ; reflexivity.
  - (* vstore global *)
    destruct args; auto. destruct args; auto. simpl in H1. 
    rewrite volatile_store_global_charact in H1. destruct H1 as (b & A & B).
    exists (Values_symbolictype.Eval(Vptr b ofs)), (e#p); split; auto. split; eauto.
    constructor. econstructor. eapply H0; eauto. repeat intro ; reflexivity.
  - (* memcpy *)
    destruct args; auto. destruct args; auto. destruct args; auto.
    exists (e#p), (e#p0); eauto.
  - (* annot *)
    simpl in H1. inv H1.  split. auto.
    red. reflexivity.
  - (* annot val *)
    destruct args; auto. destruct args; auto.
    simpl in H1. inv H1. split; eauto.
Qed.


(** ** Constructing block classifications *)

Definition bc_nostack (bc: block_classification) : Prop :=
  forall b, bc b <> BCstack.

Section NOSTACK.

Variable bc: block_classification.
Hypothesis NOSTACK: bc_nostack bc.

Lemma pmatch_no_stack: forall  e p,
    epmatch bc e p -> epmatch bc  e Nonstack.
Proof.
  intros. inv H; econstructor;
          try (eapply depends_on_blocks_le ; eauto; simpl ; intuition congruence).
  - unfold is_pointer in H1.
    rewrite <- depends_on_blocks_same_eval ; eauto.
    repeat intro ; simpl.
    rewrite H ; try reflexivity.
    intuition congruence.
  -
    eapply depends_on_blocks_le ; eauto; simpl.
    intros. simpl in H.
    destruct H ; intuition congruence.
    Grab Existential Variables. intro. exact True.
Qed.

Lemma vmatch_no_stack: forall v x ,
    evmatch bc v x ->
    evmatch bc v (Ptr Nonstack).
Proof.
  induction 1; constructor; auto ;
  try (eapply pmatch_no_stack; eauto; fail);
  try (unfold is_constant in H; 
        rewrite <- epmatch_same_eval ; eauto;
        constructor ; repeat intro ; reflexivity).
Qed.

Lemma smatch_no_stack: forall m b p, smatch bc m b p -> smatch bc m b Nonstack.
Proof.
  intros. destruct H as [A B]. split; intros.
  - reflexivity.
  - exploit B ; eauto.
    destruct mv ; simpl in *.
    eapply pmatch_no_stack; eauto. 
Qed.

Lemma mmatch_no_stack: forall m am astk,
  mmatch bc m am -> mmatch bc m {| am_stack := astk; am_glob := PTree.empty _; am_nonstack := Nonstack; am_top := Nonstack |}.
Proof.
  intros. destruct H. constructor; simpl; intros.
- elim (NOSTACK b); auto. 
- rewrite PTree.gempty in H0; discriminate.
- eapply smatch_no_stack; eauto. 
- eapply smatch_no_stack; eauto. 
- auto.
Qed.

End NOSTACK.

(** ** Construction 1: allocating the stack frame at function entry *)

Ltac splitall := repeat (match goal with |- _ /\ _ => split end).

Theorem allocate_stack:
  forall m sz m' sp bc ge rm am,
  Mem.alloc m 0 sz Normal = Some (m', sp) ->
  genv_match bc ge ->
  romatch bc m rm ->
  mmatch bc m am ->
  bc_nostack bc ->
  exists bc',
     bc_incr bc bc'
  /\ bc' sp = BCstack
  /\ genv_match bc' ge
  /\ romatch bc' m' rm
  /\ mmatch bc' m' mfunction_entry
  /\ (forall b, Plt b sp -> bc' b = bc b)
  /\ (forall v x, evmatch bc v x -> evmatch bc' v (Ptr Nonstack)).
Proof.
  intros until am; intros ALLOC GENV RO MM NOSTACK. 
  exploit Mem.nextblock_alloc; eauto. intros NB. 
  exploit Mem.alloc_result; eauto. intros SP.
  assert (SPINVALID: bc sp = BCinvalid).
  { rewrite SP. eapply bc_below_invalid. apply Plt_strict. eapply mmatch_below; eauto. }
(* Part 1: constructing bc' *)
  set (f := fun b => if eq_block b sp then BCstack else bc b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> b = sp).
    { unfold f; intros. destruct (eq_block b sp); auto. eelim NOSTACK; eauto. }
    intros. transitivity sp; auto. symmetry; auto. 
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> bc b = BCglob id).
    { unfold f; intros. destruct (eq_block b sp). congruence. auto. }
    intros. eapply (bc_glob bc); eauto. 
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.
  assert (BC'EQ: forall b, bc b <> BCinvalid -> bc' b = bc b).
  { intros; simpl. apply dec_eq_false. congruence. }
  assert (INCR: bc_incr bc bc').
  { red; simpl; intros. apply BC'EQ; auto. }
(* Part 2: invariance properties *)
  assert (SM: forall b p, bc b <> BCinvalid -> smatch bc m b p -> smatch bc' m' b Nonstack).
  {
    intros. 
    apply smatch_incr with bc; auto.
    apply smatch_inv with m. 
    apply smatch_no_stack with p; auto.
    intros. eapply Mem.loadbytes_alloc_unchanged; eauto. eapply mmatch_below; eauto. 
  }
  assert (SMSTACK: smatch bc' m' sp Pcst).
  {
    split; intros.
    simpl ; auto.
    
    (*    exploit Mem.load_alloc_same; eauto. intros EQ. subst v. constructor.*)
    exploit Mem.loadbytes_alloc_same; eauto with coqlib.
    intro; subst mv. (* intros [x [y EQ]]. subst mv.  *)
    simpl. constructor. repeat intro ; reflexivity.
  } 
(* Conclusions *)
  exists bc'; splitall.
- (* incr *)
  assumption.
- (* sp is BCstack *)
  simpl; apply dec_eq_true. 
- (* genv match *)
  eapply genv_match_exten; eauto.
  simpl; intros. destruct (eq_block b sp); intuition congruence.
  simpl; intros. destruct (eq_block b sp); congruence. 
- (* romatch *)
  apply romatch_exten with bc. 
  eapply romatch_alloc; eauto. eapply mmatch_below; eauto. 
  simpl; intros. destruct (eq_block b sp); intuition. 
- (* mmatch *)
  constructor; simpl; intros.
  + (* stack *)
    apply ablock_init_sound. destruct (eq_block b sp).
    subst b. apply SMSTACK.
    elim (NOSTACK b); auto.
  + (* globals *)
    rewrite PTree.gempty in H0; discriminate.
  + (* nonstack *)
    destruct (eq_block b sp). congruence. eapply SM; auto. eapply mmatch_nonstack; eauto.
  + (* top *)
    destruct (eq_block b sp).
    subst b. apply smatch_ge with Pcst. apply SMSTACK. constructor.  
    eapply SM; auto. eapply mmatch_top; eauto.
  + (* below *)
    red; simpl; intros. rewrite NB. destruct (eq_block b sp). 
    subst b; rewrite SP; xomega. 
    exploit mmatch_below; eauto. xomega. 
- (* unchanged *)
  simpl; intros. apply dec_eq_false. apply Plt_ne. auto.
- (* values *)
  intros. apply vmatch_incr with bc; auto. eapply vmatch_no_stack; eauto. 
Qed.

Theorem loadbytes_allocbytes_unchanged:
  forall m1 n m2 (AB: MemReserve.reserve_boxes m1 n = Some m2)
    b' ofs n0 
    (VB: Mem.valid_block m1 b'),
    Mem.loadbytes m2 b' ofs n0 = Mem.loadbytes m1 b' ofs n0.
Proof.
  unfold MemReserve.reserve_boxes. intros. destr_in AB; inv AB.
  reflexivity.
Qed.

Lemma romatch_allocbytes
     : forall (bc : block_classification) (m : mem) 
         (n : nat) (m' : mem) (rm : romem),
       MemReserve.reserve_boxes m n = Some m' ->
       bc_below bc (Mem.nextblock m) ->
       romatch bc m rm -> romatch bc m' rm.
Proof.
  red; intros.
  exploit H1; eauto.
  intros [A [B C]].
  repSplit; auto.
  inv B. constructor.
  inv BMS. constructor; auto.
  intros; eapply SMLD; eauto.
  rewrite <- H5. symmetry. eapply loadbytes_allocbytes_unchanged; eauto.
  red. apply H0. congruence.
  intros; eapply BML; eauto.
  eapply loadbytes_load_ext with (m':=m'); eauto.
  intros. rewrite <- H5. symmetry. eapply loadbytes_allocbytes_unchanged; eauto.
  red. apply H0. congruence.
  intros ofs PERM.
  unfold MemReserve.reserve_boxes in H; destr_in H. inv H. eapply C. apply PERM.
Qed.

Lemma match_allocbytes
     : forall (bc  : block_classification) (m : mem)
         (n : nat) (m' : mem) (am : amem)
         (AB: MemReserve.reserve_boxes m n = Some m')
         (MM: mmatch bc m am), mmatch bc m' am.
Proof.
  intros.
  inv MM; constructor; auto.
  -
    intros.
    exploit mmatch_stack; eauto. 
    intro A; inv A. constructor.
    inv BMS; constructor; auto.
    intros; eapply SMLD; eauto.
    rewrite <- H1. symmetry. eapply loadbytes_allocbytes_unchanged; eauto.
    red. apply mmatch_below. congruence.
    intros; eapply BML; eauto.
    eapply loadbytes_load_ext with (m':=m'); eauto.
    intros. rewrite <- H1. symmetry. eapply loadbytes_allocbytes_unchanged; eauto.
    red. apply mmatch_below. congruence.
  - intros.
    exploit mmatch_glob; eauto. 
    intro A; inv A. constructor.
    inv BMS; constructor; auto.
    intros; eapply SMLD; eauto.
    rewrite <- H2. symmetry. eapply loadbytes_allocbytes_unchanged; eauto.
    red. apply mmatch_below. congruence.
    intros; eapply BML; eauto.
    eapply loadbytes_load_ext with (m':=m'); eauto.
    intros. rewrite <- H2. symmetry. eapply loadbytes_allocbytes_unchanged; eauto.
    red. apply mmatch_below. congruence.
  - intros.
    exploit mmatch_nonstack; eauto. 
    intro A; inv A. constructor. auto.
    intros; eapply SMLD; eauto.
    rewrite <- H2. symmetry. eapply loadbytes_allocbytes_unchanged; eauto.
    red. apply mmatch_below. congruence.
  - intros.
    exploit mmatch_top; eauto.
    intro A; inv A.
    constructor; auto.
    intros; eapply SMLD;eauto.
    rewrite <- H1; symmetry; eapply loadbytes_allocbytes_unchanged; eauto.
    red. apply mmatch_below. congruence.
  - red. intros. exploit mmatch_below; eauto.
    rewrite (MemReserve.reserve_nextblock _ _ _ AB). xomega.
Qed.

Theorem allocate_stack':
  forall m n m' bc ge rm am,
  MemReserve.reserve_boxes m n = Some m' ->
  genv_match bc ge ->
  romatch bc m rm ->
  mmatch bc m am ->

  (* (* exists bc', *) *)
  (*    bc_incr bc bc' *)
  (* /\ Forall (fun b => bc' b = BCother) l *)
  (* /\ genv_match bc' ge *)
   romatch bc m' rm
  /\ mmatch bc m' am
  (* /\ (forall b, Plt b (Mem.nextblock m) -> bc' b = bc b) *)
  (* /\ (forall v x, evmatch bc v x -> evmatch bc' v x) *).
Proof.
  intros until am; intros ALLOC GENV RO MM .
  split.
  - eapply romatch_allocbytes; eauto.
    inv MM; auto.
  - eapply match_allocbytes; eauto.
Qed.


(** Construction 2: turn the stack into an "other" block, at public calls or function returns *)

Theorem anonymize_stack:
  forall m  sp bc ge rm am
  ,
  genv_match bc ge ->
  romatch bc m rm ->
  mmatch bc m am ->
  bc sp = BCstack ->
  exists bc',
     bc_nostack bc'
  /\ bc' sp = BCother
  /\ (forall b, b <> sp -> bc' b = bc b)
  /\ (forall v x, evmatch bc  v x -> evmatch bc' v Vtop)
  /\ genv_match bc' ge
  /\ romatch bc' m rm
  /\ mmatch bc' m mtop.
Proof.
  intros until am; intros  GENV RO MM SP.
(* Part 1: constructing bc' *)
  set (f := fun b => if eq_block b sp then BCother else bc b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    unfold f; intros.
    destruct (eq_block b1 sp); try discriminate.
    destruct (eq_block b2 sp); try discriminate. 
    eapply bc_stack; eauto. 
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    unfold f; intros.
    destruct (eq_block b1 sp); try discriminate.
    destruct (eq_block b2 sp); try discriminate. 
    eapply bc_glob; eauto. 
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.

(* Part 2: matching wrt bc' *)
  assert (PM: forall e p, epmatch bc  e p -> epmatch bc' e Ptop).
  {
    intros. assert (epmatch bc  e Ptop) by (eapply epmatch_top'; eauto).
    inv H0. constructor; simpl. eapply depends_on_blocks_le ; eauto.
    repeat intro.
    destruct (eq_block b sp); congruence. 
  }
  assert (VM: forall v x, evmatch bc  v x -> evmatch bc'  v Vtop).
  {
    induction 1; constructor; eauto.
    - 
    unfold is_constant in H.
    rewrite <- epmatch_same_eval ; eauto.
    constructor. repeat intro ; reflexivity.
    -     unfold is_constant in H.
    rewrite <- epmatch_same_eval ; eauto.
    constructor. repeat intro ; reflexivity.
    -     unfold is_constant in H.
    rewrite <- epmatch_same_eval ; eauto.
    constructor. repeat intro ; reflexivity.
    -     unfold is_constant in H.
    rewrite <- epmatch_same_eval ; eauto.
    constructor. repeat intro ; reflexivity.
  }
  assert (SM: forall b p, smatch bc m b p -> smatch bc' m b Ptop).
  {
    intros. destruct H as [S1 S2]. split; intros.
    reflexivity.
    exploit S2 ; eauto.
    destruct mv; simpl ; eauto.
  }
(* Conclusions *)
  exists bc'; splitall.
- (* nostack *)
  red; simpl; intros. destruct (eq_block b sp). congruence. 
  red; intros. elim n. eapply bc_stack; eauto. 
- (* bc' sp is BCother *)
  simpl; apply dec_eq_true. 
- (* other blocks *)
  intros; simpl; apply dec_eq_false; auto. 
- (* values *)
  auto.
- (* genv *)
  apply genv_match_exten with bc; auto. 
  simpl; intros. destruct (eq_block b sp); intuition congruence.
  simpl; intros. destruct (eq_block b sp); auto.
- (* romatch *)
  apply romatch_exten with bc; auto. 
  simpl; intros. destruct (eq_block b sp); intuition. 
- (* mmatch top *)
  constructor; simpl; intros. 
  + destruct (eq_block b sp). congruence. elim n. eapply bc_stack; eauto.
  + rewrite PTree.gempty in H0; discriminate.
  + destruct (eq_block b sp).
    subst b. eapply SM. eapply mmatch_stack; eauto.
    eapply SM. eapply mmatch_nonstack; eauto. 
  + destruct (eq_block b sp).
    subst b. eapply SM. eapply mmatch_stack; eauto.
    eapply SM. eapply mmatch_top; eauto.
  + red; simpl; intros. destruct (eq_block b sp). 
    subst b. eapply mmatch_below; eauto. congruence.
    eapply mmatch_below; eauto.
Qed.

(** Construction 3: turn the stack into an invalid block, at private calls *)

Theorem hide_stack:
  forall m sp bc ge rm am
  ,
  genv_match bc ge ->
  romatch bc m rm ->
  mmatch bc m am ->
  bc sp = BCstack ->
  epge Nonstack am.(am_nonstack) ->
  exists bc',
     bc_nostack bc'
  /\ bc' sp = BCinvalid
  /\ (forall b, b <> sp -> bc' b = bc b)
  /\ (forall v x, evge (Ptr Nonstack) x -> evmatch bc  v x -> evmatch bc'  v Vtop)
  /\ genv_match bc' ge
  /\ romatch bc' m rm
  /\ mmatch bc' m mtop.
Proof.
  intros until am; intros GENV RO MM SP NOLEAK.
(* Part 1: constructing bc' *)
  set (f := fun b => if eq_block b sp then BCinvalid else bc b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    unfold f; intros.
    destruct (eq_block b1 sp); try discriminate.
    destruct (eq_block b2 sp); try discriminate. 
    eapply bc_stack; eauto. 
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    unfold f; intros.
    destruct (eq_block b1 sp); try discriminate.
    destruct (eq_block b2 sp); try discriminate. 
    eapply bc_glob; eauto. 
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.

(* Part 2: matching wrt bc' *)
  assert (PM: forall e p, epge Nonstack p -> epmatch bc  e p -> epmatch bc'  e Ptop).
  {
    intros.
    assert (epmatch bc  e Nonstack) by (eapply epmatch_ge; eauto).
    inv H1.
    constructor.
    eapply depends_on_blocks_le ; eauto.
    repeat intro.
    simpl in H1.
    unfold bc' in H3.
    simpl in H3.
    destruct (eq_block b sp);
    intuition try congruence.
  }
  assert (VM: forall v x, evge (Ptr Nonstack) x ->
                          evmatch bc  v x -> evmatch bc'  v Vtop).
  {
    intros. constructor.
    inv H0.
    - constructor.
      apply is_constant_depends in H1. 
    eapply depends_on_blocks_le ; eauto; simpl ; auto.
    -
      inv H.
      eapply PM ; eauto.
      unfold is_bot in H0.
      simpl in H0. subst.
      inv H3.
    - 
      inv H; auto.
      eapply PM ; eauto.
      unfold is_bot in H0.
      simpl in H0. subst.
      inv H3.
    - 
      constructor.
    apply is_constant_depends in H1.
    eapply depends_on_blocks_le ; eauto; simpl ; auto.
    -
      constructor.
    apply is_constant_depends in H1.
    eapply depends_on_blocks_le ; eauto; simpl ; auto.
    -
      constructor.
    apply is_constant_depends in H1.
    eapply depends_on_blocks_le ; eauto; simpl ; auto.
    -
      inv H.
      apply PM with (2:= H1) ; simpl ; auto.
      eauto.
      unfold is_bot in H0.
      simpl in H0. subst. inv H1.
  }
  assert (SM: forall b p, epge Nonstack p -> smatch bc m b p -> smatch bc' m b Ptop).
  {
    intros. destruct H0 as [S1 S2]. split; intros.
    - simpl ; auto.
    - eapply S2 in H1 ; eauto.
      destruct mv ; simpl in *.
      eapply PM ; eauto.
  }
(* Conclusions *)
  exists bc'; splitall.
- (* nostack *)
  red; simpl; intros. destruct (eq_block b sp). congruence. 
  red; intros. elim n. eapply bc_stack; eauto. 
- (* bc' sp is BCinvalid *)
  simpl; apply dec_eq_true. 
- (* other blocks *)
  intros; simpl; apply dec_eq_false; auto. 
- (* values *)
  auto.
- (* genv *)
  apply genv_match_exten with bc; auto. 
  simpl; intros. destruct (eq_block b sp); intuition congruence.
  simpl; intros. destruct (eq_block b sp); congruence.
- (* romatch *)
  apply romatch_exten with bc; auto. 
  simpl; intros. destruct (eq_block b sp); intuition. 
- (* mmatch top *)
  constructor; simpl; intros. 
  + destruct (eq_block b sp). congruence. elim n. eapply bc_stack; eauto.
  + rewrite PTree.gempty in H0; discriminate.
  + destruct (eq_block b sp). congruence.
    eapply SM. eauto. eapply mmatch_nonstack; eauto. 
  + destruct (eq_block b sp). congruence.
    eapply SM. eauto. eapply mmatch_nonstack; eauto. 
    red; intros; elim n. eapply bc_stack; eauto. 
  + red; simpl; intros. destruct (eq_block b sp). congruence. 
    eapply mmatch_below; eauto.
Qed.

(** Construction 4: restore the stack after a public call *)


Theorem return_from_public_call:
  forall (caller callee: block_classification) bound sp ge e ae v m  rm 
         
  ,
  bc_below caller bound ->
  callee sp = BCother ->
  caller sp = BCstack ->
  (forall b, Plt b bound -> b <> sp -> caller b = callee b) ->
  genv_match caller ge ->
  ematch caller  e ae ->
  Ple bound (Mem.nextblock m) ->
  evmatch callee  v Vtop ->
  romatch callee m rm ->
  mmatch callee m mtop ->
  genv_match callee ge ->
  bc_nostack callee ->
  exists bc,
      evmatch bc  v Vtop
   /\ ematch bc  e ae
   /\ romatch bc m rm
   /\ mmatch bc m mafter_public_call
   /\ genv_match bc ge
   /\ bc sp = BCstack
   /\ (forall b, Plt b sp -> bc b = caller b).
Proof.
  intros until rm; intros  BELOW SP1 SP2 SAME GE1 EM BOUND RESM RM MM GE2 NOSTACK.
(* Constructing bc *)
  set (f := fun b => if eq_block b sp then BCstack else callee b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> b = sp).
    { unfold f; intros. destruct (eq_block b sp); auto. eelim NOSTACK; eauto. }
    intros. transitivity sp; auto. symmetry; auto. 
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> callee b = BCglob id).
    { unfold f; intros. destruct (eq_block b sp). congruence. auto. }
    intros. eapply (bc_glob callee); eauto. 
  }
  set (bc := BC f F_stack F_glob). unfold f in bc.
  assert (INCR: bc_incr caller bc).
  {
    red; simpl; intros. destruct (eq_block b sp). congruence. 
    symmetry; apply SAME; auto. 
  }
(* Invariance properties *)
  assert (PM: forall ex p, epmatch callee  ex p -> epmatch bc ex Ptop).  
  {
    intros. assert (epmatch callee  ex Ptop) by (eapply epmatch_top'; eauto).
    inv H0. constructor; simpl.
    eapply depends_on_blocks_le ; eauto. simpl. intros.
    destruct (eq_block b sp); congruence.
  }
  assert (VM: forall v x, evmatch callee  v x -> evmatch bc  v Vtop).
  {
    intros. assert (evmatch callee  v0 Vtop) by (eapply evmatch_top; eauto). 
    inv H0; constructor; eauto.
  }
  assert (SM: forall b p, smatch callee m b p -> smatch bc m b Ptop).
  {
    intros. destruct H; split; intros.
    reflexivity.
    exploit SMLD ; eauto.
    destruct mv ; simpl. 
    eapply PM ; eauto.
  }
(* Conclusions *)
  exists bc; splitall.
- (* result value *)
  eapply VM; eauto.
- (* environment *)
  eapply ematch_incr; eauto. 
- (* romem *)
  apply romatch_exten with callee; auto.
  intros; simpl. destruct (eq_block b sp); intuition. 
- (* mmatch *)
  constructor; simpl; intros.
  + (* stack *)
    apply ablock_init_sound. destruct (eq_block b sp).
    subst b. eapply SM. eapply mmatch_nonstack; eauto. congruence. 
    elim (NOSTACK b); auto.
  + (* globals *)
    rewrite PTree.gempty in H0; discriminate.
  + (* nonstack *)
    destruct (eq_block b sp). congruence. eapply SM; auto. eapply mmatch_nonstack; eauto.
  + (* top *)
    eapply SM. eapply mmatch_top; eauto. 
    destruct (eq_block b sp); congruence.
  + (* below *)
    red; simpl; intros. destruct (eq_block b sp). 
    subst b. eapply mmatch_below; eauto. congruence.
    eapply mmatch_below; eauto.
- (* genv *)
  eapply genv_match_exten with caller; eauto.
  simpl; intros. destruct (eq_block b sp). intuition congruence. 
  split; intros. rewrite SAME in H by eauto with va. auto.
  apply <- (proj1 GE2) in H. apply (proj1 GE1) in H. auto.
  simpl; intros. destruct (eq_block b sp). congruence. 
  rewrite <- SAME; eauto with va.
- (* sp *)
  simpl. apply dec_eq_true.
- (* unchanged *)
  simpl; intros. destruct (eq_block b sp). congruence. 
  symmetry. apply SAME; auto. eapply Plt_trans. eauto. apply BELOW. congruence.
Qed.

(** Construction 5: restore the stack after a private call *)

Theorem return_from_private_call:
  forall (caller callee: block_classification) bound sp ge e ae v  m rm am
  ,
  bc_below caller bound ->
  callee sp = BCinvalid ->
  caller sp = BCstack ->
  (forall b, Plt b bound -> b <> sp -> caller b = callee b) ->
  genv_match caller ge ->
  ematch caller  e ae ->
  bmatch caller m sp am.(am_stack) ->
  Ple bound (Mem.nextblock m) ->
  evmatch callee  v Vtop ->
  romatch callee m rm ->
  mmatch callee m mtop ->
  genv_match callee ge ->
  bc_nostack callee ->
  exists bc,
      evmatch bc  v (Ptr Nonstack)
   /\ ematch bc  e ae
   /\ romatch bc m rm
   /\ mmatch bc m (mafter_private_call am)
   /\ genv_match bc ge
   /\ bc sp = BCstack
   /\ (forall b, Plt b sp -> bc b = caller b).
Proof.
  intros until am; intros  BELOW SP1 SP2 SAME GE1 EM CONTENTS BOUND RESM RM MM GE2 NOSTACK.
(* Constructing bc *)
  set (f := fun b => if eq_block b sp then BCstack else callee b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> b = sp).
    { unfold f; intros. destruct (eq_block b sp); auto. eelim NOSTACK; eauto. }
    intros. transitivity sp; auto. symmetry; auto. 
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> callee b = BCglob id).
    { unfold f; intros. destruct (eq_block b sp). congruence. auto. }
    intros. eapply (bc_glob callee); eauto. 
  }
  set (bc := BC f F_stack F_glob). unfold f in bc.
  assert (INCR1: bc_incr caller bc).
  {
    red; simpl; intros. destruct (eq_block b sp). congruence. 
    symmetry; apply SAME; auto. 
  }
  assert (INCR2: bc_incr callee bc).
  {
    red; simpl; intros. destruct (eq_block b sp). congruence. auto.
  }

(* Invariance properties *)
  assert (PM: forall e p, epmatch callee  e p -> epmatch bc  e Nonstack).  
  {
    intros. assert (epmatch callee  e0 Ptop) by (eapply epmatch_top'; eauto).
    inv H0. constructor; simpl.
    eapply depends_on_blocks_le ; eauto.
    simpl. intros.
    destruct (eq_block b sp); intuition congruence.
  }
  assert (VM: forall v x, evmatch callee  v x -> evmatch bc  v (Ptr Nonstack)).
  {
    intros. assert (evmatch callee  v0 Vtop) by (eapply evmatch_top; eauto). 
    inv H0; constructor; eauto.
  } 
  assert (SM: forall b p, smatch callee m b p -> smatch bc m b Nonstack).
  {
    intros. destruct H; split; intros.
    reflexivity.
    exploit SMLD ; eauto.
    destruct mv ; simpl.
    eapply PM; eauto.
  }
  assert (BSTK: bmatch bc m sp (am_stack am)).
  {
    apply bmatch_incr with caller; eauto. 
  }
(* Conclusions *)
  exists bc; splitall.
- (* result value *)
  eapply VM; eauto.
- (* environment *)
  eapply ematch_incr; eauto. 
- (* romem *)
  apply romatch_exten with callee; auto.
  intros; simpl. destruct (eq_block b sp); intuition. 
- (* mmatch *)
  constructor; simpl; intros.
  + (* stack *)
    destruct (eq_block b sp). 
    subst b. exact BSTK.
    elim (NOSTACK b); auto.
  + (* globals *)
    rewrite PTree.gempty in H0; discriminate.
  + (* nonstack *)
    destruct (eq_block b sp). congruence. eapply SM; auto. eapply mmatch_nonstack; eauto.
  + (* top *)
    destruct (eq_block b sp). 
    subst. apply smatch_ge with (ab_summary (am_stack am)). apply BSTK. apply epge_lub_l. 
    apply smatch_ge with Nonstack. eapply SM. eapply mmatch_top; eauto. apply epge_lub_r.
  + (* below *)
    red; simpl; intros. destruct (eq_block b sp). 
    subst b. apply Plt_le_trans with bound. apply BELOW. congruence. auto. 
    eapply mmatch_below; eauto.
- (* genv *)
  eapply genv_match_exten; eauto.
  simpl; intros. destruct (eq_block b sp); intuition congruence.
  simpl; intros. destruct (eq_block b sp); congruence.
- (* sp *)
  simpl. apply dec_eq_true.
- (* unchanged *)
  simpl; intros. destruct (eq_block b sp). congruence. 
  symmetry. apply SAME; auto. eapply Plt_trans. eauto. apply BELOW. congruence.
Qed.

(** Construction 6: external call *)

Lemma eventval_match_dep:
  forall (ge: genv) bc
    (ME: genv_match bc ge)
    t ev v chunk
    (EVM : eventval_match ge ev t v),
    depends_on_blocks (fun b0 : block => bc b0 <> BCinvalid)
                      (Values_symbolic.Val.load_result chunk (Values_symbolictype.Eval v)).
Proof.
  intros.
  inv EVM; try now (des chunk; destr).
  red; intros.
  destruct ME as [ME ME']. rewrite ME in FS.
  trim (H b). congruence.
  des chunk; destr; rewrite H; auto.
Qed.

Theorem external_call_match:
  forall ef (ge: genv) vargs m t vres m' bc rm am,
  external_call ef ge vargs m t vres m' ->
  genv_match bc ge ->
  (forall v, In v vargs -> evmatch bc v Vtop) ->
  romatch bc m rm ->
  mmatch bc m am ->
  bc_nostack bc ->
  exists bc',
     bc_incr bc bc'
  /\ (forall b, Plt b (Mem.nextblock m) -> bc' b = bc b)
  /\ evmatch bc' vres Vtop
  /\ genv_match bc' ge
  /\ romatch bc' m' rm
  /\ mmatch bc' m' mtop
  /\ bc_nostack bc'
  /\ (forall b ofs n, Mem.valid_block m b -> bc b = BCinvalid -> Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n).
Proof.
  intros until am; intros EC GENV ARGS RO MM NOSTACK.
  generalize (ec_dep (external_call_spec ef) ge t vres m' EC).
  intro DEP. specialize (DEP (fun b => match bc b with BCinvalid => true | _ => false end)).
  trim DEP.
  {
    intros.
    erewrite bc_below_invalid; eauto. eapply mmatch_below; eauto.
  }
  trim DEP.
  {
    intros.
    des GENV. rewrite i in H. destr.
  }
  trim DEP.
  {
    apply Forall_forall. intros x IN; apply ARGS in IN.
    inv IN. inv H1.
    red. eapply depends_on_blocks_le; eauto. simpl. intros; destr.
  }
  assert (SMTOP1: forall b, match bc b with BCinvalid => true | _ => false end = false -> smatch bc m b Ptop).
  {
    intros.
    des MM.
    split. constructor.
    intros.
    des mv. eapply epmatch_top_def.
    destruct (mmatch_top b). des (bc b).
    specialize (SMLD _ _ _ H0 H1 _ H2). simpl in SMLD. eauto. 
  }
  trim DEP.
  {
    intros.
    red; intros. specialize (SMTOP1 _ NS). des SMTOP1.
    rewrite Forall_forall. intros.
    specialize (SMLD _ _ _ POS LB _ H). des x. inv SMLD.
    red. eapply depends_on_blocks_le; eauto.
    simpl; intros. destr.
  }

  destruct DEP as (unreachable & INCR & SAME & NODEP & DEP_valid & ReachSpec).

 set (f := fun b => if plt b (Mem.nextblock m)
                       then bc b
                       else if unreachable b
                            then BCinvalid else BCother).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> bc b = BCstack).
    { unfold f; intros. destruct (plt b (Mem.nextblock m)); auto. destr_in H. }
    intros. apply (bc_stack bc); auto.
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> bc b = BCglob id).
    { unfold f; intros. destruct (plt b (Mem.nextblock m)); auto. destr_in H.  }
    intros. eapply (bc_glob bc); eauto.
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.
  assert (INCR': bc_incr bc bc').
  {
    red; simpl; intros. apply pred_dec_true. eapply mmatch_below; eauto.
  }
  assert (BELOW: forall b, Plt b (Mem.nextblock m) -> bc' b = bc b).
  {
    simpl; intros; apply pred_dec_true; auto.
  }
  assert (SMTOP: forall b, unreachable b = false (* bc b <> BCinvalid *) -> smatch bc' m' b Ptop).
  {
    intros; split; intros.
    - constructor.
    - generalize (NODEP _ H _ _ _ H0 H1); intro.
      rewrite Forall_forall in H3; apply H3 in H2. des mv. constructor. 
      eapply depends_on_blocks_le. 2: eauto. simpl.
      intros.
      Require Import Tactics.
      destr. apply ReachSpec in H4. des H4.  destr_in e0. xomega.
      rewrite H4. destr. 
  }
   exists bc'; repSplit; auto.
  - constructor. constructor. 
    red in DEP_valid.
    eapply depends_on_blocks_le. 2: eauto. simpl.
    intros.
    destr. apply ReachSpec in H. des H. destr_in e. xomega.
    rewrite H. destr.
  - apply genv_match_exten with bc; auto.
    simpl; intros; split; intros.
    rewrite pred_dec_true by (eapply mmatch_below; eauto with va). auto.
    destruct (plt b (Mem.nextblock m)). auto. destr_in H. 
    simpl; intros. rewrite pred_dec_true by (eapply mmatch_below; eauto with va). auto.
  - red; simpl; intros.
    destruct (plt b (Mem.nextblock m)).
    + exploit RO; eauto. intros (R & P & Q).
      split; auto.
      split.
      * apply bmatch_incr with bc; auto. apply bmatch_inv with m; auto.
        intros. eapply Mem.loadbytes_unchanged_on_1. eapply external_call_readonly; eauto.
        auto. intros; red. apply Q.
      * intros; red; intros; elim (Q ofs).
        eapply external_call_max_perm with (m2 := m'); eauto.
    + destr_in H.
  - constructor; simpl; intros.
    + repeat destr_in H. 
    + rewrite PTree.gempty in H0; discriminate.
    + apply SMTOP; auto.
      des (unreachable b). rename Heqb0 into UR. generalize UR; intro.
      apply INCR in UR.
      destr_in H0. destr_in UR.
    + apply SMTOP; auto.
      des (unreachable b). rename Heqb0 into UR. generalize UR; intro.
      apply INCR in UR.
      destr_in H. destr_in UR.
    + red; simpl; intros.
      destruct (plt b (Mem.nextblock m)).
      eapply Plt_le_trans. eauto. eapply external_call_nextblock; eauto.
      destr_in H.
      eapply ReachSpec in Heqb0. des Heqb0.
      replace (bc b) with BCinvalid in e. destr.
      symmetry; eapply bc_below_invalid; eauto.
      eapply mmatch_below; eauto.
  - red; intros. unfold bc'. simpl.
    destr. destr.
  - intros. rewrite SAME; auto. rewrite H0; auto.
Qed.

(** ** Semantic invariant *)

Section SOUNDNESS.

Variable prog: program.

Let ge : genv := Genv.globalenv prog.

Let rm := romem_for_program prog.

Inductive sound_stack: block_classification -> list stackframe -> mem -> block -> Prop :=
  | sound_stack_nil: forall bc  m bound,
      sound_stack bc  nil m bound
  | sound_stack_public_call:
      forall (bc: block_classification)  res f sp pc e stk  m bound bc' bound' ae
             (STK: sound_stack bc'  stk m sp)
             (INCR: Ple bound' bound)
             (BELOW: bc_below bc' bound')
             (SP: bc sp = BCother)
             (SP': bc' sp = BCstack)
             (SAME: forall b, Plt b bound' -> b <> sp -> bc b = bc' b)
             (GE: genv_match bc' ge)
             (AN: VA.ge (analyze  rm f)!!pc (VA.State (AE.set res Vtop ae) mafter_public_call))
             (EM: ematch bc'  e ae),
        sound_stack bc (Stackframe res f sp pc e :: stk) m bound
  | sound_stack_private_call:
      forall (bc: block_classification) res f sp pc e stk  m  bound bc' bound' ae am
             (STK: sound_stack bc'  stk m sp)
             (INCR: Ple bound' bound)
             (BELOW: bc_below bc' bound')
             (SP: bc sp = BCinvalid)
             (SP': bc' sp = BCstack)
             (SAME: forall b, Plt b bound' -> b <> sp -> bc b = bc' b)
             (GE: genv_match bc' ge)
             (AN: VA.ge (analyze rm f)!!pc (VA.State (AE.set res (Ptr Nonstack) ae) (mafter_private_call am)))
             (EM: ematch bc'  e ae)
             (CONTENTS: bmatch bc' m sp am.(am_stack)),
        sound_stack bc  (Stackframe res f sp pc e :: stk) m bound.

Inductive sound_state: state -> Prop :=
  | sound_regular_state:
      forall s f sp pc e  m ae am bc 
        (STK: sound_stack bc s m sp)
        (AN: (analyze rm f)!!pc = VA.State ae am)
        (EM: ematch bc  e ae)
        (RO: romatch bc m rm)
        (MM: mmatch bc m am)
        (GE: genv_match bc ge)
        (SP: bc sp = BCstack),
      sound_state (State s f sp pc e m)
  | sound_call_state:
      forall s fd args   m bc
        (STK: sound_stack bc  s m (Mem.nextblock m))
        (ARGS: forall v, In v args -> evmatch bc v Vtop)
        (RO: romatch bc m rm)
        (MM: mmatch bc m mtop)
        (GE: genv_match bc ge)
        (NOSTK: bc_nostack bc),
      sound_state (Callstate s fd args m)
  | sound_return_state:
      forall s v  m bc 
        (STK: sound_stack bc  s m (Mem.nextblock m))
        (RES: evmatch bc  v Vtop)
        (RO: romatch bc m rm)
        (MM: mmatch bc m mtop)
        (GE: genv_match bc ge)
        (NOSTK: bc_nostack bc),
      sound_state (Returnstate s v m).

(** Properties of the [sound_stack] invariant on call stacks. *)


Lemma sound_stack_ext:
  forall m' (bc: block_classification) stk  m bound
  ,
    sound_stack bc stk m bound ->
  (forall b ofs n bytes,
       Plt b bound -> bc b = BCinvalid -> n >= 0 ->
       Mem.loadbytes m' b ofs n = Some bytes ->
       Mem.loadbytes m b ofs n = Some bytes) ->
  sound_stack bc  stk m' bound.
Proof.
  intros until 0.
  induction 1; intros INV.
- constructor.
- assert (Plt sp bound') by eauto with va.
  subst.
  eapply sound_stack_public_call; eauto.
  apply IHsound_stack; intros; auto.
  apply INV. xomega. rewrite SAME; auto. xomega. auto. auto.
- assert (Plt sp bound') by eauto with va. 
  eapply sound_stack_private_call; eauto. apply IHsound_stack; intros; auto.
  apply INV. xomega. rewrite SAME; auto. xomega. auto. auto.
  apply bmatch_ext with m; auto.
  intros.
  apply INV. xomega. auto. auto. auto.
Qed.

Lemma sound_stack_inv:
  forall  m' bc stk m bound,
  sound_stack bc stk m bound ->
  (forall b ofs n, Plt b bound -> bc b = BCinvalid -> n >= 0 -> Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n) ->
  sound_stack bc  stk m' bound.
Proof.
  intros. eapply sound_stack_ext  ; eauto. intros. rewrite <- H0; auto. 
Qed.


Lemma sound_stack_storev:
  forall chunk  m addr v m' bc aaddr stk bound
  ,
  Mem.storev chunk m addr v = Some m' ->
  evmatch bc addr aaddr ->
  sound_stack bc  stk m bound ->
  sound_stack bc  stk m' bound.
Proof.
  intros. apply sound_stack_inv with m; auto.
  unfold Mem.storev in H. 
  revert H.
  case_eq (Mem.mem_norm m addr) ; try discriminate.
  intros.
  assert (A: pmatch bc  b i Ptop).
  {
    eapply normalise_sound ; eauto.
    apply mem_no_forgery.
    apply evmatch_aptr_of_aval in H0.
    subst.
    eapply epmatch_ge; eauto.
    simpl. auto.
  }
  inv A. 
  intros. eapply Mem.loadbytes_store_other; eauto. left; congruence. 
Qed. 

Lemma sound_stack_storebytes:
  forall m b ofs bytes m' bc aaddr stk bound dst,
    Mem.mem_norm m dst  = Vptr b ofs -> 
    Mem.storebytes m b (Int.unsigned ofs) bytes = Some m' ->
    pmatch bc b ofs aaddr ->
    sound_stack bc stk m bound ->
    sound_stack bc stk m' bound.
Proof.
  intros. apply sound_stack_inv with m; auto. 
  assert (A: pmatch bc b ofs Ptop).
  {
    eapply pmatch_ge; eauto. constructor.
  }
  inv A. 
  intros. eapply Mem.loadbytes_storebytes_other; eauto.
  left ; intro ; subst.
  inv H1; try congruence.
Qed. 

Import NormaliseSpec.

Lemma sound_stack_free:
  forall m  b lo hi m' bc stk bound,
  Mem.free m b lo hi = Some m' ->
  sound_stack bc  stk m bound ->
  sound_stack bc  stk m' bound.
Proof.
  intros. eapply sound_stack_ext with (1:= H0); eauto.
  repeat intro.
  eapply Mem.loadbytes_free_2; eauto.
Qed.

Lemma loadbytes_free_list_2:
  forall l (m1 m2 : mem),
  MemReserve.release_boxes m1 l = Some m2 ->
  forall (b : block) (ofs n : Z) (bytes : list memval),
  Mem.loadbytes m2 b ofs n = Some bytes ->
  Mem.loadbytes m1 b ofs n = Some bytes.
Proof.
  intros ; subst.
  unfold MemReserve.release_boxes in H; destr_in H; inv H.
  Transparent Mem.loadbytes.
  unfold Mem.loadbytes in *. destr_in H0. inv H0. destr.
  exfalso; apply n0. red; intros.
  apply r. auto.
Qed.

Lemma sound_stack_free_list:
  forall m l m' bc stk bound,
  MemReserve.release_boxes m l =  Some m' ->
  sound_stack bc  stk m bound ->
  sound_stack bc  stk m' bound.
Proof.
  intros. eapply sound_stack_ext with (1:= H0); eauto.
  repeat intro.
  eapply loadbytes_free_list_2; eauto.
Qed.

Lemma sound_stack_new_bound:
  forall bc stk m bound bound',
  sound_stack bc stk m bound ->
  Ple bound bound' ->
  sound_stack bc stk m bound'.
Proof.
  intros. inv H. 
- constructor.
- eapply sound_stack_public_call with (bound' := bound'0); eauto. xomega. 
- eapply sound_stack_private_call with (bound' := bound'0); eauto. xomega. 
Qed.

Lemma sound_stack_exten:
  forall bc stk m bound (bc1: block_classification),
  sound_stack bc stk m bound ->
  (forall b, Plt b bound -> bc1 b = bc b) ->
  sound_stack bc1 stk m bound.
Proof.
  intros. inv H. 
- constructor.
- assert (Plt sp bound') by eauto with va. 
  eapply sound_stack_public_call; eauto.
  rewrite H0; auto. xomega. 
  intros. rewrite H0; auto. xomega.
- assert (Plt sp bound') by eauto with va. 
  eapply sound_stack_private_call; eauto.
  rewrite H0; auto. xomega. 
  intros. rewrite H0; auto. xomega.
Qed.

(** ** Preservation of the semantic invariant by one step of execution *)

Lemma sound_succ_state:
  forall bc pc ae am instr ae' am'  s f sp pc' e' m',
  (analyze rm f)!!pc = VA.State ae am ->
  f.(fn_code)!pc = Some instr ->
  In pc' (successors_instr instr) ->
  transfer f rm pc ae am = VA.State ae' am' ->
  ematch bc e' ae' ->
  mmatch bc m' am' ->
  romatch bc m' rm ->
  genv_match bc ge ->
  bc sp = BCstack ->
  sound_stack bc s m' sp ->
  sound_state (State s f sp pc' e' m').
Proof.
  intros. exploit analyze_succ; eauto. intros (ae'' & am'' & AN & EM & MM).
  econstructor; eauto. 
Qed.

Lemma areg_sound:
  forall bc e ae r, ematch bc e ae -> evmatch bc (e#r) (areg ae r).
Proof.
  intros. apply H. 
Qed.

Lemma aregs_sound:
  forall bc e ae rl, ematch bc e ae -> list_forall2 (evmatch bc) (e##rl) (aregs ae rl).
Proof.
  induction rl; simpl; intros. constructor. constructor; auto. apply areg_sound; auto.
Qed.

Hint Resolve areg_sound aregs_sound: va.

Lemma epge_evge : forall v,
    epge Nonstack (provenance v) -> 
    evge (Ptr Nonstack) v.
Proof.
  intros.
  unfold provenance in H.
  simpl in H.
  destruct v ; simpl in H ; try constructor ; simpl; auto.
  destruct p ; simpl in * ; auto.
  destruct p ; simpl in * ; auto.
  destruct p ; simpl in * ; auto.
Qed.
  

Lemma romatch_free_list:
  forall l bc m  m' rm,
  MemReserve.release_boxes m l =  Some m' ->
  romatch bc m rm ->
  romatch bc m' rm.
Proof.
  intros. apply romatch_ext with m; auto. 
  intros. eapply loadbytes_free_list_2; eauto. 
  intros.
  unfold MemReserve.release_boxes in H; destr_in H; inv H. apply H2.
Qed.

Lemma mmatch_free_list : 
      forall l (bc : block_classification) (m : mem) 
          (m' : mem) (am : amem),
        MemReserve.release_boxes m l = Some  m' -> mmatch bc m am -> mmatch bc m' am.
Proof.
  intros. apply mmatch_ext with m; auto. 
  intros. eapply loadbytes_free_list_2; eauto. 
  erewrite MemReserve.release_nextblock by eauto. xomega.
Qed.

Lemma match_aptr_of_aval :
  forall bc dst adst m bdst odst,
    evmatch bc dst adst-> 
    Mem.mem_norm m dst = Vptr bdst odst -> 
    pmatch bc bdst odst (aptr_of_aval adst).
Proof.
  intros.
  eapply normalise_sound; eauto.  apply mem_no_forgery.
  apply aptr_of_aval_sound; auto. 
Qed.

Theorem sound_step:
  forall st sz t st', RTL.step ge sz st t st' -> sound_state st -> sound_state st'.
Proof.
  induction 1; intros SOUND; inv SOUND.

- (* nop *)
  eapply sound_succ_state; eauto. simpl; auto. 
  unfold transfer; rewrite H. auto.

- (* op *)
  eapply sound_succ_state; eauto. simpl; auto. 
  unfold transfer; rewrite H. eauto. 
  apply ematch_update; auto. eapply eval_static_operation_sound; eauto with va.
  econstructor; eauto.
  repeat intro ; reflexivity.
- (* load *)
  eapply sound_succ_state; eauto. simpl; auto. 
  unfold transfer; rewrite H. eauto. 
  apply ematch_update; auto. eapply loadv_sound; eauto with va. 
  eapply eval_static_addressing_sound; eauto with va.
  econstructor; eauto.
  repeat intro ; reflexivity.

- (* store *)
  exploit eval_static_addressing_sound; eauto with va.
  econstructor; eauto.
  repeat intro ; reflexivity.
  intros VMADDR.
  eapply sound_succ_state; eauto. simpl; auto. 
  unfold transfer; rewrite H. eauto. 
  eapply storev_sound; eauto.
  revert H1.
  unfold Mem.storev.
  case_eq (Mem.mem_norm m a ) ; try congruence.
  intros.
  eapply romatch_store; eauto. 
  eapply sound_stack_storev; eauto. 

- (* call *)
  assert (TR: transfer f rm pc ae am = transfer_call ae am args res).
  { unfold transfer; rewrite H; auto. }
  unfold transfer_call in TR. 
  destruct (epincl (am_nonstack am) Nonstack && 
            forallb (fun r : reg => epincl (provenance (areg ae r)) Nonstack) args) eqn:NOLEAK.
+ (* private call *)
  InvBooleans.
  exploit analyze_successor; eauto. simpl; eauto. rewrite TR. intros SUCC. 
  exploit hide_stack; eauto. apply epincl_ge; auto.
  intros (bc' & A & B & C & D & E & F & G).
  apply sound_call_state with bc'; auto.
  * eapply sound_stack_private_call with (bound' := Mem.nextblock m) (bc' := bc); eauto.
    apply Ple_refl.
    eapply mmatch_below; eauto.
    eapply mmatch_stack; eauto. 
  * intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v. 
    apply D with (areg ae r). 
    rewrite forallb_forall in H2.
    apply H2 in Q.
    apply epge_evge.
    apply epincl_ge. auto.
    auto with va.
+ (* public call *)
  exploit analyze_successor; eauto. simpl; eauto. rewrite TR. intros SUCC. 
  exploit anonymize_stack; eauto. intros (bc' & A & B & C & D & E & F & G).
  apply sound_call_state with bc'; auto.
  * eapply sound_stack_public_call with (bound' := Mem.nextblock m) (bc' := bc); eauto.
    apply Ple_refl.
    eapply mmatch_below; eauto.
  * intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v. 
    apply D with (areg ae r). auto with va.

- (* tailcall *)
  exploit anonymize_stack; eauto. intros (bc' & A & B & C & D & E & F & G).
  apply sound_call_state with bc'; auto.
  +
  erewrite <- MemReserve.release_nextblock by eauto.
  erewrite Mem.nextblock_free by eauto. 
  apply sound_stack_new_bound with stk.
  apply sound_stack_exten with bc.
  eapply sound_stack_free_list; eauto.
  eapply sound_stack_free; eauto.
  intros. apply C. apply Plt_ne; auto.
  apply Plt_Ple. eapply mmatch_below; eauto. congruence. 
  + 
  intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v. 
  apply D with (areg ae r). auto with va.
  + 
    eapply romatch_free_list ; eauto.
    eapply romatch_free ; eauto.
  + 
    eapply mmatch_free_list; eauto. 
    eapply mmatch_free; eauto.
- (* builtin *)
  assert (SPVALID: Plt sp (Mem.nextblock m)) by (eapply mmatch_below; eauto with va).
  assert (TR: transfer f rm pc ae am = transfer_builtin ae am rm ef args res).
  { unfold transfer; rewrite H; auto. }
  assert (TR' := TR).
  unfold transfer_builtin in TR.
  exploit classify_builtin_sound; eauto. destruct (classify_builtin ef args ae)  eqn:BUILTIN.
+ (* volatile load *)
  intros (addr & VLOAD & VADDR). inv VLOAD.
  eapply sound_succ_state; eauto. simpl; auto.
  apply ematch_update; auto. 
  inv VOLLOAD.
  * (* true volatile access *)
    assert (V: evmatch bc (Values_symbolictype.Eval v0) (Ptr Glob)).
    { inv EVM; constructor; try (econstructor ; repeat intro ; reflexivity).
      constructor. repeat intro ; simpl.
      rewrite H1. reflexivity.
      exists id0.
      eapply GE; eauto. }
    destruct (va_strict tt).
    apply evmatch_lub_r. apply vnormalize_sound. auto. 
    apply vnormalize_sound. eapply evmatch_ge; eauto. constructor. constructor.
  * (* normal memory access *)
    exploit loadv_sound; eauto. unfold Mem.loadv. rewrite MN. eauto.
    intros V.
    destruct (va_strict tt). 
    apply evmatch_lub_l. auto.
    eapply vnormalize_cast; eauto. eapply evmatch_top; eauto. 
+ (* volatile store *)
  intros (addr & src & VSTORE & VADDR & VSRC). inv VSTORE.
  inv VOLSTORE.
  * (* true volatile access *)
    eapply sound_succ_state; eauto. simpl; auto.
    apply ematch_update; auto. repeat constructor. 
    apply mmatch_lub_l; auto.
  * (* normal memory access *)
    eapply sound_succ_state; eauto. simpl; auto.
    apply ematch_update; auto. repeat  constructor.
    apply mmatch_lub_r. eapply storev_sound; eauto.
    unfold Mem.storev. rewrite MN. auto.
    eapply romatch_store; eauto.
    eapply sound_stack_storev with (chunk := chunk) (m:=m) (addr := addr); eauto.
    unfold Mem.storev. rewrite MN. eauto.
+ (* memcpy *)
  intros (dst & src & MEMCPY & VDST & VSRC).
  destruct (zlt 0 sz0); inv MEMCPY; try Psatz.lia.
  * eapply sound_succ_state; eauto. simpl; auto. 
    apply ematch_update; auto. repeat constructor.
    eapply storebytes_sound; eauto.
    eapply normalise_sound; eauto.  apply mem_no_forgery.
    apply aptr_of_aval_sound; auto. 
    eapply Mem.loadbytes_length; eauto. 
    intros. eapply loadbytes_sound; eauto. Psatz.lia. 
    eapply match_aptr_of_aval ; eauto.
    eapply romatch_storebytes; eauto. 
    eapply sound_stack_storebytes. apply MNv'. apply SB.
    eapply match_aptr_of_aval. apply VDST. apply MNv'.
    auto.
  * eapply sound_succ_state; eauto. simpl; auto.
    apply ematch_update. auto. repeat constructor.
  
 + (* annot *)
  intros (A & B); subst. 
  eapply sound_succ_state; eauto. simpl; auto. 
  apply ematch_update; auto. constructor.
  apply is_constant_depends in B.
  constructor. eapply depends_on_blocks_le ; eauto.
  simpl. tauto.
 + (* annot val *)
  intros (A & B); subst. 
  eapply sound_succ_state; eauto. simpl; auto. 
  apply ematch_update; auto. 
 + (* general case *)

   intros _.
  unfold transfer_call in TR. 
  destruct (epincl (am_nonstack am) Nonstack && 
            forallb (fun r : reg => epincl (provenance (areg ae r)) Nonstack) args) eqn:NOLEAK.
* (* private builtin call *)
  InvBooleans. rewrite forallb_forall in H2.
  exploit hide_stack; eauto. apply epincl_ge; auto.
  intros (bc1 & A & B & C & D & E & F & G).
  exploit external_call_match; eauto. 
  intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v0.
  generalize (H2 _ Q). unfold areg.
  intros. eapply D; eauto with va.
  exploit epincl_ge.  apply H4. intro.
  des (AE.get r ae); repeat constructor.
  unfold provenance in H4, H5. simpl in *. des p.
  unfold provenance in H4, H5. simpl in *. des p.
  unfold provenance in H4, H5. simpl in *. des p.
  intros (bc2 & J & K & L & M & N & O & P & Q).
  exploit (return_from_private_call bc bc2); eauto.
  eapply mmatch_below; eauto.
  rewrite K; auto.
  intros. rewrite K; auto. rewrite C; auto.
  apply bmatch_inv with m. eapply mmatch_stack; eauto. 
  intros. apply Q; auto.
  eapply external_call_nextblock; eauto. 
  intros (bc3 & U & V & W & X & Y & Z & AA).
  eapply sound_succ_state with (bc := bc3); eauto. simpl; auto. 
  apply ematch_update; auto.
  apply sound_stack_exten with bc. 
  apply sound_stack_inv with m. auto.
  intros. apply Q. red. eapply Plt_trans; eauto.
  rewrite C; auto.
  exact AA.

  * (* public builtin call *)
  exploit anonymize_stack; eauto. 
  intros (bc1 & A & B & C & D & E & F & G).
  exploit external_call_match; eauto. 
  intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v0. eapply D; eauto with va.
  intros (bc2 & J & K & L & M & N & O & P & Q).
  exploit (return_from_public_call bc bc2); eauto.
  eapply mmatch_below; eauto.
  rewrite K; auto.
  intros. rewrite K; auto. rewrite C; auto.
  eapply external_call_nextblock; eauto. 
  intros (bc3 & U & V & W & X & Y & Z & AA).
  eapply sound_succ_state with (bc := bc3); eauto. simpl; auto. 
  apply ematch_update; auto.
  apply sound_stack_exten with bc. 
  apply sound_stack_inv with m. auto.
  intros. apply Q. red. eapply Plt_trans; eauto.
  rewrite C; auto.
  exact AA.
  
- (* cond *)
  eapply sound_succ_state; eauto. 
  simpl.
  destruct (Int.eq vb Int.zero) ; intuition.
  unfold transfer; rewrite H; auto. 

- (* jumptable *)
  eapply sound_succ_state; eauto. 
  simpl. eapply list_nth_z_in; eauto. 
  unfold transfer; rewrite H; auto.

- (* return *)
  exploit anonymize_stack; eauto. intros (bc' & A & B & C & D & E & F & G).
  apply sound_return_state with bc'; auto.
  erewrite <- MemReserve.release_nextblock by eauto.
  erewrite Mem.nextblock_free by eauto. 
  apply sound_stack_new_bound with stk.
  apply sound_stack_exten with bc.
  eapply sound_stack_free_list ; eauto.
  eapply sound_stack_free; eauto.
  intros. apply C. apply Plt_ne; auto.
  apply Plt_Ple. eapply mmatch_below; eauto with va.
  destruct or; simpl. eapply D; eauto. constructor.  constructor.
  repeat intro ; reflexivity.
  eapply romatch_free_list; eauto.   
  eapply romatch_free; eauto. 
  eapply mmatch_free_list; eauto.
  eapply mmatch_free; eauto.

- (* internal function *)
  exploit allocate_stack; eauto. 
  intros (bc' & A & B & C & D & E & F & G).
  exploit allocate_stack'; eauto.
  intros (J & I). clear D E.
  exploit (analyze_entrypoint rm f args m' bc'); eauto.
  
  intros (ae & am & AN & EM & MM').
  econstructor; eauto. 
  erewrite Mem.alloc_result by eauto. 
  apply sound_stack_exten with bc; auto.
  apply sound_stack_inv with m; auto. 
  intros.
  erewrite loadbytes_allocbytes_unchanged.
  eapply Mem.loadbytes_alloc_unchanged ; eauto. eauto.
  unfold Mem.valid_block.
  erewrite Mem.nextblock_alloc; eauto. xomega.
  intros.  eapply F; eauto.
  erewrite Mem.alloc_result by eauto.  auto.

- (* external function *)

  exploit external_call_match; eauto with va.
  intros (bc' & A & B & C & D & E & F & G & K).
  econstructor; eauto. 
  apply sound_stack_new_bound with (Mem.nextblock m).
  apply sound_stack_exten with bc; auto.
  apply sound_stack_inv with m; auto. 
  eapply external_call_nextblock; eauto.

- (* return *)
  inv STK.
  + (* from public call *)
   exploit return_from_public_call; eauto. 
   intros; rewrite SAME; auto.
   intros (bc1 & A & B & C & D & E & F & G). 
   destruct (analyze rm f)#pc as [ |ae' am'] eqn:EQ; simpl in AN; try contradiction. destruct AN as [A1 A2].
   eapply sound_regular_state with (bc := bc1); eauto.
   apply sound_stack_exten with bc'; auto.
   eapply ematch_ge; eauto. apply ematch_update. auto. auto. 
  + (* from private call *)
   exploit return_from_private_call; eauto. 
   intros; rewrite SAME; auto.
   intros (bc1 & A & B & C & D & E & F & G). 
   destruct (analyze rm f)#pc as [ |ae' am'] eqn:EQ; simpl in AN; try contradiction. destruct AN as [A1 A2].
   eapply sound_regular_state with (bc := bc1); eauto.
   apply sound_stack_exten with bc'; auto.
   eapply ematch_ge; eauto. apply ematch_update. auto. auto.
Qed.

End SOUNDNESS.

(** ** Soundness of the initial memory abstraction *)

Section INITIAL.

Variable prog: program.

Let ge := Genv.globalenv prog.

Lemma initial_block_classification:
  forall m fid sz,
  Genv.init_mem fid sz  prog  = Some m ->
  exists bc,
     genv_match bc ge
  /\ bc_below bc (Mem.nextblock m)
  /\ bc_nostack bc
  /\ (forall b id, bc b = BCglob id -> Genv.find_symbol ge id = Some b)
  /\ (forall b, Mem.valid_block m b -> bc b <> BCinvalid).
Proof.
  intros. 
  set (f := fun b => 
              if plt b (Genv.genv_next ge) then
                match Genv.invert_symbol ge b with None => BCother | Some id => BCglob id end
              else
                BCinvalid).
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    unfold f; intros.
    destruct (plt b1 (Genv.genv_next ge)); try discriminate.
    destruct (Genv.invert_symbol ge b1) as [id1|] eqn:I1; inv H0.
    destruct (plt b2 (Genv.genv_next ge)); try discriminate.
    destruct (Genv.invert_symbol ge b2) as [id2|] eqn:I2; inv H1.
    exploit Genv.invert_find_symbol. eexact I1. 
    exploit Genv.invert_find_symbol. eexact I2. 
    congruence.
  }
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    unfold f; intros.
    destruct (plt b1 (Genv.genv_next ge)); try discriminate.
    destruct (Genv.invert_symbol ge b1); discriminate.
  }
  set (bc := BC f F_stack F_glob). unfold f in bc.
  exists bc; splitall.
- split; simpl; intros. 
  + split; intros.
    * rewrite pred_dec_true by (eapply Genv.genv_symb_range; eauto).
      erewrite Genv.find_invert_symbol; eauto.
    * apply Genv.invert_find_symbol. 
      destruct (plt b (Genv.genv_next ge)); try discriminate.
      destruct (Genv.invert_symbol ge b); congruence.
  + rewrite ! pred_dec_true by assumption. 
    destruct (Genv.invert_symbol); split; congruence.
- red; simpl; intros. destruct (plt b (Genv.genv_next ge)); try congruence.
  erewrite <- Genv.init_mem_genv_next by eauto. auto. 
- red; simpl; intros. 
  destruct (plt b (Genv.genv_next ge)). 
  destruct (Genv.invert_symbol ge b); congruence.
  congruence.
- simpl; intros. destruct (plt b (Genv.genv_next ge)); try discriminate.
  destruct (Genv.invert_symbol ge b) as [id' | ] eqn:IS; inv H0.
  apply Genv.invert_find_symbol; auto.
- intros; simpl. unfold ge; erewrite Genv.init_mem_genv_next by eauto.
  rewrite pred_dec_true by assumption.
  destruct (Genv.invert_symbol (Genv.globalenv prog) b); congruence.
Qed.

Section INIT.

Variable bc: block_classification.
Hypothesis GMATCH: genv_match bc ge.

Lemma store_init_data_summary:
  forall ab p id,
    is_romem (ab_summary ab) ->
    is_romem (ab_summary (store_init_data ab p id)).
Proof.
  intros.
  assert (DFL: forall chunk av,
             is_romem (aptr_of_aval av) ->
             is_romem (ab_summary (ablock_store chunk ab p av))).
  {
    intros. 
    unfold ablock_store. unfold ab_summary.
    destruct ab. unfold ValueDomain.ab_summary in H.
    unfold evplub.
    unfold provenance.
    revert H0. generalize (aptr_of_aval av).
    intro. destruct a ; simpl ; try tauto.
    -  destruct ab_summary ; simpl in *; auto.
    -  destruct ab_summary ; simpl in *; auto.
       destruct (ident_eq id0 id1) ; simpl ; auto.
       destruct (ident_eq id0 id1) ; simpl ; auto.
    -  destruct ab_summary ; simpl in *; auto.
       destruct (ident_eq id0 id1) ; simpl ; auto.
       destruct (ident_eq id0 id1) ; simpl ; auto.
    -  destruct ab_summary ; simpl in *; auto.
  }
  unfold store_init_data.
  destruct id; try (apply DFL; constructor; simpl; auto; fail).
  auto.
Qed.


Lemma store_init_data_is_romem_block:
  forall ab p id,
    is_romem_block ab ->
    is_romem_block (store_init_data ab p id).
Proof.
  intros.
  destruct H.
  constructor.
  apply store_init_data_summary ; auto.
  unfold store_init_data.
  destruct id; try apply ablock_store_summary ; auto.
Qed.
  
Lemma store_init_data_list_summary:
  forall idl ab p,
  is_romem_block  ab ->
  is_romem_block (store_init_data_list ab p idl).
Proof.
  induction idl; simpl; intros. auto. apply IHidl. apply store_init_data_is_romem_block; auto. 
Qed.


Lemma store_init_data_sound:
  forall m b p id m' ab,
  Genv.store_init_data ge m b p id = Some m' ->
  bmatch bc m b ab ->
  bmatch bc m' b (store_init_data ab p id).
Proof.
  intros.
  destruct id; try (eapply ablock_store_sound; eauto; repeat constructor; fail).
  simpl in H. inv H. auto. 
  simpl in H. destruct (Genv.find_symbol ge i) as [b'|] eqn:FS; try discriminate.
  eapply ablock_store_sound; eauto. constructor. econstructor. apply GMATCH; eauto.
  repeat intro ; reflexivity.
Qed.

Lemma store_init_data_list_sound:
  forall idl m b p m' ab,
  Genv.store_init_data_list ge m b p idl = Some m' ->
  bmatch bc m b ab ->
  bmatch bc m' b (store_init_data_list ab p idl).
Proof.
  induction idl; simpl; intros.
- inv H; auto.
- destruct (Genv.store_init_data ge m b p a) as [m1|] eqn:SI; try discriminate.
  eapply IHidl; eauto. eapply store_init_data_sound; eauto. 
Qed.

Lemma store_init_data_other:
  forall m b p id m' ab b',
  Genv.store_init_data ge m b p id = Some m' ->
  b' <> b ->
  bmatch bc m b' ab ->
  bmatch bc m' b' ab.
Proof.
  intros. eapply bmatch_inv; eauto.
  intros. destruct id; try (eapply Mem.loadbytes_store_other; eauto; fail); simpl in H.
  inv H; auto. 
  destruct (Genv.find_symbol ge i); try discriminate.
  eapply Mem.loadbytes_store_other; eauto.
Qed.

Lemma store_init_data_list_other:
  forall b b' ab idl m p m',
  Genv.store_init_data_list ge m b p idl = Some m' ->
  b' <> b ->
  bmatch bc m b' ab ->
  bmatch bc m' b' ab.
Proof.
  induction idl; simpl; intros. 
  inv H; auto.
  destruct (Genv.store_init_data ge m b p a) as [m1|] eqn:SI; try discriminate.
  eapply IHidl; eauto. eapply store_init_data_other; eauto. 
Qed.

Lemma store_zeros_same:
  forall p m b pos n m',
  store_zeros m b pos n = Some m' ->
  smatch bc m b p ->
  smatch bc m' b p.
Proof.
  intros until n. functional induction (store_zeros m b pos n); intros.
- inv H. auto.
- eapply IHo; eauto. replace p with (evplub (I Int.zero) p). 
  eapply smatch_store; eauto. simpl ; auto.
  constructor.  repeat intro ; reflexivity.
  inv H0.
  destruct p ; simpl in * ;  tauto.
- discriminate.
Qed.

Lemma store_zeros_other:
  forall b' ab m b p n m',
  store_zeros m b p n = Some m' ->
  b' <> b ->
  bmatch bc m b' ab ->
  bmatch bc m' b' ab.
Proof.
  intros until n. functional induction (store_zeros m b p n); intros.
- inv H. auto.
- eapply IHo; eauto. eapply bmatch_inv; eauto. 
  intros. eapply Mem.loadbytes_store_other; eauto. 
- discriminate.
Qed.

Definition initial_mem_match (bc: block_classification) (m: mem) (g: genv) :=
  forall b v,
  Genv.find_var_info g b = Some v ->
  v.(gvar_volatile) = false -> v.(gvar_readonly) = true ->
  bmatch bc m b (store_init_data_list (ablock_init Pcst) 0 v.(gvar_init)).

Lemma alloc_global_match:
  forall m g idg m' fsz fid,
  Genv.genv_next g = Mem.nextblock m ->
  initial_mem_match bc m g ->
  Genv.alloc_global fid fsz ge m idg = Some m' ->
  initial_mem_match bc m' (Genv.add_global g idg).
Proof.
  intros; red; intros. destruct idg as [id [fd | gv]]; simpl in *.
  - destruct (Mem.alloc m 0 (Genv.size_glob' fid fsz fd) Normal) as [[m1 b1]| _] eqn:ALLOC; try congruence. 
  unfold Genv.find_var_info, Genv.add_global in H2; simpl in H2.
  assert (Plt b (Mem.nextblock m)). 
  { rewrite <- H. eapply Genv.genv_vars_range; eauto. }
  assert (b <> b1). 
  { apply Plt_ne. erewrite Mem.alloc_result by eauto. auto. }
  apply bmatch_inv with m. 
  eapply H0; eauto. 
  intros. transitivity (Mem.loadbytes m1 b ofs n). 
  eapply Mem.loadbytes_drop; eauto. 
  eapply Mem.loadbytes_alloc_unchanged; eauto.
- set (sz := Genv.init_data_list_size (gvar_init gv)) in *.
  repeat destr_in H1.
  unfold Genv.find_var_info, Genv.add_global in H2; simpl in H2.
  rewrite PTree.gsspec in H2. destruct (peq b (Genv.genv_next g)).
+ inversion H2; clear H2; subst v. 
  assert (b = b0). { erewrite Globalenvs.Genv.low_alloc_result by eauto. congruence. }
  clear e. subst b. 
  apply bmatch_inv with m2. 
  eapply store_init_data_list_sound; eauto. 
  apply ablock_init_sound.
  eapply store_zeros_same; eauto. 
  split; intros.
  * simpl ; auto.
  *
    assert (mv = Symbolic (Values_symbolictype.Eval Vundef) None O).
    unfold Mem.low_alloc in Heqo; destr_in Heqo; inv Heqo; simpl in *.
    Transparent Mem.loadbytes.
    unfold Mem.loadbytes in H5; simpl in H5. destr_in H5. inv H5.
    rewrite PMap.gss in H6.
    generalize (Mem.init_block_eundef (nat_of_Z n) ofs 0 sz (Mem.nextblock m)).
    rewrite Forall_forall; intro A; apply A in H6. auto.
    subst mv. simpl in *.
    repeat constructor ; reflexivity.
  * intros. eapply Mem.loadbytes_drop; eauto. 
    right; right; right. unfold Genv.perm_globvar. rewrite H3, H4. constructor. 
+ assert (Plt b (Mem.nextblock m)). 
  { rewrite <- H. eapply Genv.genv_vars_range; eauto. }
  assert (b <> b0). 
  { apply Plt_ne. erewrite Globalenvs.Genv.low_alloc_result by eauto. auto. }
  apply bmatch_inv with m2.
  eapply store_init_data_list_other; eauto. 
  eapply store_zeros_other; eauto. 
  apply bmatch_inv with m. 
  eapply H0; eauto. 
  intros. unfold Mem.loadbytes.
  erewrite Genv.low_alloc_contents_old; eauto.
  repeat destr.
  exfalso; apply n1.
  red. intros ofs0 ENC; apply r in ENC.
  eapply Genv.perm_low_alloc_4; eauto.
  exfalso; apply n1.
  red. intros ofs0 ENC; apply r in ENC.
  rewrite <- (Genv.low_alloc_perm _ _ _ _ Heqo); eauto.
  intros. eapply Mem.loadbytes_drop; eauto.
Qed.

Lemma alloc_globals_match:
  forall gl m g m' fsz ,
  Genv.genv_next g = Mem.nextblock m ->
  initial_mem_match bc m g ->
  Genv.alloc_globals fid fsz ge m gl = Some m' ->
  initial_mem_match bc m' (Genv.add_globals g gl).
Proof.
  induction gl; simpl; intros. 
- inv H1; auto. 
- destruct (Genv.alloc_global fid fsz ge m a) as [m1|] eqn:AG; try discriminate.
  eapply IHgl; eauto. 
  erewrite Genv.alloc_global_nextblock; eauto. simpl. congruence. 
  eapply alloc_global_match; eauto. 
Qed.

Definition romem_consistent (g: genv) (rm: romem) :=
  forall id b ab,
  Genv.find_symbol g id = Some b -> rm!id = Some ab ->
  exists v,
     Genv.find_var_info g b = Some v
  /\ v.(gvar_readonly) = true
  /\ v.(gvar_volatile) = false
  /\ ab = store_init_data_list (ablock_init Pcst) 0 v.(gvar_init).

Lemma alloc_global_consistent:
  forall g rm idg,
  romem_consistent g rm ->
  romem_consistent (Genv.add_global g idg) (alloc_global rm idg).
Proof.
  intros; red; intros. destruct idg as [id1 [fd1 | v1]];
  unfold Genv.add_global, Genv.find_symbol, Genv.find_var_info, alloc_global in *; simpl in *.
- rewrite PTree.gsspec in H0. rewrite PTree.grspec in H1. unfold PTree.elt_eq in *.
  destruct (peq id id1). congruence. eapply H; eauto. 
- rewrite PTree.gsspec in H0. destruct (peq id id1).
+ inv H0. rewrite PTree.gss. 
  destruct (gvar_readonly v1 && negb (gvar_volatile v1)) eqn:RO.
  InvBooleans. rewrite negb_true_iff in H2.
  rewrite PTree.gss in H1.
  exists v1. intuition try congruence. 
  rewrite PTree.grs in H1. discriminate.
+ rewrite PTree.gso. eapply H; eauto. 
  destruct (gvar_readonly v1 && negb (gvar_volatile v1)).
  rewrite PTree.gso in H1; auto. 
  rewrite PTree.gro in H1; auto. 
  apply Plt_ne. eapply Genv.genv_symb_range; eauto. 
Qed.

Lemma alloc_globals_consistent:
  forall gl g rm,
  romem_consistent g rm ->
  romem_consistent (Genv.add_globals g gl) (List.fold_left alloc_global gl rm).
Proof.
  induction gl; simpl; intros. auto. apply IHgl. apply alloc_global_consistent; auto. 
Qed.

End INIT.



Theorem initial_mem_matches:
  forall fsz m (Fsz_spec: forall i, fsz i > 0),
  Genv.init_mem RTL.fid fsz prog = Some m -> 
  exists bc,
     genv_match bc ge
  /\ bc_below bc (Mem.nextblock m)
  /\ bc_nostack bc
  /\ romatch bc m (romem_for_program prog)
  /\ (forall b, Mem.valid_block m b -> bc b <> BCinvalid).
Proof.
  intros.
  exploit initial_block_classification; eauto. intros (bc & GE & BELOW & NOSTACK & INV & VALID). 
  exists bc; splitall; auto.
  assert (A: initial_mem_match bc m ge).
  {
    apply alloc_globals_match with (fsz := fsz) (m := Mem.empty); auto.
    red. unfold Genv.find_var_info; simpl. intros. rewrite PTree.gempty in H0; discriminate.
  }
  assert (B: romem_consistent ge (romem_for_program prog)).
  {
    apply alloc_globals_consistent.
    red; intros. rewrite PTree.gempty in H1; discriminate.
  }
  red; intros.
  exploit B; eauto. intros (v & FV & RO & NVOL & EQ).
  assert (BM : bmatch bc m b ab) by (subst ab; eapply A ; eauto).
  split. subst ab.
  - apply store_init_data_list_summary.
    constructor. simpl ; auto.
    apply ablock_init_summary ; simpl ; auto.
  - 
  split. subst ab. eapply A; eauto.
  unfold ge in FV.
  eapply Genv.init_mem_characterization in FV; eauto.
  revert FV.
  intros (P & Q & R & S & T). 
  intros; red; intros. exploit S; eauto. intros [U V]. 
  unfold Genv.perm_globvar in V; rewrite RO, NVOL in V. inv V. 
Qed.

End INITIAL. 

Lemma genv_store_init_data_smatch_top : 
  forall (ge: Genv.t fundef unit) bc m m' b p a
         (MENV  : genv_match bc ge)
         (SI : Genv.store_init_data ge m b p a = Some m')
         (SMATCH : forall b : positive,
             Plt b (Mem.nextblock m) -> smatch bc m b Ptop),
  forall b : positive, Plt b (Mem.nextblock m') -> smatch bc m' b Ptop.
Proof.
  intros.
  assert (NEXT : Mem.nextblock m' = Mem.nextblock m).
  {
    unfold Genv.store_init_data in SI.
    destruct a; try (eapply Mem.nextblock_store ; eauto; fail).
    congruence.
    destruct (Genv.find_symbol ge i) ; try congruence.
    eapply Mem.nextblock_store ; eauto; fail.
  }
  rewrite NEXT in H.
  apply SMATCH in H. clear NEXT.
  destruct a ; simpl in SI.
  - 
  apply smatch_store with (2:= H) (av:= Pcst) in SI; simpl ; auto.
  repeat constructor ; repeat intro ; reflexivity.
  - 
  apply smatch_store with (2:= H) (av:= Pcst) in SI; simpl ; auto.
  repeat constructor ; repeat intro ; reflexivity.
  - 
  apply smatch_store with (2:= H) (av:= Pcst) in SI; simpl ; auto.
  repeat constructor ; repeat intro ; reflexivity.
  - 
  apply smatch_store with (2:= H) (av:= Pcst) in SI; simpl ; auto.
  repeat constructor ; repeat intro ; reflexivity.
  - 
  apply smatch_store with (2:= H) (av:= Pcst) in SI; simpl ; auto.
  repeat constructor ; repeat intro ; reflexivity.
  - 
  apply smatch_store with (2:= H) (av:= Pcst) in SI; simpl ; auto.
  repeat constructor ; repeat intro ; reflexivity.
  - inv SI ; congruence.
  - destruct (Genv.find_symbol ge i) eqn:SYMB ; try congruence.
    apply smatch_store with (2:= H) (av:= Glob) in SI; simpl ; auto.
    apply epmatch_ge with (q:= Gl i i0). simpl ; auto.
    destruct MENV.
    rewrite H0 in SYMB.
    econstructor; eauto. repeat intro ; reflexivity.
Qed.
    

Lemma genv_store_init_data_list_smatch_top :
  forall (ge: Genv.t fundef unit) bc idl m m' b p
         (ENV : genv_match bc ge)
         (SIDL : Genv.store_init_data_list ge m b p idl = Some m')
         (SMATCH : forall b : positive, Plt b (Mem.nextblock m) -> smatch bc m b Ptop),
  forall b : positive, Plt b (Mem.nextblock m') -> smatch bc m' b Ptop.
Proof.
  induction idl; simpl; intros.
- inv SIDL ; auto.
- destruct (Genv.store_init_data ge m b p a) as [m1|] eqn:SI; try discriminate.
  eapply IHidl; eauto.
  eapply genv_store_init_data_smatch_top ; eauto.
Qed.

Lemma alloc_smatch_top :
  forall bc m j m' b'
         (ALLOC : Mem.alloc m 0 j Normal = Some (m', b'))
         (SMATCH : forall b : positive,
             Plt b (Mem.nextblock m) -> smatch bc m b Ptop),
    forall b,
      Plt b (Mem.nextblock m') -> smatch bc m' b Ptop.
Proof.
  intros.
  assert (CASE : Plt b (Mem.nextblock m) \/ b = b').
  { exploit Mem.nextblock_alloc ; eauto.
    exploit Mem.alloc_result ; eauto.
    intros.
    subst.
    rewrite H1 in H.
    xomega.
  }
  destruct CASE.
  -
    specialize (SMATCH _ H0).
    destruct SMATCH ; constructor ; auto.
    intros.
    eapply SMLD ; eauto.
    rewrite <- H2.
    symmetry.
    eapply Mem.loadbytes_alloc_unchanged; eauto.
  - subst.
    constructor ; simpl ; auto.
    intros.
    exploit Mem.loadbytes_alloc_same ; eauto.
    intros (* [x [y EQ]] *); subst. simpl. constructor.
    repeat intro ; reflexivity.
Qed.

Lemma  drop_perm_loadbytes :
  forall m b sz p m' n ofs b' l
         (ALLOCG : Mem.drop_perm m b 0 sz p  = Some m')
         (LOAD : Mem.loadbytes m' b' ofs n = Some l),
    Mem.loadbytes m b' ofs n = Some l.
Proof.
  Transparent Mem.loadbytes.
  unfold Mem.loadbytes.
  intros m b sz p m' n ofs b' l ALLOCG.
  repeat destr. intro.
  erewrite Mem.drop_perm_contents; eauto.
  exfalso; apply n0.
  red; intros.
  eapply Mem.perm_drop_4; eauto.
Qed.

Lemma low_alloc_smatch_top :
  forall bc m j m' b' al
         (ALLOC : Mem.low_alloc m 0 j al Normal = Some (m', b'))
         (SMATCH : forall b : positive,
             Plt b (Mem.nextblock m) -> smatch bc m b Ptop),
    forall b,
      Plt b (Mem.nextblock m') -> smatch bc m' b Ptop.
Proof.
  intros.
  assert (CASE : Plt b (Mem.nextblock m) \/ b = b').
  { exploit Genv.low_alloc_nextblock ; eauto.
    exploit Genv.low_alloc_result ; eauto.
    intros.
    subst.
    rewrite H1 in H.
    xomega.
  }
  destruct (peq b b'). clear CASE.
  - subst.
    constructor ; simpl ; auto.
    intros.
    assert (mv = Symbolic (Values_symbolictype.Eval Vundef) None O).
    unfold Mem.low_alloc in ALLOC; destr_in ALLOC; inv ALLOC; simpl in *.
    unfold Mem.loadbytes in H1; simpl in H1. destr_in H1. inv H1.
    rewrite PMap.gss in H2.
    generalize (Mem.init_block_eundef (nat_of_Z n) ofs 0 j (Mem.nextblock m)).
    rewrite Forall_forall; intro A; apply A in H2. auto.
    subst mv. simpl in *.
    repeat constructor ; reflexivity.
  - des CASE.
    specialize (SMATCH _ p).
    destruct SMATCH ; constructor ; auto.
    intros.
    eapply SMLD ; eauto.
    rewrite <- H1. instantiate (1 := ofs).
    unfold Mem.loadbytes.
    erewrite (Genv.low_alloc_contents_old _ _ _ _ _ ALLOC); eauto.
    repeat destr.
    exfalso; apply n1.
    red. intros ofs0 ENC; apply r in ENC.
    rewrite <- (Genv.low_alloc_perm _ _ _ _ ALLOC); eauto.

    exfalso; apply n1.
    red. intros ofs0 ENC; apply r in ENC.
    eapply Genv.perm_low_alloc_4; eauto.

Qed.



Lemma alloc_global_smatch_top :
  forall (ge: Genv.t fundef unit) bc m  idg m' fsz
         (MENV  : genv_match bc ge)
         (ALLOCG : Genv.alloc_global fid fsz ge m idg = Some m')
         (SMATCH : forall b, Plt b (Mem.nextblock m) -> smatch bc m b Ptop),
  (forall b', Plt b' (Mem.nextblock m') -> smatch bc m' b' Ptop).
Proof.
  intros. destruct idg as [id [fd | gv]]; simpl in *.
  - destruct (Mem.alloc m 0 (Genv.size_glob' fid fsz fd) Normal) as [[m1 b1]| _] eqn:ALLOC; try congruence.
    exploit Mem.nextblock_drop ; eauto.
    intro. rewrite H0 in *.
    assert (forall b : positive,
               Plt b (Mem.nextblock m1) -> smatch bc m1 b Ptop).
    { intros. exploit alloc_smatch_top ; eauto. }
    eapply smatch_ext ; eauto.
    intros.
    destruct (peq b' b1) ; subst ; try tauto.
    + eapply drop_perm_loadbytes ; eauto.
    + rewrite <- H2.
      symmetry.
      eapply Mem.loadbytes_drop; eauto.
  -  set (sz := Genv.init_data_list_size (gvar_init gv)) in *.
     repeat destr_in ALLOCG.
     unfold fundef in *.
     revert H. revert b'.
     assert (HM1 : forall b, Plt b (Mem.nextblock m0) -> smatch bc m0 b Ptop).
     { eapply low_alloc_smatch_top; eauto. }
     assert (HM2 : forall b, Plt b (Mem.nextblock m1) -> smatch bc m1 b Ptop).
     { intros.
       exploit Genv.store_zeros_nextblock; eauto.
       intro. rewrite H0 in *.
       destruct (peq b b0). subst.
       eapply store_zeros_same; eauto.
       apply HM1 in H.
       eapply smatch_ext ; eauto.
       intros. rewrite <- H1.
       symmetry.
       eapply Genv.store_zeros_loadbytes_outside; eauto.
     }
     assert (HM3 :  forall b, Plt b (Mem.nextblock m2) -> smatch bc m2 b Ptop).
     {
       eapply genv_store_init_data_list_smatch_top ; eauto.
     }
     intros.
     exploit Mem.nextblock_drop ; eauto.
     intros. rewrite H0 in *.
     apply HM3 in H.
     destruct H ; auto.
     constructor ; auto.
     intros.
     eapply SMLD with (ofs:=ofs); eauto.
     eapply drop_perm_loadbytes ; eauto.
Qed.
    


Lemma alloc_globals_smatch_top :
  forall (ge: Genv.t fundef unit) bc idg m   m' fsz
         (MENV  : genv_match bc ge)
         (ALLOCG : Genv.alloc_globals fid fsz ge m idg = Some m')
         (SMATCH : forall b', Plt b' (Mem.nextblock m) -> smatch bc m b' Ptop),

  (forall b', Plt b' (Mem.nextblock m') -> smatch bc m' b' Ptop).
Proof.
  induction idg ; simpl.
  - intros. inv ALLOCG ; eauto.
  -intros.
   destruct (Genv.alloc_global fid fsz ge m a) eqn:ALLOC; try congruence.
   eapply IHidg in ALLOCG ;  eauto.
   eapply alloc_global_smatch_top; eauto.
Qed.   


Lemma mmatch_init_top : 
  forall m prog fsz bc
  (INIT : Genv.init_mem fid fsz prog = Some m)
  (GE : genv_match bc (Genv.globalenv prog))
  (BELOW : bc_below bc (Mem.nextblock m))
  (NOSTACK : bc_nostack bc)
  (RM : romatch bc m (romem_for_program prog))
  (VALID : forall b : block, Mem.valid_block m b -> bc b <> BCinvalid),
    mmatch bc m mtop.
Proof.
  intros.
  constructor; auto.
  - intuition.
  - intros.
    simpl in H0. rewrite PTree.gempty in H0. congruence.
  - intros. simpl.
    unfold Genv.init_mem in INIT.
    eapply alloc_globals_smatch_top; eauto.
    intros. simpl in H1. xomega.
  - intros.  simpl.
    unfold Genv.init_mem in INIT.
    eapply alloc_globals_smatch_top; eauto.
    intros. simpl in H0. xomega.
Qed.    


Theorem sound_initial:
  forall prog fsz (Fszspec: forall i, fsz i > 0) st, initial_state prog fsz st -> sound_state prog st.
Proof.
destruct 2. 
  exploit initial_mem_matches; eauto. intros (bc & GE & BELOW & NOSTACK & RM & VALID).
  apply sound_call_state with bc; auto.
- constructor. 
- simpl; tauto. 
- eapply mmatch_init_top ; eauto.
Qed.

Hint Resolve areg_sound aregs_sound: va.

(** * Interface with other optimizations *)

Definition avalue (a: VA.t) (r: reg) : aval :=
  match a with
  | VA.Bot => Vbot
  | VA.State ae am => AE.get r ae
  end.


Lemma avalue_sound:
  forall prog s f sp pc e m r,
  sound_state prog (State s f  sp pc e m) ->
  exists bc,
     evmatch bc e#r (avalue (analyze (romem_for_program prog) f)!!pc r)
  /\ genv_match bc (Genv.globalenv prog)
  /\ bc sp = BCstack.
Proof.
  intros. inv H. exists bc; split; auto. rewrite AN. apply EM.
Qed. 

Definition aaddr (a: VA.t) (r: reg) : aptr :=
  match a with
  | VA.Bot => Pbot
  | VA.State ae am => aptr_of_aval (AE.get r ae)
  end.


Definition aaddressing (a: VA.t) (addr: addressing) (args: list reg) : aptr :=
  match a with
  | VA.Bot => Pbot
  | VA.State ae am => aptr_of_aval (eval_static_addressing addr (aregs ae args))
  end.

  


