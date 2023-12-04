(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Observable events, execution traces, and semantics of external calls. *)

Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import NormaliseSpec.
Require Import ExprEval.
Require Import Memory.
Require Import Globalenvs.
Require Import Values_symbolic.
Require Import Values_symbolictype.
Require Import IntFacts.
Require Import Equivalences.
Require Import Memperm.
Require Export EventsGeneric.
Require Import MemRel.
Require Import Psatz.
Require Import Tactics Permutation MemReserve.


(** * Relating values and event values *)

Set Implicit Arguments.

Section EVENTVAL.

(** Global environment used to translate between global variable names and their block identifiers. *)
Variables F V: Type.
Variable ge: Genv.t F V.

(** Translation between values and event values. *)

Inductive eventval_match: eventval -> typ -> val -> Prop :=
| ev_match_int: forall i (* sv, same_eval sv (Eval (Vint i)) -> *),
                  eventval_match (EVint i) AST.Tint (Vint i)
| ev_match_long: forall i (* sv,same_eval sv (Eval (Vlong i)) -> *),
                   eventval_match (EVlong i) AST.Tlong (Vlong i)
| ev_match_float: forall f (* sv, *)
    (* same_eval sv (Eval (Vfloat f)) -> *),
    eventval_match (EVfloat f) AST.Tfloat (Vfloat f)
| ev_match_single: forall f (* sv, same_eval sv (Eval (Vsingle f)) -> *),
                     eventval_match (EVsingle f) AST.Tsingle (Vsingle f)
| ev_match_ptr: forall id b ofs
                  (FS: Genv.find_symbol ge id = Some b)
                  (* sv (SE: same_eval sv (Eval (Vptr b ofs))) *),
    eventval_match (EVptr_global id ofs) AST.Tint (Vptr b ofs).

Inductive eventval_list_match: list eventval -> list typ -> list val -> Prop :=
  | evl_match_nil:
      eventval_list_match nil nil nil
  | evl_match_cons:
      forall ev1 evl ty1 tyl v1 vl
        (EVM: eventval_match ev1 ty1 v1)
        (EVLM: eventval_list_match evl tyl vl),
        eventval_list_match (ev1::evl) (ty1::tyl) (v1::vl).

(** Some properties of these translation predicates. *)


Lemma same_eval_nu_type:
  forall e v t,
    same_eval e (Eval v) ->
    v <> Vundef /\
    wt_val v t ->
    wt_expr e t.
Proof.
  intros.
  eapply (ExprEval.expr_nu_type (fun _ => Int.zero) (fun _ _ => Byte.zero)). eauto.
  des v. des v.
Qed.


Lemma eventval_match_type:
  forall ev ty v,
  eventval_match ev ty v -> Values.Val.has_type v ty.
Proof.
  intros.
  inv H; simpl; auto.
  (* eapply same_eval_nu_type; eauto; destr. *)
  (* eapply same_eval_nu_type; eauto; destr. *)
  (* eapply same_eval_nu_type; eauto; destr. *)
  (* eapply same_eval_nu_type; eauto; destr. *)
  (* eapply same_eval_nu_type; eauto; destr. *)
Qed.

Lemma eventval_list_match_length:
  forall evl tyl vl, eventval_list_match evl tyl vl -> List.length vl = List.length tyl.
Proof.
  induction 1; simpl; eauto.
Qed.

Lemma eventval_match_lessdef:
  forall ev ty v1 v2,
  eventval_match ev ty  v1 -> Values.Val.lessdef v1 v2 -> eventval_match ev ty v2.
Proof.
  intros.
  inv H; inv H0; econstructor; eauto.
  (* try (red; intros; specialize (H0 alloc em); rewrite H1 in H0; *)
  (*      simpl in *; inv H0; auto). *)
  (* red; intros; specialize (H0 alloc em); rewrite SE in H0; *)
  (* simpl in *; inv H0; auto. *)
Qed.

Lemma eventval_list_match_lessdef:
  forall  vl1 evl tyl, eventval_list_match evl tyl vl1->
  forall vl2, Values.Val.lessdef_list vl1 vl2 -> eventval_list_match evl tyl vl2.
Proof.
  induction vl1; intros. inv H; inv H0; constructor. 
  inv H0. inv H. constructor. eapply eventval_match_lessdef; eauto. eauto.
Qed.

(** Compatibility with memory injections *)

Variable f: block -> option (block * Z).
Variable ei: meminj -> expr_sym -> expr_sym -> Prop.
Hypothesis wf: wf_inj ei.

Definition meminj_preserves_globals : Prop :=
     (forall id b, Genv.find_symbol ge id = Some b -> f b = Some(b, 0))
  /\ (forall b gv, Genv.find_var_info ge b = Some gv -> f b = Some(b, 0))
  /\ (forall b1 b2 delta gv, Genv.find_var_info ge b2 = Some gv -> f b1 = Some(b2, delta) -> b2 = b1).

Hypothesis glob_pres: meminj_preserves_globals.

Lemma same_eval_ei:
    forall v1 v2 v
      (EI: ei f v1 v2)
      (NOPTR: match v with
         Vptr _ _ | Vundef => False
       | _ => True
       end)
      (SE: same_eval v1 (Eval v)),
      same_eval v2 (Eval v).
  Proof.
    red; intros.
    generalize (ei_ld'_expr _ wf _ _ _ EI alloc em
                            _ _ (cm_inj_inj_alloc _ _) (em_inj_inj_em _ _)).
    simpl. rewrite SE. simpl. intro A; inv A; auto.
    des v.
    des v.
  Qed.
  

Lemma eventval_match_inject:
  forall ev ty v1 v2,
  eventval_match ev ty  v1 -> val_inject f v1 v2 -> eventval_match ev ty v2.
Proof.
  intros.
  inv H; inv H0; try econstructor; eauto.
  destruct glob_pres as [A [B C]].
  exploit A; eauto.
  intro D; rewrite D in FB. inv FB. rewrite Int.add_zero. constructor. auto.
Qed.


Lemma eventval_match_inject_2:
  forall ev ty v,
  eventval_match ev ty v -> val_inject f v v.
Proof.
  intros; des v; auto.
  destruct glob_pres as [A [B C]].
  inv H.
  econstructor. eapply A; eauto. eauto. symmetry; apply Int.add_zero. 
Qed.

Lemma eventval_list_match_inject:
  forall  evl tyl vl1, eventval_list_match evl tyl vl1 ->
  forall vl2, list_forall2 (val_inject f) vl1 vl2 -> eventval_list_match evl tyl vl2.
Proof.
  induction 1; intros. inv H; constructor.
  inv H0. constructor. eapply eventval_match_inject; eauto. eauto.
Qed.

(** Determinism *)

Lemma eventval_match_determ_1:
  forall ev ty v1 v2, eventval_match ev ty v1 -> eventval_match ev ty v2 ->
                 v1 = v2.
Proof.
  intros. inv H; inv H0; auto; try rewrite H1, H2; try reflexivity.
  congruence. 
Qed.

Lemma eventval_match_determ_2:
  forall ev1 ev2 ty v, eventval_match ev1 ty v -> eventval_match ev2 ty v -> ev1 = ev2.
Proof.
  intros. inv H; inv H0; auto.
  des (peq id id0).
  generalize (Genv.global_addresses_distinct ge n FS FS0). destr.
Qed.

Lemma eventval_list_match_determ_2:
  forall evl1 tyl vl, eventval_list_match evl1 tyl vl ->
  forall evl2, eventval_list_match evl2 tyl vl -> evl1 = evl2.
Proof.
  induction 1; intros. inv H. auto. inv H0. f_equal; eauto.
  eapply eventval_match_determ_2; eauto.
Qed.

(** Validity *)

Definition eventval_valid (ev: eventval) : Prop :=
  match ev with
  | EVint _ => True
  | EVlong _ => True
  | EVfloat _ => True
  | EVsingle _ => True
  | EVptr_global id ofs => exists b, Genv.find_symbol ge id = Some b
  end.

Definition eventval_type (ev: eventval) : typ :=
  match ev with
  | EVint _ => AST.Tint
  | EVlong _ => AST.Tlong
  | EVfloat _ => AST.Tfloat
  | EVsingle _ => AST.Tsingle
  | EVptr_global id ofs => AST.Tint
  end.

Lemma eventval_match_receptive:
  forall ev1 ty v1 ev2,
  eventval_match ev1 ty v1 ->
  eventval_valid ev1 -> eventval_valid ev2 -> eventval_type ev1 = eventval_type ev2 ->
  exists v2, eventval_match ev2 ty v2.
Proof.
  intros.
  inv H; des ev2; dex; eexists; econstructor; try reflexivity; eauto.
Qed.

Lemma eventval_match_valid:
  forall ev ty v, eventval_match ev ty v -> eventval_valid ev.
Proof.
  destruct 1; simpl; auto. exists b; auto.
Qed.

Lemma eventval_match_same_type:
  forall ev1 ty v1 ev2 v2,
  eventval_match ev1 ty v1 -> eventval_match ev2 ty v2 -> eventval_type ev1 = eventval_type ev2.
Proof.
  destruct 1; intros EV; inv EV; auto. 
Qed.

End EVENTVAL.

(** Invariance under changes to the global environment *)

Section EVENTVAL_INV.

Variables F1 V1 F2 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.

Hypothesis symbols_preserved:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

Lemma eventval_match_preserved:
  forall ev ty v,
  eventval_match ge1 ev ty v -> eventval_match ge2 ev ty v.
Proof.
  induction 1; econstructor; eauto. rewrite symbols_preserved; auto. 
Qed.

Lemma eventval_list_match_preserved:
  forall evl tyl vl,
  eventval_list_match ge1 evl tyl vl -> eventval_list_match ge2 evl tyl vl.
Proof.
  induction 1; constructor; auto. eapply eventval_match_preserved; eauto.
Qed.

Lemma eventval_valid_preserved:
  forall ev, eventval_valid ge1 ev -> eventval_valid ge2 ev.
Proof.
  unfold eventval_valid; destruct ev; auto. 
  intros [b A]. exists b; rewrite symbols_preserved; auto.
Qed.

End EVENTVAL_INV.

(** * Matching traces. *)

Section MATCH_TRACES.

Variables F V: Type.
Variable ge: Genv.t F V.

(** Matching between traces corresponding to single transitions.
  Arguments (provided by the program) must be equal.
  Results (provided by the outside world) can vary as long as they
  can be converted safely to values. *)

Inductive match_traces: trace -> trace -> Prop :=
  | match_traces_E0:
      match_traces nil nil
  | match_traces_syscall: forall id args res1 res2,
      eventval_valid ge res1 -> eventval_valid ge res2 -> eventval_type res1 = eventval_type res2 ->
      match_traces (Event_syscall id args res1 :: nil) (Event_syscall id args res2 :: nil)
  | match_traces_vload: forall chunk id ofs res1 res2,
      eventval_valid ge res1 -> eventval_valid ge res2 -> eventval_type res1 = eventval_type res2 ->
      match_traces (Event_vload chunk id ofs res1 :: nil) (Event_vload chunk id ofs res2 :: nil)
  | match_traces_vstore: forall chunk id ofs arg,
      match_traces (Event_vstore chunk id ofs arg :: nil) (Event_vstore chunk id ofs arg :: nil)
  | match_traces_annot: forall id args,
      match_traces (Event_annot id args :: nil) (Event_annot id args :: nil).

End MATCH_TRACES.

(** Invariance by change of global environment *)

Section MATCH_TRACES_INV.

Variables F1 V1 F2 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.

Hypothesis symbols_preserved:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

Lemma match_traces_preserved:
  forall t1 t2, match_traces ge1 t1 t2 -> match_traces ge2 t1 t2.
Proof.
  induction 1; constructor; auto; eapply eventval_valid_preserved; eauto.
Qed.

End MATCH_TRACES_INV.

(** An output trace is a trace composed only of output events,
  that is, events that do not take any result from the outside world. *)

Definition output_event (ev: event) : Prop :=
  match ev with
  | Event_syscall _ _ _ => False
  | Event_vload _ _ _ _ => False
  | Event_vstore _ _ _ _ => True
  | Event_annot _ _ => True
  end.
  
Fixpoint output_trace (t: trace) : Prop :=
  match t with
  | nil => True
  | ev :: t' => output_event ev /\ output_trace t'
  end.

(** * Semantics of volatile memory accesses *)

Definition block_is_volatile (F V: Type) (ge: Genv.t F V) (b: block) : bool :=
  match Genv.find_var_info ge b with
  | None => false
  | Some gv => gv.(gvar_volatile)
  end.

Inductive volatile_load (F V: Type) (ge: Genv.t F V):
                   memory_chunk -> mem -> expr_sym -> trace -> expr_sym -> Prop :=
| volatile_load_vol: forall addr chunk m b ofs id ev v
                       (MN: Mem.mem_norm m addr = Vptr b ofs)
                       (IB: Mem.in_bound_m (Int.unsigned ofs) m b)
                       (VOL: block_is_volatile ge b = true)
                       (FS: Genv.find_symbol ge id = Some b)
                       (EVM: eventval_match ge ev (AST.type_of_chunk chunk) v),
    volatile_load ge chunk m addr
                  (Event_vload chunk id ofs ev :: nil)
                  (Val.load_result chunk (Eval v))
| volatile_load_nonvol: forall addr chunk m b ofs v
                          (MN: Mem.mem_norm m addr = Vptr b ofs)
                          (VOL: block_is_volatile ge b = false)
                          (LOAD: Mem.load chunk m b (Int.unsigned ofs) = Some v),
    volatile_load ge chunk m addr E0 v.

Inductive volatile_store (F V: Type) (ge: Genv.t F V):
                  memory_chunk -> mem -> expr_sym -> expr_sym -> trace -> mem -> Prop :=
| volatile_store_vol:
    forall addr chunk m b ofs id ev v nv
      (MN: Mem.mem_norm m addr = Vptr b ofs)
      (IB: Mem.in_bound_m (Int.unsigned ofs) m b)
      (VOL: block_is_volatile ge b = true)
      (FS: Genv.find_symbol ge id = Some b)
      (MNv: Mem.mem_norm m (Val.load_result chunk v) = nv)
      (EVM: eventval_match ge ev (AST.type_of_chunk chunk) nv),
      volatile_store ge chunk m addr v (Event_vstore chunk id ofs ev :: nil) m
| volatile_store_nonvol:
    forall addr chunk m b ofs v m'
      (MN: Mem.mem_norm m addr = Vptr b ofs)
      (VOL: block_is_volatile ge b = false)
      (STORE: Mem.store chunk m b (Int.unsigned ofs) v = Some m'),
      volatile_store ge chunk m addr v E0 m'.

(** * Semantics of external functions *)

(** For each external function, its behavior is defined by a predicate relating:
- the global environment
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).
*)

Definition extcall_sem : Type :=
  forall (F V: Type), Genv.t F V -> list expr_sym -> mem -> trace -> expr_sym -> mem -> Prop.

(** We now specify the expected properties of this predicate. *)

Definition loc_out_of_bounds (m: mem) (b: block) (ofs: Z) : Prop :=
  ~Mem.perm m b ofs Max Nonempty.

Definition loc_not_writable (m: mem) (b: block) (ofs: Z) : Prop :=
  ~Mem.perm m b ofs Max Writable.

Definition loc_unmapped (f: meminj) (b: block) (ofs: Z): Prop :=
  f b = None.

Definition loc_out_of_reach (f: meminj) (m: mem) (b: block) (ofs: Z): Prop :=
  forall b0 delta,
  f b0 = Some(b, delta) -> ~Mem.perm m b0 (ofs - delta) Max Writable.

Definition inject_separated (f f': meminj) (m1 m2: mem): Prop :=
  forall b1 b2 delta,
  f b1 = None -> f' b1 = Some(b2, delta) ->
  ~Mem.valid_block m1 b1 /\ ~Mem.valid_block m2 b2.

Require Import ForgetNorm.


(* sv is independent from blocks in S *)
Definition independent S sv :=
  ExprEval.depends_on_blocks (fun b => S b = false) sv.

Definition independent_mv S mv :=
  match mv with
    Symbolic e t n => independent S e
  end.

Definition independent_m S m :=
  forall b (NS: S b = false) ofs n l
         (POS: n >= 0)
    (LB: Mem.loadbytes m b ofs n = Some l),
  Forall (independent_mv S) l.


Record extcall_properties (sem: extcall_sem)
                          (sg: signature) : Prop := mk_extcall_properties {

(** The return value of an external call must agree with its signature. *)
  ec_well_typed:
    forall F V (ge: Genv.t F V) vargs m1 t vres m2,
    sem F V ge vargs m1 t vres m2 ->
    wt vres (proj_sig_res sg);

(** The semantics is invariant under change of global environment that preserves symbols. *)
  ec_symbols_preserved:
    forall F1 V1 (ge1: Genv.t F1 V1) F2 V2 (ge2: Genv.t F2 V2) vargs m1 t vres m2,
    (forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) ->
    (forall b, block_is_volatile ge2 b = block_is_volatile ge1 b) ->
    sem F1 V1 ge1 vargs m1 t vres m2 ->
    sem F2 V2 ge2 vargs m1 t vres m2;

(** External calls cannot invalidate memory blocks.  (Remember that
  freeing a block does not invalidate its block identifier.) *)
  ec_valid_block:
     forall F V (ge: Genv.t F V) vargs m1 t vres m2 b,
    sem F V ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.valid_block m2 b;

(** External calls cannot increase the max permissions of a valid block.
    They can decrease the max permissions, e.g. by freeing. *)
  ec_max_perm:
    forall F V (ge: Genv.t F V) vargs m1 t vres m2 b ofs p,
    sem F V ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p;

  ec_perm:
    forall F V (ge: Genv.t F V) vargs m1 t vres m2,
      sem F V ge vargs m1 t vres m2 ->
      forall b,
      Mem.valid_block m1 b ->
      ~ Mem.is_dynamic_block m1 b ->
      forall ofs k p, Mem.perm m1 b ofs k p <-> Mem.perm m2 b ofs k p;

(** External call cannot modify memory unless they have [Max, Writable]
   permissions. *)
  ec_readonly:
    forall F V (ge: Genv.t F V) vargs m1 t vres m2,
    sem F V ge vargs m1 t vres m2 ->
    Mem.unchanged_on (loc_not_writable m1) m1 m2;

(** External call cannot modify memory unless they have [Max, Writable]
   permissions. *)
  ec_readonly':
    forall F V (ge: Genv.t F V) vargs m1 t vres m2,
    sem F V ge vargs m1 t vres m2 ->
    forall b ofs (VB: Mem.valid_block m1 b),
      loc_not_writable m1 b ofs ->
      Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m1)) =
      Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m2));
  
(** External calls must commute with memory injections,
  in the following sense. *)
  ec_mem_inject:
    forall ei (wf: wf_inj ei) F V (ge: Genv.t F V)
      vargs m1 t vres m2 f m1' vargs'
      (ABI: Mem.all_blocks_injected f m1),
      meminj_preserves_globals ge f ->
      sem F V ge vargs m1 t vres m2 ->
      Mem.inject true ei f m1 m1' ->
      list_ei ei f vargs vargs' ->
      exists f' vres' m2',
        sem F V ge vargs' m1' t vres' m2'
        /\ Mem.all_blocks_injected f' m2
        /\ ei f' vres vres'
        /\ Mem.inject true ei f' m2 m2'
        /\ Mem.unchanged_on (loc_unmapped f) m1 m2
        /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
        /\ inject_incr f f'
        /\ inject_separated f f' m1 m1' /\ 
        (exists C C',
            nb_boxes_dynamic m2 + C = nb_boxes_dynamic m1 + C' /\
            nb_boxes_dynamic m2' + C = nb_boxes_dynamic m1' + C' )%nat /\
        nb_boxes_static m1 = nb_boxes_static m2 /\
        nb_boxes_static m1' = nb_boxes_static m2' /\
        Mem.nb_extra m1 = Mem.nb_extra m2 /\
        Mem.nb_extra m1' = Mem.nb_extra m2';
  ec_mem_rel: 
    forall mr (wf: wf_mr mr) (wfn: wf_mr_norm mr) (F V: Type) m m' args args' (ge: Genv.t F V) t vres m2
    (MR: mem_rel mr m m')
    (LF2: list_forall2 mr args args')
    (EC: sem F V ge args m t vres m2),
    exists vres' m2',
      sem F V ge args' m' t vres' m2' /\
      mr vres vres' /\
      mem_rel mr m2 m2' /\ 
      (exists C C', Mem.nb_boxes_used_m m2 + C = Mem.nb_boxes_used_m m + C' /\
               Mem.nb_boxes_used_m m2' + C = Mem.nb_boxes_used_m m' + C')%nat /\
      Mem.nb_extra m = Mem.nb_extra m2 /\ 
      Mem.nb_extra m' = Mem.nb_extra m2';

  ec_mem_inject_forget:
    forall F V (ge : Genv.t F V) vargs m1 t vres m2 f m1' vargs'
      (IWB: inj_well_behaved f m1 m1')
      (MPG: meminj_preserves_globals ge f)
      (EC: sem F V ge vargs m1 t vres m2)
      (MINJ: Mem.inject true expr_inj_se f m1 m1')
      (EI: list_ei expr_inj_se f vargs vargs')
      (SEP: Forall (sep_inj m1 f) vargs),
    exists f' (vres' : expr_sym) (m2' : mem),
      sem F V ge vargs' m1' t vres' m2' /\
      inj_well_behaved f' m2 m2' /\ 
      expr_inj_se f' vres vres' /\
      Mem.inject true expr_inj_se f' m2 m2' /\
      Mem.unchanged_on (loc_unmapped f) m1 m2 /\
      Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' /\
      inject_incr f f' /\ 
      inject_separated f f' m1 m1' /\
      (exists C C',
          Mem.nb_boxes_used_m m2 + C = Mem.nb_boxes_used_m m1 + C' /\
          Mem.nb_boxes_used_m m2' + C = Mem.nb_boxes_used_m m1' + C' )%nat /\
      nb_boxes_static m1 = nb_boxes_static m2 /\
      nb_boxes_static m1' = nb_boxes_static m2' /\
      Mem.nb_extra m1 = Mem.nb_extra m2 /\
      Mem.nb_extra m1' = Mem.nb_extra m2';

(** External calls produce at most one event. *)
  ec_trace_length:
    forall F V ge vargs m t vres m',
    sem F V ge vargs m t vres m' -> (length t <= 1)%nat;

(** External calls must be receptive to changes of traces by another, matching trace. *)
  ec_receptive:
    forall F V ge vargs m t1 vres1 m1 t2,
    sem F V ge vargs m t1 vres1 m1 -> match_traces ge t1 t2 ->
    exists vres2, exists m2, sem F V ge vargs m t2 vres2 m2;

(** External calls must be deterministic up to matching between traces. *)
  ec_determ:
    forall F V ge vargs m t1 vres1 m1 t2 vres2 m2,
    sem F V ge vargs m t1 vres1 m1 -> sem F V ge vargs m t2 vres2 m2 ->
    match_traces ge t1 t2 /\ (t1 = t2 -> vres1 = vres2 /\ m1 = m2);

  ec_bounds_mask:
    forall F V ge vargs m t1 vres1 m1,
      sem F V ge vargs m t1 vres1 m1 ->
      forall b, Mem.valid_block m b -> ~ Mem.is_dynamic_block m b ->
           Mem.bounds_of_block m b = Mem.bounds_of_block m1 b /\
           Mem.mask m b = Mem.mask m1 b /\ ~ Mem.is_dynamic_block m1 b;
  ec_preserves_dynamic:
    forall F V ge vargs m1 t1 vres m2
      (EC: sem F V ge vargs m1 t1 vres m2)
      b
      (VB: Mem.valid_block m1 b),
      (Mem.is_dynamic_block m1 b <-> Mem.is_dynamic_block m2 b)
  ;
  ec_dep:
    forall F V (ge: Genv.t F V) vargs m t vres m'
         (EC: sem F V ge vargs m t vres m')
         (S: block -> bool)
         (Invalid: forall b, ~ Mem.valid_block m b -> S b = true)
         (GlobNotS: forall id b, Genv.find_symbol ge id = Some b -> S b = false)
         (DEP: Forall (independent S) vargs)
         (DEPmem: independent_m S m),
    exists (S': block -> bool),
      (forall b, S' b = true -> S b = true) /\
      (forall b,
          Mem.valid_block m b -> S b = true ->
          (forall ofs n, Mem.loadbytes m b ofs n = Mem.loadbytes m' b ofs n)) /\
      independent_m S' m'/\
      independent S' vres /\
      (forall b, S' b = false -> S b = false \/ (Ple (Mem.nextblock m) b /\ Plt b (Mem.nextblock m')))
}.

(** ** Semantics of volatile loads *)

Inductive volatile_load_sem (chunk: memory_chunk) (F V: Type) (ge: Genv.t F V):
              list expr_sym -> mem -> trace -> expr_sym -> mem -> Prop :=
  | volatile_load_sem_intro: forall addr m t v
                               (VOLLOAD: volatile_load ge chunk m addr t v),
      volatile_load_sem chunk ge (addr :: nil) m t v m.


Lemma volatile_load_preserved:
  forall F1 V1 (ge1: Genv.t F1 V1) F2 V2 (ge2: Genv.t F2 V2) chunk m addr b ofs t v
         (MN: Mem.mem_norm m addr = Vptr b ofs)
         (GFS: forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id)
         (IV: forall b, block_is_volatile ge2 b = block_is_volatile ge1 b)
         (VOLLOAD: volatile_load ge1 chunk m addr t v),
    volatile_load ge2 chunk m addr t v.
Proof.
  intros. inv VOLLOAD; econstructor; eauto.
  rewrite GFS; auto.
  eapply eventval_match_preserved; eauto.
Qed.

Remark meminj_preserves_block_is_volatile:
  forall F V (ge: Genv.t F V) f b1 b2 delta,
  meminj_preserves_globals ge f ->
  f b1 = Some (b2, delta) ->
  block_is_volatile ge b2 = block_is_volatile ge b1.
Proof.
  intros. destruct H as [A [B C]]. unfold block_is_volatile. 
  case_eq (Genv.find_var_info ge b1); intros.
  exploit B; eauto. intro EQ; rewrite H0 in EQ; inv EQ. rewrite H; auto.
  case_eq (Genv.find_var_info ge b2); intros.
  exploit C; eauto. intro EQ. congruence.
  auto.
Qed.

Lemma load_result_ei:
  forall ei (wf: wf_inj ei) f vl vl' chunk,
    ei f vl vl' ->
    ei f (Val.load_result chunk vl) (Val.load_result chunk vl').
Proof.
  intros. inv wf.
  assert (Decidable.decidable (chunk <> Many32 /\ chunk <> Many64)).
  red; des chunk; eauto.
  destruct H0.
  assert (forall v', ei f (Eval Vundef) v').
  {
    intros; apply wf_inj_undef.
    reflexivity.
  }
  des chunk; eauto.
  des chunk. 
  repeat destr_no_dep; eauto.
  destruct (wf_typ _ _ _ H).
  apply wf_inj_undef; auto. rewrite H0 in w; congruence.
  destruct (wf_typ _ _ _ H).
  apply wf_inj_undef; auto. rewrite H0 in w; congruence.
  apply wf_inj_undef; auto. reflexivity.
  apply wf_inj_undef; auto. reflexivity.
Qed.



Lemma volatile_load_inject:
  forall sm ei (wf: wf_inj ei) F V (ge: Genv.t F V)  f chunk m addr addr' t v m'
    (ABI: Mem.all_blocks_injected f m)
    (MPG: meminj_preserves_globals ge f)
    (VOLLOAD: volatile_load ge chunk m addr t v)
    (EI: ei f addr addr')
    (MINJ: Mem.inject sm ei f m m'),
  exists v', volatile_load ge chunk m' addr' t v' /\ ei f v v'.
Proof.
  intros. inv VOLLOAD. 
  - 
    exploit (proj1 MPG); eauto. intros EQ.
    exists (Val.load_result chunk (Eval v0)); split.
    + econstructor; eauto.
      generalize (Mem.norm_inject _ _ wf _ _ _ _ (Vptr b ofs) _ ABI MINJ EI).
      intro A. trim A. congruence.
      destruct (A MN) as [A1 A2]; clear A.
      rewrite <- MN in A2. eapply (Mem.ei_vi_norm _ ei) in A2; eauto.
      rewrite MN in A2. inv A2. 
      rewrite EQ in FB. inv FB.
      rewrite Int.add_zero. eauto.
      eapply Mem.mi_bounds in IB; eauto. rewrite Z.add_0_r in IB. eauto. inv MINJ; eauto.
    + 
      apply load_result_ei; auto.
      exploit eventval_match_inject_2; eauto.
      apply ei_val; auto.
  -
    generalize (Mem.norm_inject _ _ wf _ _ _ _ (Vptr b ofs) _ ABI MINJ EI).
    intro A; destruct A as [A1 A2]; eauto. congruence.
    rewrite <- MN in A2. eapply (Mem.ei_vi_norm _ ei) in A2; eauto.  rewrite MN in A2; inv A2.
    generalize (Mem.load_inject _ ei wf f m m' chunk b (Int.unsigned ofs) b2 delta v MINJ LOAD FB); eauto. 
    simpl; intros [v' [C D]]. exists v'; split; auto. 
    econstructor; eauto. rewrite <- VOL. 
    eapply meminj_preserves_block_is_volatile; eauto. 
    rewrite <- C. f_equal.
    rewrite <- (Int.repr_unsigned ofs) at 1.
    rewrite Val.int_add_repr.
    apply Int.unsigned_repr.
    inv MINJ. 
    refine ( (Mem.mi_representable _ _ _ _ _ mi_inj _ _ _ ofs FB (or_introl _)) _).
    apply Mem.load_valid_access in LOAD.
    eapply Mem.valid_access_perm in LOAD; eauto.
    eapply Mem.perm_implies; eauto. constructor.
    eapply mi_delta_pos; eauto.
Qed.

Lemma volatile_load_receptive:
  forall F V (ge: Genv.t F V) chunk m addr t1 t2 v1,
  volatile_load ge chunk m addr t1 v1 -> match_traces ge t1 t2 ->
  exists v2, volatile_load ge chunk m addr t2 v2.
Proof.
  intros. inv H; inv H0.
  exploit eventval_match_receptive; eauto. intros [v' EM].
  exists (Val.load_result chunk (Eval v')). econstructor; eauto.
  exists v1; econstructor; eauto.
Qed.

Lemma type_load_result:
  forall c v,
    wt (Val.load_result c v) (type_of_chunk c).
Proof.
  generalize isTint isTlong.
  intros.
  destruct (wt_expr_dec v (styp_of_ast (type_of_chunk c))).
  exploit Val.load_result_type; eauto.
  des c; try now (
               left; eexists; split; [|apply subtype_refl]; destr).
  des c; try now (right; intro; dex; destr).
  repeat destr.
  left; exists AST.Tsingle; destr.
  left; exists AST.Tsingle; destr.
  destruct (wt_expr_dec v Tint). left; exists AST.Tint; destr.
  destruct (wt_expr_dec v Tsingle). left; exists AST.Tsingle; destr.
  destruct (wt_expr_dec v Tfloat). left; exists AST.Tfloat; destr.
  right; intro; dex. des t.
Qed.

Lemma type_or_undef:
  forall v t t',
    wt_expr v t ->
    wt_expr v t' ->
    t = t' \/ v = Eval Vundef.
Proof.
  induction v; simpl; intros; eauto.
  des v; des t; des t'.
  subst; auto.
  intuition.
  des u; des s; des t; des t'; try des p.
  des b; des s; des s0; des t; des t'.
Qed.

Lemma volatile_load_inj:
  forall sm ei (wf: wf_inj ei) F V f (ge0: Genv.t F V)
    (MPG : meminj_preserves_globals ge0 f)
    addr chunk m2 t vres
    (VOLLOAD : volatile_load ge0 chunk m2 addr t vres)
    m1'
    (IWB : inj_well_behaved f m2 m1')
    (MINJ : Mem.inject sm ei f m2 m1')
    b (EI0 : ei f addr b)
    (SEP : sep_inj m2 f addr),
  exists (vres' : expr_sym),
     volatile_load  ge0 chunk m1' b t vres' /\
     ei f vres vres'.
Proof.
  intros.
  generalize (forget_norm _ _ wf _ _ _ MINJ IWB _ _ EI0 SEP); intro VI.
  inv VOLLOAD.
  + exploit (proj1 MPG); eauto. intros EQ.
    exists (Val.load_result chunk (Eval v)); repSplit; eauto with mem.
    * econstructor; eauto.
      rewrite MN in VI. inv VI.
      exploit iwb_o2o; eauto.
      intros; subst. rewrite Int.add_zero in H.
      rewrite FB in EQ; inv EQ; auto.
      rewrite Int.add_zero; auto.
      eapply Mem.mi_bounds in IB; eauto. rewrite Z.add_0_r in IB. eauto. inv MINJ; eauto.

    * apply load_result_ei; auto. exploit eventval_match_inject_2; eauto.
      apply ei_val; auto.
  + rewrite MN in VI; inv VI.
    exploit iwb_o2o; eauto.
    intros; subst. rewrite Int.add_zero in H.
    generalize (Mem.load_inject _ _ wf _ _ _ _ _ _ _ _ _ MINJ LOAD FB).
    simpl; intros [v' [C D]]. exists v'; repSplit; eauto with mem.
    econstructor; eauto. rewrite <- VOL. eapply meminj_preserves_block_is_volatile; eauto.
    rewrite <- C.
    rewrite Zplus_0_r; auto.
Qed.

Lemma same_eval_vptr_vint:
  forall i b o,
    ~ same_eval (Eval (Vptr b o)) (Eval (Vint i)).
Proof.
  intros i b o SE.
  generalize (SE (fun _ => Int.zero) (fun _ _ => Byte.zero)).
  generalize (SE (fun _ => Int.one) (fun _ _ => Byte.zero)). simpl.
  intros A B.
  rewrite <- A in B. apply inj_vint in B.
  rewrite ! (Int.add_commut _ o) in B. apply ExprEval.int_add_eq_l in B.
  discriminate.
Qed.

Lemma same_eval_vptr_vlong:
  forall i b o,
    ~ same_eval (Eval (Vptr b o)) (Eval (Vlong i)).
Proof.
  intros i b o SE.
  generalize (SE (fun _ => Int.zero) (fun _ _ => Byte.zero)). destr.
Qed.

Lemma same_eval_vptr_vfloat:
  forall i b o,
    ~ same_eval (Eval (Vptr b o)) (Eval (Vfloat i)).
Proof.
  intros i b o SE.
  generalize (SE (fun _ => Int.zero) (fun _ _ => Byte.zero)). destr.
Qed.

Lemma same_eval_vptr_vsingle:
  forall i b o,
    ~ same_eval (Eval (Vptr b o)) (Eval (Vsingle i)).
Proof.
  intros i b o SE.
  generalize (SE (fun _ => Int.zero) (fun _ _ => Byte.zero)). destr.
Qed.

Lemma same_eval_vptr:
  forall b o b' o'
    (SE: same_eval (Eval (Vptr b o)) (Eval (Vptr b' o'))),
    b = b' /\ o = o'.
Proof.
  intros.
  generalize (SE (fun bb => if peq bb b then Int.one
                         else if peq bb b' then (Int.repr 2)
                              else Int.zero) (fun _ _ => Byte.zero)).
  generalize (SE (fun bb =>  Int.zero) (fun _ _ => Byte.zero)). simpl.
  rewrite peq_true.
  destr.
  - subst. intros. apply inj_vint in H0.
    apply ExprEval.int_add_eq_l in H0. auto.
  - rewrite peq_true. intros. 
    apply inj_vint in H.
    apply inj_vint in H0.
    apply ExprEval.int_add_eq_l in H. subst.
    rewrite ! (Int.add_commut _ o') in H0. apply ExprEval.int_add_eq_l in H0.
    discriminate.
Qed.

Lemma volatile_store_inj:
  forall sm ei (wf: wf_inj ei) F V f (ge0: Genv.t F V)
    (MPG : meminj_preserves_globals ge0 f)
    m1 m1'
    (IWB: inj_well_behaved f m1 m1')
    (MINJ : Mem.inject sm ei f m1 m1')
    addr v t m2 chunk
    (VOLSTORE : volatile_store ge0 chunk m1 addr v t m2)
    b
    (EI0 : ei f addr b) b0
    (EI : ei f v b0)
    (SEP1 : sep_inj m1 f addr)
    (SEP2 : sep_inj m1 f v),
  exists m2',
    volatile_store ge0  chunk m1' b b0 t m2' /\
    Mem.inject sm ei f m2 m2' /\
    Mem.unchanged_on (loc_unmapped f) m1 m2 /\
    Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'.
Proof.
  intros.
  generalize (forget_norm _ _ wf _ _ _ MINJ IWB _ _ EI0 SEP1); intro VI.
  inv VOLSTORE.
  + exploit (proj1 MPG); eauto. intros EQ.
    exists  m1'; repSplit; eauto with mem.
    econstructor; eauto.
    rewrite MN in VI. inv VI.
    exploit iwb_o2o; eauto.
    intros; subst. rewrite Int.add_zero in *.
    rewrite FB in EQ; inv EQ; auto.
    eapply Mem.mi_bounds in IB; eauto. rewrite Z.add_0_r in IB. eauto. inv MINJ; eauto.
    generalize (forget_norm _ _ wf _ _ _ MINJ IWB _ _ (load_result_ei wf _ _ _ chunk EI)
                            (sep_inj_load_result _ _ _ SEP2 chunk)); intro VI'.
    inv VI'; try rewrite <- H0 in EVM; auto.
    inv EVM.
    exploit (proj1 MPG). apply FS0. intro EQ'; rewrite EQ' in FB. inv FB.
    rewrite Int.add_zero. constructor. auto.
    inv EVM.
  + rewrite MN in VI; inv VI.
    exploit Mem.store_mapped_inject; eauto. intros [n2 [A B]].
    exploit iwb_o2o; eauto.
    intros; subst. rewrite Int.add_zero in H.
    exists n2; repSplit; eauto with mem.
    * econstructor; eauto.
      rewrite <- VOL. eapply meminj_preserves_block_is_volatile; eauto.
      rewrite <- A.
      rewrite Zplus_0_r; auto.
    * eapply Mem.store_unchanged_on; eauto.
      unfold loc_unmapped. rewrite FB. congruence.
    * eapply Mem.store_unchanged_on; eauto.
      unfold loc_out_of_reach. intros. intro.
      specialize (H1 _ _ FB). apply H1.
      rewrite Z.sub_0_r.
      eapply Mem.store_valid_access_3 in STORE.
      destruct STORE as [STORE C].
      eapply Mem.perm_implies.
      eapply Mem.perm_cur_max.
      eapply STORE. omega. constructor.
Qed.

Lemma load_result_same:
  forall a b em sv,
    eSexpr a em sv = eSexpr b em sv ->
    forall chunk,
      eSexpr a em (Val.load_result chunk sv) =
      eSexpr b em (Val.load_result chunk sv).
Proof.
  intros; des chunk; repeat destr.
Qed.

Lemma psa_independent:
  forall S bytes
    (LB : Forall (independent_mv S) bytes),
    independent S (proj_symbolic_aux_le bytes).
Proof.
  induction 1; simpl; intros; eauto.
  repeat red; destr.
  repeat red; simpl; intros.
  specialize (IHLB _ _ H0 u). rewrite IHLB.
  red in H. des x. specialize (H a a' H0 u).
  rewrite ! gnp_rew, H. auto.
Qed.

Lemma decode_val_independent:
  forall S bytes chunk
    (LB : Forall (independent_mv S) bytes),
    independent S (decode_val chunk bytes).
Proof.
  intros.
  cut (independent S (proj_symbolic_le bytes)). intro I.
  unfold decode_val, from_bits.
  des chunk;
    repeat destr;
    try solve [red; red; simpl; intros a a' EQ u;
               try rewrite (I a a' EQ u); auto].
  unfold proj_symbolic_le.
  unfold rev_if_be; destr.
  apply psa_independent.
  apply Forall_rev; auto.
  rewrite rev_involutive. auto.
  apply psa_independent. auto.
Qed.

Lemma norm_independent:
  forall m e b ofs
    (MN: Mem.mem_norm m e = Vptr b ofs)
    S
    (INDEP: independent S e),
    S b = false.
Proof.
  intros.
  des (S b). exfalso.
  destruct (Mem.exists_two_cms m b) as (cm & cm' & COMP & COMP' & DIFF & SAME).
  generalize (INDEP cm cm'). intro A; trim A. intros ; apply SAME; destr.
  generalize (Mem.norm_correct m e); rewrite MN; intro IN. inv IN.
  generalize (eval_ok_m cm  Normalise.dummy_em COMP).
  generalize (eval_ok_m cm' Normalise.dummy_em COMP').
  simpl.
  intros B C; inv B; inv C.
  rewrite A in H2. rewrite <- H2 in H1.
  apply NormaliseSpec.inj_vint in H1.
  rewrite ! (Int.add_commut _ ofs) in H1.
  apply int_add_eq_l in H1. congruence.
Qed.
Require Import Classical_Prop.
Lemma volatile_load_ok:
  forall chunk,
    extcall_properties (volatile_load_sem chunk) 
                       (mksignature (AST.Tint :: nil) (Some (AST.type_of_chunk chunk)) cc_default).
Proof.
  intros; constructor; intros.
  - (* well typed *) 
    unfold proj_sig_res; simpl. inv H. inv VOLLOAD.
    apply type_load_result.
    eapply Mem.load_type; eauto.
  - (* symbols *)
    inv H1. inv VOLLOAD; econstructor; econstructor; eauto.
    rewrite H; auto.
    inv EVM; econstructor; eauto. rewrite H; auto.
  - (* valid blocks *)
    inv H; auto.
  - (* max perms *)
    inv H; auto.
  - inv H.  tauto.
  - (* readonly *)
    inv H. apply Mem.unchanged_on_refl.
  - inv H; auto.
  (*-  (* mem extends *) *)
  (* inv H. inv H1. inv H8. inv H6. simpl in *. rewrite Val.apply_inj_id in inj_ok. inv inj_ok. *)
  (* exploit volatile_load_extends; eauto. intros [v' [A B]]. *)
  (* exists v'; exists m1'; intuition.  *)
  (* eapply volatile_load_sem_intro; eauto. econstructor; auto. *)
  - (* mem injects *) 
    inv H0. inv H2. inv LEI. 
    exploit volatile_load_inject; eauto. 
    intros [v'0 [A B]]. 
    exists f, v'0; exists m1'; intuition. constructor; auto.
    red. destr.
    exists O, O; repSplit; omega.
  - inv EC. inv LF2. inv H3. inv VOLLOAD.
    + eexists; eexists; split; eauto.
      econstructor; eauto.
      econstructor; eauto.
      rewrite (mem_rel_norm mr _ _ addr MR) in MN.
      generalize (wfn m' _ _ H1). rewrite MN.
      intro A; apply (mr_val_refl _ wf) in A; auto.
      congruence.
      rewrite <- mem_lessdef_in_bound_m. 2: eauto. eauto.
      split. apply (mr_refl _ wf). split. auto.
      repSplit; auto.
      exists O, O. 
      lia.
    + eapply mem_rel_load in LOAD; eauto.
      destruct LOAD as [v' [A B]].
      exists v'; exists m'.
      split. econstructor; eauto. econstructor; eauto.
      rewrite (mem_rel_norm mr _ _ addr MR) in MN.
      generalize (wfn m' _ _ H1). rewrite MN.
      intro C; apply (mr_val_refl _ wf) in C; auto.
      congruence.
      split; auto. split; auto.
      repSplit; auto. exists O, O; lia.
  - inv EC. inv EI. inv LEI. inv SEP.
    exploit volatile_load_inj; eauto.
    intros [vres' [A B]].
    exists f, vres', m1'; repSplit; auto with mem.
    econstructor; auto.
    red; destr.
    exists O, O. lia.
  - (* trace length *)
    inv H; inv VOLLOAD; simpl; omega.
  - (* receptive *)
    inv H. exploit volatile_load_receptive; eauto. intros [v3 A].
    exists v3; exists m1; econstructor; eauto.
  - (* determ *)
    inv H; inv H0.
    inv VOLLOAD; inv VOLLOAD0; try congruence.
    + rewrite MN in MN0; inv MN0.
      assert (id = id0) by (eapply Genv.genv_vars_inj; eauto). subst id0.
      split. constructor.
      eapply eventval_match_valid; eauto.
      eapply eventval_match_valid; eauto.
      eapply eventval_match_same_type; eauto.
      intros EQ; inv EQ. 
      assert (v = v0) by (eapply eventval_match_determ_1; eauto).
      split; auto.
      congruence. 
    + 
      split. constructor. intuition congruence.
  - inv H. auto.
  - inv EC. tauto.
  - inv EC.
    exists S; repSplit; auto.
    inv VOLLOAD.
    red; red; inv EVM; try solve [des chunk].
    intros.
    apply load_result_same. simpl.
    rewrite H; auto. eapply GlobNotS; eauto.
    eapply Mem.load_loadbytes in LOAD.
    destruct LOAD as (bytes & LB & EQ). subst.
    eapply DEPmem in LB.
    apply decode_val_independent; auto.
    eapply norm_independent; eauto. inv DEP; auto.
    des chunk; lia.
Qed.

Inductive volatile_load_global_sem (chunk: memory_chunk) (id: ident) (ofs: int)
          (F V: Type) (ge: Genv.t F V):
  list expr_sym -> mem -> trace -> expr_sym -> mem -> Prop :=
| volatile_load_global_sem_intro: forall b t v m
                                    (FS: Genv.find_symbol ge id = Some b)
                                    (VOLLOAD: volatile_load ge chunk m (Eval (Vptr b ofs)) t v),
    volatile_load_global_sem chunk id ofs ge nil m t v m.

Remark volatile_load_global_charact:
  forall chunk id ofs (F V: Type) (ge: Genv.t F V) vargs m t vres m',
  volatile_load_global_sem chunk id ofs ge vargs m t vres m' <->
  exists b,
    Genv.find_symbol ge id = Some b /\ volatile_load_sem chunk ge (Eval (Vptr b ofs) :: vargs) m t vres m'.
Proof.
  intros; split.
  intros. inv H. exists b.  split; auto.
  econstructor; eauto.
  intros [b [sv P]]. inv P. econstructor; eauto.
Qed.

Lemma volatile_load_global_ok:
  forall chunk id ofs,
  extcall_properties (volatile_load_global_sem chunk id ofs) 
                     (mksignature nil (Some (AST.type_of_chunk chunk)) cc_default).
Proof.
  intros; constructor; intros.
- (* well typed *)
  unfold proj_sig_res; simpl. inv H. inv VOLLOAD. 
  apply type_load_result.
  exploit Mem.load_type; eauto. 
- (* symbols *)
  inv H1. inv VOLLOAD; econstructor; eauto; try econstructor; eauto; try rewrite H; eauto.
  inv EVM; econstructor; eauto.
  rewrite H; auto.
- (* valid blocks *)
  inv H; auto.
- (* max perm *)
  inv H; auto.
- inv H; tauto.
- (* readonly *)
  inv H. apply Mem.unchanged_on_refl.
- inv H; auto.
(* - (* extends *) *)
(*   inv H. inv H1. exploit volatile_load_extends; eauto. intros [v' [A B]]. *)
(*   exists v'; exists m1'; intuition. econstructor; eauto. *)
- (* inject *)
  inv H0. inv H2. 
  assert (ei f (Eval (Vptr b ofs)) (Eval (Vptr b ofs))).
  {
    apply vi_ei.    auto. simpl. 
    unfold Val.inj_ptr.
    erewrite (proj1 H); eauto.
    rewrite Int.add_zero. auto.
  }
  generalize (volatile_load_inject wf _ ABI H VOLLOAD H0 H1).
  intros [v' [A B]].
  exists f, v'; exists m1'; intuition. econstructor; eauto.
  red; destr.
  exists O, O; repSplit; omega.
- inv EC. inv LF2. inv VOLLOAD.
  + eexists; eexists; split; eauto.
    econstructor; eauto.
    econstructor; eauto.
    rewrite <- MN.
    symmetry.
    eapply mem_rel_norm; eauto.
    rewrite <- mem_lessdef_in_bound_m. 2: eauto. eauto.
    split. apply (mr_refl _ wf). auto. split; auto.
    repSplit; auto. exists O,O; lia.
  + eapply mem_rel_load in LOAD; eauto.
    destruct LOAD as [v' [A B]].
    eexists; eexists.
    split. econstructor; eauto. econstructor; eauto.
    rewrite <- MN.
    symmetry.
    eapply mem_rel_norm; eauto. split; auto.
    split; auto.
    repSplit; auto. exists O,O; lia. 
- inv EC. inv EI. clear SEP.
  exploit volatile_load_inj; eauto.
  apply vi_ei; auto; simpl; unfold Val.inj_ptr.
  erewrite (proj1 MPG); eauto.
  red; intros. intro DEP; apply depends_ptr in DEP; subst.
  exploit (proj1 MPG); eauto. congruence.
  apply Mem.exists_two_cms.
  intros [vres' [A B]]. exists f, vres', m1'; repSplit; auto with mem.
  econstructor; eauto. rewrite Int.add_zero in A; auto.  red; destr.
  exists O, O; lia.
- (* trace length *)
  inv H; inv VOLLOAD; simpl; omega.
- (* receptive *)
  inv H. exploit volatile_load_receptive; eauto. intros [v2 A].
  exists v2; exists m1; econstructor; eauto.
- (* determ *)
  inv H; inv H0.
  rewrite FS in FS0; inv FS0.
  eapply ec_determ. eapply volatile_load_ok; eauto.
  econstructor; eauto. 
  econstructor; eauto.
- inv H. auto.
- inv EC. tauto.
- inv EC.
  exists S; repSplit; auto.
  inv VOLLOAD.
  red; red; inv EVM; try solve [des chunk].
  intros.
  apply load_result_same. simpl.
  rewrite H; auto. eapply GlobNotS; eauto.
  eapply Mem.load_loadbytes in LOAD.
  destruct LOAD as (bytes & LB & EQ). subst.
  eapply DEPmem in LB.
  apply decode_val_independent; auto.
  rewrite Mem.norm_val in MN. inv MN. eapply GlobNotS; eauto.
  des chunk; lia.
Qed.

(** ** Semantics of volatile stores *)

Inductive volatile_store_sem (chunk: memory_chunk) (F V: Type) (ge: Genv.t F V):
              list expr_sym -> mem -> trace -> expr_sym -> mem -> Prop :=
  | volatile_store_sem_intro: forall addr  m1 v t m2 
                                (VOLSTORE: volatile_store ge chunk m1 addr v t m2),
      volatile_store_sem chunk ge (addr :: v :: nil) m1 t (Eval Vundef) m2.

Lemma volatile_store_preserved:
  forall F1 V1 (ge1: Genv.t F1 V1) F2 V2 (ge2: Genv.t F2 V2) chunk m1 addr b ofs v t m2
         (MN: Mem.mem_norm m1 addr = Vptr b ofs)
         (GFS: forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id)
         (IV: forall b, block_is_volatile ge2 b = block_is_volatile ge1 b)
         (VS: volatile_store ge1 chunk m1 addr v t m2),
    volatile_store ge2 chunk m1 addr v t m2.
Proof.
  intros. inv VS; econstructor; eauto.
  rewrite GFS; auto.
  eapply eventval_match_preserved; eauto.
Qed.

Lemma volatile_store_readonly:
  forall F V (ge: Genv.t F V) chunk1 m1 addr v t m2
    (VS: volatile_store ge chunk1 m1 addr v t m2),
  Mem.unchanged_on (loc_not_writable m1) m1 m2.
Proof.
  intros. inv VS.
  apply Mem.unchanged_on_refl.
  eapply Mem.store_unchanged_on; eauto. 
  exploit Mem.store_valid_access_3; eauto. intros [P Q].
  intros i ENC.
  unfold loc_not_writable.
  red; intros PERM. elim PERM. 
  apply Mem.perm_cur_max. apply P. auto. 
Qed.

Lemma wt_gt:
  forall v v',
    (forall t, wt_expr v t <-> wt_expr v' t) ->
    get_type v = get_type v'.
Proof.
  unfold get_type; repeat destr_no_dep; try rewrite H in *; destr.
Qed.

Lemma volatile_store_inject:
  forall sm ei (wf: wf_inj ei) F V (ge: Genv.t F V) f chunk m1 bofs v t m2 m1' bofs' v'
    (ABI:Mem.all_blocks_injected f m1)
    (MPG: meminj_preserves_globals ge f)
    (VS: volatile_store ge chunk m1 bofs v t m2)
    (EIad: ei f bofs bofs')
    (EI: ei f v v')
    (MINJ: Mem.inject sm ei f m1 m1'),
  exists m2',
    volatile_store ge chunk m1' bofs' v' t m2'
    /\ Mem.inject sm ei f m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'.
Proof.
  intros. inv VS. 
  - generalize (Mem.norm_inject_val' _ _ wf _ _ _ _ _ ABI MINJ EIad).
    rewrite MN. intro A; inv A.
    erewrite (proj1 MPG) in FB; eauto. inv FB. rewrite Int.add_zero in H.
    exists m1'. intuition.
    econstructor; eauto.
    exploit (proj1 MPG); eauto. intro FB.
    eapply Mem.mi_bounds in IB; eauto. rewrite Z.add_0_r in IB. eauto. inv MINJ; eauto.
    generalize (Mem.norm_inject_val' _ _ wf _ _ _ _ _  ABI MINJ
                                     (load_result_ei wf _ _ _ chunk EI)).
    intro VI'.
    inv VI'; try rewrite <- H1 in EVM; auto.
    inv EVM.
    exploit (proj1 MPG); eauto. intro EQ'; rewrite EQ' in FB. inv FB.
    rewrite Int.add_zero. constructor. auto.
    inv EVM. 
  - generalize (Mem.norm_inject _ _ wf _ _ _ _  (Vptr b ofs) _ ABI
                               MINJ EIad).
    intro A; destruct A  as [MNU EI']; eauto. congruence.
    rewrite <- MN in EI'. eapply (Mem.ei_vi_norm _ ei) in EI'; eauto.  rewrite MN in EI'; inv EI'.
    destruct (Mem.store_mapped_inject 
                _ _ wf _ _ _ _ _ _ _ _ _ _
                _ MINJ STORE FB EI) 
      as [m2' [B C]]; eauto. destr.
    exists m2'; intuition.
    + econstructor; eauto.
      * rewrite <- VOL. eapply meminj_preserves_block_is_volatile; eauto.
      * rewrite <- B. f_equal.
        inv MINJ.
        generalize (Mem.mi_representable _ _ _ _ _ mi_inj
                                         _ _ _ ofs FB).
        intro D. trim D.
        left.
        apply Mem.store_valid_access_3 in STORE.
        destruct STORE as [STORE _].
        apply Mem.perm_cur_max.
        eapply Mem.perm_implies.
        apply STORE. destruct chunk; simpl; omega.
        constructor.
        trim D.
        eapply mi_delta_pos; eauto.
        unfold Int.add.
        rewrite (Int.unsigned_repr delta).
        rewrite Int.unsigned_repr. auto. auto.
        apply mi_delta_pos in FB. generalize (Int.unsigned_range_2 ofs). omega.
    + eapply Mem.store_unchanged_on; eauto.
      unfold loc_unmapped; intros. congruence.
    + eapply Mem.store_unchanged_on; eauto.
      unfold loc_out_of_reach; intros. red; intros.
      assert (EQ: Int.unsigned (Int.add ofs (Int.repr delta)) = Int.unsigned ofs + delta)
        by (eapply Mem.address_inject; eauto with mem).
      eelim H1; eauto.
      exploit Mem.store_valid_access_3. eexact STORE. intros [P Q].
      apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
      apply P. omega.
Qed.

Lemma volatile_store_receptive:
  forall F V (ge: Genv.t F V) chunk m addr v t1 m1 t2,
  volatile_store ge chunk m addr v t1 m1 -> match_traces ge t1 t2 -> t1 = t2.
Proof.
  intros. inv H; inv H0; auto.  
Qed.

Lemma sval_of_val_inj:
  forall v v0, Eval v = Eval v0 -> v = v0.
Proof.
  intros; injection H. auto. 
Qed.

Lemma expr_inject_wt:
  forall f a b (ei: Val.expr_inject f a b)
    t (wtb: wt b t), wt a t.
Proof.
  intros.
  inv ei.
  des wtb; dex; destr. des e.
  erewrite <- Val.ai_type in w; eauto.
  left; eexists; split; eauto.
  right; intro; dex.
  erewrite Val.ai_type in H; eauto.
Qed.

Lemma volatile_store_sinj:
  forall F V (ge: Genv.t F V) chunk m m' a b t
    (VS: volatile_store ge chunk m a b t m')
    tm c d tm'
    (VS': volatile_store ge chunk tm c d t tm')
    f 
    (SINJ: inj_well_behaved f m tm),
    inj_well_behaved f m' tm'.
Proof.
  intros.
  eapply iwb_inv; eauto.
  - intros; inv VS; auto.
    eapply Mem.bounds_of_block_store; eauto.
  - intros; inv VS'; auto.
    eapply Mem.bounds_of_block_store; eauto.
  - intros; inv VS; auto.
    eapply Mem.mask_store; eauto.
  - intros; inv VS'; auto.
    eapply Mem.mask_store; eauto.
  - intros; inv VS'; auto. xomega.
    erewrite Mem.nextblock_store in H0; eauto. xomega.
Qed.

Lemma volatile_store_ok:
  forall chunk,
  extcall_properties (volatile_store_sem chunk) 
                     (mksignature (AST.Tint :: AST.type_of_chunk chunk :: nil) None cc_default).
Proof.
  intros; constructor; intros.
- (* well typed *)
  unfold proj_sig_res; simpl. inv H.
  left; eexists; split; destr; try apply subtype_refl; destr.
- (* symbols preserved *)
  inv H1. inv VOLSTORE; econstructor; eauto; econstructor; eauto.
  rewrite H; auto.
  inv EVM; econstructor; eauto. 
  rewrite <- FS0; auto. 
- (* valid block *)
  inv H. inv VOLSTORE. auto. eauto with mem.
- (* perms *)
  inv H. inv VOLSTORE. auto. eauto with mem.
- inv H. inv VOLSTORE. tauto.
  split. eapply Mem.perm_store_1; eauto.
  eapply Mem.perm_store_2; eauto.
- (* readonly *)
  inv H. eapply volatile_store_readonly; eauto.
- inv H. inv VOLSTORE; auto.
  generalize (Mem.store_valid_access_3 _ _ _ _ _ _ STORE). intros.
  rewrite (Mem.store_mem_contents _ _ _ _ _ _ STORE).
  rewrite Maps.PMap.gsspec. destr.
  rewrite Mem.setN_outside.  subst; auto.
  erewrite encode_val_length; eauto. rewrite <- size_chunk_conv. 
  destruct (zlt ofs (Int.unsigned ofs0)); auto. 
  destruct (zlt ofs (Int.unsigned ofs0 + size_chunk chunk)); auto.
  subst.
  des H. specialize (r ofs).
  red in H0. elim H0. apply Mem.perm_cur_max. apply r. omega.
- (* mem inject *)
  inv H0. inv H2. inv LEI. inv LEI0. 
  exploit volatile_store_inject; eauto.
  intros [m2' [A [B [C D]]]].
  exists f, (Eval Vundef); exists m2'; intuition. 
  constructor; auto. 
  + red; intros.
    eapply ABI; eauto.
    rewrite <- H0.
    inv VOLSTORE. auto.
    eapply Mem.bounds_of_block_store; eauto.
  + apply vi_ei; auto.
  + red; destr.
  + inv VOLSTORE; inv A. 
    exists O, O; repSplit; omega.
    rewrite (store_nb_dynamic _ _ _ _ _ _ STORE).
    rewrite (store_nb_dynamic _ _ _ _ _ _ STORE0).
    exists O, O; repSplit; omega.
  + inv VOLSTORE; inv A. auto.
    rewrite (store_nb_static _ _ _ _ _ _ STORE). auto.
  + inv A. auto.
    rewrite (store_nb_static _ _ _ _ _ _ STORE). auto.
  + inv VOLSTORE. auto.
    rewrite (Mem.nb_extra_store _ _ _ _ _ _ STORE). auto.
  + inv A. auto.
    rewrite (Mem.nb_extra_store _ _ _ _ _ _ STORE). auto.
- inv EC. inv LF2. inv H3. inv H5. inv VOLSTORE.
  + eexists; eexists; split; eauto.
    econstructor; eauto.
    econstructor; eauto.
    rewrite (mem_rel_norm mr _ _ addr MR) in MN.
    generalize (wfn m' _ _ H1). rewrite MN.
    intro A; apply (mr_val_refl _ wf) in A; auto.
    congruence. 
    rewrite <- mem_lessdef_in_bound_m; eauto.
    assert (mr (Val.load_result chunk v) (Val.load_result chunk b0)).
    {
      inv wf; des chunk; eauto.
      inv EVM. 
    }
    rewrite <- (mem_rel_norm mr _ _ _ MR).
    generalize (wfn m2 _ _ H).
    intro A. apply (mr_val_refl _ wf) in A; eauto. rewrite <- A. auto.
    intro E; rewrite E in *.
    inv EVM; try rename H4 into SE;
      try specialize (SE (fun _ => Int.zero) (fun _ _ => Byte.zero)); destr.
    split. apply (mr_refl _ wf). auto.
    split; auto.
    repSplit; auto. exists O,O; lia. 
  + eapply store_rel in STORE; eauto.
    destruct STORE as [m0 [A B]].
    eexists; eexists.
    split. econstructor; eauto. econstructor; eauto.
    rewrite <- MN.
    symmetry.
    generalize (wfn m' _ _ H1).
    rewrite (mem_rel_norm mr _ _ addr MR). 
    intro C; apply (mr_val_refl _ wf) in C; auto.
    rewrite <- (mem_rel_norm mr _ _ addr MR).  congruence.
    split. apply (mr_refl _ wf); auto. split; auto.
    rewrite (nb_blocks_used_rel _ _ _ MR).
    rewrite (nb_blocks_used_rel _ _ _ B).
    rewrite (Mem.nb_boxes_used_same m0 m').
    rewrite (mem_nb_extra_eq _ _ _ MR).
    rewrite (Mem.nb_extra_store _ _ _ _ _ _ A).
    rewrite (mem_nb_extra_eq _ _ _ B).
    split; auto. exists O, O. lia.
    eapply Mem.store_mk_block_list; eauto.
    symmetry; eapply Mem.nb_extra_store; eauto.

- inv EC. inv EI. inv LEI. inv LEI0. inv SEP. inv H2. inv H4.
  exploit volatile_store_inj; eauto.
  intros [m2' [A [B [C D]]]].
  exists f,(Eval Vundef), m2'; repSplit; eauto with mem.
  econstructor; eauto.
  + eapply volatile_store_sinj; eauto. 
  + apply vi_ei; simpl; auto.
  + red; destr.
  + inv VOLSTORE; inv A.
    exists O, O; repSplit; omega.
    unfold Mem.nb_boxes_used_m.
    rewrite (Mem.store_mk_block_list _ _ _ _ _ _ STORE).
    rewrite (Mem.store_mk_block_list _ _ _ _ _ _ STORE0).
    rewrite (Mem.nb_extra_store _ _ _ _ _ _ STORE).
    rewrite (Mem.nb_extra_store _ _ _ _ _ _ STORE0).
    exists O, O; repSplit; omega.
  + unfold nb_boxes_static.
    inv VOLSTORE; inv A. auto.
    rewrite (Mem.store_mk_block_list _ _ _ _ _ _ STORE).
    erewrite filter_ext. reflexivity.
    intros (bb,z). simpl. unfold is_static_block_b.
    Transparent Mem.store.
    unfold Mem.store in STORE; destr_in STORE; inv STORE.
    reflexivity.
  + unfold nb_boxes_static.
    inv A. auto.
    rewrite (Mem.store_mk_block_list _ _ _ _ _ _ STORE).
    erewrite filter_ext. reflexivity.
    intros (bb,z). simpl. unfold is_static_block_b.
    unfold Mem.store in STORE; destr_in STORE; inv STORE.
    reflexivity.
  + inv VOLSTORE. auto. rewrite (Mem.nb_extra_store _ _ _ _ _ _ STORE). auto.
  + inv A. auto. rewrite (Mem.nb_extra_store _ _ _ _ _ _ STORE). auto.
    
- (* trace length *)
  inv H; inv VOLSTORE; simpl; omega.
- (* receptive *)
  assert (t1 = t2). inv H. eapply volatile_store_receptive; eauto.
  subst t2; exists vres1; exists m1; auto.
- (* determ *) 
  inv H; inv H0. inv VOLSTORE; inv VOLSTORE0; try congruence.
  + rewrite MN in MN0; inv MN0.
    assert (id = id0) by (eapply Genv.genv_vars_inj; eauto). subst id0.
    assert (ev = ev0).
    {
      inv EVM; inv EVM0; try congruence.
      assert (Vptr b ofs = Vptr b1 ofs1) by congruence. inv H.
      des (peq id0 id1). exploit Genv.global_addresses_distinct. eauto.
      eauto. eauto. auto. easy.
    }
    subst ev0.
    split. constructor. auto. 
  + split. constructor. intuition congruence.
- inv H. inv VOLSTORE; auto.
  rewrite (Mem.bounds_of_block_store _ _ _ _ _ _ STORE).
  rewrite (Mem.mask_store _ _ _ _ _ _ STORE). repSplit; auto.
  Transparent Mem.store.
  unfold Mem.is_dynamic_block in *;
    unfold Mem.store in STORE; destr_in STORE; inv STORE; auto.
- inv EC. inv VOLSTORE; auto. tauto.
  unfold Mem.is_dynamic_block in *;
    unfold Mem.store in STORE; destr_in STORE; inv STORE; auto.
  reflexivity.
- inv EC.
  exists S; inv VOLSTORE; repSplit; auto.
  + repeat red; destr.
  + intros.
    inv DEP.
    eapply norm_independent in MN; eauto.
    symmetry; eapply Mem.loadbytes_store_other; eauto.
    left. destr.
  + red; intros.
    Transparent Mem.loadbytes Mem.storebytes.
    apply Mem.store_storebytes in STORE.
    specialize (DEPmem _ NS).
    specialize (fun l => DEPmem ofs0 n l POS).
    destruct (Mem.range_perm_loadbytes m b0 ofs0 n) as [bytes LB'].
    red; intros.
    eapply Mem.perm_storebytes_2; eauto.
    eapply Mem.loadbytes_range_perm in LB. apply LB; auto.
    specialize (DEPmem _ LB').
    unfold Mem.loadbytes, Mem.storebytes in *.
    destr_in LB. destr_in LB'. destr_in STORE. inv STORE. inv LB. inv LB'.
    clear r r0 r1.
    rewrite Maps.PMap.gsspec. destr. subst.

    Lemma Forall_getN:
      forall (P: memval -> Prop) n o l,
        (forall x, o <= x < o + Z.of_nat n -> P (Maps.ZMap.get x l)) ->
        Forall P (Mem.getN n o l).
    Proof.
      induction n; simpl; intros.
      constructor.
      constructor; auto.
      apply H. lia.
      apply IHn.
      intros. apply H. lia.
    Qed.
    apply Forall_getN.
    intros.

    assert (Decidable.decidable ( Int.unsigned ofs <= x < Int.unsigned ofs + Z.of_nat (length (encode_val chunk v)))).
    {
      red; intros. lia.
    }
    destruct H0 as [In | OUT].
    eapply Mem.setN_property; auto.
    intros v0 IN.
    unfold encode_val, inj_symbolic in IN.
    rewrite <- in_rev in IN.
    apply in_rib in IN.
    rewrite rev_if_be_involutive in IN. des v0.
    inv DEP. inv H3. clear - H4 IN.
    red; red; intros. specialize (H4 a a' H u).
    des chunk; repeat destruct IN as [IN|IN]; inv IN; simpl; repeat destr; try rewrite H4; auto.

    rewrite Mem.setN_outside. 
    rewrite Forall_forall in DEPmem. apply DEPmem.
    apply Mem.getN_in. auto. lia.
  + repeat red; destr.

Qed.

Inductive volatile_store_global_sem (chunk: memory_chunk) (id: ident) (ofs: int)
                                   (F V: Type) (ge: Genv.t F V):
              list expr_sym -> mem -> trace -> expr_sym -> mem -> Prop :=
  | volatile_store_global_sem_intro: forall b m1 v t m2
                                       (FS: Genv.find_symbol ge id = Some b)
                                       (VOLSTORE: volatile_store ge chunk m1 (Eval (Vptr b ofs)) v t m2),
      volatile_store_global_sem chunk id ofs ge (v :: nil) m1 t (Eval Vundef) m2.

Remark volatile_store_global_charact:
  forall chunk id ofs (F V: Type) (ge: Genv.t F V) vargs m t vres m',
  volatile_store_global_sem chunk id ofs ge vargs m t vres m' <->
  exists b, Genv.find_symbol ge id = Some b /\ volatile_store_sem chunk ge (Eval (Vptr b ofs) :: vargs) m t vres m'.
Proof.
  intros; split.
  intros. inv H; exists b. split; auto. econstructor; eauto.
  intros [b [P Q]]. inv Q. econstructor; eauto.
Qed.

Lemma volatile_store_global_ok:
  forall chunk id ofs,
  extcall_properties (volatile_store_global_sem chunk id ofs) 
                     (mksignature (AST.type_of_chunk chunk :: nil) None cc_default).
Proof.
  intros; constructor; intros.
- (* well typed *)
  unfold proj_sig_res; simpl. inv H. repeat red; simpl; auto.  left; exists AST.Tint; destr.
- (* symbols preserved *)
  inv H1. econstructor. rewrite H; eauto.
  inv VOLSTORE; eapply volatile_store_preserved; eauto;
  econstructor; eauto.
- (* valid block *)
  inv H. inv VOLSTORE. auto. eauto with mem.
- (* perms *)
  inv H. inv VOLSTORE. auto. eauto with mem.
- inv H. inv VOLSTORE. tauto.
  split. eapply Mem.perm_store_1; eauto.
  eapply Mem.perm_store_2; eauto.
- (* readonly *)
  inv H. eapply volatile_store_readonly; eauto.
- inv H. inv VOLSTORE; auto.
  generalize (Mem.store_valid_access_3 _ _ _ _ _ _ STORE). intros.
  rewrite (Mem.store_mem_contents _ _ _ _ _ _ STORE).
  rewrite Maps.PMap.gsspec. destr.
  rewrite Mem.setN_outside.  subst; auto.
  erewrite encode_val_length; eauto. rewrite <- size_chunk_conv.  
  destruct (zlt ofs0 (Int.unsigned ofs1)); auto. 
  destruct (zlt ofs0 (Int.unsigned ofs1 + size_chunk chunk)); auto.
  subst.
  des H. specialize (r ofs0).
  red in H0. elim H0. apply Mem.perm_cur_max. apply r. omega.
- (* mem inject *)
  rewrite volatile_store_global_charact in H0. destruct H0 as [b [P Q]].
  exploit (proj1 H). eauto. intros EQ.
  assert (ei f (Eval (Vptr b ofs)) (Eval (Vptr b ofs))). 
  {
    apply vi_ei; auto. simpl.
    unfold Val.inj_ptr. rewrite EQ. rewrite Int.add_zero; auto.
  }
  exploit ec_mem_inject. eapply volatile_store_ok. eauto. eauto. eauto. eauto. eauto.
  econstructor. eauto. eauto.
  intros  [f' [vres' [m2' [A [B [C [D [E G]]]]]]]].
  exists f', vres'; exists m2'; intuition.
  rewrite volatile_store_global_charact. exists b; auto.
- inv EC. inv LF2. inv H3. inv VOLSTORE.
  + eexists; eexists; split; eauto.
    econstructor; eauto.
    econstructor; eauto.
    rewrite <- MN.
    symmetry.
    eapply mem_rel_norm; eauto.
    rewrite <- mem_lessdef_in_bound_m; eauto.
    assert (mr (Val.load_result chunk v) (Val.load_result chunk b1)).
    {
      inv wf; des chunk; eauto.
      inv EVM.
    }
    erewrite <- mem_rel_norm; eauto.
    generalize (wfn m2 _ _ H).
    intro A; apply (mr_val_refl _ wf) in A. rewrite <- A. auto.
    intro E; rewrite E in *. 
    inv EVM; try rename H3 into SE;
    try specialize (SE (fun _ => Int.zero) (fun _ _ => Byte.zero)); destr.
    split. apply (mr_refl _ wf). split; auto. split; auto.
    exists O, O; lia.
  + eapply store_rel in STORE; eauto.
    destruct STORE as [m0 [A B]].
    eexists; eexists.
    split. econstructor; eauto. econstructor; eauto.
    rewrite <- MN.
    symmetry.
    eapply mem_rel_norm; eauto. split; auto.
    apply (mr_refl); auto. split; auto.
    rewrite (nb_blocks_used_rel _ _ _ MR).
    rewrite (nb_blocks_used_rel _ _ _ B).
    rewrite (Mem.nb_boxes_used_same m0 m').
    rewrite (mem_nb_extra_eq _ _ _ MR).
    rewrite (Mem.nb_extra_store _ _ _ _ _ _ A).
    rewrite (mem_nb_extra_eq _ _ _ B).
    split; auto. exists O, O. lia.
    eapply Mem.store_mk_block_list; eauto.
    symmetry; eapply Mem.nb_extra_store; eauto.

-
  rewrite volatile_store_global_charact in EC. destruct EC as [b [P Q]].
  exploit (proj1 MPG). eauto. intros EQ.
  assert (expr_inj_se f (Eval (Vptr b ofs)) (Eval (Vptr b ofs))). 
  {
    apply vi_ei; auto. simpl.
    unfold Val.inj_ptr. rewrite EQ. rewrite Int.add_zero; auto.
  }
  exploit ec_mem_inject_forget. eapply volatile_store_ok. eauto. eauto. eauto. eauto.
  econstructor. eauto. eauto.
  constructor; auto.
  red. intros. intro DEP. red in DEP. red in DEP. simpl in DEP.
  destruct (Mem.exists_two_cms m1 b0) as (cm1 & cm2 & COMP1 & COMP2 & DIFF & SAME).
  eapply DEP. apply COMP1. apply COMP2. auto. intros; apply Byte.zero.
  rewrite SAME. auto. congruence.
  intros  [f' [vres' [m2' [A [B [C [D [E [G i]]]]]]]]].
  exists f', vres'; exists m2'; intuition.
  rewrite volatile_store_global_charact. exists b; auto.

- (* trace length *)
  inv H. inv VOLSTORE; simpl; omega.
- (* receptive *)
  assert (t1 = t2). inv H. eapply volatile_store_receptive; eauto. subst t2. 
  exists vres1; exists m1; congruence.
- (* determ *)
  inv H; inv H0. rewrite FS in FS0; inv FS0.
  eapply ec_determ. eapply volatile_store_ok. eauto.
  econstructor; eauto. econstructor; eauto.
- inv H. inv VOLSTORE; auto.
  rewrite (Mem.bounds_of_block_store _ _ _ _ _ _ STORE).
  rewrite (Mem.mask_store _ _ _ _ _ _ STORE). auto.
  unfold Mem.is_dynamic_block in *;
    unfold Mem.store in STORE; destr_in STORE; inv STORE; auto.
- inv EC. inv VOLSTORE; auto. tauto.
  unfold Mem.is_dynamic_block in *;
    unfold Mem.store in STORE; destr_in STORE; inv STORE; destr.
- inv EC.
  exists S; inv VOLSTORE; repSplit; auto.
  + repeat red; destr.
  + intros.
    rewrite Mem.norm_val in MN. inv MN. 
    symmetry; eapply Mem.loadbytes_store_other; eauto.
    left. apply GlobNotS in FS. destr.
  + red; intros.
    rewrite Mem.norm_val in MN. inv MN.
    apply Mem.store_storebytes in STORE.
    specialize (DEPmem _ NS).
    specialize (fun l => DEPmem ofs1 n l POS).
    destruct (Mem.range_perm_loadbytes m b1 ofs1 n) as [bytes LB'].
    red; intros.
    eapply Mem.perm_storebytes_2; eauto.
    eapply Mem.loadbytes_range_perm in LB. apply LB; auto.
    specialize (DEPmem _ LB').
    unfold Mem.loadbytes, Mem.storebytes in *.
    destr_in LB. destr_in LB'. destr_in STORE. inv STORE. inv LB. inv LB'.
    clear r r0 r1.
    rewrite Maps.PMap.gsspec. destr. subst.
    apply Forall_getN.
    intros.

    assert (Decidable.decidable ( Int.unsigned ofs0 <= x < Int.unsigned ofs0 + Z.of_nat (length (encode_val chunk v)))).
    {
      red; intros. lia.
    }
    destruct H0 as [In | OUT].
    eapply Mem.setN_property; auto.
    intros v0 IN.
    unfold encode_val, inj_symbolic in IN.
    rewrite <- in_rev in IN.
    apply in_rib in IN.
    rewrite rev_if_be_involutive in IN. des v0.
    inv DEP. clear - H2 IN.
    red; red; intros. specialize (H2 a a' H u).
    des chunk; repeat destruct IN as [IN|IN]; inv IN; simpl; repeat destr; try rewrite H2; auto.

    rewrite Mem.setN_outside. 
    rewrite Forall_forall in DEPmem. apply DEPmem.
    apply Mem.getN_in. auto. lia.
  + repeat red; destr.
Qed.

(** ** Semantics of [memcpy] operations. *)

Inductive extcall_memcpy_sem (sz al: Z) (F V: Type) (ge: Genv.t F V): list expr_sym -> mem -> trace -> expr_sym -> mem -> Prop :=
| extcall_memcpy_sem_intro:
    forall bdst odst bsrc osrc m bytes m'
      (ALok: al = 1 \/ al = 2 \/ al = 4 \/ al = 8)
      (SzPos: sz > 0)
      (AlDiv: (al | sz))
      (AlDivSrc: (al | Int.unsigned osrc))
      (AlDivDst: (al | Int.unsigned odst))
      (Cases: bsrc <> bdst \/ Int.unsigned osrc = Int.unsigned odst
              \/ Int.unsigned osrc + sz <= Int.unsigned odst
              \/ Int.unsigned odst + sz <= Int.unsigned osrc)
      (LB: Mem.loadbytes m bsrc (Int.unsigned osrc) sz = Some bytes)
      (SB: Mem.storebytes m bdst (Int.unsigned odst) bytes = Some m')
      v' v
      (MNv': Mem.mem_norm m v' = Vptr bdst odst)
      (MNv:  Mem.mem_norm m v  = Vptr bsrc osrc),
      extcall_memcpy_sem sz al ge (v' :: v :: nil) m E0 (Eval Vundef) m'
| extcall_memcpy_sem_intro_0:
    forall m v' v,
      sz = 0 ->
      extcall_memcpy_sem sz al ge (v' :: v :: nil) m E0 (Eval Vundef) m.


Require Import Psatz.


Lemma extcall_memcpy_ok:
  forall sz al,
  extcall_properties (extcall_memcpy_sem sz al) (mksignature (AST.Tint :: AST.Tint :: nil) None cc_default).
Proof.
  intros. constructor.
- (* return type *)
  intros.
  inv H; repeat red; left; eexists; split; destr; try apply subtype_refl; destr.
  - (* change of globalenv *)
  intros. inv H1.
  eapply extcall_memcpy_sem_intro with (odst:=odst) (osrc:=osrc); eauto.
  eapply extcall_memcpy_sem_intro_0; eauto.
- (* valid blocks *)
  intros. inv H; eauto with mem. 
- (* perms *)
  intros. inv H. eapply Mem.perm_storebytes_2; eauto.  auto.
- intros. inv H. 2: tauto.
  split. eapply Mem.perm_storebytes_1; eauto.
  eapply Mem.perm_storebytes_2; eauto.
- (* readonly *)
  intros. inv H. eapply Mem.storebytes_unchanged_on; eauto. 
  intros; red; intros. elim H0. 
  apply Mem.perm_cur_max. eapply Mem.storebytes_range_perm; eauto.
  apply Mem.unchanged_on_refl.
- intros. inv H; auto. 
  generalize (Mem.storebytes_range_perm _ _ _ _ _ SB). intros.
  rewrite (Mem.storebytes_mem_contents _ _ _ _ _ SB).
  rewrite Maps.PMap.gsspec. destr.
  rewrite Mem.setN_outside.  subst; auto.
  destruct (zlt ofs (Int.unsigned odst)); auto. 
  destruct (zlt ofs (Int.unsigned odst + Z.of_nat (length bytes))); auto.
  subst.
  specialize (H ofs).
  red in H0. elim H0. apply Mem.perm_cur_max. apply H. omega.
- (* injections *)
  intros. inv H0.
  + inv H2. inv LEI. inv LEI0.
    generalize (Mem.norm_inject _ _ wf _ _ _ _ (Vptr bsrc osrc) _ ABI
                                H1 EI0).
    intro A. trim A. congruence.
    destruct A as [A1 A2]; eauto.
    rewrite <- MNv in A2; auto. eapply (Mem.ei_vi_norm _ ei) in A2; eauto.  rewrite MNv in A2; inv A2.
    generalize (Mem.norm_inject _ _ wf _ _ _ _ (Vptr bdst odst) _ ABI
                                H1 EI).
    intro A; destruct A as [A3 A4]; eauto. congruence.
    rewrite <- MNv' in A4. eapply (Mem.ei_vi_norm _ ei) in A4; eauto.  rewrite MNv' in A4; inv A4.
 
    (* general case sz > 0 *)
    exploit Mem.loadbytes_length; eauto. intros LEN.
    assert (RPSRC: Mem.range_perm m1 bsrc (Int.unsigned osrc) (Int.unsigned osrc + sz) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
    assert (RPDST: Mem.range_perm m1 bdst (Int.unsigned odst) (Int.unsigned odst + sz) Cur Nonempty).
    replace sz with (Z_of_nat (length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply nat_of_Z_eq. lia.
    assert (PSRC: Mem.perm m1 bsrc (Int.unsigned osrc) Cur Nonempty).
    apply RPSRC. lia.
    assert (PDST: Mem.perm m1 bdst (Int.unsigned odst) Cur Nonempty).
    apply RPDST. lia.
    (* simpl in *; unfold Val.inj_ptr in *.  *)
    (* destruct (f bsrc) eqn:?; try congruence. destruct (f bdst) eqn:?; try congruence. *)
    (* destruct p0; destruct p1. inv inj_ok; inv inj_ok0. *)
    exploit Mem.address_inject.  eauto. eexact PSRC. eauto. intros EQ1.
    exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
    exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
    exploit Mem.storebytes_mapped_inject; eauto. 
    intros [m2' [C D]]. 
    exists f, (Eval Vundef); exists m2'.
    split.
    eapply extcall_memcpy_sem_intro
    with (bdst:=b3)
           (bsrc:=b2)
           (odst:=Int.add odst (Int.repr delta0))
           (osrc:= Int.add osrc (Int.repr delta)); eauto. 
    rewrite EQ1. intros; eapply Mem.aligned_area_inject with (m := m1); eauto.
    rewrite EQ2. intros; eapply Mem.aligned_area_inject with (m := m1); eauto.
    rewrite EQ1, EQ2. eapply Mem.disjoint_or_equal_inject with (m := m1); eauto.
    apply Mem.range_perm_max with Cur; auto.
    apply Mem.range_perm_max with Cur; auto. 
    rewrite EQ1. eauto.
    rewrite EQ2. eauto.
    split.
    red; intros; eapply ABI; eauto.
    erewrite Mem.bounds_of_block_storebytes; eauto.
    split. apply vi_ei; auto.
    split. auto.
    split. eapply Mem.storebytes_unchanged_on; eauto. unfold loc_unmapped; intros.
    congruence.
    repSplit.
    eapply Mem.storebytes_unchanged_on; eauto. unfold loc_out_of_reach; intros. red; intros.
    eelim H2; eauto.
    apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
    eapply Mem.storebytes_range_perm; eauto.
    erewrite list_forall2_length; eauto.
    lia. red; auto. red; destr.
    exists O, O.
    rewrite (storebytes_nb_dynamic _ _ _ _ _ C).
    rewrite (storebytes_nb_dynamic _ _ _ _ _ SB). lia.
    apply (storebytes_nb_static _ _ _ _ _ SB). 
    apply (storebytes_nb_static _ _ _ _ _ C).
    apply (Mem.nb_extra_storebytes _ _ _ _ _ SB).
    apply (Mem.nb_extra_storebytes _ _ _ _ _ C). 
  + inv H2. inv LEI. inv LEI0.
    exists f, (Eval Vundef), m1'.
    repSplit; auto.
    eapply extcall_memcpy_sem_intro_0; auto. 
    apply vi_ei; auto. 
    apply Mem.unchanged_on_refl.
    apply Mem.unchanged_on_refl.
    red; destr.
    exists O, O. lia.

- intros. inv EC.
  + inv LF2. inv H3. inv H5.
    eapply mem_rel_loadbytes in LB; eauto.
    destruct LB as [v'0 [LB LF]].
    eapply storebytes_rel in SB; eauto.
    destruct SB as [m0 [A B]].
    eexists; eexists; split; eauto.
    eapply extcall_memcpy_sem_intro with (osrc:=osrc) (odst:=odst); eauto.
    erewrite <- mem_rel_norm; eauto.
    generalize (wfn m _ _ H1). rewrite MNv'.
    intro C; apply (mr_val_refl _ wf) in C. rewrite <- C. auto. congruence.
    erewrite <- mem_rel_norm; eauto.
    generalize (wfn m _ _ H2). rewrite MNv.
    intro C; apply (mr_val_refl _ wf) in C. rewrite <- C. auto. congruence.
    split. apply (mr_refl _ wf). split; auto.
    rewrite (nb_blocks_used_rel _ _ _ MR).
    rewrite (nb_blocks_used_rel _ _ _ B).
    rewrite (Mem.nb_boxes_used_same m0 m').
    rewrite (mem_nb_extra_eq _ _ _ MR).
    rewrite (Mem.nb_extra_storebytes _ _ _ _ _ A).
    rewrite (mem_nb_extra_eq _ _ _ B).
    split; auto. exists O, O. lia.
    eapply Mem.storebytes_mk_block_list; eauto.
    symmetry; eapply Mem.nb_extra_storebytes; eauto.
  + eexists; eexists; repSplit.
    inv LF2. inv H3. inv H5.
    apply extcall_memcpy_sem_intro_0; auto.
    apply mr_refl; auto.
    auto. exists O, O; lia. auto. auto.
- intros. inv EC. inv EI. inv LEI. inv LEI0. inv SEP. inv H2. clear H4.
  generalize (forget_norm _ _ wf_inj_expr_inj_se _ _ _ MINJ IWB _ _ EI H3); intro VI.
  generalize (forget_norm _ _ wf_inj_expr_inj_se _ _ _ MINJ IWB _ _ EI0 H1); intro VI'.
  rewrite MNv in VI.
  rewrite MNv' in VI'.
  inv VI; inv VI'.
  exploit Mem.loadbytes_inject; eauto.
  intros [bytes2 [A B]].
  exploit Mem.storebytes_mapped_inject; eauto.
  intros [n2 [C D]].
  
  exists f,(Eval Vundef), n2; repSplit; eauto with mem.
  + exploit iwb_o2o; eauto. exploit (iwb_o2o _ _ _ IWB bsrc); eauto. intros; subst.
    rewrite Z.add_0_r in *. rewrite Int.add_zero in *.
    econstructor; try eexact A; eauto.
    exploit (Mem.disjoint_or_equal_inject _ _ _ _ _
                                          _ _ _ _ _ _ (Int.unsigned osrc) (Int.unsigned odst)
                                          sz MINJ FB FB0); eauto.
    eapply Mem.range_perm_cur. eapply Mem.range_perm_implies.
    eapply Mem.loadbytes_range_perm; eauto.
    constructor.
    eapply Mem.range_perm_cur. eapply Mem.range_perm_implies.
    replace sz with (Z.of_nat (length bytes)). clear C.
    eapply Mem.storebytes_range_perm; eauto.
    erewrite Mem.loadbytes_length; eauto. rewrite nat_of_Z_eq. auto. lia.  constructor.
    rewrite ! Zplus_0_r. auto.
  + eapply iwb_inv; eauto.
    intros; eapply Mem.bounds_of_block_storebytes; eauto.
    intros; eapply Mem.bounds_of_block_storebytes; eauto.
    eapply Mem.mask_storebytes; eauto.
    eapply Mem.mask_storebytes; eauto.
    erewrite <- Mem.nextblock_storebytes; eauto. intros; xomega.
  + apply vi_ei; auto.
  + eapply Mem.storebytes_unchanged_on; eauto. unfold loc_unmapped. congruence.
  + eapply Mem.storebytes_unchanged_on; eauto. unfold loc_out_of_reach.
    intros i ENC PERM.
    apply (PERM _ _ FB0).
    exploit iwb_o2o; eauto. intros; subst. rewrite Z.sub_0_r.
    eapply Mem.perm_cur_max. eapply Mem.perm_implies.
    eapply Mem.storebytes_range_perm; eauto.
    apply Mem.loadbytes_length in A.
    apply Mem.loadbytes_length in LB.
    rewrite LB; rewrite A in ENC. omega.
    constructor.
  + red; destr.
  + exists O, O.
    unfold Mem.nb_boxes_used_m.
    rewrite (Mem.storebytes_mk_block_list _ _ _ _ _ SB).
    rewrite (Mem.storebytes_mk_block_list _ _ _ _ _ C).
    rewrite (Mem.nb_extra_storebytes _ _ _ _ _ SB).
    rewrite (Mem.nb_extra_storebytes _ _ _ _ _ C). lia.
  + unfold nb_boxes_static.
    rewrite (Mem.storebytes_mk_block_list _ _ _ _ _ SB).
    erewrite filter_ext. reflexivity.
    intros (bb,z). simpl. unfold is_static_block_b.
    Transparent Mem.storebytes.
    unfold Mem.storebytes in SB; destr_in SB; inv SB.
    reflexivity.
  + unfold nb_boxes_static.
    rewrite (Mem.storebytes_mk_block_list _ _ _ _ _ C).
    erewrite filter_ext. reflexivity.
    intros (bb,z). simpl. unfold is_static_block_b.
    unfold Mem.storebytes in C; destr_in C; inv C.
    reflexivity.
  + rewrite (Mem.nb_extra_storebytes _ _ _ _ _ SB). auto.
  + rewrite (Mem.nb_extra_storebytes _ _ _ _ _ C). auto.

  + inv EI. inv LEI. inv LEI0. exists f; eexists; eexists; repSplit.
    econstructor 2; eauto. auto.
    apply vi_ei; auto.
    auto.
    apply Mem.unchanged_on_refl.
    apply Mem.unchanged_on_refl. 
    apply inject_incr_refl. red; destr.
    exists O, O; lia. reflexivity. reflexivity. reflexivity. reflexivity.
- (* trace length *)
  intros; inv H; simpl; omega.
- (* receptive *)
  intros. 
  assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
- (* determ *)
  intros; inv H; inv H0. split. constructor.
  intros; split; congruence.
  lia. lia.
  repSplit; auto.
  constructor.
- intros. inv H. 
  Transparent Mem.storebytes.
  unfold Mem.bounds_of_block, Mem.mask, Mem.is_dynamic_block in *;
    unfold Mem.storebytes in SB; destr_in SB; inv SB; auto.
  auto.
- intros. inv EC.
  unfold Mem.is_dynamic_block in *;
    unfold Mem.storebytes in SB; destr_in SB; inv SB; simpl; tauto.
  tauto.
- intros.
  exists S; repSplit; inv EC; try (repeat red; destr; fail).
  + intros. inv DEP. inv H4.
    eapply norm_independent in MNv; eauto.
    eapply norm_independent in MNv'; eauto.
    destruct (zle 0 n).
    symmetry; eapply Mem.loadbytes_storebytes_other; eauto.
    lia. destr.
    rewrite ! Mem.loadbytes_empty by lia; auto.
  + red; intros.
    intros. inv DEP. inv H2.
    eapply norm_independent in MNv; eauto.
    eapply norm_independent in MNv'; eauto.
    generalize (fun pf => DEPmem _ MNv _ _ _ pf LB). intro DM; trim DM; try lia.
    specialize (DEPmem _ NS).
    specialize (fun l => DEPmem ofs n l POS).
    destruct (Mem.range_perm_loadbytes m b ofs n) as [bytes' LB'].
    red; intros.
    eapply Mem.perm_storebytes_2; eauto.
    eapply Mem.loadbytes_range_perm in LB0. apply LB0; auto.
    specialize (DEPmem _ LB').
    unfold Mem.loadbytes, Mem.storebytes in *.
    destr_in LB. destr_in LB'. destr_in SB. inv SB. inv LB. inv LB'.
    destr_in LB0. clear r r0 r1 r2. inv LB0.
    rewrite Maps.PMap.gsspec. destr. subst.
    apply Forall_getN.
    intros.
    assert (Decidable.decidable ( Int.unsigned odst <= x < Int.unsigned odst + sz)).
    {
      red; intros. lia.
    }
    destruct H0 as [iin | OUT].
    eapply Mem.setN_property; auto.
    intros v0 IN.
    unfold encode_val, inj_symbolic in IN.
    rewrite Forall_forall in DM; apply DM; auto.
    rewrite Mem.getN_length. rewrite nat_of_Z_eq. auto. lia.
    rewrite Mem.setN_outside. 
    rewrite Forall_forall in DEPmem. apply DEPmem.
    apply Mem.getN_in. auto.
    rewrite Mem.getN_length, nat_of_Z_eq; auto. lia. lia.  
Qed.

(** ** Semantics of annotations. *)

Lemma map_inj:
  forall {A B: Type} (f: A -> B)
         (f_inj: forall a0 a1, f a0 = f a1 -> a0 = a1) l0 l1,
    map f l0 = map f l1 ->
    l0 = l1.
Proof.
  induction l0; simpl; intros.
  - destruct l1; simpl in *; intuition try congruence.
  - destruct l1; simpl in *; intuition try congruence.
    inv H.
    f_equal.
    apply f_inj; auto.
    apply IHl0; auto.
Qed.

(** ** Semantics of external functions. *)

(** For functions defined outside the program ([EF_external] and [EF_builtin]),
  we do not define their semantics, but only assume that it satisfies
  [extcall_properties]. *)

Parameter external_functions_sem: ident -> signature -> extcall_sem.

Axiom external_functions_properties:
  forall id sg, extcall_properties (external_functions_sem id sg) sg.

(** We treat inline assembly similarly. *)

Parameter inline_assembly_sem: ident -> extcall_sem.

Axiom inline_assembly_properties:
  forall id, extcall_properties (inline_assembly_sem id) (mksignature nil None cc_default).

(** ** Combined semantics of external calls *)

(** Combining the semantics given above for the various kinds of external calls,
  we define the predicate [external_call] that relates:
- the external function being invoked
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).

This predicate is used in the semantics of all CompCert languages. *)
(** ** Semantics of dynamic memory allocation (malloc) *)

Inductive extcall_malloc_sem (F V: Type) (ge: Genv.t F V):
              list expr_sym -> mem -> trace -> expr_sym -> mem -> Prop :=
| extcall_malloc_sem_intro:
    forall sv n m m' b m''
      (MN: Mem.mem_norm m sv = Vint n)
      (ALLOC: Mem.alloc m 0 (Int.unsigned n + 4) Dynamic = Some (m', b))
      (STORE: Mem.store Mint32 m' b 0 (Eval (Vint n)) = Some m''),
      extcall_malloc_sem ge (sv :: nil) m E0 (Eval (Vptr b (Int.repr 4))) m''.

Lemma alloc_static_nb_dynamic:
  forall m lo hi m' b (ALLOC: Mem.alloc m lo hi Normal = Some (m',b)),
    (nb_boxes_dynamic m = nb_boxes_dynamic m')%nat.
Proof.
  intros.
  unfold nb_boxes_dynamic.
  unfold Mem.mk_block_list.
  unfold Mem.size_block.
  Transparent Mem.alloc.
  unfold Mem.alloc, Mem.low_alloc in ALLOC. destr_in  ALLOC; inv ALLOC. simpl.
  unfold is_dynamic_block_b. simpl.
  erewrite mk_block_list_aux_eq. simpl. rewrite Maps.PMap.gss.
  erewrite ForgetNorm.filter_ext. reflexivity.
  intros; simpl. rewrite Maps.PMap.gsspec.  destr. destr.  des b.
  erewrite Mem.blocktype_valid in Heqo. congruence. rewrite e. xomega.
  apply MA_bound.
Qed.

Lemma extcall_malloc_ok:
  extcall_properties extcall_malloc_sem 
                     (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default).
Proof.
  assert (UNCHANGED:
    forall (P: block -> Z -> Prop) m sv n m' b m'',
      Mem.alloc m 0 (Int.unsigned n + 4) Dynamic = Some (m', b) ->
      Mem.store Mint32 m' b 0 (Eval (Vint n)) = Some m'' ->
      Mem.mem_norm m sv = Vint n ->
    Mem.unchanged_on P m m'').
  {
    intros; constructor; intros.
  - split; intros; eauto with mem.
  - assert (b0 <> b) by (eapply Mem.valid_not_valid_diff; eauto with mem).
    erewrite Mem.store_mem_contents; eauto. rewrite Maps.PMap.gso by auto.
    Local Transparent Mem.alloc. unfold Mem.alloc, Mem.low_alloc in H. destr_in H; injection H; intros A B.
    rewrite <- B; simpl. rewrite A. rewrite Maps.PMap.gso by auto. auto.
  } 

  constructor; intros.
  - inv H. unfold proj_sig_res; simpl.
    red. left. exists AST.Tint; split; simpl; auto. 
  - inv H1; econstructor; eauto.
  - inv H. eauto with mem.
  - inv H. exploit Mem.perm_alloc_inv. eauto. eapply Mem.perm_store_2; eauto.
    rewrite dec_eq_false. auto. 
    apply Mem.valid_not_valid_diff with m1; eauto with mem.
  - inv H.
    split; intros. eapply Mem.perm_alloc_1 in H. 2: eauto.
    eapply Mem.perm_store_1; eauto.
    eapply Mem.perm_store_2 in H. 2:eauto.
    exploit Mem.perm_alloc_inv. eauto. eauto. destr. subst.
    contradict H0. eapply Mem.fresh_block_alloc; eauto.
  - inv H. eapply UNCHANGED; eauto.
  - inv H.
    rewrite (Mem.store_mem_contents _ _ _ _ _ _ STORE).
    rewrite (Mem.a_mem_contents' _ _ _ _ _ ALLOC).
    assert (b <> b0). eapply Mem.fresh_block_alloc in ALLOC; eauto. destr.
    rewrite Maps.PMap.gso; auto.
    rewrite Maps.PMap.gso; auto.
  - inv H0. inv H2. inv LEI.
    exploit Mem.alloc_parallel_inject; eauto.
    generalize (Int.unsigned_range n); lia.
    generalize (Int.unsigned_range n); lia.
    intros [f' [m3' [b' [ALLOC' [A [B [C D]]]]]]].
    exploit Mem.store_mapped_inject. eauto. eexact A. eauto. eauto. 
    instantiate (1 := Eval(Vint n)).
    eapply vi_ei; eauto.
    intros [m2' [E G]].
    exists f'; exists (Eval (Vptr b' (Int.repr 4))); exists m2'; intuition.
    + econstructor; eauto.
      generalize (Mem.norm_inject_val' _ _ wf _ _ _ _ _ ABI H1 EI).
      rewrite MN; intro Z; inv Z. auto.
    + red; intros.
      des (peq b1 b). rewrite D.
      eapply ABI; eauto.
      erewrite Mem.bounds_of_block_alloc_other. 2:eauto. 2: auto. 2: auto.
      rewrite (Mem.bounds_of_block_store _ _ _ _ _ _ STORE). auto.
    + apply vi_ei; auto. simpl. unfold Val.inj_ptr. rewrite C.
      rewrite Int.add_zero. auto.
    + eapply UNCHANGED; eauto.
    + eapply UNCHANGED; eauto.
      generalize (Mem.norm_inject_val' _ _ wf _ _ _ _ _ ABI H1 EI).
      rewrite MN; intro Z; inv Z. rewrite H3. eauto.
    + red; intros. destruct (eq_block b1 b). 
      subst b1. rewrite C in H2. inv H2. eauto with mem. 
      rewrite D in H2. congruence. auto.
    + rewrite <- (store_nb_dynamic _ _ _ _ _ _ STORE).
      rewrite <- (store_nb_dynamic _ _ _ _ _ _ E).
      rewrite <- (alloc_dynamic_nb_dynamic _ _ _ _ _ ALLOC).
      rewrite <- (alloc_dynamic_nb_dynamic _ _ _ _ _ ALLOC'). 
      exists O, (Mem.box_span (Z.max 0 (Int.unsigned n + 4)))%nat. lia.
    + rewrite <- (store_nb_static _ _ _ _ _ _ STORE).
      rewrite <- (alloc_dynamic_nb_static _ _ _ _ _ ALLOC). lia.
    + rewrite <- (store_nb_static _ _ _ _ _ _ E).
      rewrite <- (alloc_dynamic_nb_static _ _ _ _ _ ALLOC'). lia.
    + rewrite (Mem.nb_extra_alloc _ _ _ _ _ _ ALLOC).
      eapply Mem.nb_extra_store; eauto.
    + rewrite (Mem.nb_extra_alloc _ _ _ _ _ _ ALLOC').
      eapply Mem.nb_extra_store; eauto.

  - inv EC. inv LF2. inv H3.
    destruct (alloc_mem_rel _ wf _ _ _ _ _ _ ALLOC _ MR) as (m0 & A & MR').
    destruct (fun (pf: mr (Eval (Vint n)) (Eval (Vint n))) =>
                store_rel _ wf _ _ _ _ _ _ _ _ MR' pf STORE) as (m2' & S & MR'').
    apply mr_refl; auto.
    exists (Eval (Vptr b (Int.repr 4))), m2'; split; auto.
    econstructor; eauto.
    generalize (rel_norm _ wf wfn _ _ _ _ MR H1). rewrite MN.
    intro MRN. generalize (mr_val_refl _ wf _ _ MRN).  destr.
    split; auto.
    apply mr_refl; auto. split; auto.
    split.
    rewrite (nb_blocks_used_rel _ _ _ MR).
    rewrite (nb_blocks_used_rel _ _ _ MR'').
    rewrite (Mem.nb_boxes_used_same m2' m0).
    rewrite (Mem.nb_boxes_alloc _ _ _ _ _ _ A).
    exists O, (Mem.box_span (Z.max 0 (Int.unsigned n + 4))); lia.
    eapply Mem.store_mk_block_list; eauto.
    symmetry; eapply Mem.nb_extra_store; eauto.
    rewrite (mem_nb_extra_eq _ _ _ MR).
    rewrite (mem_nb_extra_eq _ _ _ MR'').
    rewrite <- (Mem.nb_extra_store _ _ _ _ _ _ S).
    rewrite (Mem.nb_extra_alloc _ _ _ _ _ _ A); auto.
  - inv EC. inv EI. inv LEI. inv SEP. inv H2.

    Lemma alloc_iwb:
      forall m lo hi m' b bt
        (A: Mem.alloc m lo hi bt = Some (m',b))
        f tm ei (WFI: wf_inj ei)
        (IWB: inj_well_behaved f m tm)
        (MINJ: Mem.inject true ei f m tm)
        (LOHI: lo <= hi) (HIPOS: hi >= 0),
      exists tm' tb f',
        Mem.alloc tm lo hi bt = Some (tm',tb)
        /\ inj_well_behaved f' m' tm'
        /\ Mem.inject true ei f' m' tm'
        /\ f' b = Some (tb,0)
        /\ (forall b', b' <> b -> f' b' = f b').
    Proof.
      intros.
      exploit (Mem.alloc_parallel_inject true _ WFI f m tm lo hi m' b); eauto.
      intros [f' [m2' [b2 [A' [MINJ' [INCR [F'B F'nB]]]]]]].
      exists m2', b2, f'.
      repSplit; auto.
      inv IWB; constructor; simpl; intros; eauto.
      - red; intros.
        des (peq b b0). rewrite F'nB in H; eauto.
      - red; intros.
        des (peq b b0). Mem.rewbnd. Mem.rewmsk. eapply iwb_wb.
        des (f b0). des p. eapply INCR in Heqo; destr.
      - des (peq b b0).
        assert (b2 = b') by congruence. subst.
        Mem.rewbnd.  auto.
        assert (b2 <> b'). intro; subst. exploit Mem.valid_block_inject_2. 
        rewrite <- F'nB. apply H. auto. eauto. intros.
        eapply Mem.fresh_block_alloc. apply A'.  auto. 
        repeat Mem.rewbnd.  eapply iwb_bounds.
        rewrite <- F'nB; eauto.
      - des (peq b b0).
        assert (b2 = b') by congruence. subst.
        Mem.rewmsk.  auto.
        assert (b2 <> b'). intro; subst. exploit Mem.valid_block_inject_2. 
        rewrite <- F'nB. apply H. auto. eauto. intros.
        eapply Mem.fresh_block_alloc. apply A'.  auto. 
        repeat Mem.rewmsk.  eapply iwb_mask.
        rewrite <- F'nB; eauto.
      - des (peq b' b2).
        exists b; rewrite F'B. eauto.
        edestruct (Mem.valid_block_alloc_inv _ _ _ _ _ _ A'); eauto. destr. edestruct iwb_no_oota; eauto. dex. apply INCR in H1. eauto.
      - des (peq b1 b); des (peq b0 b). rewrite F'nB in H0 by auto.
        eapply Mem.valid_block_inject_2 in H0; eauto.
        assert (b' = b2) by congruence. subst.
        exploit Mem.fresh_block_alloc; eauto. tauto.
        rewrite F'nB in H by auto.
        eapply Mem.valid_block_inject_2 in H; eauto.
        assert (b' = b2) by congruence. subst.
        exploit Mem.fresh_block_alloc; eauto. tauto.
        rewrite F'nB in * by auto. eauto.
    Qed.

    destruct (alloc_iwb _ ALLOC wf_inj_expr_inj_se IWB MINJ)
      as (tm' & tb & f' & A' & IWB' & MINJ' & Fnew & Fold).
    generalize (Int.unsigned_range n); lia.
    generalize (Int.unsigned_range n); lia.
    exists f', (Eval (Vptr tb (Int.repr 4))).
    destruct (fun (pf: expr_inj_se f' (Eval (Vint n)) (Eval (Vint n))) =>
                Mem.store_mapped_inject _ _ wf_inj_expr_inj_se _ _ _ _ _ _ _ _ _ _ _ MINJ' STORE Fnew pf)
      as (m2' & S & MINJ'').
    apply vi_ei; auto.
    exists m2'; repSplit; auto.
    + econstructor; eauto.
      generalize (forget_norm _ _ wf_inj_expr_inj_se _ _ _ MINJ IWB _ _ EI0 H1).
      rewrite MN. intro X; inv X; auto.
    + eapply iwb_inv; eauto.
      * intros.
        eapply Mem.bounds_of_block_store; eauto.
      * intros.
        eapply Mem.bounds_of_block_store; eauto.
      * intros.
        eapply Mem.mask_store; eauto.
      * intros.
        eapply Mem.mask_store; eauto.
      * intros.
        erewrite <- Mem.nextblock_store in H; eauto. xomega.
    + apply vi_ei; auto. unfold Val.apply_inj, Val.inj_ptr. rewrite Fnew.
      rewrite Int.add_zero; auto.
    + eauto.
    + constructor. intros.
      assert (b1 <> tb). eapply Mem.fresh_block_alloc in A'; destr.
      split; intros.
      * eapply Mem.perm_alloc_1 in H3. 2: eauto.
        eapply Mem.perm_store_1; eauto.
      * eapply Mem.perm_store_2 in H3.
        eapply Mem.perm_alloc_inv in H3; eauto. destr_in H3. eauto.
      *  intros.
         assert (b1 <> tb). eapply Mem.fresh_block_alloc in A'; destr.
         eapply Mem.perm_valid_block in H0; destr.
         erewrite <- (Mem.alloc_contents _ _ _ _ _ _ A').
         rewrite (Mem.store_mem_contents _ _ _ _ _ _ S).
         rewrite Maps.PMap.gso. auto. auto. auto.
    + red; intros. des (peq b1 b).
      erewrite Mem.mi_freeblocks in H; eauto. destr.
      eapply Mem.fresh_block_alloc; eauto.
      rewrite Fold; auto.
    + red; intros.
      des (peq b b1).
      split. eapply Mem.fresh_block_alloc; eauto. replace b2 with tb in * by congruence.
      eapply Mem.fresh_block_alloc; eauto.
      rewrite Fold in H0. destr. auto.
    + apply Mem.nb_boxes_alloc in ALLOC.
      apply Mem.nb_boxes_alloc in A'.
      rewrite (Mem.nb_boxes_used_same m2 m').
      rewrite (Mem.nb_boxes_used_same m2' tm').
      rewrite ALLOC, A'.
      exists O, (Mem.box_span (Z.max 0 (Int.unsigned n + 4)))%nat. lia.
      eapply Mem.store_mk_block_list; eauto.
      symmetry; eapply Mem.nb_extra_store; eauto.
      eapply Mem.store_mk_block_list; eauto.
      symmetry; eapply Mem.nb_extra_store; eauto. 
    +

      etransitivity. eapply alloc_dynamic_nb_static; eauto. eapply store_nb_static; eauto.
    + etransitivity. eapply alloc_dynamic_nb_static; eauto. eapply store_nb_static; eauto.
    + etransitivity. eapply Mem.nb_extra_alloc; eauto. eapply Mem.nb_extra_store; eauto.
    + etransitivity. eapply Mem.nb_extra_alloc; eauto. eapply Mem.nb_extra_store; eauto.
  - (* trace length *)
    inv H; simpl; omega.
  - (* receptive *)
    assert (t1 = t2). inv H; inv H0; auto. subst t2.
    exists vres1; exists m1; auto.
  - (* determ *)
    inv H; inv H0. split. constructor. intuition congruence.
  - inv H.
    assert (b <> b0). eapply Mem.fresh_block_alloc in ALLOC. destr.
    rewrite <- (Mem.bounds_of_block_store _ _ _ _ _ _ STORE).
    rewrite <- (Mem.mask_store _ _ _ _ _ _ STORE).
    unfold Mem.alloc, Mem.low_alloc in ALLOC; destr_in ALLOC; inv ALLOC.
    unfold Mem.mask, Mem.bounds_of_block. simpl.
    rewrite ! Maps.PMap.gso by eauto. repSplit; auto.
    unfold Mem.is_dynamic_block in *; destr. unfold Mem.store in STORE.
    repeat destr_in STORE. inv STORE. simpl. auto.
    simpl in *. auto. rewrite Maps.PMap.gso; auto.
  - inv EC.
    rewrite (Mem.is_block_dynamic_alloc' _ _ _ _ _ _ ALLOC).
    unfold Mem.store in STORE; destr_in STORE; inv STORE.
    unfold Mem.is_dynamic_block in *; destr.
    eapply Mem.fresh_block_alloc in ALLOC. destr.
  - inv EC.
    exists (fun b' => negb (eq_block b b') && S b').
    repSplit; auto.
    + intros; destr.
      des (eq_block b b0).
    + intros. 
      rewrite (Mem.loadbytes_store_other _ _ _ _ _ _ STORE).
      rewrite (Mem.loadbytes_alloc_unchanged _ _ _ _ _ _ ALLOC); auto.
      eapply Mem.fresh_block_alloc in ALLOC. destr.
    + 
      red; intros.
      apply Mem.store_storebytes in STORE.
      assert (b = b0 \/ S b0 = false). des (eq_block b b0).
      des (eq_block b b0).
      unfold Mem.loadbytes in LB; unfold Mem.storebytes in STORE.
      destr_in STORE; inv STORE.
      destr_in LB; inv LB. clear r0 r.
      rewrite Maps.PMap.gss.
    apply Forall_getN.
    intros.

    Lemma setN_forall:
      forall (P: memval -> Prop) vl t o x,
      (forall x, P (Maps.ZMap.get x t)) ->
      (Forall P vl) ->
      P (Maps.ZMap.get x (Mem.setN vl o t)).
    Proof.
      intros.
      assert (Decidable.decidable (o <= x < o + Z.of_nat (length vl))).
      red; lia.
      des H1.
      apply Mem.setN_property; auto. rewrite Forall_forall in H0. auto.
      rewrite Mem.setN_outside; auto. lia.
    Qed.
    apply setN_forall; simpl; auto.
    unfold Mem.alloc, Mem.low_alloc in ALLOC. destr_in ALLOC. inv ALLOC. simpl.
    intros; rewrite Maps.PMap.gss.
    rewrite Mem.get_init_block.
    repeat red; destr. unfold encode_val. simpl.
    unfold inj_symbolic; simpl.
    apply Mem.Forall_rev'.
    apply Forall_rib.
    repeat constructor; repeat red; destr. des H.
    rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ STORE) in LB; auto.
    rewrite (Mem.loadbytes_alloc_unchanged _ _ _ _ _ _ ALLOC) in LB; auto.
    generalize (DEPmem _ e _ _ _ POS LB).
    apply Forall_impl.
    intros. des a.
    red; red; intros.
    apply H. intros; apply H0. des (eq_block b b1). 
    destruct (Mem.valid_block_dec m b0); destr.
    apply Invalid in n2. destr.
    + repeat red; destr. intros.
      rewrite H; auto. des (eq_block b b).
    + intros. des (S b0). des (eq_block b b0).
      right.
      exploit (Mem.alloc_result); eauto.
      exploit (Mem.nextblock_alloc); eauto.
      exploit Mem.nextblock_store; eauto. intros A B C.
      rewrite C, A, B. xomega.
Qed.

(** ** Semantics of dynamic memory deallocation (free) *)

Inductive extcall_free_sem  (F V: Type) (ge: Genv.t F V):
              list expr_sym -> mem -> trace -> expr_sym -> mem -> Prop :=
| extcall_free_sem_intro:
    forall sv sv' b lo sz m m'
      (MN: Mem.mem_norm m sv = Vptr b lo)
      (is_dynamic: Mem.is_dynamic_block m b)
      (LOAD: Mem.load Mint32 m b (Int.unsigned lo - 4) = Some sv')
      (MNsz: Mem.mem_norm m sv' = Vint sz)
      (SzPos: Int.unsigned sz > 0)
      (FREE: Mem.free m b (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz) = Some m'),
      extcall_free_sem ge (sv :: nil) m E0 (Eval Vundef) m'.

Lemma free_sinj:
  forall m lo hi m' b
    (A: Mem.free m b lo hi = Some m')
    f tm ei (WFI: wf_inj ei)
    (MINJ: Mem.inject true ei f m tm) delta
    tb (FB: f b = Some (tb,delta))
    (ID: Mem.is_dynamic_block m b),
  exists tm',
    Mem.free tm tb lo hi = Some tm' 
    /\ Mem.inject true ei f m' tm'
    /\ (inj_well_behaved f m tm -> inj_well_behaved f m' tm').
Proof.
  intros.
  generalize (Mem.mi_inj_dynamic _ _ _ _ _ MINJ _ _ _ FB).
  intros (IDBeq & DYNimpl & DYNimpl').
  trim DYNimpl; auto.
  trim DYNimpl'. destr.
  assert (Bnds: Mem.bounds_of_block m b = (lo,hi)).
  {
    Transparent Mem.free. unfold Mem.free in A; repeat destr_in A; inv A.
    unfold Mem.has_bounds in Heqb0. repeat destr_in Heqb0.
    des (zeq lo z); des (zeq hi z0).
  }
  assert (Bnds': Mem.bounds_of_block tm tb = (lo,hi)).
  {
    des DYNimpl. 
  }
  unfold Mem.free.
  destr. destr.
  - eexists; repSplit; eauto.
    unfold Mem.free in A; repeat destr_in A; inv A.
    + inv MINJ; constructor; simpl; intros; eauto.
      {
        inv mi_inj; constructor; simpl; intros; eauto.
        - rewrite (Mem.perm_unchecked_free _ _ _ _ Bnds _ eq_refl) in H0.
          rewrite (Mem.perm_unchecked_free _ _ _ _ Bnds' _ eq_refl).
          des H0.
          eapply mi_perm in p0; eauto. split; auto.
          intro; subst. exploit DYNimpl'; eauto. 
        - unfold Mem.in_bound_m in *.
          rewrite Mem.unchecked_free_bounds' in *.
          destr_in H0. destr. rewrite Bnds in H0. rewrite Bnds'.
          des (zeq lo lo); des (zeq hi hi). red in H0; destr; lia.
          destr. subst. generalize (DYNimpl' _ _ H). destr.
          eauto.
        - rewrite (Mem.perm_unchecked_free _ _ _ _ Bnds _ eq_refl) in H0.
          des H0. eauto.
        - rewrite <- (@unchecked_free_nb_boxes m b lo hi) in mi_size_mem.
          rewrite <- (@unchecked_free_nb_boxes tm tb lo hi) in mi_size_mem. intuition lia. auto. auto.
      }
      * apply mi_mappedblocks in H. destr.
      * red; intros.
        unfold Mem.in_bound_m in *.
        rewrite Mem.unchecked_free_bounds' in *.
        destr_in H2. rewrite Bnds in H2. 
        des (zeq lo lo); des (zeq hi hi). red in H2; destr; lia.
        destr_in H3. rewrite Bnds in H3. 
        des (zeq lo lo); des (zeq hi hi). red in H3; destr; lia.
        eauto.
      * 
        specialize (mi_inj_dynamic _ _ _ H). repSplit. destr.
        rewrite ! Mem.unchecked_free_bounds'. des mi_inj_dynamic. des a.
        intros. trim a0. destr.
        rewrite Bnds, Bnds'.
        des (zeq lo lo); des (zeq hi hi). split. destr.
        repeat destr; subst.
        rewrite <- i in e. trim e; auto. elim n. symmetry; eapply e; eauto.
        intros.
        des mi_inj_dynamic. des a. trim e. destr. trim a0. destr. eapply e. eauto.
  + unfold Mem.free in A; repeat destr_in A; inv A.
    intros IWB. inv IWB; constructor; simpl; intros; eauto.
    * red; intros.
      rewrite <- ! Mem.size_block_snd, ! Mem.unchecked_free_bounds'.
      rewrite Bnds. destr.
      rewrite Mem.unchecked_free_mask. 
      rewrite ! Mem.size_block_snd; eauto.
    * rewrite <- ! Mem.size_block_snd, ! Mem.unchecked_free_bounds'.
      rewrite Bnds, Bnds'.
      des (zeq lo lo); des (zeq hi hi). repeat destr; eauto.
      subst.
      exploit iwb_inj. apply H. apply FB. destr.
      rewrite ! Mem.size_block_snd; eauto.
    * rewrite ! Mem.unchecked_free_mask. eauto.
  - contradict Heqb0. 
    unfold Mem.free in A; repeat destr_in A; inv A.
    unfold Mem.has_bounds in *.
    rewrite Bnds in Heqb0.
    rewrite Bnds'.
    des (zeq lo lo); des (zeq hi hi).
  - elim n.
    unfold Mem.free in A; repeat destr_in A; inv A.
    red; intros. specialize (r _ H).
    inv MINJ. inv mi_inj.
    eapply mi_perm in r; eauto.
    specialize (mi_inj_dynamic _ _ _ FB). des mi_inj_dynamic. des a.
    trim a0. auto. des a0.
    rewrite Z.add_0_r in r. auto.
Qed.



Lemma extcall_free_ok:
  extcall_properties extcall_free_sem 
                     (mksignature (AST.Tint :: nil) None cc_default).
Proof.
  constructor; intros.
  - inv H. unfold proj_sig_res. simpl. red. left. exists AST.Tint; simpl; destr.
  - inv H1; econstructor; eauto.
  - inv H. eauto with mem.
  - inv H. eapply Mem.perm_free_3; eauto.
  - inv H.
    assert (b <> b0). destr.
    split; intros.
    eapply Mem.perm_free_inv in H2; eauto. des H2.
    eapply Mem.perm_free_3; eauto.
  - inv H. eapply Mem.free_unchanged_on; eauto. 
    intros. red; intros. elim H0. 
    apply Mem.perm_cur_max.
    apply Mem.perm_implies with Freeable; auto with mem. 
    eapply Mem.free_range_perm; eauto.
  - inv H. rewrite (Mem.free_contents _ _ _ _ _ FREE). auto.         
  - inv H0. inv H2. inv LEI. 
    generalize (Mem.norm_inject_val' _ _ wf _ _ _ _ _ ABI H1 EI).
    rewrite MN. intro X; inv X.
    exploit Mem.load_inject; eauto. intros [vsz [A B]]. 
    assert (Mem.range_perm m1 b (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz) Cur Freeable).
    eapply Mem.free_range_perm; eauto.
    exploit Mem.address_inject; eauto. 
    apply Mem.perm_implies with Freeable; auto with mem.
    apply H0. instantiate (1 := lo). omega. 
    intro EQ.
    destruct (free_sinj _ _ FREE wf H1 FB is_dynamic)
      as (m2' & FREE' & MINJ' & SINJ).
    destruct (Mem.mi_inj_dynamic _ _ _ _ _ H1 _ _ _ FB) as (C & D & E).
    trim D. auto.
    trim E. destr. des D. rewrite Int.add_zero in *. rewrite Z.add_0_r in *.
    exists f, (Eval Vundef), m2'; repSplit; auto.
    + eapply extcall_free_sem_intro with (sv' := vsz).
      eauto.
      destr. auto.
      generalize (Mem.norm_inject_val' _ _ wf _ _ _ _ _ ABI H1 B).
      rewrite MNsz; intro X; inv X; auto.
      auto. auto.
    + red; intros.
      destruct (Mem.free_bounds' _ _ _ _ _ b1 FREE).
      eapply ABI. rewrite <- H5; eauto. auto.
      rewrite H5 in H2. inv H2. lia.
    + apply vi_ei; auto. 
    + eapply Mem.free_unchanged_on; eauto. unfold loc_unmapped. intros; congruence.
    + eapply Mem.free_unchanged_on; eauto. unfold loc_out_of_reach. 
      intros. red; intros. eelim H3; eauto.
      apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem. 
      apply H0.
      omega.
    + red; intros. congruence.
    + rewrite (free_dynamic_nb_dynamic _ _ _ _ _ is_dynamic FREE).
      rewrite (free_dynamic_nb_dynamic _ _ _ _ _ (proj1 C is_dynamic) FREE'). 
      exists (Mem.box_span (Int.unsigned lo + Int.unsigned sz - (Int.unsigned lo - 4)))%nat, O. lia.
    + rewrite (free_dynamic_nb_static _ _ _ _ _ is_dynamic FREE). auto.
    + rewrite (free_dynamic_nb_static _ _ _ _ _ (proj1 C is_dynamic) FREE'). auto.
    + eapply Mem.nb_extra_free; eauto.
    + eapply Mem.nb_extra_free; eauto.

  - inv EC. inv LF2. inv H3.
    generalize (rel_norm _ wf wfn _ _ _ _ MR H1). rewrite MN.
    intro MRE. generalize (mr_val_refl _ wf _ _ MRE). intro A; trim A. destr.
    clear MRE.
    destruct (mem_rel_load _ wf _ _ _ _ _ _ MR LOAD) as [sv'' [LOAD' ME']].
    generalize (rel_norm _ wf wfn _ _ _ _ MR ME'). rewrite MNsz.
    intro MRE. generalize (mr_val_refl _ wf _ _ MRE). intro B; trim B. destr.
    clear MRE.
    destruct (free_mem_rel _ _ _ _ _ _ _ MR FREE) as [m2' [FREE' MR']].
    exists (Eval Vundef), m2'; repSplit; auto.
    + econstructor; eauto.
      red. erewrite <- mem_blocktype_eq. eauto. eauto.
    + apply mr_refl. auto.
    + rewrite (nb_blocks_used_rel _ _ _ MR').
      rewrite (nb_blocks_used_rel _ _ _ MR).
      unfold Mem.free in FREE'; repeat destr_in FREE'. inv FREE'.
      erewrite <- (@unchecked_free_nb_boxes m' b  (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz)).
      exists (Mem.box_span (Z.max 0 (Int.unsigned lo + Int.unsigned sz))), O. lia.
      eapply Mem.has_bounds_bounds; eauto.
    + eapply Mem.nb_extra_free; eauto.
    + eapply Mem.nb_extra_free; eauto.

  - inv EC. inv EI. inv LEI. inv SEP. inv H2.
    generalize (forget_norm _ _ wf_inj_expr_inj_se _ _ _ MINJ IWB _ _ EI0 H1).
    rewrite MN. intro X; inv X.
    exploit Mem.load_inject; eauto. intros [vsz [A B]].
    assert (Mem.range_perm m1 b (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz) Cur Freeable).
    eapply Mem.free_range_perm; eauto.
    exploit Mem.address_inject; eauto.
    apply Mem.perm_implies with Freeable; auto with mem.
    apply H0. instantiate (1 := lo). omega.
    intro EQ.
    destruct (free_sinj _ _ FREE wf_inj_expr_inj_se MINJ FB is_dynamic)
      as (m2' & FREE' & MINJ' & SINJ').
    destruct (Mem.mi_inj_dynamic _ _ _ _ _ MINJ _ _ _ FB) as (C & D & E).
    trim D. auto.
    trim E. destr. des D. rewrite Int.add_zero in *. rewrite Z.add_0_r in *.
    
    exists f, (Eval Vundef), m2'; repSplit; auto.
    + eapply extcall_free_sem_intro with (sv' := vsz).
      eauto.
      destr. auto.
      generalize (forget_norm _ _ wf_inj_expr_inj_se _ _ _ MINJ IWB _ _ B).
      intro D; trim D.
      eapply expr_inj_se_not_dep; eauto.
      rewrite MNsz in D. inv D. eauto.
      auto. auto.
    + apply vi_ei; auto.
    + eapply Mem.free_unchanged_on; eauto. unfold loc_unmapped. intros; congruence.
    + eapply Mem.free_unchanged_on; eauto. unfold loc_out_of_reach.
      intros. red; intros. eelim H3; eauto.
      apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
      apply H0.
      omega.
    + red; destr.
    + unfold Mem.free in FREE. repeat destr_in FREE. inv FREE.
      unfold Mem.free in FREE'. repeat destr_in FREE'. inv FREE'.
      generalize (@unchecked_free_nb_boxes _ _ _ _ (Mem.has_bounds_bounds _ _ _ _ Heqb1)).
      generalize (@unchecked_free_nb_boxes _ _ _ _ (Mem.has_bounds_bounds _ _ _ _ Heqb0)). intros.
      rewrite <- H2, <- H3.
      exists (Mem.box_span (Z.max 0 (Int.unsigned lo + Int.unsigned sz)))%nat, O. lia.
    +

      eapply free_dynamic_nb_static; eauto.
    + eapply free_dynamic_nb_static; eauto.
      tauto.
    + eapply Mem.nb_extra_free; eauto.
    + eapply Mem.nb_extra_free; eauto.
- (* trace length *)
  inv H; simpl; omega.
- (* receptive *)
  assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
- (* determ *)
  inv H; inv H0. split. constructor. intuition congruence.
- inv H. assert (b <> b0) by destr. rewrite (Mem.bounds_free _ _ _ _ _ _ FREE); auto.
  erewrite Mem.mask_free. 2: eauto. auto.
  unfold Mem.free in FREE; repeat destr_in FREE; inv FREE;
  unfold Mem.is_dynamic_block in *; destr.
- inv EC. symmetry; eapply Mem.is_block_dynamic_free; eauto.
- inv EC;intros.
  inv DEP. inv H2.
  eapply norm_independent in MN; eauto.
  exists S; repSplit; try solve [repeat red; destr]; auto.
  +  symmetry; eapply Mem.loadbytes_free; eauto. destr.
  + red; intros.
    eapply Mem.loadbytes_free_2 in LB; eauto.
Qed.

Fixpoint annot_eventvals (targs: list annot_arg) (vargs: list eventval) : list eventval :=
  match targs, vargs with
  | AA_arg ty :: targs', varg :: vargs' => varg :: annot_eventvals targs' vargs'
  | AA_int n :: targs', _ => EVint n :: annot_eventvals targs' vargs
  | AA_float n :: targs', _ => EVfloat n :: annot_eventvals targs' vargs
  | _, _ => vargs
  end.


Inductive extcall_annot_sem (text: ident) (targs: list annot_arg) (F V: Type) (ge: Genv.t F V):
              list expr_sym -> mem -> trace -> expr_sym -> mem -> Prop :=
  | extcall_annot_sem_intro: forall vargs m args,
      eventval_list_match ge args (annot_args_typ targs) (map (Mem.mem_norm m) vargs) ->
      extcall_annot_sem text targs ge vargs m
           (Event_annot text (annot_eventvals targs args) :: E0) (Eval Vundef) m.





Lemma eventval_match_mr:
  forall {F V} (ge: Genv.t F V) mr (wf: wf_mr mr) (wfn: wf_mr_norm mr)  ev ty v1 v2 m m'
    (MR: mem_rel mr m m'),
    eventval_match ge ev ty (Mem.mem_norm m v1) -> mr v1 v2 -> eventval_match ge ev ty (Mem.mem_norm m' v2).
Proof.
  intros.
  generalize (rel_norm _ wf wfn _ _ _ _ MR H0).
  edestruct mr_se_or_ld; eauto.
  subst.
  - intro SE. apply same_eval_val in SE. rewrite SE in H.
    inv H; econstructor; eauto.
  - subst. intro SE. apply lessdef_val in SE. inv SE.
    inv H; constructor; auto. inv H; destr.
Qed.

Lemma eventval_list_match_mr:
  forall {F V} (ge: Genv.t F V) mr (wf: wf_mr mr)(wfn: wf_mr_norm mr) vl1 evl tyl m m'
  (MR: mem_rel mr m m'),
    eventval_list_match ge evl tyl (map (Mem.mem_norm m) vl1) ->
  forall vl2, list_forall2 mr vl1 vl2 -> eventval_list_match ge evl tyl (map (Mem.mem_norm m') vl2).
Proof.
  induction vl1; simpl; intros.
  inv H. inv H0. constructor.
  inv H0. inv H. simpl; constructor. eapply eventval_match_mr; eauto.
  eauto.
Qed.


Lemma extcall_annot_ok:
  forall text targs,
  extcall_properties (extcall_annot_sem text targs) (mksignature (annot_args_typ targs) None cc_default).
Proof.
  intros; constructor; intros.
  - (* well typed *)
    inv H. left; exists AST.Tint; split; simpl; auto.
  - (* symbols *)
    inv H1. econstructor; eauto.
    eapply eventval_list_match_preserved; eauto.
  - (* valid blocks *)
    inv H; auto.
  - (* perms *)
    inv H; auto.
  - inv H; tauto.
  - (* readonly *)
    inv H. apply Mem.unchanged_on_refl.
  - inv H; auto.
  - inv H0.
    exists f, (Eval Vundef), m1'.
    repSplit; auto.
    constructor; auto.
    eapply eventval_list_match_inject; eauto.

    Lemma list_ei_norm:
      forall ei (wf: wf_inj ei)
        f m m' (ABI: Mem.all_blocks_injected f m)
        (MINJ: Mem.inject true ei f m m')
        vl vl'
        (EI: list_ei ei f vl vl'),
        list_forall2 (val_inject f) (map (Mem.mem_norm m) vl)
                     (map (Mem.mem_norm m') vl').
    Proof.
      induction 4; simpl; intros; eauto.
      constructor.
      constructor; eauto.
      eapply Mem.norm_inject_val'; eauto.
    Qed.
    eapply list_ei_norm; eauto.
    apply vi_ei; auto. apply Mem.unchanged_on_refl.
    apply Mem.unchanged_on_refl. red; destr.
    exists O, O. lia.
  - inv EC.
    exists (Eval Vundef), m'.
    repSplit; auto.
    constructor; auto.
    eapply eventval_list_match_mr; eauto.
    apply mr_refl; auto. exists O, O; lia.

  - inv EC.
    exists f, (Eval Vundef), m1'.
    repSplit; auto.
    constructor; auto.
    eapply eventval_list_match_inject; eauto.
    Lemma list_ei_norm':
      forall ei (wf: wf_inj ei)
        f m m'
        (IWB: inj_well_behaved f m m')
        (MINJ: Mem.inject true ei f m m')
        vl vl'
        (EI: list_ei ei f vl vl')
        (SEP: Forall (sep_inj m f) vl),
        list_forall2 (val_inject f) (map (Mem.mem_norm m) vl)
                     (map (Mem.mem_norm m') vl').
    Proof.
      induction 4; simpl; intros; eauto.
      constructor.
      inv SEP.
      constructor; eauto.
      eapply forget_norm; eauto.
    Qed.
    eapply list_ei_norm'; eauto.
    apply vi_ei; auto. apply Mem.unchanged_on_refl.
    apply Mem.unchanged_on_refl.
    red; destr. exists O, O; lia. 

  - (* trace length *)
    inv H; simpl; omega.
  - (* receptive *)
    assert (t1 = t2). inv H; inv H0; auto.
    exists vres1; exists m1; congruence.
  - (* determ *)
    inv H; inv H0.
    assert (args = args0). eapply eventval_list_match_determ_2; eauto. subst args0.
    split. constructor. intros; split; auto. 
  - inv H; auto.
  - inv EC; tauto.
  - inv EC. exists S; repSplit; eauto.
    repeat red; destr.
Qed.

Inductive extcall_annot_val_sem (text: ident) (targ: typ) (F V: Type) (ge: Genv.t F V):
              list expr_sym -> mem -> trace -> expr_sym -> mem -> Prop :=
  | extcall_annot_val_sem_intro: forall varg m arg,
      eventval_match ge arg targ (Mem.mem_norm m varg) ->
      extcall_annot_val_sem text targ ge ( varg :: nil) m (Event_annot text (arg :: nil) :: E0) varg m.

Lemma extcall_annot_val_ok:
  forall text targ,
  extcall_properties (extcall_annot_val_sem text targ) (mksignature (targ :: nil) (Some targ) cc_default).
Proof.
  intros; constructor; intros.
  - (* well typed *)
    inv H. unfold proj_sig_res; simpl.
    assert (Mem.mem_norm m2 vres <> Vundef). intro A; rewrite A in H0. inv H0.
    eapply eventval_match_type in H0; eauto.
    assert (forall v t, Values.Val.has_type v t -> v <> Vundef ->
                   exists t', wt_val v (styp_of_ast t') /\ subtype t' t = true).
    {
      intros.
      des v; des t;
      first [ now (exists AST.Tint; destr) |
              now (exists AST.Tlong; destr) |
              now (exists AST.Tfloat; destr) |
              now (exists AST.Tsingle; destr) | idtac].
    }
    apply H1 in H0; auto. destruct H0 as [t' [WV ST]].
    generalize (Mem.norm_type m2 vres _ _ eq_refl H WV).
    left; eexists; eauto.

  - (* symbols *)
    inv H1. econstructor; eauto.
    eapply eventval_match_preserved; eauto.
  - (* valid blocks *)
    inv H; auto.
  - (* perms *)
    inv H; auto.
  - inv H; tauto.
  - (* readonly *)
    inv H. apply Mem.unchanged_on_refl.
  - inv H; auto.
  - (* mem inject *)
    inv H0. inv H2. inv LEI.
    exists f, b, m1'; intuition.
    econstructor; eauto.
    eapply eventval_match_inject; eauto.
    eapply Mem.norm_inject_val'; eauto.
    red; intros; congruence. exists O, O; lia.
  - 
    inv EC. inv LF2. inv H4.
    exists b1, m'; intuition.
    econstructor; eauto.
    eapply eventval_match_mr; eauto.
    exists O,O; lia.
  - (* mem inject *)
    inv EC. inv EI. inv LEI. inv SEP. inv H3.
    exists f, b, m1'; intuition.
    econstructor; eauto.
    eapply eventval_match_inject; eauto.
    eapply forget_norm; eauto. red; destr. exists O,O; lia. 
  - (* trace length *)
    inv H; simpl; omega.
  - (* receptive *)
    assert (t1 = t2). inv H; inv H0; auto. subst t2.
    exists vres1; exists m1; auto.
  - (* determ *)
    inv H; inv H0.
    assert (arg = arg0). eapply eventval_match_determ_2; eauto. subst arg0.
    split. constructor. intuition.
  - inv H; auto.
  - inv EC; tauto.
  - inv EC. exists S; repSplit; eauto.
    inv DEP; auto. 
Qed.


Definition external_call (ef: external_function): extcall_sem :=
  match ef with
  | EF_external name sg  => external_functions_sem name sg
  | EF_builtin name sg   => external_functions_sem name sg
  | EF_vload chunk       => volatile_load_sem chunk
  | EF_vstore chunk      => volatile_store_sem chunk
  | EF_vload_global chunk id ofs => volatile_load_global_sem chunk id ofs
  | EF_vstore_global chunk id ofs => volatile_store_global_sem chunk id ofs
  | EF_malloc            => extcall_malloc_sem
  | EF_free              => extcall_free_sem
  | EF_memcpy sz al      => extcall_memcpy_sem sz al
  | EF_annot txt targs   => extcall_annot_sem txt targs
  | EF_annot_val txt targ=> extcall_annot_val_sem txt targ
  | EF_inline_asm txt    => inline_assembly_sem txt
  end.

Theorem external_call_spec:
  forall ef, 
  extcall_properties (external_call ef) (ef_sig ef).
Proof.
  intros. unfold external_call, ef_sig. destruct ef.
  apply external_functions_properties.
  apply external_functions_properties.
  apply volatile_load_ok.
  apply volatile_store_ok.
  apply volatile_load_global_ok.
  apply volatile_store_global_ok.
  apply extcall_malloc_ok.
  apply extcall_free_ok.
  apply extcall_memcpy_ok.
  apply extcall_annot_ok.
  apply extcall_annot_val_ok.
  apply inline_assembly_properties.
Qed.

Definition external_call_well_typed ef := ec_well_typed (external_call_spec ef).
Definition external_call_symbols_preserved_gen ef := ec_symbols_preserved (external_call_spec ef).
Definition external_call_valid_block ef := ec_valid_block (external_call_spec ef).
Definition external_call_max_perm ef := ec_max_perm (external_call_spec ef).
Definition external_call_readonly ef := ec_readonly (external_call_spec ef).
Definition external_call_readonly' ef := ec_readonly' (external_call_spec ef).
Definition external_call_mem_inject ef := ec_mem_inject (external_call_spec ef).
Definition external_call_mem_rel ef := ec_mem_rel (external_call_spec ef).
Definition external_call_mem_inject_forget ef := ec_mem_inject_forget (external_call_spec ef).
Definition external_call_trace_length ef := ec_trace_length (external_call_spec ef).
Definition external_call_receptive ef := ec_receptive (external_call_spec ef).
Definition external_call_determ ef := ec_determ (external_call_spec ef).
Definition external_call_bounds_mask ef := ec_bounds_mask (external_call_spec ef).
Definition external_call_dyn ef := ec_preserves_dynamic (external_call_spec ef).
Definition external_call_perm ef := ec_perm (external_call_spec ef).
(** Special cases of [external_call_symbols_preserved_gen]. *)

Lemma external_call_symbols_preserved:
  forall ef F1 F2 V (ge1: Genv.t F1 V) (ge2: Genv.t F2 V) vargs m1 t vres m2,
  external_call ef ge1 vargs m1 t vres m2 ->
  (forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) ->
  (forall b, Genv.find_var_info ge2 b = Genv.find_var_info ge1 b) ->
  external_call ef ge2 vargs m1 t vres m2.
Proof.
  intros. eapply external_call_symbols_preserved_gen; eauto.
  intros. unfold block_is_volatile. rewrite H1. auto.
Qed.

Require Import Errors.

Lemma external_call_symbols_preserved_2:
  forall ef F1 V1 F2 V2 (tvar: V1 -> res V2)
         (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) vargs m1 t vres m2,
  external_call ef ge1 vargs m1 t vres m2 ->
  (forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) ->
  (forall b gv1, Genv.find_var_info ge1 b = Some gv1 ->
     exists gv2, Genv.find_var_info ge2 b = Some gv2 /\ transf_globvar tvar gv1 = OK gv2) ->
  (forall b gv2, Genv.find_var_info ge2 b = Some gv2 ->
     exists gv1, Genv.find_var_info ge1 b = Some gv1 /\ transf_globvar tvar gv1 = OK gv2) ->
  external_call ef ge2 vargs m1 t vres m2.
Proof.
  intros. eapply external_call_symbols_preserved_gen; eauto.
  intros. unfold block_is_volatile.
  case_eq (Genv.find_var_info ge1 b); intros.
  exploit H1; eauto. intros [g2 [A B]]. rewrite A. monadInv B. destruct g; auto.
  case_eq (Genv.find_var_info ge2 b); intros.
  exploit H2; eauto. intros [g1 [A B]]. congruence.
  auto.
Qed.

(** Corollary of [external_call_valid_block]. *)

Lemma external_call_nextblock:
  forall ef (F V : Type) (ge : Genv.t F V) vargs m1 t vres m2,
  external_call ef ge vargs m1 t vres m2 ->
  Ple (Mem.nextblock m1) (Mem.nextblock m2).
Proof.
  intros. destruct (plt (Mem.nextblock m2) (Mem.nextblock m1)).
  exploit external_call_valid_block; eauto. intros.
  eelim Plt_strict; eauto.
  unfold Plt, Ple in *; zify; omega.
Qed.

(** Corollaries of [external_call_determ]. *)

Lemma external_call_match_traces:
  forall ef (F V : Type) (ge : Genv.t F V) vargs m t1 vres1 m1 t2 vres2 m2,
  external_call ef ge vargs m t1 vres1 m1 ->
  external_call ef ge vargs m t2 vres2 m2 ->
  match_traces ge t1 t2.
Proof.
  intros. exploit external_call_determ. eexact H. eexact H0. tauto.
Qed.

Lemma external_call_deterministic:
  forall ef (F V : Type) (ge : Genv.t F V) vargs m t vres1 m1 vres2 m2,
  external_call ef ge vargs m t vres1 m1 ->
  external_call ef ge vargs m t vres2 m2 ->
  vres1 = vres2 /\ m1 = m2.
Proof.
  intros. exploit external_call_determ. eexact H. eexact H0. intuition.
Qed.

(** Late in the back-end, calling conventions for external calls change:
  arguments and results of type [Tlong] are passed as two integers.
  We now wrap [external_call] to adapt to this convention. *)

Fixpoint decode_longs (tyl: list typ) (vl: list expr_sym) : list expr_sym :=
  match tyl with
  | nil => nil
  | AST.Tlong :: tys =>
      match vl with
      | v1 :: v2 :: vs => Val.longofwords v1 v2 :: decode_longs tys vs
      | _ => nil
      end
  | ty :: tys =>
      match vl with
      | v1 :: vs => v1 :: decode_longs tys vs
      | _ => nil
      end
  end.

Definition encode_long (oty: option typ) (v: expr_sym) : list expr_sym :=
  match oty with
  | Some AST.Tlong => Val.hiword v :: Val.loword v :: nil
  | _ => v :: nil
  end.

Definition proj_sig_res' (s: signature) : list typ :=
  match s.(sig_res) with
  | Some AST.Tlong => AST.Tint :: AST.Tint :: nil
  | Some ty => ty :: nil
  | None => AST.Tint :: nil
  end.

Inductive external_call'
      (ef: external_function) (F V: Type) (ge: Genv.t F V)
      (vargs: list expr_sym) (m1: mem) (t: trace) (vres: list expr_sym) (m2: mem) : Prop :=
  external_call'_intro:
    forall v
      (EC: external_call ef ge (decode_longs (sig_args (ef_sig ef)) vargs) m1 t v m2)
      (RES: vres = encode_long (sig_res (ef_sig ef)) v),
      external_call' ef ge vargs m1 t vres m2.

Lemma decode_longs_lessdef:
  forall tyl vl1 vl2, Val.lessdef_list vl1 vl2 -> Val.lessdef_list (decode_longs tyl vl1) (decode_longs tyl vl2).
Proof.
  induction tyl; simpl; intros. 
  auto.
  destruct a; inv H; auto. inv LDL; auto. constructor; auto. apply Val.longofwords_lessdef; auto. 
Qed.

Lemma decode_longs_rel:
  forall mr (wf: wf_mr mr) tyl vl1 vl2,
    list_forall2 mr vl1 vl2 ->
    list_forall2 mr (decode_longs tyl vl1) (decode_longs tyl vl2).
Proof.
  induction tyl; simpl; intros; try constructor. 
  destruct a; inv H; auto; repeat (constructor; auto).
  inv H1; auto; constructor; auto.
  unfold Val.longofwords; inv wf; auto.
Qed.


Lemma decode_longs_inject:
  forall p (wf: wf_inj p) f tyl vl1 vl2,
    list_ei p f vl1 vl2 -> list_ei p f (decode_longs tyl vl1) (decode_longs tyl vl2).
Proof.
  induction tyl; simpl; intros. constructor. 
  destruct a; inv H; auto; try constructor; auto.
  inv LEI; constructor; auto.
  unfold Val.longofwords. eapply ei_binop; auto.
Qed.


Lemma encode_long_rel:
  forall mr (wf: wf_mr mr) oty v1 v2,
    mr v1 v2 ->
    list_forall2 mr (encode_long oty v1) (encode_long oty v2).
Proof.
  intros. destruct oty as [[]|]; simpl; auto; 
  repeat (constructor; auto); unfold Val.hiword, Val.loword; inv wf; auto.  
Qed.


Lemma encode_long_lessdef:
  forall oty v1 v2, Val.lessdef v1 v2 -> Val.lessdef_list (encode_long oty v1) (encode_long oty v2).
Proof.
  intros. destruct oty as [[]|]; simpl; auto. 
  constructor. apply Val.hiword_lessdef; auto. constructor. apply Val.loword_lessdef; auto. auto.
Qed.

Lemma encode_long_inject:
  forall p (wf: wf_inj p)f oty v1 v2, p f v1 v2 -> list_ei p f (encode_long oty v1) (encode_long oty v2).
Proof.
  intros. inv wf. destruct oty as [[]|]; simpl; repeat  constructor; eauto. 
Qed.

Lemma encode_long_has_type:
  forall v sg,
    wt v (proj_sig_res sg) ->
    list_forall2 wt (encode_long (sig_res sg) v) (proj_sig_res' sg).
Proof.
  unfold proj_sig_res, proj_sig_res', encode_long; intros.
  destruct (sig_res sg) as [[] | ]; simpl in *; constructor; auto; try solve [constructor].
  - des H; dex; destr. des t'.
    left; exists AST.Tint; destr.
    right; intro; dex; destr; apply n.
    des H. eexists; destr; eauto.
  - constructor; [|constructor].
    des H; dex; destr. des t'.
    left; exists AST.Tint; destr.
    right; intro; dex; destr; apply n. des H. eexists; destr; eauto.
Qed.

(* Lemma encode_long_has_type_false: *)
(*   forall v sg, *)
(*     (~exists t, Val.has_type v t) -> *)
(*     ~exists tl, Val.has_type_list (encode_long (sig_res sg) v) tl. *)
(* Proof. *)
(*   unfold proj_sig_res, proj_sig_res', encode_long; intros. *)
(*   intro; dex. *)
(*   destruct (sig_res sg) as [[] | ]; simpl in *; eauto; *)
(*   repeat match goal with *)
(*              H : match ?g with _ => _ end |- _ => des g *)
(*            | H: (exists _, _) -> False |- _ => solve [exfalso; apply H; eexists; eauto] *)
(*          end. *)
(* Qed. *)

Lemma external_call_well_typed':
  forall ef (F V : Type) (ge : Genv.t F V) vargs m1 t vres m2,
  external_call' ef ge vargs m1 t vres m2 ->
  list_forall2 wt vres (proj_sig_res' (ef_sig ef)).
Proof.
  intros. inv H.
  exploit external_call_well_typed. eauto.
  intro. apply encode_long_has_type. eauto. 
Qed.

Lemma external_call_symbols_preserved':
  forall ef F1 F2 V (ge1: Genv.t F1 V) (ge2: Genv.t F2 V) vargs m1 t vres m2,
  external_call' ef ge1 vargs m1 t vres m2 ->
  (forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) ->
  (forall b, Genv.find_var_info ge2 b = Genv.find_var_info ge1 b) ->
  external_call' ef ge2 vargs m1 t vres m2.
Proof.
  intros. inv H. exists v; auto. eapply external_call_symbols_preserved; eauto.
Qed.

Lemma external_call_valid_block':
  forall ef (F V : Type) (ge : Genv.t F V) vargs m1 t vres m2 b,
  external_call' ef ge vargs m1 t vres m2 ->
  Mem.valid_block m1 b -> Mem.valid_block m2 b.
Proof.
  intros. inv H. eapply external_call_valid_block; eauto.
Qed.

Lemma external_call_nextblock':
  forall ef (F V : Type) (ge : Genv.t F V) vargs m1 t vres m2,
  external_call' ef ge vargs m1 t vres m2 ->
  Ple (Mem.nextblock m1) (Mem.nextblock m2).
Proof.
  intros. inv H. eapply external_call_nextblock; eauto.
Qed.

Lemma lessdef_load_result:
  forall chunk v v',
    Val.lessdef v v' ->
    Val.lessdef (Val.load_result chunk v) (Val.load_result chunk v').
Proof.
  apply Val.load_result_lessdef.
Qed.

Lemma external_call_rel:
  forall mr (wf: wf_mr mr) (wfn: wf_mr_norm mr) (F V: Type) m m' args args' ef (ge: Genv.t F V) t vres m2
    (MR: mem_rel mr m m')
    (LF2: list_forall2 mr args args')
    (EC: external_call ef ge args m t vres m2),
  exists vres' m2',
    external_call ef ge args' m' t vres' m2' /\
    mr vres vres' /\
    mem_rel mr m2 m2'.
Proof.
  intros.
  exploit ec_mem_rel; eauto. apply external_call_spec; auto.
  intros [vres' [m2' P]]; exists vres', m2'; destr.
Qed.

Lemma external_call'_rel:
  forall mr (wf: wf_mr mr) (wfn: wf_mr_norm mr)
         (F V: Type) m m' args args' ef (ge: Genv.t F V) t vres m2,
    mem_rel mr m m' ->
    list_forall2 mr args args' ->
    external_call' ef ge args m t vres m2 ->
    exists vres' m2',
      external_call' ef ge args' m' t vres' m2' /\
      list_forall2 mr vres vres' /\
      mem_rel mr m2 m2'.
Proof.
  intros mr wf wfn F V m m' args args' ef ge t vres m2 ME SE EC.
  inv EC.
  eapply external_call_rel in EC0; eauto.
  destruct EC0 as [vres' [m2' [A [B C]]]].
  exists (encode_long (sig_res (ef_sig ef)) vres'), m2'. 
  split. econstructor; eauto.
  split. apply encode_long_rel; auto. auto.
  apply decode_longs_rel; auto.
Qed.

Lemma external_call_mem_inject':
  forall ef ei (wf: wf_inj ei) F V (ge: Genv.t F V) vargs m1 t vres m2 f m1' vargs'
  (ABI: Mem.all_blocks_injected f m1),
  meminj_preserves_globals ge f ->
  external_call' ef ge vargs m1 t vres m2 ->
  Mem.inject true ei f m1 m1' ->
  list_ei ei f vargs vargs' ->
  exists f' vres' m2',
     external_call' ef ge vargs' m1' t vres' m2'
  /\ list_ei ei f' vres vres'
  /\ Mem.inject true ei f' m2 m2'
  /\ Mem.unchanged_on (loc_unmapped f) m1 m2
  /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
  /\ inject_incr f f'
  /\ inject_separated f f' m1 m1'
  /\         (exists C C',
            nb_boxes_dynamic m2 + C = nb_boxes_dynamic m1 + C' /\
            nb_boxes_dynamic m2' + C = nb_boxes_dynamic m1' + C' )%nat /\
        nb_boxes_static m1 = nb_boxes_static m2 /\
        nb_boxes_static m1' = nb_boxes_static m2' /\
        Mem.nb_extra m1 = Mem.nb_extra m2 /\
        Mem.nb_extra m1' = Mem.nb_extra m2'.
Proof.
  intros. inv H0. 
  exploit external_call_mem_inject; eauto.
  eapply decode_longs_inject; eauto.
  intros (f' & v' & m2' & A & B & C & D & E & P ).
  exists f', (encode_long (sig_res (ef_sig ef)) v'); exists m2'; intuition.
  econstructor; eauto.
  apply encode_long_inject; auto.
Qed.


Lemma external_call_determ':
  forall ef (F V : Type) (ge : Genv.t F V) vargs m t1 vres1 m1 t2 vres2 m2,
  external_call' ef ge vargs m t1 vres1 m1 ->
  external_call' ef ge vargs m t2 vres2 m2 ->
  match_traces ge t1 t2 /\ (t1 = t2 ->  vres1 = vres2 /\ m1 = m2).
Proof.
  intros. inv H; inv H0. exploit external_call_determ. eexact EC. eexact EC0. 
  intros [A B]. split. auto. intros. destruct B as [C D]; auto. subst.
  split; auto.
Qed.

Lemma external_call_match_traces':
  forall ef (F V : Type) (ge : Genv.t F V) vargs m t1 vres1 m1 t2 vres2 m2,
  external_call' ef ge vargs m t1 vres1 m1 ->
  external_call' ef ge vargs m t2 vres2 m2 ->
  match_traces ge t1 t2.
Proof.
  intros. inv H; inv H0. eapply external_call_match_traces; eauto.
Qed.

Lemma external_call_deterministic':
  forall ef (F V : Type) (ge : Genv.t F V) vargs m t vres1 m1 vres2 m2,
  external_call' ef ge vargs m t vres1 m1 ->
  external_call' ef ge vargs m t vres2 m2 ->
  vres1 = vres2 /\ m1 = m2.
Proof.
  intros. inv H; inv H0. 
  exploit external_call_deterministic. eexact EC. eexact EC0. intros [A B].
  subst. split; auto.
Qed.


Lemma extcall_bounds:
  forall ef (F V : Type) (ge : Genv.t F V) el m t e m',
    external_call ef ge el m t e m' ->
    forall b, Mem.valid_block m b ->
         ~ Mem.is_dynamic_block m b ->
         Mem.bounds_of_block m' b = Mem.bounds_of_block m b.
Proof.
  intros.
  exploit external_call_bounds_mask; eauto. destr.
Qed.

Lemma extcall_msk:
  forall ef (F V : Type) (ge : Genv.t F V) el m t e m',
    external_call ef ge el m t e m' ->
    forall b, Mem.valid_block m b ->
         ~ Mem.is_dynamic_block m b ->
         Mem.nat_mask m' b = Mem.nat_mask m b.
Proof.
  intros.
  exploit external_call_bounds_mask; eauto. unfold Mem.nat_mask; intros [A [B C]].
  rewrite B. reflexivity.
Qed.

