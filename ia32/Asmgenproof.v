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

(** Correctness proof for x86 generation: main proof. *)

Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Values_symbolictype.
Require Import Values_symbolic.
Require Import NormaliseSpec.
Require Import ExprEval.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Conventions.
Require Import Asm.
Require Import Asmgen.
Require Import Asmgenproof0.
Require Import Asmgenproof1.
Require Import MemRel.

Section PRESERVATION.

Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: transf_program prog = Errors.OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.


(* Lemma funct_bounds: *)
(*   forall fb f im tf *)
(*     (TF: transf_function f = OK tf) *)
(*     (FFP : Genv.find_funct_ptr ge fb = Some (Internal f)) *)
(*     (IM : Genv.init_mem prog = Some im), *)
(*     Mem.bounds_of_block im fb = (0, list_length_z (fn_code tf) + 1). *)
(* Proof. *)
(*   intros fb f im tf TF.  *)
(*   unfold Genv.find_funct_ptr. *)
(*   unfold Genv.init_mem. *)
(*   intros. *)
(*   generalize (Genv.alloc_globals_initialized *)
(*                 (ge:=ge) (prog_defs prog) *)
(*                 (ge0:=Genv.empty_genv Mach.fundef unit) *)
(*                 (m:=Mem.empty) (m':=im)). *)
(*   simpl. *)
(*   intro A; trim A. auto. *)
(*   trim A. unfold ge; auto. *)
(*   trim A. { *)
(*     red. intros. *)
(*     unfold Genv.find_var_info in H. simpl in H. *)
(*     rewrite Maps.PTree.gempty in H. congruence. *)
(*   } *)
(*   trim A. { *)
(*     red; intros. *)
(*     unfold Genv.find_symbol in H0. simpl in H0. *)
(*     rewrite Maps.PTree.gempty in H0. congruence. *)
(*   } *)
(*   destruct A as [A B]. *)

(*   assert (Maps.PTree.get fb (Genv.genv_funs (Genv.empty_genv Mach.fundef unit)) *)
(*           = Some (Internal f) -> *)
(*           Mem.bounds_of_block Mem.empty fb = (0, list_length_z (fn_code tf) + 1)). *)
(*   { *)
(*     simpl. rewrite Maps.PTree.gempty. congruence. *)
(*   } *)
(*   revert H. *)
(*   revert im. *)
(*   generalize (Genv.empty_genv Mach.fundef unit). *)
(*   generalize (Mem.empty). *)
(*   generalize (prog_defs prog). *)

(*   induction l; simpl; intros; eauto. *)
(*   - inv IM. auto. *)
(*   - destruct (Genv.alloc_global (Genv.add_globals (Genv.add_global t a) l) m a) *)
(*              eqn:?. *)
    
(*     eapply IHl; eauto. *)
(*   destr_cond_match. simpl. *)
(* Qed. *)

(* Lemma return_address_offset_correct: *)
(*   forall f c ofs *)
(*     tf (TRANSF: transf_function f = OK tf) *)
(*     tc (TRANSL: transl_code f c false = OK tc) *)
(*     (RAO:return_address_offset f c ofs) *)
(*     fb *)
(*     (FFP: Genv.find_funct_ptr ge fb = Some (Internal f)) *)
(*     im (IM: Genv.init_mem prog = Some im), *)
(*     Mem.in_bound_m (Int.unsigned ofs) im fb. *)
(* Proof. *)
(*   intros. *)
(*   specialize (RAO _ _ TRANSF0 TRANSL). *)
(*   apply code_tail_bounds_1 in RAO. *)
(* Qed. *)

Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_symbol_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma functions_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = Errors.OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial transf_fundef _ TRANSF).

Lemma functions_transl:
  forall fb f tf,
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transf_function f = OK tf ->
  Genv.find_funct_ptr tge fb = Some (Internal tf).
Proof.
  intros. exploit functions_translated; eauto. intros [tf' [A B]].
  monadInv B. rewrite H0 in EQ; inv EQ; auto. 
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_var_info_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

(** * Properties of control flow *)

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> list_length_z (fn_code tf) <= Int.max_unsigned.
Proof.
  intros. monadInv H. destruct (zlt Int.max_unsigned (list_length_z (fn_code x))); monadInv EQ0.
  omega. 
Qed.

Lemma exec_straight_exec:
  forall fb f c ep tf tc c' rs m rs' m' o,
    reg_ptr rs PC fb o ->
    transl_code_at_pc ge fb o f c ep tf tc ->
    exec_straight tge tf tc rs m c' rs' m' ->
    plus step tge (State rs m) E0 (State rs' m').
Proof.
  intros. inv H0.
  eapply exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto. 
Qed.

Lemma exec_straight_at:
  forall fb f c ep tf tc c' ep' tc' rs m rs' m' o,
    reg_ptr rs PC fb o ->
    transl_code_at_pc ge fb o f c ep tf tc ->
    transl_code f c' ep' = OK tc' ->
    exec_straight tge tf tc rs m tc' rs' m' ->
    exists o',
      reg_ptr rs' PC fb o' /\
      transl_code_at_pc ge fb o' f c' ep' tf tc'.
Proof.
  intros. inv H0. 
  exploit exec_straight_steps_2; eauto. 
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  intros [ofs' [PC' CT']].
  unfold reg_ptr;
  rewrite PC'. eexists; split; eauto. constructor; auto.
Qed.

(** The following lemmas show that the translation from Mach to Asm
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ Asm instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- Asm instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that Asm constructor
  functions do not introduce new labels.

  In passing, we also prove a "is tail" property of the generated Asm code.
*)

Section TRANSL_LABEL.

Remark mk_mov_label:
  forall rd rs k c, mk_mov rd rs k = OK c -> tail_nolabel k c.
Proof.
  unfold mk_mov; intros. 
  destruct rd; try discriminate; destruct rs; TailNoLabel.
Qed.
Hint Resolve mk_mov_label: labels.

Remark mk_shrximm_label:
  forall n k c, mk_shrximm n k = OK c -> tail_nolabel k c.
Proof.
  intros. monadInv H; TailNoLabel.
Qed.
Hint Resolve mk_shrximm_label: labels.

Remark mk_intconv_label:
  forall f r1 r2 k c, mk_intconv f r1 r2 k = OK c -> 
  (forall r r', nolabel (f r r')) ->
  tail_nolabel k c.
Proof.
  unfold mk_intconv; intros. TailNoLabel. 
Qed.
Hint Resolve mk_intconv_label: labels.

Remark mk_smallstore_label:
  forall f addr r k c, mk_smallstore f addr r k = OK c -> 
  (forall r addr, nolabel (f r addr)) ->
  tail_nolabel k c.
Proof.
  unfold mk_smallstore; intros. TailNoLabel. 
Qed.
Hint Resolve mk_smallstore_label: labels.

Remark loadind_label:
  forall base ofs ty dst k c,
  loadind base ofs ty dst k = OK c ->
  tail_nolabel k c.
Proof.
  unfold loadind; intros. destruct ty; try discriminate; destruct (preg_of dst); TailNoLabel.
Qed.

Remark storeind_label:
  forall base ofs ty src k c,
  storeind src base ofs ty k = OK c ->
  tail_nolabel k c.
Proof.
  unfold storeind; intros. destruct ty; try discriminate; destruct (preg_of src); TailNoLabel.
Qed.

Remark mk_setcc_base_label:
  forall xc rd k,
  tail_nolabel k (mk_setcc_base xc rd k).
Proof.
  intros. destruct xc; simpl; destruct (ireg_eq rd EAX); TailNoLabel.
Qed.

Remark mk_setcc_label:
  forall xc rd k,
  tail_nolabel k (mk_setcc xc rd k).
Proof.
  intros. unfold mk_setcc. destruct (low_ireg rd).
  apply mk_setcc_base_label.
  eapply tail_nolabel_trans. apply mk_setcc_base_label. TailNoLabel.
Qed.

Remark mk_jcc_label:
  forall xc lbl' k,
  tail_nolabel k (mk_jcc xc lbl' k).
Proof.
  intros. destruct xc; simpl; TailNoLabel.
Qed.

Remark transl_cond_label:
  forall cond args k c,
  transl_cond cond args k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_cond; intros.
  destruct cond; TailNoLabel.
  destruct (Int.eq_dec i Int.zero); TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
Qed.

Remark transl_op_label:
  forall op args r k c,
  transl_op op args r k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_op; intros. destruct op; TailNoLabel.
  destruct (Int.eq_dec i Int.zero); TailNoLabel.
  destruct (Float.eq_dec f Float.zero); TailNoLabel.
  destruct (Float32.eq_dec f Float32.zero); TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_setcc_label.  
Qed.

Remark transl_load_label:
  forall chunk addr args dest k c,
  transl_load chunk addr args dest k = OK c ->
  tail_nolabel k c.
Proof.
  intros. monadInv H. destruct chunk; TailNoLabel.
Qed.

Remark transl_store_label:
  forall chunk addr args src k c,
  transl_store chunk addr args src k = OK c ->
  tail_nolabel k c.
Proof.
  intros. monadInv H. destruct chunk; TailNoLabel.
Qed.

Lemma transl_instr_label:
  forall f i ep k c,
  transl_instr f i ep k = OK c ->
  match i with Mlabel lbl => c = Plabel lbl :: k | _ => tail_nolabel k c end.
Proof.
Opaque loadind.
  unfold transl_instr; intros; destruct i; TailNoLabel.
  eapply loadind_label; eauto.
  eapply storeind_label; eauto.
  eapply loadind_label; eauto.
  eapply tail_nolabel_trans; eapply loadind_label; eauto. 
  eapply transl_op_label; eauto.
  eapply transl_load_label; eauto.
  eapply transl_store_label; eauto.
  destruct s0; TailNoLabel.
  destruct s0; TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_jcc_label.  
Qed.

Lemma transl_instr_label':
  forall lbl f i ep k c,
  transl_instr f i ep k = OK c ->
  find_label lbl c = if Mach.is_label lbl i then Some k else find_label lbl k.
Proof.
  intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply B). 
  intros. subst c. simpl. auto.
Qed.

Lemma transl_code_label:
  forall lbl f c ep tc,
  transl_code f c ep = OK tc ->
  match Mach.find_label lbl c with
  | None => find_label lbl tc = None
  | Some c' => exists tc', find_label lbl tc = Some tc' /\ transl_code f c' false = OK tc'
  end.
Proof.
  induction c; simpl; intros.
  inv H. auto.
  monadInv H. rewrite (transl_instr_label' lbl _ _ _ _ _ EQ0).
  generalize (Mach.is_label_correct lbl a). 
  destruct (Mach.is_label lbl a); intros.
  subst a. simpl in EQ. exists x; auto.
  eapply IHc; eauto.
Qed.

Lemma transl_find_label:
  forall lbl f tf,
  transf_function f = OK tf ->
  match Mach.find_label lbl f.(Mach.fn_code) with
  | None => find_label lbl tf.(fn_code) = None
  | Some c => exists tc, find_label lbl tf.(fn_code) = Some tc /\ transl_code f c false = OK tc
  end.
Proof.
  intros. monadInv H. destruct (zlt Int.max_unsigned (list_length_z (fn_code x))); inv EQ0.
  monadInv EQ. simpl. eapply transl_code_label; eauto. rewrite transl_code'_transl_code in EQ0; eauto. 
Qed.

End TRANSL_LABEL.

(** A valid branch in a piece of Mach code translates to a valid ``go to''
  transition in the generated PPC code. *)

Lemma find_label_goto_label:
  forall f tf lbl rs m c' b ofs
         (FFP: Genv.find_funct_ptr ge b = Some (Internal f))
         (TF: transf_function f = OK tf)
         (Npc: reg_ptr rs PC b ofs)
         (FL: Mach.find_label lbl f.(Mach.fn_code) = Some c'),
  exists tc' rs' o',
    goto_label tf lbl rs m = Next rs' m
    /\ reg_ptr rs' PC b o' 
    /\ transl_code_at_pc ge b o' f c' false tf tc'
    /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. exploit (transl_find_label lbl f tf); eauto. rewrite FL. 
  intros [tc [A B]].
  exploit label_pos_code_tail; eauto. instantiate (1 := 0).
  intros [pos' [P [Q R]]].
  exists tc; exists (rs#PC <- (Eval (Vptr b (Int.repr pos')))).
  exists (Int.repr pos').
  split. unfold goto_label. rewrite P. rewrite Npc. auto.
  assert (IUR: Int.unsigned (Int.repr pos') = pos').
  { rewrite Int.unsigned_repr. 
    auto.
    generalize (transf_function_no_overflow _ _ TF). omega.
  }
  repSplit.
  - Simplifs. 
  - constructor; auto.
    rewrite IUR. replace (pos' - 0) with pos' in Q.
    auto. omega.
  - intros. Simplifs. 
Qed.

(** Existence of return addresses *)

Lemma return_address_exists:
  forall f sg ros c, is_tail (Mcall sg ros :: c) f.(Mach.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. eapply Asmgenproof0.return_address_exists; eauto. 
- intros. exploit transl_instr_label; eauto. 
  destruct i; try (intros [A B]; apply A). intros. subst c0. repeat constructor.
- intros. monadInv H0. 
  destruct (zlt Int.max_unsigned (list_length_z (fn_code x))); inv EQ0.
  monadInv EQ. rewrite transl_code'_transl_code in EQ0.
  exists x; exists true; split; auto. unfold fn_code. repeat constructor.
- exact transf_function_no_overflow.
Qed.

(** * Proof of semantic preservation *)

(** Semantic preservation is proved using simulation diagrams
  of the following form.
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant is the [match_states] predicate below, which includes:
- The PPC code pointed by the PC register is the translation of
  the current Mach code sequence.
- Mach register values and PPC register values agree.
*)

(* Definition find_symbol_in_bound {F V: Type} (t: Genv.t F V) m := *)
(*   forall fid f', *)
(*     Genv.find_symbol t fid = Some f' -> *)
(*     Mem.in_bound_m 0 m f'. *)


(* Lemma exec_instr_wfpc *)
(* : forall (ge: genv) (fn : function) i rs1 m rs2 m' b o bra ora *)
(*          (RP: reg_ptr rs1 PC b o) *)
(*          (Ra: reg_ptr rs1 RA bra ora) *)
(*          (EI: exec_instr ge fn i rs1 m = Next rs2 m'), *)
(*   exists bb oo, reg_ptr rs2 PC bb oo. *)
(* Proof. *)
(*   intros until i; pose (N:=i); des i; unfold exec_load, exec_store, goto_label in EI; *)
(*   repeat (revert EI; destr); inv EI; eexists; eexists; srp; eauto. *)
(* Qed. *)

Lemma pou_set:
  forall rs1 r v,
    (v = Eval (Vint Int.zero) \/ exists b o, v = Eval (Vptr b o)) ->
    ptr_or_zero rs1 # r <- v r.
Proof.
  unfold ptr_or_zero; intros.
  destr; dex; subst; srp; eauto.
Qed.


Lemma exec_instr_wfpc
: forall (ge: genv) (fn : function) i rs1 m rs2 m' 
         (RP: ptr_or_zero rs1 PC)
         (Ra: ptr_or_zero rs1 RA)
         (EI: exec_instr ge fn i rs1 m = Next rs2 m'),
    ptr_or_zero rs2 PC.
Proof.
  intros. 
  des i; unfold exec_load, exec_store, goto_label in EI;
  repeat (revert EI; destr); inv EI;
  try (apply nextinstr_pcu; srp; fail);
  try (apply pou_set; eauto; fail).
  apply pou_set.
  destruct Ra; eauto.
Qed.

Lemma exec_instr_wfra
: forall (ge: genv) (fn : function) i rs1 m rs2 m' 
         (RP: ptr_or_zero rs1 PC)
         (Ra: ptr_or_zero rs1 RA)
         (EI: exec_instr ge fn i rs1 m = Next rs2 m'),
    ptr_or_zero rs2 RA.
Proof.
  intros.  (* destruct RP; destruct Ra; dex. *)
  
  des i; unfold exec_load, exec_store, goto_label in EI;
  repeat (revert EI; destr); inv EI; try (destruct RP; destruct Ra; dex;
                                          try (right; srp; fail);
                                          try (left; eexists; eexists; srp; eauto; fail); fail).
  
Qed.

Lemma exec_straight_wfra
: forall (ge: genv) (fn : function) i rs1 m k rs2 m' 
         (EI: exec_straight ge fn i rs1 m k rs2 m')
         (RP: ptr_or_zero rs1 PC)
         (Ra: ptr_or_zero rs1 RA),
    ptr_or_zero rs2 RA.
Proof.
  induction 1; simpl; intros.
  eapply exec_instr_wfra; eauto.
  exploit exec_instr_wfpc; eauto.
  exploit exec_instr_wfra; eauto.
Qed.

Lemma exec_straight_wfpcu
: forall (ge: genv) (fn : function) i rs1 m k rs2 m' 
         (EI: exec_straight ge fn i rs1 m k rs2 m')
         (RP: ptr_or_zero rs1 PC)
         (Ra: ptr_or_zero rs1 RA),
    ptr_or_zero rs2 PC.
Proof.
  induction 1; simpl; intros.
  exploit exec_instr_wfpc; eauto.
  exploit exec_instr_wfpc; eauto.
  intros. apply IHEI; auto.
  eapply exec_instr_wfra. eexact RP. eauto. eauto.
Qed.


Definition is_func_ptr (b: block) : Prop :=
  exists f, Genv.find_funct_ptr ge b = Some f.

Definition is_stack_ptr (b: block) : Prop :=
  Genv.find_funct_ptr ge b = None.

Inductive valid_ra : list stackframe -> block -> mem -> Prop :=
| vra_nil: forall p m, Ple p (Mem.nextblock m) -> valid_ra nil p m
| vra_cons: forall m s b bsp osp bra ora k p
              (VRA: valid_ra s bsp m)
                   (FP_RA: is_func_ptr bra)
                   (SP_SP: is_stack_ptr bsp)
                   (NDYN: ~ Mem.is_dynamic_block m bra)
                   (NDYN': ~ Mem.is_dynamic_block m bsp)
                   (IB: Mem.in_bound_m (Int.unsigned ora) m bra)
                   (IBsp: Mem.in_bound_m (Int.unsigned osp) m bsp)
                   (ORD: Plt bsp p)
                   (ORD': Plt bra p),
              valid_ra (Stackframe b (Eval (Vptr bsp osp)) (Eval (Vptr bra ora)) k :: s) p m.

Lemma func_not_stack:
  forall b,
    is_func_ptr b -> ~ is_stack_ptr b.
Proof.
  unfold is_func_ptr, is_stack_ptr.
  intros.
  des (Genv.find_funct_ptr ge b); dex; congruence.
Qed.

Lemma stack_not_func:
  forall b,
    is_stack_ptr b -> ~ is_func_ptr b.
Proof.
  unfold is_func_ptr, is_stack_ptr.
  intros.
  des (Genv.find_funct_ptr ge b); dex; congruence.
Qed.


Lemma not_func_stack:
  forall b,
    ~ is_func_ptr b -> is_stack_ptr b.
Proof.
  unfold is_func_ptr, is_stack_ptr.
  intros.
  des (Genv.find_funct_ptr ge b). exfalso; apply H; eexists; eauto. 
Qed.

Lemma not_stack_func:
  forall b,
    ~ is_stack_ptr b -> is_func_ptr b.
Proof.
  unfold is_func_ptr, is_stack_ptr.
  intros.
  des (Genv.find_funct_ptr ge b). eexists; eauto. 
Qed.





Inductive match_states: Mach.state -> Asm.state -> Prop :=
| match_states_intro:
    forall s fb sp bsp osp c ep ms m m' rs f tf tc o
           (FFP_VB: forall b f,
                   Genv.find_funct_ptr ge b = Some f ->
                   Mem.valid_block m b /\ ~ Mem.is_dynamic_block m b)
           (FFP: forall b f tf,
                   transf_function f = OK tf -> 
                   Genv.find_funct_ptr ge b = Some (Internal f) ->
                   Mem.bounds_of_block m b = (0, list_length_z (fn_code tf) + 1))
           (Npc: reg_ptr rs PC fb o)
           (STACKS: match_stack ge s)
           (VRA: valid_ra s bsp m)
           (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
           (* (NDYNfb: ~ Mem.is_dynamic_block m fb) *)
           (NDYNsp: ~ Mem.is_dynamic_block m bsp)
           (MEXT: mem_lessdef m m')
           (AT: transl_code_at_pc ge fb o f c ep tf tc)
           (SPbnds: Mem.in_bound_m (Int.unsigned osp) m bsp)
           (SPex: sp = Eval (Vptr bsp osp))
           (AG: agree ms sp rs)
           (DXP: ep = true -> Val.lessdef (parent_sp s) rs#EDX)
           (SPRA: forall sb so,
                    Mem.mem_norm m' sp = Vptr sb so ->
                    is_stack_ptr sb),
      match_states (Mach.State s fb sp c ms m)
                   (Asm.State rs m')
| match_states_call:
    forall s fb ms m m' rs p
           (FFP_VB: forall b f,
                      Genv.find_funct_ptr ge b = Some f ->
                      Mem.valid_block m b /\ ~ Mem.is_dynamic_block m b)
           (FFP: forall b f tf,
                   transf_function f = OK tf -> 
                   Genv.find_funct_ptr ge b = Some (Internal f) ->
                   Mem.bounds_of_block m b = (0, list_length_z (fn_code tf) + 1))
           (STACKS: match_stack ge s)
           (SPRA: forall sb so,
                    Mem.mem_norm m' (parent_sp s) = Vptr sb so ->
                    is_stack_ptr sb)
           (VRA: valid_ra s p m)
           (MEXT: mem_lessdef m m')
           (AG: agree ms (parent_sp s) rs)
           (ATPC: reg_ptr rs PC fb Int.zero)
           (* (NDYNfb: ~ Mem.is_dynamic_block m fb) *)
           (ATLR: Val.lessdef (parent_ra s) (rs RA))
           (* (ATLR: same_eval (rs RA) (parent_ra s)) *),
      match_states (Mach.Callstate s fb ms m)
                   (Asm.State rs m')
| match_states_return:
    forall s ms m m' rs p
           (FFP_VB: forall b f,
                      Genv.find_funct_ptr ge b = Some f ->
                      Mem.valid_block m b /\ ~ Mem.is_dynamic_block m b)
           (FFP: forall b f tf,
                   transf_function f = OK tf -> 
                   Genv.find_funct_ptr ge b = Some (Internal f) ->
                   Mem.bounds_of_block m b = (0, list_length_z (fn_code tf) + 1))
           (STACKS: match_stack ge s)
           (SPRA: forall sb so,
                    Mem.mem_norm m' (parent_sp s) = Vptr sb so ->
                    is_stack_ptr sb)
           (VRA: valid_ra s p m)
           (MEXT: mem_lessdef m m')
           (AG: agree ms (parent_sp s) rs)
           (ATPC: Val.lessdef (parent_ra s) rs#PC),
      match_states (Mach.Returnstate s ms m)
                   (Asm.State rs m').

Lemma exec_straight_steps:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 o bsp osp
         (Stack: match_stack ge s)
         (MLD: mem_lessdef m2 m2')
         (FFP: Genv.find_funct_ptr ge fb = Some (Internal f))
         (Npc: reg_ptr rs1 PC fb o)
         (Nra: ptr_or_zero rs1 RA)
         (VRA: valid_ra s bsp m2)
         (SPex: sp = Eval (Vptr bsp osp))
         (SPbnds: Mem.in_bound_m (Int.unsigned osp) m2 bsp)
         (AT: transl_code_at_pc ge fb o f (i :: c) ep tf tc)
         (TIex: forall k c (TR: transl_instr f i ep k = OK c),
                exists rs2,
                  exec_straight tge tf c rs1 m1' k rs2 m2'
                  /\ agree ms2 sp rs2
                  /\ (it1_is_parent ep i = true -> Val.lessdef (parent_sp s) rs2#EDX))
         (SPRA: forall sb so,
                  Mem.mem_norm m2' sp = Vptr sb so ->
                  is_stack_ptr sb)
         (FFP_VB: forall b f,
                    Genv.find_funct_ptr ge b = Some f ->
                    Mem.valid_block m2 b /\ ~ Mem.is_dynamic_block m2 b
         )
         (FFP: forall b f tf,
                 transf_function f = OK tf -> 
                 Genv.find_funct_ptr ge b = Some (Internal f) ->
                 Mem.bounds_of_block m2 b = (0, list_length_z (fn_code tf) + 1))
         (* (NDYNfb: ~ Mem.is_dynamic_block m2 fb) *)
           (NDYNsp: ~ Mem.is_dynamic_block m2 bsp)
         (* (FSIB: find_symbol_in_bound ge m2) *),
  exists st',
    plus step tge (State rs1 m1') E0 st' /\
    match_states (Mach.State s fb sp c ms2 m2) st'.
Proof.
  intros. inversion AT. subst.  monadInv H1.  
  exploit TIex; eauto. intros [rs2 [A [B C]]]. 
  exists (State rs2 m2'); split.
  - eapply exec_straight_exec; eauto.
  - exploit exec_straight_wfpc. eexact A. eauto.
    intros D.
    exploit exec_straight_at. eexact Npc. eauto. eauto. eauto.
    intros [o' [E F]].
    econstructor; eauto. 
Qed.

Lemma exec_straight_steps_goto:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c' o bsp osp
         (Stack: match_stack ge s)
         (MLD: mem_lessdef m2 m2')
         (FFP: Genv.find_funct_ptr ge fb = Some (Internal f))
         (FL: Mach.find_label lbl f.(Mach.fn_code) = Some c')
         (Npc: reg_ptr rs1 PC fb o)
         (Nra: ptr_or_zero rs1 RA)
         (AT: transl_code_at_pc ge fb o f (i :: c) ep tf tc)
         (IIP: it1_is_parent ep i = false)
         (VRA: valid_ra s bsp m2)
         (SPex: sp = Eval (Vptr bsp osp))
         (SPbnds: Mem.in_bound_m (Int.unsigned osp) m2 bsp)
           (FFP_VB: forall b f,
                      Genv.find_funct_ptr ge b = Some f ->
                      Mem.valid_block m2 b /\ ~ Mem.is_dynamic_block m2 b)
           (FFP: forall b f tf,
                   transf_function f = OK tf -> 
                   Genv.find_funct_ptr ge b = Some (Internal f) ->
                   Mem.bounds_of_block m2 b = (0, list_length_z (fn_code tf) + 1))
         (SPRA: forall sb so,
                  Mem.mem_norm m2' sp = Vptr sb so ->
                  is_stack_ptr sb)
         (* (NDYNfb: ~ Mem.is_dynamic_block m2 fb) *)
         (NDYNsp: ~ Mem.is_dynamic_block m2 bsp)
         (TIex: forall k c (TR: transl_instr f i ep k = OK c),
                exists jmp k' rs2,
                  exec_straight tge tf c rs1 m1' (jmp :: k') rs2 m2'
                  /\ agree ms2 sp rs2
                  /\ exec_instr tge tf jmp rs2 m2' = goto_label tf lbl rs2 m2'),
  exists st',
    plus step tge (State rs1 m1') E0 st' /\
    match_states (Mach.State s fb sp c' ms2 m2) st'.
Proof.
  intros. inversion AT. subst. monadInv H1.
  exploit TIex; eauto. intros [jmp [k' [rs2 [A [B C]]]]].
  generalize (functions_transl _ _ _ FFP H0); intro FN.
  generalize (transf_function_no_overflow _ _ H0); intro NOOV.
  exploit exec_straight_steps_2; eauto. 
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto. 
  intros [tc' [rs3 [o' [GOTO [MN' [AT' OTH]]]]]].
  exists (State rs3 m2'); split.
  eapply plus_right'.
  eapply exec_straight_steps_1; eauto. 
  econstructor; eauto.
  eapply find_instr_tail. eauto. 
  rewrite C. eexact GOTO.
  traceEq. subst.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  unfold ptr_or_zero; eauto.
  unfold ptr_or_zero, reg_ptr; rewrite OTH. inv B; auto. congruence.
  congruence. 
Qed.

(** We need to show that, in the simulation diagram, we cannot
  take infinitely many Mach transitions that correspond to zero
  transitions on the PPC side.  Actually, all Mach transitions
  correspond to at least one Asm transition, except the
  transition from [Mach.Returnstate] to [Mach.State].
  So, the following integer measure will suffice to rule out
  the unwanted behaviour. *)

Definition measure (s: Mach.state) : nat :=
  match s with
  | Mach.State _ _ _ _ _ _ => 0%nat
  | Mach.Callstate _ _ _ _ => 0%nat
  | Mach.Returnstate _ _ _ => 1%nat
  end.

(** This is the simulation diagram.  We prove it by case analysis on the Mach transition. *)


Lemma loadv_lessdef :
  forall c m ptr ptr' v,
    Val.lessdef ptr ptr' ->
    Mem.loadv c m ptr = Some v ->
    Mem.loadv c m ptr' = Some v.
Proof.
  intros c m ptr ptr' v LD.
  unfold Mem.loadv.
  generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ (mem_lessdef_refl m) LD).
  rewrite lessdef_val.
  destr. inv H; auto.
Qed.

Ltac rw_loadv AG A :=
  generalize (loadv_lessdef _ _ _ _ _ (Val.add_lessdef _ _ _ _ (sp_val _ _ _ AG) (Val.lessdef_refl _))
                            A); clear A; intro A.


Lemma storev_lessdef :
  forall c m ptr ptr' v m',
    Val.lessdef ptr ptr' ->
    Mem.storev c m ptr  v = Some m' ->
    Mem.storev c m ptr' v = Some m'.
Proof.
  intros c m ptr ptr' v m' LD.
  unfold Mem.storev.
  generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ (mem_lessdef_refl m) LD).
  rewrite lessdef_val.
  destr. inv H; auto.
Qed.

Ltac rw_storev AG A :=
  generalize (storev_lessdef _ _ _ _ _ _ (Val.add_lessdef _ _ _ _ (sp_val _ _ _ AG) (Val.lessdef_refl _)) A); clear A; intro A.


Lemma list_lessdef_refl:
  forall l,
    Val.lessdef_list l l.
Proof.
  induction l; simpl; eauto.
Qed.

Lemma eval_addressing_sp_ld:
  forall sp sp' a vl oe,
    eval_addressing tge sp a vl = Some oe ->
    Val.lessdef sp sp' ->
    exists oe' : expr_sym,
      eval_addressing tge sp' a vl = Some oe' /\
      Val.lessdef oe oe'.
Proof.
  intros.
  destruct a; simpl in *;
  repeat match goal with
             H: context [match ?vl with _ => _ end = Some _] |- _ => des vl
           | H: Some _ = Some _ |- _ => inv H
           | |- exists _, _ = _ /\ _ => solve [eexists; split; eauto]
         end.
  eexists; split; eauto.
  apply Val.add_lessdef; auto.
Qed.

Lemma eval_operation_sp_ld:
  forall sp sp' op vl oe,
    eval_operation tge sp op vl = Some oe ->
    Val.lessdef sp sp' ->
    exists oe',
      eval_operation tge sp' op vl = Some oe' /\
      Val.lessdef oe oe'.
Proof.
  intros sp sp' op vl oe EOP VLD.
  destruct op; simpl in *;
  repeat match goal with
             H: context [match ?vl with _ => _ end = Some _] |- _ => des vl
           | H: Some _ = Some _ |- _ => inv H
           | |- exists _, _ = _ /\ _ => solve [eexists; split; eauto]
         end.
  eapply  eval_addressing_sp_ld; eauto.
Qed.

Lemma norm_and:
  forall m a b i,
    Mem.mem_norm m (Val.and a b) = Vint i ->
    (forall alloc em i, eSexpr alloc em a = Vint i -> i = Int.one \/ i = Int.zero) ->
    (forall alloc em i, eSexpr alloc em b = Vint i -> i = Int.one \/ i = Int.zero) ->
    Int.eq i Int.zero = false ->
    exists j k,
      Mem.mem_norm m a = Vint j /\
      Mem.mem_norm m b = Vint k /\
      i = Int.and j k.
Proof.
  intros m a b i MN A10 B10 EQf.
  generalize (Mem.norm_ld _ _ _ MN). simpl; intros LD.
  destruct (Mem.concrete_mem m).
  generalize (LD _ Normalise.dummy_em H). simpl. seval ; inv H0.
  revert H3; seval. inv H3.
  repeat eexists; repeat split; eauto;
  apply Mem.eq_norm; try constructor; red; simpl; auto; try congruence; intros alloc em H0;
  specialize (LD alloc em H0); simpl in LD; inv LD; repeat (revert H3; seval);
  apply A10 in Heqv; apply B10 in Heqv0;
  apply A10 in Heqv1; apply B10 in Heqv2;
  destr; subst; auto; inv H3;
  try rewrite Int.and_zero in EQf; rewrite Int.eq_true in EQf; discriminate.
Qed.

Lemma norm_or_zero:
  forall m a b,
    Mem.mem_norm m (Val.or a b) = Vint Int.zero ->
    (forall alloc em i, eSexpr alloc em a = Vint i -> i = Int.one \/ i = Int.zero) ->
    (forall alloc em i, eSexpr alloc em b = Vint i -> i = Int.one \/ i = Int.zero) ->
    Mem.mem_norm m a = Vint Int.zero /\
    Mem.mem_norm m b = Vint Int.zero.
Proof.
  intros m a b MN A10 B10.
  generalize (Mem.norm_ld _ _ _ MN). simpl; intros LD.
  split;   apply Mem.eq_norm; try constructor; red; simpl; auto; try congruence; intros al em COMP;
  specialize (LD al em COMP); inv LD;
  repeat (revert H1; seval);
  apply A10 in Heqv; apply B10 in Heqv0; destr; subst; auto;
  discriminate.
Qed.

Lemma eval_testcond_10:
  forall c rs alloc em i,
    eSexpr alloc em (eval_testcond c rs) = Vint i ->
    i = Int.one \/ i = Int.zero.
Proof.
  des c; 
   match goal with
             H : context [eSexpr ?al ?em ?v] |- _ =>
             repeat match goal with
                 H: eSexpr ?al ?em ?v = _ |- _ => fail 
               | |- _ => revert H; seval
             end 
           | |- context [eSexpr _ _ _] => seval
         end; 
  rewrite ! lift_vint in *; destr;
  repeat match goal with
             H: Vint _ = Vint _ |- _ => inv H
         end; destr.
Qed.

Lemma se_ld:
  forall a b,
    same_eval a b ->
    Val.lessdef a b.
Proof.
  intros a b SE.
  red; intros; rewrite SE; auto.
Qed.


Lemma norm_ptr_subexpr:
  forall m1 sp b o b' o' f
         (Nsp: Mem.mem_norm m1 sp = Vptr b o)
         (Nplus: Mem.mem_norm m1 (Val.add sp (Eval (Vint f))) = Vptr b' o'),
    Mem.mem_norm m1 (Eval (Vptr b (Int.add o f))) = Vptr b' o'.
Proof.
  intros.
  apply Mem.eq_norm; simpl; intros; try congruence.
  constructor; simpl; intros; try congruence.
  - red; intros alloc em H;
    generalize (Mem.norm_ld _ _ _ Nsp alloc em H)
               (Mem.norm_ld _ _ _ Nplus alloc em H).
    simpl.
    intros A B; inv A; inv B.
    rewrite <- H2 in H3. rewrite H3. simpl. sint. auto.
 Qed.


Lemma norm_ptr_subexpr_ld:
  forall m1 m sp b o b' o' f
         (Nsp: Mem.mem_norm m sp = Vptr b o)
         (LD: mem_lessdef m m1)
         (Nplus: Mem.mem_norm m1 (Val.add sp (Eval (Vint f))) = Vptr b' o'),
    Mem.mem_norm m1 (Val.add (Eval (Vptr b o)) (Eval (Vint f))) = Vptr b' o'.
Proof.
  intros.
  rewrite Mem.same_eval_eqm with (v2:=Eval (Vptr b (Int.add o f)))
    by (red; simpl; intros; sint; auto).
  erewrite norm_ptr_subexpr; eauto.
  generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ LD (Val.lessdef_refl sp)).
  rewrite Nsp. rewrite lessdef_val. intro X; inv X; auto.
Qed.


Lemma valid_ra_store:
  forall s m p (VRA: valid_ra s p m)
         c b o v m'
         (STORE: Mem.store c m b o v = Some m'),
    valid_ra s p m'.
Proof.
  induction 1; simpl; intros; constructor; auto.
  erewrite Mem.nextblock_store; eauto.
  eapply IHVRA; eauto.
  erewrite <- Genv.store_dyn; eauto.
  erewrite <- Genv.store_dyn; eauto.
  eapply Mem.store_in_bound_m_1; eauto.
  eapply Mem.store_in_bound_m_1; eauto.
Qed.

Lemma valid_ra_storev:
  forall s m p (VRA: valid_ra s p m)
         c bo v m'
         (STORE: Mem.storev c m bo v = Some m'),
    valid_ra s p m'.
Proof.
  unfold Mem.storev; intros until m'; destr.
  eapply valid_ra_store; eauto.
Qed.


Lemma storebytes_norm:
  forall m1 b o v m2 e,
    Mem.storebytes m1 b o v = Some m2 ->
    Mem.mem_norm m1 e = Mem.mem_norm m2 e.
Proof.
  intros.
  generalize (Mem.bounds_of_block_storebytes _ _ _ _ _ H).
  generalize (Mem.nat_mask_storebytes _ _ _ _ _ H).
  intros M B.
  apply Mem.norm_same_compat; auto.
Qed.


Lemma valid_ra_storebytes:
  forall s m p (VRA: valid_ra s p m)
         b o v m'
         (STORE: Mem.storebytes m b o v = Some m'),
    valid_ra s p m'.
Proof.
  induction 1; simpl; intros; constructor; eauto.
  erewrite Mem.nextblock_storebytes; eauto.
  rewrite <- Mem.is_block_dynamic_storebytes; eauto.
  rewrite <- Mem.is_block_dynamic_storebytes; eauto.
  unfold Mem.in_bound_m.
  erewrite <- Mem.bounds_of_block_storebytes; eauto.
  unfold Mem.in_bound_m.
  erewrite <- Mem.bounds_of_block_storebytes; eauto.
Qed.

Lemma norm_ra_eq:
  forall m s b o p
         (Rra : Mem.mem_norm m (parent_ra s) = Vptr b o)
         (VRA : valid_ra s p m),
    parent_ra s = Eval (Vptr b o).
Proof.
  intros.
  inv VRA.
  - simpl in *. rewrite Mem.norm_val in Rra; congruence.
  - simpl in *.
    rewrite Mem.norm_val in Rra; inv Rra; auto.
Qed.

Lemma valid_ra_same_bounds:
  forall s m m' p
         (VRA: valid_ra s p m)
         (B: forall b, Plt b (Mem.nextblock m) -> ~ Mem.is_dynamic_block m b ->
                  Mem.bounds_of_block m' b = Mem.bounds_of_block m b)
         (D: forall b, Plt b (Mem.nextblock m) -> (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b))
         (NB: Ple (Mem.nextblock m) (Mem.nextblock m')),
    valid_ra s p m'.
Proof.
  induction 1; simpl; intros.
  - constructor; eauto.
    unfold Mem.valid_block in *. xomega.
  - repeat (trim IHVRA; [clear IHVRA|]).
    + intros; eapply B; eauto. 
    + intros; eapply D. auto. 
    + auto.
    +
      generalize (Mem.in_bound_valid _ _ _ IB), (Mem.in_bound_valid _ _ _ IBsp).
      unfold Mem.valid_block.
      constructor; auto.
      rewrite <- D; eauto.
      rewrite <- D; eauto.
      unfold Mem.in_bound_m; rewrite B; auto.
      unfold Mem.in_bound_m; rewrite B; auto. 
Qed.

Lemma extcall_vra:
  forall ef el m t e m',
    external_call ef ge el m t e m' ->
    forall s p,
      valid_ra s p m ->
      valid_ra s p m'.
Proof.
  intros.
  eapply valid_ra_same_bounds. eauto.
  eapply extcall_bounds; eauto.
  eapply external_call_dyn; eauto.
  eapply external_call_nextblock; eauto.
Qed.

Lemma alloc_vra:
  forall s m p (VRA: valid_ra s p m) lo hi m' b
         (AL: Mem.alloc m lo hi Normal = Some (m', b))
         (* (SPN: stack_ptr_norm s m) *),
    valid_ra s p m'.
Proof.
  induction 1; simpl; intros; (* inv SPN; *) constructor; eauto.
  - erewrite Mem.nextblock_alloc; eauto. xomega.
  - rewrite <- Mem.is_block_dynamic_alloc; eauto.
  - rewrite <- Mem.is_block_dynamic_alloc; eauto.
  - eapply Mem.alloc_in_bound; eauto.
  - eapply Mem.alloc_in_bound; eauto.
Qed.

Lemma compat_free_change:
  forall m cm q
         (COMP: Mem.compat_m m q cm)
         b (SZ: Mem.size_block m b <= 0)
         k (RNG: 0 < two_power_nat MA * k < Int.max_unsigned),
    Mem.compat_m m q (fun bb => if peq b bb then Int.repr (two_power_nat MA *k) else cm bb).
Proof.
  intros m cm q COMP b SZ k RNG.
  inv COMP.
  Local Opaque Z.mul two_power_nat.
  constructor; simpl; intros; (destruct (peq b b0); [try solve [subst; unfold Mem.size_block, Mem.bounds_of_block, Alloc.get_size, in_bound in *; revert SZ; destr; try des p; try omega]|eauto]).
  - subst.
    unfold Mem.size_block, Mem.bounds_of_block, Alloc.get_size, in_bound in *. destr.
    revert SZ; destr; try des p; try omega.
  - destr.
    + subst. clear - H1 SZ.
      unfold Mem.size_block, Mem.bounds_of_block, Alloc.get_size, in_bound in *. 
      revert SZ; destr; try des p; try omega.
    + eauto.
  - unfold Mem.nat_mask, Mem.mask.
    generalize (Mem.alignment_ok m b0). destr.
    specialize (H _ eq_refl).
    IntFacts.solve_int.
    rewrite Int.bits_not; auto.
    rewrite ! two_power_nat_two_p.
    rewrite Z.mul_comm, <- Byte.Zshiftl_mul_two_p; auto. 2: omega.
    rewrite Int.testbit_repr; auto.
    rewrite Z.shiftl_spec; auto.
    rewrite Int.testbit_repr, Int.Ztestbit_two_p_m1; auto.
    destr. rewrite andb_false_r. symmetry.
    rewrite Z.testbit_neg_r. auto. omega.
    apply andb_true_r. omega.
    change (two_power_nat 0 - 1) with 0.
    change (Int.repr 0) with Int.zero. rewrite Int.not_zero.
    apply  Int.and_mone.
Qed.

    


(* Lemma valid_ra_same_bounds_plt: *)
(*   forall s m m' p *)
(*          (VRA: valid_ra s p m) *)
(*          (B: forall b, Plt b p \/ is_func_ptr b -> Mem.bounds_of_block m' b = Mem.bounds_of_block m b) *)
(*          (* (M: forall b, Plt b p -> Mem.nat_mask m' b = Mem.nat_mask m b) *) *)
(*          (NB: Ple (Mem.nextblock m) (Mem.nextblock m')), *)
(*     valid_ra s p m'. *)
(* Proof. *)
(*   induction 1; simpl; intros; constructor; eauto. xomega. *)
(*   eapply IHVRA; intros; eauto. *)
(*   apply B. des H. left. xomega.  *)
(*   unfold Mem.in_bound_m; rewrite B. auto. auto.  *)
(*   unfold Mem.in_bound_m; rewrite B. *)
(*   auto. auto. *)
(* Qed. *)

Lemma valid_ra_same_bounds':
  forall s m m' p
         (VRA: valid_ra s p m)
         (B: forall b, Plt b p -> ~ Mem.is_dynamic_block m b ->
                  Mem.bounds_of_block m' b = Mem.bounds_of_block m b)
         (D: forall b, Plt b p -> (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b))
         (NB: Ple (Mem.nextblock m) (Mem.nextblock m')),
    valid_ra s p m'.
Proof.
  induction 1; simpl; intros.
  - constructor; eauto.
    unfold Mem.valid_block in *. xomega.
  - repeat (trim IHVRA; [clear IHVRA|]).
    + intros; eapply B; eauto.  xomega.
    + intros; eapply D; eauto.  xomega.
    + auto.
    +
      constructor; auto.
      rewrite <- D; eauto.
      rewrite <- D; eauto.
      unfold Mem.in_bound_m; rewrite B; auto. 
      unfold Mem.in_bound_m; rewrite B; auto. 
Qed.


Lemma valid_ra_free:
  forall m s stk
         (VRA : valid_ra s stk m)
         m' lo sz
         (* (SP: is_stack_ptr stk) *)
         (FREE : Mem.free m stk lo sz = Some m'),
    valid_ra s stk m'.
Proof.
  induction 1; simpl; intros; constructor; eauto.
  erewrite Mem.nextblock_free; eauto.
  eapply valid_ra_same_bounds'; eauto.
  intros. erewrite Mem.bounds_free; eauto.
  intro; subst. xomega.
  intros; symmetry; eapply Mem.is_block_dynamic_free; eauto.
  erewrite <- Mem.nextblock_free; eauto. xomega.
  rewrite Mem.is_block_dynamic_free; eauto.
  rewrite Mem.is_block_dynamic_free; eauto.
  unfold Mem.in_bound_m.
  erewrite Mem.bounds_free; eauto. intro; subst. xomega. 
  unfold Mem.in_bound_m.
  erewrite Mem.bounds_free; eauto. intro; subst. xomega.
Qed.

Lemma valid_ra_free_high:
  forall m s stk
         (VRA : valid_ra s stk m)
         m' b
         (ISP: is_stack_ptr b)
         (PLE: Ple stk b)
         lo hi
         (FREE : Mem.free m b lo hi = Some m'),
    valid_ra s stk m'.
Proof.
  induction 1; simpl; intros; eauto.
  - constructor. erewrite Mem.nextblock_free; eauto.
  - specialize (fun b => IHVRA  _ _ ISP b _ _ FREE).
    trim IHVRA. xomega.
    constructor; auto.
    rewrite Mem.is_block_dynamic_free; eauto.
    rewrite Mem.is_block_dynamic_free; eauto.
    unfold Mem.in_bound_m.
    erewrite Mem.bounds_free; eauto. intro; subst. xomega. 
    unfold Mem.in_bound_m.
    erewrite Mem.bounds_free; eauto. intro; subst. xomega.
Qed.
    
Lemma valid_ra_freelist:
  forall l m s stk
         (VRA : valid_ra s stk m)
         m' 
         (SP: Forall (fun a => is_stack_ptr (fst (fst a)) /\ Ple stk (fst (fst a))) l)
         (FREE : Mem.free_list m l = Some m'),
    valid_ra s stk m'.
Proof.
  induction l; simpl; intros.
  inv FREE; auto.
  destruct a as [[b lo] hi]. inv SP.
  des (Mem.free m b lo hi).
  eapply IHl; [idtac|eauto|eauto].
  eapply valid_ra_free_high; eauto.
Qed.

Lemma lessdef_ptr_eq:
  forall b o b' o'
         (LD : Val.lessdef (Eval (Vptr b o)) (Eval (Vptr b' o'))),
    Vptr b o = Vptr b' o'.
Proof.
  intros.
  generalize (LD (fun bb => if peq bb b then Int.zero else Int.one) Normalise.dummy_em).
  generalize (LD (fun bb => if peq bb b' then Int.zero else Int.one) Normalise.dummy_em).
  simpl.
  rewrite ! peq_true.
  des (peq b b'); try des (peq b' b);
    repeat rewrite peq_true in *;
    apply lessdef_vint in H; apply lessdef_vint in  H0;
    rewrite ! Int.add_zero_l in *; try subst; auto.
  rewrite <- H in H0.
  contradict H0. clear.
  rewrite Int.add_commut. rewrite (Int.add_commut _ o). sint.
  change (o <> Int.add o (Int.repr 2)).
  replace o with (Int.add o Int.zero) at 1.
  intro.
  apply int_add_eq_l in H. discriminate.
  apply Int.add_zero.
Qed.
  
Lemma valid_ra_sup:
  forall m s p (VRA : valid_ra s p m) q (ple: Ple p q) (plt: Plt q (Mem.nextblock m)),
    valid_ra s q m.
Proof.
  induction 1; simpl; intros; constructor; eauto. xomega.
  xomega. xomega.
Qed.

Lemma valid_ra_nb:
  forall m s p (VRA : valid_ra s p m),
    valid_ra s (Mem.nextblock m) m.
Proof.
  induction 1; simpl; intros; constructor; eauto. xomega.
  eapply Mem.in_bound_valid; eauto.
  eapply Mem.in_bound_valid; eauto.
Qed.

Lemma in_bound_valid:
  forall m o b,
    Mem.in_bound_m (Int.unsigned o) m b ->
    Mem.valid_block m b.
Proof.
  unfold Mem.in_bound_m, in_bound.
  intros.
  destruct (Mem.bounds_of_block m b) eqn:?.
  simpl in *.
  apply (Mem.bounds_of_block_valid _ _ _ _ Heqp).
  omega.
Qed.

(* Lemma alloc_norm_nempty: *)
(*   forall m s m1 stk o b i *)
(*          (ALLOC : Mem.alloc m 0 s = Some (m1, stk)) *)
(*          (MN : Mem.mem_norm m1 (Eval (Vptr stk o)) = Vptr b i), *)
(*     s > 0. *)
(* Proof. *)
(*   intros. *)
(*   rewrite Mem.norm_ptr_ptr in MN; inv MN. *)
(*   generalize (Mem.norm_ld _ _ _ _ MN). simpl. *)
(*   intro X. *)
(*   destruct (Mem.concrete_mem m1) as [al COMP]. *)
(*   des (zlt 0 s). omega. *)
(*   cut (Mem.size_block m1 stk <= 0). intro SB. *)
(*   assert (0 < 8 * 1 < Int.max_unsigned) by (vm_compute; intuition congruence). *)
(*   assert (0 < 8 * 2 < Int.max_unsigned) by (vm_compute; intuition congruence). *)
(*   generalize (X _ Normalise.dummy_em *)
(*                 (compat31_32 _ _ _ *)
(*                              (compat_free_change _ _ _ COMP stk SB _ H))). *)
(*   generalize (X _ Normalise.dummy_em *)
(*                 (compat31_32 _ _ _ *)
(*                              (compat_free_change _ _ _ COMP stk SB _ H0))). *)
(*   simpl. *)
(*   rewrite ! peq_true. *)
(*   intro Z; apply lessdef_vint in Z. *)
(*   intro ZZ; apply lessdef_vint in ZZ. *)
(*   des (peq stk b). *)
(*   generalize (Mem.norm_gr m1 (Eval (Vptr b o)) Ptr). *)
(*   rewrite MN. simpl. revert SB; unfold Mem.size_block, Mem.bounds_of_block, Alloc.get_size. *)
(*   destr; try des p; unfold in_bound in *; simpl in *; omega. *)
(*   rewrite ZZ in Z. *)
(*   rewrite <-! (Int.add_commut o) in Z. apply int_add_eq_l in Z. *)
(*   discriminate. *)
(*   generalize (Mem.bounds_of_block_alloc _ _ _ _ _ ALLOC). *)
(*   unfold Mem.bounds_of_block, Mem.size_block, Alloc.get_size. *)
(*   destr; try des p; inv H. rewrite Zmax_l. omega. omega. omega. *)
(* Qed. *)

Lemma lf2_ld:
  forall a b,
    list_forall2 Val.lessdef a b ->
    Val.lessdef_list a b.
Proof.
  induction 1; simpl; intros; repeat econstructor; eauto.
Qed.  

Lemma lessdef_norm:
  forall m m' v v',
    mem_lessdef m m' ->
    Val.lessdef v v' ->
    Values.Val.lessdef (Mem.mem_norm m v) (Mem.mem_norm m' v').
Proof.
  intros.
  rewrite <- lessdef_val.
  apply (rel_norm _ wf_mr_ld wf_mr_norm_ld); auto. 
Qed.

Implicit Arguments lessdef_norm.

Lemma freelist_valid:
  forall fbl m m',
    Mem.free_list m fbl = Some m' ->
    forall b,
      Mem.valid_block m b -> Mem.valid_block m' b.
Proof.
  induction fbl; simpl; intros.
  inv H; auto.
  destruct a as [[bb lo] hi].
  des (Mem.free m bb lo hi).
  eapply IHfbl; eauto.
  eapply Mem.valid_block_free_1; eauto.
Qed.




Require Import Tactics.

Theorem step_simulation:
  forall S1 t S2, Mach.step return_address_offset ge S1 t S2 ->
                  forall S1' (MS: match_states S1 S1'),
                    (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
                    \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS.

  - (* Mlabel *) 
    left; eapply exec_straight_steps; eauto; intros.
    inv AG; auto.
    monadInv TR. econstructor; split. eapply exec_straight_one. simpl; eauto.
    srp. 
    split. apply agree_nextinstr; auto. simpl; congruence.

  - (* Mgetstack *)
    unfold load_stack in H.
    exploit loadv_mem_rel; eauto. intros [v' [A B]].
    rw_loadv AG A.
    left; eapply exec_straight_steps; eauto.
    inv AG; auto. intros. simpl in TR.
    exploit loadind_correct; eauto.
    intros [rs' [P [Q R]]].
    exists rs'; split. eauto.
    split. eapply agree_set_mreg; eauto. subst. auto. 
    unfold ptr_or_zero, reg_ptr. left. erewrite exec_straight_wfpc; eauto.
    inv AG. 
    eapply exec_straight_wfra; eauto.
    simpl; congruence.

  - (* Msetstack *)
    unfold store_stack in H.
    assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
    exploit storev_rel; eauto.  auto.
    
    intros [m2' [A B]]. 
    left; eapply exec_straight_steps; eauto.
    inv AG; auto.
    eapply valid_ra_storev; eauto.
    unfold Mem.in_bound_m, in_bound; erewrite <- Mem.storev_bounds; eauto.
    (* eapply spn_storev; eauto. *)
    rw_storev AG A.
    intros. simpl in TR.
    exploit storeind_correct; eauto. intros [rs' [P Q]].
    exists rs'. repSplit.
    + eauto.
    + inversion AG. eapply agree_undef_regs; eauto.
      unfold ptr_or_zero; eapply exec_straight_wfpcu; eauto.
      unfold ptr_or_zero; eapply exec_straight_wfra; eauto.
    + simpl. rewrite Q; auto with asmgen.
      Local Transparent destroyed_by_setstack. des ty.
    + intros. eapply SPRA. eauto.
      erewrite Mem.storev_norm; eauto.
    + intros. exploit FFP_VB; eauto.
      unfold Mem.storev in H; destr_in H.
      intros [C D]; split. eapply Mem.store_valid_block_1; eauto.
      rewrite <- Genv.store_dyn; eauto.
    + intros. exploit FFP; eauto.
      erewrite Mem.storev_bounds; eauto.   
    + unfold Mem.storev in  H; destr_in H.
      rewrite <- Genv.store_dyn; eauto.

  - (* Mgetparam *)
    assert (f0 = f) by congruence; subst f0.
    unfold load_stack in *.
    exploit loadv_mem_rel. apply wf_mr_ld. eauto. eexact H0.
    intros [parent' [A B]].
    rw_loadv AG A.
    exploit loadv_mem_rel. apply wf_mr_ld. eauto. eexact H2. 
    intros [v' [C D]].
    Opaque loadind.
    left; eapply exec_straight_steps; eauto; intros.
    inv AG; auto.
    assert (DIFF: negb (mreg_eq dst DX) = true -> IR EDX <> preg_of dst).
    { intros. change (IR EDX) with (preg_of DX). red; intros. 
      unfold proj_sumbool in H1. destruct (mreg_eq dst DX); try discriminate.
      elim n. eapply preg_of_injective; eauto.
    }
    destruct ep; simpl in TR.
    + (* EDX contains parent *)
      exploit loadind_correct. eauto.  eexact TR.
      erewrite loadv_lessdef. eauto. apply Val.add_lessdef. apply DXP; auto. auto. eauto.
      intros [rs1 [P [Q R]]].
      {
        exists rs1; repSplit.
        - eauto.
        - eapply agree_set_mreg.
          + eapply agree_set_mreg; eauto. red; intros; simpl; auto. inv AG; auto. inv AG; auto.
          + subst; auto.
            red; intros. rewrite <- H3. auto.
          + auto. 
          + inv AG;  eapply exec_straight_wfpcu; eauto.
          + inv AG; 
            eapply exec_straight_wfra; eauto.
        - simpl; intros.  rewrite R; auto. 
      }
    + (* EDX does not contain parent *)
      monadInv TR.
      exploit loadind_correct. eauto. eexact EQ0. eauto. intros [rs1 [P [Q R]]]. simpl in Q.
      exploit exec_straight_wfpc. eexact P. eauto. intros E.
      exploit loadind_correct. eexact E. eexact EQ. rewrite Q.
      erewrite loadv_lessdef. eauto. apply Val.add_lessdef.
      eapply Val.lessdef_trans with (parent_sp s); eauto.
      red; intros. rewrite <- H1. auto. auto. 
      eauto.
      intros [rs2 [S [T U]]]. 
      {
        exists rs2;  repSplit.
        - eapply exec_straight_trans; eauto.
        - eapply agree_set_mreg.
          + eapply agree_set_mreg; eauto. red; intros; simpl; auto.
            inv AG; auto. eapply exec_straight_wfpcu; eauto.
            inv AG; auto. eapply exec_straight_wfra; eauto. 
          + subst; auto.
            eapply Val.lessdef_trans; [|eauto].
            apply se_ld; symmetry; auto. 
          + auto. 
          + inv AG; eapply exec_straight_wfpcu; eauto.
            eapply exec_straight_wfpcu; eauto.
            eapply exec_straight_wfra; eauto.
          + inv AG; auto. 
            eapply exec_straight_wfra; eauto. unfold ptr_or_zero; eauto. 
            eapply exec_straight_wfra; eauto.
        - simpl; intros.  rewrite U; auto. subst; auto.
          ldt. red; intros; rewrite <- H1; auto. 
      }

  - (* Mop *)
    assert (eval_operation tge (Eval (Vptr bsp osp)) op rs##args = Some v). 
    { rewrite <- H. apply eval_operation_preserved. exact symbols_preserved. }
    exploit eval_operation_rel. apply wf_mr_ld. eapply Val.lessdef_list_inv. eapply preg_vals; eauto.
    eauto. (* eexact H0. *)
    intros [v' [A B]].
    exploit eval_operation_sp_ld. eexact A. apply (sp_val _ _ _ AG).
    intros [v'' [C D]].
    left; eapply exec_straight_steps; eauto; intros.
    inv AG; auto.
    simpl in TR.
    exploit transl_op_correct; eauto.
    intros [rs2 [P [Q R]]]. 
    assert (S: Val.lessdef v (rs2 (preg_of res))).
    { eapply Val.lessdef_trans; eauto.
      eapply Val.lessdef_trans; eauto.
    }
    exists rs2; split. eauto.
    split.
    + eapply agree_set_undef_mreg; eauto. 
      eapply exec_straight_wfpcu; eauto.
      unfold ptr_or_zero; eauto. inv AG; auto.
      eapply exec_straight_wfra; eauto.
      unfold ptr_or_zero; eauto. inv AG; auto.
    + simpl. congruence.

  - (* Mload *)
    assert (eval_addressing tge (Eval (Vptr bsp osp)) addr rs##args = Some a). 
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
    exploit eval_addressing_rel. apply wf_mr_ld. eapply Val.lessdef_list_inv.
    eapply preg_vals; eauto. eexact H1.
    intros [a' [A B]].
    exploit eval_addressing_sp_ld. eexact A. apply (sp_val _ _ _ AG).
    intros [a'' [E F]].
    exploit loadv_addr_rel. apply wf_mr_ld. apply wf_mr_norm_ld.
    eauto. eauto. instantiate (1:=a''). ldt.
    intros [v' [C D]].
    left; eapply exec_straight_steps; eauto; intros. inv AG; auto. simpl in TR.
    exploit transl_load_correct; eauto. intros [rs2 [P [Q R]]]. 
    exists rs2; split. eauto.
    split. eapply agree_set_undef_mreg; eauto.
    subst.  eapply Val.lessdef_trans; [eauto|]. red; intros; auto.
    inv AG; eapply exec_straight_wfpcu; eauto.
    inv AG; eapply exec_straight_wfra; eauto.
    simpl. congruence.

  - (* Mstore *)
    assert (eval_addressing tge (Eval (Vptr bsp osp)) addr rs##args = Some a). 
    { rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved. }
    exploit eval_addressing_rel. apply wf_mr_ld. eapply Val.lessdef_list_inv.
    eapply preg_vals; eauto. eexact H1.
    intros [a' [A B]].
    exploit eval_addressing_sp_ld. eexact A. apply (sp_val _ _ _ AG).
    intros [a'' [E F]].
    assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
    exploit storev_rel. apply wf_mr_ld. apply wf_mr_norm_ld. eauto. eauto.
    instantiate (1:=a''). ldt. eauto.
    intros [m2' [C D]].
    left; eapply exec_straight_steps; eauto.
    + inv AG; auto.
    + eapply valid_ra_storev; eauto.
    (* + eapply spn_storev; eauto. *)
    + unfold Mem.in_bound_m, in_bound; erewrite <- Mem.storev_bounds; eauto.
    + intros. simpl in TR. 
      exploit transl_store_correct; eauto. intros [rs2 [P Q]]. 
      exists rs2; repSplit.
      * eauto.
      * eapply agree_undef_regs; eauto.
        inv AG; eapply exec_straight_wfpcu; eauto.
        inv AG; eapply exec_straight_wfra; eauto.
      * simpl. congruence.
    + intros; eapply SPRA; eauto.
      erewrite Mem.storev_norm; eauto.
    + intros. exploit FFP_VB; eauto.
      unfold Mem.storev in H0; destr_in H0.
      intros [G I]; split. eapply Mem.store_valid_block_1; eauto.
      rewrite <- Genv.store_dyn; eauto.
    + intros. exploit FFP; eauto.
      erewrite Mem.storev_bounds; eauto.
    + unfold Mem.storev in  H0; destr_in H0; inv H0.
      rewrite <- Genv.store_dyn; eauto.
      
  - (* Mcall *)    
    assert (f0 = f) by congruence.  subst f0.
    inv AT.    
    assert (NOOV: list_length_z tf.(fn_code) <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto. 
    destruct ros as [rf|fid]; simpl in H; monadInv H4.
    + (* Indirect call *)
      des (Mem.mem_norm m (rs rf)).  repeat destr_in H; inv H.  
      generalize (code_tail_next_int _ _ _ _ NOOV H5). intro CT1.
      assert (TCA: transl_code_at_pc ge fb (Int.add o Int.one) f c false tf x).
      { econstructor; eauto. }
      exploit return_address_offset_correct; eauto. intros; subst ra.
      left; econstructor; split.
      * apply plus_one. eapply exec_step_internal. eauto.
        eapply functions_transl; eauto. eapply find_instr_tail; eauto.
        simpl. rewrite Npc.
        generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ MEXT (agree_mregs _ _ _ AG rf)); rewrite lessdef_val.
        rewrite Heqv. erewrite ireg_of_eq; eauto. intro A; inv A. 
        eauto. 
      * {  
          econstructor; eauto.  
          - econstructor; eauto.
          -
            assert (   Mem.in_bound_m (Int.unsigned (Int.add o Int.one)) m fb).
            {
              red. exploit FFP; eauto. intros Y; rewrite Y.
              unfold in_bound; simpl.   
              exploit code_tail_bounds_1. eexact CT1. omega.
            }
            constructor; eauto.
            + red; eauto.
            + eapply SPRA.
              apply Mem.norm_val.
            + eapply FFP_VB; eauto.
            + eapply in_bound_valid; eauto.
            + eapply in_bound_valid; eauto.
          - simpl. eapply agree_exten; eauto. intros. Simplifs.
            srp.  repeat eexists; eauto.
            srp.  repeat eexists; eauto.
          - generalize (Int.eq_spec i Int.zero); rewrite Heqb0; intro; subst; auto.
            srp.
        }

    + (* Direct call *)
      clear_useless.
      generalize (code_tail_next_int _ _ _ _ NOOV H5). intro CT1.
      assert (TCA: transl_code_at_pc ge fb (Int.add o Int.one) f c false tf x).
      { econstructor; eauto. }
      exploit return_address_offset_correct; eauto. intros; subst ra.
      left; econstructor; split.
      apply plus_one. eapply exec_step_internal. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
      simpl. rewrite Npc. unfold Genv.symbol_address. rewrite symbols_preserved.
      rewrite H. eauto.
      econstructor; eauto.  
      * dex; subst; econstructor; eauto.
      * {
          assert (   Mem.in_bound_m (Int.unsigned (Int.add o Int.one)) m fb ).
          {
            red. exploit FFP; eauto. intros Y; rewrite Y.
            unfold in_bound; simpl.   
            exploit code_tail_bounds_1. eexact CT1. omega.
          }
          constructor; simpl; eauto.
          - red; eauto.
          - eapply SPRA.
            apply Mem.norm_val.
          - eapply FFP_VB; eauto.
          - eapply in_bound_valid; eauto.
          - eapply in_bound_valid; eauto.
        }
      * simpl. eapply agree_exten; eauto. intuition Simplifs.
        srp; repeat eexists; eauto.
        srp; repeat eexists; eauto.
      * Simplifs.


  - (* Mtailcall *) 
    assert (f0 = f) by congruence.  subst f0.
    inv AT. clear_useless.
    assert (NOOV: list_length_z tf.(fn_code) <= Int.max_unsigned).
    { eapply transf_function_no_overflow; eauto. }
    unfold load_stack in *.
    exploit loadv_addr_rel. apply wf_mr_ld. apply wf_mr_norm_ld. eauto.
    eexact H2. auto. simpl. intros [parent' [A B]].
    exploit loadv_addr_rel. apply wf_mr_ld. apply wf_mr_norm_ld. eauto.
    eexact H4. auto. simpl. intros [ra' [C D]].
    exploit free_mem_rel. eauto. eauto. intros [m2' [E F]].
    destruct ros as [rf|fid]; simpl in H;  monadInv H9.
    + (* Indirect call *) 
      des (Mem.mem_norm m' (rs rf) ). 
      revert H; predSpec Int.eq Int.eq_spec i Int.zero; intros; try congruence.
      inv H0.
      generalize (code_tail_next_int _ _ _ _ NOOV H10). intro CT1.
      {

        left; econstructor; split.
        - eapply plus_left.
          generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ MEXT (sp_val _ _ _ AG)); rewrite lessdef_val.
          rewrite H1. intro X; inv X.
          + eapply exec_step_internal. 
            * eauto.
            * eapply functions_transl; eauto.
            * eapply find_instr_tail; eauto.  
            * simpl.
              rw_loadv AG C. rw_loadv AG A.
              rewrite C. rewrite A.
              rewrite <- H9. rewrite E.
              instantiate (2:= nextinstr (rs0 # ESP <- parent') # RA <- (Eval
                                                                         (match Mem.mem_norm m'0 ra' with
                                                                            Vptr bra ora => Vptr bra ora
                                                                          | _ => Vint Int.zero end)
                          )).
              generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld
                                       _ _ _ _ MEXT D).
              rewrite (Mem.same_eval_eqm _ _ _ H5).
              des s.
              Focus 2. des s0.
              inv STACKS. intro H; apply lessdef_val in H. 
              rewrite Mem.norm_val in H. inv H. auto.
              rewrite Mem.norm_val. intro H; apply lessdef_val in H. inv H. simpl.
              rewrite pred_dec_true; auto.

          + apply star_one. eapply exec_step_internal with (b:=fb) (ofs:=Int.add o Int.one).
            * srp. 
            * eapply functions_transl; eauto.
            * eapply find_instr_tail; eauto. 
            * simpl. srp.  
              rewrite <- (ireg_of_eq _ _ EQ1).
              rewrite Pregmap.gso by des rf.
              generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ F (agree_mregs _ _ _ AG rf)); rewrite lessdef_val.
              rewrite Heqv. intro X; inv X. eauto.
          + traceEq.
        - econstructor; eauto.
          + intros. exploit FFP_VB; eauto.
            intros [VB DYN]. split.
            eapply Mem.valid_block_free_1 in VB; eauto.
            rewrite Mem.is_block_dynamic_free; eauto.
          + intros. exploit FFP; eauto.
            intros Y.
            generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ MEXT (Val.lessdef_refl (Eval (Vptr bsp osp)))). rewrite lessdef_val.
            rewrite H1. 
            intro LD; inv LD.
            exploit SPRA. rewrite <- H12; eauto.
            intro ISP.
            erewrite <- Mem.bounds_free in Y; [|eauto|idtac].
            auto.
            congruence.
          + clear - MEXT E SPRA AG H1 VRA SPbnds.
            intros.
            assert (forall s p m, valid_ra s p m -> parent_sp s = Eval (Vint Int.zero) \/ exists b o, parent_sp s = Eval (Vptr b o) /\ Mem.in_bound_m (Int.unsigned o) m b /\ is_stack_ptr b /\ Plt b p).
            {
              clear; induction 1; simpl; auto.
              right. eexists; eexists; split; split; eauto.
            }
            destruct (H0 _ _ _ VRA).
            rewrite H2 in H.
            rewrite Mem.norm_val in H. discriminate.
            dex. destruct H2. destruct H3. destruct H4.
            rewrite H2 in H.
            rewrite Mem.norm_val in H. inv H.  auto.

          + rewrite Mem.norm_val in H1. inv H1. 
            eapply valid_ra_free; eauto. 

          + apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
            constructor. rewrite Pregmap.gss. eapply Val.lessdef_trans; [|eexact B]. apply se_ld; symmetry; auto. 
            inv AG. auto.
            inv AG. auto.
            inv AG; intros; auto.
            srp.
            assert (LD: Val.lessdef (parent_ra s) ra').
            { red; intros. rewrite <- H5. auto. }
            assert (SE: same_eval (parent_ra s) ra').
            {
              destruct s.
              - red; intros.  specialize (LD cm em). inv LD; auto.
              - simpl. inv VRA.
                clear - LD; simpl in LD.
                red; intros.  specialize (LD cm em). inv LD; auto.
            }
            rewrite <- (Mem.same_eval_eqm _ _ _ SE).
            des s; destr; try rewrite Mem.norm_val. eauto.
            eauto. eauto.
          + srp.
          + srp.
            assert (LD: Val.lessdef (parent_ra s) ra').
            { red; intros. rewrite <- H5. auto. }
            assert (SE: same_eval (parent_ra s) ra').
            {
              destruct s.
              - red; intros.  specialize (LD cm em). inv LD; auto.
              - simpl. inv VRA.
                clear - LD; simpl in LD.
                red; intros.  specialize (LD cm em). inv LD; auto.
            }
            rewrite <- (Mem.same_eval_eqm _ _ _ SE).
            inv VRA; simpl in *; rewrite Mem.norm_val; auto.
      }
      
    + (* Direct call *)
      generalize (code_tail_next_int _ _ _ _ NOOV H10). intro CT1.
      {
        left; econstructor; split.
        - eapply plus_left.
          generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ MEXT D). rewrite lessdef_val. rewrite (Mem.same_eval_eqm  _ _ _ (H5)). 
          generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ MEXT (sp_val _ _ _ AG)). rewrite lessdef_val. rewrite H1.
          intro X; inv X.  intro X.
          eapply exec_step_internal. eauto.
          eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
          simpl. rw_loadv AG C. rw_loadv AG A.
          rewrite C. rewrite A.
          rewrite <- H11. rewrite E.
          instantiate (2:= nextinstr (rs0 # ESP <- parent') # RA <- (Eval
                                                                     (match Mem.mem_norm m'0 ra' with
                                                                        Vptr bra ora => Vptr bra ora
                                                                      | _ => Vint Int.zero end)
                      )).
          generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld
                                   _ _ _ _ MEXT D).
          rewrite (Mem.same_eval_eqm _ _ _ H5).
          rewrite lessdef_val.
          des s.
          Focus 2. des s0.
          inv STACKS. 
          rewrite Mem.norm_val. intro H0; inv H0. auto.
          rewrite Mem.norm_val. intro H0; inv H0. simpl.
          rewrite pred_dec_true; auto.

          apply star_one. eapply exec_step_internal.
          srp.
          eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
          simpl.
          unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. auto.
          traceEq.
        - econstructor; eauto.
          + intros. exploit FFP_VB; eauto.
            intros [VB DYN]. split.
            eapply Mem.valid_block_free_1 in VB; eauto.
            rewrite Mem.is_block_dynamic_free; eauto.
          + intros. exploit FFP; eauto.
            intro.
            erewrite Mem.bounds_free; eauto.
            generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ MEXT (Val.lessdef_refl (Eval (Vptr bsp osp)))). rewrite lessdef_val.
            rewrite H1. 
            intro LD; inv LD.
            exploit SPRA. rewrite <- H14; eauto. congruence.
          +    clear - MEXT E SPRA AG H1 VRA SPbnds.
            intros.
            assert (forall s p m, valid_ra s p m -> parent_sp s = Eval Vzero \/ exists b o, parent_sp s = Eval (Vptr b o) /\ Mem.in_bound_m (Int.unsigned o) m b /\ is_stack_ptr b /\ Plt b p).
            {
              clear; induction 1; simpl; auto.
              right. eexists; eexists; split; split; eauto.
            }
            destruct (H0 _ _ _ VRA).
            rewrite H2 in H.
            rewrite Mem.norm_val in H.
            discriminate.
            dex. destruct H2. destruct H3. destruct H4.
            rewrite H2 in H.
            rewrite Mem.norm_val in H. inv H.  auto.
          + rewrite Mem.norm_val in H1; inv H1.
            eapply valid_ra_free. eauto. eauto.
          + apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
            constructor; inv AG; auto.
            srp. eapply Val.lessdef_trans; [|eauto].
            apply se_ld; symmetry; auto. 
            intros. rewrite Pregmap.gso. 
            auto. des r.
            destr; eauto.             
            left; eauto.
          + srp.
          + srp.
            assert (LD: Val.lessdef (parent_ra s) ra').
            { red; intros. rewrite <- H5. auto. }
            assert (SE: same_eval (parent_ra s) ra').
            {
              destruct s.
              - red; intros.  specialize (LD cm em). inv LD; auto.
              - simpl. inv VRA.
                clear - LD; simpl in LD.
                red; intros.  specialize (LD cm em). inv LD; auto.
            }
            rewrite <- (Mem.same_eval_eqm _ _ _ SE).
            inv VRA; simpl in *;
            rewrite Mem.norm_val; auto.
      }

  - (* Mbuiltin *)
    inv AT. monadInv H2. 
    exploit functions_transl; eauto. intro FN.
    generalize (transf_function_no_overflow _ _ H1); intro NOOV.
    exploit external_call'_rel. apply wf_mr_ld. apply wf_mr_norm_ld. eauto.
    eapply Val.lessdef_list_inv. eapply preg_vals; eauto. eauto.
    intros [vres' [m2' [A [B C]]]].
    left. econstructor; split. apply plus_one. 
    eapply exec_step_builtin. eauto.
    eapply functions_transl; eauto. 
    eapply find_instr_tail; eauto.
    eapply external_call_symbols_preserved'; eauto.
    exact symbols_preserved. exact varinfo_preserved.
    eauto.
    econstructor; eauto.
    + intros; exploit FFP_VB; eauto.
      intros [VB DYN]. split.
      eapply external_call_valid_block'; eauto.
      inv H.
      rewrite <- external_call_dyn; eauto.
    + intros; exploit FFP; eauto.
      inv H. intro.
      exploit FFP_VB; eauto. intros [VB DYN].
      erewrite extcall_bounds; eauto.
    + unfold nextinstr_nf, nextinstr. 
      rewrite undef_regs_other by destr.
      rewrite set_pregs_other_2.
      rewrite undef_regs_other_2.
      rewrite Npc. simpl. srp. 
      rewrite preg_notin_charact. intros. auto with asmgen.
      rewrite preg_notin_charact. intros. auto with asmgen.
    + inv H. eapply extcall_vra. eauto. auto.
    + inv H; rewrite <- external_call_dyn; eauto.
      eapply in_bound_valid; eauto.
    + constructor; eauto. 
      eapply code_tail_next_int; eauto.
    + unfold Mem.in_bound_m. inv H.  erewrite extcall_bounds; eauto.
      eapply in_bound_valid; eauto.
    + apply agree_nextinstr_nf. eapply agree_set_mregs; auto.
      eapply agree_undef_regs; eauto.
      unfold ptr_or_zero, reg_ptr; erewrite undef_regs_other_2; eauto. 
      rewrite preg_notin_charact. intros. auto with asmgen.
      unfold ptr_or_zero, reg_ptr; erewrite undef_regs_other_2; eauto.
      inv AG; auto.
      rewrite preg_notin_charact. intros. des mr. 
      intros; erewrite undef_regs_other_2; eauto.
      eapply lf2_ld; eauto.      
    + congruence.
    + intros sb so. rewrite Mem.norm_val. intro D; inv D. 
      apply (SPRA sb so). rewrite Mem.norm_val. auto.

  - (* Mgoto *)
    assert (f0 = f) by congruence. subst f0.
    inv AT. monadInv H3. 
    exploit find_label_goto_label; eauto. intros [tc' [rs' [o' [GOTO [RP [AT2 INV]]]]]].
    left; exists (State rs' m'); split.
    apply plus_one. econstructor; eauto.
    eapply functions_transl; eauto.
    eapply find_instr_tail; eauto.
    simpl; eauto.
    inversion AT2.
    econstructor; eauto.
    eapply agree_exten; eauto with asmgen.
    unfold ptr_or_zero; eauto.
    unfold ptr_or_zero, reg_ptr; rewrite INV.
    inv AG; auto.
    discriminate.
    congruence.

  - (* Mcond true *)
    assert (f0 = f) by congruence. subst f0.
    exploit eval_condition_rel. apply wf_mr_ld. eapply Val.lessdef_list_inv.
    eapply preg_vals; eauto. eauto. eauto. intros [b1 [EC LD]].
    left; eapply exec_straight_steps_goto; eauto.
    inv AG; auto.
    intros. simpl in TR.
    destruct (transl_cond_correct tge tf cond args _ _ rs0 m' _ _ Npc TR)
      as [rs' [b0 [A [B0 [B C]]]]]. 
    unfold PregEq.t in EC. rewrite EC in B0. inv B0.
    destruct (testcond_for_condition cond); simpl in *.
    + (* simple jcc *)
      (exists (Pjcc c1 lbl), k, rs').
      split. eexact A.
      split. eapply agree_exten; eauto.
      eapply exec_straight_wfpcu; eauto. unfold ptr_or_zero; eauto. inv AG; auto.
      eapply exec_straight_wfra; eauto. unfold ptr_or_zero; eauto. inv AG; auto.
      simpl. erewrite Mem.same_eval_eqm; eauto.
      generalize (lessdef_norm MEXT LD). rewrite H0. intro D; inv D. rewrite H1. auto. 
    + (* jcc; jcc *)
      (exists (PjccOr c1 c2 lbl); exists k; exists rs').
      split. eexact A.
      split. eapply agree_exten; eauto.
      eapply exec_straight_wfpcu; eauto.  unfold ptr_or_zero; eauto. inv AG; auto.
      eapply exec_straight_wfra; eauto. unfold ptr_or_zero; eauto. inv AG; auto.
      simpl. erewrite Mem.same_eval_eqm; eauto.
      generalize (lessdef_norm MEXT LD). rewrite H0. intro D; inv D. rewrite H1. auto. 
    + (* jcc2 *)
      (exists (Pjcc2 c1 c2 lbl); exists k; exists rs').
      split. eexact A.
      split. eapply agree_exten; eauto.
      eapply exec_straight_wfpcu; eauto. unfold ptr_or_zero; eauto. inv AG; auto.
      eapply exec_straight_wfra; eauto. unfold ptr_or_zero; eauto. inv AG; auto.
      simpl.
      generalize (lessdef_norm MEXT LD).
      rewrite H0. intro D; inv D.
      erewrite <- Mem.same_eval_eqm in H6; eauto.
      rewrite <- H6. rewrite H1. auto.
      
  - (* Mcond false *)
    exploit eval_condition_rel. apply wf_mr_ld. eapply Val.lessdef_list_inv. eapply preg_vals; eauto. eauto. eauto. intros [b1 [EC LD]].
    left; eapply exec_straight_steps; eauto. inv AG; auto. intros. simpl in TR. 
    destruct (transl_cond_correct tge tf cond args _ _ rs0 m' _ _ Npc TR)
      as [rs' [b0 [A [B0 [B C]]]]]. 
    unfold PregEq.t in EC. rewrite EC in B0.
    exploit exec_straight_wfpc. eexact A. eauto. intros D. inv B0.
    destruct (testcond_for_condition cond); simpl in *.
    + (* simple jcc *)
      econstructor; split. 
      eapply exec_straight_trans. eexact A. 
      eapply exec_straight_one. simpl. erewrite Mem.same_eval_eqm; eauto.
      generalize (lessdef_norm MEXT LD). rewrite H0. intro E; inv E.
      rewrite Int.eq_true. simpl. eauto. eauto.
      srp. 
      split. apply agree_nextinstr. eapply agree_exten; eauto.
      eapply exec_straight_wfpcu; eauto. unfold ptr_or_zero; eauto. inv AG; auto.
      eapply exec_straight_wfra; eauto. unfold ptr_or_zero; eauto. inv AG; auto.
      congruence.
    + (* jcc ; jcc *)
      generalize (lessdef_norm MEXT LD). rewrite H0. intro E; inv E.
      erewrite <- Mem.same_eval_eqm in H3; eauto.
      symmetry in H3. (* destruct (norm_or_zero _ _ _ H3). *)
      (* apply eval_testcond_10. apply eval_testcond_10. *)
      econstructor; split.
      eapply exec_straight_trans. eexact A. 
      eapply exec_straight_one. simpl. rewrite H3. rewrite Int.eq_true.  simpl. eauto.
      srp.
      split. apply agree_nextinstr. eapply agree_exten; eauto.
      eapply exec_straight_wfpcu; eauto. unfold ptr_or_zero; eauto. inv AG; auto.
      eapply exec_straight_wfra; eauto. unfold ptr_or_zero; eauto. inv AG; auto.
      congruence.
    + (* jcc2 *)
      (exists (nextinstr rs'); split).
      eapply exec_straight_trans. eexact A. 
      eapply exec_straight_one. simpl.
      generalize (lessdef_norm MEXT LD).
      rewrite H0. erewrite <- Mem.same_eval_eqm; eauto.
      intro E; inv E. rewrite Int.eq_true; simpl; auto.
      eauto. srp. 
      split. apply agree_nextinstr. eapply agree_exten; eauto.
      eapply exec_straight_wfpcu; eauto. unfold ptr_or_zero; eauto. inv AG; auto.
      eapply exec_straight_wfra; eauto. unfold ptr_or_zero; eauto. inv AG; auto.
      congruence.

  - (* Mjumptable *)
    assert (f0 = f) by congruence. subst f0.
    inv AT. monadInv H5.  clear_useless.
    exploit functions_transl; eauto. intro FN.
    generalize (transf_function_no_overflow _ _ H4); intro NOOV.
    exploit find_label_goto_label; eauto. 
    intros [tc' [rs' [o' [A [B0 [B C]]]]]].
    generalize (ireg_val _ _ _ _ _ AG EQ1). intro LD.
    generalize (lessdef_norm MEXT LD); rewrite H. intro D; inv D.
    inversion B. subst.
    left; econstructor; split.
    apply plus_one. econstructor; eauto. 
    eapply find_instr_tail; eauto. 
    simpl. rewrite <- H7. unfold Mach.label in H0; unfold label; rewrite H0. eauto.
    econstructor; eauto. 
    Transparent destroyed_by_jumptable. 
    simpl. eapply agree_exten; eauto. intros. rewrite C; auto with asmgen.
    unfold ptr_or_zero; eauto.
    unfold goto_label in A; repeat destr_in A; inv A; srp.
    inv AG; auto.
    congruence.

  - (* Mreturn *) 
    assert (f0 = f) by congruence. subst f0.
    inv AT. 
    assert (NOOV: list_length_z tf.(fn_code) <= Int.max_unsigned).
    { eapply transf_function_no_overflow; eauto. }
    unfold load_stack in *.
    rw_loadv AG H1. rw_loadv AG H3.
    exploit loadv_mem_rel. apply wf_mr_ld. eauto. eexact H1. intros [parent' [A B]]. 
    exploit loadv_mem_rel. apply wf_mr_ld. eauto. eexact H3. intros [ra' [C D]]. 
    exploit free_mem_rel; eauto. intros [m2' [E F]].
    monadInv H8.
    exploit code_tail_next_int; eauto. intro CT1.
    generalize (lessdef_norm MEXT D). rewrite (Mem.same_eval_eqm _ _ _ (H4)).
    intro Y.
    left; econstructor; split.
    eapply plus_left. eapply exec_step_internal. eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
    simpl in *. rewrite C. rewrite A.
    generalize (lessdef_norm MEXT (sp_val _ _ _ AG)).
    rewrite H0. intro X; inv X.
    rewrite E.
    instantiate (2:= nextinstr (rs0 # ESP <- parent') # RA <- (Eval
                                                               (match Mem.mem_norm m'0 ra' with
                                                                  Vptr bra ora => Vptr bra ora
                                                                | _ => Vint Int.zero end)
                )).

    generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld
                             _ _ _ _ MEXT D).
    rename H into Hold. 
    rewrite (Mem.same_eval_eqm _ _ _ H4).
    intro H.
    des s.
    Focus 2. des s0.
    inv STACKS. apply lessdef_val in H. 
    rewrite Mem.norm_val in H. inv H. auto.
    rewrite Mem.norm_val in H. apply lessdef_val in H. inv H. simpl.
    rewrite pred_dec_true; auto.

    + apply star_one. eapply exec_step_internal with (b:=fb) (ofs:=Int.add o Int.one).
      * srp. 
      * eapply functions_transl; eauto.
      * eapply find_instr_tail; eauto. 
      * simpl. srp.  
    + traceEq.
    + econstructor; eauto.
      * intros. exploit FFP_VB; eauto.
        intros [VB DYN]. split.
        eapply Mem.valid_block_free_1 in VB; eauto.
        rewrite Mem.is_block_dynamic_free; eauto.
      * intros. exploit FFP; eauto.
        intros YY.
        generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ MEXT (Val.lessdef_refl (Eval (Vptr bsp osp)))). rewrite lessdef_val.
        intro LD; inv LD.
        exploit SPRA. rewrite <- H13; eauto.
        intro ISP.
        erewrite <- Mem.bounds_free in YY; [|eauto|idtac].
        auto.
        congruence. rewrite Mem.norm_val in H12; congruence.
      * clear - MEXT E SPRA AG H1 VRA SPbnds.
        intros.
        assert (forall s p m, valid_ra s p m -> parent_sp s = Eval (Vint Int.zero) \/ exists b o, parent_sp s = Eval (Vptr b o) /\ Mem.in_bound_m (Int.unsigned o) m b /\ is_stack_ptr b /\ Plt b p).
        {
          clear; induction 1; simpl; auto.
          right. eexists; eexists; split; split; eauto.
        }
        destruct (H0 _ _ _ VRA).
        rewrite H2 in H.
        rewrite Mem.norm_val in H. discriminate.
        dex. destruct H2. destruct H3. destruct H4.
        rewrite H2 in H.
        rewrite Mem.norm_val in H. inv H.  auto.

      * rewrite Mem.norm_val in H0. inv H0. 
        eapply valid_ra_free; eauto. 
      * apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
        constructor. rewrite Pregmap.gss. eapply Val.lessdef_trans; [|eexact B]. apply se_ld; symmetry; auto. 
        inv AG. auto.
        inv AG. auto.
        inv AG; intros; auto.
        srp.
        assert (LD: Val.lessdef (parent_ra s) ra').
        { red; intros. rewrite <- H4. auto. }
        assert (SE: same_eval (parent_ra s) ra').
        {
          destruct s.
          - red; intros.  specialize (LD cm em). inv LD; auto.
          - simpl. inv VRA.
            clear - LD; simpl in LD.
            red; intros.  specialize (LD cm em). inv LD; auto.
        }
        rewrite <- (Mem.same_eval_eqm _ _ _ SE).
        des s; destr; try rewrite Mem.norm_val. eauto.
        eauto. eauto.
        destr; eauto. left; eauto.
        srp.  eauto.
      * srp.
        assert (LD: Val.lessdef (parent_ra s) ra').
        { red; intros. rewrite <- H4. auto. }
        assert (SE: same_eval (parent_ra s) ra').
        {
          destruct s.
          - red; intros.  specialize (LD cm em). inv LD; auto.
          - simpl. inv VRA.
            clear - LD; simpl in LD.
            red; intros.  specialize (LD cm em). inv LD; auto.
        }
        rewrite <- (Mem.same_eval_eqm _ _ _ SE).
        inv VRA; simpl in *; rewrite Mem.norm_val; auto.
      
  - (* internal function *) 
    exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
    generalize EQ; intros EQ'. monadInv EQ'. 
    destruct (zlt Int.max_unsigned (list_length_z (fn_code x0))); inv EQ1.
    monadInv EQ0. rewrite transl_code'_transl_code in EQ1. simpl in *.
    assert (Val.lessdef (parent_ra s) (rs0 RA)).
    { exact ATLR. (* red; intros; rewrite ATLR; auto. *) }
    unfold store_stack in *. 
    exploit alloc_mem_rel. apply wf_mr_ld. eauto. eauto. 
    intros [m1' [C D]].
    exploit storev_rel. apply wf_mr_ld. apply wf_mr_norm_ld. eexact D. eexact H1. eauto. apply (sp_val _ _ _ AG). 
    intros [m2' [F G]].
    exploit storev_rel. apply wf_mr_ld. apply wf_mr_norm_ld. eexact G. eexact H2.  auto. eexact H3.
    intros [m3' [P Q]].
    left; econstructor; split.
    + apply plus_one. econstructor; eauto.  eauto.
      * simpl. rewrite Int.unsigned_zero. simpl. eauto.
      * simpl. 
        destruct (zlt 0 (Mach.fn_stacksize f)).
        {
          assert (Hsp:    Mem.mem_norm m1 sp = Vptr stk Int.zero).
          {
            clear - H0 l.
            unfold sp.
            apply Mem.norm_val.
          }

          rewrite C. simpl in F. 
          revert F; unfold Mem.storev. destr.
          erewrite norm_ptr_subexpr_ld; eauto.
          intro F; rewrite F. 
          revert P. unfold Mem.storev.
          erewrite <- ! (Mem.store_norm _ m1'); eauto. destr.
          erewrite <-  (Mem.store_norm _ m1'); eauto.
          erewrite norm_ptr_subexpr_ld; eauto.
          intro P; rewrite P. eauto.
        }
        {
          contradict H1.
          unfold Mem.storev.
          rewrite (Mem.same_eval_eqm) with (v2:= Eval (Vptr stk (fn_link_ofs f))) by
              (red; intros; unfold sp; simpl; sint;apply Int.add_zero).
          rewrite Mem.norm_val.
          intro VA. apply Mem.store_valid_access_3 in VA.
          destruct VA as [VA VA'].
          specialize (VA (Int.unsigned (fn_link_ofs f))).
          trim VA. simpl. Psatz.lia.
          eapply Mem.perm_bounds in VA.
          red in VA.
          erewrite Mem.bounds_of_block_alloc in VA; eauto.
          rewrite Z.max_l in VA by Psatz.lia.
          red in VA; destr; Psatz.lia.
        }
    + unfold sp in *. econstructor; eauto. 
      * intros.
        exploit FFP_VB; eauto. intros [VB DYN].
        split.
        generalize H2; unfold Mem.storev; destr. intros.
        eapply Mem.store_valid_block_1 with (m1:=m2); eauto.
        generalize H1; unfold Mem.storev; destr. intros.
        eapply Mem.store_valid_block_1 with (m1:=m1); eauto.
        eapply Mem.valid_block_alloc; eauto.
        unfold Mem.storev in H1, H2. destr_in H1; destr_in H2.
        rewrite <- Genv.store_dyn. rewrite <- Genv.store_dyn.
        rewrite <- Mem.is_block_dynamic_alloc. eauto. eauto. eauto. eauto.
      * intros.
        exploit FFP_VB; eauto.
        exploit FFP; eauto.
        intros. 
        erewrite <- (Mem.storev_bounds) with (m1:=m2); eauto.
        erewrite <- (Mem.storev_bounds) with (m1:=m1); eauto.
        destruct (peq b stk).
        {
          subst.
          exfalso.
          refine (Mem.fresh_block_alloc _ _ _ _ _ _ H0 _). destr.  
        }
        {
          rewrite <- H6.
          symmetry; eapply (Mem.bounds_of_block_alloc_other _ _ _ _ _ _ H0); auto.
        }      
      * srp.
      * 
        generalize H2; apply valid_ra_storev; auto.
        generalize H1; apply valid_ra_storev; auto.
        eapply alloc_vra; eauto.
        apply Mem.alloc_result in H0. subst.
        eapply valid_ra_nb; eauto.
      * unfold Mem.storev in H1, H2. destr_in H1; destr_in H2.
        rewrite <- Genv.store_dyn. 2: eexact H2.
        rewrite <- Genv.store_dyn. 2: eexact H1.
        rewrite <- Mem.is_block_dynamic_alloc. 2: eexact H0.
        unfold Mem.is_dynamic_block; rewrite Mem.blocktype_valid. destr.
        eapply Mem.fresh_block_alloc; eauto. 
      * constructor; eauto. simpl.
        eapply code_tail_next_int. simpl in g. omega. 
        constructor.

      * unfold Mem.in_bound_m.
        unfold Mem.storev in H2; destr_in H2.
        eapply Mem.in_bound_zero.
        eapply Mem.perm_bounds.
        eapply Mem.perm_store_1. eauto.
        apply Mem.store_valid_access_3 in H2.
        des H2. red in r.
        cut (stk = b). intro; subst. apply (r (Int.unsigned i)). Psatz.lia.
        erewrite (Mem.same_eval_eqm) with (v2:=Eval (Vptr stk (fn_retaddr_ofs f))) in Heqv.
        rewrite Mem.norm_val in Heqv. inv Heqv. auto.
        red; intros; simpl; sint. apply Int.add_zero.
        
      * 
        apply agree_nextinstr.
        eapply agree_change_sp. 
        Transparent destroyed_at_function_entry.
        eapply agree_undef_regs with rs0; eauto.
        inv AG; unfold ptr_or_zero, reg_ptr; srp.
        inv AG; unfold ptr_or_zero, reg_ptr; srp.
        simpl; intros. apply Pregmap.gso; auto with asmgen. tauto.
      * srp.  intros; eapply agree_sp; eauto.
      * intros.
        erewrite <- Mem.storev_norm in H4; eauto.
        erewrite <- Mem.storev_norm in H4; eauto.
        erewrite Mem.norm_val in H4. inv H4.
        apply not_func_stack.
        unfold is_func_ptr; intro. dex.
        exploit FFP_VB. eexact H4. 
        generalize (Mem.fresh_block_alloc _ _ _ _ _ _ H0).
        destr. 


  - (* external function *)
    exploit functions_translated; eauto.
    intros [tf [A B]]. simpl in B. inv B.
    exploit extcall_arguments_match; eauto. 
    intros [args' [C D]].
    exploit external_call'_rel; eauto.
    eapply Val.lessdef_list_inv; eauto.
    intros [res' [m2' [P [Q R ]]]].
    left; econstructor; split.
    apply plus_one. eapply exec_step_external; eauto. 
    eapply external_call_symbols_preserved'; eauto. 
    exact symbols_preserved. exact varinfo_preserved.
    econstructor; eauto.
    + intros; exploit FFP_VB; eauto.
      intros [VB DYN]. split.
      eapply external_call_valid_block'; eauto.
      inv H1.
      rewrite <- external_call_dyn; eauto.
    + intros; exploit FFP; eauto.
      exploit FFP_VB; eauto. intros [VB DYN].
      inv H1. erewrite <- extcall_bounds; eauto.
    + des s. intros sb so; rewrite Mem.norm_val; intro E; inv E.
      des s0. inv VRA. intros sb so; rewrite Mem.norm_val; intro E; inv E. auto.
    + inv H1. eapply extcall_vra. eauto. eauto.
    + unfold loc_external_result.
      apply agree_set_other; auto. apply agree_set_mregs; auto.
      apply lf2_ld; eauto.
      inv AG; eauto.
      
  - (* return *)
    inv STACKS. simpl in *.
    right. split. omega. split. auto. 
    inv VRA.
    econstructor; auto.
    + red. inv AG. destruct agree_pc. dex. unfold reg_ptr in H. rewrite H in *. 
      f_equal.  eapply lessdef_ptr_eq; eauto.
      apply Val.lessdef_sym. eauto. congruence. 

      rewrite H in ATPC. 
      destruct (Mem.concrete_mem m) as [al COMP].
      destruct COMP.
      generalize (addr_space f rao).
      specialize (ATPC al (fun _ _ => Byte.zero)); simpl in ATPC.
      apply lessdef_vint in ATPC.
      intro A; trim A. auto.
      rewrite ATPC in A.
      change (Int.unsigned Int.zero) with 0 in A. omega.
    + congruence. 
    + eauto.
    + eauto.
    + eauto.
    + auto.
    + congruence.
Qed.

Definition sg_prop sg:=
  forall b f tf,
    transf_function f = OK tf ->
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    sg (fn_id tf) = list_length_z (fn_code tf) + 1.

Definition sg_pos sg := forall i:ident, sg i > 0.

Lemma fid_eq:
  forall (a : Mach.fundef) (b : AST.fundef function),
    transf_fundef a = OK b -> Mach.fid a = fid b.
Proof.
  intros a b TR; des a; des b; monadInv TR.
  unfold transf_function in EQ. monadInv EQ.
  destr_in EQ1. inv EQ1.
  unfold transl_function in EQ0. monadInv EQ0. auto.
Qed.

Lemma transf_initial_states:
  forall sg
    (sg_eq: sg_prop sg)
    (sgpos: sg_pos sg)
    st1, Mach.initial_state prog sg st1 ->
  exists st2, Asm.initial_state tprog sg st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. unfold ge0 in *.
  econstructor; split.
  - econstructor.
    + eapply Genv.init_mem_transf_partial; eauto.
      apply fid_eq.
    + replace (Genv.symbol_address (Genv.globalenv tprog) (prog_main tprog) Int.zero)
      with (Vptr fb Int.zero). eauto.
      unfold Genv.symbol_address.
      rewrite (transform_partial_program_main _ _ TRANSF).
      rewrite symbols_preserved. 
      unfold ge; rewrite H1. auto.
  - econstructor; eauto.
    + intros.
      split. 
      eapply Genv.find_funct_ptr_not_fresh; eauto.
      exploit functions_translated; eauto. intros [tf0 [A B]].
      generalize (Genv.init_mem_characterization_2 fid sg sgpos
                                                   tprog b A (m:=m0)).
      erewrite Genv.init_mem_transf_partial by (eauto; apply fid_eq).
      intro C; trim C; auto.
      destr.

    + intros.
      exploit functions_translated; eauto. intros [tf0 [A B]].
      generalize (Genv.init_mem_characterization_2 fid sg sgpos
                                                   tprog b A (m:=m0)).
      erewrite Genv.init_mem_transf_partial by (eauto; apply fid_eq).
      intro C; trim C; auto.
      destr_and.
      rewrite H5. f_equal. 
      erewrite <- sg_eq; eauto.
      simpl in B. monadInv B. inv H.
      unfold Genv.size_glob', Genv.size_glob. simpl. congruence.
  + constructor.
  + intros. simpl in H3. rewrite Mem.norm_val in H3. discriminate.
  + econstructor. instantiate (1:=Mem.nextblock m0). xomega.
  + apply mem_lessdef_refl.
  + constructor.
    red; simpl; auto.
    srp; repeat eexists; eauto.
    srp; repeat eexists; eauto.
    intros.
    srp.
  + srp.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> Mach.final_state st1 r -> Asm.final_state st2 r.
Proof.
  intros. inv H0. inv H. simpl in *.
  constructor.
  - destruct (agree_pc _ _ _ AG); dex; auto.
    rewrite H in ATPC.  
    exfalso; clear - ATPC.
    generalize (ATPC (fun _ => Int.zero) (fun _ _ => Byte.zero)).
    generalize (ATPC (fun _ => Int.one) (fun _ _ => Byte.zero)).
    clear; simpl.
    intros A B.
    apply lessdef_vint in A.
    apply lessdef_vint in B.
    rewrite A in B at 1. clear - B.
    rewrite <- ! (Int.add_commut o) in B.
    apply int_add_eq_l in B.
    discriminate.
  - compute in H1. inv H1.  
    generalize (preg_val _ _ _ AX AG).
    intro LD.
    generalize (lessdef_norm MEXT LD).
    rewrite H2. intros LD'; inv LD'. auto.
Qed.

Theorem transf_program_correct:
  forall sg (sg_eq: sg_prop sg) (sg_pos: sg_pos sg),
    forward_simulation
      (Mach.semantics return_address_offset prog sg)
      (Asm.semantics tprog sg).
Proof.
  intros.
  eapply forward_simulation_star with (measure := measure).
  eexact symbols_preserved.
  apply transf_initial_states; auto.
  eexact transf_final_states.
  exact step_simulation.
Qed.

End PRESERVATION.
