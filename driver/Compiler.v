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

(** The whole compiler and its proof of semantic preservation *)

(** Libraries. *)
Require Import String.
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Smallstep.
(** Languages (syntax and semantics). *)
Require Csyntax.
Require Csem.
Require Cstrategy.
Require Cexec.
Require Clight.
Require Csharpminor.
Require Cminor.
Require CminorSel.
Require RTL.
Require LTL.
Require Linear.
Require Mach.
Require Asm.
(** Translation passes. *)
Require Initializers.
Require SimplExpr.
(* Require SimplLocalsDummy. *)
Require SimplLocals.
Require Cshmgen.
Require Cminorgen.
Require Selection.
Require RTLgen.
(* Require Tailcall. *)
(* Require Inlining. *)
Require Renumber.
Require Constprop.
Require CSE.
Require Deadcode.
Require Allocation.
Require Tunneling.
Require Linearize.
Require CleanupLabels.
Require Stacking.
Require Asmgen.
(** Proofs of semantic preservation. *)
Require SimplExprproof.
(* Require SimplLocalsDummyproof. *)
Require SimplLocalsproof.
Require Cshmgenproof.
Require Cminorgenproof.
Require Selectionproof.
Require RTLgenproof.
(* Require Tailcallproof. *)
(* Require Inliningproof. *)
Require Renumberproof.
Require Constpropproof.
Require CSEproof.
Require Deadcodeproof.
Require Allocproof.
Require Tunnelingproof.
Require Linearizeproof.
Require CleanupLabelsproof.
Require Stackingproof.
Require Asmgenproof.

(** Pretty-printers (defined in Caml). *)
Parameter print_Clight: Clight.program -> unit.
Parameter print_Cminor: Cminor.program -> unit.
Parameter print_RTL: Z -> RTL.program -> unit.
Parameter print_LTL: LTL.program -> unit.
Parameter print_Linear: Linear.program -> unit.
Parameter print_Mach: Mach.program -> unit.

Open Local Scope string_scope.

(** * Composing the translation passes *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Type)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  let unused := printer prog in prog.

Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.

(** We define three translation functions for whole programs: one
  starting with a C program, one with a Cminor program, one with an
  RTL program.  The three translations produce Asm programs ready for
  pretty-printing and assembling. *)

Definition transf_rtl_program (f: RTL.program) : res Asm.program :=
   OK f
   @@ print (print_RTL 0)
  (*  @@ time "Tail calls" Tailcall.transf_program *)
  (*  @@ print (print_RTL 1) *)
  (* @@@ time "Inlining" Inlining.transf_program *)
   @@ print (print_RTL 2)
   @@ time "Renumbering" Renumber.transf_program
   @@ print (print_RTL 3)
   @@ time "Constant propagation" Constprop.transf_program
   @@ print (print_RTL 4)
   @@ time "Renumbering" Renumber.transf_program
   @@ print (print_RTL 5)
  @@@ time "CSE" CSE.transf_program
   @@ print (print_RTL 6)
  @@@ time "Dead code" Deadcode.transf_program
   @@ print (print_RTL 7)
  @@@ time "Register allocation" Allocation.transf_program
   @@ print print_LTL
   @@ time "Branch tunneling" Tunneling.tunnel_program
  @@@ Linearize.transf_program
   @@ time "Label cleanup" CleanupLabels.transf_program
  @@@ time "Mach generation" Stacking.transf_program
   @@ print print_Mach
  @@@ time "Asm generation" Asmgen.transf_program.

Definition transf_cminor_program (p: Cminor.program) : res Asm.program :=
   OK p
   @@ print print_Cminor
  @@@ time "Instruction selection" Selection.sel_program
  @@@ time "RTL generation" RTLgen.transl_program
  @@@ transf_rtl_program.


Definition transf_clight_program (p: Clight.program) : res Asm.program :=
  OK p 
   @@ print print_Clight
  @@@ time "Simplification of locals" SimplLocals.transf_program
  @@@ time "C#minor generation" Cshmgen.transl_program
  @@@ time "Cminor generation" Cminorgen.transl_program
  @@@ transf_cminor_program.
  
Definition transf_c_program (p: Csyntax.program) : res Asm.program :=
  OK p 
  @@@ time "Clight generation" SimplExpr.transl_program
  @@@ transf_clight_program.

(** Force [Initializers] and [Cexec] to be extracted as well. *)

Definition transl_init := Initializers.transl_init.
Definition cexec_do_step := Cexec.do_step.

(** The following lemmas help reason over compositions of passes. *)

Lemma print_identity:
  forall (A: Type) (printer: A -> unit) (prog: A),
  print printer prog = prog.
Proof.
  intros; unfold print. destruct (printer prog); auto. 
Qed.

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit), 
  x @@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto. 
Qed.

(** * Semantic preservation *)

(** We prove that the [transf_program] translations preserve semantics
  by constructing the following simulations:
- Forward simulations from [Cstrategy] / [Cminor] / [RTL] to [Asm]
  (composition of the forward simulations for each pass).
- Backward simulations for the same languages
  (derived from the forward simulation, using receptiveness of the source
  language and determinacy of [Asm]).
- Backward simulation from [Csem] to [Asm]
  (composition of two backward simulations).

These results establish the correctness of the whole compiler! *)


(** We prove here determinism of Cminor evaluation, since it is needed to obtain
the backward simulation from the forward simulation.  *)

Lemma Cminor_eval_expr_determ:
  forall ge sp e m a v1,
    Cminor.eval_expr ge sp e m a v1 ->
    forall v2,
      Cminor.eval_expr ge sp e m a v2 ->
      v1 = v2.
Proof.
  induction 1; simpl; intros; eauto;
  try solve [inv H0; congruence].
  inv H1.
  apply IHeval_expr in H4. congruence.
  inv H2.
  apply IHeval_expr1 in H6.
  apply IHeval_expr2 in H8. congruence.
  inv H1.
  apply IHeval_expr in H4. congruence.
Qed.

Lemma Cminor_eval_exprlist_determ:
  forall ge sp e m a v1,
    Cminor.eval_exprlist ge sp e m a v1 ->
    forall v2,
      Cminor.eval_exprlist ge sp e m a v2 ->
      v1 = v2.
Proof.
  induction 1; simpl; intros; auto.
  inv H; auto.
  inv H1; auto.
  f_equal.
  eapply Cminor_eval_expr_determ; eauto.
  eapply IHeval_exprlist; eauto.
Qed.

Ltac detcm :=
  match goal with
      A : ?a = ?b, B : ?a = ?c |- _ => rewrite A in B; inv B
    | A: Cminor.eval_expr ?ge ?sp ?e ?m ?a ?v1,
         B: Cminor.eval_expr ?ge ?sp ?e ?m ?a ?v2 |- _ =>
      rewrite (Cminor_eval_expr_determ ge sp e m a _ A _ B) in *; clear A B
    | A: Cminor.eval_exprlist ?ge ?sp ?e ?m ?a ?v1,
         B: Cminor.eval_exprlist ?ge ?sp ?e ?m ?a ?v2 |- _ =>
      rewrite (Cminor_eval_exprlist_determ ge sp e m a _ A _ B) in *; clear A B
  end.

(* Lemma cminor_determinate: *)
(*   forall tp, *)
(*     determinate (Cminor.semantics tp). *)
(* Proof. *)
(*   intros; constructor; simpl; intros. *)
(*   - inv H; inv H0; split; auto; try constructor; *)
(*     simpl in *; try solve [exfalso; auto]; *)
(*     repeat detcm; try congruence. *)
(*     eapply Events.external_call_determ; eauto. *)
(*     generalize (Events.external_call_determ _ _ _ _ _ _ _ _ _ _ H2 H13). *)
(*     intros [A B] C. *)
(*     apply B in C. destruct C; congruence. *)
(*     inv H2; inv H14. congruence. congruence. *)
(*     generalize (Events.external_call_determ _ _ _ _ _ _ _ _ _ _ H1 H7). tauto. *)
(*     intro. *)
(*     generalize (Events.external_call_determ _ _ _ _ _ _ _ _ _ _ H1 H7). *)
(*     intros [A B]. *)
(*     apply B in H. destruct H; congruence. *)
(*   - red; intros. *)
(*     inv H; simpl; auto; *)
(*     eapply Events.external_call_trace_length; eauto. *)
(*   - inv H; inv H0. repeat detcm. *)
(*     unfold ge, ge0 in *. congruence. *)
(*   - red; intros. inv H.  intro A; inv A. *)
(*   - inv H; inv H0. *)
(*     congruence. *)
(* Qed. *)

(** We prove here determinism of Linear evaluation, since it is needed to obtain
the backward simulation from the forward simulation.  *)


Ltac detlin :=
  match goal with
      A : ?a = ?b, B : ?a = ?c |- _ => rewrite A in B; inv B
    | H: Events.external_call' _ _ _ _ _ _ _ |- _ => inv H
    | H: Events.external_call _ _ _ _ _ _ _,
         H': Events.external_call _ _ _ _ _ _ _ |- _ =>
      exploit (Events.external_call_determ); [eexact H'|eexact H|];
      clear H H'
  end.

Definition needed_stackspace_exact ns tp :=
  forall p' (COMP: Asmgen.transf_program p' = OK tp)
    f tf
    (STACK: Stacking.transf_function f = OK tf)
    b
    (GFF: Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv (V:=unit) p') b =
          Some (Internal tf)),
    Linear.fn_stacksize f + 8*  Z.of_nat (ns (Linear.fn_id f)) = Mach.fn_stacksize tf.


Definition oracle_ns (p: Asm.program) : (ident -> nat) :=
  fold_right (fun (elt: ident * globdef Asm.fundef unit)
                (acc: (ident -> nat)) =>
                let ns: ident -> nat := acc in
                match snd elt with
                  Gfun (Internal f) =>
                  (fun i => if peq i (Asm.fn_id f) then
                           NPeano.div (Asm.fn_nbextra f) 8
                         else ns i)
                | _ => ns
                end
             ) (fun _ => O) (prog_defs p).

Definition cond_globalenv (tp:Asm.program) :=
  list_norepet (prog_defs_names tp) /\
  forall b1 f1 b2 f2,
    Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv tp) b1 = Some (Internal f1) ->
    Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv tp) b2 = Some (Internal f2) ->
    Asm.fn_id f1 = Asm.fn_id f2 ->
    Asm.fn_nbextra f1 = Asm.fn_nbextra f2 /\
    list_length_z (Asm.fn_code f1) = list_length_z (Asm.fn_code f2).
    
    
Lemma in_find_funct:
  forall {F: Type} tp
         (lnr: list_norepet (prog_defs_names tp))
    i1 (f1: F)
    (IN : In (i1, Gfun (Internal f1)) (prog_defs (V:=unit) tp)),
  exists b, Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv tp) b =
       Some (Internal f1).
Proof.
  intros.
  exploit Globalenvs.Genv.find_funct_ptr_exists; eauto.
  intros [b [A B]]; exists b; auto.
Qed.

Lemma oracle_ns_correct:
  forall tp
    (Cond_Ge: cond_globalenv tp),
    needed_stackspace_exact (oracle_ns tp) tp.
Proof.
  intros.
  red; intros.
  unfold oracle_ns.
  exploit Asmgenproof.functions_translated; eauto.
  intros [tf0 [A B]].
  assert (EQ_id: Mach.fn_id tf = Linear.fn_id f).
  rewrite (Stackingproof.unfold_transf_function _ _ STACK). auto.
  erewrite <- EQ_id.

  simpl in B. monadInv B.
  replace (Mach.fn_stacksize tf) with (Asm.fn_stacksize x).
  Focus 2. unfold Asmgen.transf_function in EQ; monadInv EQ.
  revert EQ1; destr. inv EQ1.
  unfold Asmgen.transl_function in EQ0. monadInv EQ0. auto.

  assert (EQ_id': Mach.fn_id tf = Asm.fn_id x).
  {
    unfold Asmgen.transf_function in EQ; monadInv EQ.
    revert EQ1; destr. inv EQ1.
    unfold Asmgen.transl_function in EQ0. monadInv EQ0. auto.
  }
  rewrite EQ_id'.
  exploit Globalenvs.Genv.find_funct_ptr_inversion. eexact A.
  intros [id IN].

  
  assert (NBx: Asm.fn_nbextra x = Z.to_nat
                                    ((align (Stacklayout.fe_size
             (Stacklayout.make_env (Bounds.function_bounds f))) 8 -
           Linear.fn_stacksize f))).
  { unfold Asmgen.transf_function in EQ. monadInv EQ.
    unfold Asmgen.transl_function in EQ0. monadInv EQ0.
    Opaque Stacklayout.make_env Bounds.function_bounds.
    Opaque Z.mul.
    revert EQ1; destr. inv EQ1.
    unfold Stacking.transf_function in STACK.
  revert STACK. 
  repeat (destr_cond_match; try congruence).
  intro S; inv S. simpl in *. auto.
  }

  assert (Sx: Asm.fn_stacksize x = 
              align (Stacklayout.fe_size
             (Stacklayout.make_env (Bounds.function_bounds f))) 8).
  { unfold Asmgen.transf_function in EQ. monadInv EQ.
    unfold Asmgen.transl_function in EQ0. monadInv EQ0.
    Opaque Stacklayout.make_env Bounds.function_bounds.
    revert EQ1; destr. inv EQ1. simpl.
    unfold Stacking.transf_function in STACK.
    revert STACK.
    repeat (destr_cond_match; try congruence).
    intro S; inv S. simpl in *. auto.
  }

  
  
  
  
  assert (forall i1 i2 f1 f2, In (i1, Gfun (Internal f1)) (prog_defs tp) ->
                      In (i2, Gfun (Internal f2)) (prog_defs tp) ->
                      Asm.fn_id f1 = Asm.fn_id f2 ->
                      Asm.fn_nbextra f1 = Asm.fn_nbextra f2).
  {
    intros.
    destruct Cond_Ge as [lnr O].
    destruct (in_find_funct _ lnr _ _ H) as [b1 O1].
    destruct (in_find_funct _ lnr _ _ H0) as [b2 O2].
    eapply O; eauto.
  }
  revert H.
  revert IN. fold Asm.fundef.
  generalize (prog_defs tp).
  
  clear - NBx Sx. 
  Opaque Z.mul NPeano.div.
  induction l; simpl; intros; auto.
  easy.
  des IN.  
  - destr. rewrite NBx. rewrite Sx.
    rewrite div_Zdiv by Psatz.lia.
    rewrite Z2Nat.id. rewrite <- Z_div_exact_full_2. Psatz.lia.
    Psatz.lia.
    replace (Linear.fn_stacksize f) with (align (Linear.fn_stacksize f) 8).
    destruct (align_divides (Stacklayout.fe_size (Stacklayout.make_env (Bounds.function_bounds f))) 8)
      as [X xeq]. Psatz.lia.
    destruct (align_divides (Linear.fn_stacksize f) 8) as [y yeq]. Psatz.lia.
    simpl. IntFacts.elim_div. Psatz.lia.
    destruct f; auto.
    set (b:= Bounds.function_bounds f).
    generalize (Stacklayout.frame_env_separated b).
    generalize 
               (Bounds.bound_outgoing_pos b)
               (Bounds.bound_int_callee_save_pos b)
               (Bounds.bound_float_callee_save_pos b)
               (Bounds.bound_local_pos b).
    set (fe:=Stacklayout.make_env b).

    generalize (Stackingproof.bound_stack_data_stacksize f). unfold b, fe.
    generalize (align_le (Stacklayout.fe_size (Stacklayout.make_env b)) 8); Psatz.lia. 

  - simpl.  destr.
    + trim H0. 
      { destr. des a. eapply H; eauto. }
      rewrite <- H0. rewrite Sx in H0.
      f_equal.
      destr. destr.
      des a.
      erewrite H with (f2:=x); eauto.
      2: subst; eauto.
      rewrite NBx. f_equal.
      rewrite <- H0.
      assert (forall a b, a + b - a = b) by (intros; Psatz.lia).
      rewrite H1.
      rewrite Z2Nat.inj_mul by Psatz.lia.
      erewrite <- NPeano.Nat.div_unique_exact. eauto. Psatz.lia.
      rewrite Nat2Z.id. auto.
    + apply H0.
      intros; eapply H; eauto.
Qed.

Definition oracle_sg (p: Asm.program) : (ident -> Z) :=
  fold_right (fun (elt: ident * globdef Asm.fundef unit)
                (acc: (ident -> Z)) =>
                let sg: ident -> Z := acc in
                match snd elt with
                  Gfun (Internal f) =>
                  (fun i => if peq i (Asm.fn_id f) then
                            list_length_z (Asm.fn_code f) + 1
                         else sg i)
                | _ => sg
                end
             ) (fun _ => 1) (prog_defs p).

Lemma oracle_sg_correct_1:
  forall p' tp
    (Cond_Ge: cond_globalenv tp)
    (AG: Asmgen.transf_program p' = OK tp),
    Asmgenproof.sg_prop p' (oracle_sg tp).
Proof.
  intros.
  red. intros b f tf TF FF.
  unfold oracle_sg.
  exploit Asmgenproof.functions_translated; eauto.
  intros [tf0 [A B]].
  simpl in B. monadInv B.
  assert (x = tf) by congruence; subst. clear EQ.
  exploit Globalenvs.Genv.find_funct_ptr_inversion. eexact A.
  intros [id IN].
  
  cut (forall i1 i2 f1 f2, In (i1, Gfun (Internal f1)) (prog_defs tp) ->
                      In (i2, Gfun (Internal f2)) (prog_defs tp) ->
                      Asm.fn_id f1 = Asm.fn_id f2 ->
                      list_length_z (Asm.fn_code f1) = list_length_z (Asm.fn_code f2)).  
  revert IN. fold Asm.fundef.
  generalize (prog_defs tp).
  clear.
  induction l; simpl; intros; auto.
  easy.
  des IN.
  - destr.
  - simpl. destr.
    + destr. subst.
      rewrite H0. destr. des a. f_equal. eapply H.
      subst. eauto. eauto. auto.
      intros; eapply H; auto. right; eexact H1. right; eexact H2.
      apply H0.
      intros; eapply H; eauto.
    + apply H0.
      intros; eapply H; eauto.
  - intros.
    destruct Cond_Ge as [lnr O].
    destruct (in_find_funct _ lnr _ _ H) as [b1 O1].
    destruct (in_find_funct _ lnr _ _ H0) as [b2 O2].
    eapply O; eauto.
Qed.    


Definition return_address_correct {V} (p8: program (fundef Mach.function) V) sg:=
  forall f tf c ofs sig ros,
    (forall (f : Mach.function) (i : Mach.instruction) 
       (ep : bool) (k : Asm.code) (c : list Asm.instruction),
        Asmgen.transl_instr f i ep k = OK c -> is_tail k c) ->
    Stacking.transf_function f = OK tf ->
    is_tail
          (Mach.Mcall sig ros
           :: Stacking.transl_code (Stacklayout.make_env (Bounds.function_bounds f)) c) 
          (Mach.fn_code tf) ->
    Asmgenproof0.return_address_offset tf (Stacking.transl_code (Stacklayout.make_env (Bounds.function_bounds f)) c) ofs ->
    forall fb : Values.block,
      Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv (V:=V) p8) fb =
      Some (Internal tf) ->
      forall im : Memory.Mem.mem,
        Globalenvs.Genv.init_mem Mach.fid sg p8 = Some im ->
        Memory.Mem.in_bound_m (Integers.Int.unsigned ofs) im fb.

Lemma oracle_sg_pos:
  forall tp i, oracle_sg tp i > 0.
Proof.
  unfold oracle_sg; intros.
  generalize (prog_defs tp).
  induction l; simpl. Psatz.lia.
  destr. destr.
  destr. generalize (list_length_z_pos (Asm.fn_code f0)). Psatz.lia.
Qed.

Lemma oracle_sg_correct_2:
  forall p' tp
    (Cond_Ge: cond_globalenv tp)
    (AG: Asmgen.transf_program p' = OK tp),
    return_address_correct p' (oracle_sg tp).
Proof.
  intros.
  red. intros f tf c ofs sig ros Cond_ti TF IST RAO fb FFP im IM.
  red in RAO.
  exploit Asmgenproof.functions_translated; eauto.
  intros [tf0 [A B]].
  simpl in B. monadInv B.
  destruct (Asmgen.transl_code tf (Stacking.transl_code
             (Stacklayout.make_env (Bounds.function_bounds f)) c) false) eqn:?.
  - specialize (RAO _ _ EQ eq_refl).
    apply Asmgenproof0.code_tail_bounds_1 in RAO.

    exploit Globalenvs.Genv.init_mem_transf_partial; eauto.
    apply Asmgenproof.fid_eq.
    intro IM'.
    red; rewrite (fun prf => proj1 (Globalenvs.Genv.init_mem_characterization_2
                           (V:=unit)
                           Asm.fid
                           ( (oracle_sg tp)) prf tp
                           fb A IM')).
    red; simpl.
    
    exploit oracle_sg_correct_1; eauto.
    unfold Globalenvs.Genv.size_glob', Globalenvs.Genv.size_glob. simpl.
    intro B; rewrite B. omega.
    apply oracle_sg_pos.
  - exfalso.
    unfold Asmgen.transf_function in EQ. monadInv EQ.
    revert EQ1; destr. inv EQ1.
    unfold Asmgen.transl_function in EQ0. monadInv EQ0.
    simpl in *.
    rewrite Asmgenproof0.transl_code'_transl_code in EQ.

    exploit Asmgenproof0.transl_code_tail; eauto.
    intro; dex. destruct H.
    clear RAO.
    simpl in H. monadInv H.
    congruence.
Qed.


Lemma box_span_mul_plus:
  forall z y, z >= 0 -> y >= 0 ->
    Memory.Mem.box_span (8 * z + y) = (Z.to_nat z + Memory.Mem.box_span y)%nat.
Proof.
  intros.
  replace 8 with (two_power_nat Memory.MA) by (rewrite Stackingproof.ma_3; reflexivity).
  unfold Memory.Mem.box_span.
  rewrite Stackingproof.ma_3.
  replace ((two_power_nat 3 * z + y - 1) / two_power_nat 3)
    with (z + (y - 1) / two_power_nat 3).
  rewrite <- Z.add_assoc. rewrite (Z2Nat.inj_add z). auto.
  Psatz.lia.
  destruct (zlt 0 y). apply Z.add_nonneg_nonneg. apply Z.div_pos. Psatz.lia.
  vm_compute; destr.
  Psatz.lia.
  replace y with 0 by Psatz.lia. vm_compute. destr.
  rewrite Z.mul_comm.
  replace (z * two_power_nat 3 + y - 1) with (z * two_power_nat 3 + (y - 1)) by Psatz.lia.
  rewrite Z_div_plus_full_l. Psatz.lia. vm_compute. destr. 
Qed.


Theorem transf_rtl_program_correct:
  forall p tp
    (cond_ge: cond_globalenv tp)
    (TRTL: transf_rtl_program p = OK tp),
    let sg := oracle_sg tp in
    let ns := oracle_ns tp in
    forward_simulation (RTL.semantics p ns sg) (Asm.semantics tp sg)
    * backward_simulation (RTL.semantics p ns sg) (Asm.semantics tp sg).
Proof.
  intros.
  assert (F: forward_simulation (RTL.semantics p ns sg) (Asm.semantics tp sg)).
  unfold transf_rtl_program, time in TRTL.
  repeat rewrite compose_print_identity in TRTL.
  simpl in TRTL.
  (* set (p1 := Tailcall.transf_program p) in *. *)
  (* destruct (Inlining.transf_program p1) as [p11|] eqn:?; simpl in H; try discriminate. *)
  set (p12 := Renumber.transf_program p) in *.
  set (p2 := Constprop.transf_program p12) in *.
  set (p21 := Renumber.transf_program p2) in *.
  destruct (CSE.transf_program p21) as [p3|] eqn:?; simpl in TRTL; try discriminate.
  destruct (Deadcode.transf_program p3) as [p31|] eqn:?; simpl in TRTL; try discriminate.
  destruct (Allocation.transf_program p31) as [p4|] eqn:?; simpl in TRTL; try discriminate.
  set (p5 := Tunneling.tunnel_program p4) in *.
  destruct (Linearize.transf_program p5) as [p6|] eqn:?; simpl in TRTL; try discriminate.
  set (p7 := CleanupLabels.transf_program p6) in *.
  destruct (Stacking.transf_program p7) as [p8|] eqn:?; simpl in TRTL; try discriminate.
  (* eapply compose_forward_simulation. apply Tailcallproof.transf_program_correct.  *)
  (* eapply compose_forward_simulation. apply Inliningproof.transf_program_correct. eassumption. *)
  eapply compose_forward_simulation. apply Renumberproof.transf_program_correct. 
  eapply compose_forward_simulation. apply Constpropproof.transf_program_correct.
  apply oracle_sg_pos.
  eapply compose_forward_simulation. apply Renumberproof.transf_program_correct.
  eapply compose_forward_simulation. apply CSEproof.transf_program_correct. eassumption.
  apply oracle_sg_pos.
  eapply compose_forward_simulation. apply Deadcodeproof.transf_program_correct. eassumption.
  apply oracle_sg_pos.
  eapply compose_forward_simulation. apply Allocproof.transf_program_correct. eassumption.
  eapply compose_forward_simulation. apply Tunnelingproof.transf_program_correct.
  eapply compose_forward_simulation. apply Linearizeproof.transf_program_correct. eassumption. 
  eapply compose_forward_simulation. apply CleanupLabelsproof.transf_program_correct. 
  eapply compose_forward_simulation.
  {
    apply Stackingproof.transf_program_correct.
    - eexact Asmgenproof.return_address_exists.
    - eassumption.
    - intros.
      generalize (oracle_ns_correct tp cond_ge  _ TRTL _ _ TF _ GFF).
      unfold ns.
      replace
        (Mach.fn_stacksize tf)
      with (align (Stacklayout.fe_size (Stacklayout.make_env (Bounds.function_bounds f))) 8).
      rewrite <- Stackingproof.box_span_ma_3.
      rewrite <- Linear.fn_stacksize_aligned at 1.
      rewrite <- Stackingproof.box_span_ma_3.
      Psatz.lia.
      des f.        Psatz.lia.
      clear. set (b:=Bounds.function_bounds f).
      generalize (Stacklayout.frame_env_separated b). intuition.
      generalize (Bounds.bound_local_pos b); intro;
        generalize (Bounds.bound_int_callee_save_pos b); intro;
          generalize (Bounds.bound_float_callee_save_pos b); intro;
            generalize (Bounds.bound_outgoing_pos b); intro;
              generalize (Bounds.bound_stack_data_pos b); intro.
      Psatz.lia.
      
      des tf. unfold Stacking.transf_function in TF. repeat destr_in TF. 
    - intros. eapply oracle_sg_correct_2; eauto.
      intros f0 i ep k c0 TI.
      exploit Asmgenproof.transl_instr_label; eauto.
      des i; try  (red in H4; destr).
      subst. constructor. constructor.
    - apply (oracle_sg_pos).
  }
  {
    apply Asmgenproof.transf_program_correct; eauto.
    apply oracle_sg_correct_1; auto.
    red. apply (oracle_sg_pos).
  }
  split. auto. 
  apply forward_to_backward_simulation. auto. 
  apply RTL.semantics_receptive.
  apply Asm.semantics_determinate. 
Qed.

Theorem transf_cminor_program_correct:
  forall p tp (cond_ge: cond_globalenv tp),
    transf_cminor_program p = OK tp ->
    let sg := oracle_sg tp in
    let ns := oracle_ns tp in
    forward_simulation (Cminor.semantics p ns sg) (Asm.semantics tp sg)
    * backward_simulation (Cminor.semantics p ns sg) (Asm.semantics tp sg).
Proof.
  intros.
  assert (F: forward_simulation (Cminor.semantics p ns sg) (Asm.semantics tp sg)).
  unfold transf_cminor_program, time in H.
  repeat rewrite compose_print_identity in H.
  simpl in H. 
  destruct (Selection.sel_program p) as [p1|] eqn:?; simpl in H; try discriminate.
  destruct (RTLgen.transl_program p1) as [p2|] eqn:?; simpl in H; try discriminate.
  eapply compose_forward_simulation. apply Selectionproof.transf_program_correct. eauto.
  eapply compose_forward_simulation. apply RTLgenproof.transf_program_correct. eassumption.
  exact (fst (transf_rtl_program_correct _ _ cond_ge H)).

  split. auto. 
  apply forward_to_backward_simulation. auto. 
  apply Cminor.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.

Definition nssl (p: Clight.program) :=
    fold_right (fun (elt: ident * globdef Clight.fundef Ctypes.type)
                (acc: (ident -> nat)) =>
                let ns: ident -> nat := acc in
                match snd elt with
                  Gfun (Clight.Internal f) =>
                  (fun i => if peq i (Clight.fn_id f) then
                           Clight.fn_sl_save f
                         else ns i)
                | _ => ns
                end
             ) (fun _ => O) (prog_defs p).


Lemma varsort_app_comm:
  forall l1 l2,
    Permutation.Permutation (VarSort.varsort (l1 ++ l2)) (VarSort.varsort (l2 ++ l1)).
Proof.
  intros.
  rewrite <- ! VarSort.varsort_permut.
  apply Permutation.Permutation_app_comm.
Qed.

Definition cond_ge_clight (p: Clight.program) :=
  forall f1 f2 : Clight.function,
    In (Gfun (Clight.Internal f1)) (map snd (prog_defs p)) ->
    In (Gfun (Clight.Internal f2)) (map snd (prog_defs p)) ->
    Clight.fn_id f1 = Clight.fn_id f2 ->
    Clight.fn_params f1 = Clight.fn_params f2 /\
    Clight.fn_vars f1 = Clight.fn_vars f2 /\
    SimplLocals.addr_taken_stmt (Clight.fn_body f1) =
    SimplLocals.addr_taken_stmt (Clight.fn_body f2).


Lemma sl_correct:
  forall p p',
    SimplLocals.transf_program p = OK p' ->
    forall (NR: cond_ge_clight p)

    ,
    forall f : Clight.function, 

      In (Gfun (Clight.Internal f)) (map snd (prog_defs p)) ->
      nssl p' (Clight.fn_id f) = 
      Datatypes.length
        (filter
           (fun it : SimplLocals.VSet.elt * Ctypes.type =>
              SimplLocals.VSet.mem (fst it)
                                   (SimplLocalsproof.cenv_for_gen
                                      (SimplLocals.addr_taken_stmt (Clight.fn_body f))
                                      (VarSort.varsort (Clight.fn_params f ++ Clight.fn_vars f))))
           (VarSort.varsort (Clight.fn_params f ++ Clight.fn_vars f))).
Proof.
  intros p p' TP NR f.
  unfold nssl.
  unfold SimplLocals.transf_program in TP.
  unfold transform_partial_program in TP.
  unfold transform_partial_program2 in TP.
  monadInv TP.
  simpl. revert EQ.
  revert x NR.
  unfold cond_ge_clight.
  generalize ((prog_defs p)). 
  induction l; simpl; intros.
  - inv EQ; easy.
  - destruct H.
    + des a. subst.
      clear IHl.
      revert EQ; destr.
      monadInv EQ.
      monadInv Heqr.
      simpl.
      unfold SimplLocals.transf_function in EQ.
      revert EQ; destr.
      * monadInv EQ. simpl.
        rewrite peq_true. auto.
        rewrite VarSort.varsort_filter.
        rewrite <- (Permutation.Permutation_length (VarSort.varsort_permut  _ )).
        rewrite ! SimplLocalsproof.filter_app.
        rewrite ! app_length.
        rewrite plus_comm.
        rewrite <- ! app_length.
        rewrite <- ! SimplLocalsproof.filter_app.
        f_equal.
        apply Memory.Mem.filter_ext.
        intros.
        apply SimplLocalsproof.VSF.mem_m. auto.
        apply SimplLocalsproof.cenv_for_cenv_for_gen_eq; auto.
      * inv EQ.
    + des a. des g.
      * revert EQ; destr.
        monadInv EQ.
        trim (IHl x0).
        intros; eauto.
        trim IHl. auto.
        trim IHl. auto.
        simpl.
        destr. subst.
        destr.  
        unfold SimplLocals.transf_fundef in Heqr. des f0.
        monadInv Heqr.
        simpl. 
        unfold SimplLocals.transf_function in EQ.
        revert EQ; destr; monadInv EQ.
        simpl in *.
        apply NR in e; auto. subst.
        rewrite VarSort.varsort_filter.
        rewrite <- (Permutation.Permutation_length (VarSort.varsort_permut  _ )).
        rewrite ! SimplLocalsproof.filter_app.
        rewrite ! app_length.
        rewrite plus_comm.
        rewrite <- ! app_length.
        rewrite <- ! SimplLocalsproof.filter_app.
        f_equal.
        destruct e as [e1 [e2 e3]]; rewrite e1,e2, e3.
        apply Memory.Mem.filter_ext.
        intros.
        apply SimplLocalsproof.VSF.mem_m. auto.
        apply SimplLocalsproof.cenv_for_cenv_for_gen_eq; auto.
        
      * monadInv EQ.
        simpl.
        apply IHl; auto.
Qed.

Theorem transf_clight_program_correct:
  forall p tp (cond_ge: cond_globalenv tp) (cond_ge': cond_ge_clight p),
    transf_clight_program p = OK tp ->
    forall p',
      SimplLocals.transf_program p = OK p' ->
      let sg := oracle_sg tp in
      let ns := oracle_ns tp in
      let sl := nssl p' in
      let ns := fun i =>  (ns i - sl i)%nat in
    forward_simulation (Clight.semantics1 p ns sg) (Asm.semantics tp sg)
    * backward_simulation (Clight.semantics1 p ns sg) (Asm.semantics tp sg).
Proof.
 
  intros. 
  assert (F: forward_simulation (Clight.semantics1 p ns0 sg) (Asm.semantics tp sg)).
  revert H; unfold transf_clight_program, time; simpl.
  rewrite print_identity. 
  rewrite H0.
  simpl.
  caseEq (Cshmgen.transl_program p'); simpl; try congruence; intros p1 EQ1.
  caseEq (Cminorgen.transl_program p1); simpl; try congruence; intros p2 EQ2.
  intros. eapply compose_forward_simulation.
  apply SimplLocalsproof.transf_program_correct
  with (ns2 := ns) (ns1 := ns0). eauto.
	intros.
	unfold ns0, sl, ns.
	rewrite (sl_correct _ _ H0 cond_ge' _ H1). Psatz.lia.
	eapply compose_forward_simulation. apply Cshmgenproof.transl_program_correct. eauto.
	eapply compose_forward_simulation. apply Cminorgenproof.transl_program_correct. eauto.
	apply  (fst (transf_cminor_program_correct _ _ cond_ge H)).
  split. auto. 
  apply forward_to_backward_simulation. auto.
  apply Clight.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.

Fixpoint filter_map { A B : Type} (f: A -> option B) (l: list A): list B :=
  match l with
    nil => nil
  | a::r => match f a with
             Some a' => a':: filter_map f r
           | None => filter_map f r
           end
  end.

Definition cond_ge_c (p: Csyntax.program) :=
  list_norepet (prog_defs_names p) /\
  list_norepet (filter_map (fun x => match x with
                                    Gfun (Csyntax.Internal f) => Some (Csyntax.fn_id f)
                                  | _ => None
                                  end) (map snd (prog_defs p))).

Definition cond_ge_c' (p: Csyntax.program) :=
  list_norepet (prog_defs_names p) /\
  forall f1 f2 : Csyntax.function,
    In (Gfun (Csyntax.Internal f1)) (map snd (prog_defs p)) ->
    In (Gfun (Csyntax.Internal f2)) (map snd (prog_defs p)) ->
    Csyntax.fn_id f1 = Csyntax.fn_id f2 ->
    f1 = f2.

Lemma filter_map_in:
  forall {A B: Type} f l (a:A) (b:B),
  In a l -> f a = Some b ->
  In b (filter_map f l).
Proof.
  induction l; simpl; intros; eauto.
  destr. right; eapply IHl; eauto.
  eapply IHl; eauto.
Qed.

Lemma cond_ge_c_impl:
  forall p,
    cond_ge_c p -> cond_ge_c' p.
Proof.
  intros p [A B]; split; auto.
  revert B.
  generalize (prog_defs p).
  induction l; simpl; intros; eauto.
  easy.
  trim IHl. 
  repeat destr_in B; inv B; auto.
  des (snd a).
  - inv H2. inv B. exfalso; apply H3.
    rewrite H1.
    eapply filter_map_in. apply H. reflexivity.
  - inv H. inv B. exfalso; apply H3.
    rewrite <- H1.
    eapply filter_map_in. apply H2. reflexivity.
  - eapply IHl; eauto.
  - eapply IHl; eauto.
Qed.


Lemma find_funct_ptr_impl_in_snd_prog_defs:
  forall {V W: Type} (p: program V W) b f,
    Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv p) b = Some f ->
    (* (Csyntax.Internal f) -> *)
    (* list_norepet (map snd (prog_defs p)) -> *)
    In (Gfun f) (map snd (prog_defs p)).
Proof.
  unfold Globalenvs.Genv.globalenv.
  intros V W p b f.
  assert (Init: forall b f, Globalenvs.Genv.find_funct_ptr
               (Globalenvs.Genv.empty_genv V W) b = Some f ->
             In (Gfun f) (map snd (prog_defs p))).
  {
    setoid_rewrite Maps.PTree.gempty. easy.
  }
  revert Init.
  unfold prog_defs_names.
  generalize (Globalenvs.Genv.empty_genv V W).
  generalize (prog_defs p).


  intros.
  revert Init H. 
  eapply Globalenvs.Genv.add_globals_preserves.
  - intros ge id g H Init H0 H1.
    unfold Globalenvs.Genv.find_funct_ptr in H1; simpl in H1.
    des g.
    rewrite Maps.PTree.gsspec in H1.
    destr_in H1.
    inv H1. apply in_map_iff.
    eexists; split; simpl; eauto.
    simpl; auto.
  - intros Init H. eauto.
Qed.


    Ltac des t :=
      destruct t eqn:?; try subst; simpl in *;
      try intuition congruence;
      repeat
        match goal with
        | H:_ = left _ |- _ => clear H
        | H:_ = right _ |- _ => clear H
        end.

    Ltac destr' := try destr_cond_match; simpl in *; try intuition congruence.

    Ltac destr :=
      destr';
      repeat
        match goal with
        | H:_ = left _ |- _ => clear H
        | H:_ = right _ |- _ => clear H
        end.

    Ltac destr_in H :=
      match type of H with
      | context [match ?f with
                 | _ => _
                 end] => des f
      end;
      repeat
        match goal with
        | H:_ = left _ |- _ => clear H
        | H:_ = right _ |- _ => clear H
        end.

Ltac inv H := inversion H; clear H; try subst.
Ltac ami := repeat match goal with
                     H: bind _ _ = OK _ |- _ => monadInv H
                   | H : OK _ = OK _ |- _ => inv H
                   | H : context [if ?a then _ else _ ] |- _ => destr_in H
                   | |- _ => destr
                   end.




Lemma tgdefs_fn_id:
  forall l g' x0 tf,
    SimplExpr.transl_globdefs l g' = OK x0 ->
    In (Gfun (Clight.Internal tf)) (map snd x0) ->
    In (Clight.fn_id tf) (filter_map (fun x : globdef Csyntax.fundef Ctypes.type =>
                                        match x with
                                        | Gfun (Csyntax.Internal f) => Some (Csyntax.fn_id f)
                                        | Gfun (Csyntax.External _ _ _ _) => None
                                        | Gvar _ => None
                                        end) (map snd l)).
Proof.
  induction l; simpl; intros; eauto.
  inv H; destr.
  ami.
  repeat destr_in Heqo. inv Heqo.
  des a. repeat destr_in H; ami.
  des H0. inv e. inv Heqg. simpl in *.
  unfold SimplExpr.bind in Heqr. repeat destr_in Heqr.  inv Heqr.
  unfold SimplExpr.transl_function, SimplExpr.bind in Heqr0.
  repeat destr_in Heqr0. destr_in Heqr1. inv Heqr0; inv Heqr1. simpl. auto. 
  exploit IHl. eauto. eauto. auto.
  des a. des g. des f. ami. des H0. eapply IHl; eauto.
  ami. des H0. eapply IHl; eauto.
Qed.

Lemma se_function_ptr_translated_rev''
  : forall (prog : Csyntax.program) (tprog : Clight.program),
    cond_ge_c prog ->
    SimplExpr.transl_program prog = OK tprog ->
    forall (b : Values.block) tf b' tf',
      Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv tprog) b =
      Some (Clight.Internal tf) ->
      Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv tprog) b' =
      Some (Clight.Internal tf') ->
      Clight.fn_id tf = Clight.fn_id tf' ->
      tf = tf'.
Proof.
  intros prog tprog CGE TP b tf b' tf' FFP FFP' EQid.
  generalize (find_funct_ptr_impl_in_snd_prog_defs _ _ _ FFP).
  generalize (find_funct_ptr_impl_in_snd_prog_defs _ _ _ FFP').
  destruct CGE as [A B].
  revert TP B EQid. clear.

  unfold SimplExpr.transl_program in *; simpl; intros.
  ami.
  revert B x EQ tf tf' EQid H H0.
  generalize (prog_defs prog) (SimplExpr.initial_generator tt).
  induction l; simpl; intros; eauto.
  - inv EQ; destr.
  - des a. des g0; eauto.
    + destr_in EQ. ami.
      specialize (IHl g'). trim IHl. repeat destr_in B; inv B; auto.
      specialize (IHl _ EQ0 _ _ EQid).

      destruct H.
      * inv H. destruct H0. inv H. auto.
        des f. unfold SimplExpr.bind in Heqr. repeat destr_in Heqr. inv Heqr.
        unfold SimplExpr.transl_function, SimplExpr.bind in Heqr0.
        repeat destr_in Heqr0. destr_in Heqr1. inv Heqr0; inv Heqr1. simpl in *.
        clear IHl.
        rewrite <- EQid in B. inv B.
        exfalso; apply H2. eapply tgdefs_fn_id ; eauto.
        inv Heqr.
      * destruct H0; auto. inv H0.
        des f. unfold SimplExpr.bind in Heqr. repeat destr_in Heqr. inv Heqr.
        unfold SimplExpr.transl_function, SimplExpr.bind in Heqr0.
        repeat destr_in Heqr0. destr_in Heqr1. inv Heqr0; inv Heqr1. simpl in *.
        clear IHl.
        rewrite EQid in B. inv B.
        exfalso; apply H2. eapply tgdefs_fn_id ; eauto.
        inv Heqr.
    + ami. des H.  des H0. eapply IHl; eauto.
Qed.            


Lemma se_transf_globdefs_doesnt_invent_names:
  forall l l' g,
    SimplExpr.transl_globdefs l g = OK l' ->
    forall i, 
    In i (map fst l') ->
    In i (map fst l).
Proof.
  induction l; simpl; intros.
  - inv H; auto.
  - des a; des g0; try destr_in H; monadInv H.
    des H0. right; eapply IHl; eauto.
    destr. des H0. right; eapply IHl; eauto.
Qed.


Lemma setp_lnr_pdn:
  forall  p p',
    list_norepet (prog_defs_names p) ->
    SimplExpr.transl_program p = OK p' ->
    list_norepet (prog_defs_names p').
Proof.
  intros.
  unfold SimplExpr.transl_program, prog_defs_names in *; simpl in *.
  monadInv H0. simpl.
  revert x EQ.  
  generalize (SimplExpr.initial_generator tt).
  revert H.
  generalize (prog_defs p).
  clear.
  induction l; simpl; intros.
  - inv EQ; constructor.
  - des a. inv H. trim IHl; auto.
    des g0.
    + destr_in EQ. monadInv EQ.
      simpl. constructor.
      intro IN. eapply se_transf_globdefs_doesnt_invent_names in IN; eauto.
      eapply IHl; eauto.
    + monadInv EQ.
      simpl. constructor.
      intro IN. eapply se_transf_globdefs_doesnt_invent_names in IN; eauto.
      eapply IHl; eauto.
Qed.


Lemma cond_ge_c_clight:
  forall p p',
    SimplExpr.transl_program p = OK p' ->
    cond_ge_c p ->
    cond_ge_clight p'.
Proof.
  red. intros p p' SE CGE f1 f2 i1 i2 EQid.
  assert (f1 = f2).
  {
    rewrite in_map_iff in i1, i2.
    destruct i1 as [x [EQ IN]].
    destruct i2 as [y [EQ' IN']]. des x; des y. subst.
    generalize (Globalenvs.Genv.find_funct_ptr_exists _ _ _ (setp_lnr_pdn _ _ (proj1 CGE) SE) IN).
    generalize (Globalenvs.Genv.find_funct_ptr_exists _ _ _ (setp_lnr_pdn _ _ (proj1 CGE) SE) IN').
    intros [b2 [FS2 FFP2]] [b1 [FS1 FFP1]].
    generalize (se_function_ptr_translated_rev'' _ _ CGE SE _ _ _ _ FFP1 FFP2). destr.
  }
  subst; auto.
Qed.


  Ltac t H :=
    match type of H with
    | ?f _ = _ => unfold f in H; unfold bind in H; destr_in H; inv H
    | ?f _ _ = _ => unfold f in H; unfold bind in H; destr_in H; inv H
    | ?f _ _ _ = _ => unfold f in H; unfold bind in H; destr_in H; inv H
    | ?f _ _ _ _ = _ => unfold f in H; unfold bind in H; destr_in H; inv H
    end.






Definition eq_f {A B: Type} (f: A -> B) (a b: A) : Prop :=
  f a = f b.



Ltac nice_inv' H :=
  match type of H with
    OK _ = OK _ => inv H
  | Error _ = OK _ => inv H
  | _ :: _ = _ => inv H
  | _ => idtac
  end.
  
Ltac dinv' H :=
  unfold bind2, bind in H;
  repeat destr_in H; nice_inv' H.

Ltac autodinv' :=
  repeat match goal with
         | H: context [bind _ _] |-  _ => dinv' H
         | H: context [bind2 _ _] |-  _ => dinv' H
         | H: context [match _ with _ => _ end] |-  _ => dinv' H
         | H: _ = OK _ |- _ => dinv' H
         end.

    

Lemma transf_globdefs_doesnt_invent_names:
  forall A B V W (ff: A -> res B) (fv: V -> res W) l l',
    transf_globdefs ff fv l = OK l' ->
    forall i, 
    In i (map fst l') ->
    In i (map fst l).
Proof.
  induction l; simpl; intros.
  - inv H; auto.
  - des a; des g; destr_in H; monadInv H.
    destr. des H0. right; eapply IHl; eauto.
    destr. des H0. right; eapply IHl; eauto.
Qed.

Lemma transform_partial_program2_lnr_pdn:
  forall A B V W (ff: A -> res B) (fv: V -> res W) (p: program A V) p',
    list_norepet (prog_defs_names p) ->
    transform_partial_program2 ff fv p = OK p' ->
    list_norepet (prog_defs_names p').
Proof.
  intros.
  unfold transform_partial_program2, prog_defs_names in *; simpl in *.
  monadInv H0. simpl.
  revert H x EQ.
  generalize (prog_defs p).
  clear.
  induction l; simpl; intros.
  - inv EQ; constructor.
  - des a. inv H. trim IHl; auto.
    des g.
    + destr_in EQ. monadInv EQ.
      simpl. constructor.
      intro IN. eapply transf_globdefs_doesnt_invent_names in IN; eauto.
      apply IHl; auto.
    + destr_in EQ. monadInv EQ.
      simpl. constructor.
      intro IN. eapply transf_globdefs_doesnt_invent_names in IN; eauto.
      apply IHl; auto.
Qed.

Lemma transform_partial_program_lnr_pdn:
  forall A B V (f: A -> res B) (p: program A V) p',
    list_norepet (prog_defs_names p) ->
    transform_partial_program f p = OK p' ->
    list_norepet (prog_defs_names p').
Proof.
  intros.
  unfold transform_partial_program in H0.
  eapply transform_partial_program2_lnr_pdn; eauto.
Qed.
Lemma transform_program_lnr_pdn:
  forall A B V (f: A -> B) (p: program A V),
    list_norepet (prog_defs_names p) ->
    list_norepet (prog_defs_names (transform_program f p)).
Proof.
  intros.
  unfold transform_program, prog_defs_names in *; simpl in *.
  rewrite map_map. simpl.
  eapply list_map_norepet.
  eapply Maps.PTree_Properties.list_norepet_map. eauto.
  intros. unfold transform_program_globdef. destruct x, y.
  intro EQ.
  assert (i = i0) by (des g; des g0). subst.
  exploit (@Alloc.norepet_eq ident). eauto. eexact H1. eexact H0.
  intro; subst. congruence.
Qed.


Require Import Globalenvs.

Lemma find_funct_add_globvars:
  forall {F V} l (ge: Genv.t (fundef F) V) id x b (f: fundef F),
    Genv.find_funct_ptr (Genv.add_globals (Genv.add_global ge (id, Gvar x)) l) b = Some f ->
    exists b',
      Genv.find_funct_ptr (Genv.add_globals ge l) b' = Some f.
Proof.
  unfold Genv.find_funct_ptr, Genv.add_globals, Genv.add_global. simpl.
  intros F V l ge id x b f.
  rewrite <- ! fold_left_rev_right.
  set (add_glob := fun y x0 => Genv.add_global (F:=fundef F) (V:=V) x0 y).
  change           (fun (y : ident * globdef (fundef F) V) (x0 : Genv.t (fundef F) V) =>
                      {|
                        Genv.genv_symb := Maps.PTree.set (fst y) (Genv.genv_next x0) (Genv.genv_symb x0);
                        Genv.genv_funs := match snd y as x1 return (x1 = snd y -> Maps.PTree.t (fundef F)) with
                                          | Gfun f0 =>
                                            fun _ : Gfun f0 = snd y =>
                                              Maps.PTree.set (Genv.genv_next x0) f0 (Genv.genv_funs x0)
                                          | Gvar v => fun _ : Gvar v = snd y => Genv.genv_funs x0
                                          end eq_refl;
                        Genv.genv_vars := match snd y as x1 return (x1 = snd y -> Maps.PTree.t (globvar V)) with
                                          | Gfun f0 => fun _ : Gfun f0 = snd y => Genv.genv_vars x0
                                          | Gvar v =>
                                            fun _ : Gvar v = snd y =>
                                              Maps.PTree.set (Genv.genv_next x0) v (Genv.genv_vars x0)
                                          end eq_refl;
                        Genv.genv_next := Pos.succ (Genv.genv_next x0);
                        Genv.genv_symb_range := Genv.add_global_obligation_1 x0 y;
                        Genv.genv_funs_range := Genv.add_global_obligation_2 x0 y;
                        Genv.genv_vars_range := Genv.add_global_obligation_3 x0 y;
                        Genv.genv_funs_vars := Genv.add_global_obligation_4 x0 y;
                        Genv.genv_vars_inj := Genv.add_global_obligation_5 x0 y |}) with add_glob.  
  revert ge id x b f. generalize (rev l).
  clear.
  induction l; simpl; intros; eauto.
  (* - rewrite Maps.PTree.gsspec in H; destr_in H. *)
  (*   eauto. *)
  - des a. des g.
    2: apply IHl in H; auto.
    rewrite Maps.PTree.gsspec in *.
    destr_in H.
    + inv H. eexists; apply Maps.PTree.gss.
    + apply IHl in H. dex. exists b'. rewrite Maps.PTree.gso. auto.
      apply Genv.genv_funs_range in H. intro; subst. xomega.
Qed.

Lemma find_funct_add_globs:
  forall {F V} l (ge: Genv.t (fundef F) V) id (x: external_function) b (f: F),
    Genv.find_funct_ptr (Genv.add_globals (Genv.add_global ge (id, Gfun (External x))) l) b = Some (Internal f) ->
    exists b',
      Genv.find_funct_ptr (Genv.add_globals ge l) b' = Some (Internal f).
Proof.
  unfold Genv.find_funct_ptr, Genv.add_globals, Genv.add_global. simpl.
  intros F V l ge id x b f.
  rewrite <- ! fold_left_rev_right.
  set (add_glob := fun y x0 => Genv.add_global (F:=fundef F) (V:=V) x0 y).
  change           (fun (y : ident * globdef (fundef F) V) (x0 : Genv.t (fundef F) V) =>
                      {|
                        Genv.genv_symb := Maps.PTree.set (fst y) (Genv.genv_next x0) (Genv.genv_symb x0);
                        Genv.genv_funs := match snd y as x1 return (x1 = snd y -> Maps.PTree.t (fundef F)) with
                                          | Gfun f0 =>
                                            fun _ : Gfun f0 = snd y =>
                                              Maps.PTree.set (Genv.genv_next x0) f0 (Genv.genv_funs x0)
                                          | Gvar v => fun _ : Gvar v = snd y => Genv.genv_funs x0
                                          end eq_refl;
                        Genv.genv_vars := match snd y as x1 return (x1 = snd y -> Maps.PTree.t (globvar V)) with
                                          | Gfun f0 => fun _ : Gfun f0 = snd y => Genv.genv_vars x0
                                          | Gvar v =>
                                            fun _ : Gvar v = snd y =>
                                              Maps.PTree.set (Genv.genv_next x0) v (Genv.genv_vars x0)
                                          end eq_refl;
                        Genv.genv_next := Pos.succ (Genv.genv_next x0);
                        Genv.genv_symb_range := Genv.add_global_obligation_1 x0 y;
                        Genv.genv_funs_range := Genv.add_global_obligation_2 x0 y;
                        Genv.genv_vars_range := Genv.add_global_obligation_3 x0 y;
                        Genv.genv_funs_vars := Genv.add_global_obligation_4 x0 y;
                        Genv.genv_vars_inj := Genv.add_global_obligation_5 x0 y |}) with add_glob.  
  revert ge id x b f. generalize (rev l).
  clear.
  induction l; simpl; intros; eauto.
  - rewrite Maps.PTree.gsspec in H; destr_in H.
    eauto.
  - des a. des g.
    2: apply IHl in H; auto.
    rewrite Maps.PTree.gsspec in *.
    destr_in H.
    + inv H. eexists; apply Maps.PTree.gss.
    + apply IHl in H. dex. exists b'. rewrite Maps.PTree.gso. auto.
      apply Genv.genv_funs_range in H. intro; subst. xomega.
Qed.

Definition front_end (p: Csyntax.program) : res Cminor.program :=
  OK p
     @@@ time "Clight generation" SimplExpr.transl_program
     @@@ time "Simplification of locals" SimplLocals.transf_program
     @@@ time "C#minor generation" Cshmgen.transl_program
     @@@ time "Cminor generation" Cminorgen.transl_program.

Lemma front_end_lnr:
 forall p tp
         (TC: front_end p = OK tp)
         (CGE: cond_ge_c p),
    list_norepet (prog_defs_names tp).
Proof.
 intros p tp TC CGE. 
  unfold front_end, time, print in TC; simpl in TC.
  Opaque SimplExpr.transl_program. 
  repeat match goal with
         | TC : ?a @@@ _ = OK _ |- _ => des a
         | TC: ?a @@ _ = OK _ |- _ => des a
         | TC: ?f _ = OK _ |- _ => unfold f, time, print, bind in TC; simpl in TC
         | TC: ?f _ = OK _ |- _ => unfold f, time, print, bind in TC; simpl in TC
         end.
 repeat
    match goal with
      |- list_norepet (prog_defs_names ?tp) =>
      match goal with
        H: transform_partial_program _ _ = OK tp |- _ =>
        eapply transform_partial_program_lnr_pdn; [idtac | exact H]; clear H
      | H: transform_partial_program2 _ _ _ = OK tp |- _ =>
        eapply transform_partial_program2_lnr_pdn; [idtac | exact H]; clear H
      end
    | |- list_norepet (prog_defs_names (transform_program _ _)) =>
      apply transform_program_lnr_pdn
    end.
 red in CGE. des CGE.
  eapply setp_lnr_pdn in l; eauto.
Qed. 

Lemma cond_ge_c_front_end:
  forall p tp,
    front_end p = OK tp ->
    cond_ge_c p ->
    list_norepet (prog_defs_names tp) /\
    forall b1 f1 b2 f2,
      Genv.find_funct_ptr (Genv.globalenv tp) b1 = Some (Internal f1) ->
      Genv.find_funct_ptr (Genv.globalenv tp) b2 = Some (Internal f2) ->
      Cminor.fn_id f1 = Cminor.fn_id f2 -> f1 = f2.
Proof.
  intros p tp FE CGE.
  exploit front_end_lnr; eauto. intro lnr; split; auto.
  repeat match goal with
         | TC : ?a @@@ _ = OK _ |- _ => destruct a eqn:?; simpl in *; try intuition congruence
         | TC: ?a @@ _ = OK _ |- _ => destruct a eqn:?; simpl in *; try intuition congruence
         | TC: ?f _ = OK _ |- _ => unfold f, time, print, bind in TC; simpl in TC
         | TC: ?f _ = OK _ |- _ => unfold f, time, print, bind in TC; simpl in TC
         end.
  intros b1 f1 b2 f2 FFP1 FFP2 EQid.
 Ltac clean FFP1 FFP2 :=
    let ff1 := fresh "f1" in
    let ff2 := fresh "f2" in
    let TF1 := fresh "TF1" in
    let TF2 := fresh "TF2" in
    destruct FFP1 as [ff1 [FFP1 TF1]];
      destruct FFP2 as [ff2 [FFP2 TF2]].

 repeat match type of FFP1 with
        | context [ transform_program _ _ ] =>
          eapply (Globalenvs.Genv.find_funct_ptr_rev_transf) in FFP1;
            eapply (Globalenvs.Genv.find_funct_ptr_rev_transf) in FFP2;
            clean FFP1 FFP2
        | context [Globalenvs.Genv.globalenv ?p] =>
          match goal with
          | TC: transform_partial_program _ _ = OK p |- _ =>
            eapply (Globalenvs.Genv.find_funct_ptr_rev_transf_partial
                      _ _ TC) in FFP1;
              eapply (Globalenvs.Genv.find_funct_ptr_rev_transf_partial
                        _ _ TC) in FFP2;
              clean FFP1 FFP2; clear TC
          | TC: transform_partial_program2 _ _ _ = OK p |- _ =>
            eapply (Globalenvs.Genv.find_funct_ptr_rev_transf_partial2
                      _ _ _ TC) in FFP1;
              eapply (Globalenvs.Genv.find_funct_ptr_rev_transf_partial2
                        _ _ _ TC) in FFP2;
              clean FFP1 FFP2; clear TC
          end
        end.
  Ltac eq_id PASS ID PID :=
    match goal with
    | H: PASS ?f = OK ?f',
         H': PASS ?f1 = OK ?f1',
             H2: PID ?f' = PID ?f1' |- _ =>
      let X := fresh "EQID" in
      assert (X : ID f = ID f1); [
        clear - H H' H2;
        unfold PASS in H, H'; des f; des f1; ami
       |]
    | H: PASS _ ?f = OK ?f',
         H': PASS _ ?f1 = OK ?f1',
             H2: PID ?f' = PID ?f1' |- _ =>
      let X := fresh "EQID" in
      assert (X : ID f = ID f1); [
        clear - H H' H2;
        unfold PASS in H, H'; des f; des f1; ami
       |]
   | H: PASS _ _ ?f = OK ?f',
         H': PASS _ _ ?f1 = OK ?f1',
             H2: PID ?f' = PID ?f1' |- _ =>
      let X := fresh "EQID" in
      assert (X : ID f = ID f1); [
        clear - H H' H2;
        unfold PASS in H, H'; des f; des f1; ami
       |]
 | 
 H2: PID (PASS ?f) = PID (PASS ?f1) |- _ =>
      let X := fresh "EQID" in
      assert (X : ID f = ID f1); [
        clear - H2;
        unfold PASS in H2; des f; des f1; ami
       |] | 
 H2: PID (PASS _ ?f) = PID (PASS _ ?f1) |- _ =>
      let X := fresh "EQID" in
      assert (X : ID f = ID f1); [
        clear - H2;
        unfold PASS in H2; des f; des f1; ami
       |]
    end.
  Ltac get_deepest_subterm_fundef a t :=
    match a with
    | _ ?x => get_deepest_subterm_fundef x t
    | _ _ ?x => get_deepest_subterm_fundef x t
    | _ _ _ ?x => get_deepest_subterm_fundef x t
    | ?x : fundef _ => t x
    end.

  Ltac tac_do x :=
    let H := fresh in
    set (H := x).

  repeat match goal with
           H: ?a = OK (Internal _) |- _ =>
           get_deepest_subterm_fundef a des; (* ami; *)
             revert H; try solve [destr]
         end.
  intros.
  ami.
  
  eq_id Cminorgen.transl_function Csharpminor.fn_id Cminor.fn_id.
  unfold Cminorgen.transl_funbody in *; simpl in *. ami.
  eq_id Cshmgen.transl_function Clight.fn_id Csharpminor.fn_id.
  des f6; des f7. ami.
  eq_id SimplLocals.transf_function Clight.fn_id Clight.fn_id. inv EQ3. inv EQ4. inv EQ4.
  generalize FFP1 FFP2; intros FFP1' FFP2'.
  generalize (fun cge => se_function_ptr_translated_rev'' _ _ cge Heqr1 _ _ _ _ FFP1 FFP2 EQID1).
  intro A; trim A.  auto. subst.
  repeat match goal with
           H: ?a = _, H1: ?a = _ |- _ =>
           rewrite H in H1; inv H1; clear H
         end.
  auto.
Qed.

Lemma back_end_lnr:
 forall p tp
         (TC: transf_cminor_program p = OK tp)
         (CGE: list_norepet (prog_defs_names p)),
    list_norepet (prog_defs_names tp).
Proof.
 intros p tp TC LNR. 
  unfold transf_cminor_program, transf_rtl_program, time, print in TC; simpl in TC.
  repeat match goal with
         | TC : ?a @@@ _ = OK _ |- _ => des a
         | TC: ?a @@ _ = OK _ |- _ => des a
         | TC: ?f _ = OK _ |- _ => unfold f, time, print, bind in TC; simpl in TC
         | TC: ?f _ = OK _ |- _ => unfold f, time, print, bind in TC; simpl in TC
         end.
  destr_in Heqr1. ami.
  unfold CleanupLabels.transf_program, Tunneling.tunnel_program, Renumber.transf_program,
  Constprop.transf_program in *.
  repeat
    match goal with
      |- list_norepet (prog_defs_names ?tp) =>
      match goal with
        H: transform_partial_program _ _ = OK tp |- _ =>
        eapply transform_partial_program_lnr_pdn; [idtac | exact H]; clear H
      | H: transform_partial_program2 _ _ _ = OK tp |- _ =>
        eapply transform_partial_program2_lnr_pdn; [idtac | exact H]; clear H
      end
    | |- list_norepet (prog_defs_names (transform_program _ _)) =>
      apply transform_program_lnr_pdn
    end. auto.
Qed. 

Lemma cond_ge_cminor_asm:
  forall p tp
         (TC: transf_cminor_program p = OK tp)
         (LNR: list_norepet (prog_defs_names p))
         (EQ: forall b1 f1 b2 f2,
             Genv.find_funct_ptr (Genv.globalenv p) b1 = Some (Internal f1) ->
             Genv.find_funct_ptr (Genv.globalenv p) b2 = Some (Internal f2) ->
             Cminor.fn_id f1 = Cminor.fn_id f2 ->
             f1 = f2),
    cond_globalenv tp.
Proof.
  intros.
  exploit back_end_lnr; eauto. intro lnr. red; split; auto.
  repeat match goal with
         | TC : ?a @@@ _ = OK _ |- _ => destruct a eqn:?; simpl in *; try intuition congruence
         | TC: ?a @@ _ = OK _ |- _ => destruct a eqn:?; simpl in *; try intuition congruence
         | TC: ?f _ = OK _ |- _ => unfold f, time, print, bind in TC; simpl in TC
         | TC: ?f _ = OK _ |- _ => unfold f, time, print, bind in TC; simpl in TC
         end.
  repeat match goal with
           H: OK _ = OK _  |- _ => inv H
         end.
  intros b1 f1 b2 f2 FFP1 FFP2 EQid.
   
  unfold CleanupLabels.transf_program, Tunneling.tunnel_program,
  Renumber.transf_program, Constprop.transf_program in *.
  destr_in Heqr0.
  repeat match type of FFP1 with
         | context [ transform_program _ _ ] =>
           eapply (Globalenvs.Genv.find_funct_ptr_rev_transf) in FFP1;
             eapply (Globalenvs.Genv.find_funct_ptr_rev_transf) in FFP2;
             clean FFP1 FFP2
         | context [Globalenvs.Genv.globalenv ?p] =>
           match goal with
           | TC: transform_partial_program _ _ = OK p |- _ =>
             eapply (Globalenvs.Genv.find_funct_ptr_rev_transf_partial
                       _ _ TC) in FFP1;
               eapply (Globalenvs.Genv.find_funct_ptr_rev_transf_partial
                         _ _ TC) in FFP2;
               clean FFP1 FFP2; clear TC
           | TC: transform_partial_program2 _ _ _ = OK p |- _ =>
             eapply (Globalenvs.Genv.find_funct_ptr_rev_transf_partial2
                       _ _ _ TC) in FFP1;
               eapply (Globalenvs.Genv.find_funct_ptr_rev_transf_partial2
                         _ _ _ TC) in FFP2;
               clean FFP1 FFP2; clear TC
           end
         end.
  repeat match goal with
           H: ?a = OK (Internal _) |- _ =>
           get_deepest_subterm_fundef a des; (* ami; *)
             revert H
         end.
  intros.
  ami.
  eq_id Asmgen.transf_function Mach.fn_id Asm.fn_id.
  unfold Asmgen.transl_function in *; ami.
  eq_id Stacking.transf_function Linear.fn_id Mach.fn_id.
  subst f f13; simpl in *; auto.
  eq_id CleanupLabels.transf_function Linear.fn_id Linear.fn_id.
  eq_id Linearize.transf_function LTL.fn_id Linear.fn_id.
  subst f3 f0. simpl in *. auto.
  eq_id Tunneling.tunnel_function LTL.fn_id LTL.fn_id.
  eq_id Allocation.transf_function RTL.fn_id LTL.fn_id.
  repeat destr_in EQ11. ami. repeat destr_in EQ3. ami.
  unfold Allocation.check_function in *.
  repeat destr_in EQ. repeat destr_in EQ0.
  eq_id Deadcode.transf_function RTL.fn_id RTL.fn_id.
  destr_in EQ12. destr_in EQ4. ami.
  eq_id CSE.transf_function RTL.fn_id RTL.fn_id.
  destr_in EQ13. destr_in EQ5. ami.
  eq_id Renumber.transf_function RTL.fn_id RTL.fn_id.
  des f14. des f8.
  unfold Constprop.transf_function in *; simpl in *.
  inv Heqf. auto.
  eq_id Constprop.transf_function RTL.fn_id RTL.fn_id.
  eq_id Renumber.transf_function RTL.fn_id RTL.fn_id.
  eq_id RTLgen.transl_function CminorSel.fn_id RTL.fn_id.
  repeat destr_in EQ14; repeat destr_in EQ6. ami.
  simpl in *; auto.
  eq_id Selection.sel_function Cminor.fn_id CminorSel.fn_id.
  specialize (EQ _ _ _ _ FFP1 FFP2). trim EQ. auto. subst.
  repeat match goal with
           H: ?a = _,
              H1: ?a = _ |- _ =>
           rewrite H in H1; inv H1; clear H
         end.
  auto.
Qed.

Definition inj_internal_id  (ge : Cminor.genv)  := 
  forall b1 f1 b2 f2,
    Genv.find_funct_ptr ge b1 = Some (Internal f1) ->
    Genv.find_funct_ptr ge b2 = Some (Internal f2) ->
    Cminor.fn_id f1 = Cminor.fn_id f2 ->
    f1 = f2.


Definition cminor_preserves_fn_id (p tp : Cminor.program) : Prop :=
  forall
         (LNR: list_norepet (prog_defs_names p))
         (EQ: inj_internal_id  (Genv.globalenv p)),
    inj_internal_id  (Genv.globalenv tp).

  
Lemma transf_c_program_decomp:
  forall p,
    transf_c_program p =
    front_end p @@@ (transf_cminor_program).
Proof.
  unfold transf_c_program, front_end, transf_clight_program.
  simpl; intros.
  unfold time, print. 
  des (SimplExpr.transl_program p).
Qed.

Definition list_norepet_preserves (F : Cminor.program -> res Cminor.program) : Prop :=
  forall p p'
         (NOREP : list_norepet (prog_defs_names p))
         (APP  : F p = OK p'),
    list_norepet (prog_defs_names p').


Lemma list_norepet_apply_partial :
  forall (R : res Cminor.program) (tp : Cminor.program)
         (G: Cminor.program -> res Cminor.program)
         (APPG : list_norepet_preserves G)
         (ROK : forall p (ROK : R = OK p),  list_norepet (prog_defs_names p)) 
         (APP : R @@@ G = OK tp),
    list_norepet (prog_defs_names tp).
Proof.
  intros.
  destruct R ; simpl in APP.
  apply APPG in APP; auto.
  eapply ROK; auto.
Qed.
  
Lemma  list_norepet_time :
  forall str (F : Cminor.program -> res Cminor.program),
         list_norepet_preserves F -> 
         list_norepet_preserves (time str F).
Proof.
  intros.
  unfold time; auto.
Qed.

Hint Resolve list_norepet_time.


Lemma cminor_preserves_fn_id_trans :
  forall p q r
         (NOREP : list_norepet (prog_defs_names p) -> list_norepet (prog_defs_names q))
         (P_PQ : cminor_preserves_fn_id p q)
         (P_QR : cminor_preserves_fn_id q r),
    cminor_preserves_fn_id p r.
Proof.
  intros.
  unfold cminor_preserves_fn_id in * ; auto.
Qed.

Lemma cminor_preserves_fn_id_apply_partial :
  forall (p tp: Cminor.program) 
         (R: res Cminor.program)
         (G: Cminor.program -> res Cminor.program)
         (APP : R @@@ G = OK tp)
         (APPG : forall q r, G q = OK r ->     cminor_preserves_fn_id q r)
  ,
    exists p, R = OK p /\  G p = OK tp /\ cminor_preserves_fn_id p tp.
Proof.
  intros.
  subst.
  des R.
  exists p0 ; split ; auto.
Qed.

Lemma cond_ge_c_asm:
  forall p tp
         (TC: transf_c_program p = OK tp)
         (CGE: cond_ge_c p),
    cond_globalenv tp.
Proof.
  intros.
  rewrite transf_c_program_decomp in TC.
  des (front_end p).
  exploit (cond_ge_c_front_end); eauto. intros [lnr_fe GE_ge].

  eapply cond_ge_cminor_asm. eauto. eauto. eauto.
Qed.

Theorem transf_cstrategy_program_correct:
  forall p tp
    p' (SE: SimplExpr.transl_program p = OK p')
    (cond_ge: cond_ge_c p),
    transf_c_program p = OK tp ->
  forall p'',
      SimplLocals.transf_program p' = OK p'' ->
      let sg := oracle_sg tp in
      let ns := oracle_ns tp in
      let sl := nssl p'' in
      let ns := fun i =>  (ns i - sl i)%nat in
  forward_simulation (Cstrategy.semantics p ns sg) (Asm.semantics tp sg)
  * backward_simulation (atomic (Cstrategy.semantics p ns sg)) (Asm.semantics tp sg).
Proof.
  intros.
  assert (F: forward_simulation (Cstrategy.semantics p ns0 sg) (Asm.semantics tp sg)).
  revert H; unfold transf_c_program, time; simpl.
  rewrite SE; simpl. 
  intro EQ0.
  eapply compose_forward_simulation. apply SimplExprproof.transl_program_correct. eauto.
  destruct (SimplLocals.transf_program p') eqn:?; try congruence.
  
  generalize (fun cond_ge cond_ge' => fst (transf_clight_program_correct _ _ cond_ge cond_ge' EQ0 _ Heqr)).
  unfold ns, sg.
  intro A; inv H0. apply A.
  eapply cond_ge_c_asm; eauto.
  unfold transf_c_program, time. simpl. rewrite SE; simpl; auto.
  eapply cond_ge_c_clight; eauto.
  
  split. auto. 
  apply forward_to_backward_simulation.
  apply factor_forward_simulation. auto. eapply sd_traces. eapply Asm.semantics_determinate.
  apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
  apply Asm.semantics_determinate.
Qed.

Definition oracles p tp (TC: transf_c_program p = OK tp) :
  (ident -> Z) * (ident -> nat) * (ident -> nat).
Proof.
  unfold transf_c_program in TC.
  simpl in TC.
  unfold time in TC.
  destruct (SimplExpr.transl_program p) eqn:?; simpl in TC; try congruence.
  unfold transf_clight_program in TC.
  simpl in TC.
  unfold time, print in TC.
  destruct (SimplLocals.transf_program p0) eqn:?; simpl in TC; try congruence.
  split.
  split.
  exact (oracle_sg tp).
  exact (fun i => oracle_ns tp i - nssl p1 i)%nat.
  exact (nssl p1).
Defined.

Definition do_oracles (p: Csyntax.program) : option ((ident -> Z) * (ident -> nat) * (ident -> nat)).
Proof.
  destruct (transf_c_program p) eqn:?.
  exact (Some (oracles _ _ Heqr)).
  exact None.
Defined.

Theorem transf_c_program_correct:
  forall p tp
    (cond_ge: cond_ge_c p) 
    (TC: transf_c_program p = OK tp),
    let (sgns,sl) := oracles p tp TC in
    let (sg,ns) := sgns in
  backward_simulation (Csem.semantics p ns sg) (Asm.semantics tp sg).
Proof.
  intros.
  destruct (oracles p tp TC) as [[sg ns] sl] eqn:?.
  apply compose_backward_simulation with (atomic (Cstrategy.semantics p ns sg)).
  eapply sd_traces; eapply Asm.semantics_determinate.
  apply factor_backward_simulation. 
  apply Cstrategy.strategy_simulation.
  apply Csem.semantics_single_events.
  eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.

  generalize TC; intro TC'.
  unfold transf_c_program in TC.
  unfold oracles in Heqp0.
  simpl in *.
  unfold time in TC.
  destruct (SimplExpr.transl_program p) eqn:?; simpl in TC; try congruence.
  unfold transf_clight_program in TC.
  simpl in TC.
  unfold time, print in TC.
  destruct (SimplLocals.transf_program p0) eqn:?; simpl in TC; try congruence.
  inv Heqp0.
  apply(snd (transf_cstrategy_program_correct p tp _ Heqr cond_ge TC' _ Heqr0)); auto.
Qed.
