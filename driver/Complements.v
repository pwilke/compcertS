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

(** Corollaries of the main semantic preservation theorem. *)

Require Import Classical.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Behaviors.
Require Import Csyntax.
Require Import Csem.
Require Import Cstrategy.
Require Import Clight.
Require Import Cminor.
Require Import RTL.
Require Import Asm.
Require Import Compiler.
Require Import Errors.

(** * Preservation of whole-program behaviors *)

(** From the simulation diagrams proved in file [Compiler]. it follows that
  whole-program observable behaviors are preserved in the following sense.
  First, every behavior of the generated assembly code is matched by
  a behavior of the source C code. *)

Theorem transf_c_program_preservation:
  forall p tp (cond_ge: cond_ge_c p) beh
    (TC: transf_c_program p = OK tp),
    let (sgns,sl) := oracles _ _ TC in
    let (sg,ns) := sgns in
    program_behaves (Asm.semantics tp sg) beh ->
    exists beh', program_behaves (Csem.semantics p ns sg) beh' /\ behavior_improves beh' beh.
Proof.
  intros.
  destr. destr.
  eapply backward_simulation_behavior_improves; eauto. 
  generalize (transf_c_program_correct _ _ cond_ge TC).
  rewrite Heqp0. auto.
Qed.

(** As a corollary, if the source C code cannot go wrong, the behavior of the
  generated assembly code is one of the possible behaviors of the source C code. *)

Theorem transf_c_program_is_refinement:
  forall p tp (cond_ge: cond_ge_c p)    (TC: transf_c_program p = OK tp),
    let (sgns,sl) := oracles _ _ TC in
    let (sg,ns) := sgns in
    (forall beh, program_behaves (Csem.semantics p ns sg) beh -> not_wrong beh) ->
    (forall beh, program_behaves (Asm.semantics tp sg) beh -> program_behaves (Csem.semantics p ns sg) beh).
Proof.
  intros.
  destr; destr. eapply backward_simulation_same_safe_behavior; eauto.
  generalize (transf_c_program_correct _ _ cond_ge TC).
  rewrite Heqp0. auto.
Qed.

(** If we consider the C evaluation strategy implemented by the compiler,
  we get stronger preservation results. *)

Theorem transf_cstrategy_program_preservation:
  forall p tp (cond_ge: cond_ge_c p)
    (TC: transf_c_program p = OK tp)
    sg ns sl
    (EQ: ((sg,ns),sl) = oracles _ _ TC),
    (forall beh, program_behaves (Cstrategy.semantics p ns sg) beh ->
            exists beh', program_behaves (Asm.semantics tp sg) beh' /\ behavior_improves beh beh')
    /\(forall beh, program_behaves (Asm.semantics tp sg) beh ->
             exists beh', program_behaves (Cstrategy.semantics p ns sg) beh' /\ behavior_improves beh' beh)
    /\(forall beh, not_wrong beh ->
             program_behaves (Cstrategy.semantics p ns sg) beh -> program_behaves (Asm.semantics tp sg) beh)
    /\(forall beh,
         (forall beh', program_behaves (Cstrategy.semantics p ns sg) beh' -> not_wrong beh') ->
         program_behaves (Asm.semantics tp sg) beh ->
         program_behaves (Cstrategy.semantics p ns sg) beh).
Proof.
  intros.
  
  generalize TC; intro TC'.
  unfold transf_c_program in TC.
  unfold oracles in EQ.
  simpl in *.
  unfold time in TC.
  destruct (SimplExpr.transl_program p) eqn:?; simpl in TC; try congruence.
  unfold transf_clight_program in TC.
  simpl in TC.
  unfold time, print in TC.
  destruct (SimplLocals.transf_program p0) eqn:?; simpl in TC; try congruence.
  assert (WBT: well_behaved_traces (Cstrategy.semantics p ns sg)).
  { intros. eapply ssr_well_behaved. apply Cstrategy.semantics_strongly_receptive. }
  inv EQ.
  intros. intuition.
  - eapply forward_simulation_behavior_improves; eauto.
    apply (fst (transf_cstrategy_program_correct p tp _ Heqr cond_ge TC' _ Heqr0)).
  -
    exploit backward_simulation_behavior_improves.
    + eapply (snd (transf_cstrategy_program_correct p tp _ Heqr cond_ge TC' _ Heqr0)).
    + eauto.
    + intros [beh1 [A B]]. exists beh1; split; auto.
      rewrite atomic_behaviors; auto.
  - eapply forward_simulation_same_safe_behavior; eauto.
    apply (fst (transf_cstrategy_program_correct p tp _ Heqr cond_ge TC' _ Heqr0)).
  - exploit backward_simulation_same_safe_behavior.
    + eapply (snd (transf_cstrategy_program_correct p tp _ Heqr cond_ge TC' _ Heqr0)).
    + intros. rewrite <- atomic_behaviors in H1; eauto.
    + eauto.
    + intros. rewrite atomic_behaviors; auto. 
Qed.

(** We can also use the alternate big-step semantics for [Cstrategy]
  to establish behaviors of the generated assembly code. *)

Theorem bigstep_cstrategy_preservation:
  forall p tp (cond_ge: cond_ge_c p)    (TC: transf_c_program p = OK tp)

    sg ns sl
    (EQ: ((sg,ns),sl) = oracles _ _ TC),
    (forall t r,
        Cstrategy.bigstep_program_terminates p ns sg t r ->
        program_behaves (Asm.semantics tp sg) (Terminates t r))
    /\(forall T,
         Cstrategy.bigstep_program_diverges p ns sg T ->
         program_behaves (Asm.semantics tp sg) (Reacts T)
         \/ exists t, program_behaves (Asm.semantics tp sg) (Diverges t) /\ traceinf_prefix t T).
Proof.
  intros.
  
  split; intros.
  -
    eapply transf_cstrategy_program_preservation; eauto. red; auto.
    eapply behavior_bigstep_terminates with (Cstrategy.bigstep_semantics p ns sg); auto.
    apply Cstrategy.bigstep_semantics_sound.
  - generalize (behavior_bigstep_diverges (Cstrategy.bigstep_semantics_sound p ns sg) T). 
    intros [A | [t [A B]]].  eassumption.
    + left. eapply transf_cstrategy_program_preservation; eauto. red; auto.
    + right; exists t; split; auto. eapply transf_cstrategy_program_preservation; eauto. red; auto.
Qed.

(** * Satisfaction of specifications *)

(** The second additional results shows that if all executions
  of the source C program satisfies a given specification
  (a predicate on the observable behavior of the program),
  then all executions of the produced Asm program satisfy
  this specification as well.  

  We first show this result for specifications that are stable
  under the [behavior_improves] relation. *) 

Section SPECS_PRESERVED.

Variable spec: program_behavior -> Prop.

Hypothesis spec_stable:
  forall beh1 beh2, behavior_improves beh1 beh2 -> spec beh1 -> spec beh2.

Theorem transf_c_program_preserves_spec:
  forall p tp (cond_ge: cond_ge_c p)
       (TC: transf_c_program p = OK tp)

    sg ns sl
    (EQ: ((sg,ns),sl) = oracles _ _ TC),
    (forall beh, program_behaves (Csem.semantics p ns sg) beh -> spec beh) ->
    (forall beh, program_behaves (Asm.semantics tp sg) beh -> spec beh).
Proof.
  intros.
  generalize (transf_c_program_preservation p tp cond_ge beh TC); eauto. erewrite <- EQ.
  intros [beh' [A B]]. auto.
  apply spec_stable with beh'; auto. 
Qed.

End SPECS_PRESERVED.

(** As a corollary, we obtain preservation of safety specifications:
  specifications that exclude "going wrong" behaviors. *)

Section SAFETY_PRESERVED.

Variable spec: program_behavior -> Prop.

Hypothesis spec_safety:
  forall beh, spec beh -> not_wrong beh.

Theorem transf_c_program_preserves_safety_spec:
  forall p tp (cond_ge: cond_ge_c p)  (TC: transf_c_program p = OK tp)
    sg ns sl
    (EQ: ((sg,ns),sl) = oracles _ _ TC),
    (forall beh, program_behaves (Csem.semantics p ns sg) beh -> spec beh) ->
    (forall beh, program_behaves (Asm.semantics tp sg) beh -> spec beh).
Proof.
  intros. eapply transf_c_program_preserves_spec; eauto. 
  intros. destruct H1. congruence. destruct H1 as [t [EQ1 EQ2]]. 
  subst beh1. elim (spec_safety _ H2). 
Qed.

End SAFETY_PRESERVED.

(** We also have preservation of liveness specifications:
  specifications that assert the existence of a prefix of the observable
  trace satisfying some conditions. *)

Section LIVENESS_PRESERVED.

Variable spec: trace -> Prop.

Definition liveness_spec_satisfied (b: program_behavior) : Prop :=
  exists t, behavior_prefix t b /\ spec t.

Theorem transf_c_program_preserves_liveness_spec:
  forall p tp (cond_ge: cond_ge_c p)  (TC: transf_c_program p = OK tp)

    sg ns sl
    (EQ: ((sg,ns),sl) = oracles _ _ TC),
    (forall beh, program_behaves (Csem.semantics p ns sg) beh -> liveness_spec_satisfied beh) ->
    (forall beh, program_behaves (Asm.semantics tp sg) beh -> liveness_spec_satisfied beh).
Proof.
  intros. eapply transf_c_program_preserves_spec; eauto.
  intros. destruct H2 as [t1 [A B]]. destruct H1.
  subst. exists t1; auto.
  destruct H1 as [t [C D]]. subst.
  destruct A as [b1 E]. destruct D as [b2 F].
  destruct b1; simpl in E; inv E.
  exists t1; split; auto. 
  exists (behavior_app t0 b2); apply behavior_app_assoc. 
Qed.

End LIVENESS_PRESERVED.

