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

(** Recognition of combined operations, addressing modes and conditions 
  during the [CSE] phase. *)

Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import ExprEval.
Require Import Memory.
Require Import Op.
Require Import RTL.
Require Import CSEdomain.
Require Import CombineOp.

Require Import Values_symbolictype.
Require Import Values_symbolic.

Section COMBINE.

Variable ge: genv.
Variable sp: expr_sym.
Variable m: mem.
Variable get: valnum -> option rhs.
Variable valu: valnum -> expr_sym.
Hypothesis get_sound: forall v rhs, get v = Some rhs -> rhs_eval_to valu ge sp m rhs (valu v).

Lemma get_op_sound:
  forall v op vl, get v = Some (Op op vl) -> eval_operation ge sp op (map valu vl) = Some (valu v).
Proof.
  intros. exploit get_sound; eauto. intros REV; inv REV; auto. 
Qed.

Ltac UseGetSound :=
  match goal with
  | [ H: get _ = Some _ |- _ ] =>
      let x := fresh "EQ" in (generalize (get_op_sound _ _ _ H); intros x; simpl in x; FuncInv)
  end.
  
Lemma combine_compimm_ne_0_sound:
  forall x cond args,
  combine_compimm_ne_0 get x = Some(cond, args) ->
  exists v, eval_condition cond (map valu args) = Some v /\
       same_eval v (Val.cmp_bool Cne (valu x) (Eval (Vint Int.zero))) /\
       same_eval v (Val.cmpu_bool Cne (valu x) (Eval (Vint Int.zero))).
Proof.
  intros until args. functional induction (combine_compimm_ne_0 get x); intros EQ; inv EQ.
  - (* of cmp *)
    UseGetSound. rewrite EQ.  eexists; split; auto.
    split; red; intros; rewrite <- (eval_condition_boolval _ _ EQ); simpl; seval.
  - (* of and *)
    UseGetSound. rewrite <- H.
    simpl.
    eexists; split; auto.
    split; red; intros; simpl; seval; destr. 
Qed.

Lemma combine_compimm_eq_0_sound:
  forall x cond args,
  combine_compimm_eq_0 get x = Some(cond, args) ->
  exists v, eval_condition cond (map valu args) = Some v /\
       same_eval v (Val.cmp_bool Ceq (valu x) (Eval (Vint Int.zero))) /\ 
       same_eval v (Val.cmpu_bool Ceq (valu x) (Eval (Vint Int.zero))).
Proof.
  intros until args. functional induction (combine_compimm_eq_0 get x); intros EQ; inv EQ.
  - (* of cmp *)
    UseGetSound.
    generalize (eval_negate_condition c (map valu args)).
    rewrite EQ. simpl. destr.
    eexists; split; eauto.
    split; red; simpl; intros; rewrite H; seval; auto.
  - (* of and *)
    UseGetSound. simpl. eexists; split; eauto.
    rewrite <- H.
    split; red; simpl; intros; seval.
Qed.

Lemma combine_compimm_eq_1_sound:
  forall x cond args,
  combine_compimm_eq_1 get x = Some(cond, args) ->
  exists v, eval_condition cond (map valu args) = Some v /\
       same_eval v (Val.cmp_bool Ceq (valu x) (Eval (Vint Int.one))) /\
       same_eval v (Val.cmpu_bool Ceq (valu x) (Eval (Vint Int.one))).
Proof.
  intros until args. functional induction (combine_compimm_eq_1 get x); intros EQ; inv EQ.
  (* of cmp *)
  UseGetSound. rewrite EQ.
  eexists; split; eauto.
  split; red; intros; rewrite <- (eval_condition_boolval _ _ EQ); simpl; seval;
  exploit (eval_condition_zero_one); eauto; intros [A|A]; subst;
  try rewrite Int.eq_true; try (rewrite Int.eq_false by discriminate); simpl; auto.
Qed.

Lemma combine_compimm_ne_1_sound:
  forall x cond args,
  combine_compimm_ne_1 get x = Some(cond, args) ->
  exists v, 
    eval_condition cond (map valu args) = Some v /\
    same_eval v (Val.cmp_bool Cne (valu x) (Eval (Vint Int.one))) /\
    same_eval v (Val.cmpu_bool Cne (valu x) (Eval (Vint Int.one))).
Proof.
  intros until args. functional induction (combine_compimm_ne_1 get x); intros EQ; inv EQ.
  (* of cmp *)
  UseGetSound. 
  generalize (eval_negate_condition c (map valu args)).
  rewrite EQ; simpl. destr.
  eexists; split; auto.
  split; red; simpl; intros; rewrite H; simpl; seval;
  exploit (eval_condition_zero_one c); eauto; intros [A|A]; subst;
  try rewrite Int.eq_true; try (rewrite Int.eq_false by discriminate); simpl; auto.
Qed.

Theorem combine_cond_sound:
  forall cond args cond' args',
    combine_cond get cond args = Some(cond', args') ->
    forall v,
      eval_condition cond (map valu args) = Some v ->
      exists v', eval_condition cond' (map valu args') = Some v' /\ same_eval v' v.
Proof.
  intros.
  Ltac UseFact fact :=
    exploit fact; eauto; simpl in *;
    match goal with
      H: Some _ = Some _ |- _ => inv H
    end; intros [v [A [B C]]]; eexists; split; eauto.

  Ltac UseFacts fact1 fact2 fact3 fact4 :=
    first [ now (UseFact combine_compimm_eq_0_sound) |
            now (UseFact combine_compimm_eq_1_sound) |
            now (UseFact combine_compimm_ne_0_sound) |
            now (UseFact combine_compimm_ne_1_sound)].
  functional inversion H; subst;
  UseFacts combine_compimm_ne_0_sound combine_compimm_eq_0_sound combine_compimm_eq_1_sound combine_compimm_ne_1_sound.
Qed.

Theorem combine_addr_sound:
  forall addr args addr' args',
    combine_addr get addr args = Some(addr', args') ->
    forall v,
      eval_addressing  ge sp addr (map valu args) = Some v ->
      exists v',
        eval_addressing ge sp addr' (map valu args') = Some v' /\
        same_eval v' v.
Proof.
  intros. functional inversion H; subst.
  (* indexed - lea *)
  UseGetSound. simpl. exploit eval_offset_addressing_total; eauto.
  intros [e [A B]].
  rewrite A. eexists; split; eauto.
  simpl in H0; inv H0. auto.
Qed.

Theorem combine_op_sound:
  forall op args op' args',
    combine_op get op args = Some(op', args') ->
    forall v, eval_operation ge sp op (map valu args) = Some v->
         exists v', eval_operation ge sp op' (map valu args') = Some v' /\
               same_eval v' v.
Proof.
  intros. functional inversion H; subst.
  - (* lea-lea *)
    simpl. eapply combine_addr_sound; eauto. 
  - (* andimm - andimm *)
    UseGetSound; simpl. eexists; split; eauto. simpl in H0; inv H0.
    rewrite <- H1. clear. red; intros; simpl; seval. rewrite Int.and_assoc; auto.
  - (* orimm - orimm *)
    UseGetSound; simpl. simpl in H0; inv H0. rewrite <- H1. eexists; split; auto.
    clear; red; intros; simpl; seval. rewrite Int.or_assoc. auto.
  - (* xorimm - xorimm *)
    UseGetSound; simpl. simpl in H0; inv H0. rewrite <- H1. eexists; split; auto.
    clear; red; intros; simpl; seval. rewrite Int.xor_assoc. auto.
  - (* cmp *)
    simpl. eapply combine_cond_sound; eauto.
Qed.

End COMBINE.
