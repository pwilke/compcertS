Require Import Coqlib.
Require Import Psatz.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Values_symbolictype.
Require Import ExprEval.
Require Import NormaliseSpec.
Require Import IntFacts.

(** This module defines useful properties of the [normalise] function.  *)

(** We axiomatise the [normalise] function, it will be implemented later in
    [Values_symbolic_aux.ml]. *)

Axiom normalise : norm_typ.
Axiom norm_correct : normalise_correct normalise.
Axiom norm_complete : normalise_complete normalise.

Require Import Setoid.

Section NormSpec.

Lemma norm_eq'':
  forall e e' bound align
    (SE: same_eval_on (compat Int.max_unsigned bound align) e e'),
    normalise bound align e = normalise bound align e'.
Proof.
  exact (normalise_eq normalise  norm_correct norm_complete).
Qed.

Lemma norm_gr:
  forall bound align e,
    good_result Int.max_unsigned bound align e (normalise bound align e).
Proof.
  intros.
  apply is_norm_dep.
  apply norm_correct. 
Qed.

Definition dummy_em : block -> int -> byte := fun _ _ => Byte.zero.

Section NormaliseFacts.

Variable sz : block -> Z*Z.
Variable msk : block -> int.
(* Variable alloc : block -> int. *)
(* Variable alloc_compat : compat31 sz msk alloc. *)

Hypothesis exists_two_cms:
  forall b1 : block,
    exists cm cm' : block -> int,
      compat Int.max_unsigned sz msk cm /\
      compat Int.max_unsigned sz msk cm' /\
      cm b1 <> cm' b1 /\
      forall b', b1 <> b' -> cm b' = cm' b'.

Lemma depends_ptr:
  forall bnd msk b i,
    depends Int.max_unsigned bnd msk (Eval (Vptr b i)) b.
Proof.
  clear; intros.
  red; intros; simpl.
  intro EQ.
  apply inj_vint in EQ.
  rewrite ! (Int.add_commut _ i) in EQ.
  apply int_add_eq_l in EQ; congruence.
Qed.

Lemma exists_cm:
  exists alloc, compat Int.max_unsigned sz msk alloc.
Proof.
  destruct (exists_two_cms xH) as [cm [_ [Hcm _]]]; eauto.
Qed.

Lemma normalise_val:
  forall v,
    normalise sz msk (Eval v) = v.
Proof.
  intros.
  generalize (norm_correct sz msk (Eval v)); intro A.
  assert (IsNorm.t sz msk (Eval v) v).
  {
    inversion A; constructor; simpl; intros; auto.
    red; intros; auto.
  }
  generalize (norm_complete sz msk (Eval v) v H).
  intro B. des v; inv B; auto.
  inv A.
  destruct exists_cm as [cm Hcm].
  specialize (eval_ok _ dummy_em  Hcm ); inv eval_ok;
  des (normalise sz msk (Eval Vundef)).
Qed.

Lemma lessdef_vint:
  forall i j,
    Values.Val.lessdef (Vint i) (Vint j) ->
    i = j.
Proof.
  intros i j A; inv A; auto.
Qed.

End NormaliseFacts.

Definition styp_of_typ (t:typ) : styp :=
  styp_of_ast t.

Definition typ_of_styp (t:styp) : typ :=
  match t with
      Tint => AST.Tint
    | Tlong => AST.Tlong
    | Tfloat => AST.Tfloat
    | Tsingle => AST.Tsingle
  end.

Lemma compat_same_bounds:
  forall ms a b c d e, 
    (forall f, b f = c f) ->
    (forall f, d f = e f) ->
    compat ms b d a->
    compat ms c e a.
Proof.
  intros.
  destruct H1.
  constructor; intros; eauto.
  apply addr_space; rewrite H; auto.
  apply overlap; auto; rewrite H; auto.
  rewrite <- H0; apply alignment. 
Qed.

End NormSpec.
