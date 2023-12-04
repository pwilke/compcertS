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

(** Abstract domain for neededness analysis *)

Require Import Coqlib.
Require Import Maps.
Require Import IntvSets.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Values_symbolictype Values_symbolic ExprEval Normalise NormaliseSpec Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Lattice.
Require Import Registers.
Require Import ValueDomain.
Require Import Op.
Require Import RTL.
Require Import Psatz.
Require Import Tactics.

(** * Neededness for values *)

Inductive nval : Type :=
  | Nothing              (**r value is entirely unused *)
  | I (m: int)           (**r only need the bits that are 1 in [m] *)
  | All.                 (**r every bit of the value is used *)

Definition eq_nval (x y: nval) : {x=y} + {x<>y}.
Proof.
  decide equality.
Defined.

(** ** Agreement between two values relative to a need. *)

Definition iagree (p q mask: int) : Prop :=
  forall i, 0 <= i < Int.zwordsize -> Int.testbit mask i = true ->
            Int.testbit p i = Int.testbit q i.

Fixpoint vagree (v w: expr_sym) (x: nval) {struct x}: Prop :=
  match x with
  | Nothing => True
  | I m =>
    Val.lessdef (Val.and v (Eval (Vint m)))
                (Val.and w (Eval (Vint m)))
  | All => Val.lessdef v w
  end.

Lemma vagree_same: forall v x, vagree v v x.
Proof.
  intros. des x; auto.
Qed.

Lemma vagree_lessdef: forall v w x, Val.lessdef v w -> vagree v w x.
Proof.
  intros. des x.
  red; intros.
  specialize (H alloc em); simpl in *. inv H. auto. simpl. auto.
Qed.

Lemma lessdef_vagree: forall v w, vagree v w All -> Val.lessdef v w.
Proof.
  intros. simpl in H. auto.
Qed.

Hint Resolve vagree_same vagree_lessdef lessdef_vagree: na.

Inductive vagree_list: list expr_sym -> list expr_sym -> list nval -> Prop :=
  | vagree_list_nil: forall nvl,
      vagree_list nil nil nvl
  | vagree_list_default: forall v1 vl1 v2 vl2,
      vagree v1 v2 All -> vagree_list vl1 vl2 nil ->
      vagree_list (v1 :: vl1) (v2 :: vl2) nil
  | vagree_list_cons: forall v1 vl1 v2 vl2 nv1 nvl,
      vagree v1 v2 nv1 -> vagree_list vl1 vl2 nvl ->
      vagree_list (v1 :: vl1) (v2 :: vl2) (nv1 :: nvl).

Lemma lessdef_vagree_list:
  forall vl1 vl2, vagree_list vl1 vl2 nil -> Val.lessdef_list vl1 vl2.
Proof.
  induction vl1; intros; inv H; constructor; auto with na.
Qed.

Lemma vagree_lessdef_list:
  forall vl1 vl2, Val.lessdef_list vl1 vl2 -> forall nvl, vagree_list vl1 vl2 nvl.
Proof.
  induction 1; intros.
  constructor.
  destruct nvl; constructor; auto with na.
Qed.

Hint Resolve lessdef_vagree_list vagree_lessdef_list: na.

(** ** Ordering and least upper bound between value needs *)

Inductive nge: nval -> nval -> Prop :=
  | nge_nothing: forall x, nge All x
  | nge_all: forall x, nge x Nothing
  | nge_int: forall m1 m2,
      (forall i, 0 <= i < Int.zwordsize -> Int.testbit m2 i = true -> Int.testbit m1 i = true) ->
      nge (I m1) (I m2).

Lemma nge_refl: forall x, nge x x.
Proof.
  destruct x; constructor; auto.
Qed.

Hint Constructors nge: na.
Hint Resolve nge_refl: na.

Lemma nge_trans: forall x y, nge x y -> forall z, nge y z -> nge x z.
Proof.
  induction 1; intros w VG; inv VG; eauto with na.
Qed.

Lemma nge_agree:
  forall v w x y, nge x y -> vagree v w x -> vagree v w y.
Proof.
  induction 1; simpl; auto.
- destruct v; auto with na.
- red; intros. specialize (H0 alloc em); simpl in *.
  seval; auto; try solve [inv H0].
  apply lessdef_vint in H0.
  apply Values.Val.lessdef_same. f_equal.
  apply Int.same_bits_eq.
  intros.
  rewrite ! Int.bits_and; auto.
  des (Int.testbit m2 i1).
  apply H in Heqb; auto.
  apply (f_equal (fun x => Int.testbit x i1)) in H0.
  rewrite ! Int.bits_and in H0; auto.
  rewrite Heqb in H0. auto.
  ring.
Qed.

Definition nlub (x y: nval) : nval :=
  match x, y with
  | Nothing, _ => y
  | _, Nothing => x
  | I m1, I m2 => I (Int.or m1 m2)
  | _, _ => All
  end.

Lemma nge_lub_l:
  forall x y, nge (nlub x y) x.
Proof.
  unfold nlub; destruct x, y; auto with na.
  constructor. intros. autorewrite with ints; auto. rewrite H0; auto. 
Qed.

Lemma nge_lub_r:
  forall x y, nge (nlub x y) y.
Proof.
  unfold nlub; destruct x, y; auto with na.
  constructor. intros. autorewrite with ints; auto. rewrite H0. apply orb_true_r; auto.
Qed.

(** ** Properties of agreement between integers *)

Lemma iagree_refl:
  forall p m, iagree p p m.
Proof.
  intros; red; auto.
Qed.

Remark eq_same_bits:
  forall i x y, x = y -> Int.testbit x i = Int.testbit y i.
Proof.
  intros; congruence.
Qed.

Lemma iagree_and_eq:
  forall x y mask,
  iagree x y mask <-> Int.and x mask = Int.and y mask.
Proof.
  intros; split; intros. 
- Int.bit_solve. specialize (H i H0). 
  destruct (Int.testbit mask i). 
  rewrite ! andb_true_r; auto. 
  rewrite ! andb_false_r; auto.
- red; intros. exploit (eq_same_bits i); eauto; autorewrite with ints; auto.
  rewrite H1. rewrite ! andb_true_r; auto. 
Qed.

Lemma iagree_mone:
  forall p q, iagree p q Int.mone -> p = q.
Proof.
  intros. rewrite iagree_and_eq in H. rewrite ! Int.and_mone in H. auto.
Qed.

Lemma iagree_zero:
  forall p q, iagree p q Int.zero.
Proof.
  intros. rewrite iagree_and_eq. rewrite ! Int.and_zero; auto.
Qed.

Lemma iagree_and:
  forall x y n m,
  iagree x y (Int.and m n) -> iagree (Int.and x n) (Int.and y n) m.
Proof.
  intros. rewrite iagree_and_eq in *. rewrite ! Int.and_assoc.
  rewrite (Int.and_commut n). auto.
Qed.

Lemma iagree_not:
  forall x y m, iagree x y m -> iagree (Int.not x) (Int.not y) m.
Proof.
  intros; red; intros; autorewrite with ints; auto. f_equal; auto. 
Qed.

Lemma iagree_not':
  forall x y m, iagree (Int.not x) (Int.not y) m -> iagree x y m.
Proof.
  intros. rewrite <- (Int.not_involutive x). rewrite <- (Int.not_involutive y).
  apply iagree_not; auto.
Qed.

Lemma iagree_or:
  forall x y n m,
  iagree x y (Int.and m (Int.not n)) -> iagree (Int.or x n) (Int.or y n) m.
Proof.
  intros. apply iagree_not'. rewrite ! Int.not_or_and_not. apply iagree_and. 
  apply iagree_not; auto.
Qed.

Lemma iagree_bitwise_binop:
  forall sem f,
  (forall x y i, 0 <= i < Int.zwordsize ->
       Int.testbit (f x y) i = sem (Int.testbit x i) (Int.testbit y i)) ->
  forall x1 x2 y1 y2 m,
  iagree x1 y1 m -> iagree x2 y2 m -> iagree (f x1 x2) (f y1 y2) m.
Proof.
  intros; red; intros. rewrite ! H by auto. f_equal; auto. 
Qed.

Lemma iagree_shl:
  forall x y m n,
  iagree x y (Int.shru m n) -> iagree (Int.shl x n) (Int.shl y n) m.
Proof.
  intros; red; intros. autorewrite with ints; auto. 
  destruct (zlt i (Int.unsigned n)).
- auto.
- generalize (Int.unsigned_range n); intros. 
  apply H. omega. rewrite Int.bits_shru by omega. 
  replace (i - Int.unsigned n + Int.unsigned n) with i by omega. 
  rewrite zlt_true by omega. auto.
Qed.

Lemma iagree_shru:
  forall x y m n,
  iagree x y (Int.shl m n) -> iagree (Int.shru x n) (Int.shru y n) m.
Proof.
  intros; red; intros. autorewrite with ints; auto. 
  destruct (zlt (i + Int.unsigned n) Int.zwordsize).
- generalize (Int.unsigned_range n); intros. 
  apply H. omega. rewrite Int.bits_shl by omega. 
  replace (i + Int.unsigned n - Int.unsigned n) with i by omega. 
  rewrite zlt_false by omega. auto.
- auto.
Qed.

Lemma iagree_shr_1:
  forall x y m n,
  Int.shru (Int.shl m n) n = m ->
  iagree x y (Int.shl m n) -> iagree (Int.shr x n) (Int.shr y n) m.
Proof.
  intros; red; intros. rewrite <- H in H2. rewrite Int.bits_shru in H2 by auto. 
  rewrite ! Int.bits_shr by auto. 
  destruct (zlt (i + Int.unsigned n) Int.zwordsize).
- apply H0; auto. generalize (Int.unsigned_range n); omega.
- discriminate.
Qed.

Lemma iagree_shr:
  forall x y m n,
  iagree x y (Int.or (Int.shl m n) (Int.repr Int.min_signed)) ->
  iagree (Int.shr x n) (Int.shr y n) m.
Proof.
  intros; red; intros. rewrite ! Int.bits_shr by auto. 
  generalize (Int.unsigned_range n); intros. 
  set (j := if zlt (i + Int.unsigned n) Int.zwordsize
            then i + Int.unsigned n
            else Int.zwordsize - 1).
  assert (0 <= j < Int.zwordsize).
  { unfold j; destruct (zlt (i + Int.unsigned n) Int.zwordsize); omega. }
  apply H; auto. autorewrite with ints; auto. apply orb_true_intro. 
  unfold j; destruct (zlt (i + Int.unsigned n) Int.zwordsize).
- left. rewrite zlt_false by omega. 
  replace (i + Int.unsigned n - Int.unsigned n) with i by omega. 
  auto.
- right. reflexivity.
Qed.

Lemma iagree_rol:
  forall p q m amount,
  iagree p q (Int.ror m amount) ->
  iagree (Int.rol p amount) (Int.rol q amount) m.
Proof.
  intros. assert (Int.zwordsize > 0) by (compute; auto).
  red; intros. rewrite ! Int.bits_rol by auto. apply H.
  apply Z_mod_lt; auto.
  rewrite Int.bits_ror.
  replace (((i - Int.unsigned amount) mod Int.zwordsize + Int.unsigned amount)
   mod Int.zwordsize) with i. auto.
  apply Int.eqmod_small_eq with Int.zwordsize; auto.
  apply Int.eqmod_trans with ((i - Int.unsigned amount) + Int.unsigned amount).
  apply Int.eqmod_refl2; omega. 
  eapply Int.eqmod_trans. 2: apply Int.eqmod_mod; auto.
  apply Int.eqmod_add. 
  apply Int.eqmod_mod; auto. 
  apply Int.eqmod_refl. 
  apply Z_mod_lt; auto. 
  apply Z_mod_lt; auto.
Qed. 

Lemma iagree_ror:
  forall p q m amount,
  iagree p q (Int.rol m amount) ->
  iagree (Int.ror p amount) (Int.ror q amount) m.
Proof.
  intros. rewrite ! Int.ror_rol_neg by apply int_wordsize_divides_modulus.
  apply iagree_rol. 
  rewrite Int.ror_rol_neg by apply int_wordsize_divides_modulus.
  rewrite Int.neg_involutive; auto. 
Qed.

Lemma eqmod_iagree:
  forall m x y,
  Int.eqmod (two_p (Int.size m)) x y ->
  iagree (Int.repr x) (Int.repr y) m.
Proof.
  intros. set (p := nat_of_Z (Int.size m)). 
  generalize (Int.size_range m); intros RANGE.
  assert (EQ: Int.size m = Z_of_nat p). { symmetry; apply nat_of_Z_eq. omega. }
  rewrite EQ in H; rewrite <- two_power_nat_two_p in H.
  red; intros. rewrite ! Int.testbit_repr by auto.
  destruct (zlt i (Int.size m)). 
  eapply Int.same_bits_eqmod; eauto. omega.
  assert (Int.testbit m i = false) by (eapply Int.bits_size_2; omega). 
  congruence.
Qed.

Definition complete_mask (m: int) := Int.zero_ext (Int.size m) Int.mone.

Lemma iagree_eqmod:
  forall x y m,
  iagree x y (complete_mask m) ->
  Int.eqmod (two_p (Int.size m)) (Int.unsigned x) (Int.unsigned y).
Proof.
  intros. set (p := nat_of_Z (Int.size m)). 
  generalize (Int.size_range m); intros RANGE.
  assert (EQ: Int.size m = Z_of_nat p). { symmetry; apply nat_of_Z_eq. omega. }
  rewrite EQ; rewrite <- two_power_nat_two_p. 
  apply Int.eqmod_same_bits. intros. apply H. omega. 
  unfold complete_mask. rewrite Int.bits_zero_ext by omega. 
  rewrite zlt_true by omega. rewrite Int.bits_mone by omega. auto.
Qed.

Lemma complete_mask_idem:
  forall m, complete_mask (complete_mask m) = complete_mask m.
Proof.
  unfold complete_mask; intros. destruct (Int.eq_dec m Int.zero).
+ subst m; reflexivity.
+ assert (Int.unsigned m <> 0).
  { red; intros; elim n. rewrite <- (Int.repr_unsigned m). rewrite H; auto. }
  assert (0 < Int.size m). 
  { apply Int.Zsize_pos'. generalize (Int.unsigned_range m); omega. }
  generalize (Int.size_range m); intros.
  f_equal. apply Int.bits_size_4. tauto. 
  rewrite Int.bits_zero_ext by omega. rewrite zlt_true by omega.
  apply Int.bits_mone; omega.
  intros. rewrite Int.bits_zero_ext by omega. apply zlt_false; omega. 
Qed.

(** ** Abstract operations over value needs. *)

Ltac InvAgree :=
  simpl vagree in *;
  repeat (
  auto || exact Logic.I ||
  match goal with
  | [ H: False |- _ ] => contradiction
  | [ H: match ?v with Vundef => _ | Vint _ => _ | Vlong _ => _ | Vfloat _ => _ | Vsingle _ => _ | Vptr _ _ => _ end |- _ ] => destruct v
  end).

(** And immediate, or immediate *)

Definition andimm (x: nval) (n: int) :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.and m n)
  | All => I n
  end.

Lemma andimm_sound:
  forall v w x n,
  vagree v w (andimm x n) ->
  vagree (Val.and v (Eval (Vint n))) (Val.and w (Eval (Vint n))) x.
Proof.
  unfold andimm; intros; destruct x; simpl in *; unfold Val.and.
- auto.
- red; simpl; intros.
  specialize (H alloc em). simpl in H. seval; auto; try solve [inv H].
  apply lessdef_vint in H.
  apply Values.Val.lessdef_same. f_equal.
  rewrite ! Int.and_assoc.
  rewrite ! (Int.and_commut n). auto.
- red; simpl; intros.
  specialize (H alloc em); simpl in H; seval; auto; try solve [inv H].
Qed.

Definition orimm (x: nval) (n: int) :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.and m (Int.not n))
  | _ => I (Int.not n)
  end.


Lemma orimm_sound:
  forall v w x n,
  vagree v w (orimm x n) ->
  vagree (Val.or v (Eval (Vint n))) (Val.or w (Eval (Vint n))) x.
Proof.
  unfold orimm; intros; destruct x; simpl in *.
- auto.
- red; simpl; intros.
  specialize (H alloc em). simpl in H. seval; auto; try solve [inv H].
  apply lessdef_vint in H.
  apply Values.Val.lessdef_same. f_equal.
  assert (Int.and (Int.and i (Int.not n)) m = Int.and (Int.and i0 (Int.not n)) m).
  {
    rewrite ! Int.and_assoc. rewrite (Int.and_commut _ m); auto.
  } clear H.
  apply Int.same_bits_eq; auto.
  intros.
  apply (f_equal (fun x => Int.testbit x i1)) in H0.
  revert H0.
  rewrite ! Int.bits_and; auto.
  rewrite ! Int.bits_or; auto.
  rewrite ! Int.bits_not; auto.
  des (Int.testbit i i1); des (Int.testbit i0 i1); des (Int.testbit n i1);
    des (Int.testbit m i1).

- red; simpl; intros.
  specialize (H alloc em); simpl in H; seval; auto; try solve [inv H].
  apply lessdef_vint in H.
  apply Values.Val.lessdef_same.
  f_equal.  apply Int.same_bits_eq; auto.
  intros.
  apply (f_equal (fun x => Int.testbit x i1)) in H.
  revert H.
  rewrite ! Int.bits_and; auto.
  rewrite ! Int.bits_or; auto.
  rewrite ! Int.bits_not; auto.
  des (Int.testbit i i1); des (Int.testbit i0 i1); des (Int.testbit n i1).
Qed.

(** Bitwise operations: and, or, xor, not *)

Definition bitwise (x: nval) := x.

Remark bitwise_idem: forall nv, bitwise (bitwise nv) = bitwise nv.
Proof. auto. Qed.

(* Lemma vagree_bitwise_binop: *)
(*   forall f, *)
(*   (forall p1 p2 q1 q2 m, *)
(*      iagree p1 q1 m -> iagree p2 q2 m -> iagree (f p1 p2) (f q1 q2) m) -> *)
(*   forall v1 w1 v2 w2 x, *)
(*   vagree v1 w1 (bitwise x) -> vagree v2 w2 (bitwise x) -> *)
(*   vagree (match v1, v2 with Vint i1, Vint i2 => Vint(f i1 i2) | _, _ => Vundef end) *)
(*          (match w1, w2 with Vint i1, Vint i2 => Vint(f i1 i2) | _, _ => Vundef end) *)
(*          x. *)
(* Proof. *)
(*   unfold bitwise; intros. destruct x; simpl in *. *)
(* - auto.  *)
(* - InvAgree.  *)
(* - inv H0; auto. inv H1; auto. destruct w1; auto. *)
(* Qed. *)

Lemma and_sound:
  forall v1 w1 v2 w2 x,
  vagree v1 w1 (bitwise x) -> vagree v2 w2 (bitwise x) ->
  vagree (Val.and v1 v2) (Val.and w1 w2) x.
Proof.
  intros.
  des x.
  red; intros.
  specialize (H alloc em); specialize (H0 alloc em).
  simpl in *; seval; auto; try solve[inv H; inv H0].
  apply Values.Val.lessdef_same.
  apply lessdef_vint in H. apply lessdef_vint in H0.
  f_equal. apply Int.same_bits_eq.
  intros.
  apply (f_equal (fun x => Int.testbit x i3)) in H0.
  apply (f_equal (fun x => Int.testbit x i3)) in H.
  revert H H0; rewrite ! Int.bits_and; auto.
  des (Int.testbit i i3); des (Int.testbit m i3); des (Int.testbit i1 i3); des (Int.testbit i2 i3).
  eapply Val.lessdef_binop; eauto.
Qed.

Lemma or_sound:
  forall v1 w1 v2 w2 x,
  vagree v1 w1 (bitwise x) -> vagree v2 w2 (bitwise x) ->
  vagree (Val.or v1 v2) (Val.or w1 w2) x.
Proof.
  intros.
  des x.
  red; intros.
  specialize (H alloc em); specialize (H0 alloc em).
  simpl in *; seval; auto; try solve[inv H; inv H0].
  apply Values.Val.lessdef_same.
  apply lessdef_vint in H. apply lessdef_vint in H0.
  f_equal. apply Int.same_bits_eq.
  intros.
  apply (f_equal (fun x => Int.testbit x i3)) in H0.
  apply (f_equal (fun x => Int.testbit x i3)) in H.
  revert H H0; rewrite ! Int.bits_and, ! Int.bits_or; eauto.
  des (Int.testbit i i3); des (Int.testbit m i3); des (Int.testbit i1 i3); des (Int.testbit i2 i3).
  eapply Val.lessdef_binop; eauto.
Qed.


Lemma xor_sound:
  forall v1 w1 v2 w2 x,
  vagree v1 w1 (bitwise x) -> vagree v2 w2 (bitwise x) ->
  vagree (Val.xor v1 v2) (Val.xor w1 w2) x.
Proof.
  intros.
  des x.
  red; intros.
  specialize (H alloc em); specialize (H0 alloc em).
  simpl in *; seval; auto; try solve[inv H; inv H0].
  apply Values.Val.lessdef_same.
  apply lessdef_vint in H. apply lessdef_vint in H0.
  f_equal. apply Int.same_bits_eq.
  intros.
  apply (f_equal (fun x => Int.testbit x i3)) in H0.
  apply (f_equal (fun x => Int.testbit x i3)) in H.
  revert H H0; rewrite ! Int.bits_and, ! Int.bits_xor; auto.
  des (Int.testbit i i3); des (Int.testbit m i3); des (Int.testbit i1 i3); des (Int.testbit i2 i3);
    des (Int.testbit i0 i3).
  eapply Val.lessdef_binop; eauto.
Qed.

Lemma notint_sound:
  forall v w x,
  vagree v w (bitwise x) -> vagree (Val.notint v) (Val.notint w) x.
Proof.
  intros.
  des x.
  red; intros.
  specialize (H alloc em).
  simpl in *; seval; auto; try solve[inv H].
  apply Values.Val.lessdef_same.
  apply lessdef_vint in H.
  f_equal. apply Int.same_bits_eq.
  intros.
  apply (f_equal (fun x => Int.testbit x i1)) in H.
  revert H; rewrite ! Int.bits_and, ! Int.bits_not; auto.
  des (Int.testbit i i1); des (Int.testbit m i1); des (Int.testbit i0 i1).
  eapply Val.lessdef_unop; eauto.
Qed.

(** Shifts and rotates *)

Definition shlimm (x: nval) (n: int) :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.shru m n)
  | All => I (Int.shru Int.mone n)
  end.

Lemma shlimm_sound:
  forall v w x n,
  vagree v w (shlimm x n) ->
  vagree (Val.shl v (Eval (Vint n))) (Val.shl w (Eval (Vint n))) x.
Proof.
  unfold shlimm; intros. unfold Val.shl. 
  destruct (Int.ltu n Int.iwordsize). 
  destruct x; simpl in *.
- auto.
-
  Ltac ldt :=
    match goal with
      |- Val.lessdef ?a ?b =>
      let cm := fresh "cm" in
      let em := fresh "em" in
      red; intros cm em; simpl;
      repeat match goal with
               H: Val.lessdef _ _ |- _ => specialize (H cm em); simpl in H; inv H
             end;
      seval; auto
    end.
  ldt.
  destr; auto.
  Ltac sld :=
    match goal with
      |- Values.Val.lessdef (Vint ?i) (Vint ?j) =>
      apply Values.Val.lessdef_same; f_equal;
      apply Int.same_bits_eq;
      let ii := fresh "ii" in
      let HH := fresh "iirng" in
      intros ii HH;
      repeat match goal with
               H: Vint _ = Vint _ |- _ => apply inj_vint in H

             end
    | |- Values.Val.lessdef (Vlong ?i) (Vlong ?j) =>
      apply Values.Val.lessdef_same; f_equal;
      apply Int64.same_bits_eq;
      let ii := fresh "ii" in
      let HH := fresh "iirng" in
      intros ii HH;
      repeat match goal with
               H: Vint _ = Vint _ |- _ => apply inj_vint in H

             end
    end.
  Ltac eqint i H :=
    apply (f_equal (fun x => Int.testbit x i)) in H;
    revert H.
  sld. 
  Require Import Psatz.
  Ltac gotb :=
    match goal with
      |- context [Int.testbit (Int.or _ _) _] => rewrite Int.bits_or; try auto
    | |- context [Int.testbit (Int.and _ _) _] => rewrite Int.bits_and; try auto
    | |- context [Int.testbit (Int.shl _ _) _] => rewrite Int.bits_shl; try auto
    | |- context [Int.testbit (Int.shr _ _) _] => rewrite Int.bits_shr; try auto
    | |- context [Int.testbit (Int.shru _ _) _] => rewrite Int.bits_shru; try auto
    | |- context [Int.testbit (Int.ror _ _) _] => rewrite Int.bits_ror; try auto
    | |- context [Int.testbit (Int.rol _ _) _] => rewrite Int.bits_rol; try auto
    | |- context [Int.testbit (Int.mone) _] => rewrite Int.bits_mone; try auto
    end.
  repeat gotb.
  destr.
  eqint (ii - Int.unsigned n) H2.
  repeat gotb.
  Lemma sub_plus_eq:
    forall (a b: Z), a - b + b = a.
  Proof.
    intros. omega.
  Qed.
  rewrite ! sub_plus_eq.
  destr.
  generalize (Int.unsigned_range n); omega.
  generalize (Int.unsigned_range n); omega.
  generalize (Int.unsigned_range n); omega.
- ldt. destr; auto.
  sld. repeat gotb. destr.
  eqint (ii - Int.unsigned n) H2.
  repeat gotb; try (generalize (Int.unsigned_range n); omega).
  destr.
  rewrite ! andb_true_r; auto.
  rewrite sub_plus_eq in g0. lia.
- des x.
  ldt. destr; auto. sld. repeat gotb. destr.
  eqint (ii - Int.unsigned n) H2.
  repeat gotb; try (generalize (Int.unsigned_range n); omega).
  destr.
  rewrite ! sub_plus_eq. auto.
  rewrite sub_plus_eq in g0. lia.

  ldt. destr; auto. sld. repeat gotb. destr.
  eqint (ii - Int.unsigned n) H2.
  repeat gotb; try (generalize (Int.unsigned_range n); omega).
  rewrite ! sub_plus_eq.
  destr.
  rewrite ! andb_true_r; auto.
Qed.

Definition shruimm (x: nval) (n: int) :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.shl m n)
  | All => I (Int.shl Int.mone n)
  end.
Lemma plus_sub_eq:
  forall (a b: Z), a + b - b = a.
Proof. intros; omega. Qed.

Lemma shruimm_sound:
  forall v w x n,
  vagree v w (shruimm x n) ->
  vagree (Val.shru v (Eval (Vint n))) (Val.shru w (Eval (Vint n))) x.
Proof.
  unfold shruimm; intros. unfold Val.shru.
  des x.
  - ldt. destr; auto.
    sld. repeat gotb. destr.
    eqint (ii + Int.unsigned n) H2.
    repeat gotb; try (generalize (Int.unsigned_range n); omega).
    destr. lia. rewrite plus_sub_eq. auto.

  - ldt. destr; auto.
    sld. repeat gotb. destr.
    eqint (ii + Int.unsigned n) H2.
    repeat gotb; try (generalize (Int.unsigned_range n); omega).
    destr. lia.
    rewrite ! andb_true_r; auto.
Qed.

Definition shrimm (x: nval) (n: int) :=
  match x with
  | Nothing => Nothing
  | I m => I (let m' := Int.shl m n in
              if Int.eq_dec (Int.shru m' n) m
              then m'
              else Int.or m' (Int.repr Int.min_signed))
  | All => I (Int.or (Int.shl Int.mone n) (Int.repr Int.min_signed))
  end.

Lemma shrimm_sound:
  forall v w x n,
  vagree v w (shrimm x n) ->
  vagree (Val.shr v (Eval (Vint n))) (Val.shr w (Eval (Vint n))) x.
Proof.
  unfold shrimm; intros. unfold Val.shr.
  des x.
  - ldt. destr; auto.
    sld. repeat gotb. Opaque Z.sub. destr.
    + (* destr_in H2.  *)
      eqint (ii + Int.unsigned n) H2.
      destr; repeat gotb; try (generalize (Int.unsigned_range n); omega).
      destr. lia. rewrite plus_sub_eq. auto.
      destr. lia. rewrite plus_sub_eq.
      des (Int.testbit m ii). intros; ring.
    + eqint (Int.zwordsize - 1) H2.
      assert (0 <= Int.zwordsize - 1 < Int.zwordsize).
      {
        split. vm_compute. destr. vm_compute. auto.
      }
      destr; repeat gotb;  auto.
      *
        apply Int.ltu_iwordsize_inv in Heqb.
        destr. lia.
        eqint ii e.
        rewrite Int.bits_shru; auto.
        destr.
        intro A; rewrite <- A; intros; ring.
      * destr.
        replace (Int.testbit (Int.repr Int.min_signed) (Int.zwordsize - 1)) with true by reflexivity.
        rewrite ! andb_true_r. intro A; rewrite A; auto.
        replace (Int.testbit (Int.repr Int.min_signed) (Int.zwordsize - 1)) with true by reflexivity.
        rewrite orb_true_r.
        rewrite ! andb_true_r. intro A; rewrite A; auto.
  - ldt. destr; auto.
    sld. repeat gotb. destr.
    + eqint (ii + Int.unsigned n) H2.
      repeat gotb; try (generalize (Int.unsigned_range n); omega).
      destr. lia. 
      simpl. rewrite ! andb_true_r; auto.
      rewrite plus_sub_eq. lia.
    + eqint (Int.zwordsize - 1) H2.
      assert (0 <= Int.zwordsize - 1 < Int.zwordsize).
      {
        vm_compute. destr. 
      }
      repeat gotb.
      destr;
      replace (Int.testbit (Int.repr Int.min_signed) (Int.zwordsize - 1)) with true by reflexivity;
      try rewrite ! orb_true_r;
      rewrite ! andb_true_r; auto.
      split. apply Int.ltu_iwordsize_inv in Heqb. lia. lia.
Qed.

Definition rolm (x: nval) (amount mask: int) :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.ror (Int.and m mask) amount)
  | _ => I (Int.ror mask amount)
  end.

Lemma rolm_sound:
  forall v w x amount mask,
  vagree v w (rolm x amount mask) ->
  vagree (Val.rolm v amount mask) (Val.rolm w amount mask) x.
Proof.
  unfold rolm; intros; destruct x; simpl in *.
- auto.
- ldt. sld. unfold Int.rolm. repeat gotb.
  eqint ((ii - Int.unsigned amount) mod Int.zwordsize) H2.
  repeat gotb. 2: apply Z.mod_pos_bound; reflexivity.
  2: apply Z.mod_pos_bound; reflexivity.
  2: apply Z.mod_pos_bound; reflexivity.
  2: apply Z.mod_pos_bound; reflexivity.

  Lemma sub_plus_mod_eq:
    forall a b c, c > 0 ->
      ((a - b) mod c + b) mod c = a mod c.
  Proof.
    intros; rewrite <- Z.add_opp_r.
    rewrite (Z.add_mod a (-b)). 2: omega.
    rewrite Z.add_mod. 2: omega.
    rewrite ! Zplus_mod_idemp_l.
    transitivity ((a mod c) mod c). 
    rewrite <- Z.add_assoc.
    destruct (zeq 0 (b mod c)).
    rewrite Z_mod_zero_opp_full. rewrite <- e. f_equal. lia.  lia.
    rewrite Z_mod_nz_opp_full; auto.
    replace (c - b mod c + b mod c) with c by lia.
    rewrite Z.add_mod. rewrite Z_mod_same_full. f_equal.
    rewrite Zmod_mod. lia. lia.
    apply Zmod_mod.
  Qed.

  rewrite ! sub_plus_mod_eq by reflexivity.
  rewrite ! (Z.mod_small ii Int.zwordsize); auto.
  des (Int.testbit m ii).
  rewrite ! andb_false_r. auto.
- ldt; sld.
  unfold Int.rolm. repeat gotb. 
  eqint ((ii - Int.unsigned amount) mod Int.zwordsize) H2.
  repeat gotb. 
  2: apply Z.mod_pos_bound; reflexivity.
  2: apply Z.mod_pos_bound; reflexivity.
  2: apply Z.mod_pos_bound; reflexivity.
  rewrite ! sub_plus_mod_eq by reflexivity.
  rewrite ! (Z.mod_small ii Int.zwordsize); auto.
Qed.

Definition ror (x: nval) (amount: int) :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.rol m amount)
  | All => All
  end.

Lemma plus_sub_mod_eq:
    forall a b c, c > 0 ->
      ((a + b) mod c - b) mod c = a mod c.
  Proof.
    intros; rewrite <- Z.add_opp_r.
    rewrite (Z.add_mod a b). 2: omega.
    rewrite Z.add_mod. 2: omega.
    rewrite ! Zplus_mod_idemp_l.
    transitivity ((a mod c) mod c). 
    rewrite <- Z.add_assoc.
    destruct (zeq 0 (b mod c)).
    rewrite Z_mod_zero_opp_full. rewrite <- e. f_equal. lia.  lia.
    rewrite Z_mod_nz_opp_full; auto.
    replace (b mod c + (c - b mod c)) with c by lia.
    rewrite Z.add_mod. rewrite Z_mod_same_full. f_equal.
    rewrite Zmod_mod. lia. lia.
    apply Zmod_mod.
  Qed.


Lemma ror_sound:
  forall v w x n,
  vagree v w (ror x n) ->
  vagree (Val.ror v (Eval (Vint n))) (Val.ror w (Eval (Vint n))) x.
Proof.
  unfold ror; intros. unfold Val.ror.
  des x.
  - ldt. destr; auto. sld.
    repeat gotb.
    eqint ((ii + Int.unsigned n) mod Int.zwordsize) H2.
    repeat gotb; try (apply Z.mod_pos_bound; reflexivity).
    rewrite ! plus_sub_mod_eq by reflexivity.
    rewrite ! (Z.mod_small ii Int.zwordsize); auto.
  - eapply Val.lessdef_binop; eauto.
Qed.

(** Modular arithmetic operations: add, mul, opposite.
    (But not subtraction because of the pointer - pointer case. *)

Definition modarith (x: nval) :=
  match x with
  | Nothing => Nothing
  | I m => I (complete_mask m)
  | All => All
  end.

Lemma add_sound:
  forall v1 w1 v2 w2 x,
  vagree v1 w1 (modarith x) -> vagree v2 w2 (modarith x) ->
  vagree (Val.add v1 v2) (Val.add w1 w2) x.
Proof.
  unfold modarith; intros. destruct x; simpl in *. 
- auto.
- ldt. sld.
  (* eqint ii H2. eqint ii H3. *)
  unfold complete_mask.
  repeat gotb.
  des (Int.testbit m ii). 2: rewrite ! andb_false_r; auto.
  rewrite ! andb_true_r.
  intros.
  eapply eqmod_iagree; eauto.
  apply Int.eqmod_add; apply iagree_eqmod; auto.
  red.
  intros.
  eqint i3 H2. repeat gotb. rewrite H0. rewrite ! andb_true_r; auto.
  red; intros. eqint i3 H3. repeat gotb. rewrite H0. rewrite ! andb_true_r; auto.
- eapply Val.lessdef_binop; eauto.
Qed.

Remark modarith_idem: forall nv, modarith (modarith nv) = modarith nv.
Proof.
  destruct nv; simpl; auto. f_equal; apply complete_mask_idem.
Qed.

Lemma mul_sound:
  forall v1 w1 v2 w2 x,
  vagree v1 w1 (modarith x) -> vagree v2 w2 (modarith x) ->
  vagree (Val.mul v1 v2) (Val.mul w1 w2) x.
Proof.
  unfold mul, add; intros. des x.

  - ldt. sld. repeat gotb. des (Int.testbit m ii).
    2: rewrite ! andb_false_r; auto.
    rewrite ! andb_true_r.
    eapply eqmod_iagree; eauto. apply Int.eqmod_mult; apply iagree_eqmod; auto.
    red; intros. eqint i3 H2; repeat gotb; rewrite H0, ! andb_true_r; auto.
    red; intros. eqint i3 H3; repeat gotb; rewrite H0, ! andb_true_r; auto.
  - eapply Val.lessdef_binop; eauto. 
Qed.

Lemma neg_sound:
  forall v w x,
  vagree v w (modarith x) ->
  vagree (Val.neg v) (Val.neg w) x.
Proof.
  intros. des x.
  - ldt. sld. repeat gotb. des (Int.testbit m ii).
    2: rewrite ! andb_false_r; auto.
    rewrite ! andb_true_r.
    eapply eqmod_iagree; eauto. apply Int.eqmod_neg. apply iagree_eqmod; auto.
    red; intros. eqint i1 H2; repeat gotb; rewrite H0, ! andb_true_r; auto.
  - eapply Val.lessdef_unop; eauto. 
Qed.

(** Conversions: zero extension, sign extension, single-of-float *)

Definition zero_ext (n: Z) (x: nval) :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.zero_ext n m)
  | All => I (Int.zero_ext n Int.mone)
  end.

Lemma zero_ext_sound:
  forall v w x n,
  vagree v w (zero_ext n x) ->
  0 <= n ->
  vagree (Val.zero_ext n v) (Val.zero_ext n w) x.
Proof.
  unfold zero_ext; intros.
  des x.
- unfold Val.zero_ext. 
  ldt. sld.
  eqint ii H3.
  repeat gotb.
  des (Int.testbit m ii).
  2: rewrite ! andb_false_r; auto.
  rewrite ! andb_true_r.
  rewrite ! Int.bits_zero_ext; destr.
  rewrite Heqb. rewrite ! andb_true_r; auto.
- ldt; sld. eqint ii H3.
  repeat gotb.
  rewrite ! Int.bits_zero_ext; destr.
  repeat gotb. rewrite ! andb_true_r; auto.
Qed.

Definition sign_ext (n: Z) (x: nval) :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.or (Int.zero_ext n m) (Int.shl Int.one (Int.repr (n - 1))))
  | All => I (Int.zero_ext n Int.mone)
  end.

Lemma sign_ext_sound:
  forall v w x n,
  vagree v w (sign_ext n x) ->
  0 < n < Int.zwordsize ->
  vagree (Val.sign_ext n v) (Val.sign_ext n w) x.
Proof.
  unfold sign_ext; intros.
  des x.
- unfold Val.sign_ext.  
  ldt. sld.
  generalize H3; intro SAVE. 
  eqint ii H3.
  repeat gotb.
  des (Int.testbit m ii).
  2: rewrite ! andb_false_r; auto.
  rewrite ! andb_true_r.
  replace (Int.unsigned (Int.repr (n - 1))) with (n - 1).
  rewrite ! Int.bits_sign_ext, ! Int.bits_zero_ext; destr. destr.
  rewrite Heqb; simpl. rewrite ! andb_true_r; auto.
  rewrite Heqb; simpl. rewrite ! andb_true_r; auto.
  destr. lia. rewrite Int.bits_one.
  destruct (zeq (ii - (n - 1)) 0); simpl.
  assert (ii = n - 1) by lia; subst.
  rewrite ! andb_true_r; auto.
  intros.
  eqint (n-1) SAVE.
  repeat gotb; try lia.
  replace (Int.unsigned (Int.repr (n - 1))) with (n - 1).
  destr; try lia.
  rewrite Int.bits_zero_ext. destr; try lia.
  replace (n - 1 - (n - 1)) with 0 by lia.
  rewrite Int.bits_one. des (zeq 0 0). rewrite !orb_true_r.
  rewrite ! andb_true_r; auto. lia. rewrite Int.unsigned_repr; auto.
  split. lia. transitivity Int.zwordsize. lia. apply Int.wordsize_max_unsigned.
  rewrite Int.unsigned_repr; auto.
  split. lia. transitivity Int.zwordsize. lia. apply Int.wordsize_max_unsigned.
- ldt; sld.
  generalize H3; intro SAVE. eqint ii H3.
  repeat gotb.
  rewrite ! Int.bits_sign_ext, ! Int.bits_zero_ext; destr.
  repeat gotb. rewrite ! andb_true_r; auto.
  intros _ .
  eqint (n-1) SAVE.
  repeat gotb; try lia.
  rewrite ! Int.bits_zero_ext; destr; try lia.
  gotb; try lia. rewrite ! andb_true_r; auto.
Qed.

(** The needs of a memory store concerning the value being stored. *)

Definition store_argument (chunk: memory_chunk) :=
  match chunk with
  | Mint8signed | Mint8unsigned => I (Int.repr 255)
  | Mint16signed | Mint16unsigned => I (Int.repr 65535)
  | _ => All
  end.

Lemma lf2_inj_symb:
  forall P n e t e' t',
    list_forall2 P (inj_symbolic' n e t) (inj_symbolic' n e' t') ->
    list_forall2 P (inj_symbolic n e t) (inj_symbolic n e' t').
Proof.
  intros; unfold inj_symbolic.
  apply IntFacts.list_forall2_rev.
  apply list_forall2_rib. simpl; auto.
Qed.

Lemma store_argument_sound:
  forall chunk v w,
  vagree v w (store_argument chunk) ->
  list_forall2 memval_lessdef (encode_val chunk v) (encode_val chunk w).
Proof.
  intros.

  (* assert (UNDEF: list_forall2 memval_lessdef *)
  (*                    (list_repeat (size_chunk_nat chunk) (Symbolic (Eval Vundef) None O)) *)
  (*                    (encode_val chunk w)). *)
  (* { *)
  (*    rewrite <- (encode_val_length chunk w).  *)
  (*    apply repeat_Undef_inject_any. *)
  (* } *)
  assert (SAME: forall vl1 vl2,
                vl1 = vl2 ->
                list_forall2 memval_lessdef vl1 vl2).
  {
    intros. subst vl2. apply MemRel.lf2_rel_refl.
    apply wf_mr_ld.
  }

  intros. unfold store_argument in H.
  assert (Case8:
            forall v w,
              vagree v w (I (Int.repr 255)) ->
              Val.lessdef
                (Ebinop OpAnd Tlong Tlong (Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint v)
                        (Eval (Vlong (Int64.repr 255))))
                (Ebinop OpAnd Tlong Tlong (Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint w)
                        (Eval (Vlong (Int64.repr 255))))).
  {
    clear; intros.
    simpl in *.
    ldt. sld.
    Ltac gotb' :=
      match goal with
        |- context [Int64.testbit (Int64.or _ _) _] => rewrite Int64.bits_or; try auto
      | |- context [Int64.testbit (Int64.and _ _) _] => rewrite Int64.bits_and; try auto
      | |- context [Int64.testbit (Int64.shl _ _) _] => rewrite Int64.bits_shl; try auto
      | |- context [Int64.testbit (Int64.shr _ _) _] => rewrite Int64.bits_shr; try auto
      | |- context [Int64.testbit (Int64.shru _ _) _] => rewrite Int64.bits_shru; try auto
      | |- context [Int64.testbit (Int64.ror _ _) _] => rewrite Int64.bits_ror; try auto
      | |- context [Int64.testbit (Int64.rol _ _) _] => rewrite Int64.bits_rol; try auto
      | |- context [Int64.testbit (Int64.mone) _] => rewrite Int64.bits_mone; try auto
      end.
    repeat gotb'.

    Lemma bits64_255:
      forall i,
        Int64.testbit (Int64.repr 255) i = if zle 0 i && zlt i 8 then true else false.
    Proof.
      intros; destr.
      rewrite IntFacts.bits64_255_below; auto. apply Mem.zle_zlt in Heqb. auto.
      apply Mem.zle_zlt_false in Heqb.
      des Heqb.
      des i. lia. lia.
      destruct (zlt i Int64.zwordsize).
      apply IntFacts.bits64_255_above. lia.
      apply Int64.bits_above; auto.
    Qed.
    rewrite bits64_255.
    destr.
    2: rewrite ! andb_false_r; auto.
    rewrite ! andb_true_r.
    eqint ii H2. repeat gotb; try (change (Int.zwordsize) with 32%Z; apply Mem.zle_zlt in Heqb; lia).
    rewrite ! IntFacts.bits_255_below by (apply Mem.zle_zlt; auto).
    rewrite ! Int64.testbit_repr; auto. rewrite <- ! Int.testbit_repr by (change (Int.zwordsize) with 32; apply Mem.zle_zlt in Heqb; lia).
    rewrite ! Int.repr_unsigned.
    rewrite ! andb_true_r; auto.
  }    assert (forall v w, vagree v w (I (Int.repr 65535)) ->
   list_forall2 memval_lessdef
     (Symbolic (Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint v) None 1
      :: Symbolic (Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint v) None 0 :: nil)
     (Symbolic (Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint w) None 1
      :: Symbolic (Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint w) None 0 :: nil)).
    {
      clear; intros.
      repeat constructor; simpl in *; auto.
      ldt. destr; auto.
      sld. repeat gotb'.
      rewrite ! IntFacts.shru'_shru by (vm_compute; destr).
      repeat gotb'.
      change (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 8)))) with 8.
      rewrite bits64_255.
      destr. destr. 2: rewrite ! andb_false_r; auto.
      rewrite ! andb_true_r.
      apply Mem.zle_zlt in Heqb0.
      rewrite ! Int64.testbit_repr; auto; try lia.
      rewrite <- ! Int.testbit_repr by (change (Int.zwordsize) with 32; lia).
      rewrite ! Int.repr_unsigned.
      eqint (ii+8) H2. repeat gotb; try (change Int.zwordsize with 32; lia).
      rewrite ! Int.testbit_repr by (change Int.zwordsize with 32; lia) .
      change 65535 with (two_p 16 -1).
      rewrite Int.Ztestbit_two_p_m1 by lia.
      destr.
      rewrite ! andb_true_r; auto.
      lia.
      ldt.
      sld. repeat gotb'.
      rewrite bits64_255.
      destr. 2: rewrite ! andb_false_r; auto.
      rewrite ! andb_true_r.
      apply Mem.zle_zlt in Heqb.
      rewrite ! Int64.testbit_repr; auto; try lia.
      rewrite <- ! Int.testbit_repr by (change (Int.zwordsize) with 32; lia).
      rewrite ! Int.repr_unsigned.
      eqint (ii) H2. repeat gotb; try (change Int.zwordsize with 32; lia).
      rewrite ! Int.testbit_repr by (change Int.zwordsize with 32; lia) .
      change 65535 with (two_p 16 -1).
      rewrite Int.Ztestbit_two_p_m1 by lia.
      destr.
      rewrite ! andb_true_r; auto.
      lia.
    } 
  destruct chunk; unfold encode_val; apply lf2_inj_symb; simpl.

  Ltac ldtrans :=
    repeat (first [ eapply Val.lessdef_binop; eauto
                  | eapply Val.lessdef_unop; eauto ]).

    Lemma memval_ld_vundef:
      forall a b t n,
        same_eval a (Eval Vundef) ->
        memval_lessdef (Symbolic a t n) b.
    Proof.
      red; red; simpl; intros.
      split. red; intros; simpl. rewrite gnp_rew. rewrite H.
      simpl. des n; auto.
      right. red; intros. rewrite gnp_rew. rewrite H. des n.
    Qed.
 
  - repeat constructor; simpl in *; auto.
  - repeat constructor; simpl in *; auto.
  - auto.
  - auto.
  - simpl in H. repeat constructor; simpl; ldtrans.
  - simpl in H. repeat constructor; simpl; ldtrans.
  - simpl in H. repeat constructor; simpl; ldtrans.
  - simpl in H. repeat constructor; simpl; ldtrans.
  - clear Case8 H0. simpl in *.
    generalize (Mem.mr_vundef_get_type _ wf_mr_ld _ _ H).
    intros [A|A].
    + destr;
      repeat apply list_forall2_cons;
        try (apply memval_ld_vundef; red; simpl; intros; try rewrite A; destr);
        constructor.
    + rewrite A. destr; auto;
      repeat apply list_forall2_cons;
      repeat constructor; simpl in *; ldtrans.
  - clear Case8 H0. simpl in *.
    generalize (Mem.mr_vundef_get_type _ wf_mr_ld _ _ H).
    intros [A|A].
    + destr;
      repeat apply list_forall2_cons;
        try (apply memval_ld_vundef; red; simpl; intros; try rewrite A; destr);
        constructor.
    + rewrite A. destr; auto;
      repeat apply list_forall2_cons;
      repeat constructor; simpl in *; ldtrans.
Qed.


Lemma store_argument_load_result:
  forall chunk v w,
  vagree v w (store_argument chunk) ->
  Val.lessdef (Val.load_result chunk v) (Val.load_result chunk w).
Proof.
  unfold store_argument; intros; destruct chunk;
  auto using Val.load_result_lessdef; InvAgree; simpl.
- apply sign_ext_sound with (x:=All). auto. compute; auto.
- apply zero_ext_sound with (x := All) (n := 8).
  auto. omega.
- apply sign_ext_sound with (x := All) (n := 16).
  auto. compute; auto.
- apply zero_ext_sound with  (x := All) (n := 16).
  auto. omega.
Qed.

(** The needs of a comparison *)

Definition maskzero (n: int) := I n.

Lemma maskzero_sound:
  forall v w n ,
  vagree v w (maskzero n) ->
  Val.lessdef (Val.maskzero_bool v n)
              (Val.maskzero_bool w n). 
Proof.
  unfold maskzero; intros. 
  unfold Val.maskzero_bool; InvAgree; try discriminate.
  ldt.
Qed.

(** The default abstraction: if the result is unused, the arguments are
  unused; otherwise, the arguments are needed in full. *)

Definition default (x: nval) :=
  match x with
  | Nothing => Nothing
  | _ => All
  end.

Section DEFAULT.

Variable ge: genv.
Variable sp: block.
Variables m1 m2: mem.
Hypothesis PERM: forall b ofs k p, Mem.perm m1 b ofs k p -> Mem.perm m2 b ofs k p.

Let valid_pointer_inj:
  forall b1 ofs b2 delta,
  inject_id b1 = Some(b2, delta) ->
  Mem.valid_pointer m1 b1 (Int.unsigned ofs) = true ->
  Mem.valid_pointer m2 b2 (Int.unsigned (Int.add ofs (Int.repr delta))) = true.
Proof.
  unfold inject_id; intros. inv H. rewrite Int.add_zero.
  rewrite Mem.valid_pointer_nonempty_perm in *. eauto.
Qed.

Let weak_valid_pointer_inj:
  forall b1 ofs b2 delta,
  inject_id b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Int.unsigned ofs) = true ->
  Mem.weak_valid_pointer m2 b2 (Int.unsigned (Int.add ofs (Int.repr delta))) = true.
Proof.
  unfold inject_id; intros. inv H. rewrite Int.add_zero.
  rewrite Mem.weak_valid_pointer_spec in *.
  rewrite ! Mem.valid_pointer_nonempty_perm in *.
  destruct H0; [left|right]; eauto.
Qed.

Let weak_valid_pointer_no_overflow:
  forall b1 ofs b2 delta,
  inject_id b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Int.unsigned ofs) = true ->
  0 <= Int.unsigned ofs + Int.unsigned (Int.repr delta) <= Int.max_unsigned.
Proof.
  unfold inject_id; intros. inv H. rewrite Zplus_0_r. apply Int.unsigned_range_2.
Qed.

Let valid_different_pointers_inj:
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m1 b1 (Int.unsigned ofs1) = true ->
  Mem.valid_pointer m1 b2 (Int.unsigned ofs2) = true ->
  inject_id b1 = Some (b1', delta1) ->
  inject_id b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Int.unsigned (Int.add ofs1 (Int.repr delta1)) <> Int.unsigned (Int.add ofs2 (Int.repr delta2)).
Proof.
  unfold inject_id; intros. left; congruence.
Qed.

Lemma vagree_list_ld:
  forall args1 args2 l,
    vagree_list args1 args2 l ->
    l = nil ->
    list_forall2 Val.lessdef args1 args2.
Proof.
  induction 1; simpl; intros; eauto.
  constructor.
  constructor; auto.
  inv H1.
Qed.

Lemma default_needs_of_condition_sound:
  forall cond args1 b args2,
  eval_condition cond args1 = Some b ->
  vagree_list args1 args2 nil ->
  exists b',
    eval_condition cond args2 = Some b' /\ Val.lessdef b b'.
Proof.
  intros. eapply eval_condition_rel; eauto. apply wf_mr_ld.
  eapply vagree_list_ld; eauto.
Qed.

Lemma default_needs_of_operation_sound:
  forall op args1 v1 args2 nv,
  eval_operation ge (Eval (Vptr sp Int.zero)) op args1 = Some v1 ->
  vagree_list args1 args2 nil
  \/ vagree_list args1 args2 (default nv :: nil)
  \/ vagree_list args1 args2 (default nv :: default nv :: nil) ->
  nv <> Nothing ->
  exists v2,
     eval_operation ge (Eval (Vptr sp Int.zero)) op args2 = Some v2
  /\ vagree v1 v2 nv.
Proof.
  intros. assert (default nv = All) by (destruct nv; simpl; congruence).
  rewrite H2 in H0.
  assert (Val.lessdef_list args1 args2).
  {
    destruct H0. auto with na.
    destruct H0. inv H0; constructor; auto with na.
    inv H0; constructor; auto with na. inv H8; constructor; auto with na.
  }
  exploit (@eval_operation_rel _ _ ge _ wf_mr_ld (Eval (Vptr sp Int.zero))).
  apply Val.lessdef_list_inv; eauto. eauto.
  intros (v2 & A & B). exists v2; split; auto.
  apply vagree_lessdef. auto.
Qed.

End DEFAULT.

(** ** Detecting operations that are redundant and can be turned into a move *)

Definition andimm_redundant (x: nval) (n: int) :=
  match x with
  | Nothing => true
  | I m => Int.eq_dec (Int.and m (Int.not n)) Int.zero
  | _ => false
  end.

Lemma andimm_redundant_sound:
  forall v w x n,
  andimm_redundant x n = true ->
  vagree v w (andimm x n) ->
  vagree (Val.and v (Eval (Vint n))) w x.
Proof.
  unfold andimm_redundant; intros. des x.
  - ldt. sld. eqint ii H3.
    des (Int.eq_dec (Int.and m (Int.not n)) Int.zero).
    clear Heqs. eqint ii e.
    repeat gotb.
    rewrite Int.bits_not, Int.bits_zero; auto.
    des (Int.testbit i0 ii); des (Int.testbit i ii);
      des (Int.testbit m ii); des (Int.testbit n ii); intros; try ring.
Qed.

Definition orimm_redundant (x: nval) (n: int) :=
  match x with
  | Nothing => true
  | I m => Int.eq_dec (Int.and m n) Int.zero
  | _ => false
  end.

Lemma orimm_redundant_sound:
  forall v w x n,
  orimm_redundant x n = true ->
  vagree v w (orimm x n) ->
  vagree (Val.or v (Eval (Vint n))) w x.
Proof.
  unfold orimm_redundant; intros.
  des x.
  - ldt. sld. eqint ii H3.
    des (Int.eq_dec (Int.and m n) Int.zero).
    clear Heqs. eqint ii e.
    repeat gotb.
    rewrite Int.bits_not, Int.bits_zero; auto.
    des (Int.testbit i0 ii); des (Int.testbit i ii);
      des (Int.testbit m ii); des (Int.testbit n ii); intros; try ring.
Qed.

Definition rolm_redundant (x: nval) (amount mask: int) :=
  Int.eq_dec amount Int.zero && andimm_redundant x mask.

Lemma rolm_redundant_sound:
  forall v w x amount mask,
  rolm_redundant x amount mask = true ->
  vagree v w (rolm x amount mask) ->
  vagree (Val.rolm v amount mask) w x.
Proof.
  unfold rolm_redundant; intros; InvBooleans. subst amount.
  des x.
  - ldt. sld. eqint ii H3.
    des (Int.eq_dec (Int.and m (Int.not mask)) Int.zero).
    clear Heqs. eqint ii e.
    unfold Int.rolm. 
    repeat gotb.    
    rewrite Int.bits_not, Int.bits_zero; auto.
    change (Int.unsigned Int.zero) with 0. rewrite Z.add_0_r.
    rewrite Z.sub_0_r. rewrite Z.mod_small; auto.

    des (Int.testbit i0 ii); des (Int.testbit i ii);
      des (Int.testbit m ii); des (Int.testbit mask ii); intros; try ring.
    change (Int.unsigned Int.zero) with 0. rewrite Z.add_0_r.
    apply Z.mod_pos_bound. vm_compute; destr.
Qed.

Definition zero_ext_redundant (n: Z) (x: nval) :=
  match x with
  | Nothing => true
  | I m => Int.eq_dec (Int.zero_ext n m) m
  | _ => false
  end.

Lemma zero_ext_redundant_sound:
  forall v w x n,
  zero_ext_redundant n x = true ->
  vagree v w (zero_ext n x) ->
  0 <= n ->
  vagree (Val.zero_ext n v) w x.
Proof.
  unfold zero_ext_redundant; intros. des x.
  ldt. sld.
  des (Int.eq_dec (Int.zero_ext n m) m). clear Heqs.
  eqint ii e. eqint ii H4.
  repeat gotb.
  rewrite ! Int.bits_zero_ext by lia.
  destr.
  intros _ A; rewrite <- A; ring.
Qed.

Definition sign_ext_redundant (n: Z) (x: nval) :=
  match x with
  | Nothing => true
  | I m => Int.eq_dec (Int.zero_ext n m) m
  | _ => false
  end.

Lemma sign_ext_redundant_sound:
  forall v w x n,
  sign_ext_redundant n x = true ->
  vagree v w (sign_ext n x) ->
  0 < n ->
  vagree (Val.sign_ext n v) w x.
Proof.
  unfold sign_ext_redundant; intros. des x.
  ldt. sld.
  des (Int.eq_dec (Int.zero_ext n m) m). clear Heqs.
  eqint ii H4. eqint ii e.
  repeat gotb.
  rewrite ! Int.bits_zero_ext by lia.
  rewrite Int.bits_one.
  rewrite Int.bits_sign_ext by lia.
  des (Int.testbit m ii). 2: intros; ring.
  rewrite ! andb_true_r. destr.
  rewrite ! andb_true_r. auto.
Qed.

(** * Neededness for register environments *)

Module NVal <: SEMILATTICE.

  Definition t := nval.
  Definition eq (x y: t) := (x = y).
  Definition eq_refl: forall x, eq x x := (@refl_equal t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@sym_equal t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@trans_equal t).
  Definition beq (x y: t) : bool := proj_sumbool (eq_nval x y).
  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof. unfold beq; intros. InvBooleans. auto. Qed.
  Definition ge := nge.
  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof. unfold eq, ge; intros. subst y. apply nge_refl. Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof. unfold ge; intros. eapply nge_trans; eauto. Qed.
  Definition bot : t := Nothing.
  Lemma ge_bot: forall x, ge x bot.
  Proof. intros. constructor. Qed.
  Definition lub := nlub.
  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof nge_lub_l.
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof nge_lub_r.
End NVal.

Module NE := LPMap1(NVal).

Definition nenv := NE.t. 

Definition nreg (ne: nenv) (r: reg) := NE.get r ne.

Definition eagree (e1 e2: regset) (ne: nenv) : Prop :=
  forall r, vagree e1#r e2#r (NE.get r ne).

Lemma nreg_agree:
  forall rs1 rs2 ne r, eagree rs1 rs2 ne -> vagree rs1#r rs2#r (nreg ne r).
Proof.
  intros. apply H. 
Qed.

Hint Resolve nreg_agree: na.

Lemma eagree_ge:
  forall e1 e2 ne ne',
  eagree e1 e2 ne -> NE.ge ne ne' -> eagree e1 e2 ne'.
Proof.
  intros; red; intros. apply nge_agree with (NE.get r ne); auto. apply H0.  
Qed.

Lemma eagree_bot:
  forall e1 e2, eagree e1 e2 NE.bot.
Proof.
  intros; red; intros. rewrite NE.get_bot. exact Logic.I.
Qed.

Lemma eagree_same:
  forall e ne, eagree e e ne.
Proof.
  intros; red; intros. apply vagree_same. 
Qed.

Lemma eagree_update_1:
  forall e1 e2 ne v1 v2 nv r,
  eagree e1 e2 ne -> vagree v1 v2 nv -> eagree (e1#r <- v1) (e2#r <- v2) (NE.set r nv ne).
Proof.
  intros; red; intros. rewrite NE.gsspec. rewrite ! PMap.gsspec. 
  destruct (peq r0 r); auto. 
Qed.

Lemma eagree_update:
  forall e1 e2 ne v1 v2 r,
  vagree v1 v2 (nreg ne r) ->
  eagree e1 e2 (NE.set r Nothing ne) ->
  eagree (e1#r <- v1) (e2#r <- v2) ne.
Proof.
  intros; red; intros. specialize (H0 r0). rewrite NE.gsspec in H0. 
  rewrite ! PMap.gsspec. destruct (peq r0 r).
  subst r0. auto.
  auto.
Qed.

Lemma eagree_update_dead:
  forall e1 e2 ne v1 r,
  nreg ne r = Nothing ->
  eagree e1 e2 ne -> eagree (e1#r <- v1) e2 ne.
Proof.
  intros; red; intros. rewrite PMap.gsspec. 
  destruct (peq r0 r); auto. subst. unfold nreg in H. rewrite H. red; auto. 
Qed.

(** * Neededness for memory locations *)

Inductive nmem : Type :=
  | NMemDead
  | NMem (stk: ISet.t) (gl: PTree.t ISet.t).

(** Interpretation of [nmem]:
- [NMemDead]: all memory locations are unused (dead).  Acts as bottom.
- [NMem stk gl]: all memory locations are used, except:
  - the stack locations whose offset is in the interval [stk]
  - the global locations whose offset is in the corresponding entry of [gl].
*)

Section LOCATIONS.

Variable ge: genv.
Variable sp: block.

Inductive nlive: nmem -> block -> Z -> Prop :=
  | nlive_intro: forall stk gl b ofs
      (STK: b = sp -> ~ISet.In ofs stk)
      (GL: forall id iv,
           Genv.find_symbol ge id = Some b ->
           gl!id = Some iv ->
           ~ISet.In ofs iv),
      nlive (NMem stk gl) b ofs.

(** All locations are live *)

Definition nmem_all := NMem ISet.empty (PTree.empty _).

Lemma nlive_all: forall b ofs, nlive nmem_all b ofs.
Proof.
  intros; constructor; intros.
  apply ISet.In_empty.
  rewrite PTree.gempty in H0; discriminate.
Qed.

(** Add a range of live locations to [nm].  The range starts at
  the abstract pointer [p] and has length [sz]. *)

Definition nmem_add (nm: nmem) (p: aptr) (sz: Z) : nmem :=
  match nm with
  | NMemDead => nmem_all       (**r very conservative, should never happen *)
  | NMem stk gl =>
      match p with
      | Gl id ofs =>
          match gl!id with
          | Some iv => NMem stk (PTree.set id (ISet.remove (Int.unsigned ofs) (Int.unsigned ofs + sz) iv) gl)
          | None => nm
          end
      | Glo id =>
          NMem stk (PTree.remove id gl)
      | Stk ofs =>
          NMem (ISet.remove (Int.unsigned ofs) (Int.unsigned ofs + sz) stk) gl
      | Stack =>
          NMem ISet.empty gl
      | _ => nmem_all
      end
  end.

Lemma nlive_add:
  forall bc b ofs p nm sz i,
  genv_match bc ge ->
  bc sp = BCstack ->
  pmatch bc b ofs p ->
  Int.unsigned ofs <= i < Int.unsigned ofs + sz ->
  nlive (nmem_add nm p sz) b i.
Proof.
  intros. unfold nmem_add. destruct nm. apply nlive_all. 
  inv H1; try (apply nlive_all). 
  - (* Gl id ofs *)
    assert (Genv.find_symbol ge id = Some b) by (eapply H; eauto). 
    destruct gl!id as [iv|] eqn:NG.
  + constructor; simpl; intros. 
    congruence.
    assert (id0 = id) by (eapply Genv.genv_vars_inj; eauto). subst id0.
    rewrite PTree.gss in H5. inv H5. rewrite ISet.In_remove.
    intros [A B]. elim A; auto.
  + constructor; simpl; intros.
    congruence.
    assert (id0 = id) by (eapply Genv.genv_vars_inj; eauto). subst id0.
    congruence.
  - (* Glo id *)
    assert (Genv.find_symbol ge id = Some b) by (eapply H; eauto). 
    constructor; simpl; intros.
    congruence.
    assert (id0 = id) by (eapply Genv.genv_vars_inj; eauto). subst id0. 
    rewrite PTree.grs in H5. congruence.
  - (* Stk ofs *)
    constructor; simpl; intros. 
    rewrite ISet.In_remove. intros [A B]. elim A; auto.
    assert (bc b = BCglob id) by (eapply H; eauto). congruence.
  - (* Stack *)
    constructor; simpl; intros.
    apply ISet.In_empty.
    assert (bc b = BCglob id) by (eapply H; eauto). congruence.
Qed.

Lemma incl_nmem_add:
  forall nm b i p sz,
  nlive nm b i -> nlive (nmem_add nm p sz) b i.
Proof.
  intros. inversion H; subst. unfold nmem_add; destruct p; try (apply nlive_all).
- (* Gl id ofs *)
  destruct gl!id as [iv|] eqn:NG.
  + split; simpl; intros. auto. 
    rewrite PTree.gsspec in H1. destruct (peq id0 id); eauto. inv H1. 
    rewrite ISet.In_remove. intros [P Q]. eelim GL; eauto.
  + auto. 
- (* Glo id *)
  split; simpl; intros. auto. 
  rewrite PTree.grspec in H1. destruct (PTree.elt_eq id0 id). congruence. eauto.
- (* Stk ofs *)
  split; simpl; intros. 
  rewrite ISet.In_remove. intros [P Q]. eelim STK; eauto.
  eauto.
- (* Stack *)
  split; simpl; intros. 
  apply ISet.In_empty.
  eauto.
Qed.

(** Remove a range of locations from [nm], marking these locations as dead.
  The range starts at the abstract pointer [p] and has length [sz]. *)

Definition nmem_remove (nm: nmem) (p: aptr) (sz: Z) : nmem :=
  match nm with
  | NMemDead => NMemDead
  | NMem stk gl =>
    match p with
    | Gl id ofs =>
        let iv' :=
        match gl!id with
        | Some iv => ISet.add (Int.unsigned ofs) (Int.unsigned ofs + sz) iv
        | None    => ISet.interval (Int.unsigned ofs) (Int.unsigned ofs + sz)
        end in
        NMem stk (PTree.set id iv' gl)
    | Stk ofs =>
        NMem (ISet.add (Int.unsigned ofs) (Int.unsigned ofs + sz) stk) gl
    | _ => nm
    end
  end.

Lemma nlive_remove:
  forall bc b ofs p nm sz b' i,
  genv_match bc ge ->
  bc sp = BCstack ->
  pmatch bc b ofs p ->
  nlive nm b' i ->
  b' <> b \/ i < Int.unsigned ofs \/ Int.unsigned ofs + sz <= i ->
  nlive (nmem_remove nm p sz) b' i.
Proof.
  intros. inversion H2; subst. unfold nmem_remove; inv H1; auto.
- (* Gl id ofs *)
  set (iv' := match gl!id with
                  | Some iv =>
                      ISet.add (Int.unsigned ofs) (Int.unsigned ofs + sz) iv
                  | None =>
                      ISet.interval (Int.unsigned ofs)
                        (Int.unsigned ofs + sz)
              end).
  assert (Genv.find_symbol ge id = Some b) by (eapply H; eauto).
  split; simpl; auto; intros.
  rewrite PTree.gsspec in H6. destruct (peq id0 id).
+ inv H6. destruct H3. congruence. destruct gl!id as [iv0|] eqn:NG.
  rewrite ISet.In_add. intros [P|P]. omega. eelim GL; eauto. 
  rewrite ISet.In_interval. omega. 
+ eauto. 
- (* Stk ofs *)
  split; simpl; auto; intros. destruct H3. 
  elim H3. subst b'. eapply bc_stack; eauto. 
  rewrite ISet.In_add. intros [P|P]. omega. eapply STK; eauto. 
Qed.

(** Test (conservatively) whether some locations in the range delimited
  by [p] and [sz] can be live in [nm]. *)

Definition nmem_contains (nm: nmem) (p: aptr) (sz: Z) :=
  match nm with
  | NMemDead => false
  | NMem stk gl =>
      match p with
      | Gl id ofs =>
          match gl!id with
          | Some iv => negb (ISet.contains (Int.unsigned ofs) (Int.unsigned ofs + sz) iv)
          | None => true
          end
      | Stk ofs =>
          negb (ISet.contains (Int.unsigned ofs) (Int.unsigned ofs + sz) stk)
      | _ => true  (**r conservative answer *)
      end
  end.

Lemma nlive_contains:
  forall bc b ofs p nm sz i,
  genv_match bc ge ->
  bc sp = BCstack ->
  pmatch bc b ofs p ->
  nmem_contains nm p sz = false ->
  Int.unsigned ofs <= i < Int.unsigned ofs + sz ->
  ~(nlive nm b i).
Proof.
  unfold nmem_contains; intros. red; intros L; inv L.
  inv H1; try discriminate.
- (* Gl id ofs *)
  assert (Genv.find_symbol ge id = Some b) by (eapply H; eauto).
  destruct gl!id as [iv|] eqn:HG; inv H2. 
  destruct (ISet.contains (Int.unsigned ofs) (Int.unsigned ofs + sz) iv) eqn:IC; try discriminate.
  rewrite ISet.contains_spec in IC. eelim GL; eauto.
- (* Stk ofs *) 
  destruct (ISet.contains (Int.unsigned ofs) (Int.unsigned ofs + sz) stk) eqn:IC; try discriminate.
  rewrite ISet.contains_spec in IC. eelim STK; eauto. eapply bc_stack; eauto. 
Qed.

(** Kill all stack locations between 0 and [sz], and mark everything else
  as live.  This reflects the effect of freeing the stack block at
  a [Ireturn] or [Itailcall] instruction. *)

Definition nmem_dead_stack (sz: Z) :=
  NMem (ISet.interval 0 sz) (PTree.empty _).

Lemma nlive_dead_stack:
  forall sz b' i, b' <> sp \/ ~(0 <= i < sz) -> nlive (nmem_dead_stack sz) b' i.
Proof.
  intros; constructor; simpl; intros.
- rewrite ISet.In_interval. intuition. 
- rewrite PTree.gempty in H1; discriminate.
Qed.

(** Least upper bound *)

Definition nmem_lub (nm1 nm2: nmem) : nmem :=
  match nm1, nm2 with
  | NMemDead, _ => nm2
  | _, NMemDead => nm1
  | NMem stk1 gl1, NMem stk2 gl2 =>
      NMem (ISet.inter stk1 stk2)
           (PTree.combine
                (fun o1 o2 =>
                  match o1, o2 with
                  | Some iv1, Some iv2 => Some(ISet.inter iv1 iv2)
                  | _, _ => None
                  end)
                gl1 gl2)
  end.

Lemma nlive_lub_l:
  forall nm1 nm2 b i, nlive nm1 b i -> nlive (nmem_lub nm1 nm2) b i.
Proof.
  intros. inversion H; subst. destruct nm2; simpl. auto.
  constructor; simpl; intros.
- rewrite ISet.In_inter. intros [P Q]. eelim STK; eauto.
- rewrite PTree.gcombine in H1 by auto. 
  destruct gl!id as [iv1|] eqn:NG1; try discriminate;
  destruct gl0!id as [iv2|] eqn:NG2; inv H1.
  rewrite ISet.In_inter. intros [P Q]. eelim GL; eauto. 
Qed.

Lemma nlive_lub_r:
  forall nm1 nm2 b i, nlive nm2 b i -> nlive (nmem_lub nm1 nm2) b i.
Proof.
  intros. inversion H; subst. destruct nm1; simpl. auto.
  constructor; simpl; intros.
- rewrite ISet.In_inter. intros [P Q]. eelim STK; eauto.
- rewrite PTree.gcombine in H1 by auto. 
  destruct gl0!id as [iv1|] eqn:NG1; try discriminate;
  destruct gl!id as [iv2|] eqn:NG2; inv H1.
  rewrite ISet.In_inter. intros [P Q]. eelim GL; eauto. 
Qed.

(** Boolean-valued equality test *)

Definition nmem_beq (nm1 nm2: nmem) : bool :=
  match nm1, nm2 with
  | NMemDead, NMemDead => true
  | NMem stk1 gl1, NMem stk2 gl2 => ISet.beq stk1 stk2 && PTree.beq ISet.beq gl1 gl2
  | _, _ => false
  end.

Lemma nmem_beq_sound:
  forall nm1 nm2 b ofs,
  nmem_beq nm1 nm2 = true ->
  (nlive nm1 b ofs <-> nlive nm2 b ofs).
Proof.
  unfold nmem_beq; intros. 
  destruct nm1 as [ | stk1 gl1]; destruct nm2 as [ | stk2 gl2]; try discriminate.
- split; intros L; inv L.
- InvBooleans. rewrite ISet.beq_spec in H0. rewrite PTree.beq_correct in H1.
  split; intros L; inv L; constructor; intros.
+ rewrite <- H0. eauto. 
+ specialize (H1 id). rewrite H2 in H1. destruct gl1!id as [iv1|] eqn: NG; try contradiction.
  rewrite ISet.beq_spec in H1. rewrite <- H1. eauto. 
+ rewrite H0. eauto. 
+ specialize (H1 id). rewrite H2 in H1. destruct gl2!id as [iv2|] eqn: NG; try contradiction.
  rewrite ISet.beq_spec in H1. rewrite H1. eauto.
Qed. 

End LOCATIONS.


(** * The lattice for dataflow analysis *)

Module NA <: SEMILATTICE.

  Definition t := (nenv * nmem)%type.

  Definition eq (x y: t) :=
    NE.eq (fst x) (fst y) /\
    (forall ge sp b ofs, nlive ge sp (snd x) b ofs <-> nlive ge sp (snd y) b ofs).

  Lemma eq_refl: forall x, eq x x.
  Proof.
    unfold eq; destruct x; simpl; split. apply NE.eq_refl. tauto. 
  Qed.
  Lemma eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    unfold eq; destruct x, y; simpl. intros [A B]. 
    split. apply NE.eq_sym; auto.
    intros. rewrite B. tauto.
  Qed.
  Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq; destruct x, y, z; simpl. intros [A B] [C D]; split.
    eapply NE.eq_trans; eauto.
    intros. rewrite B; auto.
  Qed.

  Definition beq (x y: t) : bool :=
    NE.beq (fst x) (fst y) && nmem_beq (snd x) (snd y).
 
  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    unfold beq, eq; destruct x, y; simpl; intros. InvBooleans. split. 
    apply NE.beq_correct; auto.
    intros. apply nmem_beq_sound; auto.
  Qed.

  Definition ge (x y: t) : Prop :=
    NE.ge (fst x) (fst y) /\
    (forall ge sp b ofs, nlive ge sp (snd y) b ofs -> nlive ge sp (snd x) b ofs).

  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold eq, ge; destruct x, y; simpl. intros [A B]; split.
    apply NE.ge_refl; auto.
    intros. apply B; auto.
  Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge; destruct x, y, z; simpl. intros [A B] [C D]; split.
    eapply NE.ge_trans; eauto.
    auto.
  Qed.

  Definition bot : t := (NE.bot, NMemDead).

  Lemma ge_bot: forall x, ge x bot.
  Proof.
    unfold ge, bot; destruct x; simpl. split.
    apply NE.ge_bot.
    intros. inv H. 
  Qed.

  Definition lub (x y: t) : t :=
    (NE.lub (fst x) (fst y), nmem_lub (snd x) (snd y)).

  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold ge; destruct x, y; simpl; split. 
    apply NE.ge_lub_left.
    intros; apply nlive_lub_l; auto.
  Qed.
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    unfold ge; destruct x, y; simpl; split. 
    apply NE.ge_lub_right.
    intros; apply nlive_lub_r; auto.
  Qed.

End NA.

