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

(** Locations are a refinement of RTL pseudo-registers, used to reflect
  the results of register allocation (file [Allocation]). *)

Require Import OrderedType.
Require Import Coqlib.
Require Import Maps.
Require Import Ordered.
Require Import AST.
Require Import Values.
Require Export Machregs.
Require Import ExprEval.
Require Import Values_symbolic.
Require Import Values_symbolictype.
Require Import NormaliseSpec.

(** * Representation of locations *)

(** A location is either a processor register or (an abstract designation of)
  a slot in the activation record of the current function. *)

(** ** Processor registers *)

(** Processor registers usable for register allocation are defined
  in module [Machregs]. *)

(** ** Slots in activation records *)

(** A slot in an activation record is designated abstractly by a kind,
  a type and an integer offset.  Three kinds are considered:
- [Local]: these are the slots used by register allocation for 
  pseudo-registers that cannot be assigned a hardware register.
- [Incoming]: used to store the parameters of the current function
  that cannot reside in hardware registers, as determined by the 
  calling conventions.
- [Outgoing]: used to store arguments to called functions that 
  cannot reside in hardware registers, as determined by the 
  calling conventions. *)

Inductive slot: Type :=
  | Local
  | Incoming
  | Outgoing.

(** Morally, the [Incoming] slots of a function are the [Outgoing]
slots of its caller function.

The type of a slot indicates how it will be accessed later once mapped to
actual memory locations inside a memory-allocated activation record:
as 32-bit integers/pointers (type [Tint]) or as 64-bit floats (type [Tfloat]).

The offset of a slot, combined with its type and its kind, identifies
uniquely the slot and will determine later where it resides within the
memory-allocated activation record.  Offsets are always positive.
*)

Lemma slot_eq: forall (p q: slot), {p = q} + {p <> q}.
Proof.
  decide equality.
Defined.

Open Scope Z_scope.

Definition typesize (ty: typ) : Z :=
  match ty with
  | AST.Tint => 1
  | AST.Tlong => 2
  | AST.Tfloat => 2
  | AST.Tsingle => 1
  | AST.Tany32 => 1
  | AST.Tany64 => 2
  end.

Lemma typesize_pos:
  forall (ty: typ), typesize ty > 0.
Proof.
  destruct ty; compute; auto.
Qed.

(** ** Locations *)

(** Locations are just the disjoint union of machine registers and
  activation record slots. *)

Inductive loc : Type :=
  | R (r: mreg)
  | S (sl: slot) (pos: Z) (ty: typ).

Module Loc.

  Definition type (l: loc) : typ :=
    match l with
    | R r => mreg_type r
    | S sl pos ty => ty
    end.

  Lemma eq: forall (p q: loc), {p = q} + {p <> q}.
  Proof.
    decide equality.
    apply mreg_eq.
    (* apply typ_eq. *)
    (* apply zeq. *)
    apply slot_eq.
  Defined.

(** As mentioned previously, two locations can be different (in the sense
  of the [<>] mathematical disequality), yet denote 
  overlapping memory chunks within the activation record.
  Given two locations, three cases are possible:
- They are equal (in the sense of the [=] equality)
- They are different and non-overlapping.
- They are different but overlapping.

  The second case (different and non-overlapping) is characterized 
  by the following [Loc.diff] predicate.
*)
  Definition diff (l1 l2: loc) : Prop :=
    match l1, l2 with
    | R r1, R r2 => 
        r1 <> r2
    | S s1 d1 t1, S s2 d2 t2 =>
        s1 <> s2 \/ d1 + typesize t1 <= d2 \/ d2 + typesize t2 <= d1
    | _, _ =>
        True
    end.

  Lemma same_not_diff:
    forall l, ~(diff l l).
  Proof.
    destruct l; unfold diff; auto.
    red; intros. destruct H; auto. generalize (typesize_pos ty); omega. 
  Qed.

  Lemma diff_not_eq:
    forall l1 l2, diff l1 l2 -> l1 <> l2.
  Proof.
    unfold not; intros. subst l2. elim (same_not_diff l1 H).
  Qed.

  Lemma diff_sym:
    forall l1 l2, diff l1 l2 -> diff l2 l1.
  Proof.
    destruct l1; destruct l2; unfold diff; auto.
    intuition.
  Qed.

  Definition diff_dec (l1 l2: loc) : { Loc.diff l1 l2 } + { ~Loc.diff l1 l2 }.
  Proof.
    intros. destruct l1; destruct l2; simpl.
  - destruct (mreg_eq r r0). right; tauto. left; auto.
  - left; auto.
  - left; auto.
  - destruct (slot_eq sl sl0).
    destruct (zle (pos + typesize ty) pos0).
    left; auto.
    destruct (zle (pos0 + typesize ty0) pos).
    left; auto.
    right; red; intros [P | [P | P]]. congruence. omega. omega. 
    left; auto.
  Defined.

(** We now redefine some standard notions over lists, using the [Loc.diff]
  predicate instead of standard disequality [<>].

  [Loc.notin l ll] holds if the location [l] is different from all locations
  in the list [ll]. *)

  Fixpoint notin (l: loc) (ll: list loc) {struct ll} : Prop :=
    match ll with
    | nil => True
    | l1 :: ls => diff l l1 /\ notin l ls
    end.

  Lemma notin_iff:
    forall l ll, notin l ll <-> (forall l', In l' ll -> Loc.diff l l').
  Proof.
    induction ll; simpl. 
    tauto.
    rewrite IHll. intuition. subst a. auto. 
  Qed.

  Lemma notin_not_in:
    forall l ll, notin l ll -> ~(In l ll).
  Proof.
    intros; red; intros. rewrite notin_iff in H.
    elim (diff_not_eq l l); auto.
  Qed.

  Lemma notin_dec (l: loc) (ll: list loc) : {notin l ll} + {~notin l ll}.
  Proof.
    induction ll; simpl.
    left; auto.
    destruct (diff_dec l a).
    destruct IHll.
    left; auto.
    right; tauto.
    right; tauto.
  Defined.

(** [Loc.disjoint l1 l2] is true if the locations in list [l1]
  are different from all locations in list [l2]. *)

  Definition disjoint (l1 l2: list loc) : Prop :=
    forall x1 x2, In x1 l1 -> In x2 l2 -> diff x1 x2.

  Lemma disjoint_cons_left:
    forall a l1 l2,
    disjoint (a :: l1) l2 -> disjoint l1 l2.
  Proof.
    unfold disjoint; intros. auto with coqlib.    
  Qed.
  Lemma disjoint_cons_right:
    forall a l1 l2,
    disjoint l1 (a :: l2) -> disjoint l1 l2.
  Proof.
    unfold disjoint; intros. auto with coqlib.    
  Qed.

  Lemma disjoint_sym:
    forall l1 l2, disjoint l1 l2 -> disjoint l2 l1.
  Proof.
    unfold disjoint; intros. apply diff_sym; auto.
  Qed.

  Lemma in_notin_diff:
    forall l1 l2 ll, notin l1 ll -> In l2 ll -> diff l1 l2.
  Proof.
    intros. rewrite notin_iff in H. auto. 
  Qed.

  Lemma notin_disjoint:
    forall l1 l2,
    (forall x, In x l1 -> notin x l2) -> disjoint l1 l2.
  Proof.
    intros; red; intros. exploit H; eauto. rewrite notin_iff; intros. auto. 
  Qed.

  Lemma disjoint_notin:
    forall l1 l2 x, disjoint l1 l2 -> In x l1 -> notin x l2.
  Proof.
    intros; rewrite notin_iff; intros. red in H. auto. 
  Qed.

(** [Loc.norepet ll] holds if the locations in list [ll] are pairwise
  different. *)

  Inductive norepet : list loc -> Prop :=
  | norepet_nil:
      norepet nil
  | norepet_cons:
      forall hd tl, notin hd tl -> norepet tl -> norepet (hd :: tl).

  Lemma norepet_dec (ll: list loc) : {norepet ll} + {~norepet ll}.
  Proof.
    induction ll.
    left; constructor.
    destruct (notin_dec a ll).
    destruct IHll.
    left; constructor; auto.
    right; red; intros P; inv P; contradiction.
    right; red; intros P; inv P; contradiction.
  Defined.

(** [Loc.no_overlap l1 l2] holds if elements of [l1] never overlap partially
  with elements of [l2]. *)

  Definition no_overlap (l1 l2 : list loc) :=
   forall r, In r l1 -> forall s, In s l2 ->  r = s \/ Loc.diff r s.

End Loc.

(** * Mappings from locations to values *)

(** The [Locmap] module defines mappings from locations to values,
  used as evaluation environments for the semantics of the [LTL] 
  and [Linear] intermediate languages.  *)

Set Implicit Arguments.

Module Locmap.

  Definition t := loc -> expr_sym.

  Definition init : t := fun (_: loc) => Eval Vundef.

  Definition get (l: loc) (m: t) : expr_sym := m l.

  (** The [set] operation over location mappings reflects the overlapping
      properties of locations: changing the value of a location [l]
      invalidates (sets to [Vundef]) the locations that partially overlap
      with [l].  In other terms, the result of [set l v m]
      maps location [l] to value [v], locations that overlap with [l]
      to [Vundef], and locations that are different (and non-overlapping)
      from [l] to their previous values in [m].  This is apparent in the
      ``good variables'' properties [Locmap.gss] and [Locmap.gso].

      Additionally, the [set] operation also anticipates the fact that
      abstract stack slots are mapped to concrete memory locations
      in the [Stacking] phase.  Hence, values stored in stack slots
      are normalized according to the type of the slot. *)

  Definition set (l: loc) (v: expr_sym) (m: t) : t :=
    fun (p: loc) =>
      if Loc.eq l p then
        match l with R r => v | S sl ofs ty => Val.load_result (chunk_of_type ty) v end
      else if Loc.diff_dec l p then
             (m p)
      else Eval Vundef.

  Lemma gss: forall l v m,
    (set l v m) l = 
    match l with R r => v | S sl ofs ty => Val.load_result (chunk_of_type ty) v end.
  Proof.
    intros. unfold set. rewrite dec_eq_true.
    destruct l; auto.
  Qed.

  Lemma gss_reg: forall r v m, (set (R r) v m) (R r) = v.
  Proof.
    intros. unfold set. rewrite dec_eq_true. auto.
  Qed.

  Lemma gss_typed: forall l v m, Memdata.wt v (Loc.type l) -> same_eval ((set l v m) l) v.
  Proof.
    intros. rewrite gss. destruct l. reflexivity. simpl in *. 
    generalize (Events.type_load_result (chunk_of_type ty) v).
    des ty; red; simpl; intros;
    destruct H as [[t [A B]]|A]; try (des t; [idtac];
                                      generalize (expr_type _ _ A cm em); seval);
    try (rewrite nwt_expr_undef; auto; fail).
    rewrite Integers.Int.sign_ext_above; auto. IntFacts.unfsize. omega.
    rewrite Integers.Int64.sign_ext_above; auto. IntFacts.unfsize. omega.
    repeat destr. des t.
    repeat destr.
    rewrite nwt_expr_undef; auto.
  Qed.

  Lemma gso: forall l v m p, Loc.diff l p -> (set l v m) p = m p.
  Proof.
    intros. unfold set. destruct (Loc.eq l p).
    subst p. elim (Loc.same_not_diff _ H).
    destruct (Loc.diff_dec l p).
    auto.
    contradiction.
  Qed.

  Fixpoint undef (ll: list loc) (m: t) {struct ll} : t :=
    match ll with
    | nil => m
    | l1 :: ll' => undef ll' (set l1 (Eval Vundef) m)
    end.
    
  Lemma guo: forall ll l m, Loc.notin l ll -> (undef ll m) l = m l.
  Proof.
    induction ll; simpl; intros. auto. 
    destruct H. rewrite IHll; auto. apply gso. apply Loc.diff_sym; auto.
  Qed.

  Lemma gus: forall ll l m, In l ll -> same_eval ((undef ll m) l) (Eval Vundef).
  Proof.
    assert (P: forall ll l m, same_eval (m l) (Eval Vundef) ->
                              same_eval ((undef ll m) l) (Eval Vundef)).
    induction ll; simpl; intros.  rewrite  H; reflexivity.  apply IHll. 
    unfold set. destruct (Loc.eq a l).
    destruct a. reflexivity. destruct ty; simpl; constructor; simpl; intros; unfold convert_t; reflexivity.
    destruct (Loc.diff_dec a l); auto. reflexivity.
    induction ll; simpl; intros. contradiction. 
    destruct H. apply P. subst a. apply gss_typed. left; exists (Loc.type l); split; destr.
    apply Memdata.subtype_refl.
    auto.
  Qed.

  Fixpoint setlist (ll: list loc) (vl: list expr_sym) (m: t) {struct ll} : t :=
    match ll, vl with
    | l1 :: ls, v1 :: vs => setlist ls vs (set l1 v1 m)
    | _, _ => m
    end.

  Lemma gsetlisto: forall l ll vl m, Loc.notin l ll -> (setlist ll vl m) l = m l.
  Proof.
    induction ll; simpl; intros. 
    auto.
    destruct vl; auto. destruct H. rewrite IHll; auto. apply gso; auto. apply Loc.diff_sym; auto.
  Qed.

End Locmap.

(** * Total ordering over locations *)

Module IndexedTyp <: INDEXED_TYPE.
  Definition t := typ.
  Definition index (x: t) :=
    match x with
    | AST.Tany32 => 1%positive
    | AST.Tint => 2%positive
    | AST.Tsingle => 3%positive
    | AST.Tany64 => 4%positive
    | AST.Tfloat => 5%positive
    | AST.Tlong => 6%positive
    end.
  Lemma index_inj: forall x y, index x = index y -> x = y.
  Proof. destruct x; destruct y; simpl; congruence. Qed.
  Definition eq := typ_eq.
End IndexedTyp.

Module OrderedTyp := OrderedIndexed(IndexedTyp).

Module IndexedSlot <: INDEXED_TYPE.
  Definition t := slot.
  Definition index (x: t) :=
    match x with Local => 1%positive | Incoming => 2%positive | Outgoing => 3%positive end.
  Lemma index_inj: forall x y, index x = index y -> x = y.
  Proof. destruct x; destruct y; simpl; congruence. Qed.
  Definition eq := slot_eq.
End IndexedSlot.

Module OrderedSlot := OrderedIndexed(IndexedSlot).

Module OrderedLoc <: OrderedType.
  Definition t := loc.
  Definition eq (x y: t) := x = y.
  Definition lt (x y: t) :=
    match x, y with
    | R r1, R r2 => Plt (IndexedMreg.index r1) (IndexedMreg.index r2)
    | R _, S _ _ _ => True
    | S _ _ _, R _ => False
    | S sl1 ofs1 ty1, S sl2 ofs2 ty2 =>
        OrderedSlot.lt sl1 sl2 \/ (sl1 = sl2 /\
        (ofs1 < ofs2 \/ (ofs1 = ofs2 /\ OrderedTyp.lt ty1 ty2)))
    end.
  Lemma eq_refl : forall x : t, eq x x.
  Proof (@refl_equal t). 
  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof (@sym_equal t).
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof (@trans_equal t).
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros. 
    destruct x; destruct y; destruct z; try tauto.
    eapply Plt_trans; eauto.
    destruct H. 
    destruct H0. left; eapply OrderedSlot.lt_trans; eauto.
    destruct H0. subst sl0. auto. 
    destruct H. subst sl.
    destruct H0. auto.
    destruct H. 
    right.  split. auto.
    intuition.
    right; split. congruence. eapply OrderedTyp.lt_trans; eauto. 
  Qed.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq; intros; red; intros. subst y. 
    destruct x. 
    eelim Plt_strict; eauto.
    destruct H. eelim OrderedSlot.lt_not_eq; eauto. red; auto. 
    destruct H. destruct H0. omega. 
    destruct H0. eelim OrderedTyp.lt_not_eq; eauto. red; auto.
  Qed.
  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros. destruct x; destruct y.
  - destruct (OrderedPositive.compare (IndexedMreg.index r) (IndexedMreg.index r0)).
    + apply LT. red. auto. 
    + apply EQ. red. f_equal. apply IndexedMreg.index_inj. auto. 
    + apply GT. red. auto.
  - apply LT. red; auto. 
  - apply GT. red; auto.
  - destruct (OrderedSlot.compare sl sl0).
    + apply LT. red; auto.
    + destruct (OrderedZ.compare pos pos0).
      * apply LT. red. auto. 
      * destruct (OrderedTyp.compare ty ty0).
        apply LT. red; auto.
        apply EQ. red; red in e; red in e0; red in e1. congruence. 
        apply GT. red; auto.
      * apply GT. red. auto. 
    + apply GT. red; auto.
  Defined.
  Definition eq_dec := Loc.eq.

(** Connection between the ordering defined here and the [Loc.diff] predicate. *)

  Definition diff_low_bound (l: loc) : loc :=
    match l with
    | R mr => l
    | S sl ofs ty => S sl (ofs - 1) Tany64
    end.

  Definition diff_high_bound (l: loc) : loc :=
    match l with
    | R mr => l
    | S sl ofs ty => S sl (ofs + typesize ty - 1) AST.Tlong
    end.

  Lemma outside_interval_diff:
    forall l l', lt l' (diff_low_bound l) \/ lt (diff_high_bound l) l' -> Loc.diff l l'.
  Proof.
    intros. 
    destruct l as [mr | sl ofs ty]; destruct l' as [mr' | sl' ofs' ty']; simpl in *; auto.
    - assert (IndexedMreg.index mr <> IndexedMreg.index mr').
      { destruct H. apply sym_not_equal. apply Plt_ne; auto. apply Plt_ne; auto. }
      congruence.
    - assert (RANGE: forall ty, 1 <= typesize ty <= 2).
      { intros; unfold typesize. destruct ty0; omega.  }
      destruct H. 
      + destruct H. left. apply sym_not_equal. apply OrderedSlot.lt_not_eq; auto. 
        destruct H. right.
        destruct H0. right. generalize (RANGE ty'); omega. 
        destruct H0. 
        assert (ty' = AST.Tint \/ ty' = AST.Tsingle \/ ty' = AST.Tany32). 
        { unfold OrderedTyp.lt in H1. destruct ty'; auto; compute in H1; congruence. }
        right. destruct H2 as [E|[E|E]]; subst ty'; simpl typesize; omega. 
      + destruct H. left. apply OrderedSlot.lt_not_eq; auto.
        destruct H. right.
        destruct H0. left; omega.
        destruct H0. exfalso. destruct ty'; compute in H1; congruence.
  Qed.

  Lemma diff_outside_interval:
    forall l l', Loc.diff l l' -> lt l' (diff_low_bound l) \/ lt (diff_high_bound l) l'.
  Proof.
    intros. 
    destruct l as [mr | sl ofs ty]; destruct l' as [mr' | sl' ofs' ty']; simpl in *; auto.
    - unfold Plt, Pos.lt. destruct (Pos.compare (IndexedMreg.index mr) (IndexedMreg.index mr')) eqn:C.
      elim H. apply IndexedMreg.index_inj. apply Pos.compare_eq_iff. auto.
      auto. 
      rewrite Pos.compare_antisym. rewrite C. auto. 
    - destruct (OrderedSlot.compare sl sl'); auto.
      destruct H. contradiction. 
      destruct H.
      right; right; split; auto. left; omega. 
      left; right; split; auto.
      assert (EITHER: typesize ty' = 1 /\ OrderedTyp.lt ty' Tany64 \/ typesize ty' = 2).
      { destruct ty'; compute; auto. }
      destruct (zlt ofs' (ofs - 1)). left; auto.
      destruct EITHER as [[P Q] | P].
      right; split; auto. omega.
      left; omega. 
  Qed.

End OrderedLoc.

