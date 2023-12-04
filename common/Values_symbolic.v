
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

(** This module defines the type of symbolic expressions that is used in the
  dynamic semantics of all our intermediate languages. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Values_symbolictype.
Require Import NormaliseSpec.
Require Import Normalise.
Require Import IntFacts.
Require Import ExprEval.

Ltac destr_and :=
  match goal with
      H: ?A /\ ?B |- _ => 
      let a1 := fresh in
      let a2 := fresh in
      destruct H as [a1 a2];
        try destr_and a1; try destr_and a2
    | H: exists _, _ |- _ =>
      let a1 := fresh in
      let a2 := fresh in
      destruct H as [a1 a2];
        try destr_and a2
    | H: let _ := ?A in ?B |- _ =>
      destruct A; try destr_and H
                      
    | H: _ |- _ => idtac
  end.

(** [same_eval] states that two symbolic expressions are equivalent if they have
    the same type, and they evaluate identically in any given environment *)

Definition same_eval (v1 v2: expr_sym) : Prop :=
  forall alloc em,
    eSexpr alloc em v1 = eSexpr alloc em v2.

Lemma same_eval_sym:
  forall v1 v2,
    same_eval v1 v2 -> same_eval v2 v1.
Proof.
  red; intros v1 v2 A alloc em; rewrite A; auto.
Qed.

Lemma same_eval_refl:
  forall v,
    same_eval v v.
Proof.
  red; intros; auto. 
Qed.

Lemma same_eval_trans:
  forall v1 v2 v3,
    same_eval v1 v2 ->
    same_eval v2 v3 ->
    same_eval v1 v3.
Proof.
  red; intros v1 v2 v3 A B alloc em.
  rewrite A; rewrite B; auto.
Qed.

Instance same_eval_equi : RelationClasses.Equivalence same_eval :=
  RelationClasses.Build_Equivalence  _ _
                                     (same_eval_refl)
                                     (same_eval_sym)
                                     (same_eval_trans).

Lemma norm_eq:
  forall e e' bound align
    (SE: same_eval_on (compat Int.max_unsigned bound align) e e'),
    normalise bound align e = normalise bound align e'.
Proof.
  intros.
  eapply norm_eq''; simpl; eauto.
Qed.

(** [Ebinop] and [Eunop] are morphisms for [same_eval].  *)

Lemma binop_same_eval:
  forall x x' y y' op t t',
    same_eval x x' -> same_eval y y' ->
    same_eval (Ebinop op t t' x y)
      (Ebinop op t t' x' y').
Proof.
  intros x x' y y' op t t' A B alloc em.
  simpl. rewrite A; rewrite B. auto.
Qed.

Lemma unop_same_eval:
  forall x x' op t ,
    same_eval x x' -> 
    same_eval (Eunop op t x) (Eunop op t  x').
Proof.
  intros x x' op t A alloc em ;
  simpl; rewrite A; auto.
Qed.

Definition conserves_same_eval (f: expr_sym -> expr_sym -> option expr_sym) : Prop :=
  forall a b a1 b1,
    same_eval a b ->
    same_eval a1 b1 ->
    match f a a1, f b b1 with
        Some c, Some d => same_eval c d
      | None, None => True
      | _ , _ => False
    end.

Ltac se_rew :=
  repeat ((apply unop_same_eval; simpl; auto)
            ||
            (apply binop_same_eval; simpl; eauto)
            || reflexivity || auto).


Lemma list_forall2_same_eval_refl:
  forall l,
    list_forall2 same_eval l l.
Proof.
  induction l; simpl; intros; constructor; auto.
  reflexivity.
Qed.

Lemma list_forall2_same_eval_sym:
  forall l1 l2,
    list_forall2 same_eval l1 l2 ->
    list_forall2 same_eval l2 l1.
Proof.
  induction 1; simpl; intros; constructor; auto.
  symmetry; auto.
Qed.

Lemma list_forall2_same_eval_trans:
  forall l1 l2 l3,
    list_forall2 same_eval l1 l2 ->
    list_forall2 same_eval l2 l3 ->
    list_forall2 same_eval l1 l3.
Proof.
  induction l1; simpl; intros.
  - inv H.  inv H0; constructor; auto.
  - inv H. inv H0.
    constructor; auto.
    rewrite H3; auto.
    eapply IHl1; eauto.
Qed.

Instance lf2_se_inst: RelationClasses.Equivalence (list_forall2 same_eval).
Proof.
  constructor; red; intros.
  apply list_forall2_same_eval_refl.
  apply list_forall2_same_eval_sym; auto.
  eapply list_forall2_same_eval_trans; eauto.
Qed.

(** * Operations over values *)

(** The module [Val] defines a number of arithmetic and logical operations over
  type [expr_sym]. These operations are generalisations of the operations on
  values and build symbolic expressions. *)

Module Val.

  Hint Resolve Val.eq_val_dec.
  Hint Resolve eq_nat_dec.
  Hint Resolve Z_eq_dec.
  Hint Resolve Int.eq_dec.
  Hint Resolve typ_eq.
  Hint Resolve se_signedness_eq_dec.
  Hint Resolve comp_eq_dec.


  Definition has_type (v: expr_sym) (t: styp) : Prop :=
    wt_expr v t.

  Fixpoint has_type_list (vl: list expr_sym) (tl: list styp) {struct vl} : Prop :=
    match vl, tl with
      | nil, nil => True
      | v1 :: vs, t1 :: ts => has_type v1 t1 /\ has_type_list vs ts
      | _, _ => False
    end.

  Definition has_opttype (v: expr_sym) (ot: option styp) : Prop :=
    match ot with
      | None => False
      | Some t => has_type v t
    end.

  (** Truth values.  Pointers and non-zero integers are treated as [True].
  The integer 0 (also used to represent the null pointer) is [False].
  [Vundef] and floats are neither true nor false. *)

  Inductive bool_of_val: expr_sym -> bool -> Prop :=
  | bool_of_expr_val : forall v b, Val.bool_of_val v b -> bool_of_val (Eval v) b
  .

  (** Arithmetic operations *)

  Definition neg (v: expr_sym) : expr_sym :=
    Eunop OpNeg Tint v.

  Definition negf (v: expr_sym) : expr_sym :=
    Eunop OpNeg Tfloat v.

  Definition negfs (v: expr_sym) : expr_sym :=
    Eunop OpNeg Tsingle v.

  Definition absf (v: expr_sym) : expr_sym :=
    Eunop OpAbsf Tfloat v.

  Definition absfs (v: expr_sym) : expr_sym :=
    Eunop OpAbsf Tsingle v.

  Definition intoffloat (v: expr_sym) : expr_sym :=
    Eunop (OpConvert SESigned (Tint,SESigned)) Tfloat  v.

  Definition intuoffloat (v: expr_sym) : expr_sym :=
    Eunop (OpConvert SESigned (Tint,SEUnsigned)) Tfloat  v.

  Definition floatofint (v: expr_sym) :  expr_sym :=
    Eunop (OpConvert SESigned (Tfloat,SESigned)) Tint  v.

  Definition floatofintu (v: expr_sym) : expr_sym :=
    Eunop (OpConvert SEUnsigned (Tfloat,SESigned)) Tint  v.

  Definition intofsingle (v: expr_sym) : expr_sym :=
    Eunop (OpConvert SESigned (Tint, SESigned)) Tsingle v.
  Definition intuofsingle (v: expr_sym) : expr_sym :=
    Eunop (OpConvert SESigned (Tint, SEUnsigned)) Tsingle v.

  Definition singleofint (v: expr_sym) : expr_sym :=
    Eunop (OpConvert SESigned (Tsingle, SESigned)) Tint v.
  Definition singleofintu (v: expr_sym) : expr_sym :=
    Eunop (OpConvert SEUnsigned (Tsingle, SESigned)) Tint v.

  Definition singleoflong (v: expr_sym) : expr_sym :=
    Eunop (OpConvert SESigned (Tsingle, SESigned)) Tlong v.
  Definition singleoflongu (v: expr_sym) : expr_sym :=
    Eunop (OpConvert SEUnsigned (Tsingle, SESigned)) Tlong v.

  Definition negint (v: expr_sym) : expr_sym :=
    Eunop OpNeg Tint v.

  Definition notint (v: expr_sym) : expr_sym :=
    Eunop OpNot Tint v.

  Definition of_bool (b: bool): expr_sym :=
    (Eval (Val.of_bool b)).

  Definition boolval (v: expr_sym) : expr_sym :=
    Eunop OpBoolval Tint v.

  Definition notbool (v: expr_sym) : expr_sym :=
    Eunop OpNotbool Tint v.

  Definition zero_ext (nbits: Z) (v: expr_sym) : expr_sym :=
    Eunop (OpZeroext nbits) Tint v.

  Definition sign_ext (nbits: Z) (v: expr_sym) : expr_sym :=
    Eunop (OpSignext nbits) Tint v.

  Definition singleoffloat (v: expr_sym) : expr_sym :=
    Eunop (OpConvert  SESigned (Tsingle, SESigned)) Tfloat  v.

  Definition floatofsingle (v: expr_sym) : expr_sym :=
    Eunop (OpConvert  SESigned (Tfloat, SESigned)) Tsingle  v.

  Definition add (v1 v2: expr_sym): expr_sym :=
    Ebinop OpAdd Tint Tint v1 v2.

  Definition sub (v1 v2: expr_sym): expr_sym :=
    Ebinop OpSub Tint Tint v1 v2.

  Definition mul (v1 v2: expr_sym): expr_sym :=
    Ebinop OpMul Tint Tint v1 v2.

  Definition mulhs (v1 v2: expr_sym): expr_sym :=
    Ebinop (OpMulh SESigned) Tint Tint v1 v2.

  Definition mulhu (v1 v2: expr_sym): expr_sym :=
    Ebinop (OpMulh SEUnsigned) Tint Tint v1 v2.

  Definition divs (v1 v2: expr_sym): expr_sym :=
    Ebinop (OpDiv SESigned) Tint Tint v1 v2.

  Definition mods (v1 v2: expr_sym):  expr_sym :=
    Ebinop (OpMod SESigned) Tint Tint v1 v2.

  Definition divu (v1 v2: expr_sym): expr_sym :=
    Ebinop (OpDiv SEUnsigned) Tint Tint v1 v2.

  Definition modu (v1 v2: expr_sym): expr_sym :=
    Ebinop (OpMod SEUnsigned) Tint Tint v1 v2.

  Definition add_carry (v1 v2 cin: expr_sym) : expr_sym :=
    Ebinop OpAdd Tint  Tint (Ebinop OpAdd Tint  Tint v1 v2) cin.

  Definition and (v1 v2: expr_sym): expr_sym :=
    Ebinop OpAnd Tint Tint v1 v2.

  Definition or (v1 v2: expr_sym): expr_sym :=
    Ebinop OpOr Tint Tint v1 v2.

  Definition xor (v1 v2: expr_sym): expr_sym :=
    Ebinop OpXor Tint Tint v1 v2.

  Definition shr (v1 v2: expr_sym): expr_sym :=
    Ebinop (OpShr SESigned) Tint Tint v1 v2.

  Definition shl (v1 v2: expr_sym): expr_sym :=
    Ebinop OpShl Tint Tint v1 v2.

  Definition shr_carry (v1 v2: expr_sym): expr_sym :=
    Ebinop OpShr_carry Tint Tint v1 v2.

  Definition shrx (v1 v2: expr_sym): expr_sym :=
    Ebinop (OpShrx) Tint Tint v1 v2.

  Definition shru (v1 v2: expr_sym): expr_sym :=
    Ebinop (OpShr SEUnsigned) Tint Tint v1 v2.

  Definition rolm (v: expr_sym) (amount mask: int): expr_sym :=
    Eunop (OpRolm amount mask) Tint v.

  Definition ror (v1 v2: expr_sym): expr_sym :=
    (Ebinop OpRor Tint Tint) v1 v2.

  Definition addf (v1 v2: expr_sym): expr_sym :=
    (Ebinop OpAdd Tfloat Tfloat) v1 v2.

  Definition subf (v1 v2: expr_sym): expr_sym :=
    (Ebinop OpSub Tfloat Tfloat) v1 v2.

  Definition mulf (v1 v2: expr_sym): expr_sym :=
    (Ebinop OpMul Tfloat Tfloat) v1 v2.

  Definition divf (v1 v2: expr_sym): expr_sym :=
    (Ebinop (OpDiv SESigned) Tfloat Tfloat) v1 v2.

  Definition addfs (v1 v2: expr_sym): expr_sym :=
    (Ebinop OpAdd Tsingle Tsingle) v1 v2.

  Definition subfs (v1 v2: expr_sym): expr_sym :=
    (Ebinop OpSub Tsingle Tsingle) v1 v2.

  Definition mulfs (v1 v2: expr_sym): expr_sym :=
    (Ebinop OpMul Tsingle Tsingle) v1 v2.

  Definition divfs (v1 v2: expr_sym): expr_sym :=
    (Ebinop (OpDiv SESigned) Tsingle Tsingle) v1 v2.

  Definition floatofwords (v1 v2: expr_sym): expr_sym :=
    (Ebinop OpFloatofwords Tint Tint) v1 v2.

  (** Operations on 64-bit integers *)

  Definition longofwords (v1 v2: expr_sym): expr_sym :=
    (Ebinop OpLongofwords Tint Tint) v1 v2.

  Definition loword (v1 : expr_sym): expr_sym :=
    (Eunop OpLoword Tlong) v1.

  Definition hiword (v1 : expr_sym): expr_sym :=
    (Eunop OpHiword Tlong) v1 .

  Definition negl (v: expr_sym) : expr_sym :=
    (Eunop OpNeg Tlong) v.

  Definition notl (v: expr_sym) : expr_sym :=
    (Eunop OpNot Tlong) v.

  Definition longofint (v: expr_sym) : expr_sym :=
    (Eunop (OpConvert SESigned (Tlong,SESigned)) Tint ) v.

  Definition longofsingle (v: expr_sym) : expr_sym :=
    (Eunop (OpConvert SESigned (Tlong,SESigned)) Tsingle ) v.

  Definition longuofsingle (v: expr_sym) : expr_sym :=
    (Eunop (OpConvert SESigned (Tlong,SEUnsigned)) Tsingle ) v.

  Definition longofintu (v: expr_sym) : expr_sym :=
    (Eunop (OpConvert SEUnsigned (Tlong,SESigned)) Tint ) v.

  Definition longoffloat (v: expr_sym) :  expr_sym :=
    (fun x =>  (Eunop (OpConvert SESigned (Tlong,SESigned)) Tfloat  x)) v.

  Definition longuoffloat (v: expr_sym) : expr_sym :=
    (fun x =>  (Eunop (OpConvert SESigned (Tlong,SEUnsigned)) Tfloat  x)) v.

  Definition floatoflong (v: expr_sym) :  expr_sym :=
    (fun x =>  (Eunop (OpConvert SESigned (Tfloat,SESigned)) Tlong   x)) v.

  Definition floatoflongu (v: expr_sym) : expr_sym :=
    (fun x => (Eunop (OpConvert SEUnsigned (Tfloat,SESigned)) Tlong   x)) v.

  Definition addl (v1 v2: expr_sym) : expr_sym :=
    (Ebinop OpAdd Tlong Tlong) v1 v2.

  Definition subl (v1 v2: expr_sym) : expr_sym :=
    (Ebinop OpSub Tlong Tlong) v1 v2.

  Definition mull (v1 v2: expr_sym) : expr_sym :=
    (Ebinop OpMul Tlong Tlong) v1 v2.

  Definition mull' (v1 v2: expr_sym) : expr_sym :=
    (Ebinop OpMull' Tint Tint) v1 v2.

  Definition divls (v1 v2: expr_sym): expr_sym :=
    (fun x y => (Ebinop (OpDiv SESigned) Tlong Tlong x y)) v1 v2.

  Definition modls (v1 v2: expr_sym): expr_sym :=
    (fun x y => (Ebinop (OpMod SESigned) Tlong Tlong x y)) v1 v2.

  Definition divlu (v1 v2: expr_sym):  expr_sym :=
    (fun x y =>  (Ebinop (OpDiv SEUnsigned) Tlong Tlong x y)) v1 v2.

  Definition modlu (v1 v2: expr_sym):  expr_sym :=
    (fun x y =>  (Ebinop (OpMod SEUnsigned) Tlong Tlong x y)) v1 v2.

  Definition andl (v1 v2: expr_sym): expr_sym :=
    (Ebinop OpAnd Tlong Tlong) v1 v2.

  Definition orl (v1 v2: expr_sym): expr_sym :=
    (Ebinop OpOr Tlong Tlong) v1 v2.

  Definition xorl (v1 v2: expr_sym): expr_sym :=
    (Ebinop OpXor Tlong Tlong) v1 v2.

  Definition shll (v1 v2: expr_sym): expr_sym :=
    (Ebinop OpShl Tlong Tint) v1 v2.

  Definition shrl (v1 v2: expr_sym): expr_sym :=
    (Ebinop (OpShr SESigned) Tlong Tint) v1 v2.

  Definition shrlu (v1 v2: expr_sym): expr_sym :=
    (Ebinop (OpShr SEUnsigned) Tlong Tint) v1 v2.

  Definition bitsofsingle (v1 : expr_sym) : expr_sym :=
    Eunop (OpBitsofsingle) Tsingle v1.

  Definition bitsofdouble (v1 : expr_sym) : expr_sym :=
    Eunop (OpBitsofdouble) Tfloat v1.

  
  (** Comparisons *)

  Section COMPARISONS.

    (* Variable valid_ptr: block -> Z -> bool. *)
    (* Let weak_valid_ptr (b: block) (ofs: Z) := valid_ptr b ofs || valid_ptr b (ofs - 1). *)

    Definition cmp_bool (c: comparison) (v1 v2: expr_sym): expr_sym :=
      (Ebinop (OpCmp SESigned c) Tint Tint v1 v2).

    Definition cmp_different_blocks (c: comparison): option bool :=
      match c with
        | Ceq => Some false
        | Cne => Some true
        | _   => None
      end.

    Definition cmpu_bool (c: comparison) (v1 v2: expr_sym): expr_sym :=
      (Ebinop (OpCmp SEUnsigned c) Tint Tint v1 v2).

    Definition cmpf_bool (c: comparison) (v1 v2: expr_sym): expr_sym :=
      (Ebinop (OpCmp SESigned c) Tfloat Tfloat v1 v2).

    Definition cmpfs_bool (c: comparison) (v1 v2: expr_sym): expr_sym :=
      (Ebinop (OpCmp SESigned c) Tsingle Tsingle v1 v2).

    Definition cmpl_bool (c: comparison) (v1 v2: expr_sym): expr_sym :=
      (Ebinop (OpCmp SESigned c) Tlong Tlong v1 v2).

    Definition cmplu_bool (c: comparison) (v1 v2: expr_sym): expr_sym :=
      (Ebinop (OpCmp SEUnsigned c) Tlong Tlong v1 v2).

    Definition maskzero_bool (v:expr_sym) (mask: int): expr_sym :=
      Ebinop (OpCmp SEUnsigned Ceq) Tint Tint (Ebinop OpAnd Tint Tint v (Eval (Vint mask)))
             (Eval (Vint Int.zero)).

    Definition cmp (c: comparison) (v1 v2: expr_sym): expr_sym :=
      (cmp_bool c v1 v2).

    Definition cmpu (c: comparison) (v1 v2: expr_sym): expr_sym :=
      (cmpu_bool c v1 v2).

    Definition cmpf (c: comparison) (v1 v2: expr_sym): expr_sym :=
      (cmpf_bool c v1 v2).

    Definition cmpfs (c: comparison) (v1 v2: expr_sym): expr_sym :=
      (cmpfs_bool c v1 v2).

    Definition cmpl (c: comparison) (v1 v2: expr_sym): expr_sym :=
      (cmpl_bool c v1 v2).

    Definition cmplu (c: comparison) (v1 v2: expr_sym): expr_sym :=
      (cmplu_bool c v1 v2).

  End COMPARISONS.

  (** [load_result] reflects the effect of storing a value with a given
  memory chunk, then reading it back with the same chunk.  Depending
  on the chunk and the type of the value, some normalization occurs.
  For instance, consider storing the integer value [0xFFF] on 1 byte
  at a given address, and reading it back.  If it is read back with
  chunk [Mint8unsigned], zero-extension must be performed, resulting
  in [0xFF].  If it is read back as a [Mint8signed], sign-extension is
  performed and [0xFFFFFFFF] is returned. *)

  Definition load_result (chunk: memory_chunk) (v: expr_sym) : expr_sym :=
  match chunk with
    | Mint8signed => sign_ext 8 v
    | Mint8unsigned => zero_ext 8 v
    | Mint16signed => sign_ext 16 v
    | Mint16unsigned => zero_ext 16 v
    | Mint32 => sign_ext 32 v
    | Mint64 => Eunop (OpSignext 64) Tlong v
    | Mfloat32 => Eunop (OpConvert SESigned (Tsingle, SESigned)) Tsingle v
    | Mfloat64 => Eunop (OpConvert SESigned (Tfloat, SESigned)) Tfloat v
    | Many32 => if wt_expr_dec v Tint then v
               else if wt_expr_dec v Tsingle then v
                    else Eval Vundef
    | Many64 => v
  end.

  Lemma load_result_type:
    forall chunk v,
      has_type v (styp_of_ast (type_of_chunk chunk)) ->
      has_type (load_result chunk v) (styp_of_ast (type_of_chunk chunk)).
  Proof.
    intros.
    unfold has_type in *.
    des v; try (des (s:sval)); des chunk; try constructor.
    repeat destr.
    repeat destr.
    repeat destr.
  Qed.
 
  (** Theorems on arithmetic operations. *)

  Theorem cast8unsigned_and:
    forall x,
      same_eval (zero_ext 8 x) (and x (Eval (Vint(Int.repr 255)))).
  Proof.
    red; intros; simpl; seval.
    rewrite Int.zero_ext_and; auto; omega.
  Qed.

  Theorem cast16unsigned_and:
    forall x,
      same_eval (zero_ext 16 x) (and x (Eval (Vint(Int.repr 65535)))).
  Proof.
    red; intros; simpl; seval.
    rewrite Int.zero_ext_and; auto; omega.
  Qed.

  Theorem notbool_negb_1:
    forall b, same_eval (of_bool (negb b)) (notbool (of_bool b)).
  Proof.
    unfold notbool. 
    red; simpl; intros; seval; des b. 
  Qed.

  Theorem notbool_negb_2:
    forall b, same_eval (of_bool b) (notbool (of_bool (negb b))).
  Proof.
    unfold notbool. 
    red; simpl; intros; seval; des b. 
  Qed.

  Theorem notbool_idem2:
    forall b, same_eval (notbool(notbool(of_bool b))) (of_bool b).
  Proof.
    unfold notbool. 
    red; simpl; intros; seval; des b. 
  Qed.
    
  Theorem notbool_idem3:
    forall x, same_eval (notbool(notbool(notbool x))) (notbool x).
  Proof.
    unfold notbool. 
    red; simpl; intros; seval.
    des (Int.eq i Int.zero).
  Qed.

  Theorem add_commut: forall x y, same_eval (add x y) (add y x).
  Proof.
    unfold add; red; simpl; intros; seval; sint.
  Qed.

  Theorem add_assoc: forall x y z, same_eval (add (add x y) z) (add x (add y z)).
  Proof.
    unfold add; red; simpl; intros; seval; sint.
  Qed.

  Theorem add_permut: forall x y z, same_eval (add x (add y z)) (add y (add x z)).
  Proof.
    unfold add; red; simpl; intros; seval; sint.
    apply Int.add_permut.
  Qed.

  Theorem add_permut_4:
    forall x y z t, same_eval (add (add x y) (add z t)) (add (add x z) (add y t)).
  Proof.
    red; simpl; intros; seval; sint;
    match goal with
      | |- Int.add ?i0 (Int.add ?i1 ?i2) = Int.add ?i1 (Int.add ?i0 ?i2) =>
        rewrite (Int.add_permut i0 i1 i2); auto
      | |- Int.add ?i1 (Int.add ?i ?i0) = Int.add ?i0 (Int.add ?i ?i1) =>
        rewrite (Int.add_commut i i0); rewrite (Int.add_permut i1 i0 i);
        rewrite (Int.add_commut i1 i); auto
      | |- Int.add ?i2 (Int.add ?i ?i0) = Int.add ?i (Int.add ?i0 ?i2) =>
        rewrite (Int.add_commut i0 i2); rewrite (Int.add_permut i2 i i0); auto
      | |-    Int.add ?i (Int.add ?i1 ?i2) = Int.add ?i2 (Int.add ?i ?i1) =>
        rewrite (Int.add_permut i2 i i1); rewrite (Int.add_commut i2 i1); auto
    end.
  Qed.


  (** We generalize the injection relation so that it specializes undefined
  values, labelled with locations, into concrete bytes. The injection is
  parameterised by an extra parameter of type [partial_undef_allocation] which
  specifies how undefined values are specialized. Specialization is then
  performed by function [subst].*)
  
  Definition partial_undef_allocation := block -> int -> option byte.

  Fixpoint subst (m:partial_undef_allocation) (e: expr_sym) : expr_sym :=
    match e with
      | Eundef b i => 
        match m b i with
            Some byte => Eval (Vint (Int.repr (Byte.unsigned byte)))
          | _ => e
        end
      | Eval ev => Eval ev
      | Eunop u t e => Eunop u t (subst m e)
      | Ebinop b t r e f => Ebinop b t r (subst m e) (subst m f)
    end.

  Lemma subst_id :
    forall e, subst (fun _ _ => None) e = e.
  Proof.
    induction e; simpl; eauto.
    rewrite IHe; auto.
    rewrite IHe1; rewrite IHe2; auto.
  Qed.
  

  (** The evaluation of an expression with substitution [m] is equal to the
  evaluation of the same expression in an enriched environment, as computed by
  [aug_em].  *)
  
  Definition aug_em (em : block -> int -> byte) (m : partial_undef_allocation) :=
    fun b i =>
      match m b i with
          Some byte => byte
        | _ => em b i
      end.



Lemma subst_type:
  forall m e t,
    wt_expr e t <->
    wt_expr (Val.subst m e) t.
Proof.
  induction e; simpl; intros; try tauto.
  - destr; subst; simpl; auto. des t.
  - destr. rewrite <- IHe; auto. rewrite IHe; auto.
  - destr. rewrite <- IHe1; auto. rewrite <- IHe2; auto.
    rewrite  IHe1; auto. rewrite  IHe2; auto.
Qed.
  

  
  Lemma eSexpr_subst_em:
    forall v alloc em m,
      eSexpr alloc em (subst m v) = 
      eSexpr alloc (aug_em em m) v.
  Proof.
    unfold aug_em; induction v; simpl; intros; auto.
    - destr. 
    - rewrite IHv. auto.
    - rewrite IHv1. rewrite IHv2.
      auto.
  Qed.
  

  Definition option_map2 { A B C} (f : A -> B -> C) (a: option A) (b: option B) : option C :=
    match a, b with
        Some aa, Some bb => Some (f aa bb)
      | _ , _ => None
    end.

  (** The function [apply_inj] injects a symbolic expression [v1] syntactically,
  where pointers and undefined labels are injected in the same sense as in
  [val_inject]. This fails when [e] mentions a block that is not injected by [f].*)
  
  Definition inj_undef (f:meminj) (b:block) (i:int) : option expr_sym :=
    match f b with
        Some (b',delta) => Some (Eundef b' (Int.add i (Int.repr delta)))
      | _ => None
    end.

  Definition inj_ptr (f:meminj) (b:block) (i:int) : option expr_sym :=
    match f b with
        Some (b',delta) => Some (Eval (Vptr b' (Int.add i (Int.repr delta))))
      | _ => None
    end.

  Fixpoint apply_inj (f:meminj) (v1: expr_sym) : option expr_sym :=
    match v1 with
        Eundef b i => inj_undef f b i
      | Eval v =>
        match v with
          | Vptr b i => inj_ptr f b i
          | _ => Some (Eval v)
        end
      | Eunop u t e => option_map (Eunop u t) (apply_inj f e)
      | Ebinop b t1 t2 e1 e2 => option_map2 (Ebinop b t1 t2) (apply_inj f e1) (apply_inj f e2)
    end.

  (** [expr_inject] is the composition of [apply_inj] and [subst]. *)
  Record expr_inject' (* m *) f e1 e2 : Prop :=
    mk_expr_inject {
        inj_ok: apply_inj f (* (subst m e1) *) e1 = Some e2
      }.

  Definition expr_inject (*m: partial_undef_allocation*) (f:meminj) (v1 v2: expr_sym) : Prop :=
    expr_inject' f v1 v2.

      
  
Lemma ai_type:
  forall f e1 e2 t,
    apply_inj f e1 = Some e2 ->
    (wt_expr e1 t <->
     wt_expr e2 t).
Proof.
  split; revert e1 e2 t H.
  {
    induction e1; simpl; intros e2 t EI WT.
  - des v; inv EI; simpl; des t.
    unfold Val.inj_ptr in H0; des (f b); des p.
    inv H0; simpl; auto.
  - inv EI.
    unfold Val.inj_undef in H0.
    des (f b); des p; inv H0; simpl; auto.
  - destr_and.
    inv EI.
    des (Val.apply_inj f e1). inv H2. destr.
    apply IHe1; auto.
  - repeat destr_and.
    inv EI.
    des (Val.apply_inj f e1_1).
    des (Val.apply_inj f e1_2).
    inv H3; destr. 
    apply IHe1_1; auto.
    apply IHe1_2; auto.
  }
    {
    induction e1; simpl; intros e2 t EI WT.
  - des v; inv EI; simpl; des t;
    unfold Val.inj_ptr in H0; des (f b); des p;
    inv H0; simpl; auto.
  - inv EI.
    unfold Val.inj_undef in H0.
    des (f b); des p; inv H0; simpl; auto.
  - destr_and.
    des (Val.apply_inj f e1); inv EI; destr.
    eapply IHe1; eauto.
  - repeat destr_and.
    des (Val.apply_inj f e1_1);
    des (Val.apply_inj f e1_2); inv EI; destr.
    eapply IHe1_1; eauto.
    eapply IHe1_2; eauto.
  }
Qed.

  
Lemma ei_type:
  forall f e1 e2 t,
    expr_inject f e1 e2 ->
    (wt_expr e1 t <->
     wt_expr e2 t).
Proof.
  intros f e1 e2 t EI.
  inv EI.
  apply ai_type with (t:=t) in inj_ok0; eauto.
Qed.
  
  Inductive expr_list_inject (f:meminj) : list expr_sym -> list expr_sym -> Prop :=
  | expr_nil_inject:
      expr_list_inject f nil nil
  | expr_cons_inject:
      forall v v' vl vl'
        (EI: expr_inject f v v')
        (ELI: expr_list_inject f vl vl'),
        expr_list_inject f (v::vl) (v'::vl').

  Hint Resolve expr_nil_inject expr_cons_inject.

  (* Definition inj_m (f: meminj) (m m': partial_undef_allocation) := *)
  (*   fun b i => *)
  (*     match m b i with *)
  (*         Some x => Some x *)
  (*       | None =>  *)
  (*         match f b with *)
  (*             Some (b', delta) => m' b' (Int.add i (Int.repr delta)) *)
  (*           | None => None *)
  (*         end *)
  (*     end. *)

  (* Lemma subst_inj_m: *)
  (*   forall m1 m2 f e, *)
  (*     apply_inj f (subst (inj_m f m1 m2) e) = option_map (subst m2) (apply_inj f (subst m1 e)). *)
  (* Proof. *)
  (*   induction e; simpl; intros. *)
  (*   - des v.  *)
  (*     unfold inj_ptr; simpl. *)
  (*     repeat destr. *)
  (*   - unfold inj_m. repeat destr. des (f b). des p. *)
  (*     unfold inj_undef. rewrite Heqo1. simpl. *)
  (*     rewrite Heqo. auto. *)
  (*     unfold inj_undef. des (f b). des p. *)
  (*     rewrite Heqo. auto. *)
  (*   - rewrite IHe. des (apply_inj f (subst m1 e)). *)
  (*   - rewrite IHe1. rewrite IHe2. des (apply_inj f (subst m1 e1)). *)
  (*     des (apply_inj f (subst m1 e2)). *)
  (* Qed. *)

  Section EXPR_INJ_OPS.
    (** This sections states that unary/binary operations are morphisms for
    [expr_inject], and states some specializations of it.  *)
    
    Variable f : meminj.
    (* Variable m : partial_undef_allocation. *)

    Lemma expr_inject_unop:
      forall f u t e1 e2,
        expr_inject f e1 e2 ->
        expr_inject f (Eunop u t e1) (Eunop u t e2).
    Proof.
      intros; inv H; constructor; simpl.
      rewrite inj_ok0; simpl; auto.
    Qed.

    Lemma expr_inject_binop:
      forall f b t1 t2 e1 e2 e1' e2',
        expr_inject f e1 e2 ->
        expr_inject f e1' e2' ->
        expr_inject f (Ebinop b t1 t2 e1 e1') (Ebinop b t1 t2 e2 e2').
    Proof.
      intros; inv H; inv H0; econstructor; simpl.
      rewrite inj_ok0; simpl; auto.
      rewrite inj_ok1; simpl ; auto.
    Qed.

    Lemma expr_load_result_inject':
      forall chunk v1 v2,
        expr_inject f v1 v2 ->
        expr_inject f (load_result chunk v1) (load_result chunk v2).
    Proof.
      intros. 
      des chunk;
        unfold sign_ext, zero_ext;
        try apply expr_inject_unop; auto.
      repeat destr.
      inv H.
      erewrite ai_type with ( e2:= v2) in w; eauto; congruence.
      inv H. erewrite ai_type with ( e2:= v2) in w; eauto; congruence.
      inv H. erewrite <- ai_type with ( e1:= v1) in w; eauto; congruence.
      inv H. erewrite <- ai_type with ( e1:= v1) in w; eauto; congruence.
      constructor; auto.
    Qed.

    Remark expr_add_inject:
      forall v1 v1' v2 v2',
        expr_inject f v1 v1' ->
        expr_inject f v2 v2' ->
        expr_inject f (add v1 v2) (add v1' v2').
    Proof.
      unfold add.
      intros. apply expr_inject_binop; auto.
    Qed.

    Remark expr_sub_inject:
      forall  v1 v1' v2 v2',
        expr_inject f v1 v1' ->
        expr_inject f v2 v2' ->
        expr_inject f (sub v1 v2) (sub v1' v2').
    Proof.
      intros. unfold sub.
      apply expr_inject_binop; auto.
    Qed.

    Lemma expr_cmp_bool_inject:
      forall c v1 v2 v1' v2',
        expr_inject f v1 v1' ->
        expr_inject f v2 v2' ->
        expr_inject f (cmp_bool c v1 v2) (cmp_bool c v1' v2').
    Proof.
      intros. 
      apply expr_inject_binop; auto.
    Qed.

    Lemma expr_cmpu_bool_inject:
      forall c v1 v2 v1' v2',
        expr_inject f v1 v1' ->
        expr_inject f v2 v2' ->
        expr_inject f (cmpu_bool c v1 v2) (cmpu_bool c v1' v2').
    Proof.
      intros. apply expr_inject_binop; auto.
    Qed.

    Lemma expr_longofwords_inject:
      forall v1 v2 v1' v2',
        expr_inject f v1 v1' ->
        expr_inject f v2 v2' ->
        expr_inject f (longofwords v1 v2) (longofwords v1' v2').
    Proof.
      intros. 
      apply expr_inject_binop; auto.
    Qed.

    Lemma expr_loword_inject:
      forall v v', expr_inject f v v' -> expr_inject f (loword v) (loword v').
    Proof.
      intros.
      apply expr_inject_unop; auto.
    Qed.

    Lemma expr_hiword_inject:
      forall v v', expr_inject f v v' -> expr_inject f (hiword v) (hiword v').
    Proof.
      intros.
      apply expr_inject_unop; auto.
    Qed.

  End EXPR_INJ_OPS.

  Definition inj_incr_compat (ei: meminj -> expr_sym -> expr_sym -> Prop) :=
    forall f f' e1 e2
           (INCR: inject_incr f f')
           (EI: ei f e1 e2),
      ei f' e1 e2.

  (** Incremental injections  *)
  
  Lemma apply_inj_incr:
    forall f1 f2 e e',
      inject_incr f1 f2 ->
      apply_inj f1 e = Some e' ->
      apply_inj f2 e = Some e'.
  Proof.
    induction e; simpl; intros.
    - des v.
      specialize (H b).
      unfold inj_ptr in *. 
      des (f1 b); des p.
      erewrite H; eauto.
    - specialize (H b).
      unfold inj_undef in *. 
      des (f1 b); des p.
      erewrite H; eauto.
    - unfold option_map in *. 
      des (apply_inj f1 e).
      erewrite IHe; eauto.
    - unfold option_map2 in *. 
      des (apply_inj f1 e1).
      des (apply_inj f1 e2).
      erewrite IHe1; eauto.
      erewrite IHe2; eauto.
  Qed.

  Lemma apply_inj_incr':
    forall e',
      inj_incr_compat (fun f e _ => apply_inj f e = Some e').
    red; intros. eapply apply_inj_incr; eauto.
  Qed.
  
  Lemma expr_inject_incr:
      inj_incr_compat expr_inject .
  Proof.
    red; unfold inject_incr; intros.
    inv EI.
    econstructor; eauto.
    erewrite apply_inj_incr; eauto. 
  Qed.

  Lemma int_add_repr:
    forall z z1,
      Int.add (Int.repr z) (Int.repr z1) = Int.repr (z + z1).
  Proof.
    intros.
    apply Int.eqm_repr_eq.
    apply Int.eqm_unsigned_repr_r.
    repeat rewrite Int.unsigned_repr_eq.
    unfold Int.eqm.
    apply Int.eqmod_add.
    apply Int.eqmod_sym.
    apply Int.eqmod_mod. vm_compute; auto.
    apply Int.eqmod_sym.
    apply Int.eqmod_mod. vm_compute; auto.
  Qed.

  (** Composing injections.  *)
  
  Lemma apply_inj_compose:
    forall f f' v,
      apply_inj (compose_meminj f f') v =
      match apply_inj f v with
          Some v1 => apply_inj f' v1 
        | _ => None
      end.
  Proof.
    induction v; simpl; intros.
    - destr. unfold compose_meminj, inj_ptr. subst.
      des (f b). des p. unfold inj_ptr. des (f' b0). des p.
      rewrite Int.add_assoc. rewrite int_add_repr. auto.
    - unfold inj_undef, compose_meminj.
      des (f b). des p. unfold inj_undef. des (f' b0). des p.
      rewrite Int.add_assoc. rewrite int_add_repr. auto. 
    - rewrite IHv. destr. 
    - rewrite IHv1. rewrite IHv2.
      destr. destr.
      unfold option_map2.
      destr.
  Qed.

  (** Injecting a concrete memory. The result of [inj_alloc] is a *pre_memory* of [alloc]. *)
  Definition inj_alloc (alloc: block -> int)  (f: meminj) :=
    (fun b => match f b with
                  Some (b', delta) => Int.add (alloc b') (Int.repr delta)
                | None => Int.zero
              end).

  (** We also inject the undef environment for the evaluation function. *)
  Definition inj_em (em: block -> int -> byte) (f:meminj) :=
    (fun b i =>
       match f b with
           Some (b', delta) => em b' (Int.add i (Int.repr delta))
         | None => Byte.zero
       end).

  (** Operations don't introduce pointers ex nihilo  *)

  Section INJ.

    Variable f : meminj.

    Variable alloc: block -> int.
    Variable em : block -> int -> byte.
    
    Lemma apply_inj_eSexpr:
      forall e ef 
             (AI: apply_inj f e = Some ef),
        eSexpr (inj_alloc alloc f) (inj_em em f) e =
        eSexpr alloc em ef.
    Proof.
      induction e; simpl; intros.
      - unfold inj_em, inj_alloc. 
        des v; inv AI; simpl; auto.
        unfold inj_ptr in H0.
        des (f b). des p. inv H0; simpl.
        sint; auto.
      - unfold inj_undef, inj_em in *.  des (f b); des p. inv AI; simpl; auto.
      - des (apply_inj f e). inv AI.
        simpl.
        rewrite (IHe e0); auto. 
      - des (apply_inj f e1); des (apply_inj f e2).
        inv AI. simpl.
        rewrite (IHe1 e); auto.
        rewrite (IHe2 e0); auto.
    Qed.

    Lemma eSexpr_eq_vi:
      forall v v' (inj_ok: forall b i, v = Vptr b i -> f b <> None), 
        (forall alloc em,
           eSexpr (inj_alloc alloc f) (inj_em em f) (Eval v) =
           eSexpr alloc em (Eval v')) ->
        val_inject f v v'.
    Proof.
      des v; des v'; auto;
      try solve [inv H; auto].
      specialize (H (fun _ => Int.sub (Int.add i Int.one) i0) (fun _ _ => Byte.zero)). simpl in H.
      apply inj_vint in H.
      rewrite Int.sub_add_opp in H.
      revert H; sint. rewrite <- (Int.add_commut i0). rewrite Int.add_neg_zero.
      rewrite Int.add_zero.
      replace i with (Int.add i Int.zero) at 1.
      intro.
      apply int_add_eq_l in H. discriminate.
      apply Int.add_zero.
      specialize (H (fun _ => Int.zero) (fun _ _ => Byte.zero));  discriminate.
      specialize (H (fun _ => Int.zero) (fun _ _ => Byte.zero));  discriminate.
      specialize (H (fun _ => Int.zero) (fun _ _ => Byte.zero));  discriminate.
      specialize (H0 (fun _ => Int.zero) (fun _ _ => Byte.zero)); discriminate.
      {
        unfold inj_alloc in H0.
        des (f b). des p.
        - specialize (H0 (fun _ => Int.sub (Int.add i0 Int.one) (Int.add i (Int.repr z))) Normalise.dummy_em).
          apply inj_vint in H0.
          rewrite Int.sub_add_opp in H0.
          revert H0; sint. rewrite <- (Int.add_commut i). rewrite (Int.add_commut (Int.neg _)). rewrite Int.add_neg_zero.
          rewrite Int.add_zero.
          replace i0 with (Int.add i0 Int.zero) at 2.
          intro.
          (* rewrite ! (Int.add_commut i0) in H0. *)
          apply int_add_eq_l in H0. discriminate.
          apply Int.add_zero.
        - eapply inj_ok0 in Heqo; eauto. destruct Heqo. 
      }
      
      specialize (H0 (fun _ => Int.zero) (fun _ _ => Byte.zero)); discriminate.
      specialize (H0 (fun _ => Int.zero) (fun _ _ => Byte.zero)); discriminate.
      specialize (H0 (fun _ => Int.zero) (fun _ _ => Byte.zero)); discriminate.
      des (f b). des p.
      des (peq b0 b1).
      econstructor; eauto.
      specialize (H0 (fun _ => Int.zero) (fun _ _ => Byte.zero)).
      unfold inj_alloc in H0.
      rewrite Heqo in H0.
      apply inj_vint in H0.
      rewrite ! Int.add_zero_l in H0. rewrite Int.add_commut; auto.
      generalize (H0 (fun bb => if peq bb b1 then Int.one else Int.zero) (fun _ _ => Byte.zero)).
      specialize (H0 (fun bb => if peq bb b1 then Int.zero else Int.one) (fun _ _ => Byte.zero)).
      revert H0.
      unfold inj_alloc.
      rewrite ! Heqo. rewrite ! peq_true. rewrite ! peq_false by auto.
      rewrite ! Int.add_zero_l. sint.
      intros A B. apply inj_vint in A. apply inj_vint in B.
      rewrite A in B.
      contradict B; clear.
      replace (Int.add Int.one (Int.add Int.one i0)) with (Int.add (Int.repr 2) i0).
      replace i0 with (Int.add Int.zero i0) at 2. intro B.
      rewrite <-! (Int.add_commut i0) in B. apply int_add_eq_l in B. discriminate.
      apply Int.add_zero_l. rewrite <- Int.add_assoc. f_equal.

      unfold inj_alloc in H0. rewrite Heqo in H0.
      specialize (H0 (fun _ => Int.sub (Int.add i Int.one) i0) (fun _ _ => Byte.zero)). simpl in H0.
      apply inj_vint in H0.
      rewrite Int.sub_add_opp in H0.
      revert H0; sint. rewrite <- (Int.add_commut i0). rewrite Int.add_neg_zero.
      rewrite Int.add_zero.
      rewrite Int.add_commut.
      intro.
      apply int_add_eq_l in H0. discriminate.
    Qed.

    
    Lemma expr_inject_compose:
      forall f f' v1 v2 v3,
        expr_inject' f  v1 v2 ->
        expr_inject' f' v2 v3 ->
        expr_inject' (compose_meminj f f') v1 v3.
    Proof.
      intros.
      inv H; inv H0.
      generalize inj_ok0; intro inj_ok2.
      constructor.
      rewrite apply_inj_compose.
      rewrite inj_ok0; simpl. 
      auto.
    Qed.

    Lemma apply_inj_id:
      forall e,
        apply_inj inject_id e = Some e.
    Proof.
      induction e; destr.
      - des v.
        unfold inj_ptr. simpl.
        rewrite Int.add_zero; auto.
      - unfold inj_undef; simpl.
        rewrite Int.add_zero; auto.
      - rewrite IHe; auto.
      - rewrite IHe1; rewrite IHe2; auto.
    Qed.

    Lemma ei_id:
      forall e,
        expr_inject inject_id e e.
    Proof.
      intros.
      econstructor; simpl; eauto; simpl; try tauto.
      rewrite apply_inj_id; auto.
    Qed.

  End INJ.
    
  Definition lessdef (e1 e2: expr_sym) : Prop :=
    forall alloc em, Val.lessdef (eSexpr alloc em e1) (eSexpr alloc em e2).

  Lemma lessdef_refl:
    forall e,
      lessdef e e.
  Proof.
    intros. constructor.
  Qed.

  Lemma lessdef_sym:
    forall v v',
      Val.lessdef (Eval v) v' ->
      v <> Vundef ->
      Val.lessdef v' (Eval v).
  Proof.
    red; intros.
    specialize (H alloc em). simpl in *.
    des v; seval; inv H; auto. 
  Qed.
  

  
  Remark val_lessdef_normalize:
    forall v v' ty,
      (Val.has_type v (styp_of_ast ty) \/ ~ exists t, Val.has_type v t) ->
      Val.lessdef v v' ->
      Val.lessdef v (Val.load_result (chunk_of_type ty) v').
  Proof.
    intros. red; intros. specialize (H0 alloc em).
    inv H0; auto. simpl.
    destruct H. 
    - generalize (expr_type _ _ H alloc em).
      generalize (expr_type _ _ H alloc em). rewrite H3 at 1.
      des ty; try rewrite <- H3; seval; auto;
      try (      repeat (revert Heqv1; destr)).
      rewrite Int.sign_ext_above; auto; vm_compute; destr.
      rewrite Int64.sign_ext_above; auto; vm_compute; destr.
      generalize (expr_type' _ _ _ _ H0 n). congruence.
      apply Val.lessdef_same. congruence.
      generalize (expr_type' _ _ _ _ H0 n). congruence.
    - rewrite nwt_expr_undef; auto.
  Qed.

  Lemma apply_inj_ext:
    forall f f' e,
      (forall b, f b = f' b) ->
      apply_inj f e = apply_inj f' e.
  Proof.
    induction e; simpl; intros.
    des v. unfold inj_ptr; rewrite H; auto.
    unfold inj_undef; rewrite H; auto.
    rewrite IHe; auto.
    rewrite IHe1; auto; rewrite IHe2; auto.
  Qed.

  Lemma subst_ext:
    forall m m' e,
      (forall b i,  m b i = m' b i) ->
      subst m e = subst m' e.
  Proof.
    induction e; simpl; intros; auto.
    rewrite H; auto.
    rewrite IHe; auto.
    rewrite IHe1; auto; rewrite IHe2; auto.
  Qed.

  Lemma expr_inject_ext:
    forall f f' a b,
      (forall b, f b = f' b) ->
      expr_inject f a b ->
      expr_inject f' a b.
  Proof.
    intros. inv H0.
    rewrite apply_inj_ext with (f':=f') in inj_ok0; auto.
    econstructor; eauto.
  Qed.
  
  Lemma lessdef_trans:
    forall v1 v2 v3,
      lessdef v1 v2 -> lessdef v2 v3 -> 
      lessdef v1 v3.
  Proof.
    red; intros. unfold lessdef in *.
    eapply Val.lessdef_trans; eauto.
  Qed.

  Inductive lessdef_list: list expr_sym -> list expr_sym -> Prop :=
  | lessdef_list_nil:
      lessdef_list nil nil
  | lessdef_list_cons:
      forall v1 v2 vl1 vl2
        (LD: lessdef v1 v2) (LDL: lessdef_list vl1 vl2),
        lessdef_list (v1 :: vl1) (v2 :: vl2).

  Hint Resolve lessdef_refl lessdef_list_nil lessdef_list_cons.

  Lemma lessdef_list_inv:
    forall vl1 vl2, lessdef_list vl1 vl2 -> 
                      list_forall2 lessdef vl1 vl2.
  Proof.
    induction 1; simpl; constructor; auto.
  Qed.


  
  Lemma lessdef_unop:
    forall v1 v2 u t,
      lessdef v1 v2 ->
      lessdef (Eunop u t v1) (Eunop u t v2).
  Proof.
    red; intros.
    specialize (H alloc em).
    inv H.
    simpl; rewrite H2. constructor.
    simpl; rewrite <- H1; simpl.
    rewrite fun_of_unop_undef; auto.
  Qed.

  Lemma lessdef_binop:
    forall v1 v2 v3 v4 b t1 t2,
      lessdef v1 v2 ->
      lessdef v3 v4 ->
      lessdef (Ebinop b t1 t2 v1 v3) (Ebinop b t1 t2 v2 v4).
  Proof.
    red; intros.
    specialize (H alloc em ).
    specialize (H0 alloc em ).
    simpl.
    inv H. rewrite H3.
    inv H0. rewrite H2. constructor.
    rewrite fun_of_binop_undef_r. constructor.
    rewrite fun_of_binop_undef_l. constructor.
  Qed.
  
  Lemma load_result_lessdef:
    forall chunk v1 v2,
      lessdef v1 v2 -> 
      lessdef (load_result chunk v1) (load_result chunk v2).
  Proof.
    intros.
    des chunk; try apply lessdef_unop; auto.
    repeat destr; try constructor.
    red; intros; specialize (H alloc em); destr.
    generalize (expr_type _ _ w alloc em).
    seval. constructor. inv H.
    rewrite (fun pf => expr_type' alloc em v2 Tint pf n) in H3. congruence.
    rewrite <- H3; auto.
    red; intros; specialize (H alloc em); destr.
    generalize (expr_type _ _ w alloc em).
    seval. constructor. inv H.
    rewrite (fun pf => expr_type' alloc em v2 Tsingle pf n1) in H3. congruence.
    rewrite <- H3; auto.
  Qed.

  Lemma zero_ext_lessdef:
    forall n v1 v2, n > 0 -> lessdef v1 v2 -> lessdef (zero_ext n v1) (zero_ext n v2).
  Proof.
    intros.
    apply lessdef_unop; auto.
  Qed.

  Lemma sign_ext_lessdef:
    forall n v1 v2, n > 0 -> lessdef v1 v2 -> lessdef (sign_ext n v1) (sign_ext n v2).
  Proof.
    intros.
    apply lessdef_unop; auto.
  Qed.

  Lemma singleoffloat_lessdef:
    forall v1 v2, lessdef v1 v2 -> lessdef (singleoffloat v1) (singleoffloat v2).
  Proof.
    intros.
    apply lessdef_unop; auto.
  Qed.

  Lemma add_lessdef:
    forall v1 v1' v2 v2',
      lessdef v1 v1' -> lessdef v2 v2' ->
      lessdef (add v1 v2) (add v1' v2').
  Proof.
    unfold lessdef; intros.
    apply lessdef_binop; auto.
  Qed.

  Lemma cmpu_bool_lessdef:
    forall  c v1 v1' v2 v2',
      lessdef v1 v1' -> lessdef v2 v2' ->
      lessdef (cmpu_bool c v1 v2)
              (cmpu_bool c v1' v2').
  Proof.
    intros.
    apply lessdef_binop; auto.
  Qed.

  Lemma longofwords_lessdef:
    forall v1 v2 v1' v2',
      lessdef v1 v1' -> lessdef v2 v2' -> lessdef (longofwords v1 v2) (longofwords v1' v2').
  Proof.
    unfold lessdef; intros.
    apply lessdef_binop; auto.
  Qed.
  
  Lemma loword_lessdef:
    forall v1 v1' ,
      lessdef v1 v1' -> lessdef (loword v1) (loword v1').
  Proof.
    unfold lessdef; intros.
    apply lessdef_unop; auto.
  Qed.

  Lemma hiword_lessdef:
    forall v1 v1' ,
      lessdef v1 v1' -> lessdef (hiword v1) (hiword v1').
  Proof.
    unfold lessdef; intros.
    apply lessdef_unop; auto.
  Qed.


  Lemma val_hiword_longofwords:
    forall v1 v2, Val.lessdef (Val.hiword (Val.longofwords v1 v2)) v1.
  Proof.
    red; intros; simpl; seval; auto. 
    rewrite Int64.hi_ofwords. auto.
  Qed.

  Lemma val_loword_longofwords:
    forall v1 v2, Val.lessdef (Val.loword (Val.longofwords v1 v2)) v2.
  Proof.
    red; intros; simpl; seval; auto. 
    rewrite Int64.lo_ofwords. auto.
  Qed.

  
End Val.

         


Ltac ldt :=
  repeat match goal with
           | H: Val.lessdef ?a ?b |-
             Val.lessdef ?c (Ebinop ?o ?t ?s ?b ?d) =>
             eapply Val.lessdef_trans with (v2:=Ebinop o t s a d);
               [|apply Val.lessdef_binop; auto]
           | H: Val.lessdef ?a ?b |-
             Val.lessdef ?c (Ebinop ?o ?t ?s ?d ?b) =>
             eapply Val.lessdef_trans with (v2:=Ebinop o t s d a);
               [|apply Val.lessdef_binop; auto]
           | H: Val.lessdef ?a ?b |-
             Val.lessdef ?c (Eunop ?o ?t ?b) =>
             eapply Val.lessdef_trans with (v2:=Eunop o t a);
               [|apply Val.lessdef_unop; auto]
           | H : Val.lessdef ?a ?b |-
             Val.lessdef ?c ?b =>
             eapply Val.lessdef_trans with (v2:=a); eauto
         end.

Ltac ld :=
  repeat match goal with
           | H: Vint _ = Vint _ |- _ => inv H
           | H: Vlong _ = Vlong _ |- _ => inv H
           | H: Vfloat _ = Vfloat _ |- _ => inv H
           | H: Vsingle _ = Vsingle _ |- _ => inv H
           | H: Vptr _ _ = Vptr _ _ |- _ => inv H
           | |- Val.lessdef _ _ =>   red; intros; simpl; seval; try constructor
         end.




Record expr_inject' (f: meminj) (a b: expr_sym) : Prop :=
  mk_ei' {
      a': expr_sym;
      b': expr_sym;
      ei_ld_1: Val.lessdef a a';
      ei_ei: Val.expr_inject f a' b';
      ei_ld_2: Val.lessdef b' b;
      ei_type: forall t, wt_expr b t -> wt_expr a t
    }.

Lemma expr_inject'_unop :
  forall f u t a b
         (EI: expr_inject' f a b),
    expr_inject' f (Eunop u t a) (Eunop u t b).
Proof.
  intros f u t a b EI; inv EI. 
  econstructor.
  apply Val.lessdef_unop; eauto.
  apply Val.expr_inject_unop; eauto.
  apply Val.lessdef_unop; eauto.
  simpl; intros. destr. eauto.
Qed.


Lemma expr_inject'_binop :
  forall f bi t t' a b c d
         (EI: expr_inject' f a b)
         (EI': expr_inject' f c d),
    expr_inject' f (Ebinop bi t t' a c) (Ebinop bi t t' b d).
Proof.
  intros f bi t t' a b c d A B; inv A; inv B.
  econstructor.
  apply Val.lessdef_binop; eauto.
  apply Val.expr_inject_binop; eauto.
  apply Val.lessdef_binop; eauto.
  simpl; intros.
  destr; eauto.
Qed.

Lemma expr_inject'_incr:
  Val.inj_incr_compat expr_inject'.
Proof.
  red; intros.
  inv EI.
  econstructor; eauto.
  eapply Val.expr_inject_incr; eauto.
Qed.

Lemma lessdef_vint:
  forall i j,
    Values.Val.lessdef (Vint i) (Vint j) ->
    i = j.
Proof.
  intros i j A; inv A; auto.
Qed.

Lemma lessdef_val:
  forall v1 v2,
    Val.lessdef (Eval v1) (Eval v2) <->
    Values.Val.lessdef v1 v2.
Proof.
  Ltac t := repeat match goal with
      H: Val.lessdef _ _ |- _ =>
      solve [specialize (H (fun _ => Int.zero) (fun _ _ => Byte.zero));
              simpl in H; inv H; try discriminate; auto]
           | H: Val.lessdef _ (Eval (Vptr ?b ?i)) |- _ =>
             generalize (H (fun bb => if peq bb b then Int.one else Int.zero) (fun _ _ => Byte.zero));
               generalize (H (fun bb => Int.zero) (fun _ _ => Byte.zero)); simpl; clear H; intros
           | H: Val.lessdef (Eval (Vptr ?b ?i)) _ |- _ =>
             generalize (H (fun bb => if peq bb b then Int.one else Int.zero) (fun _ _ => Byte.zero));
               generalize (H (fun bb => Int.zero) (fun _ _ => Byte.zero)); simpl; clear H; intros
           | H: Values.Val.lessdef _ _ |- _ => solve [inv H]
           | H: Values.Val.lessdef (Vint _) (Vint _) |- _ => apply lessdef_vint in H; subst
           | H: context [peq ?b ?b] |- _ => rewrite peq_true in H; simpl in H
           | H: context [peq ?b ?b0] |- _ => destruct (peq b b0); subst; auto; simpl in *
           | H: Int.add _ ?a = Int.add _ ?a |- _ =>
             apply f_equal with (f:= fun x => Int.sub x a) in H;
               rewrite ! Int.sub_add_opp in H;
               rewrite ! Int.add_assoc in H;
               rewrite ! Int.add_neg_zero in H;
               repeat rewrite Int.add_zero in H;
               repeat rewrite Int.add_zero_l in H; try discriminate
           | _ => rewrite Int.add_zero in *
           | _ => rewrite Int.add_zero_l in *
           | |- Val.lessdef _ _ => red; intros; auto
         end.
  split; intros; des v1; des v2; auto; t.
  - subst; auto.
  - subst i. contradict H0.
    replace i0 with (Int.add Int.zero i0) at 1. intro;  t.
    apply Int.add_zero_l.
  - inv H. auto.
Qed.

Lemma ld_unop:
  forall u t a b,
    Values.Val.lessdef a b -> 
    Values.Val.lessdef (fun_of_unop u t a) (fun_of_unop u t b).
Proof.
  intros u t a b LD; inv LD.
  - auto.
  - rewrite fun_of_unop_undef; auto.
Qed.


Lemma ld_binop:
  forall bi t s a b c d,
    Values.Val.lessdef a b ->
    Values.Val.lessdef c d -> 
    Values.Val.lessdef (fun_of_binop bi t s a c) (fun_of_binop bi t s b d).
Proof.
  intros bi t s a b c d LD1 LD2; inv LD1; inv LD2.
  - auto.
  - rewrite fun_of_binop_undef_r; auto.
  - rewrite fun_of_binop_undef_l; auto.
  - rewrite fun_of_binop_undef_l; auto.
Qed.


Lemma same_eval_val:
  forall v1 v2, same_eval (Eval v1) (Eval v2) -> v1 = v2.
Proof.
  intros.
  generalize (H (fun _ => Int.zero) (fun _ _ => Byte.zero))
             (H (fun _ => Int.one) (fun _ _ => Byte.zero)).
  des v1; des v2.
  - rewrite H0 in H1.
    apply inj_vint in H1.
    rewrite <- ! (Int.add_commut i0) in H1.
    apply int_add_eq_l in H1. discriminate.
  - rewrite <- H0 in H1.
    apply inj_vint in H1.
    rewrite <- ! (Int.add_commut i) in H1.
    apply int_add_eq_l in H1. discriminate.
  - apply inj_vint in H0. rewrite ! Int.add_zero_l in H0. subst.
    specialize (H (fun bb => if peq b bb then Int.zero else Int.one) (fun _ _ => Byte.zero)).
    clear - H.
    f_equal.
    simpl in H.
    rewrite peq_true in H.
    revert H; destr.
    apply inj_vint in H.
    rewrite <- ! (Int.add_commut i0) in H.
    apply int_add_eq_l in H. discriminate.
Qed.


Lemma inj_eval_eval:
  forall f v1 e,
    Val.apply_inj f (Eval v1) = Some e ->
    exists v, e = Eval v.
Proof.
  unfold Val.apply_inj, Val.inj_ptr.
  intros.
  exists (match v1 with
              Vptr b i => 
              match f b with
                  Some (b',delta) => Vptr b' (Int.add i (Int.repr delta))
                | _ => v1
              end
            | _ => v1
          end).
  des v1. des (f b). des p.
Qed.

Lemma inj_eval_ld:
  forall f v1 x alloc0
         (AI: Val.apply_inj f (Eval v1) = Some (Eval x)),
    Values.Val.lessdef (eSval alloc0 x) (eSval (Val.inj_alloc alloc0 f) v1).
Proof.
  intros; des v1; inv AI; simpl; auto.
  unfold Val.inj_ptr in H0.
  unfold Val.inj_alloc. des (f b). des p.
  inv H0. simpl.
    sint. rewrite (Int.add_commut i); auto.
Qed.


Lemma expr_val_inject:
  forall f v1 v2,
    Val.expr_inject f (Eval v1) (Eval v2) ->
    val_inject f v1 v2.
Proof.
  intros f v1 v2 EI.
  destruct v1; destruct v2; inv EI; simpl in *;
  try constructor; inv inj_ok; try constructor;
  unfold Val.inj_ptr in *; destruct (f b) as [[b' delta]|] eqn:?; simpl in *; inv H0.
  econstructor; eauto.
Qed.

