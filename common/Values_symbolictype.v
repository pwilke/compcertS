Require Import Coqlib.
Require Import ZArith.
Require Import Values.
Require Import AST.
Require Import Integers.
Require Import Floats.

(** This module defines the type of symbolic values, along with their
type-checking functions. *)

Inductive styp := Tint | Tlong | Tfloat | Tsingle.

Definition styp_eq (x y : styp) : {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Lemma styp_eq_refl:
  forall x, styp_eq x x = left eq_refl.
Proof.
  destruct x; simpl; auto.
Qed.

(** The type [lval] defines low-level values, i.e. values without pointer or
undefined values *)

(* Inductive lval : Type := *)
(* | Vi (i:int)             *)
(* | Vl (i:int64) *)
(* | Vf (f:float) *)
(* | Vs (f:float32) *)
(* . *)

(* Lemma eq_lval_inj_i: *)
(*   forall i j, Vi i = Vi j -> i = j. *)
(* Proof. *)
(*   intros. *)
(*   inv H; reflexivity. *)
(* Qed. *)

(* Lemma eq_lval_inj_l: *)
(*   forall i j, Vl i = Vl j -> i = j. *)
(* Proof. *)
(*   intros. *)
(*   inv H; reflexivity. *)
(* Qed. *)

(* Lemma eq_lval_inj_f: *)
(*   forall i j, Vf i = Vf j -> i = j. *)
(* Proof. *)
(*   intros. *)
(*   inv H; reflexivity. *)
(* Qed. *)

(* Lemma eq_lval_inj_s: *)
(*   forall i j, Vs i = Vs j -> i = j. *)
(* Proof. *)
(*   intros. *)
(*   inv H; reflexivity. *)
(* Qed. *)


(* Definition lval_eq_dec (x y : lval) : {x = y}+{x<> y}. *)
(* Proof. *)
(*   decide equality. *)
(*   apply Int.eq_dec. *)
(*   apply Int64.eq_dec. *)
(*   apply Float.eq_dec. *)
(*   apply Float32.eq_dec. *)
(* Qed. *)

(* (** Type-checking function for low-level values *) *)
(* Definition tcheck_lval (v:lval) : styp := *)
(*   match v with *)
(*       Vi _ => Tint *)
(*     | Vl _ => Tlong *)
(*     | Vf _ => Tfloat *)
(*     | Vs _ => Tsingle *)
(*   end. *)

(* Definition wt_lval (v:lval) (t:styp) := *)
(*   match v, t with *)
(*       Vi _, Tint *)
(*     | Vl _, Tlong *)
(*     | Vf _, Tfloat *)
(*     | Vs _, Tsingle => True *)
(*     | _, _ => False *)
(*   end. *)

(** Definition of unary/binary operators  *)

Inductive se_signedness := SESigned | SEUnsigned.

Inductive unop_t :=
  OpBoolval : unop_t
| OpNotbool : unop_t
| OpNeg : unop_t
| OpNot : unop_t
| OpZeroext : Z -> unop_t
| OpSignext : Z -> unop_t
| OpRolm : int -> int -> unop_t
| OpAbsf
| OpConvert : se_signedness -> (styp*se_signedness) -> unop_t
(*r OpConvert sg (t,sg2) : convert from type (_,sg) to (t,sg2) *)
| OpLoword : unop_t
| OpHiword : unop_t
| OpSingleofbits : unop_t
| OpDoubleofbits : unop_t
| OpBitsofsingle : unop_t
| OpBitsofdouble : unop_t.

Inductive binop_t :=
| OpAnd           : binop_t
| OpOr            : binop_t
| OpXor           : binop_t
| OpAdd           : binop_t
| OpSub           : binop_t
| OpMul           : binop_t
| OpMulh          : se_signedness -> binop_t
| OpMull'         : binop_t
| OpShrx          : binop_t
| OpShr_carry     : binop_t
| OpRor           : binop_t
| OpFloatofwords  : binop_t
| OpLongofwords   : binop_t
| OpDiv           : se_signedness -> binop_t
| OpMod           : se_signedness -> binop_t
| OpCmp           : se_signedness -> comparison -> binop_t
| OpShr           : se_signedness -> binop_t
| OpShl           : binop_t
| OpSubOverflow   : binop_t.


(** The type [sval] is identical to CompCert's [value] with the exception that
 undefined values are labelled by a location. *)

(* Inductive sval := *)
(* | Eundef  : block -> int  -> sval *)
(* | Eint    : int              -> sval *)
(* | Elong   : int64            -> sval *)
(* | Efloat  : float            -> sval *)
(* | Esingle : float32          -> sval *)
(* | Eptr    : block -> int     -> sval. *)


Inductive expr_sym : Type :=
| Eval   : val -> expr_sym
| Eundef  : block -> int  -> expr_sym 
| Eunop  : unop_t -> styp -> expr_sym -> expr_sym
| Ebinop : binop_t -> styp -> styp -> expr_sym -> expr_sym -> expr_sym.


Definition comp_eq_dec (c1 c2: comparison) : {c1=c2} + {c1 <> c2}.
Proof.
  decide equality.
Defined.

Definition se_signedness_eq_dec (s1 s2: se_signedness) : {s1=s2} + {s1 <> s2}.
Proof.
  decide equality.
Defined.

Hint Resolve Val.eq_val_dec.
Hint Resolve eq_nat_dec.
Hint Resolve Z_eq_dec.
Hint Resolve Int.eq_dec.
Hint Resolve Int64.eq_dec.
Hint Resolve styp_eq.
Hint Resolve se_signedness_eq_dec.
Hint Resolve comp_eq_dec.
Hint Resolve Float.eq_dec.
Hint Resolve Float32.eq_dec.

Definition eq_expr_sym_dec (e1 e2: expr_sym) : {e1=e2} + {e1 <> e2}.
Proof.
  repeat decide equality; auto. 
Defined.

Definition wt_val (v:val) (r:styp) : Prop := 
  match v, r with
      Vundef, _
    | Vint _, Tint
    | Vlong _, Tlong
    | Vptr _ _, Tint
    | Vfloat _, Tfloat
    | Vsingle _, Tsingle => True
    | _,_ => False
  end.

Lemma wt_val_dec : forall v r, {wt_val v r} + {~wt_val v r}.
Proof.
  intros.
  destruct v; destruct r; simpl; intuition.
Defined.

Inductive is_lval_typ : styp -> Prop :=
| isTint  : is_lval_typ Tint
| isTlong : is_lval_typ Tlong.

Definition is_lval_typ_dec (t : styp) : {is_lval_typ t} +{ ~ is_lval_typ t}.
Proof.
  refine
    (match t as t' return {is_lval_typ t'}+{~is_lval_typ t'} with
       | Tint => left isTint
       | Tlong => left isTlong
       | _     => right _
     end);
  intro;
    abstract inversion H.
Defined.

Inductive is_float_typ : styp -> Prop :=
| isTfloat: is_float_typ Tfloat
| isTsingle: is_float_typ Tsingle.

Definition is_float_typ_dec (t : styp) : {is_float_typ t} +{ ~ is_float_typ t}.
Proof.
  refine
    (match t as t' return {is_float_typ t'}+{~is_float_typ t'} with
       | Tfloat => left isTfloat
       | Tsingle => left isTsingle
       | _     => right _
     end);
  intro;
    abstract inversion H.
Defined.

(** [wt_unop o t r] holds if the operator o can be used with an argument of type t and returns a result of type r *)

Definition styp_of_ast (t : typ) : styp := 
  match t with
      Tany32 | AST.Tint => Tint
    | Tany64 | AST.Tlong => Tlong
    | AST.Tfloat => Tfloat
    | AST.Tsingle => Tsingle
  end.

Definition wt_unop (u : unop_t) (t : styp) (r : styp) : Prop :=
  match  u with
    | OpBoolval | OpNotbool | OpRolm _ _  => t = Tint /\ r = t 
    | OpNeg                  => t = r
    | OpNot                  => t = r /\ is_lval_typ t
    | OpZeroext z            => t = r /\ is_lval_typ t
    | OpSignext z            => t = r /\ is_lval_typ t
    | OpAbsf                 => t = r /\ is_float_typ t
    | OpConvert s' (ti,s)    => ti = r  (* Nothing about t *)
    | OpLoword               => t = Tlong /\ r = Tint 
    | OpHiword               => t = Tlong /\ r = Tint
    | OpSingleofbits         => t = Tint  /\ r = Tsingle
    | OpDoubleofbits         => t = Tlong /\ r = Tfloat
    | OpBitsofsingle         => t = Tsingle /\ r = Tint
    | OpBitsofdouble         => t = Tfloat  /\ r = Tlong
  end.

(** Binary operators are parametrised by a single type.
    This is sufficient to recover the type information for the arguments. *)


Definition wt_binop (b : binop_t) (t1 : styp) (t2 : styp) (r : styp) : Prop :=
  match b with
    | OpAnd | OpOr | OpXor  => t1 = t2 /\ t1 = r /\ is_lval_typ t1
    | OpAdd | OpSub 
    | OpMul | OpDiv _       => t1 = t2 /\ t1 = r
    | OpMod _               => t1 = t2 /\ t1 = r /\ is_lval_typ t1
    | OpCmp  _ _            => t1 = t2 /\ r = Tint
    | OpShrx  | OpShr_carry 
    | OpRor                 => t1 = t2 /\ t1 = Tint /\ r = Tint
    | OpMull'         => t1 = t2 /\ t1 = Tint /\ r = Tlong
    | OpMulh _        => t1 = t2 /\ t1 = Tint /\ r = Tint
    | OpFloatofwords  => t1 = t2 /\ t1 = Tint /\ r = Tfloat
    | OpLongofwords   => t1 = t2 /\ t1 = Tint /\ r = Tlong
    | OpShl | OpShr _         => t1 = r  /\ t2 = Tint /\ is_lval_typ t1
    | OpSubOverflow  => t1 = Tint /\ t2 = Tint /\ r = Tint
  end.

(* Definition wt_sval (v : sval) (t : styp) : Prop := *)
(*   match v with *)
(*     | Eundef _ _   => t = Tint *)
(*     | Eint   _   => t = Tint *)
(*     | Elong  _   => t = Tlong *)
(*     | Efloat _   => t = Tfloat *)
(*     | Esingle _   => t = Tsingle *)
(*     | Eptr   _ _ => t = Tint *)
(*   end. *)

Fixpoint wt_expr (e:expr_sym) (r:styp) {struct e}: Prop :=
  match e with
    | Eval v                     => wt_val v r
    | Eundef b i                 => r = Tint
    | Eunop u t e                => wt_expr e t /\ wt_unop u t r
    | Ebinop b t1 t2 e1 e2       => wt_expr e1 t1 /\ wt_expr e2 t2 /\ wt_binop b t1 t2 r
  end.

Definition weak_wt (e: expr_sym) (t: styp) : Prop :=
  wt_expr e t \/ ~ exists t, wt_expr e t.


Lemma wt_unop_determ:
  forall u t s s',
    wt_unop u t s ->
    wt_unop u t s' ->
    s = s'.
Proof.
  des u; des t; des s; des s'.
Qed.


Lemma wt_binop_determ:
  forall b t1 t2 s s',
    wt_binop b t1 t2 s ->
    wt_binop b t1 t2 s' ->
    s = s'.
Proof. 
  des b; des t1; des t2; des s; des s'.
Qed.


Lemma wt_expr_2_is_undef:
  forall e t t',
    wt_expr e t ->
    wt_expr e t' ->
    t <> t' ->
    e = Eval Vundef.
Proof.
  induction e; simpl; intros; eauto.
  - des v; des t; des t'.
  - congruence.
  - exfalso; apply H1. eapply wt_unop_determ; intuition eauto.
  - exfalso; apply H1. eapply wt_binop_determ; intuition eauto.
Qed.


Lemma wt_unop_dec : forall u s r, { wt_unop u s r } + { ~ wt_unop u s r }.
Proof.
  des u; des s; des r;
  match goal with
      |- {?a = ?a /\ is_lval_typ Tint} + {_} => left; split; auto; constructor
    | |- {?a = ?a /\ is_lval_typ Tlong} + {_} => left; split; auto; constructor
    | |- {?a = ?a /\ is_lval_typ Tfloat} + {_} => right; intros [A B]; inv B
    | |- {?a = ?a /\ is_lval_typ Tsingle} + {_} => right; intros [A B]; inv B
    | |- {?a = ?a /\ is_float_typ Tint} + {_} => right; intros [A B]; inv B
    | |- {?a = ?a /\ is_float_typ Tlong} + {_} => right; intros [A B]; inv B
    | |- {?a = ?a /\ is_float_typ Tfloat} + {_} => left; split; auto; constructor
    | |- {?a = ?a /\ is_float_typ Tsingle} + {_} => left; split; auto; constructor
    | |- {?a = _} + {_} => des a
  end.
Qed.

Lemma wt_binop_dec : forall b t1 t2 r, { wt_binop b t1 t2 r } + { ~ wt_binop b t1 t2 r }.
Proof.
  des b; des t1; des t2; des r;
  match goal with
      |- {?a = ?a /\ ?b = ?b /\ is_lval_typ Tint} + {_} => left; repeat split; auto; constructor
    | |- {?a = ?a /\ ?b = ?b /\ is_lval_typ Tlong} + {_} => left; repeat split; auto; constructor
    | |- {?a = ?a /\ ?b = ?b /\ is_lval_typ Tfloat} + {_} => right; intros [A [C B]]; inv B
    | |- {?a = ?a /\ ?b = ?b /\ is_lval_typ Tsingle} + {_} => right; intros [A [C B]]; inv B
    | |- {?a = ?a /\ ?b = ?b /\ is_float_typ Tint} + {_} => right; intros [A [C B]]; inv B
    | |- {?a = ?a /\ ?b = ?b /\ is_float_typ Tlong} + {_} => right; intros [A [C B]]; inv B
    | |- {?a = ?a /\ ?b = ?b /\ is_float_typ Tfloat} + {_} => left; repeat split; auto; constructor
    | |- {?a = ?a /\ ?b = ?b /\ is_float_typ Tsingle} + {_} => left; repeat split; auto; constructor
    | |- {?a = _} + {_} => des a
  end.
Qed.

Lemma wt_expr_dec : forall e r, { wt_expr e r } + { ~ wt_expr e r }.
Proof.
  induction e; simpl; intros; auto.
  - apply wt_val_dec.
  - destruct (IHe s); destruct (wt_unop_dec u s r); intuition.
  - destruct (IHe1 s); destruct (IHe2 s0); destruct (wt_binop_dec b s s0 r); intuition.
 Defined.

(** When we normalise a symbolic expression, we must know into what kind of
value we want to normalise it. This is the purpose of the [result] type. In
particular, we would have no way of knowing whether an expression with type
[Tint] should be normalised into a pointer or an integer. *)

Inductive result := Int | Long | Float | Single | Ptr .

Definition result_eq_dec (r1 r2: result) : { r1=r2 } + { r1 <> r2 }.
Proof.
  decide equality.
Defined.

