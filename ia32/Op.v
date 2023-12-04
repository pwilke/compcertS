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

(** Operators and addressing modes.  The abstract syntax and dynamic
  semantics for the CminorSel, RTL, LTL and Mach languages depend on the
  following types, defined in this library:
- [condition]:  boolean conditions for conditional branches;
- [operation]: arithmetic and logical operations;
- [addressing]: addressing modes for load and store operations.

  These types are IA32-specific and correspond roughly to what the 
  processor can compute in one instruction.  In other terms, these
  types reflect the state of the program after instruction selection.
  For a processor-independent set of operations, see the abstract
  syntax and dynamic semantics of the Cminor language.
*)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import NormaliseSpec.
Require Import ExprEval.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Values_symbolic.
Require Import Values_symbolictype.
Require Import Setoid.
Require Import MemRel.

Set Implicit Arguments.

(** Conditions (boolean-valued operators). *)

Inductive condition : Type :=
  | Ccomp: comparison -> condition      (**r signed integer comparison *)
  | Ccompu: comparison -> condition     (**r unsigned integer comparison *)
  | Ccompimm: comparison -> int -> condition (**r signed integer comparison with a constant *)
  | Ccompuimm: comparison -> int -> condition  (**r unsigned integer comparison with a constant *)
  | Ccompf: comparison -> condition     (**r 64-bit floating-point comparison *)
  | Cnotcompf: comparison -> condition  (**r negation of a floating-point comparison *)
  | Ccompfs: comparison -> condition    (**r 32-bit floating-point comparison *)
  | Cnotcompfs: comparison -> condition (**r negation of a floating-point comparison *)
  | Cmaskzero: int -> condition         (**r test [(arg & constant) == 0] *)
  | Cmasknotzero: int -> condition.     (**r test [(arg & constant) != 0] *)

(** Addressing modes.  [r1], [r2], etc, are the arguments to the 
  addressing. *)

Inductive addressing: Type :=
  | Aindexed: int -> addressing         (**r Address is [r1 + offset] *)
  | Aindexed2: int -> addressing        (**r Address is [r1 + r2 + offset] *)
  | Ascaled: int -> int -> addressing   (**r Address is [r1 * scale + offset] *)
  | Aindexed2scaled: int -> int -> addressing
                                   (**r Address is [r1 + r2 * scale + offset] *)
  | Aglobal: ident -> int -> addressing (**r Address is [symbol + offset] *)
  | Abased: ident -> int -> addressing  (**r Address is [symbol + offset + r1] *)
  | Abasedscaled: int -> ident -> int -> addressing  (**r Address is [symbol + offset + r1 * scale] *)
  | Ainstack: int -> addressing.        (**r Address is [stack_pointer + offset] *)

(** Arithmetic and logical operations.  In the descriptions, [rd] is the
  result of the operation and [r1], [r2], etc, are the arguments. *)

Inductive operation : Type :=
  | Omove: operation                    (**r [rd = r1] *)
  | Ointconst: int -> operation         (**r [rd] is set to the given integer constant *)
  | Ofloatconst: float -> operation     (**r [rd] is set to the given float constant *)
  | Osingleconst: float32 -> operation  (**r [rd] is set to the given float constant *)
  | Oindirectsymbol: ident -> operation (**r [rd] is set to the address of the symbol *)
(*c Integer arithmetic: *)
  | Ocast8signed: operation             (**r [rd] is 8-bit sign extension of [r1] *)
  | Ocast8unsigned: operation           (**r [rd] is 8-bit zero extension of [r1] *)
  | Ocast16signed: operation            (**r [rd] is 16-bit sign extension of [r1] *)
  | Ocast16unsigned: operation          (**r [rd] is 16-bit zero extension of [r1] *)
  | Oneg: operation                     (**r [rd = - r1] *)
  | Osub: operation                     (**r [rd = r1 - r2] *)
  | Omul: operation                     (**r [rd = r1 * r2] *)
  | Omulimm: int -> operation           (**r [rd = r1 * n] *)
  | Omulhs: operation                   (**r [rd = high part of r1 * r2, signed] *)
  | Omulhu: operation                   (**r [rd = high part of r1 * r2, unsigned] *)
  | Odiv: operation                     (**r [rd = r1 / r2] (signed) *)
  | Odivu: operation                    (**r [rd = r1 / r2] (unsigned) *)
  | Omod: operation                     (**r [rd = r1 % r2] (signed) *)
  | Omodu: operation                    (**r [rd = r1 % r2] (unsigned) *)
  | Oand: operation                     (**r [rd = r1 & r2] *)
  | Oandimm: int -> operation           (**r [rd = r1 & n] *)
  | Oor: operation                      (**r [rd = r1 | r2] *)
  | Oorimm: int -> operation            (**r [rd = r1 | n] *)
  | Oxor: operation                     (**r [rd = r1 ^ r2] *)
  | Oxorimm: int -> operation           (**r [rd = r1 ^ n] *)
  | Onot: operation                     (**r [rd = ~r1] *)
  | Oshl: operation                     (**r [rd = r1 << r2] *)
  | Oshlimm: int -> operation           (**r [rd = r1 << n] *)
  | Oshr: operation                     (**r [rd = r1 >> r2] (signed) *)
  | Oshrimm: int -> operation           (**r [rd = r1 >> n] (signed) *)
  | Oshrximm: int -> operation          (**r [rd = r1 / 2^n] (signed) *)
  | Oshru: operation                    (**r [rd = r1 >> r2] (unsigned) *)
  | Oshruimm: int -> operation          (**r [rd = r1 >> n] (unsigned) *)
  | Ororimm: int -> operation           (**r rotate right immediate *)
  | Oshldimm: int -> operation          (**r [rd = r1 << n | r2 >> (32-n)] *)
  | Olea: addressing -> operation       (**r effective address *)
(*c Floating-point arithmetic: *)
  | Onegf: operation                    (**r [rd = - r1] *)
  | Oabsf: operation                    (**r [rd = abs(r1)] *)
  | Oaddf: operation                    (**r [rd = r1 + r2] *)
  | Osubf: operation                    (**r [rd = r1 - r2] *)
  | Omulf: operation                    (**r [rd = r1 * r2] *)
  | Odivf: operation                    (**r [rd = r1 / r2] *)
  | Onegfs: operation                   (**r [rd = - r1] *)
  | Oabsfs: operation                   (**r [rd = abs(r1)] *)
  | Oaddfs: operation                   (**r [rd = r1 + r2] *)
  | Osubfs: operation                   (**r [rd = r1 - r2] *)
  | Omulfs: operation                   (**r [rd = r1 * r2] *)
  | Odivfs: operation                   (**r [rd = r1 / r2] *)
  | Osingleoffloat: operation           (**r [rd] is [r1] truncated to single-precision float *)
  | Ofloatofsingle: operation           (**r [rd] is [r1] extended to double-precision float *)
(*c Conversions between int and float: *)
  | Ointoffloat: operation              (**r [rd = signed_int_of_float64(r1)] *)
  (* | Ointuoffloat: operation              (**r [rd = unsigned_int_of_float64(r1)] *) *)
  | Ofloatofint: operation              (**r [rd = float64_of_signed_int(r1)] *)
  (* | Ofloatofintu: operation              (**r [rd = float64_of_unsigned_int(r1)] *) *)
  | Ointofsingle: operation             (**r [rd = signed_int_of_float32(r1)] *)
  | Osingleofint: operation             (**r [rd = float32_of_signed_int(r1)] *)
(*c Manipulating 64-bit integers: *)
  | Omakelong: operation                (**r [rd = r1 << 32 | r2] *)
  | Olowlong: operation                 (**r [rd = low-word(r1)] *)
  | Ohighlong: operation                (**r [rd = high-word(r1)] *)
(*c Boolean tests: *)
  | Ocmp: condition -> operation.       (**r [rd = 1] if condition holds, [rd = 0] otherwise. *)

(** Derived operators. *)

Definition Oaddrsymbol (id: ident) (ofs: int) : operation := Olea (Aglobal id ofs).
Definition Oaddrstack (ofs: int) : operation := Olea (Ainstack ofs).
Definition Oaddimm (n: int) : operation := Olea (Aindexed n).

(** Comparison functions (used in modules [CSE] and [Allocation]). *)

Definition eq_condition (x y: condition) : {x=y} + {x<>y}.
Proof.
  generalize Int.eq_dec; intro.
  assert (forall (x y: comparison), {x=y}+{x<>y}). decide equality.
  decide equality.
Defined.

Definition eq_addressing (x y: addressing) : {x=y} + {x<>y}.
Proof.
  generalize Int.eq_dec; intro.
  assert (forall (x y: ident), {x=y}+{x<>y}). exact peq.
  decide equality.
Defined.

Definition eq_operation (x y: operation): {x=y} + {x<>y}.
Proof.
  generalize Int.eq_dec; intro.
  generalize Float.eq_dec; intro.
  generalize Float32.eq_dec; intro.
  generalize Int64.eq_dec; intro.
  decide equality.
  apply peq.
  apply eq_addressing.
  apply eq_condition.
Defined.

Global Opaque eq_condition eq_addressing eq_operation.

(** * Evaluation functions *)

(** Evaluation of conditions, operators and addressing modes applied
  to lists of values.  Return [None] when the computation can trigger an
  error, e.g. integer division by zero.  [eval_condition] returns a boolean,
  [eval_operation] and [eval_addressing] return a value. *)

Definition eval_condition (cond: condition) (vl: list expr_sym) : option expr_sym :=
  match cond, vl with
  | Ccomp c, v1 :: v2 :: nil => Some (Val.cmp_bool c v1 v2)
  | Ccompu c, v1 :: v2 :: nil => Some (Val.cmpu_bool c v1 v2)
  | Ccompimm c n, v1 :: nil => Some (Val.cmp_bool c v1 (Eval (Vint n)))
  | Ccompuimm c n, v1 :: nil => Some (Val.cmpu_bool c v1 (Eval (Vint n)))
  | Ccompf c, v1 :: v2 :: nil => Some (Val.cmpf_bool c v1 v2)
  | Cnotcompf c, v1 :: v2 :: nil => Some (Eunop OpNotbool Tint (Val.cmpf_bool c v1 v2))
  | Ccompfs c, v1 :: v2 :: nil => Some (Val.cmpfs_bool c v1 v2)
  | Cnotcompfs c, v1 :: v2 :: nil => Some (Eunop OpNotbool Tint (Val.cmpfs_bool c v1 v2))
  | Cmaskzero n, v1 :: nil => Some (Val.maskzero_bool v1 n)
  | Cmasknotzero n, v1 :: nil => Some (Eunop OpNotbool Tint (Val.maskzero_bool v1 n))
  | _, _ => None
  end.

Ltac easy_inv :=
  repeat match goal with
           H: match ?vl : list expr_sym with _ => _ end = _ |- _ =>
           destruct vl; try discriminate
         | H: Some _ = Some _ |- _ => inv H
         end.
  
Lemma eval_condition_cmp_one:
  forall c vl x sg,
    eval_condition c vl = Some x ->
    same_eval (Ebinop (OpCmp sg Ceq) Tint Tint x (Eval (Vint Int.one))) x.
Proof.
  destruct c; simpl; intros; easy_inv;
  try (red;intros; simpl; seval);
  des sg; repeat match goal with
                     |- context[ Int.cmp ?c ?i ?i0 ] => des (Int.cmp c i i0)
                   | |- context[ Int.cmpu ?c ?i ?i0 ] => des (Int.cmpu c i i0)
                   | |- context[ Float.cmp ?c ?i ?i0 ] => des (Float.cmp c i i0)
                   | |- context[ Float32.cmp ?c ?i ?i0 ] => des (Float32.cmp c i i0)
                   | |- context[ Int.eq ?i ?i0 ] => des (Int.eq i i0)
                 end.
Qed.

Lemma eval_condition_zero_one:
  forall c vl x alloc em i,
    eval_condition c vl = Some x ->
    eSexpr alloc em x = Vint i ->
    i = Int.one \/ i = Int.zero.
Proof.
  des c; easy_inv; unfold Val.maskzero_bool in *; try des c0;
  repeat (revert H0; seval);  unfold Vtrue, Vfalse in *; 
        repeat match goal with
                   |- context[ Int.cmp ?c ?i ?i0 ] => des (Int.cmp c i i0)
                 | |- context[ Int.cmpu ?c ?i ?i0 ] => des (Int.cmpu c i i0)
                 | |- context[ Float.cmp ?c ?i ?i0 ] => des (Float.cmp c i i0)
                 | |- context[ Float32.cmp ?c ?i ?i0 ] => des (Float32.cmp c i i0)
                 | |- context[ Int.eq ?i ?i0 ] => des (Int.eq i i0)
                 | |- context[ Int.lt ?i ?i0 ] => des (Int.lt i i0)
                 | |- context[ Int.ltu ?i ?i0 ] => des (Int.ltu i i0)
                 | H : context [Int.eq Int.one Int.zero] |- _ =>
                   (rewrite Int.eq_false in H by (apply Int.one_not_zero); simpl in H)
                 | H : context [Int.eq ?a ?a] |- _ =>
                   (rewrite Int.eq_true in H; simpl in H)
                 | H : Vint _ = Vint _ |- _ => inv H; auto
                 | |- _ => unfold Vtrue, Vfalse in *
               end.
  revert Heqv; seval. des (Int.eq (Int.and i2 i) Int.zero); inv Heqv0; inv H0; auto.
  revert Heqv; seval. des (Int.eq (Int.and i2 i) Int.zero); inv Heqv0; inv H0; auto.
Qed.

Lemma eval_condition_boolval:
  forall c vl v,
    eval_condition c vl = Some v ->
    same_eval (Val.boolval v) v.
Proof.
  intros.
  generalize (eval_condition_cmp_one _ _ SESigned H).
  intros A. red.  intros; simpl.
  rewrite <- (A alloc em) at 2. simpl.
  seval; auto.
  eapply eval_condition_zero_one in H; eauto.
  destruct H; subst.
  rewrite Int.eq_true. rewrite Int.eq_false by (apply Int.one_not_zero). simpl; auto.
  rewrite Int.eq_true. rewrite Int.eq_sym. rewrite Int.eq_false by (apply Int.one_not_zero).
  simpl; auto.
Qed.
Ltac FuncInv :=
  match goal with
  | H: (match ?x with nil => _ | _ :: _ => _ end = Some _) |- _ =>
      destruct x; simpl in H; try discriminate; FuncInv
  | H: (match ?v with Vundef => _ | Vint _ => _ | Vfloat _ => _ | Vptr _ _ => _ end = Some _) |- _ =>
      destruct v; simpl in H; try discriminate; FuncInv
  | H: (Some _ = Some _) |- _ =>
      injection H; intros; clear H; FuncInv
  | _ =>
      idtac
  end.

Lemma eval_condition_type:
  forall c vl v t,
    eval_condition c vl = Some v ->
    wt_expr v t -> t = Tint.
Proof.
  intros.
  destruct c; simpl in H; FuncInv; subst; simpl in *; intuition.
Qed.

Lemma eval_cond_norm_0_1:
  forall cond args b i
         (EC: eval_condition cond args = Some b)
         m (N : Mem.mem_norm m b = Vint i),
    i = Int.one \/ i = Int.zero.
Proof.
  intros.
  generalize (Mem.norm_correct m b).
  rewrite N.
  intro A; inv A.
  destruct (Mem.concrete_mem m).
  specialize (eval_ok_m _ Normalise.dummy_em H).
  inv eval_ok_m.
  exploit eval_condition_zero_one; eauto. 
Qed.


Definition eval_addressing
    (F V: Type) (genv: Genv.t F V) (sp: expr_sym)
    (addr: addressing) (vl: list expr_sym) : option expr_sym :=
  match addr, vl with
  | Aindexed n, v1::nil =>
      Some (Val.add v1 (Eval (Vint n)))
  | Aindexed2 n, v1::v2::nil =>
      Some (Val.add (Val.add v1 v2) (Eval (Vint n)))
  | Ascaled sc ofs, v1::nil =>
      Some (Val.add (Val.mul v1 (Eval (Vint sc))) (Eval (Vint ofs)))
  | Aindexed2scaled sc ofs, v1::v2::nil =>
      Some(Val.add v1 (Val.add (Val.mul v2 (Eval (Vint sc))) (Eval (Vint ofs))))
  | Aglobal s ofs, nil => Genv.symbol_address' genv s ofs 
  | Abased s ofs, v1::nil =>
    option_map (Val.add v1) (Genv.symbol_address' genv s ofs)
  | Abasedscaled sc s ofs, v1::nil =>
    option_map (Val.add (Val.mul v1 (Eval (Vint sc))))  (Genv.symbol_address' genv s ofs)
  | Ainstack ofs, nil =>
      Some(Val.add sp (Eval (Vint ofs)))
  | _, _ => None
  end.

Definition eval_operation
    (F V: Type) (genv: Genv.t F V) (sp: expr_sym)
    (op: operation) (vl: list expr_sym) : option expr_sym :=
  match op, vl with
  | Omove, v1::nil => Some v1
  | Ointconst n, nil => Some (Eval (Vint n))
  | Ofloatconst n, nil => Some (Eval (Vfloat n))
  | Osingleconst n, nil => Some (Eval (Vsingle n))
  | Oindirectsymbol id, nil => Genv.symbol_address' genv id Int.zero
  | Ocast8signed, v1 :: nil => Some (Val.sign_ext 8 v1)
  | Ocast8unsigned, v1 :: nil => Some (Val.zero_ext 8 v1)
  | Ocast16signed, v1 :: nil => Some (Val.sign_ext 16 v1)
  | Ocast16unsigned, v1 :: nil => Some (Val.zero_ext 16 v1)
  | Oneg, v1::nil => Some (Val.neg v1)
  | Osub, v1::v2::nil => Some (Val.sub v1 v2)
  | Omul, v1::v2::nil => Some (Val.mul v1 v2)
  | Omulimm n, v1::nil => Some (Val.mul v1 (Eval (Vint n)))
  | Omulhs, v1::v2::nil => Some (Val.mulhs v1 v2)
  | Omulhu, v1::v2::nil => Some (Val.mulhu v1 v2)
  | Odiv, v1::v2::nil => Some (Val.divs v1 v2)
  | Odivu, v1::v2::nil => Some (Val.divu v1 v2)
  | Omod, v1::v2::nil => Some (Val.mods v1 v2)
  | Omodu, v1::v2::nil => Some (Val.modu v1 v2)
  | Oand, v1::v2::nil => Some(Val.and v1 v2)
  | Oandimm n, v1::nil => Some (Val.and v1 (Eval (Vint n)))
  | Oor, v1::v2::nil => Some(Val.or v1 v2)
  | Oorimm n, v1::nil => Some (Val.or v1 (Eval (Vint n)))
  | Oxor, v1::v2::nil => Some(Val.xor v1 v2)
  | Oxorimm n, v1::nil => Some (Val.xor v1 (Eval (Vint n)))
  | Onot, v1::nil => Some(Val.notint v1)
  | Oshl, v1::v2::nil => Some (Val.shl v1 v2)
  | Oshlimm n, v1::nil => Some (Val.shl v1 (Eval (Vint n)))
  | Oshr, v1::v2::nil => Some (Val.shr v1 v2)
  | Oshrimm n, v1::nil => Some (Val.shr v1 (Eval (Vint n)))
  | Oshrximm n, v1::nil => Some (Val.shrx v1 (Eval (Vint n)))
  | Oshru, v1::v2::nil => Some (Val.shru v1 v2)
  | Oshruimm n, v1::nil => Some (Val.shru v1 (Eval (Vint n)))
  | Ororimm n, v1::nil => Some (Val.ror v1 (Eval (Vint n)))
  | Oshldimm n, v1::v2::nil => Some (Val.or (Val.shl v1 (Eval (Vint n)))
                                            (Val.shru v2 (Eval (Vint (Int.sub Int.iwordsize n)))))
  | Olea addr, _ => eval_addressing genv sp addr vl
  | Onegf, v1::nil => Some(Val.negf v1)
  | Oabsf, v1::nil => Some(Val.absf v1)
  | Oaddf, v1::v2::nil => Some(Val.addf v1 v2)
  | Osubf, v1::v2::nil => Some(Val.subf v1 v2)
  | Omulf, v1::v2::nil => Some(Val.mulf v1 v2)
  | Odivf, v1::v2::nil => Some(Val.divf v1 v2)
  | Onegfs, v1::nil => Some(Val.negfs v1)
  | Oabsfs, v1::nil => Some(Val.absfs v1)
  | Oaddfs, v1::v2::nil => Some(Val.addfs v1 v2)
  | Osubfs, v1::v2::nil => Some(Val.subfs v1 v2)
  | Omulfs, v1::v2::nil => Some(Val.mulfs v1 v2)
  | Odivfs, v1::v2::nil => Some(Val.divfs v1 v2)
  | Osingleoffloat, v1::nil => Some(Val.singleoffloat v1)
  | Ofloatofsingle, v1::nil => Some(Val.floatofsingle v1)
  | Ointoffloat, v1::nil => Some (Val.intoffloat v1)
  (* | Ointuoffloat, v1::nil => Some (Val.intuoffloat v1) *)
  | Ofloatofint, v1::nil => Some (Val.floatofint v1)
  (* | Ofloatofintu, v1::nil => Some (Val.floatofintu v1) *)
  | Ointofsingle, v1::nil => Some (Val.intofsingle v1)
  | Osingleofint, v1::nil => Some (Val.singleofint v1)
  | Omakelong, v1::v2::nil => Some(Val.longofwords v1 v2)
  | Olowlong, v1::nil => Some(Val.loword v1)
  | Ohighlong, v1::nil => Some(Val.hiword v1)
  | Ocmp c, _ => (eval_condition c vl)
  | _, _ => None
  end.


(** * Static typing of conditions, operators and addressing modes. *)

Definition type_of_condition (c: condition) : list typ :=
  match c with
  | Ccomp _ => AST.Tint :: AST.Tint :: nil
  | Ccompu _ => AST.Tint :: AST.Tint :: nil
  | Ccompimm _ _ => AST.Tint :: nil
  | Ccompuimm _ _ => AST.Tint :: nil
  | Ccompf _ => AST.Tfloat :: AST.Tfloat :: nil
  | Cnotcompf _ => AST.Tfloat :: AST.Tfloat :: nil
  | Ccompfs _ => AST.Tsingle :: AST.Tsingle :: nil
  | Cnotcompfs _ => AST.Tsingle :: AST.Tsingle :: nil
  | Cmaskzero _ => AST.Tint :: nil
  | Cmasknotzero _ => AST.Tint :: nil
  end.

Definition type_of_addressing (addr: addressing) : list typ :=
  match addr with
  | Aindexed _ => AST.Tint :: nil
  | Aindexed2 _ => AST.Tint :: AST.Tint :: nil
  | Ascaled _ _ => AST.Tint :: nil
  | Aindexed2scaled _ _ => AST.Tint :: AST.Tint :: nil
  | Aglobal _ _ => nil
  | Abased _ _ => AST.Tint :: nil
  | Abasedscaled _ _ _ => AST.Tint :: nil
  | Ainstack _ => nil
  end.

Definition type_of_operation (op: operation) : list typ * typ :=
  match op with
  | Omove => (nil, AST.Tint)   (* treated specially *)
  | Ointconst _ => (nil, AST.Tint)
  | Ofloatconst f => (nil, AST.Tfloat)
  | Osingleconst f => (nil, AST.Tsingle)
  | Oindirectsymbol _ => (nil, AST.Tint)
  | Ocast8signed => (AST.Tint :: nil, AST.Tint)
  | Ocast8unsigned => (AST.Tint :: nil, AST.Tint)
  | Ocast16signed => (AST.Tint :: nil, AST.Tint)
  | Ocast16unsigned => (AST.Tint :: nil, AST.Tint)
  | Oneg => (AST.Tint :: nil, AST.Tint)
  | Osub => (AST.Tint :: AST.Tint :: nil, AST.Tint)
  | Omul => (AST.Tint :: AST.Tint :: nil, AST.Tint)
  | Omulimm _ => (AST.Tint :: nil, AST.Tint)
  | Omulhs => (AST.Tint :: AST.Tint :: nil, AST.Tint)
  | Omulhu => (AST.Tint :: AST.Tint :: nil, AST.Tint)
  | Odiv => (AST.Tint :: AST.Tint :: nil, AST.Tint)
  | Odivu => (AST.Tint :: AST.Tint :: nil, AST.Tint)
  | Omod => (AST.Tint :: AST.Tint :: nil, AST.Tint)
  | Omodu => (AST.Tint :: AST.Tint :: nil, AST.Tint)
  | Oand => (AST.Tint :: AST.Tint :: nil, AST.Tint)
  | Oandimm _ => (AST.Tint :: nil, AST.Tint)
  | Oor => (AST.Tint :: AST.Tint :: nil, AST.Tint)
  | Oorimm _ => (AST.Tint :: nil, AST.Tint)
  | Oxor => (AST.Tint :: AST.Tint :: nil, AST.Tint)
  | Oxorimm _ => (AST.Tint :: nil, AST.Tint)
  | Onot => (AST.Tint :: nil, AST.Tint)
  | Oshl => (AST.Tint :: AST.Tint :: nil, AST.Tint)
  | Oshlimm _ => (AST.Tint :: nil, AST.Tint)
  | Oshr => (AST.Tint :: AST.Tint :: nil, AST.Tint)
  | Oshrimm _ => (AST.Tint :: nil, AST.Tint)
  | Oshrximm _ => (AST.Tint :: nil, AST.Tint)
  | Oshru => (AST.Tint :: AST.Tint :: nil, AST.Tint)
  | Oshruimm _ => (AST.Tint :: nil, AST.Tint)
  | Ororimm _ => (AST.Tint :: nil, AST.Tint)
  | Oshldimm _ => (AST.Tint :: AST.Tint :: nil, AST.Tint)
  | Olea addr => (type_of_addressing addr, AST.Tint)
  | Onegf => (AST.Tfloat :: nil, AST.Tfloat)
  | Oabsf => (AST.Tfloat :: nil, AST.Tfloat)
  | Oaddf => (AST.Tfloat :: AST.Tfloat :: nil, AST.Tfloat)
  | Osubf => (AST.Tfloat :: AST.Tfloat :: nil, AST.Tfloat)
  | Omulf => (AST.Tfloat :: AST.Tfloat :: nil, AST.Tfloat)
  | Odivf => (AST.Tfloat :: AST.Tfloat :: nil, AST.Tfloat)
  | Onegfs => (AST.Tsingle :: nil, AST.Tsingle)
  | Oabsfs => (AST.Tsingle :: nil, AST.Tsingle)
  | Oaddfs => (AST.Tsingle :: AST.Tsingle :: nil, AST.Tsingle)
  | Osubfs => (AST.Tsingle :: AST.Tsingle :: nil, AST.Tsingle)
  | Omulfs => (AST.Tsingle :: AST.Tsingle :: nil, AST.Tsingle)
  | Odivfs => (AST.Tsingle :: AST.Tsingle :: nil, AST.Tsingle)
  | Osingleoffloat => (AST.Tfloat :: nil, AST.Tsingle)
  | Ofloatofsingle => (AST.Tsingle :: nil, AST.Tfloat)
  | Ointoffloat => (AST.Tfloat :: nil, AST.Tint)
  (* | Ointuoffloat => (AST.Tfloat :: nil, AST.Tint) *)
  | Ofloatofint => (AST.Tint :: nil, AST.Tfloat)
  (* | Ofloatofintu => (AST.Tint :: nil, AST.Tfloat) *)
  | Ointofsingle => (AST.Tsingle :: nil, AST.Tint)
  | Osingleofint => (AST.Tint :: nil, AST.Tsingle)
  | Omakelong => (AST.Tint :: AST.Tint :: nil, AST.Tlong)
  | Olowlong => (AST.Tlong :: nil, AST.Tint)
  | Ohighlong => (AST.Tlong :: nil, AST.Tint)
  | Ocmp c => (type_of_condition c, AST.Tint)
  end.

(** Weak type soundness results for [eval_operation]:
  the result values, when defined, are always of the type predicted
  by [type_of_operation]. *)



Lemma eval_condition_cmp_zero:
  forall c vl x sg,
    eval_condition c vl = Some x ->
    same_eval (Ebinop (OpCmp sg Cne) Tint Tint x (Eval (Vint Int.zero))) x.
Proof.
  destruct c; simpl; intros; easy_inv;
  try (red; intros; simpl; seval);
  des sg; repeat match goal with
                     |- context[ Int.cmp ?c ?i ?i0 ] => des (Int.cmp c i i0)
                   | |- context[ Int.cmpu ?c ?i ?i0 ] => des (Int.cmpu c i i0)
                   | |- context[ Float.cmp ?c ?i ?i0 ] => des (Float.cmp c i i0)
                   | |- context[ Float32.cmp ?c ?i ?i0 ] => des (Float32.cmp c i i0)
                   | |- context[ Int.eq ?i ?i0 ] => des (Int.eq i i0)
                 end.
Qed.


Ltac TrivialExists :=
  repeat match goal with
  | [ |- exists v2, Some ?v1 = Some v2 /\ _ ] => 
    exists v1; split; auto
  | H: Some _ = Some _ |- _ => inv H
  | H : ?X = Some ?v |- exists v2, ?X = Some v2 /\ _ =>
    exists v ; split;[exact H | auto] 
  | _ => idtac
  end.



Section SOUNDNESS.

Variable A V: Type.
Variable genv: Genv.t A V.


Lemma symbol_address'_has_type : forall (A V : Type) (genv:Genv.t A V) i i0 v,
    Genv.symbol_address' genv i i0 = Some v -> 
   Val.has_type v Tint.
Proof.
  intros until 0.
  unfold Genv.symbol_address'.
  destr. inv H. simpl. auto.
Qed.

Lemma option_map_symbol_address'_some :
  forall (A V : Type) (genv:Genv.t A V) i ofs v (F: expr_sym -> expr_sym),
    option_map F (Genv.symbol_address' genv i ofs) = Some v ->
    exists b, (Genv.symbol_address' genv i ofs = Some (Eval (Vptr b ofs)) /\
               v = F (Eval (Vptr b ofs))).
Proof.
  intros until 0.
  case_eq ((Genv.symbol_address' genv0 i ofs)).
  - simpl. intros. inv H0. apply Genv.symbol_address'_ptr in H.
    destruct H. exists x ; intuition congruence.
  - simpl ; congruence.
Qed.
  
Lemma symbol_address'_option_map_has_type :
forall (A V : Type) (genv:Genv.t A V) i i0 v F
  (FTYPE : forall e, Val.has_type e Tint -> Val.has_type (F e) Tint),
  option_map F (Genv.symbol_address' genv i i0) = Some v ->
   Val.has_type v Tint.
Proof.
  intros.
  exploit option_map_symbol_address'_some ; eauto.
  intros (B & P & EQ).
  subst. apply FTYPE. simpl. auto.
Qed.


Lemma type_of_operation_sound:
  forall op vl sp v,
  op <> Omove ->
  Val.has_type_list vl (map styp_of_ast (fst (type_of_operation op))) ->
  Val.has_type sp Tint ->
  eval_operation genv sp op vl = Some v ->
  Val.has_type v (styp_of_ast (snd (type_of_operation op))).
Proof with (try exact I).
  intros op vl sp v nMove tArg tSp EOP.
  destruct op eqn:?; simpl in EOP; FuncInv; subst; simpl in *; auto;   intuition try constructor.
  - eapply symbol_address'_has_type ; eauto.
  - 
    destruct a; simpl in *; FuncInv; simpl in *; subst; simpl; intuition.
    + eapply symbol_address'_has_type ; eauto.
    + eapply symbol_address'_option_map_has_type ; eauto.
      simpl. intuition.
    + eapply symbol_address'_option_map_has_type ; eauto.
      simpl. intuition.
  - destruct c; repeat (destruct vl; repeat FuncInv; simpl in *; try congruence); subst; simpl; intuition; constructor.
Qed.

End SOUNDNESS.

(** * Manipulating and transforming operations *)

(** Recognition of move operations. *)

Definition is_move_operation
    (A: Type) (op: operation) (args: list A) : option A :=
  match op, args with
  | Omove, arg :: nil => Some arg
  | _, _ => None
  end.

Lemma is_move_operation_correct:
  forall (A: Type) (op: operation) (args: list A) (a: A),
  is_move_operation op args = Some a ->
  op = Omove /\ args = a :: nil.
Proof.
  intros until a. unfold is_move_operation; destruct op;
  try (intros; discriminate).
  destruct args. intros; discriminate.
  destruct args. intros. intuition congruence. 
  intros; discriminate.
Qed.

(** [negate_condition cond] returns a condition that is logically
  equivalent to the negation of [cond]. *)

Definition negate_condition (cond: condition): condition :=
  match cond with
  | Ccomp c => Ccomp(negate_comparison c)
  | Ccompu c => Ccompu(negate_comparison c)
  | Ccompimm c n => Ccompimm (negate_comparison c) n
  | Ccompuimm c n => Ccompuimm (negate_comparison c) n
  | Ccompf c => Cnotcompf c
  | Cnotcompf c => Ccompf c
  | Ccompfs c => Cnotcompfs c
  | Cnotcompfs c => Ccompfs c
  | Cmaskzero n => Cmasknotzero n
  | Cmasknotzero n => Cmaskzero n
  end.



Lemma negate_cmp_eqm:
  forall c e e0,
    same_eval (Val.cmp_bool (negate_comparison c) e e0)
                                  (Eunop OpNotbool Tint (Val.cmp_bool c e e0)).
Proof.
  red; intros; simpl; auto.
  intros; simpl; seval. 
  rewrite Int.negate_cmp.
  destruct (Int.cmp c i i0); simpl; auto.
Qed.

Lemma negate_cmpu_eqm:
  forall c e e0,
    same_eval (Val.cmpu_bool (negate_comparison c) e e0)
              (Eunop OpNotbool Tint (Val.cmpu_bool c e e0)).
Proof.
  intros; red; simpl; auto.
  intros; seval.
  rewrite Int.negate_cmpu.
  destruct (Int.cmpu c i i0); simpl; auto.
Qed.


Lemma dbl_negate_cmpf:
  forall c e e0,
    same_eval (Val.cmpf_bool c e e0)
              (Eunop OpNotbool Tint (Eunop OpNotbool Tint (Val.cmpf_bool c e e0))).
Proof.
  intros; red; simpl; auto.
  intros; seval. 
  destruct (Float.cmp c f f0); simpl; auto.
Qed.

Lemma dbl_negate_cmpfs:
  forall c e e0,
    same_eval (Val.cmpfs_bool c e e0) (Eunop OpNotbool Tint (Eunop OpNotbool Tint (Val.cmpfs_bool c e e0))).
Proof.
  intros; red; simpl; auto.
  intros; seval. 
  destruct (Float32.cmp c f f0); simpl; auto.
Qed.


Lemma dbl_negate_mskzero:
  forall e i,
    same_eval (Val.maskzero_bool e i)
              (Eunop OpNotbool Tint (Eunop OpNotbool Tint (Val.maskzero_bool e i))).
Proof.
    intros; red; simpl; auto.
    intros; seval. 
    destruct (Int.eq (Int.and i0 i)); simpl; auto.
Qed.

Lemma eval_negate_condition:
  forall cond vl,
    match eval_condition (negate_condition cond) vl, 
          option_map (Eunop OpNotbool Tint) (eval_condition cond vl) with
        Some e, Some f => same_eval e f
      | None, None => True
      | _, _ => False
    end.
Proof.
  intros. destruct cond; simpl;
  repeat (destruct vl; simpl; auto).
  apply negate_cmp_eqm.
  apply negate_cmpu_eqm.
  apply negate_cmp_eqm.
  apply negate_cmpu_eqm.
  reflexivity.
  apply dbl_negate_cmpf.
  reflexivity.
  apply dbl_negate_cmpfs.
  reflexivity.
  apply dbl_negate_mskzero.
Qed.

(** Shifting stack-relative references.  This is used in [Stacking]. *)

Definition shift_stack_addressing (delta: int) (addr: addressing) :=
  match addr with
  | Ainstack ofs => Ainstack (Int.add delta ofs)
  | _ => addr
  end.

Definition shift_stack_operation (delta: int) (op: operation) :=
  match op with
  | Olea addr => Olea (shift_stack_addressing delta addr)
  | _ => op
  end.

Lemma type_shift_stack_addressing:
  forall delta addr, type_of_addressing (shift_stack_addressing delta addr) = type_of_addressing addr.
Proof.
  intros. destruct addr; auto. 
Qed.

Lemma type_shift_stack_operation:
  forall delta op, type_of_operation (shift_stack_operation delta op) = type_of_operation op.
Proof.
  intros. destruct op; auto. simpl. decEq. apply type_shift_stack_addressing. 
Qed.

Lemma eval_shift_stack_addressing:
  forall F V (ge: Genv.t F V) sp addr vl delta,
    match eval_addressing ge sp (shift_stack_addressing delta addr) vl,
          eval_addressing ge (Val.add sp (Eval (Vint delta))) addr vl with
        Some e, Some f => same_eval e f
      | None, None => True
      | _, _ => False
    end.
Proof.
  intros.
  destruct addr; simpl; auto; destruct vl; simpl; auto;
  repeat (try destruct vl; simpl; auto; try reflexivity).
  - destruct (Genv.symbol_address' ge i i0) eqn:?; simpl; auto.  reflexivity.
  - destruct (Genv.symbol_address' ge i i0) eqn:?; simpl; auto.  reflexivity.
  - destruct (Genv.symbol_address' ge i0 i1) eqn:?; simpl; auto. reflexivity.
  - red; simpl; intros; auto.
    seval; sint.
Qed.

Lemma eval_shift_stack_operation:
  forall F V (ge: Genv.t F V) sp op vl delta,
    match eval_operation ge sp (shift_stack_operation delta op) vl,
          eval_operation ge (Val.add sp (Eval (Vint delta))) op vl with
        Some e, Some f => same_eval e f
      | None, None => True
      | _, _ => False
    end.
Proof.
  intros.
  destruct op; simpl; auto;
          try (destruct vl; simpl; auto; try reflexivity;
               destruct vl; simpl; auto; try reflexivity;
               destruct vl; simpl; auto; try reflexivity;
               destruct vl; simpl; auto; try reflexivity;
               apply eval_shift_stack_addressing); try reflexivity.
  unfold Genv.symbol_address'.
  des (Genv.find_symbol ge i).
  des vl. des vl.
  apply eval_shift_stack_addressing.
  destruct (eval_condition c vl); try reflexivity; auto.
Qed.

(** Offset an addressing mode [addr] by a quantity [delta], so that
  it designates the pointer [delta] bytes past the pointer designated
  by [addr].  On PowerPC and ARM, this may be undefined, in which case
  [None] is returned.  On IA32, it is always defined, but we keep the
  same interface. *)

Definition offset_addressing_total (addr: addressing) (delta: int) : addressing :=
  match addr with
  | Aindexed n => Aindexed (Int.add n delta)
  | Aindexed2 n => Aindexed2 (Int.add n delta)
  | Ascaled sc n => Ascaled sc (Int.add n delta)
  | Aindexed2scaled sc n => Aindexed2scaled sc (Int.add n delta)
  | Aglobal s n => Aglobal s (Int.add n delta)
  | Abased s n => Abased s (Int.add n delta)
  | Abasedscaled sc s n => Abasedscaled sc s (Int.add n delta)
  | Ainstack n => Ainstack (Int.add n delta)
  end.

Definition offset_addressing (addr: addressing) (delta: int) : option addressing :=
  Some(offset_addressing_total addr delta).

Lemma eval_offset_addressing_total:
  forall (F V: Type) (ge: Genv.t F V) sp addr args delta v,
  eval_addressing ge sp addr args = Some v ->
  exists e,
    eval_addressing ge sp (offset_addressing_total addr delta) args = Some e /\
    same_eval e (Val.add v (Eval (Vint delta))).
Proof.
  intros. destruct addr; simpl in *; FuncInv; subst;
   try (eexists; split; eauto; (red; simpl; intros; auto); seval; sint).
  - unfold Genv.symbol_address' in *.
    des (Genv.find_symbol ge i).
    eexists; split; eauto; red; intros;  inv H; simpl; sint. 
  - unfold Genv.symbol_address' in *.
    des (Genv.find_symbol ge i).
    eexists; split; eauto; red; intros; inv H; simpl; seval; sint. 
  - unfold Genv.symbol_address' in *.
    des (Genv.find_symbol ge i0).
    eexists; split; eauto; red; intros; inv H; simpl; seval; sint. 
Qed.

Lemma eval_offset_addressing:
  forall (F V: Type) (ge: Genv.t F V) sp addr args delta addr' v,
  offset_addressing addr delta = Some addr' ->
  eval_addressing ge sp addr args = Some v ->
  exists e,
    eval_addressing ge sp addr' args = Some e /\
    same_eval e (Val.add v (Eval (Vint delta))).
Proof.
  intros. unfold offset_addressing in H; inv H. 
  eapply eval_offset_addressing_total; eauto.
Qed.

(** Operations that are so cheap to recompute that CSE should not factor them out. *)

Definition is_trivial_op (op: operation) : bool :=
  match op with
  | Omove => true
  | Ointconst _ => true
  | Olea (Aglobal _ _) => true
  | Olea (Ainstack _) => true
  | _ => false
  end.

(** Operations that depend on the memory state. *)

Definition op_depends_on_memory (op: operation) : bool :=
  match op with
  | Ocmp (Ccompu _) => true
  | _ => false
  end.

Lemma op_depends_on_memory_correct:
  forall (F V: Type) (ge: Genv.t F V) sp op args,
  op_depends_on_memory op = false ->
  eval_operation ge sp op args = eval_operation ge sp op args.
Proof.
  auto. (* intros until m2. destruct op; simpl; try congruence. *)
  (* destruct c; simpl; try congruence.  *)
Qed.

(** * Invariance and compatibility properties. *)

(** [eval_operation] and [eval_addressing] depend on a global environment
  for resolving references to global symbols.  We show that they give
  the same results if a global environment is replaced by another that
  assigns the same addresses to the same symbols. *)

Section GENV_TRANSF.

Variable F1 F2 V1 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.
Hypothesis agree_on_symbols:
  forall (s: ident), Genv.find_symbol ge2 s = Genv.find_symbol ge1 s.

Lemma eval_addressing_preserved:
  forall sp addr vl,
  eval_addressing ge2 sp addr vl = eval_addressing ge1 sp addr vl.
Proof.
  intros.
  unfold eval_addressing, Genv.symbol_address'; destruct addr; try rewrite agree_on_symbols;
  reflexivity.
Qed.

Lemma eval_operation_preserved:
  forall sp op vl,
  eval_operation ge2 sp op vl = eval_operation ge1 sp op vl.
Proof.
  intros.
  unfold eval_operation; destruct op; auto.
  unfold Genv.symbol_address'. rewrite agree_on_symbols. auto.
  apply eval_addressing_preserved.
Qed.

End GENV_TRANSF.

(** Compatibility of the evaluation functions with value injections. *)

Section EVAL_COMPAT.

Variable F V: Type.
Variable genv: Genv.t F V.
Variable f: meminj.
Variable ei: meminj -> expr_sym -> expr_sym -> Prop.
Hypothesis wf: wf_inj ei.

Hypothesis symbol_address_inj: 
  forall id ofs b ofs',
    Genv.symbol_address' genv id ofs = Some (Eval (Vptr b ofs')) ->
    f b = Some (b,0).
    (* Val.expr_inject p f (Genv.symbol_address genv id ofs) (Genv.symbol_address genv id ofs). *)

Variable m1: mem.
Variable m2: mem.

Hypothesis valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.valid_pointer m1 b1 (Int.unsigned ofs) = true ->
  Mem.valid_pointer m2 b2 (Int.unsigned (Int.add ofs (Int.repr delta))) = true.

Hypothesis weak_valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Int.unsigned ofs) = true ->
  Mem.weak_valid_pointer m2 b2 (Int.unsigned (Int.add ofs (Int.repr delta))) = true.

Hypothesis weak_valid_pointer_no_overflow:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Int.unsigned ofs) = true ->
  0 <= Int.unsigned ofs + Int.unsigned (Int.repr delta) <= Int.max_unsigned.

Hypothesis valid_different_pointers_inj:
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m1 b1 (Int.unsigned ofs1) = true ->
  Mem.valid_pointer m1 b2 (Int.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Int.unsigned (Int.add ofs1 (Int.repr delta1)) <> Int.unsigned (Int.add ofs2 (Int.repr delta2)).

Ltac InvInject :=
  match goal with
  | [ H: val_inject _ (Vint _) _ |- _ ] =>
      inv H; InvInject
  | [ H: val_inject _ (Vfloat _) _ |- _ ] =>
      inv H; InvInject
  | [ H: val_inject _ (Vptr _ _) _ |- _ ] =>
      inv H; InvInject
  | [ H: val_list_inject _ nil _ |- _ ] =>
      inv H; InvInject
  | [ H: val_list_inject _ (_ :: _) _ |- _ ] =>
      inv H; InvInject
  | _ => idtac
  end.


Ltac invInj :=
  repeat match goal with
             H: list_ei ?ei ?f (_::_) _ |- _ => inv H
           | H: list_ei ?ei ?f nil _ |- _ => inv H
         end.




Lemma eval_condition_inj:
  forall cond vl1 vl2 b,
    list_ei ei f vl1 vl2 ->
    eval_condition cond vl1 = Some b ->
    exists b1, 
      eval_condition cond vl2 = Some b1 /\ ei f b b1.
Proof.
  intros. destruct cond; simpl in H0; FuncInv; invInj; simpl; auto;
  unfold Val.cmp_bool, Val.cmpu_bool, Val.maskzero_bool; inv wf; TrivialExists; eauto 6.
Qed.

Lemma eval_addressing_inj:
  forall addr sp1 vl1 sp2 vl2 v1,
    ei f sp1 sp2 ->
    list_ei ei f vl1 vl2 ->
    eval_addressing genv sp1 addr vl1 = Some v1 ->
    exists v2, eval_addressing genv sp2 addr vl2 = Some v2 /\ ei f v1 v2.
Proof.
  intros. destruct addr; simpl in H1; simpl; FuncInv; invInj; TrivialExists;
          inv wf; eauto 6;
          destr;  TrivialExists.
  -
    exploit Genv.symbol_address'_ptr; eauto.
    intros (b & BEQ) ; subst.
    apply vi_ei; simpl.
    unfold Val.inj_ptr.
    erewrite (symbol_address_inj); eauto.
    rewrite Int.add_zero; auto.
  - exploit option_map_symbol_address'_some; eauto.
    intros (B & GS & EQ).
    exists (Val.add b (Eval (Vptr B i0))) ; repeat split ; auto.
    rewrite GS. reflexivity.
    subst.
    apply ei_binop; auto. apply vi_ei; simpl.
    unfold Val.inj_ptr.
    erewrite (symbol_address_inj); eauto.
    rewrite Int.add_zero; auto.
  -
    exploit option_map_symbol_address'_some; eauto.
    intros (B & GS & EQ).
    rewrite GS in *. subst.
    exists (Val.add (Val.mul b (Eval (Vint i))) (Eval (Vptr B i1))) ; repeat split ; auto.
    repeat apply ei_binop; auto.
    apply vi_ei; simpl.
    unfold Val.inj_ptr.
    erewrite (symbol_address_inj); eauto.
    rewrite Int.add_zero; auto.
Qed.

Ltac inv_expr_inject:= invInj.

Lemma eval_operation_inj:
  forall op sp1 vl1 sp2 vl2 v1,
    ei f sp1 sp2 ->
    list_ei ei f vl1 vl2 ->
    eval_operation genv sp1 op vl1  = Some v1 ->
    exists v2, eval_operation genv sp2 op vl2 = Some v2 /\ ei f v1 v2.
Proof.
  intros.
  destruct op; simpl in H1; simpl; FuncInv; invInj; TrivialExists; inv wf; eauto 6.
  -
    exploit Genv.symbol_address'_ptr; eauto.
    intros (b & BEQ) ; subst.
    apply vi_ei; simpl.
    unfold Val.inj_ptr.
    erewrite (symbol_address_inj); eauto.
  - eapply eval_addressing_inj; eauto. 
  - exploit eval_condition_inj; eauto.
Qed.

End EVAL_COMPAT.

(** Compatibility of the evaluation functions with the ``is less defined'' relation over values. *)

Ltac myinv :=
  repeat match goal with
           | H : list_forall2 _ (_::_) _ |- _ => inv H
           | H : list_forall2 _ nil _ |- _ => inv H
           | H : context [match ?v with _ => _ end] |- _ => des v
           | |- exists v, Some ?V = Some v /\ _ => exists V; split; auto
           | H : Some _ = Some _ |- _ => inv H
           | H : None = Some _ |- _ => inv H
           | H : Some _ = None |- _ => inv H
         end.


Ltac ld' H :=
  repeat
    ((apply (mr_unop _ H); auto)
       ||
       (apply (mr_binop _ H); auto)
       || (apply (mr_refl _ H))).

Ltac ld :=
  match goal with
      H: wf_mr ?mr |- _ => ld' H
  end.
  

Section EVAL_LESSDEF.

Variable F V: Type.
Variable genv: Genv.t F V.

(* Lemma list_lessdef_list_expr_inject: *)
(*   forall a b, *)
(*     Val.lessdef_list a b <-> Val.expr_list_inject p (fun b => Some (b,0)) a b. *)
(* Proof. *)
(*   split; induction 1; constructor. *)
(*   apply Mem.expr_inject_lessdef; auto. *)
(*   auto. *)
(*   apply Mem.expr_inject_lessdef; auto. *)
(*   auto. *)
(* Qed. *)

Variable mr : expr_sym -> expr_sym -> Prop.
Hypothesis wf: wf_mr mr.
                                        

Lemma eval_condition_rel:
  forall cond vl1 vl2 b,
    list_forall2 mr vl1 vl2 ->
    (* mem_rel mr m1 m2 -> *)
    eval_condition cond vl1  = Some b ->
    exists b1, 
      eval_condition cond vl2 = Some b1 /\
      mr b b1.
Proof.
  intros.
  des cond; myinv; ld.
Qed.


Lemma eval_addressing_rel:
  forall sp addr vl1 vl2 v1,
    list_forall2 mr vl1 vl2 ->
    eval_addressing genv sp addr vl1 = Some v1 ->
    exists v2, eval_addressing genv sp addr vl2 = Some v2 /\ mr v1 v2.
Proof.
  intros.
  des addr; myinv ; ld.
  - exists v1; split ; auto; ld.
  -  exploit option_map_symbol_address'_some ; eauto.
     intros (b & SYMB & EQ).
     rewrite SYMB. simpl. subst. myinv ; ld.
  -   exploit option_map_symbol_address'_some ; eauto.
     intros (b & SYMB & EQ).
     rewrite SYMB. simpl. subst. myinv ; ld.
Qed.
  
  
Lemma eval_operation_rel:
  forall sp op vl1 vl2 v1 ,
    list_forall2 mr vl1 vl2 ->
    (* mem_rel mr m1 m2 -> *)
    eval_operation genv sp op vl1 = Some v1 ->
    exists v2, eval_operation genv sp op vl2 = Some v2 /\ mr v1 v2.
Proof.
  intros.
  des op; myinv ; try solve [ld].
  - auto.
  - rewrite H0. myinv ; ld.
  - eapply eval_addressing_rel; eauto.
  - eapply eval_condition_rel; eauto.
Qed.

End EVAL_LESSDEF.

(** Compatibility of the evaluation functions with memory injections. *)

Section EVAL_INJECT.

Variable F V: Type.
Variable genv: Genv.t F V.
Variable f: meminj.
Variable ei : meminj -> expr_sym -> expr_sym -> Prop.
Hypothesis wf: wf_inj ei.
Hypothesis globals: meminj_preserves_globals genv f.
Variable sp1: block.
Variable sp2: block.
Variable delta: Z.
Hypothesis sp_inj: f sp1 = Some(sp2, delta).

Remark symbol_address_inject:
  forall id ofs, val_inject f (Genv.symbol_address genv id ofs) (Genv.symbol_address genv id ofs).
Proof.
  intros. unfold Genv.symbol_address. destruct (Genv.find_symbol genv id) eqn:?; auto.
  exploit (proj1 globals); eauto. intros. 
  econstructor; eauto. rewrite Int.add_zero; auto.
Qed.

Lemma sp_inject:
  forall b1 ofs b2 delta0, 
    f b1 = Some (b2, delta0) ->
    ei f (Eval (Vptr b1 ofs))
       (Eval (Vptr b2 (Int.add ofs (Int.repr delta0)))).
Proof.
  intros.
  inv wf. apply vi_ei; simpl.
  unfold Val.inj_ptr. rewrite H. eauto.
Qed.

Lemma eval_condition_inject:
  forall cond vl1 vl2 b,
    list_ei ei f vl1 vl2 ->
    (* Mem.inject ei f m1 m2 -> *)
    eval_condition cond vl1 = Some b ->
    exists b1, eval_condition cond vl2 = Some b1 /\ ei f b b1.
Proof.
  intros. generalize (eval_condition_inj (f:=f) wf cond H (b:=b) H0); eauto. 
Qed.

Inductive opt_same_eval : option expr_sym -> option expr_sym -> Prop :=
| opt_same_eval_None : opt_same_eval None None
| opt_same_eval_Some : forall e e' (OPTSAME : same_eval e e'), opt_same_eval (Some e) (Some e').


Instance EquiOptSameEval : Equivalence opt_same_eval.
Proof.
  constructor.
  - unfold Reflexive.
    intros. destruct x ; constructor.
    reflexivity.
  - unfold Symmetric.
    intros.
    inv H; constructor. rewrite OPTSAME ; reflexivity.
  - unfold Transitive.
    intros.
    inv H ; inv H0 ; constructor.
    rewrite OPTSAME. auto.
Qed.

Lemma eval_addressing_mod_norm:
  forall addr vl a b
         (EQM: same_eval a b),
    opt_same_eval (eval_addressing genv a addr vl) (eval_addressing genv b addr vl).
Proof.
  intros.
  destruct addr; simpl; try reflexivity.
  destruct vl; constructor.
  red; intros; simpl; rewrite EQM; reflexivity.
Qed.

Add Parametric Morphism
  : (eval_addressing  genv) with
    signature same_eval ==> @eq addressing ==> (@eq (list expr_sym)) ==> opt_same_eval as eval_addressing_same_eval.
Proof.
  intros.
  apply eval_addressing_mod_norm ; auto.
Qed.

Lemma eval_addressing_inject:
  forall addr vl1 vl2 v1,
    list_ei ei f vl1 vl2 ->
    eval_addressing genv (Eval (Vptr sp1 Int.zero)) addr vl1 = Some v1 ->
    exists v2 e, 
      eval_addressing genv (Eval (Vptr sp2 Int.zero)) (shift_stack_addressing (Int.repr delta) addr) vl2 = Some v2
      /\ same_eval v2 e         
      /\ ei f v1 e.
Proof.
  intros.
  
  assert (exists v2,
            eval_addressing genv (Eval (Vptr sp2 (Int.repr delta)))  addr vl2 = Some v2 /\
            ei f v1 v2).
  {
    eapply eval_addressing_inj with (sp1 := Eval (Vptr sp1 Int.zero)); eauto.
    inv globals. unfold Genv.symbol_address'; intros.
    erewrite H1 with (id:=id); eauto.     destruct (Genv.find_symbol genv id); simpl in *; intuition try congruence. 
    generalize (sp_inject Int.zero sp_inj).
    rewrite Int.add_zero_l. auto.
  }
  destruct H1 as [v2 [H1 H2]].
 
  generalize (eval_shift_stack_addressing genv (Eval (Vptr sp2 Int.zero)) addr vl2 (Int.repr delta)).
  generalize (eval_addressing_mod_norm addr vl2).
  intro A; specialize (A (Eval (Vptr sp2 (Int.repr delta))) (Val.add (Eval (Vptr sp2 Int.zero)) (Eval (Vint (Int.repr delta))))).
  trim A.
  red; simpl; intros; sint. rewrite Int.add_zero; auto.
  revert A. rewrite H1.
  destruct ( eval_addressing genv
       (Val.add (Eval (Vptr sp2 Int.zero)) (Eval (Vint (Int.repr delta))))
       addr vl2) eqn:?; simpl; try intuition congruence.
  intro.
  destruct (eval_addressing genv (Eval (Vptr sp2 Int.zero)) (shift_stack_addressing (Int.repr delta) addr) vl2); try intuition congruence.
  exists e0. exists v2.
  split; auto. split; auto. inv A.
  rewrite OPTSAME; rewrite H3. reflexivity.
  intros. inv A.
Qed.


Lemma eval_operation_mod_norm:
  forall vl a b op
         (EQM: same_eval a b), opt_same_eval (eval_operation genv a op vl) (eval_operation genv b op vl).
Proof.
  intros.
  destruct op ; simpl; try reflexivity.
  rewrite EQM.
  reflexivity.
Qed.

Add Parametric Morphism
  : (eval_operation  genv) with
    signature same_eval ==> @eq operation ==> (@eq (list expr_sym)) ==> opt_same_eval as eval_operation_same_eval.
Proof.
  intros.
  apply eval_operation_mod_norm; auto.
Qed.
  
  
Lemma eval_operation_inject:
  forall op vl1 vl2 v1,
    list_ei ei f vl1 vl2 ->
    (* Mem.inject ei f m1 m2 -> *)
    eval_operation genv (Eval (Vptr sp1 Int.zero)) op vl1 = Some v1 ->
    exists v2 e,
      eval_operation genv (Eval (Vptr sp2 Int.zero))
                     (shift_stack_operation (Int.repr delta) op) vl2 = Some e
      /\ same_eval v2 e         
     /\ ei f v1 v2.
Proof.
  intros. 
  assert (exists v2,
            eval_operation genv
                           (Eval (Vptr sp2 (Int.repr delta)))
                           op vl2  = Some v2 /\
            ei f v1 v2).
  {
    eapply eval_operation_inj with (sp1:= Eval (Vptr sp1 Int.zero)); eauto.
    inv globals. intros; apply H1 with (id:=id); eauto.
    unfold Genv.symbol_address' in H3; destruct (Genv.find_symbol genv id); inv H3; auto.
    replace (Int.repr delta) with (Int.add Int.zero (Int.repr delta)).
    apply sp_inject. auto.
    apply Int.add_zero_l.
  }
  destruct H1 as [v2 [A B]].
  generalize (eval_shift_stack_operation genv (Eval (Vptr sp2 Int.zero)) op vl2 (Int.repr delta)).
  generalize (eval_operation_mod_norm vl2).
  intro U; specialize (U (Eval (Vptr sp2 (Int.repr delta)))
                                      (Ebinop OpAdd Tint Tint (Eval (Vptr sp2 Int.zero))
                                              (Eval (Vint (Int.repr delta)))) op); eauto.
  trim U.
  - red; simpl; intros. sint. 
    rewrite Int.add_zero. auto.
  -
    revert U. rewrite A.
    destruct (eval_operation genv
       (Ebinop OpAdd Tint Tint (Eval (Vptr sp2 Int.zero))
               (Eval (Vint (Int.repr delta)))) op vl2 ) eqn:?; try intuition congruence.
    intros. inv U.
    unfold Val.add in H1. rewrite Heqo in H1.
    destruct (eval_operation genv (Eval (Vptr sp2 Int.zero))
           (shift_stack_operation (Int.repr delta) op) vl2) eqn:?; try intuition congruence.
    exists v2; exists e0.  split; eauto.
    split; auto.
    rewrite H1. auto.
    intros. inv U.
Qed.

End EVAL_INJECT.



Ltac Inv :=   repeat match goal with
           | H : match ?vl with _ => _ end = Some _ |- _ =>
             destruct vl; try discriminate
           | H: Some _ = Some _ |- _ => inv H
           | H: list_forall2 _ (_ :: _) _ |- _ => inv H
           | H: list_forall2 _ nil _ |- _ => inv H
           | H: Val.lessdef_list (_::_) _ |- _ => inv H
           | H: Val.lessdef_list nil _ |- _ => inv H
     
         end. 


Lemma eval_addressing_se:
  forall F V (genv: Genv.t F V) sp  a vl1 vl2 v1 (* m1 m2 *)
         (LF: Val.lessdef_list vl1 vl2)
         (* (ME: mem_lessdef m1 m2) *)
         (EOP : eval_addressing genv sp a vl1 = Some v1),
  exists v2,
    eval_addressing genv sp a vl2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros F V genv sp0 a vl1 vl2 v1 LF  EOP.
  destruct a ; simpl in *; Inv; TrivialExists;   repeat (apply Val.lessdef_binop; auto).
  - 
    exploit option_map_symbol_address'_some ; eauto.
    intros (B & GE & EQ).
    exists (Val.add v2 (Eval (Vptr B i0))).
    rewrite GE. subst.
    split ;auto.
    repeat (apply Val.lessdef_binop; auto).    
  - exploit option_map_symbol_address'_some ; eauto.
    intros (B & GE & EQ).
    exists (Val.add (Val.mul v2 (Eval (Vint i))) (Eval (Vptr B i1))).
    rewrite GE. subst.
    split ;auto.
    repeat (apply Val.lessdef_binop; auto).    
Qed.

Lemma eval_condition_se:
  forall F V (genv: Genv.t F V) c vl1 vl2 v1 (* m1 m2 *)
         (LF: Val.lessdef_list vl1 vl2)
         (* (ME: mem_lessdef m1 m2) *)
         (EOP : eval_condition c vl1 = Some v1),
  exists v2,
    eval_condition c vl2 = Some v2 /\
    Val.lessdef v1 v2.
Proof.
  intros F V genv c vl1 vl2 v1 LF EOP.
  destruct c; simpl in *; Inv; eexists; split; eauto;
  repeat (apply Val.lessdef_binop || apply Val.lessdef_unop || auto).
Qed.

Lemma eval_operation_se:
  forall F V (genv: Genv.t F V) sp op vl1 vl2 v1 (* m1 m2 *)
         (LF: Val.lessdef_list vl1 vl2)
         (* (ME: mem_lessdef m1 m2) *)
         (EOP: eval_operation genv sp op vl1 = Some v1),
  exists v2,
    eval_operation genv sp op vl2 = Some v2 /\
    Val.lessdef v1 v2.
Proof.
  intros F V genv sp0 op vl1 vl2 v1 LF EOP.
  destruct op; simpl in *; Inv;
  try (eexists; split; eauto;
       repeat (apply Val.lessdef_binop || apply Val.lessdef_unop || auto);
       fail).
  eapply eval_addressing_se; eauto.
  eapply eval_condition_se; eauto.
Qed.

Lemma eval_operation_inject' :
forall (F V : Type) (genv : Genv.t F V) (f : meminj),  
  meminj_preserves_globals genv f ->
  forall (sp1 sp2 : block) (delta : Z),
    f sp1 = Some (sp2, delta) ->
    forall (op : operation) (vl1 vl2 : list expr_sym) 
      (v1 : expr_sym) (m1 m2 : mem),
      expr_list_inject f vl1 vl2 ->
       (* Mem.inject expr_inj_se f m1 m2 -> *)
       eval_operation genv (Eval (Vptr sp1 Int.zero)) op vl1  = Some v1 ->
       exists v2 : expr_sym,
         eval_operation genv (Eval (Vptr sp2 Int.zero))
           (shift_stack_operation (Int.repr delta) op) vl2 = 
         Some v2 /\ expr_inj_se f v1 v2.
Proof.
  clear. intros.
  exploit eval_operation_inject; eauto.
  eapply expr_list_inject_list_ei; eauto.
  intros [v2 [e [A [B C]]]].
  exists e; split; eauto.
  eapply expr_inj_se_se; eauto.
Qed.


Lemma eval_addressing_inject':
  forall (F V : Type) (genv : Genv.t F V) (f : meminj),
       meminj_preserves_globals genv f ->
       forall (sp1 sp2 : block) (delta : Z),
       f sp1 = Some (sp2, delta) ->
       forall (addr : addressing) (vl1 vl2 : list expr_sym)
         (v1 : expr_sym),
         expr_list_inject f vl1 vl2 ->
         eval_addressing genv (Eval (Vptr sp1 Int.zero)) addr vl1 = Some v1 ->
       exists v2 : expr_sym,
         eval_addressing genv (Eval (Vptr sp2 Int.zero))
           (shift_stack_addressing (Int.repr delta) addr) vl2 = 
         Some v2 /\ expr_inj_se f v1 v2.
Proof.
  intros.
  exploit eval_addressing_inject; eauto.
  eapply expr_list_inject_list_ei; eauto.
  intros [v2 [e [A [B C]]]]; eexists; split; eauto.
  eapply expr_inj_se_se; eauto. congruence.
Qed.


Ltac inv_se :=
  repeat match goal with
           | H: match ?vl with _ => _ end = Some _ |- _ => des vl
           | H: Some _ = Some _ |- _ => inv H
           | H: None = Some _ |- _ => inv H
           | H : list_forall2 _ (_ :: _) _ |- _=> inv H
           | H : list_forall2 _ nil _  |- _ => inv H
           | |- exists _, _ = _ /\ _  =>
             eexists; split; eauto;
             repeat match goal with
                      | |- same_eval ?a ?a => reflexivity
                      | |- same_eval _ _ => apply unop_same_eval; auto
                      | |- same_eval _ _ => apply binop_same_eval; auto
                    end; fail
         end.

Lemma eval_addressing_se':
  forall F V (ge: Genv.t F V) sp addr vl v,
    eval_addressing ge sp addr vl = Some v ->
    forall vl',
      list_forall2 same_eval vl vl' ->
      exists v',
        eval_addressing ge sp addr vl' = Some v' /\
        same_eval v v'.
Proof.
  des addr; inv_se.
  -  exploit option_map_symbol_address'_some ; eauto.
    intros (B & GE & EQ).
    exists (Val.add b1 (Eval (Vptr B i0))).
    rewrite GE. subst.
    split ;auto. repeat apply binop_same_eval; auto. reflexivity.
  -  exploit option_map_symbol_address'_some ; eauto.
    intros (B & GE & EQ).
    exists (Val.add (Val.mul b1 (Eval (Vint i))) (Eval (Vptr B i1))).
    rewrite GE. subst.
    split ;auto. repeat apply binop_same_eval; auto. reflexivity. reflexivity.
Qed. 

Lemma eval_condition_se':
  forall c vl v,
    eval_condition c vl = Some v ->
    forall vl',
      list_forall2 same_eval vl vl' ->
      (* mem_rel same_eval m m' -> *)
      exists v',
        eval_condition c vl' = Some v' /\
        same_eval v v'.
Proof.
  des c; inv_se.
Qed.

Lemma eval_operation_se':
  forall F V (ge: Genv.t F V) sp o vl v,
    eval_operation ge sp o vl = Some v ->
    forall vl' ,
      list_forall2 same_eval vl vl' ->
      (* mem_rel same_eval m m' -> *)
      exists v',
        eval_operation ge sp o vl' = Some v' /\
        same_eval v v'.
Proof.
  des o; inv_se.
  eapply eval_addressing_se'; eauto.
  eapply eval_condition_se'; eauto.
Qed.
