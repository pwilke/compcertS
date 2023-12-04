Require Import Coqlib.
Require Import Axioms.
Require Import Bool.
Require Import ZArith.
Require Import Psatz.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Utf8.
Require Import Values_symbolictype.
Open Scope Z_scope.
Open Scope list_scope.
Require Import IntFacts.

Section Ops.
  (** This section defines a mapping from symbolic expressions operators to
      functions on values, so that we can evaluate symbolic expressions (see
      [eSexpr] below) *)

  (** The type of concrete memories, i.e. mappings from block identifier to
      32-bit addresses. *)

  Definition mem := block -> int.

  Definition boolval_t (t : styp) := match t with Tint => Val.boolval | _ => fun _ => Vundef end.

  Definition notbool_t (t : styp) := match t with Tint => Val.notbool | _ => fun _ => Vundef end.

  Definition neg_t (t:styp) :=
    match t with
      | Tint   => Val.neg
      | Tlong  => Val.negl
      | Tfloat => Val.negf
      | Tsingle => Val.negfs
    end.

  Definition and_t (t t':styp) :=
    match t, t' with
      | Tint, Tint  => Val.and
      | Tlong, Tlong => Val.andl
      |  _ , _    => (fun _ _ => Vundef)
    end.

  Definition or_t (t t':styp) :=
    match t , t' with
      | Tint, Tint  => Val.or
      | Tlong , Tlong => Val.orl
      |  _ , _    => (fun _ _ => Vundef)
    end.

  Definition xor_t (t t':styp) :=
    match t , t' with
      | Tint, Tint   => Val.xor
      | Tlong, Tlong  => Val.xorl
      |  _, _      => (fun _ _ => Vundef)
    end.

  Definition not_t (t:styp) :=
    match t with
      | Tint  => Val.notint
      | Tlong => Val.notl
      |  _     => (fun _ => Vundef)
    end.

  Definition add_t (t t':styp) :=
    match t , t' with
      | Tint, Tint  => Val.add
      | Tlong, Tlong  => Val.addl
      | Tfloat , Tfloat  => Val.addf
      | Tsingle, Tsingle  => Val.addfs
      | _, _ => fun _ _ => Vundef
    end.

  Definition sub_t (t t':styp) :=
    match t , t' with
      | Tint, Tint  => Val.sub
      | Tlong, Tlong => Val.subl
      | Tfloat, Tfloat  => Val.subf
      | Tsingle, Tsingle  => Val.subfs
      | _, _ => fun _ _ => Vundef
    end.

  Definition mul_t (t t':styp) :=
    match t, t' with
      | Tint  , Tint   => Val.mul
      | Tlong , Tlong  => Val.mull
      | Tfloat  , Tfloat   => Val.mulf
      | Tsingle  , Tsingle   => Val.mulfs
      | _, _ => fun _ _ => Vundef
    end.

  Definition div_t (s:se_signedness) (t t': styp)  :=
    match s, t, t' with
      | SESigned, Tint, Tint  => fun v v' => Val.maketotal (Val.divs v v')
      | SESigned, Tlong, Tlong=> fun v v' => Val.maketotal (Val.divls v v')
      | SEUnsigned, Tint , Tint => fun v v' => Val.maketotal (Val.divu v v')
      | SEUnsigned, Tlong, Tlong => fun v v' => Val.maketotal (Val.divlu v v')
      | _,Tfloat, Tfloat  => Val.divf
      | _,Tsingle, Tsingle  => Val.divfs
      | _, _, _ => fun _ _ => Vundef
    end.

  Definition mod_t (s:se_signedness) (t t':styp) :=
    match s, t, t' with
      | SESigned, Tint, Tint  => fun v v' => Val.maketotal (Val.mods v v')
      | SESigned, Tlong, Tlong => fun v v' => Val.maketotal (Val.modls v v')
      | SEUnsigned, Tint, Tint  => fun v v' => Val.maketotal (Val.modu v v')
      | SEUnsigned, Tlong, Tlong => fun v v' => Val.maketotal (Val.modlu v v')
      |  _      , _ , _ => (fun _ _ => Vundef)
    end.
  
  Definition shr_t (s:se_signedness) (t t2:styp) :=
    match s, t, t2 with
      | SESigned, Tint, Tint  => Val.shr
      | SESigned, Tlong, Tint => Val.shrl
      | SEUnsigned, Tint, Tint  => Val.shru
      | SEUnsigned, Tlong, Tint => Val.shrlu
      |  _      , _ , _ => (fun _ _ => Vundef)
    end.

  Definition shl_t (t t2:styp) :=
    match t,t2 with
      | Tint,Tint  => Val.shl
      | Tlong,Tint => Val.shll
      | _,_ => (fun _ _ => Vundef)
    end.

  Definition cmpu_bool (c: comparison) (v1 v2: val): option bool :=
    match v1, v2 with
      | Vint n1, Vint n2 =>
        Some (Int.cmpu c n1 n2)
      |  _ , _ => None
    end.

  Definition cmp_t (s:se_signedness) (c:comparison) (t t':styp) :=
    match s, t, t' with
      | SESigned   , Tint    , Tint     => (fun x y => Val.of_optbool (Val.cmp_bool c x y))
      | SESigned   , Tlong   , Tlong    => (fun x y => Val.of_optbool (Val.cmpl_bool c x y))
      | SEUnsigned , Tint    , Tint     => (fun x y => Val.of_optbool (cmpu_bool c x y))
      | SEUnsigned , Tlong   , Tlong    => (fun x y => Val.of_optbool (Val.cmplu_bool c x y))
      |  _         , Tfloat  , Tfloat   => (fun x y => Val.of_optbool (Val.cmpf_bool c x y))
      |  _         , Tsingle , Tsingle  => (fun x y => Val.of_optbool (Val.cmpfs_bool c x y))
      | _, _, _ => fun _ _ => Vundef
    end.
  
  Definition zeroext_t (z:Z) (t:styp) :=
    match t with
      | Tint  => Val.zero_ext z
      | Tlong => (fun v => match v with Vlong l => Vlong (Int64.zero_ext z l) | _ => Vundef end)
      | _ => (fun _ => Vundef)
    end.

  Definition signext_t (z:Z) (t:styp) :=
    match t with
      | Tint  => Val.sign_ext z
      | Tlong => (fun v => match v with Vlong l => Vlong (Int64.sign_ext z l) | _ => Vundef end)
      | _ => (fun _ => Vundef)
    end.

  Definition shrx_t  (t t':styp) :=
    match t, t' with
      | Tint, Tint  => fun x y => Val.maketotal (Val.shrx x y)
      | _, _ => (fun _ _ => Vundef)
    end.

  Definition shr_carry_t  (t t':styp) :=
    match t, t' with
      | Tint, Tint  => Val.shr_carry 
      | _, _ => (fun _ _ => Vundef)
    end.

  Definition rolm_t (amount mask : int) (t:styp) :=
    match t with
      | Tint  => (fun x => Val.rolm x amount mask)
      | _ => (fun _ => Vundef)
    end.

  Definition ror_t (t t':styp) := 
    match t, t' with
      | Tint  , Tint   => Val.ror
      | _, _ => (fun _ _ => Vundef)
    end.

  Definition absf_t (t:styp) := 
    match t with
      | Tfloat  => Val.absf
      | Tsingle  => Val.absfs
      | _  => (fun _ => Vundef)
    end.

  Definition mull'_t (t t':styp) := 
    match t, t' with
      | Tint  , Tint   => Val.mull'
      | _, _ => (fun _ _ => Vundef)
    end.

  Definition mulh_t (s:se_signedness) (t t':styp) := 
    match t , t' with
      | Tint  , Tint   => 
        match s with
            SESigned => Val.mulhs
          | SEUnsigned => Val.mulhu
        end
      | _, _  => (fun _  _ => Vundef)
    end.

  Definition convert_t (from_s:se_signedness) (to_ts : styp * se_signedness) (from_t:styp) :=
    match (from_t, from_s), to_ts with
      | (Tint, _), (Tint, _) => fun x => match x with
                                             Vint i => Vint i
                                           | _ => Vundef
                                         end
      | (Tint,SESigned)   , ( Tfloat,_)  => fun x => Val.maketotal (Val.floatofint x)
      | (Tint,SEUnsigned) , ( Tfloat,_)  => fun x => Val.maketotal (Val.floatofintu x)
      | (Tint,SESigned), (Tlong, _ )   => Val.longofint
      | (Tint,SEUnsigned), (Tlong, _ )   => Val.longofintu
      | (Tint,SESigned)   , ( Tsingle,_)  => fun x => Val.singleoffloat (Val.maketotal (Val.floatofint x))
      | (Tint,SEUnsigned) , ( Tsingle,_)  => fun x => Val.singleoffloat (Val.maketotal (Val.floatofintu x))

      | (Tfloat, _) , (Tint,SESigned)   => fun x => Val.maketotal (Val.intoffloat x)
      | (Tfloat, _) , (Tint,SEUnsigned) => fun x => Val.maketotal (Val.intuoffloat x)
      | (Tfloat,_), (Tfloat, _)   => fun x => match x with
                                                  Vfloat f => Vfloat f
                                                | _ => Vundef
                                              end
      | (Tfloat,_) , (Tlong,SESigned)   => fun x => Val.maketotal (Val.longoffloat x)
      | (Tfloat,_) , (Tlong,SEUnsigned) => fun x => Val.maketotal (Val.longuoffloat x)
      | (Tfloat,_) , (Tsingle,_)       => Val.singleoffloat

      | (Tlong, _), (Tint, _) => Val.loword
      | (Tlong,SESigned)   , ( Tfloat,_)  => fun x => Val.maketotal (Val.floatoflong x)
      | (Tlong,SEUnsigned) , (Tfloat,_)  => fun x => Val.maketotal (Val.floatoflongu x)
      | (Tlong, _), (Tlong, _) => fun x => match x with
                                               Vlong i => Vlong i
                                             | _ => Vundef
                                           end
      | (Tlong, SESigned), (Tsingle,_) => fun x => Val.maketotal (Val.singleoflong x)
      | (Tlong, SEUnsigned), (Tsingle,_) => fun x => Val.maketotal (Val.singleoflongu x)

      | (Tsingle, _), (Tint, SEUnsigned) => (fun x => Val.maketotal (Val.intuofsingle x))
      | (Tsingle, _), (Tint, SESigned) => (fun x => Val.maketotal (Val.intofsingle x))
      | (Tsingle, _), (Tfloat, _) => Val.floatofsingle
      | (Tsingle, _), (Tlong, SEUnsigned) => (fun x => Val.maketotal (Val.longuofsingle x))
      | (Tsingle, _), (Tlong, SESigned) => (fun x => Val.maketotal (Val.longofsingle x))
      | (Tsingle, _), (Tsingle, _) => fun x => match x with
                                                   Vsingle s => Vsingle s
                                                 | _ => Vundef
                                               end
    end.
  
  Definition floatofwords_t (t t':styp) :=
    match t, t' with
      | Tint , Tint  => Val.floatofwords
      | _, _  => (fun _ _ => Vundef)
    end.

  Definition longofwords_t (t t':styp) :=
    match t, t' with
      | Tint , Tint  => Val.longofwords
      |   _ , _  => (fun _ _ => Vundef)
    end.

  Definition loword_t (t:styp) :=
    match t with
      | Tlong => Val.loword
      |   _    => fun  _ => Vundef
    end.

  Definition hiword_t (t:styp) :=
    match t with
      | Tlong => Val.hiword
      |   _    => fun  _ => Vundef
    end.

  Definition bitsofsingle_t (t:styp) :=
    match t with
      | Tsingle  =>
        fun v => match v with
                     Vsingle f => Vint (Float32.to_bits f)
                   | _ => Vundef
                 end
      | _ => fun _ => Vundef
    end.

  Definition bitsofdouble_t (t:styp) :=
    match t with
      | Tfloat  =>
        fun v => match v with
                     Vfloat f => Vlong (Float.to_bits f)
                   | _ => Vundef
                 end
      | _ => fun _ => Vundef
    end.

  Definition singleofbits_t (t:styp) :=
    match t with
      | Tint =>
        fun v => match v with
                     Vint n => Vsingle (Float32.of_bits n)
                   | _ => Vundef
                 end
      | _ => fun _ => Vundef
    end.

  Definition doubleofbits_t (t:styp) :=
    match t with
      | Tlong =>
        fun v => match v with
                     Vlong n => Vfloat (Float.of_bits n)
                   | _ => Vundef
                 end
      | _ => fun _ => Vundef
    end.


  Definition sub_overflow_t (t1 t2: styp) :=
    match t1, t2 with
        Tint, Tint => Val.sub_overflow
      | _, _=> fun _ _ => Vundef
    end.
  
  Section S.
    
    Variable m : mem.           (**r A concrete memory.  *)
    Variable env_mem : block -> int -> byte. (**r A ``undef'' environment. *)

    Definition fun_of_unop (u:unop_t) : (styp -> val -> val) :=
      match u with
        | OpBoolval => boolval_t
        | OpNotbool => notbool_t
        | OpNeg => neg_t
        | OpNot => not_t
        | OpZeroext z => zeroext_t z
        | OpSignext z => signext_t z
        | OpRolm i1 i2 => rolm_t i1 i2
        | OpAbsf => absf_t
        | OpConvert sg (ti,sg') => convert_t sg (ti,sg')
        | OpLoword => loword_t
        | OpHiword => hiword_t
        | OpSingleofbits => singleofbits_t
        | OpDoubleofbits => doubleofbits_t
        | OpBitsofsingle => bitsofsingle_t
        | OpBitsofdouble => bitsofdouble_t
      end.


    Definition fun_of_binop (b:binop_t) : (styp -> styp -> val -> val -> val) :=
      match b with
        | OpAnd => and_t
        | OpOr => or_t
        | OpXor => xor_t
        | OpAdd => add_t
        | OpSub => sub_t
        | OpMul => mul_t
        | OpMull' => mull'_t
        | OpMulh s => mulh_t s
        | OpShrx => shrx_t
        | OpShr_carry => shr_carry_t
        | OpRor => ror_t
        | OpFloatofwords => floatofwords_t
        | OpLongofwords => longofwords_t
        | OpDiv sg => div_t sg
        | OpMod sg => mod_t sg
        | OpCmp sg cmp => cmp_t sg cmp
        | OpShr sg => shr_t sg 
        | OpShl => shl_t
        | OpSubOverflow => sub_overflow_t
      end.

    
    
    (** Evaluation of symbolic expressions. *)

    Definition eSval (v:val) : val :=
      match v with
        | Vptr b  o => Vint (Int.add (m b) o)
        | _ => v
      end.

    Fixpoint eSexpr  (e : expr_sym) : val :=
      match e with
        | Eval v               => eSval v
        | Eundef p i           => Vint (Int.repr (Byte.unsigned (env_mem p i)))
        | Eunop u t e          => fun_of_unop u t (eSexpr e)
        | Ebinop b t1 t2 e1 e2 => fun_of_binop b t1 t2 (eSexpr e1) (eSexpr e2)
      end.


    (** Evaluation of symbolic expressions (à la Compcert, i.e. we don't transform pointers into integers). *)

    Fixpoint eSexprCC  (e : expr_sym) : val :=
      match e with 
        | Eval v               => v
        | Eundef p i           => Vundef
        | Eunop u t e          => fun_of_unop u t (eSexprCC e)
        | Ebinop b t1 t2 e1 e2 => fun_of_binop b t1 t2 (eSexprCC e1) (eSexprCC e2)
      end.


    
  End S.

End Ops.

Ltac sint :=
  repeat
    match goal with
      | |- Vint _ = Vint _ => f_equal
      | |- Vptr _ _ = Vptr _ _ => f_equal
      | |- Int.add ?i _ = Int.add ?i _ => f_equal
      | |- Int.add _ ?i = Int.add _ ?i => f_equal
      | |- Int.add ?i ?j = Int.add ?j ?i => apply Int.add_commut
      | |- context [ Int.add (Int.add _ _) _] => rewrite Int.add_assoc
    end.



  Lemma fun_of_unop_undef:
    forall u t,
      fun_of_unop u t Vundef = Vundef.
  Proof.
    intros; des u; des t;
    des s; des a; des b.
  Qed.


  Lemma fun_of_binop_undef_l:
    forall b t1 t2 v,
      fun_of_binop b t1 t2 Vundef v = Vundef.
  Proof.
    intros; des b; des t1; des t2; des v; des s.
  Qed.
  
  Lemma fun_of_binop_undef_r:
    forall b t1 t2 v,
      fun_of_binop b t1 t2 v Vundef = Vundef.
  Proof.
    intros; des b; des t1; des t2; des v; des s.
  Qed.


  Lemma fun_of_unop_no_ptr:
    forall u s v,
      match v with
          Vptr b i =>
          match fun_of_unop u s v with
              Vptr b' i' => b = b'
            | _ => True
          end
        | _ =>
          match fun_of_unop u s v with
              Vptr _ _ => False
            | _ => True
          end
      end.
  Proof.
    des u; des v; des s;
    repeat match goal with
               |- context [Values.Val.of_bool ?b] => des b
             | |- context [convert_t ?sg (?t,?sg') ?t' ?v] =>
               unfold convert_t; des t; des sg'; des t'
             | |- context [ option_map _ ?v ] => des v
           end.
  Qed.

  Lemma fun_of_binop_no_ptr:
    forall u s s0 v v0,
      match v, v0, fun_of_binop u s s0 v v0 with
          Vptr b i, _, Vptr bb ii => b = bb
        | _, Vptr b i, Vptr bb ii => b = bb
        | _, _, Vptr _ _ => False
        | _, _, _ => True
      end.
  Proof.
    des u; des v; des v0; des s; des s0; 
    repeat match goal with
               |- context [Values.Val.of_bool ?b] => des b
             | |- context [convert_t ?sg (?t,?sg') ?t' ?v] =>
               unfold convert_t; des t; des sg'; des t'
             | |- context [ option_map _ ?v ] => des v
             | |- context [ Val.maketotal (if ?b then _ else _) ] => des b
             | |- context [ match (if ?b then _ else _) with _ => _ end ] => des b
             | |- context [ match (match ?b with _ => _ end) _ _ with _ => _ end ] => des b
           end.
  Qed.

Ltac seval':=
    repeat
      match goal with
        | |- context [eSexpr ?alloc ?em ?e] => des (eSexpr alloc em e)
      end.

Lemma unop_type:
  forall u s t e alloc em,
    wt_unop u s t ->
    wt_val (eSexpr alloc em e) s ->
    wt_val (fun_of_unop u s (eSexpr alloc em e)) t.
Proof.
  intros u s t e alloc em WTu WTv.
  des u; des s; seval'; try des p;
  repeat match goal with
           | |- context [Int.eq ?b ?b2] => des (Int.eq b b2)
           | |- context [convert_t ?s (?s1,?t1) ?t2 ?v] =>
             unfold convert_t; des s; des s1; des t1; des t2
           | |- context [option_map ?f ?o] => des o
         end.
Qed.

Lemma binop_type:
  forall b s s0 t e1 e2 alloc em,
    wt_binop b s s0 t ->
    wt_val (eSexpr alloc em e1) s ->
    wt_val (eSexpr alloc em e2) s0 ->
    wt_val (fun_of_binop b s s0 (eSexpr alloc em e1) (eSexpr alloc em e2)) t.
Proof.
  clear. 
  intros b s s0 t e1 e2 alloc0 em WTb WTv1 WTv2.
  des b; des s; try des s0; try des s1; seval';
  repeat match goal with
           | |- context [eq_block ?b ?b0] => des (eq_block b b0)
           | |- context [Int.ltu ?b ?b0] => des (Int.ltu b b0)
           | |- context [if ?b then _ else _] => des b
  end.
Qed.

Lemma expr_type:
  forall e t,
    wt_expr e t ->
    forall alloc em,
    wt_val (eSexpr alloc em e) t.
Proof.
  induction e; simpl; intros; auto.
  - des v. 
  - subst; auto.
  - destr.
    eapply IHe in H0; eauto.
    eapply unop_type; eauto.
  - destr.
    eapply IHe1 in H0; eauto.
    eapply IHe2 in H; eauto.
    eapply binop_type; eauto.
Qed.

Lemma expr_no_ptr:
  forall alloc em e b i,
    eSexpr alloc em e = Vptr b i -> False. 
Proof.
  induction e; simpl; intros.
  - des v. 
  - inv H.
  - generalize (fun_of_unop_no_ptr u s (eSexpr alloc em e)).
    rewrite H.
    destr.
  - generalize (fun_of_binop_no_ptr b s s0 (eSexpr alloc em e1) (eSexpr alloc em e2)).
    seval'; revert H0; seval'; rewrite H in H0; auto.
Qed.

Ltac seval :=
    repeat
      match goal with
        | H: eSexpr ?alloc ?em ?e = Vptr _ _ |- _ =>
          apply expr_no_ptr in H; contradiction
        | H: Vptr _ _ = eSexpr ?alloc ?em ?e |- _ =>
          symmetry in H; apply expr_no_ptr in H; contradiction
        | |- context [eSexpr ?alloc ?em ?e] => des (eSexpr alloc em e)
      end.


Lemma fou_type:
  forall v s u,
    ~ wt_val v s ->
    fun_of_unop u s v = Vundef.
Proof.
  intros.
  des u; des v; des s; des s0; des a; des b.
Qed.

Lemma convert_undef:
  forall a b c d,
    convert_t a (b,c) d Vundef = Vundef.
Proof.
  des a; des b; des c; des d.
Qed.

Lemma fob_type_r:
  forall v1 v2 b s s0,
    ¬wt_val v2 s0 ->
    fun_of_binop b s s0 v1 v2 = Vundef.
Proof.
  intros.
  des b; des s; des s0; des v1; des v2; des s1.  
Qed.

Lemma fob_type_l:
  forall v1 v2 b s s0,
    ¬wt_val v1 s ->
    fun_of_binop b s s0 v1 v2 = Vundef.
Proof.
  intros.
  des b; des s; des s0; des v1; des v2; des s1.  
Qed.

Lemma expr_type':
  forall alloc em e t,
    wt_val (eSexpr alloc em e) t ->
    ~ wt_expr e t ->
    eSexpr alloc em e = Vundef.
Proof.
  induction e; simpl; intros; auto.
  - des v.
  - des t.
  - assert (~ wt_expr e s \/ ~ wt_unop u s t).
    destruct (wt_expr_dec e s); intuition try congruence.
    clear H0.
    destruct (wt_expr_dec e s).
    + generalize (expr_type _ _ w alloc em).
      assert (~ wt_unop u s t). intuition. clear H1.
      clear IHe. clear w.
      des u; des s; seval; des t; try des p;
      repeat match goal with
               | |- context [Int.eq ?a ?b] => des (Int.eq a b)
               | H: is_lval_typ Tint -> False |- _ => exfalso; apply H; constructor
               | H: is_lval_typ Tlong -> False |- _ => exfalso; apply H; constructor
               | H: is_float_typ Tfloat -> False |- _ => exfalso; apply H; constructor
               | H: is_float_typ Tsingle -> False |- _ => exfalso; apply H; constructor
               | |- convert_t ?a (?b,?c) ?d Vundef = Vundef => apply convert_undef
               | H : wt_val (convert_t ?a (?b,?c) ?d ?v) _ |- _ =>
                 des a; des b; des c; unfold convert_t in H; unfold Val.maketotal in H; simpl in H
               | |- context[ convert_t ?a (?b,?c) ?d ?v ] =>
                 des a; des b; des c; unfold convert_t; unfold Val.maketotal; simpl
               | |- context [ option_map _ ?v ] => des v
             end.
    + destruct (wt_val_dec (eSexpr alloc em e) s).
      * specialize (IHe _ w n). rewrite IHe.
        apply fun_of_unop_undef.
      * apply fou_type; auto.
  - assert (~ wt_expr e1 s \/ ~ wt_expr e2 s0 \/ ~ wt_binop b s s0 t).
    destruct (wt_expr_dec e1 s); intuition try congruence.
    destruct (wt_expr_dec e2 s0); intuition try congruence.
    clear H0.
    destruct (wt_expr_dec e1 s).
    destruct (wt_expr_dec e2 s0).
    + generalize (expr_type _ _ w alloc em).
      generalize (expr_type _ _ w0 alloc em).
      assert (~ wt_binop b s s0 t). intuition. clear H1.
      clear IHe1 IHe2. clear w w0.
      des b; seval; des s; des s0; des t; try des s1;
      repeat match goal with
               | |- context [Int.eq ?a ?b] => des (Int.eq a b)
               | H: is_lval_typ Tint -> False |- _ => exfalso; apply H; constructor
               | H: is_lval_typ Tlong -> False |- _ => exfalso; apply H; constructor
               | H: is_float_typ Tfloat -> False |- _ => exfalso; apply H; constructor
               | H: is_float_typ Tsingle -> False |- _ => exfalso; apply H; constructor
               | |- _ => destr
             end.
    + destruct (wt_val_dec (eSexpr alloc em e2) s0).
      * specialize (IHe2 _ w0 n). rewrite IHe2.
        apply fun_of_binop_undef_r.
      * apply fob_type_r; auto.
    + destruct (wt_val_dec (eSexpr alloc em e1) s).
      * specialize (IHe1 _ w n). rewrite IHe1.
        apply fun_of_binop_undef_l.
      * apply fob_type_l; auto.
Qed.

Lemma nwt_expr_undef:
  forall alloc em e,
    (~ exists t, wt_expr e t) ->
    eSexpr alloc em e = Vundef.
Proof.
  induction e; simpl; intros.
  - des v; exfalso; apply H.
    exists Tint; auto.
    exists Tlong; auto.
    exists Tfloat; auto.
    exists Tsingle; auto.
    exists Tint; auto.
  - exfalso; apply H; eexists; eauto.
  - destruct (wt_expr_dec e s).
    + assert (~ exists t, wt_unop u s t).
      intro A; destruct A as [t A].
      apply H; exists t; split; auto. clear H.
      generalize (expr_type _ _ w alloc em).
      des u; des s; seval; try des p;
      try solve [exfalso; apply H0; eexists; split; eauto; try constructor].
    + destruct (wt_val_dec (eSexpr alloc em e) s).
      erewrite expr_type'; eauto. 
      apply fun_of_unop_undef.
      apply fou_type; auto.
  - destruct (wt_expr_dec e1 s).
    destruct (wt_expr_dec e2 s0).
    + assert (~ exists t, wt_binop b s s0 t).
      intro A; destruct A as [t A].
      apply H; exists t; split; auto. clear H.
      generalize (expr_type _ _ w alloc em).
      generalize (expr_type _ _ w0 alloc em). 
      des b; des s; des s0; seval;
      try solve [exfalso; apply H0; eexists; repeat split; eauto; try constructor];
      des s1.
    + destruct (wt_val_dec (eSexpr alloc em e2) s0).
      rewrite (expr_type' _ _ _ _ w0 n); eauto. 
      apply fun_of_binop_undef_r.
      apply fob_type_r; auto.
    + destruct (wt_val_dec (eSexpr alloc em e1) s).
      rewrite (expr_type' _ _ _ _ w n); eauto. 
      apply fun_of_binop_undef_l.
      apply fob_type_l; auto.
Qed.


Lemma expr_nu_type:
  forall alloc em e t v,
    eSexpr alloc em e = v ->
    v <> Vundef ->
    wt_val v t ->
    wt_expr e t.
Proof.
  intros alloc em e0 t v.
  generalize (expr_type' alloc em e0 t).
  seval; subst; destr; 
  destruct (wt_expr_dec e0 t); destr.
Qed.

Fixpoint contains_val v e : Prop :=
  match e with
    Eval v' => v = v'
  | Eunop u t e => contains_val v e
  | Ebinop b t1 t2 e1 e2 => contains_val v e1 \/ contains_val v e2
  | _ => False
  end.

Theorem contains_undef_undef:
  forall e,
    contains_val Vundef e ->
    forall cm im, eSexpr cm im e = Vundef.
Proof.
  induction e; simpl; intros.
  - subst; auto.
  - easy.
  - rewrite IHe; auto. apply fun_of_unop_undef.
  - destruct H; [rewrite IHe1, fun_of_binop_undef_l; auto | rewrite IHe2,fun_of_binop_undef_r; auto].
Qed.


Section S.

  Variable A : Type.
  Variable B : Type.
  Variable P : A -> B.

  Hypothesis Bdec: forall (b1 b2: B), b1 = b2 \/ b1 <> b2.
  
  Theorem t:
    forall x x',
      P x = x' /\ (~ exists y, P y <> x') ->
      forall a, P a = x'.
  Proof.
    intros. destruct H. subst.
    destruct (Bdec (P a) (P x)); auto.
    exfalso; apply H0. exists a. auto.  
  Qed.

End S. 

Section T.

Lemma int_add_eq_l:
  forall a b c,
    Int.add a b = Int.add a c ->
    b = c.
Proof.
  intros.
  generalize (Int.eq_true (Int.add a b)).
  rewrite H at 2.
  rewrite ! (Int.add_commut a). 
  rewrite Int.translate_eq.
  intro A.
  generalize (Int.eq_spec b c). rewrite A; auto.
Qed.
  
  Lemma ex_other_ptr_not_this_one:
    forall cm im b o cm' sv,
  eSexpr cm im sv = eSexpr cm im (Eval (Vptr b o)) ->
  eSexpr cm' im sv <> eSexpr cm' im (Eval (Vptr b o)) ->
  forall b' o',
    (forall cm, eSexpr cm im sv = eSexpr cm im (Eval (Vptr b' o'))) ->
    b <> b'.
  Proof.
    intros. intro. subst.
    rewrite H1 in H, H0.
    simpl in *.
    assert (o=o').
    eapply (int_add_eq_l (cm b')). congruence. subst.
    eauto.
  Qed.

End T.

Definition depends_on_blocks (B : block -> Prop) (e : expr_sym) :=
  forall a a',
         (forall b, B b -> a b = a' b) ->
         forall  u,
           eSexpr a u e = eSexpr a' u e.

