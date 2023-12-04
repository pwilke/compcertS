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

(** Arithmetic and logical operators for the Compcert C and Clight languages *)

(** In this module, we have kept both the old operators on value and the new
    ones on symbolic values, and we prove for each pair of those operators that
    our new operations are abstractions of the old ones, i.e. if [sem_* = Some
    v] then [exists v', sem_*_expr = Some v' /\ v' == v] *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Values_symbolictype.
Require Import Ctypes.
Require Import Values_symbolic.
Require Import NormaliseSpec.
Require Import ExprEval.
Require Import Memory.
Require Import Memperm.
(** * Syntax of operators. *)
Require Export CopSyntax.
Require Export CopGeneric.

Require Import Values_symbolictype.

Definition expr_cast_int_int sz2 si2 (e:expr_sym) : expr_sym :=
  match sz2 with
      IBool => Eunop OpBoolval Tint e
    | I32 => Eunop (OpZeroext 32) Tint e
    | _ => Eunop (match si2 with
                      Signed => OpSignext
                    | Unsigned => OpZeroext
                  end match sz2 with
                          I8 => 8 | I16 => 16 | I32 => 32 | _ => 1
                      end)
                 Tint e
  end.

Definition sg_conv (s:signedness) :=
  match s with
      Signed => SESigned
    | Unsigned => SEUnsigned
  end.

Definition expr_cast_gen (fromt: styp) (froms:signedness) 
           (tot: styp) (tos:signedness) (e:expr_sym) : expr_sym :=
  Eunop (OpConvert (sg_conv froms) (tot,sg_conv tos)) fromt e.


Definition sem_cast_expr (v: expr_sym) (t1 t2: type) : option expr_sym :=
  match classify_cast t1 t2 with
    | cast_case_neutral => Some (Val.sign_ext 32 v)
    | cast_case_i2i sz2 si2 => Some (expr_cast_int_int sz2 si2 v)
    | cast_case_f2f => Some (expr_cast_gen Tfloat Signed Tfloat Signed v)
    | cast_case_s2s => Some (expr_cast_gen Tsingle Signed Tsingle Signed v)
    | cast_case_s2f => Some (expr_cast_gen Tsingle Signed Tfloat Signed v)
    | cast_case_f2s => Some (expr_cast_gen Tfloat Signed Tsingle Signed v)
    | cast_case_i2f si1 => Some (expr_cast_gen Tint si1 Tfloat Signed v)
    | cast_case_i2s si1 => Some (expr_cast_gen Tint si1 Tsingle Signed v)
    | cast_case_f2i sz2 si2 =>
      Some (expr_cast_int_int sz2 si2 (expr_cast_gen Tfloat Signed Tint si2 v))
    | cast_case_s2i sz2 si2 =>
      Some (expr_cast_int_int sz2 si2 (expr_cast_gen Tsingle Signed Tint si2 v))
    | cast_case_f2bool =>
      Some (
          Eunop OpNotbool Tint 
                (Ebinop (OpCmp SESigned Ceq) Tfloat Tfloat v (Eval (Vfloat Float.zero))))
    | cast_case_s2bool =>
      Some (Eunop OpNotbool Tint 
                  (Ebinop (OpCmp SESigned Ceq) Tsingle Tsingle v (Eval (Vsingle Float32.zero))))
    | cast_case_p2bool =>
      Some (Eunop OpNotbool Tint 
                  (Ebinop (OpCmp SEUnsigned Ceq) Tint Tint v (Eval (Vint Int.zero))))
    | cast_case_l2l => Some (expr_cast_gen Tlong Signed Tlong Signed v)
    | cast_case_i2l si => Some (expr_cast_gen Tint si Tlong Signed v)
    | cast_case_l2i sz si => Some (expr_cast_int_int sz si (Val.loword v))
    | cast_case_l2bool =>
      Some (Eunop OpNotbool Tint
                  (Ebinop (OpCmp SESigned Ceq) Tlong Tlong v (Eval (Vlong Int64.zero))))
    | cast_case_l2f si1 =>
      Some (expr_cast_gen Tlong si1 Tfloat Signed v)
    | cast_case_l2s si1 =>
      Some (expr_cast_gen Tlong si1 Tsingle Signed v)
    | cast_case_f2l si2 =>
      Some (expr_cast_gen Tfloat Signed Tlong si2 v)
    | cast_case_s2l si2 =>
      Some (expr_cast_gen Tsingle Signed Tlong si2 v)
    | cast_case_struct id1 fld1 id2 fld2 =>
      if ident_eq id1 id2 && fieldlist_eq fld1 fld2 then Some v else None
    | cast_case_union id1 fld1 id2 fld2 =>
      if ident_eq id1 id2 && fieldlist_eq fld1 fld2 then Some v else None
    | cast_case_void => Some v
    | cast_case_default => None
  end.

Definition norm_eq_compat (m: mem) (e:expr_sym) (v:val) : Prop :=
  Mem.mem_norm m e = Mem.mem_norm m (Eval v).

Definition vptr (m: mem) :=
  fun b i => Mem.valid_pointer m b (Int.unsigned i).

Lemma valid_pointer:
  forall m b i,
    Mem.valid_pointer m b i = true ->
    in_bound i (Mem.bounds_of_block m b).
Proof.
  intros.
  unfold Mem.valid_pointer in H. 
  destruct (Mem.perm_dec m b i Cur Nonempty); try discriminate.
  eapply Mem.perm_bounds; eauto.
Qed.    

Lemma sem_cast_expr_ok:
  forall v t1 t2 v' m ,
    sem_cast (vptr m) v t1 t2 = Some v' ->
    exists v'',
      sem_cast_expr (Eval v) t1 t2 = Some v'' /\
      norm_eq_compat m v'' v'.
Proof.
  unfold sem_cast, sem_cast_expr.
  intros.
  destruct (classify_cast t1 t2) eqn:?;
  destruct v; simpl; try congruence; inv H; eexists; simpl; split; eauto;
  try red; intros; simpl; symmetry; try reflexivity;
  try (apply Mem.same_eval_eqm; red; simpl; intros; auto; try solve [destr];
       match goal with
         | |- Vint _ = _ => idtac
         | |- Vlong _ = _ => idtac
         | |- Vsingle _ = _ => idtac
         | |- Vfloat _ = _ => idtac
         | _ => fail
       end).
  - rewrite Int.sign_ext_above with (n:=32%Z); auto; unfsize; Psatz.lia.
  - rewrite Int.sign_ext_above with (n:=32%Z); auto; unfsize; Psatz.lia.
  - des sz2; des si2; destr.
    rewrite Int.zero_ext_above with (n:=32%Z); auto; unfsize; Psatz.lia.
    rewrite Int.zero_ext_above with (n:=32%Z); auto; unfsize; Psatz.lia.
  - des si1.
  - des si1; compute.
    rewrite Float32.of_int_double. auto.
    rewrite Float32.of_intu_double. auto.
  - revert H1; destr_cond_match; try congruence.
    intro A; inv A. 
    apply Mem.same_eval_eqm; red; simpl; intros; auto.
    des sz2; des si2; unfold convert_t; simpl; rewrite Heqo; destr;
    try rewrite Heqb; destr;
    rewrite Int.zero_ext_above with (n:=32%Z); auto; unfsize; Psatz.lia.
  - revert H1; destr_cond_match; try congruence.
    intro A; inv A.  
    apply Mem.same_eval_eqm; red; simpl; intros; auto;
    des sz2; des si2; unfold convert_t; simpl; rewrite Heqo; destr;
    try rewrite Heqb; destr;
    rewrite Int.zero_ext_above with (n:=32%Z); auto; unfsize; Psatz.lia.
  - des si1.
  - des sz2; des si2; unfold Int64.loword; destr;
    rewrite Int.zero_ext_above with (n:=32%Z); auto; unfsize; Psatz.lia.
  - des si1.
  - des si1.
  - revert H1; destr. inv H1.
    apply Mem.same_eval_eqm; red; simpl; intros; auto;
    des si2; unfold convert_t; simpl; rewrite Heqo; destr.
  - revert H1; destr. inv H1.
    apply Mem.same_eval_eqm; red; simpl; intros; auto;
    des si2; unfold convert_t; simpl; rewrite Heqo; destr.
  - revert H1; destr. inv H1. simpl.
    apply norm_eq; red; simpl; intros.
    destr.
    unfold vptr in Heqb0.
    exfalso.
    apply valid_pointer in Heqb0.
    generalize (Int.eq_spec (Int.add (cm b) i) Int.zero).
    rewrite Heqb1; intro A.
    destruct Pcm.
    specialize (addr_space b _ Heqb0).
    rewrite A in addr_space.
    change (Int.unsigned Int.zero) with 0 in addr_space.
    omega.
  - destr. 
  - destr.
Qed.

(** The following describes types that can be interpreted as a boolean:
  integers, floats, pointers.  It is used for the semantics of 
  the [!] and [?] operators, as well as the [if], [while], 
  and [for] statements. *)

Definition bool_expr (v: expr_sym) (t: type) : expr_sym :=
  match classify_bool t with
  | bool_case_i =>
    Ebinop (OpCmp SESigned Cne) Tint Tint v (Eval (Vint Int.zero))
  | bool_case_f =>
    Ebinop (OpCmp SESigned Cne) Tfloat Tfloat v (Eval (Vfloat Float.zero))
  | bool_case_s =>
    Ebinop (OpCmp SESigned Cne) Tsingle Tsingle v (Eval (Vsingle Float32.zero))
  | bool_case_p =>
    Ebinop (OpCmp SEUnsigned Cne) Tint Tint v (Eval (Vint Int.zero))
  | bool_case_l =>
    Ebinop (OpCmp SESigned Cne) Tlong Tlong v (Eval (Vlong Int64.zero))
  | bool_default => 
    Ebinop (OpCmp SESigned Cne) Tint Tint v (Eval (Vint Int.zero))
  end.

Lemma bool_val_expr_ok:
  forall m v t v',
    bool_val (vptr m) v t = Some v' ->
    exists v'',
      bool_expr (Eval v) t = v'' /\
      norm_eq_compat m v'' (Values.Val.of_bool v').
Proof.
  unfold bool_val, bool_expr. 
  intros. 
  assert (classify_bool t = bool_case_p \/ classify_bool t <> bool_case_p).
  clear. destruct classify_bool; intuition try congruence.
  destruct H0.
  - rewrite H0 in *.
    destruct v; try congruence.
    + inv H.
      eexists; split; eauto.
      red; intros.
      apply Mem.same_eval_eqm.
      red; simpl; intros; auto.
      destr.
    + destruct (vptr m b i) eqn:?; try discriminate. 
      inv H. eexists; split; eauto.
      red; simpl; intros.
      apply norm_eq; red; simpl; intros.
      apply valid_pointer in Heqb0.
      destruct (Int.eq _ _) eqn:?; simpl; auto.
      generalize (Int.eq_spec (Int.add (cm b) i) Int.zero).
      inv Pcm. 
      specialize (addr_space _ _ Heqb0). 
      rewrite Heqb1; intro A.
      rewrite A in addr_space.
      change (Int.unsigned Int.zero) with 0 in addr_space.
      omega.
  - destruct (classify_bool t) eqn:?; simpl;
    destruct v; try congruence; inv H; 
    eexists; split; eauto; apply Mem.same_eval_eqm; simpl; intros;
    red; simpl; intros; 
    try rewrite Float.cmp_ne_eq;
    try rewrite Float32.cmp_ne_eq;
    try rewrite Heqb; simpl; auto; destr.
Qed.

(** ** Unary operators *)

(** *** Boolean negation *)

Definition sem_notbool_expr (v: expr_sym) (ty: type) : expr_sym :=
  match classify_bool ty with
  | bool_case_i =>
    Eunop OpNotbool Tint v
  | bool_case_f =>
    Ebinop (OpCmp SESigned Ceq) Tfloat Tfloat v (Eval (Vfloat Float.zero))
  | bool_case_s =>
    Ebinop (OpCmp SESigned Ceq) Tsingle Tsingle v (Eval (Vsingle Float32.zero))
  | bool_case_p =>
    Eunop OpNotbool Tint v
  | bool_case_l =>
    Ebinop (OpCmp SESigned Ceq) Tlong Tlong v (Eval (Vlong Int64.zero))
  | bool_default => 
    Eunop OpNotbool Tint v
  end.


Lemma notbool_expr_ok:
  forall m v t v',
    sem_notbool (vptr m) v t = Some v' ->
    exists v'',
      sem_notbool_expr (Eval v) t = v'' /\
      norm_eq_compat m v'' v'.
Proof.
  unfold sem_notbool, sem_notbool_expr.
  intros. 
  assert (classify_bool t = bool_case_p \/ classify_bool t <> bool_case_p).
  clear. destruct classify_bool; intuition try congruence.
  destruct H0.
  - rewrite H0 in *.
    destruct v; try congruence.
    + inv H.
      eexists; split; eauto;
      unfold Values.Val.of_bool.
      apply Mem.same_eval_eqm; red; simpl; intros.
      destr.
    + destruct (vptr m b i) eqn:?; try discriminate. 
      inv H. eexists; split; eauto.
      red; simpl; intros.
      apply valid_pointer in Heqb0.
      apply norm_eq; red; simpl; intros.
      destr.
      destruct (Int.eq _ _) eqn:?; simpl; auto.
      generalize (Int.eq_spec (Int.add (cm b) i) Int.zero).
      inv Pcm. 
      specialize (addr_space _ _ Heqb0). 
      rewrite Heqb1; intro A.
      rewrite A in addr_space.
      change (Int.unsigned Int.zero) with 0 in addr_space.
      omega.
  - destruct (classify_bool t) eqn:?; simpl;
    destruct v; try congruence; inv H; 
    eexists; split; eauto; apply Mem.same_eval_eqm; red; simpl; intros; auto;
    try rewrite Float.cmp_ne_eq;
    try rewrite Float32.cmp_ne_eq;
    try rewrite Heqb; simpl; auto;destr.
    des (Int.eq i Int.zero).
Qed.

(** *** Opposite and absolute value *)


Definition sem_neg_expr (v: expr_sym) (ty: type) : expr_sym :=
  match classify_neg ty with
  | neg_case_i sg => Eunop OpNeg Tint v
  | neg_case_f => Eunop OpNeg Tfloat v
  | neg_case_s =>  Eunop OpNeg Tsingle v
  | neg_case_l sg => Eunop OpNeg Tlong v
  | neg_default => Eunop OpNeg Tint v
  end.

Lemma neg_expr_ok:
  forall v t v',
    sem_neg v t = Some v' ->
    exists v'',
      sem_neg_expr (Eval v) t = v'' /\
      same_eval (Eval v') v''.
Proof.
  unfold sem_neg, sem_neg_expr.
  intros.
  eexists; split; eauto.
  red; intros; destr; des v; inv H; simpl; auto.
Qed.

Definition sem_absfloat_expr (v: expr_sym) (ty: type) : expr_sym :=
  match classify_neg ty with
  | neg_case_i sg => 
    Eunop OpAbsf Tfloat (expr_cast_gen Tint sg Tfloat Signed v)
  | neg_case_f =>
    Eunop OpAbsf Tfloat v
  | neg_case_s =>
    Eunop OpAbsf Tfloat (expr_cast_gen Tsingle Signed Tfloat Signed v)
  | neg_case_l sg =>
    Eunop OpAbsf Tfloat (expr_cast_gen Tlong sg Tfloat Signed v)
  | neg_default => 
    Eunop OpAbsf Tfloat (expr_cast_gen Tint Signed Tfloat Signed v)
  end.


Lemma absfloat_expr_ok:
  forall v t v',
    sem_absfloat v t = Some v' ->
    exists v'',
      sem_absfloat_expr (Eval v) t = v'' /\
      same_eval (Eval v') v''.
Proof.
  unfold sem_absfloat, sem_absfloat_expr.
  intros.  unfold expr_cast_gen.
  destruct (classify_neg t) eqn:?; simpl;
    eexists; split; eauto; red; intros; des v; inv H; simpl; auto; des s.
Qed.


(** *** Bitwise complement *)


Definition sem_notint_expr (v: expr_sym) (ty: type): expr_sym :=
  match classify_notint ty with
  | notint_case_i sg =>
    Eunop OpNot Tint v
  | notint_case_l sg =>
    Eunop OpNot Tlong v
  | notint_default => 
    Eunop OpNot Tint v
  end.


Lemma notint_expr_ok:
  forall v t v',
    sem_notint v t = Some v' ->
    exists v'',
      sem_notint_expr (Eval v) t = v'' /\
      same_eval (Eval v') v''.
Proof.
  unfold sem_notint, sem_notint_expr.
  intros.  
  destruct (classify_notint t) eqn:?; des v; inv H;
  eexists; split; eauto; red; destr.
Qed.

(** ** Binary operators *)

(** For binary operations, the "usual binary conversions" consist in
- determining the type at which the operation is to be performed
  (a form of least upper bound of the types of the two arguments);
- casting the two arguments to this common type;
- performing the operation at that type.
*)

Definition sem_binarith_expr
           (sem_int: signedness -> expr_sym -> expr_sym -> option expr_sym)
           (sem_long: signedness -> expr_sym -> expr_sym -> option expr_sym)
           (sem_float: expr_sym -> expr_sym -> option expr_sym)
           (sem_single: expr_sym -> expr_sym -> option expr_sym)
           (v1: expr_sym) (t1: type) (v2: expr_sym) (t2: type) : option expr_sym :=
  let c := classify_binarith t1 t2 in
  let t := binarith_type c in
  match sem_cast_expr v1 t1 t with
    | None => None
    | Some v1' =>
      match sem_cast_expr v2 t2 t with
        | None => None
        | Some v2' =>
          match c with
            | bin_case_i sg =>
              sem_int sg v1' v2'
            | bin_case_f =>
              sem_float v1' v2'
            | bin_case_s =>
              sem_single v1' v2'
            | bin_case_l sg =>
              sem_long sg v1' v2'
            | bin_default => None
          end 
      end
  end.

Lemma expr_binarith_ok:
  forall m si sl sf ss si' sl' sf' ss' v1 t1 v2 t2 v'
         (si_same: forall sg n1 n2 v,
                     si sg n1 n2 = Some v ->
                     forall v1 v2,
                       norm_eq_compat m v1 (Vint n1) ->
                       norm_eq_compat m v2 (Vint n2) ->
                     exists v',
                       si' sg v1 v2 = Some v' /\
                       norm_eq_compat m v' v)
         (sl_same: forall sg n1 n2 v,
                     sl sg n1 n2 = Some v ->
                     forall v1 v2,
                       norm_eq_compat m v1 (Vlong n1) ->
                       norm_eq_compat m v2 (Vlong n2) ->
                     exists v',
                       sl' sg v1 v2 = Some v' /\
                       norm_eq_compat m v' v)
         (sf_same: forall n1 n2 v,
                     sf  n1 n2 = Some v ->
                     forall v1 v2,
                       norm_eq_compat m v1 (Vfloat n1) ->
                       norm_eq_compat m v2 (Vfloat n2) ->
                     exists v',
                       sf'  v1 v2 = Some v' /\
                       norm_eq_compat m v' v)
         (ss_same: forall n1 n2 v,
                     ss  n1 n2 = Some v ->
                     forall v1 v2,                       
                       norm_eq_compat m v1 (Vsingle n1) ->
                       norm_eq_compat m v2 (Vsingle n2) ->
                     exists v',
                       ss' v1 v2 = Some v' /\
                       norm_eq_compat m v' v),
    sem_binarith (vptr m) si sl sf ss v1 t1 v2 t2 = Some v' ->
    exists v'',
      sem_binarith_expr si' sl' sf' ss' 
                        (Eval v1) t1
                        (Eval v2) t2 = Some v'' /\
      norm_eq_compat m v'' v'.
Proof.
  intros m si sl sf ss si' sl' sf' ss' v1 t1 v2 t2 v' si_same sl_same sf_same ss_same.
  unfold sem_binarith, sem_binarith_expr.
  destruct (sem_cast (vptr m) v1 t1 _) eqn:?; try congruence.
  destruct (sem_cast (vptr m) v2 t2 _) eqn:?; try congruence.
  eapply sem_cast_expr_ok in Heqo; eauto.
  eapply sem_cast_expr_ok in Heqo0; eauto.
  destruct Heqo as [v'' [SC EMM]].
  destruct Heqo0 as [v''1 [SC1 EMM1]].
  rewrite SC. rewrite SC1.
  destruct (classify_binarith t1 t2);
    destruct v eqn:?; destruct v0 eqn:?; try congruence; eauto.
Qed.  

(** *** Addition *)

Definition sem_add_expr (v1:expr_sym) (t1:type) (v2: expr_sym) (t2:type) : option expr_sym :=
  match classify_add t1 t2 with 
  | add_case_pi ty =>                 (**r pointer plus integer *)
    Some 
      (Ebinop OpAdd Tint Tint v1 (Ebinop OpMul Tint Tint v2 (Eval (Vint (Int.repr (sizeof ty))))))
  | add_case_ip ty =>                 (**r integer plus pointer *)
    Some (Ebinop OpAdd Tint Tint v2 (Ebinop OpMul Tint Tint v1 (Eval (Vint (Int.repr (sizeof ty))))))
  | add_case_pl ty =>                 (**r pointer plus long *)
    Some (
        Ebinop OpAdd Tint Tint v1 (Ebinop OpMul Tint Tint 
                                      (Eunop (OpConvert SEUnsigned (Tint,SEUnsigned)) Tlong v2)
                                      (Eval (Vint (Int.repr (sizeof ty))))))
  | add_case_lp ty =>                 (**r long plus pointer *)
    Some (Ebinop OpAdd Tint Tint v2 (Ebinop OpMul Tint Tint 
                                      (Eunop (OpConvert SEUnsigned (Tint,SEUnsigned)) Tlong v1)
                                      (Eval (Vint (Int.repr (sizeof ty))))))
  | add_default =>
      sem_binarith_expr
        (fun sg n1 n2 => Some(Ebinop OpAdd Tint Tint n1 n2))
        (fun sg n1 n2 => Some(Ebinop OpAdd Tlong Tlong n1 n2))
        (fun n1 n2 => Some(Ebinop OpAdd Tfloat Tfloat n1 n2))
        (fun n1 n2 => Some(Ebinop OpAdd Tsingle Tsingle n1 n2))
        v1 t1 v2 t2
  end.



Ltac rew_tt H0 :=
  match type of H0 with
    context[Mem.mem_norm ?m (Eval ?v)] =>
    rewrite Mem.norm_val in H0
  end.

Ltac rewrite_norm :=
  match goal with
  | |- context [eSexpr ?al ?em ?v] =>
        match goal with
        | H:Mem.mem_norm _ v = _, H1:Mem.compat_m ?m ?sz ?al
          |- _ =>
              let x := fresh "H" in
              let A := fresh "A" in
              let B := fresh "B" in
              generalize (Mem.norm_correct m v); rewrite H; intro x;
              generalize (Mem.eval_ok_m _ _ _ x _ em H1); simpl; intro A; inv A
        end
  end.

Lemma add_expr_ok:
  forall m v1 v2 t1 t2 v',
    sem_add (vptr m) v1 t1 v2 t2 = Some v' ->
    exists v'',
      sem_add_expr (Eval v1) t1
                   (Eval v2) t2 = Some v'' /\
      norm_eq_compat m v''  v'.
Proof.
  unfold sem_add, sem_add_expr.
  intros.
  assert (classify_add t1 t2 = add_default \/ classify_add t1 t2 <> add_default).
  destruct (classify_add t1 t2) eqn:?; intuition try congruence.
  destruct H0.
  - rewrite H0 in *. 
    revert H. 
    apply expr_binarith_ok; intros; eauto; inv H;
    eexists; split; simpl; eauto;
    red in H1; red in H2; red; intros;
    simpl in *; rewrite Mem.norm_val in *;
    apply Mem.eq_norm; try congruence; constructor; red; simpl; intros; auto;
    repeat rewrite_norm; simpl; auto.
    
  - destruct (classify_add t1 t2) eqn:?;
             destruct v1; destruct v2; try congruence;
    inv H; try ((eexists; split; simpl; eauto);[idtac];
                red; intros); apply Mem.same_eval_eqm; red; simpl; intros; destr; sint;
    apply Int.mul_commut.
Qed.                   

(** *** Subtraction *)

Definition sem_sub_expr (v1:expr_sym) (t1:type) (v2: expr_sym) (t2:type) : option expr_sym :=
  match classify_sub t1 t2 with
  | sub_case_pi ty =>            (**r pointer minus integer *)
    Some (Ebinop OpSub Tint Tint v1 
                 (Ebinop OpMul Tint Tint v2 
                         (Eval (Vint (Int.repr (sizeof ty))))))
  | sub_case_pl ty =>            (**r pointer minus long *)
    Some (Ebinop OpSub Tint Tint v1 
                 (Ebinop OpMul Tint Tint 
                         (expr_cast_gen Tlong Unsigned Tint Unsigned v2 )
                         (Eval (Vint (Int.repr (sizeof ty))))))
  | sub_case_pp ty =>          (**r pointer minus pointer *)
    Some (Ebinop (OpDiv SEUnsigned) Tint Tint
                 (Ebinop OpSub Tint Tint v1 v2)
                 (Eval (Vint (Int.repr (sizeof ty)))))
  | sub_default =>
      sem_binarith_expr
        (fun sg n1 n2 => Some(Ebinop OpSub Tint Tint n1 n2))
        (fun sg n1 n2 => Some(Ebinop OpSub Tlong Tlong n1 n2))
        (fun n1 n2 => Some(Ebinop OpSub Tfloat Tfloat n1 n2))
        (fun n1 n2 => Some(Ebinop OpSub Tsingle Tsingle n1 n2))
        v1 t1 v2 t2
  end.


Lemma sub_expr_ok:
  forall m v1 v2 t1 t2 v',
    sem_sub (vptr m) v1 t1 v2 t2 = Some v' ->
    exists v'',
      sem_sub_expr (Eval v1) t1
                   (Eval v2) t2 = Some v'' /\
      norm_eq_compat m v'' v'.
Proof.
  unfold sem_sub, sem_sub_expr.
  intros.
  assert (classify_sub t1 t2 = sub_default \/ classify_sub t1 t2 <> sub_default).
  destruct (classify_sub t1 t2) eqn:?; intuition try congruence.
  destruct H0.
  - rewrite H0 in *. unfold norm_eq_compat.
    revert H. 
    apply expr_binarith_ok; intros; eauto; inv H;
    eexists; split; simpl; eauto;
    red in H1; red in H2; red; intros;
    simpl in *; rewrite Mem.norm_val in *;
    apply Mem.eq_norm; try congruence; constructor; red; simpl; intros; auto;
    repeat rewrite_norm; simpl; auto.
  - destruct (classify_sub t1 t2) eqn:?;
             destruct v1; destruct v2; try congruence;
    inv H; try ((eexists; split; simpl; eauto);[idtac];
                red; intros);
    apply Mem.same_eval_eqm; red; simpl; intros; auto; destr; sint.
    + rewrite ! Int.sub_add_opp. rewrite  Int.add_assoc. 
      rewrite Int.mul_commut. reflexivity.
    + destruct (eq_block b b0); try congruence.
    + destruct (eq_block b b0); try congruence. subst.
      subst.
      inv H2. simpl.
      rewrite ! (Int.add_commut (cm b0)).   
      rewrite Int.sub_shifted. auto.
    + rewrite ! Int.sub_add_opp. rewrite  Int.add_assoc. 
      rewrite Int.mul_commut. reflexivity. 
Qed.                   
 
(** *** Multiplication, division, modulus *)

Definition sem_mul_expr (v1:expr_sym) (t1:type) (v2: expr_sym) (t2:type) : option expr_sym :=
  sem_binarith_expr
    (fun sg n1 n2 => Some( Ebinop OpMul Tint Tint n1 n2))
    (fun sg n1 n2 => Some( Ebinop OpMul Tlong Tlong n1 n2))
    (fun n1 n2 => Some( Ebinop OpMul Tfloat Tfloat n1 n2))
    (fun n1 n2 => Some( Ebinop OpMul Tsingle Tsingle n1 n2))
    v1 t1 v2 t2.

Ltac autonorm :=
  repeat rewrite Mem.norm_val in *;
  apply Mem.eq_norm; try congruence; constructor; red; simpl; intros; auto;
  repeat rewrite_norm; simpl; auto.

Lemma mul_expr_ok:
  forall m v1 v2 t1 t2 v',
    sem_mul (vptr m) v1 t1 v2 t2 = Some v' ->
    exists v'',
      sem_mul_expr (Eval v1) t1
                   (Eval v2) t2 = Some v'' /\
      norm_eq_compat m  v'' v'.
Proof.
  unfold sem_mul, sem_mul_expr.
  intros m v1 v2 t1 t2 v'.
  destruct (Mem.concrete_mem m) as [al cpt].
  apply expr_binarith_ok; auto; intros;
  eexists; split; simpl; eauto; red; intros; inv H; simpl in *;
  red in H0; red in H1;
  simpl in *;
  rewrite Mem.norm_val in *; autonorm.
Qed.

Definition sem_div_expr (v1:expr_sym) (t1:type) (v2: expr_sym) (t2:type) : option expr_sym :=
  sem_binarith_expr
    (fun sg n1 n2 => Some (Ebinop (OpDiv (match sg with
                                        Signed => SESigned
                                      | Unsigned => SEUnsigned
                                    end))
                            Tint Tint n1 n2))
    (fun sg n1 n2 => Some (Ebinop (OpDiv (match sg with
                                        Signed => SESigned
                                      | Unsigned => SEUnsigned
                                    end))
                            Tlong Tlong n1 n2))
    (fun n1 n2 => Some(Ebinop (OpDiv SESigned) Tfloat Tfloat n1 n2))
    (fun n1 n2 => Some(Ebinop (OpDiv SESigned) Tsingle Tsingle n1 n2))
    v1 t1 v2 t2.

Lemma div_expr_ok:
  forall m v1 v2 t1 t2 v',
    sem_div (vptr m) v1 t1 v2 t2 = Some v' ->
    exists v'',
      sem_div_expr (Eval v1) t1
                   (Eval v2) t2 = Some v'' /\
      norm_eq_compat m v'' v'.
Proof.
  unfold sem_div, sem_div_expr.
  intros m v1 v2 t1 t2 v'.
  destruct (Mem.concrete_mem m) as [al cpt].
  apply expr_binarith_ok; auto; intros;
  eexists; split; simpl; eauto; red; intros; inv H; simpl in *;
  red in H0; red in H1; rewrite Mem.norm_val in *; try autonorm.
  - des sg; revert H3; destr; inv H3; autonorm; rewrite Heqb; auto.
  - des sg; revert H3; destr; inv H3; autonorm; rewrite Heqb; auto.
Qed.


Definition sem_mod_expr (v1:expr_sym) (t1:type) (v2: expr_sym) (t2:type) : option expr_sym :=
  sem_binarith_expr
    (fun sg n1 n2 => Some (Ebinop (OpMod (match sg with
                                        Signed => SESigned
                                      | Unsigned => SEUnsigned
                                    end))
                            Tint Tint n1 n2))
    (fun sg n1 n2 => Some (Ebinop (OpMod (match sg with
                                        Signed => SESigned
                                      | Unsigned => SEUnsigned
                                    end))
                            Tlong Tlong n1 n2))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 t1 v2 t2.

Lemma mod_expr_ok:
  forall m v1 v2 t1 t2 v',
    sem_mod (vptr m) v1 t1 v2 t2 = Some v' ->
    exists v'',
      sem_mod_expr (Eval v1) t1
                   (Eval v2) t2 = Some v'' /\
      norm_eq_compat m v'' v'.
Proof.
  unfold sem_mod, sem_mod_expr.
    intros m v1 v2 t1 t2 v'.
    destruct (Mem.concrete_mem m) as [al cpt].
  apply expr_binarith_ok; auto; intros; inv H;
  eexists; split; simpl; eauto; red; intros; inv H0; simpl in *;
  red in H1; 
  simpl in *.
  - des sg; revert H3; destr; inv H3; autonorm; rewrite Heqb; auto.
  - des sg; revert H3; destr; inv H3; autonorm; rewrite Heqb; auto.
Qed.

Definition sem_and_expr (v1:expr_sym) (t1:type) (v2: expr_sym) (t2:type) : option expr_sym :=
  sem_binarith_expr
    (fun sg n1 n2 => Some(Ebinop OpAnd Tint Tint n1 n2))
    (fun sg n1 n2 => Some(Ebinop OpAnd Tlong Tlong n1 n2))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 t1 v2 t2.


Lemma and_expr_ok:
  forall m v1 v2 t1 t2 v',
    sem_and (vptr m) v1 t1 v2 t2 = Some v' ->
    exists v'',
      sem_and_expr (Eval v1) t1
                   (Eval v2) t2 = Some v'' /\
      norm_eq_compat m v'' v'.
Proof.
  unfold sem_and, sem_and_expr.
  intros m v1 v2 t1 t2 v'.
  apply expr_binarith_ok; auto; intros; try congruence;
  eexists; split; simpl; eauto; red; intros; unfold norm_eq_compat in *; inv H;
  autonorm.
Qed.


Definition sem_or_expr (v1:expr_sym) (t1:type) (v2: expr_sym) (t2:type) : option expr_sym :=
  sem_binarith_expr
    (fun sg n1 n2 => Some(Ebinop OpOr Tint Tint n1 n2))
    (fun sg n1 n2 => Some(Ebinop OpOr Tlong Tlong n1 n2))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 t1 v2 t2.


Lemma or_expr_ok:
  forall m v1 v2 t1 t2 v',
    sem_or (vptr m) v1 t1 v2 t2 = Some v' ->
    exists v'',
      sem_or_expr (Eval v1) t1
                   (Eval v2) t2 = Some v'' /\
      norm_eq_compat m v'' v'.
Proof.
  unfold sem_or, sem_or_expr.
  intros m v1 v2 t1 t2 v'.
  apply expr_binarith_ok; auto; intros; try congruence;
  eexists; split; simpl; eauto; red; intros; unfold norm_eq_compat in *; inv H;
  autonorm.
Qed.

Definition sem_xor_expr (v1:expr_sym) (t1:type) (v2: expr_sym) (t2:type) : option expr_sym :=
  sem_binarith_expr
    (fun sg n1 n2 => Some(Ebinop OpXor Tint Tint n1 n2))
    (fun sg n1 n2 => Some(Ebinop OpXor Tlong Tlong n1 n2))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 t1 v2 t2.


Lemma xor_expr_ok:
  forall m v1 v2 t1 t2 v',
    sem_xor (vptr m) v1 t1 v2 t2 = Some v' ->
    exists v'',
      sem_xor_expr (Eval v1) t1
                   (Eval v2) t2 = Some v'' /\
      norm_eq_compat m v'' v'.
Proof.
  unfold sem_xor, sem_xor_expr.
  intros m v1 v2 t1 t2 v'.
  apply expr_binarith_ok; auto; intros; try congruence;
  eexists; split; simpl; eauto; red; intros; unfold norm_eq_compat in *; inv H;
  autonorm.
Qed.

(** *** Shifts *)

Definition sem_shift_expr
    (sem_int: signedness -> expr_sym -> expr_sym -> expr_sym)
    (sem_long: signedness -> expr_sym -> expr_sym -> expr_sym)
    (v1: expr_sym) (t1: type) (v2: expr_sym) (t2: type) : option expr_sym :=
  match classify_shift t1 t2 with
  | shift_case_ii sg => Some (sem_int sg v1 v2)
  | shift_case_il sg => Some (sem_int sg v1 (expr_cast_gen Tlong sg Tint sg v2))
  | shift_case_li sg => Some (sem_long sg v1 (expr_cast_gen Tint Unsigned Tlong Unsigned v2))
  | shift_case_ll sg => Some (sem_long sg v1 v2)
  | shift_default => None
  end.

Lemma expr_shift_sem_ok:
  forall m si sl si' sl' v1 t1 v2 t2 v'
         (si_expr: forall sg n1 n2 n2',
                     same_eval n2 n2' ->
                     same_eval (si' sg n1 n2) (si' sg n1 n2'))
         (sl_expr: forall sg n1 n2 n2',
                     same_eval n2 n2' ->
                     same_eval (sl' sg n1 n2) (sl' sg n1 n2'))
         (si_same: forall sg n1 n2 v1 v2,
                       norm_eq_compat m v1 (Vint n1) ->
                       norm_eq_compat m v2 (Vint n2) ->
                       Int.ltu n2 Int.iwordsize = true ->
                       norm_eq_compat m (si' sg v1 v2) (Vint (si sg n1 n2)))
         (sl_same: forall sg n1 n2 v1 v2,
                       norm_eq_compat m v1 (Vlong n1) ->
                       norm_eq_compat m v2 (Vlong n2) ->
                       Int64.ltu n2 Int64.iwordsize = true ->
                       norm_eq_compat m (sl' sg v1 v2) (Vlong (sl sg n1 n2))),
    sem_shift si sl v1 t1 v2 t2 = Some v' ->
    exists v'',
      sem_shift_expr si' sl' 
                     (Eval v1) t1
                     (Eval v2) t2 = Some v'' /\
      norm_eq_compat m v'' v'.
Proof.
  intros m si sl si' sl' v1 t1 v2 t2 v' si_ex sl_ex si_same sl_same.
  unfold sem_shift, sem_shift_expr.
  destruct (classify_shift t1 t2);
    destruct v1; destruct v2; try congruence;
  destr_cond_match; try congruence; intro A; inv A;
  eexists; split; simpl; eauto.
  - apply si_same; auto; red; intros; apply Mem.same_eval_eqm; reflexivity.
  - apply sl_same; auto; red; intros; apply Mem.same_eval_eqm; reflexivity. 
  - apply si_same; auto.
    reflexivity.
    apply Mem.same_eval_eqm. red; simpl; intros. des s.
    unfold Int64.ltu in Heqb; unfold Int.ltu.
    change (Int64.unsigned (Int64.repr 32)) with 32 in Heqb.
    change (Int.unsigned Int.iwordsize) with 32.
    revert Heqb; destr_cond_match; try congruence.
    destr_cond_match; auto. clear Heqs0 Heqs1.
    unfold Int64.loword in g.
    rewrite Int.unsigned_repr in g. intros; omega.
    split. generalize (Int64.unsigned_range i0). omega.
    apply Z.le_trans with 32. omega. vm_compute; congruence.
  - apply sl_same; auto.
    reflexivity.
    apply Mem.same_eval_eqm. red; simpl; intros. des s.
    unfold Int64.ltu, Int.ltu in *. 
    rewrite Int64.unsigned_repr. unfold Int64.iwordsize' in Heqb.
    rewrite Int.unsigned_repr in Heqb. auto.
    vm_compute; intuition congruence. 
    revert Heqb; destr_cond_match; try congruence. clear Heqs0.
    generalize (Int.unsigned_range_2 i0). intros; split. omega.
    destruct H; etransitivity; eauto.
    vm_compute; congruence.
Qed.

Definition sem_shl_expr(v1:expr_sym) (t1:type) (v2: expr_sym) (t2:type) : option expr_sym :=
  sem_shift_expr
    (fun sg n1 n2 => Ebinop OpShl Tint Tint n1 n2)
    (fun sg n1 n2 => Ebinop OpShl Tlong Tint n1 
                            (expr_cast_gen Tlong Unsigned Tint Unsigned n2))
    v1 t1 v2 t2.


Lemma shl_expr_ok:
  forall vptr v1 v2 t1 t2 v',
    sem_shl v1 t1 v2 t2 = Some v' ->
    exists v'',
      sem_shl_expr (Eval v1) t1
                   (Eval v2) t2 = Some v'' /\
      norm_eq_compat vptr v'' v'.
Proof.
  unfold sem_shl, sem_shl_expr. 
  intros m v1 v2 t1 t2 v'.
  destruct (Mem.concrete_mem m) as [al cpt].
  apply expr_shift_sem_ok; auto; intros; try congruence; try se_rew.
  - unfold norm_eq_compat in *. simpl in *. 
    rew_tt H0; rew_tt H. autonorm. destr; auto.
  - unfold norm_eq_compat in *. simpl in *. 
    rew_tt H0; rew_tt H. autonorm.
    IntFacts.assert_val true.
    clear - H1. unfold Int64.ltu in H1.
    revert H1; destr_cond_match; try congruence.
    unfold Int.ltu, Int64.loword.
    rewrite Int.unsigned_repr; auto.
    change (Int.unsigned Int64.iwordsize') with 64 in *.
    change (Int64.unsigned Int64.iwordsize) with 64 in *.
    rewrite Heqs. auto.
    split. generalize (Int64.unsigned_range n2); omega.
    change (Int64.unsigned Int64.iwordsize) with 64 in *.
    transitivity 64; try omega.
    vm_compute; congruence.
    unfold Int64.shl, Int64.shl', Int64.loword. 
    rewrite Int.unsigned_repr. auto.
    split. generalize (Int64.unsigned_range n2); omega.
    unfold Int64.ltu in H1. change (Int64.unsigned Int64.iwordsize) with 64 in *.
    revert H1; destr.
    transitivity 64; try omega.
    vm_compute; congruence.
Qed.

Definition sem_shr_expr (v1:expr_sym) (t1:type) (v2: expr_sym) (t2:type) : option expr_sym :=
  sem_shift_expr
    (fun sg n1 n2 => Ebinop (OpShr match sg with Signed => SESigned
                                              | Unsigned => SEUnsigned 
                                   end)
                            Tint Tint n1 n2)
    (fun sg n1 n2 => Ebinop (OpShr match sg with Signed => SESigned
                                              | Unsigned => SEUnsigned 
                                   end)
                            Tlong Tint n1 (expr_cast_gen Tlong Unsigned Tint Unsigned n2))
    v1 t1 v2 t2.

Lemma shr_expr_ok:
  forall m v1 v2 t1 t2 v',
    sem_shr v1 t1 v2 t2 = Some v' ->
    exists v'',
      sem_shr_expr (Eval v1) t1
                   (Eval v2) t2 = Some v'' /\
      norm_eq_compat m v'' v'.
Proof.
  intros m v1 v2 t1 t2 v'.
  apply expr_shift_sem_ok; auto; intros; try congruence; se_rew.
  - red; intros;
    simpl in *;
    red in H0; red in H;
    simpl in *;
    rew_tt H0; rew_tt H.
    autonorm.
    des sg; rewrite H1; auto.
  - red; intros; 
    simpl in *;
    red in H0; red in H;
    simpl in *;
    rew_tt H0; rew_tt H;
    destruct sg; autonorm; destr. 
    + unfold Int64.shr, Int64.shr'.
      unfold convert_t. simpl. unfold Int64.loword. rewrite Int.unsigned_repr. auto.
      unfold Int64.ltu in H1.
      revert H1;  destr_cond_match; try congruence.
      generalize (Int64.unsigned_range n2). split. omega.
      transitivity (Int64.unsigned Int64.iwordsize); try omega. vm_compute. congruence.
    + exfalso; clear - Heqb H1.
      unfold Int64.ltu, Int.ltu in *.
      revert Heqb; destr_cond_match; try congruence.
      revert H1; destr_cond_match; try congruence.
      clear Heqs Heqs0.
      change (Int.unsigned Int64.iwordsize') with 64 in g.
      change (Int64.unsigned Int64.iwordsize) with 64 in l.
      unfold Int64.loword in g. 
      rewrite Int.unsigned_repr in g. intros. 
      omega.
      split. generalize (Int64.unsigned_range n2); omega.
      transitivity 64; try omega.
      vm_compute; congruence.
    + unfold Int64.shru, Int64.shru'.
      unfold Int64.loword. rewrite Int.unsigned_repr. auto.
      unfold Int64.ltu in H1.
      revert H1; destr_cond_match; try congruence.
      generalize (Int64.unsigned_range n2). split. omega.
      transitivity (Int64.unsigned Int64.iwordsize); try omega. vm_compute. congruence.
    + exfalso; clear - Heqb H1.
      unfold Int64.ltu, Int.ltu in *.
      revert Heqb; destr_cond_match; try congruence.
      revert H1; destr_cond_match; try congruence.
      clear Heqs Heqs0.
      change (Int.unsigned Int64.iwordsize') with 64 in g.
      change (Int64.unsigned Int64.iwordsize) with 64 in l.
      unfold Int64.loword in g. 
      rewrite Int.unsigned_repr in g. intros. 
      omega.
      split. generalize (Int64.unsigned_range n2); omega.
      transitivity 64; try omega.
      vm_compute; congruence.
Qed.

(** *** Comparisons *)

Definition sem_cmp_expr (c:comparison)
                  (v1: expr_sym) (t1: type) (v2: expr_sym) (t2: type)
                  (* (m: mem) *): option expr_sym :=
  match classify_cmp t1 t2 with
  | cmp_case_pp =>
    Some (Ebinop (OpCmp SEUnsigned c) Tint Tint v1 v2)
  | cmp_case_pl =>
    Some (Ebinop (OpCmp SEUnsigned c) Tint Tint v1 (expr_cast_gen Tlong Unsigned Tint Unsigned v2))
  | cmp_case_lp =>
    Some (Ebinop (OpCmp SEUnsigned c) Tint Tint (expr_cast_gen Tlong Unsigned Tint Unsigned v1) v2)
  | cmp_default =>
    sem_binarith_expr
      (fun sg n1 n2 =>
         Some(
             Ebinop (OpCmp (match sg with
                                Signed => SESigned
                              | Unsigned => SEUnsigned
                            end) c) Tint Tint n1 n2))
        (fun sg n1 n2 =>
         Some(
             Ebinop (OpCmp (match sg with
                                Signed => SESigned
                              | Unsigned => SEUnsigned
                            end) c) Tlong Tlong n1 n2))
        (fun n1 n2 =>
            Some(    Ebinop (OpCmp SESigned c) Tfloat Tfloat n1 n2))
        (fun n1 n2 =>
            Some(    Ebinop (OpCmp SESigned c) Tsingle Tsingle n1 n2))
        v1 t1 v2 t2
  end.

Lemma int_eq_true:
  forall i1 i2,
    Int.eq i1 i2 = true ->
    i1 = i2.
Proof.
  intros i1 i2 A.
  generalize (Int.eq_spec i1 i2).
  rewrite A. tauto.
Qed.
Require Import Psatz.


Ltac elim_div_mod :=
  unfold Zmod, Zdiv;
  match goal with
    | |- context [Z.div_eucl ?X ?Y] =>
      let x := fresh "X" in
      (let y := fresh "Y" in
       (let eqx := fresh "EQX" in
        (let eqy := fresh "EQY" in
         (remember X as x eqn:eqx;
          remember Y as y eqn:eqy ; 
          generalize (Z_div_mod_full x y) ;
          unfold Remainder ;
          generalize (Z.div_eucl x y) ;
          (let p := fresh "P" in intro p ; destruct p)
         ))))
  end.

Require Import Psatz.

Lemma compat_conserve_cmp:
  forall c al sz msk b i i0 q (qinf: q <= Int.max_unsigned)
         (COMPAT: compat q sz msk al)
        (bnd0: forall bb, fst (sz bb) = 0)
        (IB1: in_bound (Int.unsigned i) (sz b))
        (IB2: in_bound (Int.unsigned i0) (sz b)),
    Int.cmpu c (Int.add i (al b)) (Int.add i0 (al b)) = Int.cmpu c i i0.
Proof.
  intros. inv COMPAT.
  clear overlap alignment.
  rewrite Int.translate_cmpu; auto.
  -
  generalize (addr_space _ _ IB1)
             (addr_space _ _ IB2)
             (addr_space b Int.zero)
             (addr_space b (Int.repr (snd (sz b) -1))).
  destruct (sz b) eqn:?.
  generalize (bnd0 b); rewrite Heqp. simpl; intro; subst.
  unfold in_bound in *; simpl in *.
  intros A B C D.
  trim C. change (Int.unsigned Int.zero) with 0. omega. 
  trim D. destruct (zle (z0 - 1) Int.max_unsigned). 
  rewrite Int.unsigned_repr. lia. lia.
  generalize (Int.unsigned_range_2 (Int.repr (z0-1))). lia.
  clear bnd0.
  rewrite Int.add_zero in C.
  unfold Int.add in *.
  clear B D.
  split. lia.
  destruct (zle (Int.unsigned i + Int.unsigned (al b)) Int.max_unsigned); auto.
  assert (exists j, 0 <= j <= Int.unsigned i /\ Int.unsigned (al b) + j = Int.max_unsigned + 1).
  (exists (Int.max_unsigned + 1 - Int.unsigned (al b)); split; try lia).
  destruct H as [j [E F]].
  generalize (addr_space b (Int.repr j)). rewrite Heqp; simpl.
  rewrite Int.unsigned_repr.
  rewrite F.
  change (Int.unsigned (Int.repr (Int.max_unsigned + 1))) with 0.
  intro G; trim G. lia. lia.
  generalize (Int.unsigned_range i). lia.
  -
  generalize (addr_space _ _ IB1)
             (addr_space _ _ IB2)
             (addr_space b Int.zero)
             (addr_space b (Int.repr (snd (sz b) -1))).
  destruct (sz b) eqn:?.
  generalize (bnd0 b); rewrite Heqp. simpl; intro; subst.
  unfold in_bound in *; simpl in *.
  intros A B C D.
  trim C. change (Int.unsigned Int.zero) with 0. lia. 
  trim D. destruct (zle (z0 - 1) Int.max_unsigned). 
  rewrite Int.unsigned_repr. lia. lia.
  generalize (Int.unsigned_range_2 (Int.repr (z0-1))). lia.
  clear bnd0.
  rewrite Int.add_zero in C.
  unfold Int.add in *.
  clear A D.
  split. lia.
  destruct (zle (Int.unsigned i0 + Int.unsigned (al b)) Int.max_unsigned); auto.
  assert (exists j, 0 <= j <= Int.unsigned i0 /\ Int.unsigned (al b) + j = Int.max_unsigned + 1).
  (exists (Int.max_unsigned + 1 - Int.unsigned (al b)); split; try lia).
  destruct H as [j [E F]].
  generalize (addr_space b (Int.repr j)). rewrite Heqp; simpl.
  rewrite Int.unsigned_repr.
  rewrite F.
  change (Int.unsigned (Int.repr (Int.max_unsigned + 1))) with 0.
  intro G; trim G. lia. lia.
  generalize (Int.unsigned_range i). lia.
Qed.

Lemma compat_conserve_cmp':
  forall c al sz msk b i i0 q (qinf: q <= Int.max_unsigned)
         (COMPAT: compat q sz msk al)
         (bnd0: forall bb, fst (sz bb) = 0)
         (IB1: in_bound (Int.unsigned i) (sz b))
         (IB2: (Int.unsigned i0) = snd (sz b)),
    Int.cmpu c (Int.add i (al b)) (Int.add i0 (al b)) = Int.cmpu c i i0.
Proof.
  intros. inv COMPAT.
  clear overlap alignment.
  rewrite Int.translate_cmpu; auto.
  generalize (addr_space _ _ IB1)
             (addr_space b Int.zero)
             (addr_space b (Int.repr (snd (sz b) - 1))).
  destruct (sz b) eqn:?.
  generalize (bnd0 b); rewrite Heqp. simpl; intro; subst.
  unfold in_bound in *; simpl in *.
  intros A C D.
  trim C. change (Int.unsigned Int.zero) with 0. lia. 
  trim D. destruct (zle (z0 - 1) Int.max_unsigned). 
  rewrite Int.unsigned_repr. lia. lia.
  generalize (Int.unsigned_range_2 (Int.repr (z0-1))). lia.
  clear bnd0.
  rewrite Int.add_zero in C.
  unfold Int.add in *.
  clear D.
  split. lia.
  destruct (zle (Int.unsigned i + Int.unsigned (al b)) Int.max_unsigned); auto.
  assert (exists j, 0 <= j <= Int.unsigned i /\ Int.unsigned (al b) + j = Int.max_unsigned + 1).
  (exists (Int.max_unsigned + 1 - Int.unsigned (al b)); split; try lia).
  destruct H as [j [E F]].
  generalize (addr_space b (Int.repr j)). rewrite Heqp; simpl.
  rewrite Int.unsigned_repr.
  rewrite F.
  change (Int.unsigned (Int.repr (Int.max_unsigned + 1))) with 0.
  intro G; trim G. lia. lia.
  generalize (Int.unsigned_range i). lia.
  generalize (addr_space _ _ IB1)
             (addr_space b Int.zero)
             (addr_space b (Int.repr (snd (sz b) -1))).
  destruct (sz b) eqn:?.
  generalize (bnd0 b); rewrite Heqp. simpl; intro; subst.
  unfold in_bound in *; simpl in *.
  intros A C D.
  trim C. change (Int.unsigned Int.zero) with 0. lia. 
  trim D. destruct (zle (z0 - 1) Int.max_unsigned). 
  rewrite Int.unsigned_repr. lia. lia.
  generalize (Int.unsigned_range_2 (Int.repr (z0-1))). lia.
  clear bnd0.
  rewrite Int.add_zero in C.
  unfold Int.add in *.
  clear A D.
  split. lia.
  destruct (zle (Int.unsigned i0 + Int.unsigned (al b)) Int.max_unsigned); auto.
  assert (exists j, 0 < j < Int.unsigned i0 /\ Int.unsigned (al b) + j = Int.max_unsigned).
  (exists (Int.max_unsigned  - Int.unsigned (al b)); split; try lia).
  destruct H as [j [E F]].
  generalize (addr_space b (Int.repr j)). rewrite Heqp; simpl.
  rewrite Int.unsigned_repr.
  rewrite F.
  change (Int.unsigned (Int.repr (Int.max_unsigned))) with Int.max_unsigned.
  intro G; trim G. subst. lia.
  generalize (Int.unsigned_range i). lia.
  lia.
Qed.

Require Import Psatz.

Lemma weak_valid_pointer:
  forall m b0 i0 sz
         (bnds: forall b, sz b = Mem.bounds_of_block m b)
         (bnd0: forall b, fst (sz b) = 0)
         (Hib : forall (b : block) i,
                Mem.valid_pointer m b i = true ->
                in_bound i (sz b))
         (Hnib : forall (b : block) i,
                ~ in_bound i (sz b) ->
                  Mem.valid_pointer m b i = false
         )
         (NVP: Mem.valid_pointer m b0 (Int.unsigned i0) = false)
         (NVP': Mem.valid_pointer m b0 (Int.unsigned i0 - 1) = true),
    Int.unsigned i0 = snd (sz b0) \/ in_bound (Int.unsigned i0) (sz b0).
Proof.
  intros.
  assert (in_bound (Int.unsigned i0 - 1) (sz b0)).
  {
    destruct (in_bound_dec (sz b0) (Int.unsigned i0 - 1)); auto.
  } auto.
  apply Hib in NVP'.
  assert (Int.unsigned i0 - 1 = Int.unsigned (Int.sub i0 Int.one)).
  {
    unfold in_bound in *; destruct (sz b0) eqn:?; simpl in *.
    unfold Int.sub.
    rewrite Int.unsigned_repr. change (Int.unsigned Int.one) with 1.
    lia.
    generalize (bnd0 b0); rewrite Heqp. simpl; intro; subst. 
    change (Int.unsigned Int.one) with 1.
    destruct (zle z0 0).
    subst.
    unfold Mem.valid_pointer in NVP'.
    destruct (Mem.perm_dec m b0 (Int.unsigned i0 - 1) Cur Nonempty); try discriminate.
    clear NVP'. apply Mem.perm_bounds in p.  unfold Mem.in_bound_m in p.
    rewrite <- bnds in p. rewrite Heqp in p. unfold in_bound in p; simpl in p.
    lia.
    generalize (Int.unsigned_range_2 i0). intros. lia.
    generalize (Int.unsigned_range_2 i0). intros. lia.
  } 
  destruct (in_bound_dec (sz b0) (Int.unsigned i0)). 
  auto.
  unfold in_bound in *; destruct (sz b0) eqn:?; simpl in *.
  lia.
Qed.

Lemma cmp_expr_ok:
  forall c v1 v2 t1 t2 m v',
    sem_cmp c v1 t1 v2 t2 (Mem.valid_pointer m) = Some v' ->
    exists v'',
      sem_cmp_expr c (Eval v1) t1
                   (Eval v2) t2 = Some v'' /\
      norm_eq_compat m v'' v'.
Proof.
  unfold sem_cmp, sem_cmp_expr.
  intros c v1 v2 t1 t2 m v'.
  destruct (Mem.concrete_mem m) as [al cpt].
  destruct (classify_cmp t1 t2).
  - destruct v1; destruct v2; simpl; try congruence;
    intro A; inv A;
    eexists; split; simpl; eauto; red; intros; simpl.
    + apply Mem.same_eval_eqm; red; simpl; intros; auto. destr. 
    + repeat (revert H0; destr).
      destruct (Values.Val.cmp_different_blocks c) eqn:?; simpl in H0; inv H0.
      apply valid_pointer in Heqb0.
      apply norm_eq; red; simpl; intros.
      apply int_eq_true in Heqb1. subst.
      des b0; des c; destr;
      generalize (Int.eq_spec Int.zero (Int.add (cm b) i0));
        rewrite <- (negb_involutive (Int.eq _ _)); rewrite Heqb1; simpl;
      intro A;
      inv Pcm;
      apply addr_space in Heqb0;
      rewrite <- A in Heqb0;
      change (Int.unsigned Int.zero) with 0 in Heqb0; lia.
    + repeat (revert H0; destr). 
      destruct (Values.Val.cmp_different_blocks c) eqn:?; simpl in H0; inv H0.
      apply valid_pointer in Heqb0.
      apply norm_eq; red; simpl; intros.
      apply int_eq_true in Heqb1. subst.
      des b0; des c; destr;
      generalize (Int.eq_spec (Int.add (cm b) i) Int.zero);
        rewrite <- (negb_involutive (Int.eq _ _)); rewrite Heqb1; simpl;
      intro A;
      inv Pcm;
      apply addr_space in Heqb0;
      rewrite A in Heqb0;
      change (Int.unsigned Int.zero) with 0 in Heqb0; lia.
    + repeat (revert H0;  destr); inv H0. 
      * apply norm_eq; red; simpl; intros.
        assert (forall b, fst (Mem.bounds_of_block m b) = 0). 
        {
          unfold Mem.bounds_of_block. intro; destr_cond_match; simpl; auto.
          destruct p. apply Mem.bounds_lo_inf0 in Heqo. subst; auto.
          destr.
        }
        {
          assert ((in_bound (Int.unsigned i) (Mem.bounds_of_block m b0) \/
                   Int.unsigned i = snd (Mem.bounds_of_block m b0)) /\
                  (in_bound (Int.unsigned i0) (Mem.bounds_of_block m b0) \/
                   Int.unsigned i0 = snd (Mem.bounds_of_block m b0))).
          {
            clear - Heqb1 H.
            rewrite andb_true_iff in Heqb1; destruct Heqb1 as [A B].
            rewrite orb_true_iff in A, B.
            split.
            - destruct (Mem.valid_pointer m b0 (Int.unsigned i)) eqn:?.
              + left; apply valid_pointer; auto.
              + destruct A. discriminate. 
                eapply weak_valid_pointer in H; eauto.
                * destruct H; auto.
                * intros b i1; rewrite Mem.valid_pointer_nonempty_perm.
                  apply Mem.perm_bounds.
                * intros b i1; destruct (Mem.valid_pointer m b i1) eqn:?; auto. 
                  rewrite Mem.valid_pointer_nonempty_perm in Heqb1.
                  apply Mem.perm_bounds in Heqb1. unfold Mem.in_bound_m in *; congruence.
            - destruct (Mem.valid_pointer m b0 (Int.unsigned i0)) eqn:?.
              + left; apply valid_pointer; auto.
              + destruct B. discriminate. 
                eapply weak_valid_pointer in H; eauto.
                * destruct H; auto.
                * intros b i1; rewrite Mem.valid_pointer_nonempty_perm.
                  apply Mem.perm_bounds.
                * intros b i1; destruct (Mem.valid_pointer m b i1) eqn:?; auto. 
                  rewrite Mem.valid_pointer_nonempty_perm in Heqb1.
                  apply Mem.perm_bounds in Heqb1. unfold Mem.in_bound_m in *; congruence.
          } clear Heqb1.
          destruct H0 as [[A|A] [B|B]].
          - rewrite ! (Int.add_commut (cm b0));
            erewrite compat_conserve_cmp; eauto; try congruence; try lia.
            destruct (Int.cmpu c i i0); simpl; auto.
          - rewrite ! (Int.add_commut (cm b0)).
            erewrite compat_conserve_cmp'; eauto. 
            destruct (Int.cmpu c i i0) eqn:?; simpl; auto. lia.
          - rewrite ! (Int.add_commut (cm b0)).
            rewrite <- (Int.swap_cmpu c (Int.add _ _)).
            erewrite compat_conserve_cmp'; eauto. 
            rewrite Int.swap_cmpu.
            destruct (Int.cmpu c i i0) eqn:?; simpl; auto. lia.
          - unfold Int.add. unfold Int.cmpu, Int.eq, Int.ltu.
            rewrite A, B.
            rewrite ! zeq_true.
            rewrite ! zlt_false; try lia. 
            simpl.
            destruct c; simpl; auto. 
        }        
      * revert H1; unfold option_map; destr_cond_match; try discriminate.
        intro A; inv A.
        apply norm_eq; red; simpl; intros.
        destruct (Int.cmpu c (Int.add (cm b) i)
                           (Int.add (cm b0) i0)) eqn:?; simpl; 
        destruct b1 eqn:?; simpl; auto; 
        destruct c; simpl in *; try discriminate.
        rewrite andb_true_iff in Heqb1.
        destruct Heqb1 as [A B].
        apply valid_pointer in A. 
        apply valid_pointer in B.
        inv Pcm. specialize (overlap _ _ _ _ n A B).
        rewrite (int_eq_true _ _ Heqb2) in overlap. congruence.
        rewrite andb_true_iff in Heqb1.
        destruct Heqb1 as [A B].
        apply valid_pointer in A. 
        apply valid_pointer in B.
        inv Pcm. specialize (overlap _ _ _ _ n A B).
        rewrite negb_false_iff in Heqb2.
        rewrite (int_eq_true _ _ Heqb2) in overlap. congruence.
  - destruct v2; simpl; try congruence.
    destruct v1; simpl; try congruence; intro A; inv A;
    eexists; split; simpl; eauto; red; intros.
    destruct (Int.cmpu c i0 (Int.repr (Int64.unsigned i))) eqn:?;
             apply norm_eq; red; simpl; intros;
    setoid_rewrite Heqb; simpl; auto.
    repeat (revert H0; destr).
    destruct (Values.Val.cmp_different_blocks c) eqn:?; simpl in H0; inv H0.
    apply norm_eq; red; simpl; intros.
    setoid_rewrite (int_eq_true _ _ Heqb1).
    inv Pcm.
    apply valid_pointer in Heqb0.
    specialize (addr_space _ _ Heqb0).
    destruct (Int.cmpu c (Int.add (cm b) i0) Int.zero) eqn:?; simpl;
    destruct c; simpl in Heqo; try congruence; inv Heqo; simpl in *; auto.
    rewrite (int_eq_true _ _ Heqb2) in addr_space.
    change (Int.unsigned Int.zero) with 0 in addr_space; lia.
    rewrite negb_false_iff in Heqb2.
    rewrite (int_eq_true _ _ Heqb2) in addr_space.
    change (Int.unsigned Int.zero) with 0 in addr_space; lia.
  - destruct v1; simpl; try congruence.
    destruct v2; simpl; try congruence; intro A; inv A;
    eexists; split; simpl; eauto; red; intros.
    apply norm_eq; red; simpl; intros.
    unfold Int64.loword.
    destruct (Int.cmpu c (Int.repr (Int64.unsigned i)) i0) eqn:?; simpl; auto.
    repeat (revert H0; destr).
    destruct (Values.Val.cmp_different_blocks c) eqn:?; try discriminate.
    simpl in *. inv H0.
    apply norm_eq; red; simpl; intros.
    apply int_eq_true in Heqb1.
    setoid_rewrite Heqb1.
    des c; inv Heqo; destr;
    inv Pcm; apply valid_pointer in Heqb0; specialize (addr_space _ _ Heqb0);
    try rewrite negb_false_iff in Heqb2;
    rewrite <- (int_eq_true _ _ Heqb2) in addr_space;
    change (Int.unsigned Int.zero) with 0 in addr_space; lia.
-
  apply expr_binarith_ok; auto; intros; 
  eexists; split; simpl; eauto; unfold norm_eq_compat in *; inv H;
  rewrite Mem.norm_val in *; unfold Values.Val.of_bool; repeat destr;
  unfold Vtrue, Vfalse; autonorm; destr; auto.
Qed.

Definition sem_switch_arg_expr (m: mem) (v: expr_sym) (ty: type): option Z :=
  match classify_switch ty with
  | switch_case_i =>
      match Mem.mem_norm m v with Vint n => Some(Int.unsigned n) | _ => None end
  | switch_case_l =>
      match Mem.mem_norm m v with Vlong n => Some(Int64.unsigned n) | _ => None end
  | switch_default =>
      None
  end.

(** * Combined semantics of unary and binary operators *)

Definition sem_unary_operation_expr
            (op: unary_operation) (v: expr_sym) (ty: type): expr_sym :=
  match op with
  | Onotbool => sem_notbool_expr v ty
  | Onotint => sem_notint_expr v ty
  | Oneg => sem_neg_expr v ty
  | Oabsfloat => sem_absfloat_expr v ty
  end.

Lemma expr_unop_ok:
  forall m op v ty v',
    sem_unary_operation (vptr m) op v ty = Some v' ->
    exists v'',
      sem_unary_operation_expr op (Eval v) ty = v'' /\
      norm_eq_compat m v'' v'.
Proof.
  destruct op; simpl; intros x ty v' A.
  - destruct (notbool_expr_ok _ _ _ _ A) as [v'' [B C]];
    exists v''; split; auto.
  - destruct (notint_expr_ok _ _ _ A) as [v'' [B C]];
    exists v''; split; auto.
    red; intros. apply Mem.same_eval_eqm; eauto.  symmetry; auto.
  - destruct (neg_expr_ok _ _ _ A) as [v'' [B C]];
    exists v''; split; auto.
    red; intros. apply Mem.same_eval_eqm; eauto.  symmetry; auto.
  - destruct (absfloat_expr_ok _ _ _ A) as [v'' [B C]];
    exists v''; split; auto.
    red; intros. apply Mem.same_eval_eqm;  eauto.  symmetry; auto.
Qed.

Definition sem_binary_operation_expr
    (op: binary_operation)
    (v1: expr_sym) (t1: type) (v2: expr_sym) (t2:type)
    (* (m: mem) *): option expr_sym :=
  match op with
  | Oadd => sem_add_expr v1 t1 v2 t2
  | Osub => sem_sub_expr v1 t1 v2 t2 
  | Omul => sem_mul_expr v1 t1 v2 t2
  | Omod => sem_mod_expr v1 t1 v2 t2
  | Odiv => sem_div_expr v1 t1 v2 t2 
  | Oand => sem_and_expr v1 t1 v2 t2
  | Oor  => sem_or_expr v1 t1 v2 t2
  | Oxor  => sem_xor_expr v1 t1 v2 t2
  | Oshl => sem_shl_expr v1 t1 v2 t2
  | Oshr  => sem_shr_expr v1 t1 v2 t2   
  | Oeq => sem_cmp_expr Ceq v1 t1 v2 t2 
  | One => sem_cmp_expr Cne v1 t1 v2 t2 
  | Olt => sem_cmp_expr Clt v1 t1 v2 t2 
  | Ogt => sem_cmp_expr Cgt v1 t1 v2 t2 
  | Ole => sem_cmp_expr Cle v1 t1 v2 t2 
  | Oge => sem_cmp_expr Cge v1 t1 v2 t2 
  end.

Lemma expr_binop_ok:
  forall  op v1 t1 v2 t2 m v',
    sem_binary_operation  op v1 t1 v2 t2 (Mem.valid_pointer m) = Some v' ->
    exists v'',
      sem_binary_operation_expr op (Eval v1) t1 (Eval v2) t2 = Some v'' /\
      norm_eq_compat m v'' v'.
Proof.
  destruct op; simpl; intros v1 t1 v2 t2 m v'.
  - apply add_expr_ok.
  - apply sub_expr_ok.
  - apply mul_expr_ok.
  - apply div_expr_ok.
  - apply mod_expr_ok.
  - apply and_expr_ok.
  - apply or_expr_ok.
  - apply xor_expr_ok.
  - apply shl_expr_ok.
  - apply shr_expr_ok.
  - apply cmp_expr_ok.
  - apply cmp_expr_ok.
  - apply cmp_expr_ok.
  - apply cmp_expr_ok.
  - apply cmp_expr_ok.
  - apply cmp_expr_ok.
Qed.

Lemma norm_undef:
  forall m,
    Mem.mem_norm m (Eval Vundef) = Vundef.
Proof.
  intros.
  apply Mem.norm_val; auto.
Qed.

Lemma norm_eq_compat_norm:
  forall m e v,
    norm_eq_compat m e v ->
    Mem.mem_norm m e = v.
Proof.
  intros m e v NEC.
  red in NEC.
  rewrite Mem.norm_val in NEC; auto.
Qed.

Lemma expr_binop_ok':
  forall  op v1 t1 v2 t2 m v',
    sem_binary_operation  op v1 t1 v2 t2 (Mem.valid_pointer m) = Some v' ->
    exists v'',
      sem_binary_operation_expr op (Eval v1) t1 (Eval v2) t2 = Some v'' /\
      Mem.mem_norm m v'' = v'.
Proof.
  intros op v1 t1 v2 t2 m v' SBO .
  apply expr_binop_ok in SBO.
  destruct SBO as [v'' [A B]].
  eexists; split; eauto.
  apply norm_eq_compat_norm; auto.
Qed.

Definition sem_incrdecr_expr (id: incr_or_decr) (v: expr_sym) (ty: type) :=
  match id with
  | Incr => sem_add_expr v ty (Eval (Vint Int.one)) type_int32s
  | Decr => sem_sub_expr v ty (Eval (Vint Int.one)) type_int32s
  end.

Lemma incrdecr_expr_ok:
  forall m id v1 t1 v',
    sem_incrdecr (vptr m) id v1 t1 = Some v' ->
    exists v'',
      sem_incrdecr_expr id (Eval v1) t1 = Some v'' /\
      norm_eq_compat m v'' v'.
Proof.
  unfold sem_incrdecr, sem_incrdecr_expr.
  intros m id v1 t1 v'.
  destruct id.
  apply add_expr_ok.
  apply sub_expr_ok.
Qed.

(** * Compatibility with extensions and injections *)

Section GENERIC_INJECTION.

Variable f: meminj.
Variables m m': mem.

Hypothesis valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.valid_pointer m b1 (Int.unsigned ofs) = true ->
  Mem.valid_pointer m' b2 (Int.unsigned (Int.add ofs (Int.repr delta))) = true.

Hypothesis weak_valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Int.unsigned ofs) = true ->
  Mem.weak_valid_pointer m' b2 (Int.unsigned (Int.add ofs (Int.repr delta))) = true.

Hypothesis weak_valid_pointer_no_overflow:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Int.unsigned ofs) = true ->
  0 <= Int.unsigned ofs + Int.unsigned (Int.repr delta) <= Int.max_unsigned.

Hypothesis valid_different_pointers_inj:
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m b1 (Int.unsigned ofs1) = true ->
  Mem.valid_pointer m b2 (Int.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Int.unsigned (Int.add ofs1 (Int.repr delta1)) <> Int.unsigned (Int.add ofs2 (Int.repr delta2)).

Remark val_inject_vtrue: forall f, val_inject f Vtrue Vtrue.
Proof. unfold Vtrue; auto. Qed.

Remark val_inject_vfalse: forall f, val_inject f Vfalse Vfalse.
Proof. unfold Vfalse; auto. Qed.

Remark val_inject_of_bool: forall f b, val_inject f (Values.Val.of_bool b) (Values.Val.of_bool b).
Proof. 
  intros. unfold Values.Val.of_bool. 
  destruct b; [apply val_inject_vtrue|apply val_inject_vfalse]. 
Qed.

Hint Resolve val_inject_vtrue val_inject_vfalse val_inject_of_bool.

Ltac TrivialInject :=
  match goal with
  | |- exists v', Some ?v = Some v' /\ _ => (exists v; split; auto)
  | _ => idtac
  end.

Definition vptr1 := (fun b i => Mem.valid_pointer m b (Int.unsigned i)).
Definition vptr2 := (fun b i => Mem.valid_pointer m' b (Int.unsigned i)).

Lemma sem_cast_inject:
  forall v1 ty1 ty v tv1
    (SC: sem_cast vptr1 v1 ty1 ty = Some v)
    (VI: val_inject f v1 tv1),
  exists tv, sem_cast vptr2 tv1 ty1 ty = Some tv /\ 
        val_inject f v tv.
Proof.
  unfold sem_cast; intros; destruct (classify_cast ty1 ty);
  inv VI; inv SC; TrivialInject.
  - econstructor; eauto. 
  - destruct (cast_float_int si2 f0); inv H0; TrivialInject.
  - destruct (cast_single_int si2 f0); inv H0; TrivialInject.
  - destruct (cast_float_long si2 f0); inv H0; TrivialInject.
  - destruct (cast_single_long si2 f0); inv H0; TrivialInject.
  - revert H0; destr_cond_match; try discriminate.
    intro A; inv A.
    unfold vptr1, vptr2 in *; erewrite valid_pointer_inj; eauto.
  - destruct (ident_eq id1 id2 && fieldlist_eq fld1 fld2); inv H0; TrivialInject. econstructor; eauto.
  - destruct (ident_eq id1 id2 && fieldlist_eq fld1 fld2); inv H0; TrivialInject. econstructor; eauto.
  - econstructor; eauto.
Qed.


Ltac inject_auto :=
  repeat match goal with
             H: wf_inj ?ei |- ?ei _ (Eunop _ _ _) (Eunop _ _ _ ) =>
             apply (ei_unop _ H); auto
           | H: wf_inj ?ei |- ?ei _ (Ebinop _ _ _ _ _) (Ebinop _ _ _ _ _ ) =>
             apply (ei_binop _ H); auto
           | H: wf_inj ?ei |- ?ei _ (Eval _) (Eval _) =>
             apply (vi_ei _ H); simpl; auto
         end.

Lemma sem_cast_expr_inject:
  forall ei (wf: wf_inj ei) v1 ty1 ty v tv1,
    sem_cast_expr v1 ty1 ty = Some v ->
    ei f v1 tv1 ->
    exists tv, sem_cast_expr tv1 ty1 ty = Some tv /\ ei f v tv.
Proof.
  unfold sem_cast_expr; intros; destruct (classify_cast ty1 ty);
  inv H; try (eexists; split; eauto);
  try (try destruct si2, sz2; simpl; unfold expr_cast_gen, expr_cast_int_int, Val.loword; repeat inject_auto; auto; fail).
  unfold Val.sign_ext. eapply ei_unop; eauto.
  destr_cond_match; try congruence; eauto. 
  revert H2; destr_cond_match; try congruence; eauto. 
  destr_cond_match; try congruence; eauto. 
  revert H2; destr_cond_match; try congruence; eauto. 
Qed.

Lemma sem_unary_operation_inject:
  forall op v1 ty v tv1,
  sem_unary_operation vptr1 op v1 ty = Some v ->
  val_inject f v1 tv1 ->
  exists tv, sem_unary_operation vptr2 op tv1 ty = Some tv /\ val_inject f v tv.
Proof.
  unfold sem_unary_operation; intros. destruct op.
  (* notbool *)
  - unfold sem_notbool in *; destruct (classify_bool ty); inv H0; inv H; TrivialInject.
    unfold vptr1, vptr2 in *.
    revert H1; destr_cond_match; try discriminate. intro A; inv A.
    erewrite valid_pointer_inj; eauto.
  (* notint *)
  - unfold sem_notint in *; destruct (classify_notint ty); inv H0; inv H; TrivialInject.
  (* neg *)
  - unfold sem_neg in *; destruct (classify_neg ty); inv H0; inv H; TrivialInject.
  (* absfloat *)
  - unfold sem_absfloat in *; destruct (classify_neg ty); inv H0; inv H; TrivialInject.
Qed.



Lemma sem_unary_operation_expr_inject:
  forall ei (wf: wf_inj ei) op v1 ty v tv1,
  sem_unary_operation_expr op v1 ty = v ->
  ei f v1 tv1 ->
  exists tv, sem_unary_operation_expr op tv1 ty = tv /\ ei f v tv.
Proof.
  unfold sem_unary_operation; intros. destruct op; simpl in *.
  - unfold sem_notbool_expr in *.
    destruct (classify_bool ty); inv H; eexists; split; eauto;
    repeat inject_auto. 
  - unfold sem_notint_expr in *.
    destruct (classify_notint ty); inv H; eexists; split; eauto;
    inject_auto; constructor; simpl; auto.
  - unfold sem_neg_expr in *.
    destruct (classify_neg ty); inv H; eexists; split; eauto;
    inject_auto; constructor; simpl; auto.
  - unfold sem_absfloat_expr in *. subst.
    destruct (classify_neg ty); eexists; split; eauto;
    unfold expr_cast_gen; try destruct s; repeat inject_auto.
Qed.


Definition optval_self_injects (ov: option val) : Prop :=
  match ov with
  | Some (Vptr b ofs) => False
  | _ => True
  end.


Definition optval_self_injects_expr (ov: option expr_sym) : Prop :=
  match ov with
  | Some e => forall (ei: _ -> _ -> _ -> Prop) (f: meminj), ei f e e
  | _ => True
  end.

Remark sem_binarith_inject:
  forall sem_int sem_long sem_float sem_single v1 t1 v2 t2 v v1' v2',
  sem_binarith vptr1 sem_int sem_long sem_float sem_single v1 t1 v2 t2 = Some v ->
  val_inject f v1 v1' -> val_inject f v2 v2' ->
  (forall sg n1 n2, optval_self_injects (sem_int sg n1 n2)) ->
  (forall sg n1 n2, optval_self_injects (sem_long sg n1 n2)) ->
  (forall n1 n2, optval_self_injects (sem_float n1 n2)) ->
  (forall n1 n2, optval_self_injects (sem_single n1 n2)) ->
  exists v', sem_binarith vptr2 sem_int sem_long sem_float sem_single v1' t1 v2' t2 = Some v' /\ val_inject f v v'.
Proof.
  intros. 
  assert (SELF: forall ov v, ov = Some v -> optval_self_injects ov -> val_inject f v v).
  {
    intros. subst ov; simpl in H7. destruct v0; contradiction || constructor.
  }
  unfold sem_binarith in *.
  set (c := classify_binarith t1 t2) in *.
  set (t := binarith_type c) in *.
  destruct (sem_cast vptr1 v1 t1 t) as [w1|] eqn:C1; try discriminate.
  destruct (sem_cast vptr1 v2 t2 t) as [w2|] eqn:C2; try discriminate.
  exploit (sem_cast_inject v1); eauto. intros (w1' & C1' & INJ1).
  exploit (sem_cast_inject v2); eauto. intros (w2' & C2' & INJ2).
  rewrite C1'; rewrite C2'.
  destruct c; inv INJ1; inv INJ2; discriminate || eauto.
Qed.


Definition sem_conserves_inject (sem: expr_sym -> expr_sym -> option expr_sym) : Prop :=
  forall ei (wf: wf_inj ei)  f v1 v2 v1' v2' v',
    ei f v1 v1' ->
    ei f v2 v2' ->
    sem v1 v2 = Some v' ->
    exists v'',
      sem v1' v2' = Some v'' /\ 
      ei f v' v''.

Remark sem_binarith_expr_inject:
  forall ei (wf: wf_inj ei) sem_int sem_long sem_float sem_single v1 t1 v2 t2 v v1' v2'
         (SBE: sem_binarith_expr sem_int sem_long sem_float sem_single v1 t1 v2 t2 = Some v)
         (EI1: ei f v1 v1')
         (EI2: ei f v2 v2')
         (SCIi: forall sg, sem_conserves_inject (sem_int sg))
         (SCIl: forall sg, sem_conserves_inject (sem_long sg))
         (SCIf: sem_conserves_inject sem_float)
         (SCIs: sem_conserves_inject sem_single),
  exists v', sem_binarith_expr sem_int sem_long sem_float sem_single v1' t1 v2' t2 = Some v' /\
             ei f v v'.
Proof.
  intros. 
  assert (SELF: forall ov v, ov = Some v -> optval_self_injects_expr ov -> ei f v v).
  {
    intros. subst. apply H0. 
  }
  unfold sem_binarith_expr in *.
  set (c := classify_binarith t1 t2) in *.
  set (t := binarith_type c) in *.
  destruct (sem_cast_expr v1 t1 t) as [w1|] eqn:C1; try discriminate.
  destruct (sem_cast_expr v2 t2 t) as [w2|] eqn:C2; try discriminate.
  exploit (sem_cast_expr_inject ei wf v1); eauto. intros (w1' & C1' & INJ1).
  exploit (sem_cast_expr_inject ei wf v2); eauto. intros (w2' & C2' & INJ2).
  rewrite C1'; rewrite C2'. 
  destruct c; try discriminate.
  eapply SCIi; eauto.
  eapply SCIl; eauto.
  eapply SCIf; eauto.
  eapply SCIs; eauto.
Qed.

Remark sem_shift_inject:
  forall sem_int sem_long v1 t1 v2 t2 v v1' v2',
  sem_shift sem_int sem_long v1 t1 v2 t2 = Some v ->
  val_inject f v1 v1' -> val_inject f v2 v2' ->
  exists v', sem_shift sem_int sem_long v1' t1 v2' t2 = Some v' /\ val_inject f v v'.
Proof.
  intros. exists v.
  unfold sem_shift in *; destruct (classify_shift t1 t2); inv H0; inv H1; try discriminate.
  destruct (Int.ltu i0 Int.iwordsize); inv H; auto.
  destruct (Int64.ltu i0 Int64.iwordsize); inv H; auto.
  destruct (Int64.ltu i0 (Int64.repr 32)); inv H; auto.
  destruct (Int.ltu i0 Int64.iwordsize'); inv H; auto.
Qed.



Definition sem_conserves_inject2 (sem: expr_sym -> expr_sym -> expr_sym) : Prop :=
  forall ei (wf: wf_inj ei) f v1 v2 v1' v2',
    ei f v1 v1' ->
    ei f v2 v2' ->
    ei f (sem v1 v2) (sem v1' v2').

Remark sem_shift_expr_inject:
  forall ei (wf: wf_inj ei) sem_int sem_long v1 t1 v2 t2 v v1' v2'
         (SSE:sem_shift_expr sem_int sem_long v1 t1 v2 t2 = Some v)
         (EI1: ei f v1 v1')
         (EI2: ei f v2 v2')
         (SCIi: forall sg, sem_conserves_inject2 (sem_int sg))
         (SCIl: forall sg, sem_conserves_inject2 (sem_long sg)),
  exists v', sem_shift_expr sem_int sem_long v1' t1 v2' t2 = Some v' /\ ei f v v'.
Proof.
  intros.
  unfold sem_shift_expr in *.
  destruct (classify_shift t1 t2); try discriminate; inv SSE;
  eexists; split; simpl; eauto.
  eapply SCIi; eauto.
  eapply SCIl; eauto.
  eapply SCIi; eauto. unfold expr_cast_gen. destruct s; repeat inject_auto.
  eapply SCIl; eauto. unfold expr_cast_gen. repeat inject_auto.
Qed.

Remark sem_cmp_inj:
  forall cmp v1 tv1 ty1 v2 tv2 ty2 v,
  sem_cmp cmp v1 ty1 v2 ty2 (Mem.valid_pointer m) = Some v ->
  val_inject f v1 tv1 ->
  val_inject f v2 tv2 ->
  exists tv, sem_cmp cmp tv1 ty1 tv2 ty2 (Mem.valid_pointer m') = Some tv /\ val_inject f v tv.
Proof.
  intros.
  unfold sem_cmp in *; destruct (classify_cmp ty1 ty2).
- (* pointer - pointer *)
  destruct (Values.Val.cmpu_bool (Mem.valid_pointer m) cmp v1 v2) as [b|] eqn:E; simpl in H; inv H.
  replace (Values.Val.cmpu_bool (Mem.valid_pointer m') cmp tv1 tv2) with (Some b).
  simpl. TrivialInject. 
  symmetry. eapply val_cmpu_bool_inject; eauto. 
- (* pointer - long *)
  destruct v2; try discriminate. inv H1. 
  set (v2 := Vint (Int.repr (Int64.unsigned i))) in *.
  destruct (Values.Val.cmpu_bool (Mem.valid_pointer m) cmp v1 v2) as [b|] eqn:E; simpl in H; inv H.
  replace (Values.Val.cmpu_bool (Mem.valid_pointer m') cmp tv1 v2) with (Some b).
  simpl. TrivialInject. 
  symmetry. eapply val_cmpu_bool_inject with (v2 := v2); eauto. constructor. 
- (* long - pointer *)
  destruct v1; try discriminate. inv H0. 
  set (v1 := Vint (Int.repr (Int64.unsigned i))) in *.
  destruct (Values.Val.cmpu_bool (Mem.valid_pointer m) cmp v1 v2) as [b|] eqn:E; simpl in H; inv H.
  replace (Values.Val.cmpu_bool (Mem.valid_pointer m') cmp v1 tv2) with (Some b).
  simpl. TrivialInject. 
  symmetry. eapply val_cmpu_bool_inject with (v1 := v1); eauto. constructor. 
- (* numerical - numerical *)
  assert (SELF: forall b, optval_self_injects (Some (Values.Val.of_bool b))).
  {
    destruct b; exact I.
  }
  eapply sem_binarith_inject; eauto.
Qed.


Remark sem_cmp_expr_inj:
  forall ei (wf: wf_inj ei) cmp v1 tv1 ty1 v2 tv2 ty2 v,
  sem_cmp_expr cmp v1 ty1 v2 ty2 = Some v ->
  ei f v1 tv1 ->
  ei f v2 tv2 ->
  exists tv, sem_cmp_expr cmp tv1 ty1 tv2 ty2 = Some tv /\   ei f v tv.
Proof.
  intros.
  unfold sem_cmp_expr in *; destruct (classify_cmp ty1 ty2); inv H;
  try (eexists; split; eauto; [idtac];
  unfold expr_cast_gen; repeat inject_auto).

  eapply sem_binarith_expr_inject; eauto;
   red; intros; eexists; split; eauto; inv H4; inject_auto.
Qed.

Lemma sem_binary_operation_inj:
  forall op v1 ty1 v2 ty2 v tv1 tv2,
  sem_binary_operation op v1 ty1 v2 ty2 (Mem.valid_pointer m) = Some v ->
  val_inject f v1 tv1 -> val_inject f v2 tv2 ->
  exists tv, sem_binary_operation op tv1 ty1 tv2 ty2 (Mem.valid_pointer m') = Some tv /\ val_inject f v tv.
Proof.
  unfold sem_binary_operation; intros; destruct op.
- (* add *)
  unfold sem_add in *; destruct (classify_add ty1 ty2).
  + inv H0; inv H1; inv H. TrivialInject. 
    econstructor. eauto. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  + inv H0; inv H1; inv H. TrivialInject. 
    econstructor. eauto. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  + inv H0; inv H1; inv H. TrivialInject. 
    econstructor. eauto. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  + inv H0; inv H1; inv H. TrivialInject. 
    econstructor. eauto. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  + eapply sem_binarith_inject; eauto; intros; exact I.
- (* sub *)
  unfold sem_sub in *; destruct (classify_sub ty1 ty2).
  + inv H0; inv H1; inv H. TrivialInject.
    econstructor. eauto. rewrite Int.sub_add_l. auto.
  + inv H0; inv H1; inv H. TrivialInject.
    destruct (eq_block b1 b0); try discriminate. subst b1. 
    rewrite FB in FB0; inv FB0. rewrite dec_eq_true. 
    destruct (Int.eq (Int.repr (sizeof ty)) Int.zero); inv H1.
    rewrite Int.sub_shifted. TrivialInject.
  + inv H0; inv H1; inv H. TrivialInject.
    econstructor. eauto. rewrite Int.sub_add_l. auto.
  + eapply sem_binarith_inject; eauto; intros; exact I.
- (* mul *)
  eapply sem_binarith_inject; eauto; intros; exact I.
- (* div *)
  eapply sem_binarith_inject; eauto; intros.
  destruct sg.
  destruct (Int.eq n2 Int.zero
            || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); exact I.
  destruct (Int.eq n2 Int.zero); exact I.
  destruct sg.
  destruct (Int64.eq n2 Int64.zero
            || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); exact I.
  destruct (Int64.eq n2 Int64.zero); exact I.
  exact I.
  exact I.
- (* mod *)
  eapply sem_binarith_inject; eauto; intros.
  destruct sg.
  destruct (Int.eq n2 Int.zero
            || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); exact I.
  destruct (Int.eq n2 Int.zero); exact I.
  destruct sg.
  destruct (Int64.eq n2 Int64.zero
            || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); exact I.
  destruct (Int64.eq n2 Int64.zero); exact I.
  exact I.
  exact I.
- (* and *)
  eapply sem_binarith_inject; eauto; intros; exact I.
- (* or *)
  eapply sem_binarith_inject; eauto; intros; exact I.
- (* xor *)
  eapply sem_binarith_inject; eauto; intros; exact I.
- (* shl *)
  eapply sem_shift_inject; eauto.
- (* shr *)
  eapply sem_shift_inject; eauto.
  (* comparisons *)
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
Qed.

Lemma sem_binary_operation_expr_inj:
  forall ei (wf: wf_inj ei) op v1 ty1 v2 ty2 v tv1 tv2,
  sem_binary_operation_expr op v1 ty1 v2 ty2 = Some v ->
    ei f v1 tv1 -> ei f v2 tv2 ->
  exists tv, sem_binary_operation_expr op tv1 ty1 tv2 ty2 = Some tv /\ ei f v tv.
Proof.
  intros.
  unfold sem_binary_operation_expr in *.
  destruct op; simpl in *;
  try (eapply sem_binarith_expr_inject; eauto;
    red; intros; eexists; split; eauto; inv H4; inject_auto; fail);
  try (    eapply sem_shift_expr_inject; eauto;
    red; intros; unfold expr_cast_gen; repeat inject_auto; fail);
  try (eapply sem_cmp_expr_inj; eauto; fail). 
  - unfold sem_add_expr in *.
    destruct (classify_add ty1 ty2); try discriminate; inv H;
    try (eexists; split; eauto; repeat inject_auto;
         constructor; simpl; auto).
    eapply sem_binarith_expr_inject; eauto;
    red; intros; eexists; split; eauto; inv H4; inject_auto.
  - unfold sem_sub_expr in *.
    destruct (classify_sub ty1 ty2); try discriminate; inv H;
    try (eexists; split; eauto; repeat inject_auto; fail).
    + eexists; split; eauto. inject_auto. unfold expr_cast_gen. inject_auto.
    + eapply sem_binarith_expr_inject; eauto;
      red; intros; eexists; split; eauto; inv H4; inject_auto.
Qed.

Lemma bool_val_inject:
  forall v ty b tv,
  bool_val vptr1 v ty = Some b ->
  val_inject f v tv ->
  bool_val vptr2 tv ty = Some b.
Proof.
  unfold bool_val; intros. 
  destruct (classify_bool ty); inv H0; try congruence.
  unfold vptr1, vptr2 in *.
  revert H; destr_cond_match; try discriminate. intro A; inv A.
  erewrite valid_pointer_inj; eauto.
Qed.

End GENERIC_INJECTION.

Lemma sem_binary_operation_inject:
  forall sm ei (wf: wf_inj ei) f m m' op v1 ty1 v2 ty2 v tv1 tv2,
  sem_binary_operation op v1 ty1 v2 ty2 (Mem.valid_pointer m) = Some v ->
  val_inject f v1 tv1 -> val_inject f v2 tv2 ->
  Mem.inject sm ei f m m' ->
  exists tv, sem_binary_operation op tv1 ty1 tv2 ty2 (Mem.valid_pointer m') = Some tv /\ val_inject f v tv.
Proof.
  intros. eapply sem_binary_operation_inj; eauto. 
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  apply (vi_ei _ wf); simpl; unfold Val.inj_ptr; rewrite H3; auto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  apply (vi_ei _ wf); simpl; unfold Val.inj_ptr; rewrite H3; auto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
Qed.


Lemma sem_binary_operation_expr_inject:
  forall sm ei (wf: wf_inj ei) f m m' op v1 ty1 v2 ty2 v tv1 tv2,
  sem_binary_operation_expr op v1 ty1 v2 ty2 = Some v ->
  ei f v1 tv1 -> ei f v2 tv2 ->
  Mem.inject sm ei f m m' ->
  exists tv, sem_binary_operation_expr op tv1 ty1 tv2 ty2 = Some tv /\ ei f v tv.
Proof.
  intros. eapply sem_binary_operation_expr_inj; eauto. 
Qed.


(** * Some properties of operator semantics *)

(** This section collects some common-sense properties about the type
  classification and semantic functions above.  These properties are
  not used in the CompCert semantics preservation proofs, but increase
  confidence in the specification and its relation with the ISO C99 standard. *)

(** Relation between Boolean value and casting to [_Bool] type. *)
 
Lemma cast_bool_bool_val_expr:
  forall v t b,
    sem_cast_expr v t (Ctypes.Tint IBool Signed noattr) = Some b ->
    same_eval b (bool_expr v t).
Proof.
  intros.
  assert (A: classify_bool t =
    match t with
    | Ctypes.Tint _ _ _ => bool_case_i
    | Tpointer _ _ | Tcomp_ptr _ _ | Tarray _ _ _ | Tfunction _ _ _ => bool_case_p
    | Ctypes.Tfloat F64 _ => bool_case_f
    | Ctypes.Tfloat F32 _ => bool_case_s
    | Ctypes.Tlong _ _ => bool_case_l
    | _ => bool_default
    end).
  {
    unfold classify_bool; destruct t; simpl; auto. destruct i; auto.
  }
  unfold bool_expr. rewrite A. unfold sem_cast_expr in H. 
  destruct t; simpl in *; auto; inv H;
  try solve [red; simpl; intros; seval'; destr].
  red; simpl; intros; seval.
  red; simpl; intros;
  des f; inv H1; simpl; seval.
  rewrite Float32.cmp_ne_eq. destr.
  rewrite Float.cmp_ne_eq. destr.
Qed.


(** Relation between Boolean value and Boolean negation. *)

Lemma notbool_bool_expr:
  forall v t,
    same_eval (sem_notbool_expr v t) (Eunop OpNotbool Tint (bool_expr v t)).
Proof.
  intros. unfold sem_notbool_expr, bool_expr. 
  destruct (classify_bool t); auto; red; simpl; intros; try solve[seval; destr].
  - seval. des (Int.eq i Int.zero).
  - seval. rewrite Float.cmp_ne_eq. destr.
  - seval. rewrite Float32.cmp_ne_eq. destr.
  - seval. des (Int.eq i Int.zero).
  - seval. des (Int.eq i Int.zero).
Qed.


Lemma sem_unary_operation_expr_se:
  forall u t e e',
    same_eval e e' ->
    same_eval (sem_unary_operation_expr u e t)
                   (sem_unary_operation_expr u e' t).
Proof.
  destruct u; simpl; intros;
  unfold sem_notbool_expr, sem_notint_expr, sem_neg_expr, sem_absfloat_expr;
  destr_cond_match; se_rew.
Qed.

Lemma expr_cast_int_int_se:
  forall sz2 si2 e e',
    same_eval e e' ->
    same_eval (expr_cast_int_int sz2 si2 e)
                   (expr_cast_int_int sz2 si2 e').
Proof.
  intros.
  destruct sz2; destruct si2; se_rew.
Qed.

Lemma expr_cast_gen_se:
  forall t s t' s' e e',
    same_eval e e' ->
    same_eval (expr_cast_gen t s t' s' e)
                   (expr_cast_gen t s t' s' e').
Proof.
  intros.
  destruct t; destruct s; destruct t'; destruct s'; se_rew.
Qed.

Ltac se_rew' :=
  repeat ((apply unop_same_eval; simpl; auto)
            ||
            (apply binop_same_eval; simpl; eauto)
            ||
            (apply expr_cast_int_int_se; simpl; eauto)
            ||
            (apply expr_cast_gen_se; simpl; eauto)
            || reflexivity || auto).


Definition conserves_same_eval_unary (f: expr_sym -> option expr_sym) : Prop :=
  forall e e',
    same_eval e e' ->
    match
      f e, f e'
    with
       | Some a, Some b => same_eval a b
       | None, None => True
       | _, _ => False
    end.

Lemma sem_cast_expr_se:
  forall t t',
    conserves_same_eval_unary (fun e => sem_cast_expr e t t').
Proof.
  intros.
  unfold conserves_same_eval_unary; intros.
  unfold sem_cast_expr.
  destruct (classify_cast t t'); se_rew'.
  destr_cond_match; auto.
  destr_cond_match; auto.
Qed.

Lemma sem_binarith_expr_se:
  forall si sl sf ss t t'
         (si_norm: forall s, conserves_same_eval (si s))
         (sl_norm: forall s, conserves_same_eval (sl s))
         (sf_norm: conserves_same_eval sf)
         (ss_norm: conserves_same_eval ss),
    conserves_same_eval (fun e f => sem_binarith_expr si sl sf ss e t f t').
Proof.
  red; intros.
  unfold sem_binarith_expr. 
  generalize (sem_cast_expr_se t (binarith_type (classify_binarith t t')) _ _ H).
  generalize (sem_cast_expr_se t' (binarith_type (classify_binarith t t')) _ _ H0).
  repeat destr_cond_match; try intuition congruence; try discriminate.
  - destruct (classify_binarith t t'); try discriminate;
    intros A B.
    generalize (si_norm s _ _ _ _ B A); rewrite Heqo4; rewrite Heqo1; auto.
    generalize (sl_norm s _ _ _ _ B A); rewrite Heqo4; rewrite Heqo1; auto.
    generalize (sf_norm _ _ _ _ B A); rewrite Heqo4; rewrite Heqo1; auto.
    generalize (ss_norm _ _ _ _ B A); rewrite Heqo4; rewrite Heqo1; auto.
  -  destruct (classify_binarith t t'); try discriminate;
     intros A B.
     generalize (si_norm s _ _ _ _ B A); rewrite Heqo4; rewrite Heqo1; auto.
     generalize (sl_norm s _ _ _ _ B A); rewrite Heqo4; rewrite Heqo1; auto.
     generalize (sf_norm _ _ _ _ B A); rewrite Heqo4; rewrite Heqo1; auto.
     generalize (ss_norm _ _ _ _ B A); rewrite Heqo4; rewrite Heqo1; auto.
  -  destruct (classify_binarith t t'); try discriminate;
     intros A B.
     generalize (si_norm s _ _ _ _ B A); rewrite Heqo2; rewrite Heqo1; auto.
     generalize (sl_norm s _ _ _ _ B A); rewrite Heqo2; rewrite Heqo1; auto.
     generalize (sf_norm _ _ _ _ B A); rewrite Heqo2; rewrite Heqo1; auto.
     generalize (ss_norm _ _ _ _ B A); rewrite Heqo2; rewrite Heqo1; auto. 
Qed.

Lemma sem_shift_expr_se:
  forall si sl t t'
         (si_norm: forall s a b c d,
                     same_eval a b ->
                     same_eval c d ->
                     same_eval (si s a c) (si s b d))
         (sl_norm: forall s a b c d,
                     same_eval a b ->
                     same_eval c d ->
                     same_eval (sl s a c) (sl s b d)),
    conserves_same_eval (fun e f => sem_shift_expr si sl e t f t').
Proof.
  red; intros.
  unfold sem_shift_expr.
  destruct (classify_shift t t'); try discriminate.
  apply si_norm; auto.
  apply sl_norm; auto.
  apply si_norm; auto.
  apply expr_cast_gen_se; auto.
  apply sl_norm; auto.
  apply expr_cast_gen_se; auto.
  auto.
Qed.


Lemma sem_binary_operation_expr_se:
  forall b t t' e e' f f',
    same_eval e e' ->
    same_eval f f' ->
    match sem_binary_operation_expr b e t f t', sem_binary_operation_expr b e' t f' t' with
        Some a, Some b => same_eval a b
      | None, None => True
      | _ , _ => False
    end.
Proof.
  destruct b; simpl; intros;
  unfold sem_add_expr, sem_sub_expr, sem_mul_expr, sem_div_expr, sem_mod_expr,
  sem_shl_expr, sem_shr_expr, sem_cmp_expr;
  try match goal with
      |- context [ match ?f ( _ :type) (_: type) with _ => _ end ] =>
      destruct (f t t'); se_rew
  end;
      try (apply sem_binarith_expr_se; auto; red; intros; auto; apply binop_same_eval; auto);
  try (apply sem_shift_expr_se; auto; intros; auto; apply binop_same_eval; auto;
       apply expr_cast_gen_se; auto).
Qed.


Lemma bool_expr_se:
  forall v v' t,
    same_eval v v' ->
    same_eval (bool_expr v t) (bool_expr v' t).
Proof.
  unfold bool_expr.
  intros.
  destruct (classify_bool t); simpl; se_rew.
Qed.

 
