Require Import Coqlib.
Require Import AST.
Require Import Maps.
Require Import Values.
Require Import Globalenvs.
Require Import Ctypes.
Require Import Values_symbolictype.
Require Import Values_symbolic.
Require Import Normalise.
Require Import NormaliseSpec.
Require Import ExprEval.
Require Import Memory.
Require Import Memdata.
Require Import Cop.
Require Import Integers.
Require Import Floats.


(** This module defines equivalence relations on symbolic expressions, that are
    then lifted to memories, and we prove that the primitive memory operations
    preserve these equivalences.  *)



Lemma unop_ext_se:
  forall s0 n v1,
    0 < n ->
   same_eval
     (Eunop
        (match s0 with
         | Signed => OpSignext
         | Unsigned => OpZeroext
         end n) Tint v1)
     (Eunop
        (match s0 with
         | Signed => OpSignext
         | Unsigned => OpZeroext
         end n) Tint
        (Eunop
           (match s0 with
            | Signed => OpSignext
            | Unsigned => OpZeroext
            end n) Tint v1)).
Proof.
  red; intros.
  des s0; seval.
  rewrite Int.sign_ext_widen; auto; try omega.
  rewrite Int.zero_ext_widen; auto; try omega.
Qed.

Lemma boolval_idem_se:
  forall v1,
    same_eval (Eunop OpBoolval Tint v1)
              (Eunop OpBoolval Tint (Eunop OpBoolval Tint v1)).
Proof.
  intros; red; simpl; auto.
  destr; seval. 
  destruct (Int.eq i Int.zero); simpl.
  rewrite Int.eq_true; simpl; auto.
  rewrite Int.eq_false; simpl; auto.
  apply Int.one_not_zero.
Qed.

Lemma notbool_boolval_se:
  forall e,
    same_eval (Eunop OpNotbool Tint e)
              (Eunop OpBoolval Tint (Eunop OpNotbool Tint e)).
Proof.
  intros; red; simpl; auto.
  - destr; seval. 
    destruct (Int.eq i Int.zero); simpl; auto.
Qed.


Lemma nec_cmp_ne_zero:
  forall v,
    same_eval
      (Eunop OpBoolval Tint v)
      (Val.cmp Cne v (Eval (Vint Int.zero))).
Proof.
  intros; red; simpl; try red; intros; simpl; try tauto.
  seval.
Qed.

Lemma norm_boolval_cmp:
  forall sg c t v1 v2,
    same_eval
      (Ebinop (OpCmp sg c) t t v1 v2)
      (Eunop OpBoolval Tint (Ebinop (OpCmp sg c) t t v1 v2)).
Proof.
  intros; red; simpl; try red; intros; simpl; try tauto.
  seval; des t; des sg; destr.
Qed.


Lemma eqm_notbool_ceq_cne:
  forall sg t v1 v2,
    same_eval
      (Eunop OpNotbool Tint
             (Ebinop (OpCmp sg Ceq) t t v1 v2))
      (Ebinop (OpCmp sg Cne) t t v1 v2).
Proof.
  red; simpl; intros.
  seval; des t; des sg;
  try (rewrite Float.cmp_ne_eq || rewrite Float32.cmp_ne_eq);
  destr.
Qed.


Lemma norm_cne_zero_boolval:
  forall v,
    same_eval
      (Ebinop (OpCmp SESigned Cne) Tint Tint v (Eval (Vint Int.zero)))
      (Eunop OpBoolval Tint v).
Proof.
  red; simpl; intros; auto. seval.
Qed.




Lemma eqm_notbool_eq_zero:
  forall va sg,
    same_eval
      (Eunop OpNotbool Tint va)
      (Ebinop (OpCmp sg Ceq) Tint Tint va (Eval (Vint Int.zero))).
Proof.
  red; simpl; intros; auto.
  seval; des sg.
Qed.


Lemma val_longofwords_eq:
  forall v,
  Val.has_type v Tlong ->
  same_eval (Val.longofwords (Val.hiword v) (Val.loword v)) v.
Proof.
  intros.
  red; intros; simpl.
  generalize (expr_type _ _ H cm em); seval.
  rewrite Int64.ofwords_recompose. auto.
Qed.

Lemma weak_wt_lessdef:
  forall e t v,
    weak_wt e t ->
    (wt_expr e t -> Val.lessdef e v) ->
    Val.lessdef e v.
Proof.
  intros e t v [A | A]; eauto.
  red; intros.
  rewrite nwt_expr_undef; auto.
Qed.



Lemma se_boolval:
  forall i,
    same_eval
      (Eunop OpBoolval Tint (Eval (Vint i)))
      (Eval (Vint (if Int.eq i Int.zero then Int.zero else Int.one))).
Proof.
  red; simpl; intros; seval. 
  destruct (Int.eq i Int.zero); simpl; auto.
Qed.

Lemma se_f2s:
  forall f,
    same_eval
      (Eval (Vsingle (Float.to_single f)))
      (Eunop (OpConvert SESigned (Tsingle, SESigned)) Tfloat (Eval (Vfloat f))).
Proof.
  red; simpl; intros; seval.
  reflexivity. 
Qed.

Lemma se_s2f:
  forall f,
    same_eval
      (Eval (Vfloat (Float.of_single f)))
      (Eunop (OpConvert SESigned (Tfloat,SESigned)) Tsingle (Eval (Vsingle f))).
Proof.
  red; simpl; intros; seval.
  reflexivity. 
Qed.


Lemma se_z32:
  forall i,
    same_eval (Eunop (OpZeroext 32) Tint i) (Eunop (OpZeroext 32) Tint (Eunop (OpZeroext 32) Tint i)).
Proof.
  red; intros; seval. rewrite Int.zero_ext_above with (n:=32%Z); auto; unfsize; Psatz.lia.
Qed.

Lemma se_se:
  forall v1,
    same_eval (Val.sign_ext 32 v1) (Val.sign_ext 32 (Val.sign_ext 32 v1)).
Proof.
  red; intros; seval.
  rewrite Int.sign_ext_above with (n:=32%Z); auto; unfsize; Psatz.lia.
Qed.

Lemma sem_cast_expr_idem:
  forall v1 ta ty v2,
    sem_cast_expr v1 ta ty = Some v2 ->
    exists v2',
      sem_cast_expr v2 ty ty = Some v2' /\
      same_eval v2 v2'.
Proof.
  intros v1 ta ty v2 SCE.
  unfold sem_cast_expr in *.
  Ltac t := eexists; split; eauto;
    try apply unop_ext_se; try omega;
    try apply se_z32; try apply boolval_idem_se; try apply notbool_boolval_se;
    try apply se_se;
    try reflexivity.

  Ltac ts s := t; try (red; intros; des s; seval).

  Ltac convtac:=
    unfold convert_t;
    repeat match goal with
      |- context [Val.maketotal (?f ?v)] => unfold f
    | |- context [option_map ?f ?v] => des v
           end.

  Ltac sim :=
    unfold expr_cast_gen; simpl;
    match goal with
      |- exists a, Some ?v1 = Some ?v2 /\ same_eval _ _ =>
      match goal with
        |- context[sg_conv ?s] => ts s
      | _ => ts Signed
      end    
    end.
  
  des ta; des ty; inv SCE;
  try (eexists; split; eauto; reflexivity);
  try (des i; inv H0; t; fail);
  try (des i0; inv H0; ts s; fail);
  try (des f; inv H0; ts s; fail);
  try (des f0; fail); try (sim; fail).
  - ts s.
    rewrite ! Int.sign_ext_above with (n:=32%Z); try (unfsize; Psatz.lia); auto.
    rewrite ! Int.sign_ext_above with (n:=32%Z); try (unfsize; Psatz.lia); auto.
  - ts s.
    rewrite ! Int.sign_ext_above with (n:=32%Z); try (unfsize; Psatz.lia); auto.
    rewrite ! Int.sign_ext_above with (n:=32%Z); try (unfsize; Psatz.lia); auto.
  - des i; des f; inv H0; ts s.
  - des f; inv H0; ts s; convtac.
  - des f0; des f; inv H0; t;
    red; intros; simpl; convtac; seval.
  - destruct (ident_eq i0 i0); destruct (fieldlist_eq f0 f0); simpl; try congruence.
    t.
  - destruct (ident_eq i0 i0); destruct (fieldlist_eq f0 f0); simpl; try congruence.
    t. 
Qed.
