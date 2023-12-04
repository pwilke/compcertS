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

(** * Correctness of the translation from Clight to C#minor. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import AST.
Require Import Values.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Clight.
Require Import Cminor.
Require Import Csharpminor.
Require Import Cshmgen.
Require Import Values_symbolictype.
Require Import Values_symbolic.
Require Import Normalise.
Require Import NormaliseSpec.
Require Import ExprEval.
Require Import Memory.
Require Import Equivalences.
Require Import MemRel.
Require Import ClightRel.

(** * Properties of operations over types *)

Remark transl_params_types:
  forall params,
  map typ_of_type (map snd params) = typlist_of_typelist (type_of_params params).
Proof.
  induction params; simpl. auto. destruct a as [id ty]; simpl. f_equal; auto.
Qed.

Lemma transl_fundef_sig1:
  forall f tf args res cc,
  transl_fundef f = OK tf ->
  classify_fun (type_of_fundef f) = fun_case_f args res cc ->
  funsig tf = signature_of_type args res cc.
Proof.
  intros. destruct f; simpl in *. 
  monadInv H. monadInv EQ. simpl. inversion H0.    
  unfold signature_of_function, signature_of_type.
  f_equal. apply transl_params_types.
  destruct (signature_eq (ef_sig e) (signature_of_type t t0 c)); inv H.
  simpl. congruence.
Qed.

Lemma transl_fundef_sig2:
  forall f tf args res cc,
  transl_fundef f = OK tf ->
  type_of_fundef f = Tfunction args res cc ->
  funsig tf = signature_of_type args res cc.
Proof.
  intros. eapply transl_fundef_sig1; eauto.
  rewrite H0; reflexivity.
Qed.

(** * Properties of the translation functions *)

(** Transformation of expressions and statements. *)

Lemma transl_expr_lvalue:
  forall ge e le m a locofs ta,
  Clight.eval_lvalue ge e le m a locofs ->
  transl_expr a = OK ta ->
  (exists tb, transl_lvalue a = OK tb /\ make_load tb (typeof a) = OK ta).
Proof.
  intros until ta; intros EVAL TR. inv EVAL; simpl in TR.
  -  (* var local *)
    (exists (Eaddrof id); auto).
  - (* var global *)
    (exists (Eaddrof id); auto).
  - (* deref *)
    monadInv TR. exists x; auto.
  - (* field struct *)
    rewrite H0 in TR. monadInv TR.
    econstructor; split. simpl. rewrite H0.
    rewrite EQ; rewrite EQ1; simpl; eauto. auto.
  - (* field union *)
    rewrite H0 in TR. monadInv TR.
    econstructor; split. simpl. rewrite H0. rewrite EQ; simpl; eauto. auto.
Qed.

(** Properties of labeled statements *)

Lemma transl_lbl_stmt_1:
  forall tyret nbrk ncnt n sl tsl,
  transl_lbl_stmt tyret nbrk ncnt sl = OK tsl ->
  transl_lbl_stmt tyret nbrk ncnt (Clight.select_switch n sl) = OK (select_switch n tsl).
Proof.
  intros until n.
  assert (DFL: forall sl tsl,
    transl_lbl_stmt tyret nbrk ncnt sl = OK tsl ->
    transl_lbl_stmt tyret nbrk ncnt (Clight.select_switch_default sl) = OK (select_switch_default tsl)).
  {
    induction sl; simpl; intros. 
    inv H; auto.
    monadInv H. simpl. destruct o; eauto. simpl; rewrite EQ; simpl; rewrite EQ1; auto.
  }
  assert (CASE: forall sl tsl,
    transl_lbl_stmt tyret nbrk ncnt sl = OK tsl ->
    match Clight.select_switch_case n sl with
    | None =>
        select_switch_case n tsl = None
    | Some sl' =>
        exists tsl',
           select_switch_case n tsl = Some tsl'
        /\ transl_lbl_stmt tyret nbrk ncnt sl' = OK tsl'
    end).
  {
    induction sl; simpl; intros.
    inv H; auto. 
    monadInv H; simpl. destruct o. destruct (zeq z n).
    econstructor; split; eauto. simpl; rewrite EQ; simpl; rewrite EQ1; auto.
    apply IHsl; auto.
    apply IHsl; auto.
  }
  intros. specialize (CASE _ _ H). unfold Clight.select_switch, select_switch. 
  destruct (Clight.select_switch_case n sl) as [sl'|]. 
  destruct CASE as [tsl' [P Q]]. rewrite P, Q. auto.
  rewrite CASE. auto. 
Qed.

Lemma transl_lbl_stmt_2:
  forall tyret nbrk ncnt sl tsl,
  transl_lbl_stmt tyret nbrk ncnt sl = OK tsl ->
  transl_statement tyret nbrk ncnt (seq_of_labeled_statement sl) = OK (seq_of_lbl_stmt tsl).
Proof.
  induction sl; intros.
  monadInv H. auto. 
  monadInv H. simpl. rewrite EQ; simpl. rewrite (IHsl _ EQ1). simpl. auto.
Qed.

(** * Correctness of Csharpminor construction functions *)

Section CONSTRUCTORS.

  Variable ge: genv.
  

Lemma make_intconst_correct:
  forall n e le m,
  eval_expr ge e le m (make_intconst n) (Eval (Vint n)).
Proof.
  intros. unfold make_intconst. econstructor. reflexivity. 
Qed.

Lemma make_floatconst_correct:
  forall n e le m,
  eval_expr ge e le m (make_floatconst n) (Eval (Vfloat n)).
Proof.
  intros. unfold make_floatconst. econstructor. reflexivity. 
Qed.

Lemma make_singleconst_correct:
  forall n e le m,
  eval_expr ge e le m (make_singleconst n) (Eval (Vsingle n)).
Proof.
  intros. unfold make_singleconst. econstructor. reflexivity. 
Qed.

Lemma make_longconst_correct:
  forall n e le m,
  eval_expr ge e le m (make_longconst n) (Eval (Vlong n)).
Proof.
  intros. unfold make_floatconst. econstructor. reflexivity. 
Qed.

Lemma make_singleoffloat_correct:
  forall a n e le m,
  eval_expr ge e le m a (Eval (Vfloat n)) ->
  eval_expr ge e le m (make_singleoffloat a) (expr_cast_gen Tfloat Signed Tsingle Signed (Eval (Vfloat n))).
Proof.
  intros. econstructor. eauto. eauto.
Qed.

Lemma make_floatofsingle_correct:
  forall a n e le m,
  eval_expr ge e le m a (Eval (Vsingle n)) ->
  eval_expr ge e le m (make_floatofsingle a) (expr_cast_gen Tsingle Signed Tfloat Signed (Eval (Vsingle n))).
Proof.
  intros. econstructor. eauto. auto.
Qed.

Lemma make_floatofint_correct:
  forall a n sg e le m,
  eval_expr ge e le m a (Eval (Vint n)) ->
  eval_expr ge e le m (make_floatofint a sg) 
            (expr_cast_gen Tint sg Tfloat Signed (Eval (Vint n))).
Proof.
  intros. unfold make_floatofint.
  destruct sg; econstructor; eauto. 
Qed.

Hint Resolve make_intconst_correct make_floatconst_correct make_longconst_correct
             make_singleconst_correct make_singleoffloat_correct make_floatofsingle_correct
             make_floatofint_correct: cshm.
Hint Constructors eval_expr eval_exprlist: cshm.
Hint Extern 2 (@eq trace _ _) => traceEq: cshm.



Lemma se_ld:
  forall a b,
    same_eval a b -> Val.lessdef a b.
Proof.
  red; intros; rewrite H; auto.
Qed.

Lemma make_cmp_ne_zero_correct:
  forall ge e le m a v v',
    eval_expr ge e le m a v ->
    Val.lessdef v' v ->
    exists v'' : expr_sym,
      eval_expr ge e le m (make_cmp_ne_zero a) v'' /\
      Val.lessdef (Eunop OpBoolval Tint v') v''.
Proof.
  intros. 
  inv H; try (eexists; split; [repeat (econstructor; simpl; eauto)|]; [idtac]);
  try (red; intros;
       rewrite nec_cmp_ne_zero;
       apply Val.lessdef_binop; auto).
  
  destruct op; simpl; try (eexists; split; [repeat (econstructor; simpl; eauto)|]; [idtac]);
  try (red; intros; rewrite nec_cmp_ne_zero; apply Val.lessdef_binop; auto);
  simpl in *; inv H3;
  (eapply Val.lessdef_trans; [eapply Val.lessdef_unop; eauto|]);
  apply se_ld; symmetry; apply norm_boolval_cmp.
Qed.

Lemma make_cast_int_correct:
  forall e le m a v v' sz si,
    eval_expr ge e le m a v ->
    Val.lessdef v' v ->
    exists v'',
      eval_expr ge e le m (make_cast_int a sz si) v'' /\
      Val.lessdef (expr_cast_int_int sz si v') v''.
Proof.
  intros. unfold make_cast_int, expr_cast_int_int.
  des sz; des si;
  try (eexists; split; [econstructor; simpl; eauto|apply Val.lessdef_unop; auto]).
  - eexists; split; eauto.
    eapply Val.lessdef_trans; [|eauto].
    red; intros; simpl; seval; auto.
    rewrite Int.zero_ext_above with (n:=32%Z); unfsize; auto; Psatz.lia.
  - eexists; split; eauto.
    eapply Val.lessdef_trans; [|eauto].
    red; intros; simpl; seval; auto.
    rewrite Int.zero_ext_above with (n:=32%Z); unfsize; auto; Psatz.lia.
  - eapply make_cmp_ne_zero_correct; eauto.
  - eapply make_cmp_ne_zero_correct; eauto.
Qed.

Hint Resolve make_cast_int_correct: cshm.

Lemma expr_cast_int_int_ld:
  forall a b sz sg,
    Val.lessdef a b ->
    Val.lessdef (expr_cast_int_int sz sg a)
                (expr_cast_int_int sz sg b).
Proof.
  des sz; des sg; apply Val.lessdef_unop; auto.
Qed.

Lemma make_cast_correct:
  forall e le m a b v v2 ty1 ty2 v'
    (CAST: make_cast ty1 ty2 a = OK b)
    (EVAL: eval_expr ge e le m a v)
    (SE: Val.lessdef v2 v)
    (SEM: sem_cast_expr v2 ty1 ty2 = Some v'),
  exists v'',
    eval_expr ge e le m b v'' /\
    Val.lessdef v' v''.
Proof.
  intros.
  Ltac t :=
    eexists; split; [eauto; repeat (econstructor; simpl; eauto)|];
    try (eapply Val.lessdef_trans; [|eauto]);
    try (
        (apply Val.lessdef_unop; auto) ||
        (apply Val.lessdef_binop; auto) ||
        red; intros; simpl; seval; auto).
  unfold make_cast, sem_cast_expr in *;
    destruct (classify_cast ty1 ty2) eqn:?; inv SEM; inv CAST; auto;
    try 
      (unfold expr_cast_gen; t;
       rewrite Int.sign_ext_above with (n:=32%Z); unfsize; auto; Psatz.lia).
  - eapply make_cast_int_correct; eauto.
  - unfold make_floatofint, expr_cast_gen. 
    des si1; t.
  - unfold make_singleofint, expr_cast_gen. 
    des si1; t.
  - (* float -> int *)
    unfold make_intoffloat, expr_cast_gen. 
    destruct si2.
    edestruct make_cast_int_correct
    with (a:= Csharpminor.Eunop Ointoffloat a)
      as [v'' [A B]]. econstructor; simpl; eauto.
    apply Val.lessdef_unop; auto.
    eexists; split; simpl; eauto.
    eapply Val.lessdef_trans; [|eauto].
    apply expr_cast_int_int_ld; auto.
    apply Val.lessdef_unop; auto.
    edestruct make_cast_int_correct
    with (a:= Csharpminor.Eunop Ointuoffloat a)
      as [v'' [A B]]. econstructor; simpl; eauto.
    apply Val.lessdef_unop; auto.
    eexists; split; simpl; eauto.
    eapply Val.lessdef_trans; [|eauto].
    apply expr_cast_int_int_ld; auto.
    apply Val.lessdef_unop; auto.

  - unfold make_intofsingle.
    destruct si2.
    edestruct make_cast_int_correct
    with (a:= Csharpminor.Eunop Ointofsingle a)
      as [v'' [A B]]. econstructor; simpl; eauto.
    apply Val.lessdef_unop; auto.
    eexists; split; simpl; eauto.
    eapply Val.lessdef_trans; [|eauto].
    apply expr_cast_int_int_ld; auto.
    apply Val.lessdef_unop; auto.
    edestruct make_cast_int_correct
    with (a:= Csharpminor.Eunop Ointuofsingle a)
      as [v'' [A B]]. econstructor; simpl; eauto.
    apply Val.lessdef_unop; auto.
    eexists; split; simpl; eauto.
    eapply Val.lessdef_trans; [|eauto].
    apply expr_cast_int_int_ld; auto.
    apply Val.lessdef_unop; auto.
  - unfold make_longofint, expr_cast_gen. 
    destruct si1; eexists; (split ;[(econstructor; simpl; eauto)|]; auto);
    apply Val.lessdef_unop; auto.
  - eapply make_cast_int_correct. 
    econstructor; simpl; eauto.
    apply Val.lessdef_unop; auto.
  - unfold make_floatoflong, expr_cast_gen. simpl.
    destruct si1; eexists; (split; [repeat (econstructor; simpl; eauto)|]); 
    apply Val.lessdef_unop; auto.
  - unfold make_singleoflong, expr_cast_gen. 
    destruct si1; eexists; (split; [repeat (econstructor; simpl; eauto)|]);
    apply Val.lessdef_unop; auto.
  - unfold make_longoffloat, expr_cast_gen.
    destruct si2; eexists; (split; [repeat (econstructor; simpl; eauto)|]);
    apply Val.lessdef_unop; auto.
  - unfold make_longofsingle, expr_cast_gen.
    destruct si2; eexists; (split; [repeat (econstructor; simpl; eauto)|]);
    apply Val.lessdef_unop; auto.
  - unfold make_floatconst, expr_cast_gen.
    eexists; (split; [repeat (econstructor; simpl; eauto)|]).
    unfold Val.cmpf, Val.cmpf_bool.
    red; intros; rewrite eqm_notbool_ceq_cne.
    apply Val.lessdef_binop; auto.
  - unfold make_singleconst.
    eexists; (split; [repeat (econstructor; simpl; eauto)|]).
    red; intros; rewrite eqm_notbool_ceq_cne.
    apply Val.lessdef_binop; auto.
  - unfold make_longconst. simpl.
    eexists; (split; [repeat (econstructor; simpl; eauto)|]).
    red; intros; rewrite eqm_notbool_ceq_cne.
    apply Val.lessdef_binop; auto.
  - unfold make_intconst. simpl.
    eexists; (split; [repeat (econstructor; simpl; eauto)|]).
    red; intros; rewrite eqm_notbool_ceq_cne.
    apply Val.lessdef_binop; auto.
  - (* struct *)
    destruct (ident_eq id1 id2 && fieldlist_eq fld1 fld2); inv H0.
    exists v; split; auto. 
  - (* union *)
    destruct (ident_eq id1 id2 && fieldlist_eq fld1 fld2); inv H0.
    exists v; split; auto. 
Qed.

Lemma make_boolean_correct:
 forall e le m a v v' ty,
  eval_expr ge e le m a v ->
  Val.lessdef v' v ->
  exists vb,
    eval_expr ge e le m (make_boolean a ty) vb
    /\ 
    Val.lessdef (bool_expr v' ty) vb.
Proof.
  intros. unfold make_boolean, bool_expr. 
  destruct (classify_bool ty) eqn:?.
- 
  destruct (make_cmp_ne_zero_correct _ _ _ _ _ _ _ H H0) as [vb [A B]].
  exists vb; split; auto.
  eapply Val.lessdef_trans; [|eauto].
  apply se_ld; apply norm_cne_zero_boolval.
- 
  destruct (make_cmp_ne_zero_correct _ _ _ _ _ _ _ H H0) as [vb [A B]].
  econstructor; split.
  econstructor; simpl; eauto with cshm.
  apply Val.lessdef_binop; auto.
- 
  destruct (make_cmp_ne_zero_correct _ _ _ _ _ _ _ H H0) as [vb [A B]].
  econstructor; split.
  econstructor; simpl; eauto with cshm.
  apply Val.lessdef_binop; auto.
- 
  destruct (make_cmp_ne_zero_correct _ _ _ _ _ _ _ H H0) as [vb [A B]].
  econstructor; split.
  econstructor; simpl; eauto with cshm.
  apply Val.lessdef_binop; auto.
- 
  destruct (make_cmp_ne_zero_correct _ _ _ _ _ _ _ H H0) as [vb [A B]].
  econstructor; split.
  econstructor; simpl; eauto with cshm.
  apply Val.lessdef_binop; auto.
-
  destruct (make_cmp_ne_zero_correct _ _ _ _ _ _ _ H H0) as [vb [A B]].
  econstructor; split.
  econstructor; simpl; eauto with cshm.
  apply Val.lessdef_binop; auto.
Qed.

Lemma make_neg_correct:
  forall a tya c va va' v e le m,
    Val.lessdef va' va ->
    sem_neg_expr va' tya = v ->
    make_neg a tya = OK c ->  
    eval_expr ge e le m a va ->
    exists v',
      eval_expr ge e le m c v' /\
      Val.lessdef v v'.
Proof.
  intros.
  revert H0 H1 H2.
  unfold sem_neg_expr, make_neg; intros SEM MAKE EV1.
  destruct (classify_neg tya); inv MAKE;
  eexists; (split; [econstructor; simpl; eauto|]);
  apply Val.lessdef_unop; auto.
Qed.


Lemma make_absfloat_correct:
  forall a tya c va va' v e le m,
    Val.lessdef va' va ->
    sem_absfloat_expr va' tya =  v ->
    make_absfloat a tya = OK c ->  
    eval_expr ge e le m a va ->
    exists v',
      eval_expr ge e le m c v' /\
      Val.lessdef v v'.
Proof.
  intros.
  revert H0 H1 H2.
  unfold sem_absfloat_expr, make_absfloat, make_floatofint; intros SEM MAKE EV1.
  destruct (classify_neg tya); inv MAKE;
  try destruct s; eexists; (split; [repeat (econstructor; simpl; eauto)|]);
  repeat apply Val.lessdef_unop; auto.
Qed.

Lemma make_notbool_correct:
  forall a tya c va va' v e le m,
    Val.lessdef va' va ->
    sem_notbool_expr va' tya = v ->
    make_notbool a tya = OK c ->  
    eval_expr ge e le m a va ->
    exists v',
      eval_expr ge e le m c v' /\
      Val.lessdef v v'.
Proof.
  unfold sem_notbool_expr, make_notbool; intros until m; intros SE SEM MAKE EV1;
  destruct (classify_bool tya); inv MAKE; eauto with cshm;
  try (eexists; split; [repeat (econstructor; simpl; eauto); fail|]);
  red; intros;
  try erewrite eqm_notbool_eq_zero; apply Val.lessdef_binop; auto.
Qed.

Lemma make_notint_correct:
  forall a tya c va va' v e le m,
    Val.lessdef va' va ->
    sem_notint_expr va' tya = v ->
    make_notint a tya = OK c ->  
    eval_expr ge e le m a va ->
    exists v',
      eval_expr ge e le m c v' /\
      Val.lessdef v v'.
Proof.
  unfold sem_notint_expr, make_notint; intros until m; intros SE SEM MAKE EV1;
  destruct (classify_notint tya); inv MAKE; eauto with cshm;
  eexists; (split; [repeat (econstructor; simpl; eauto)|try apply Val.lessdef_unop; auto]).
Qed.

Definition binary_constructor_correct
    (make: expr -> type -> expr -> type -> res expr)
    (sem: expr_sym -> type -> expr_sym -> type -> option expr_sym): Prop :=
  forall a tya b tyb c va vb vaa vbb v e le m,
    Val.lessdef vaa va ->
    Val.lessdef vbb vb ->
    sem vaa tya vbb tyb = Some v ->
    make a tya b tyb = OK c ->  
    eval_expr ge e le m a va ->
    eval_expr ge e le m b vb ->
    exists v',
      eval_expr ge e le m c v' /\
      Val.lessdef v v'.


Section MAKE_BIN.

Variable sem_int: signedness -> expr_sym -> expr_sym -> option expr_sym.
Variable sem_long: signedness -> expr_sym -> expr_sym -> option expr_sym.
Variable sem_float: expr_sym -> expr_sym -> option expr_sym.
Variable sem_single: expr_sym -> expr_sym -> option expr_sym.
Variables iop iopu fop sop lop lopu: binary_operation.

Hypothesis iop_ok:
  forall x y m, eval_binop iop x y m = sem_int Signed x y.
Hypothesis iopu_ok:
  forall x y m, eval_binop iopu x y m = sem_int Unsigned x y.
Hypothesis lop_ok:
  forall x y m, eval_binop lop x y m = sem_long Signed x y.
Hypothesis lopu_ok:
  forall x y m, eval_binop lopu x y m = sem_long Unsigned x y.
Hypothesis fop_ok:
  forall x y m, eval_binop fop x y m = sem_float x y.
Hypothesis sop_ok:
  forall x y m, eval_binop sop x y m = sem_single x y.

Hypothesis si_norm:
  forall sg, preserves_lessdef Val.lessdef (sem_int sg).

Hypothesis sl_norm:
  forall sg, preserves_lessdef Val.lessdef (sem_long sg).

Hypothesis sf_norm: preserves_lessdef Val.lessdef sem_float.

Hypothesis ss_norm: preserves_lessdef Val.lessdef sem_single.

Lemma make_binarith_correct:
  binary_constructor_correct
    (make_binarith iop iopu fop sop lop lopu)
    (sem_binarith_expr sem_int sem_long sem_float sem_single).
Proof.
  red; unfold make_binarith, sem_binarith_expr;
  intros until m; intros SE1 SE2 SEM MAKE EV1 EV2. 
  set (cls := classify_binarith tya tyb) in *.
  set (ty := binarith_type cls) in *.
  monadInv MAKE. 
  destruct (sem_cast_expr vaa tya ty) as [va'|] eqn:Ca; try discriminate.
  destruct (sem_cast_expr vbb tyb ty) as [vb'|] eqn:Cb; try discriminate. 
  exploit make_cast_correct. eexact EQ. eauto. eauto. eauto. intros EV1'.
  exploit make_cast_correct. eexact EQ1. eauto. eauto. eauto. intros EV2'.
  destruct EV1' as [v'' [A B]].
  destruct EV2' as [v''0 [C D]].
  destruct cls; inv EQ2.
  - generalize (si_norm s _ _ _ _ B D).
    rewrite SEM. destr_cond_match; intuition try discriminate.
    destruct s; inv H0;
    eexists; split; eauto;
    repeat (econstructor; simpl; eauto).
    rewrite iop_ok; eauto.
    rewrite iopu_ok; auto.
  - generalize (sl_norm s _ _ _  _ B D).
    rewrite SEM. destr_cond_match; intuition try discriminate.
    destruct s; inv H0; eexists; split; eauto; econstructor; eauto with cshm. 
    rewrite lop_ok; auto. rewrite lopu_ok; auto.
  - generalize (sf_norm _ _ _ _ B D).  
    rewrite SEM. destr_cond_match; intuition try discriminate.
    eexists; split; eauto; econstructor; simpl; eauto.
    erewrite fop_ok; eauto with cshm.
  - generalize (ss_norm _ _ _ _ B D).
    rewrite SEM. destr_cond_match; intuition try discriminate.
    eexists; split; eauto; econstructor; simpl; eauto.
    erewrite sop_ok; eauto with cshm.
Qed.

Lemma make_binarith_int_correct:
  binary_constructor_correct
    (make_binarith_int iop iopu lop lopu)
    (sem_binarith_expr sem_int sem_long (fun x y => None) (fun x y => None)).
Proof.
  red; unfold make_binarith_int, sem_binarith_expr;
  intros until m; intros SE1 SE2 SEM MAKE EV1 EV2 .
  set (cls := classify_binarith tya tyb) in *.
  set (ty := binarith_type cls) in *.
  monadInv MAKE.
  destruct (sem_cast_expr vaa tya ty) as [va'|] eqn:Ca; try discriminate.
  destruct (sem_cast_expr vbb tyb ty) as [vb'|] eqn:Cb; try discriminate.
  exploit make_cast_correct. eexact EQ. eauto. eauto. eauto. auto. intros EV1'.
  exploit make_cast_correct. eexact EQ1. eauto. eauto. eauto. auto. intros EV2'.
  destruct EV1' as [v'' [A B]].
  destruct EV2' as [v''0 [C D]].
  destruct cls; inv EQ2.
  - generalize (si_norm s _ _ _ _  B D).
    rewrite SEM. destr_cond_match; intuition try discriminate.
    destruct s; inv H0;
    eexists; split; eauto;
    repeat (econstructor; simpl; eauto).
    rewrite iop_ok; eauto.
    rewrite iopu_ok; auto.
  - generalize (sl_norm s _ _ _ _ B D).
    rewrite SEM. destr_cond_match; intuition try discriminate.
    destruct s; inv H0; eexists; split; eauto; econstructor; eauto with cshm. 
    rewrite lop_ok; auto. rewrite lopu_ok; auto.
Qed.

End MAKE_BIN.

Hint Extern 2 (@eq (option val) _ _) => (simpl; reflexivity) : cshm.

Lemma lessdef_mul_commut:
  forall a b,
    Val.lessdef (Val.mul a b) (Val.mul b a).
Proof.
  red; intros; simpl; seval; auto.
  rewrite Int.mul_commut; auto.
Qed.

Lemma make_add_correct: binary_constructor_correct make_add sem_add_expr.
Proof.
  red; unfold make_add, sem_add_expr;
  intros until m; intros SE1 SE2 SEM MAKE EV1 EV2;
  destruct (classify_add tya tyb); inv MAKE.
  - inv SEM. t.
    eapply Val.lessdef_trans. apply lessdef_mul_commut.
    apply Val.lessdef_binop; auto. 
  - inv SEM. t.     eapply Val.lessdef_trans. apply lessdef_mul_commut.
    apply Val.lessdef_binop; auto.
  - inv SEM. t.
    eapply Val.lessdef_trans. apply lessdef_mul_commut.
    apply Val.lessdef_binop; auto.
    red; intros; simpl; auto.
    unfold convert_t.
    apply (Val.lessdef_unop _ _ OpLoword Tlong SE2 alloc em).
  - inv SEM. t.
    eapply Val.lessdef_trans. apply lessdef_mul_commut.
    apply Val.lessdef_binop; auto.
    red; intros; simpl; auto.
    unfold convert_t.
    apply (Val.lessdef_unop _ _ OpLoword Tlong SE1 alloc em).
  - eapply make_binarith_correct in SEM; eauto; red; intros; auto;
    apply Val.lessdef_binop; auto.
Qed.

Lemma make_sub_correct: binary_constructor_correct make_sub sem_sub_expr.
Proof.
  red; unfold make_sub, sem_sub_expr;
  intros until m; intros SE1 SE2 SEM MAKE EV1 EV2;
  destruct (classify_sub tya tyb); inv MAKE.
  - inv SEM. t.
    eapply Val.lessdef_trans. apply lessdef_mul_commut.
    apply Val.lessdef_binop; auto.
  - inv SEM. t.
    apply Val.lessdef_binop; auto.
  - inv SEM. t.
    eapply Val.lessdef_trans. apply lessdef_mul_commut.
    apply Val.lessdef_binop; auto.
    red; intros; simpl.
    unfold convert_t.
    apply (Val.lessdef_unop _ _ OpLoword Tlong SE2 alloc em).
  - eapply make_binarith_correct in SEM; eauto; red; intros; auto;
    apply Val.lessdef_binop; auto.
Qed.

Lemma make_mul_correct: binary_constructor_correct make_mul sem_mul_expr.
Proof.
  intros; apply make_binarith_correct; eauto; red; intros; auto;
  apply Val.lessdef_binop; auto.
Qed.

Lemma make_div_correct: binary_constructor_correct make_div sem_div_expr.
Proof.
  intros; apply make_binarith_correct; eauto; red; intros; auto;
  apply Val.lessdef_binop; auto.
Qed.

Lemma make_mod_correct: binary_constructor_correct make_mod sem_mod_expr.
Proof.
  eapply make_binarith_int_correct; eauto; red; intros; auto;
  apply Val.lessdef_binop; auto.
Qed.

Lemma make_and_correct: binary_constructor_correct make_and sem_and_expr.
Proof.
  eapply make_binarith_int_correct; eauto; red; intros; auto;
  apply Val.lessdef_binop; auto.
Qed.

Lemma make_or_correct: binary_constructor_correct make_or sem_or_expr.
Proof.
  eapply make_binarith_int_correct; eauto; red; intros; auto;
  apply Val.lessdef_binop; auto.
Qed.

Lemma make_xor_correct: binary_constructor_correct make_xor sem_xor_expr.
Proof.
  apply make_binarith_int_correct; try red; intros; auto;
  apply Val.lessdef_binop; auto.
Qed.

Ltac comput val :=
  let x := fresh in set val as x in *; vm_compute in x; subst x.

Remark small_shift_amount_1:
  forall i,
  Int64.ltu i Int64.iwordsize = true ->
  Int.ltu (Int64.loword i) Int64.iwordsize' = true
  /\ Int64.unsigned i = Int.unsigned (Int64.loword i).
Proof.
  intros. apply Int64.ltu_inv in H. comput (Int64.unsigned Int64.iwordsize). 
  assert (Int64.unsigned i = Int.unsigned (Int64.loword i)).
  {
    unfold Int64.loword. rewrite Int.unsigned_repr; auto. 
    comput Int.max_unsigned; omega.
  }
  split; auto. unfold Int.ltu. apply zlt_true. rewrite <- H0. tauto.
Qed.

Remark small_shift_amount_2:
  forall i,
  Int64.ltu i (Int64.repr 32) = true ->
  Int.ltu (Int64.loword i) Int.iwordsize = true.
Proof.
  intros. apply Int64.ltu_inv in H. comput (Int64.unsigned (Int64.repr 32)).
  assert (Int64.unsigned i = Int.unsigned (Int64.loword i)).
  {
    unfold Int64.loword. rewrite Int.unsigned_repr; auto. 
    comput Int.max_unsigned; omega.
  }
  unfold Int.ltu. apply zlt_true. rewrite <- H0. tauto.
Qed.

Lemma small_shift_amount_3:
  forall i,
  Int.ltu i Int64.iwordsize' = true ->
  Int64.unsigned (Int64.repr (Int.unsigned i)) = Int.unsigned i.
Proof.
  intros. apply Int.ltu_inv in H. comput (Int.unsigned Int64.iwordsize'). 
  apply Int64.unsigned_repr. comput Int64.max_unsigned; omega.
Qed.

Lemma make_shl_correct: binary_constructor_correct make_shl sem_shl_expr.
Proof.
  red; unfold make_shl, sem_shl_expr, sem_shift_expr;
  intros until m; intros SE1 SE2 SEM MAKE EV1 EV2;
  destruct (classify_shift tya tyb); inv MAKE; inv SEM.
- t . 
- t. 
  red; intros; simpl; auto. unfold convert_t.
  apply (Val.lessdef_unop _ _ OpLoword Tlong SE2 alloc em).
  - t. 
    red; intros; simpl; auto. unfold convert_t.
    des (sg_conv s);
    apply (Val.lessdef_unop _ _ OpLoword Tlong SE2 alloc em).
  - t. unfold expr_cast_gen. simpl.
    eapply Val.lessdef_trans; [|eauto].
    red; intros; simpl; auto. unfold convert_t.
    seval; simpl; auto.
    unfold Int64.loword; rewrite Int64.unsigned_repr.
    rewrite Int.repr_unsigned. auto.
    generalize (Int.unsigned_range_2 i).
    intros. split. omega. destruct H. etransitivity; eauto.
    vm_compute; congruence.
Qed.

Lemma make_shr_correct: binary_constructor_correct make_shr sem_shr_expr.
Proof.
  red; unfold make_shr, sem_shr_expr, sem_shift_expr;
  intros until m; intros SE1 SE2 SEM MAKE EV1 EV2;
  destruct (classify_shift tya tyb); inv MAKE; inv SEM.
- destruct s; inv H0; t.
- destruct s; inv H0; t;
  unfold expr_cast_gen; simpl;
  red; simpl; intros;
  apply (Val.lessdef_unop _ _ OpLoword Tlong SE2 alloc em).
- destruct s; inv H0; t;
  unfold expr_cast_gen; simpl;
  red; simpl; intros;
  apply (Val.lessdef_unop _ _ OpLoword Tlong SE2 alloc em).
- destruct s; inv H0; t;
  unfold expr_cast_gen; simpl;
  (eapply Val.lessdef_trans; [|eauto]);
  red; simpl; unfold convert_t; intros; seval; auto;
  unfold Int64.loword;
  (rewrite Int64.unsigned_repr;
    [rewrite Int.repr_unsigned; auto|
    generalize (Int.unsigned_range_2 i); intro Rng;
    intros; (split; [ omega|  destruct Rng; etransitivity; eauto
  ])]).
  vm_compute; congruence.
  vm_compute; congruence.
Qed.

Lemma make_cmp_correct:
  forall cmp a tya b tyb c va va' vb' vb v e le m,
    Val.lessdef va' va ->
    Val.lessdef vb' vb ->
    sem_cmp_expr cmp va' tya vb' tyb = Some v ->
    make_cmp cmp a tya b tyb = OK c ->
    eval_expr ge e le m a va ->
    eval_expr ge e le m b vb ->
    exists v',
      eval_expr ge e le m c v' /\
      Val.lessdef v v'.
Proof.
  unfold sem_cmp_expr, make_cmp; intros until m; intros SE1 SE2 SEM MAKE EV1 EV2;
  destruct (classify_cmp tya tyb); inv MAKE; inv SEM.
  - t. 
  - t. 
    red; intros; simpl; auto. unfold convert_t.
    apply (Val.lessdef_unop _ _ OpLoword Tlong SE2 alloc em).
  - t.
    red; intros; simpl; auto. unfold convert_t.
    apply (Val.lessdef_unop _ _ OpLoword Tlong SE1 alloc em).
  - eapply make_binarith_correct in H1; eauto; red; intros; auto;
    apply Val.lessdef_binop; eauto.  
Qed.

Lemma transl_unop_correct:
  forall op a tya c va va' v e le m,
  transl_unop op a tya = OK c ->
  eval_expr ge e le m a va ->
  Val.lessdef va' va ->
  sem_unary_operation_expr op va' tya = v ->
  exists v',
    eval_expr ge e le m c v' /\
    Val.lessdef v v'.
Proof.
  intros. destruct op; simpl in *.
  eapply make_notbool_correct; eauto.
  eapply make_notint_correct; eauto.
  eapply make_neg_correct; eauto.
  eapply make_absfloat_correct; eauto.
Qed.

Lemma transl_binop_correct:
  forall op a tya b tyb c va vb va' vb' v e le m,
    Val.lessdef va' va ->
    Val.lessdef vb' vb ->
    transl_binop op a tya b tyb = OK c ->
    sem_binary_operation_expr op va' tya vb' tyb = Some v ->
    eval_expr ge e le m a va ->
    eval_expr ge e le m b vb ->
    exists v',
      eval_expr ge e le m c v' /\
      Val.lessdef v v'.
Proof.
  intros op a tya b tyb c va vb va' vb' v e le m SE1 SE2 TR SEM E1 E2.
  destruct op; simpl in *.
  eapply make_add_correct in SEM; eauto.
  eapply make_sub_correct in SEM; eauto.
  eapply make_mul_correct in SEM; eauto.
  eapply make_div_correct in SEM; eauto.
  eapply make_mod_correct in SEM; eauto.
  eapply make_and_correct in SEM; eauto.
  eapply make_or_correct in SEM; eauto.
  eapply make_xor_correct in SEM; eauto.
  eapply make_shl_correct in SEM; eauto.
  eapply make_shr_correct in SEM; eauto.
  eapply make_cmp_correct in SEM; eauto.
  eapply make_cmp_correct in SEM; eauto.
  eapply make_cmp_correct in SEM; eauto.
  eapply make_cmp_correct in SEM; eauto.
  eapply make_cmp_correct in SEM; eauto.
  eapply make_cmp_correct in SEM; eauto.
Qed.


Lemma make_load_correct:
  forall addr ty code bofs v v' e le m,
  make_load addr ty = OK code ->
  eval_expr ge e le m addr v' ->
  Val.lessdef bofs v' ->
  deref_loc ty m bofs v ->
  exists v'',
    eval_expr ge e le m code v'' /\
    Val.lessdef v v''.
Proof.
  unfold make_load; intros until m; intros MKLOAD EVEXP SE DEREF.
  inv DEREF.
  - (* scalar *)
    rewrite H in MKLOAD. inv MKLOAD. 
    eexists; split; eauto; try reflexivity.
    econstructor; eauto.
    revert H0.
    unfold Mem.loadv.
    generalize (Mem.lessdef_eqm m _ _ SE).
    destr. inv H0. auto.
  - (* by reference *)
    rewrite H in MKLOAD. inv MKLOAD. 
    eexists; split; eauto.
  - (* by copy *)
    rewrite H in MKLOAD. inv MKLOAD. 
    eexists; split; eauto.
Qed.

Variable needed_stackspace : ident -> nat.

Lemma make_memcpy_correct:
  forall f dst src ty k e le m  m' v v',
    eval_expr ge e le m dst v ->
    eval_expr ge e le m src v' ->
    assign_loc ty m v v'  m' ->
    access_mode ty = By_copy ->
    exists m'',
      step ge needed_stackspace (State f (make_memcpy dst src ty) k e le m) E0 (State f Sskip k e le m'') /\
      mem_equiv m' m''.
Proof.
  intros f dst src ty k e le m m' v v' EV EV2 AL AM. 
  unfold make_memcpy. change le with (set_optvar None (Eval Vundef) le) at 2.
  inv AL; try congruence.
  destruct (storebytes_mem_rel _ wf_mr_se m m b (Int.unsigned ofs) bytes m')
    as [m2 [A B]]; auto.
  apply mem_equiv_refl. apply wf_mr_se.
  eexists; split; eauto.
  econstructor. econstructor. eauto. econstructor. eauto. constructor.
  simpl.
  eapply extcall_memcpy_sem_intro with (osrc:=ofs') (odst:=ofs); eauto.
  apply alignof_blockcopy_1248. 
  apply sizeof_alignof_blockcopy_compat.

  eexists; split; eauto.
  econstructor. repeat econstructor; eauto.
  simpl. rewrite SZnull.
  econstructor 2. auto. reflexivity.
Qed.

Lemma make_store_correct:
  forall addr ty rhs code e le m  v v' m' f k,
  make_store addr ty rhs = OK code ->
  eval_expr ge e le m addr v' ->
  eval_expr ge e le m rhs v ->
  assign_loc ty m v' v m' ->
  exists m'',
    step ge needed_stackspace  (State f code k e le m) E0 (State f Sskip k e le m'') /\
    mem_equiv m' m''.
Proof.
  unfold make_store. intros until k; intros MKSTORE EV1 (* SE *) EV2 ASSIGN.
  inversion ASSIGN; subst.
  - (* nonvolatile scalar *)
    rewrite AM in *; inv MKSTORE.
    (exists m'; split; eauto); try reflexivity.
    econstructor; eauto.
  - (* by copy *)
    rewrite AM in *; inv MKSTORE.
    eapply make_memcpy_correct; eauto.
  - rewrite AM in MKSTORE. inv MKSTORE.
    eapply make_memcpy_correct; eauto.
Qed.

End CONSTRUCTORS.

(** * Basic preservation invariants *)

Section CORRECTNESS.

Variable prog: Clight.program.
Variable tprog: Csharpminor.program.
Hypothesis TRANSL: transl_program prog = OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall s, Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf_partial2 transl_fundef transl_globvar _ TRANSL).

Lemma functions_translated:
  forall m v f,
  Genv.find_funct m ge v = Some f ->
  exists tf, Genv.find_funct m tge v = Some tf /\ transl_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial2 transl_fundef transl_globvar _ TRANSL).

Lemma function_ptr_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial2 transl_fundef transl_globvar _ TRANSL).

Lemma var_info_translated:
  forall b v,
  Genv.find_var_info ge b = Some v ->
  exists tv, Genv.find_var_info tge b = Some tv /\ transf_globvar transl_globvar v = OK tv.
Proof (Genv.find_var_info_transf_partial2 transl_fundef transl_globvar _ TRANSL).

Lemma var_info_rev_translated:
  forall b tv,
  Genv.find_var_info tge b = Some tv ->
  exists v, Genv.find_var_info ge b = Some v /\ transf_globvar transl_globvar v = OK tv.
Proof (Genv.find_var_info_rev_transf_partial2 transl_fundef transl_globvar _ TRANSL).

Lemma block_is_volatile_preserved:
  forall b, block_is_volatile tge b = block_is_volatile ge b.
Proof.
  intros. unfold block_is_volatile.
  destruct (Genv.find_var_info ge b) eqn:?.
  exploit var_info_translated; eauto. intros [tv [A B]]. rewrite A. 
  unfold transf_globvar in B. monadInv B. auto.
  destruct (Genv.find_var_info tge b) eqn:?.
  exploit var_info_rev_translated; eauto. intros [tv [A B]]. congruence.
  auto.
Qed.

(** * Matching between environments *)

(** In this section, we define a matching relation between
  a Clight local environment and a Csharpminor local environment. *)

Record match_env (e: Clight.env) (te: Csharpminor.env) : Prop :=
  mk_match_env {
    me_local:
      forall id b ty,
      e!id = Some (b, ty) -> te!id = Some(b, sizeof ty);
    me_local_inv:
      forall id b sz,
      te!id = Some (b, sz) -> exists ty, e!id = Some(b, ty)
  }.

Lemma match_env_globals:
  forall e te id,
  match_env e te ->
  e!id = None ->
  te!id = None.
Proof.
  intros. destruct (te!id) as [[b sz] | ] eqn:?; auto.
  exploit me_local_inv; eauto. intros [ty EQ]. congruence.
Qed.

Lemma match_env_same_blocks:
  forall e te,
  match_env e te ->
  blocks_of_env te = Clight.blocks_of_env e.
Proof.
  intros.
  set (R := fun (x: (block * type)) (y: (block * Z)) =>
         match x, y with
         | (b1, ty), (b2, sz) => b2 = b1 /\ sz = sizeof ty
         end).
  assert (list_forall2 
            (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
            (PTree.elements e) (PTree.elements te)).
  apply PTree.elements_canonical_order.
  intros id [b ty] GET. exists (b, sizeof ty); split. eapply me_local; eauto. red; auto.
  intros id [b sz] GET. exploit me_local_inv; eauto. intros [ty EQ].
  exploit me_local; eauto. intros EQ1. 
  exists (b, ty); split. auto. red; split; congruence.
  unfold blocks_of_env, Clight.blocks_of_env.
  generalize H0. induction 1. auto. 
  simpl. f_equal; auto.
  unfold block_of_binding, Clight.block_of_binding. 
  destruct a1 as [id1 [blk1 ty1]]. destruct b1 as [id2 [blk2 sz2]].
  simpl in *. destruct H1 as [A [B C]]. congruence.
Qed.

Lemma match_env_free_blocks:
  forall e te m m',
  match_env e te ->
  Mem.free_list m (Clight.blocks_of_env e) = Some m' ->
  Mem.free_list m (blocks_of_env te) = Some m'.
Proof.
  intros. rewrite (match_env_same_blocks _ _ H). auto.
Qed.

Lemma match_env_empty:
  match_env Clight.empty_env Csharpminor.empty_env.
Proof.
  unfold Clight.empty_env, Csharpminor.empty_env.
  constructor.
  intros until ty. repeat rewrite PTree.gempty. congruence.
  intros until sz. rewrite PTree.gempty. congruence.
Qed.

(** The following lemmas establish the [match_env] invariant at
  the beginning of a function invocation, after allocation of
  local variables and initialization of the parameters. *)

Lemma match_env_alloc_variables:
  forall e1 m1 vars e2 m2,
  Clight.alloc_variables e1 m1 vars e2 m2 ->
  forall te1,
  match_env e1 te1 ->
  exists te2,
  Csharpminor.alloc_variables te1 m1 (map transl_var vars) te2 m2
  /\ match_env e2 te2.
Proof.
  induction 1; intros; simpl.
  exists te1; split. constructor. auto.
  exploit (IHalloc_variables (PTree.set id (b1, sizeof ty) te1)).
  constructor.
    (* me_local *)
    intros until ty0. repeat rewrite PTree.gsspec.
    destruct (peq id0 id); intros. congruence. eapply me_local; eauto. 
    (* me_local_inv *)
    intros until sz. repeat rewrite PTree.gsspec. 
    destruct (peq id0 id); intros. exists ty; congruence. eapply me_local_inv; eauto. 
  intros [te2 [ALLOC MENV]].
  exists te2; split. econstructor; eauto. 
  rewrite Zmax_r; simpl; eauto.
  generalize (sizeof_pos ty); omega.
  rewrite Zmax_r; simpl; eauto.
  generalize (sizeof_pos ty); omega.
  auto.
Qed. 

Lemma create_undef_temps_match:
  forall temps,
  create_undef_temps (map fst temps) = Clight.create_undef_temps temps.
Proof.
  induction temps; simpl. auto. 
  destruct a as [id ty]. simpl. decEq. auto.
Qed.

Lemma bind_parameter_temps_match:
  forall vars vals le1 le2,
  Clight.bind_parameter_temps vars vals le1 = Some le2 ->
  bind_parameters (map fst vars) vals le1 = Some le2.
Proof.
  induction vars; simpl; intros.
  destruct vals; inv H. auto. 
  destruct a as [id ty]. destruct vals; try discriminate. auto. 
Qed.

(** * Proof of semantic preservation *)

(** ** Semantic preservation for expressions *)

(** The proof of semantic preservation for the translation of expressions
  relies on simulation diagrams of the following form:
<<
         e, le, m, a ------------------- te, le, m, ta
            |                                |
            |                                |
            |                                |
            v                                v
         e, le, m, v ------------------- te, le, m, v
>>
  Left: evaluation of r-value expression [a] in Clight.
  Right: evaluation of its translation [ta] in Csharpminor.
  Top (precondition): matching between environments [e], [te], 
    plus well-typedness of expression [a].
  Bottom (postcondition): the result values [v] 
    are identical in both evaluations.

  We state these diagrams as the following properties, parameterized
  by the Clight evaluation. *)

Section EXPR.

  Variable e: Clight.env.
Variable le: temp_env.
Variable m: mem.
Variable te: Csharpminor.env.
Hypothesis MENV: match_env e te.

Lemma transl_expr_lvalue_correct:
    (forall a v,
       Clight.eval_expr ge e le m a v ->
       forall ta (TR: transl_expr a = OK ta) ,
       exists v',
         Csharpminor.eval_expr tge te le m ta v' /\
         Val.lessdef v v')
    /\(forall a v,
         Clight.eval_lvalue ge e le m a v ->
         forall ta (TR: transl_lvalue a = OK ta),
         exists v',
           Csharpminor.eval_expr tge te le m ta v' /\
           Val.lessdef v v') . 
Proof. 
  apply eval_expr_lvalue_ind; intros; try (monadInv TR).
- (* const int *)
  eexists; split; eauto.
  apply make_intconst_correct. 
- (* const float *)
  eexists; split; eauto.
  apply make_floatconst_correct. 
- (* const single *)
  eexists; split; eauto.
  apply make_singleconst_correct.  
- (* const long *)
  eexists; split; eauto.
  apply make_longconst_correct.  
- (* temp var *)
  eexists; split; eauto.
  constructor; eauto.  
- (* addrof *)
  simpl in TR.
  destruct (H0 _ TR) as [v' [A B]].  
  eexists; split; eauto.
- (* unop *) 
  destruct (H0 _ EQ) as [v' [A B]]. simpl.
  eapply transl_unop_correct; eauto. 
- (* binop *)
  destruct (H0 _ EQ) as [v' [A B]].
  destruct (H2 _ EQ1) as [v'' [C D]].
  eapply transl_binop_correct in H3; eauto.
- (* cast *)
  destruct (H0 _ EQ) as [v' [A B]].
  eapply make_cast_correct; eauto. 
- (* rvalue out of lvalue *)
  exploit transl_expr_lvalue; eauto. intros [tb [TRLVAL MKLOAD]].
  destruct (H0 _ TRLVAL) as [v' [A B]].
  eapply make_load_correct; eauto.
- (* var local *)
  exploit (me_local _ _ MENV); eauto. intros EQ.
  eexists; split; eauto. simpl.
  econstructor. eapply eval_var_addr_local. eauto.
- (* var global *)
  eexists; split; eauto.
  econstructor. eapply eval_var_addr_global. 
  eapply match_env_globals; eauto.
  erewrite symbols_preserved. eauto.
- (* deref *)
  simpl in TR. apply H0 in TR. 
  destruct TR as [v' [A B]].
  exists v'; split; eauto.
- (* field struct *)
  simpl in TR. rewrite H1 in TR. monadInv TR.
  destruct (H0 _ EQ) as [v' [A B]].
  eexists; split. 
  eapply eval_Ebinop; eauto.
  apply make_intconst_correct. 
  simpl. eauto. 
  rewrite H2 in EQ1. inv EQ1.
  apply Val.lessdef_binop; auto. 
- (* field union *)
  simpl in TR. rewrite H1 in TR. destruct (H0 _ TR) as [v' [A B]]; eexists; split; eauto.
Qed.

Lemma transl_expr_correct:
  forall a v,
    Clight.eval_expr ge e le m a v ->
    forall ta, transl_expr a = OK ta ->
               exists v',
                 Csharpminor.eval_expr tge te le m ta v' /\
                 Val.lessdef v v'.
Proof. apply  (proj1 (transl_expr_lvalue_correct)).
Qed.

Lemma transl_lvalue_correct:
    forall a v,
      Clight.eval_lvalue ge e le m a v ->
      forall ta, transl_lvalue a = OK ta ->
                 exists v',
                   Csharpminor.eval_expr tge te le m ta v' /\
                   Val.lessdef v v'.
Proof. apply (proj2 (transl_expr_lvalue_correct)).
Qed.

Lemma transl_arglist_correct:
  forall al tyl vl,
    Clight.eval_exprlist ge e le m al tyl vl ->
      forall tal, transl_arglist al tyl = OK tal ->
                  exists vl',
                    list_forall2 Val.lessdef vl vl' /\
                    Csharpminor.eval_exprlist tge te le m tal vl'.
Proof. 
  induction 1; intros tal TAL.
  - monadInv TAL. exists nil; split; constructor.
  - monadInv TAL.
    destruct (IHeval_exprlist _ EQ0) as [vl' [A B]].
    destruct  (transl_expr_correct _ _ H _ EQ) as [v' [C D]].
    destruct (make_cast_correct _ _ _ _ _ _ _ _ _ _ _ EQ1 C D H0)
             as [v0 [E F]].
    (exists (v0::vl'); split; auto).
    constructor; auto.
    constructor; auto.
Qed.

Lemma typlist_of_arglist_eq:
  forall m' al tyl vl,
  Clight.eval_exprlist ge e le m' al tyl vl ->
  typlist_of_arglist al tyl = typlist_of_typelist tyl.
Proof.
  clear.
  induction 1; simpl.
  auto.
  f_equal; auto.
Qed.

End EXPR.

(** ** Semantic preservation for statements *)

(** The simulation diagram for the translation of statements and functions
  is a "plus" diagram of the form
<<
           I
     S1 ------- R1
     |          | 
   t |        + | t
     v          v  
     S2 ------- R2
           I                         I
>>

The invariant [I] is the [match_states] predicate that we now define.
*)

Inductive match_transl: stmt -> cont -> stmt -> cont -> Prop :=
  | match_transl_0: forall ts tk,
      match_transl ts tk ts tk
  | match_transl_1: forall ts tk,
      match_transl (Sblock ts) tk ts (Kblock tk).

Variable needed_stackspace : ident -> nat .

Lemma match_transl_step:
  forall ts tk ts' tk' f te le m,
  match_transl (Sblock ts) tk ts' tk' ->
  star (fun ge => step ge needed_stackspace ) tge (State f ts' tk' te le m) E0 (State f ts (Kblock tk) te le m).
Proof.
  intros. inv H. 
  apply star_one. constructor. 
  apply star_refl.
Qed.

Inductive match_cont: type -> nat -> nat -> Clight.cont -> Csharpminor.cont -> Prop :=
  | match_Kstop: forall tyret nbrk ncnt,
      match_cont tyret nbrk ncnt Clight.Kstop Kstop
  | match_Kseq: forall tyret nbrk ncnt s k ts tk,
      transl_statement tyret nbrk ncnt s = OK ts ->
      match_cont tyret nbrk ncnt k tk ->
      match_cont tyret nbrk ncnt
                 (Clight.Kseq s k)
                 (Kseq ts tk)
  | match_Kloop1: forall tyret s1 s2 k ts1 ts2 nbrk ncnt tk,
      transl_statement tyret 1%nat 0%nat s1 = OK ts1 ->
      transl_statement tyret 0%nat (S ncnt) s2 = OK ts2 ->
      match_cont tyret nbrk ncnt k tk ->
      match_cont tyret 1%nat 0%nat
                 (Clight.Kloop1 s1 s2 k)
                 (Kblock (Kseq ts2 (Kseq (Sloop (Sseq (Sblock ts1) ts2)) (Kblock tk))))
  | match_Kloop2: forall tyret s1 s2 k ts1 ts2 nbrk ncnt tk,
      transl_statement tyret 1%nat 0%nat s1 = OK ts1 ->
      transl_statement tyret 0%nat (S ncnt) s2 = OK ts2 ->
      match_cont tyret nbrk ncnt k tk ->
      match_cont tyret 0%nat (S ncnt)
                 (Clight.Kloop2 s1 s2 k)
                 (Kseq (Sloop (Sseq (Sblock ts1) ts2)) (Kblock tk))
  | match_Kswitch: forall tyret nbrk ncnt k tk,
                     match_cont tyret nbrk ncnt k tk ->
                     match_cont tyret 0%nat (S ncnt)
                 (Clight.Kswitch k)
                 (Kblock tk)
  | match_Kcall_some: forall tyret nbrk ncnt nbrk' ncnt' f e k id tf te le le' tk,
      transl_function f = OK tf ->
      match_env e te ->
      temp_env_equiv Val.lessdef le le' ->
      match_cont (Clight.fn_return f) nbrk' ncnt' k tk ->
      match_cont tyret nbrk ncnt 
                 (Clight.Kcall id f e le k)
                 (Kcall id tf te le' tk).

Inductive match_states: Clight.state -> Csharpminor.state -> Prop :=
  | match_state:
      forall f nbrk ncnt s k e le le' m m' tf ts tk te ts' tk'
          (TRF: transl_function f = OK tf)
          (TR: transl_statement (Clight.fn_return f) nbrk ncnt s = OK ts)
          (MTR: match_transl ts tk ts' tk')
          (MENV: match_env e te)
          (MK: match_cont (Clight.fn_return f) nbrk ncnt k tk)
          (TE: temp_env_equiv Val.lessdef le le')
          (ME: mem_lessdef m m'),
      match_states (Clight.State f s k e le m)
                   (State tf ts' tk' te le' m')
  | match_callstate:
      forall fd args args' k m m' tfd tk targs tres cconv
          (TR: transl_fundef fd = OK tfd)
          (MK: match_cont Tvoid 0%nat 0%nat k tk)
          (ISCC: Clight.is_call_cont k)
          (TY: type_of_fundef fd = Tfunction targs tres cconv)
          (ME: mem_lessdef m m')
          (ARGS_eq: list_forall2 (Val.lessdef) args args'),
      match_states (Clight.Callstate fd args k m)
                   (Callstate tfd args' tk m')
  | match_returnstate:
      forall res res' k m m' tk 
             (MK: match_cont Tvoid 0%nat 0%nat k tk)
             (MRES: Val.lessdef res res')
             (ME: mem_lessdef m m'),
      match_states (Clight.Returnstate res k m)
                   (Returnstate res' tk m').

Remark match_states_skip:
  forall f e le le' te nbrk ncnt k tf tk m m',
  transl_function f = OK tf ->
  match_env e te ->
  match_cont (Clight.fn_return f) nbrk ncnt k tk ->
  mem_lessdef m m' ->
  temp_env_equiv Val.lessdef le le' ->
  match_states (Clight.State f ClightSyntax.Sskip k e le m) (State tf Sskip tk te le' m').
Proof.
  intros. econstructor; eauto. simpl; reflexivity. constructor.
Qed.

(** Commutation between label resolution and compilation *)

Section FIND_LABEL.
Variable lbl: label.
Variable tyret: type.

Lemma transl_find_label:
  forall s nbrk ncnt k ts tk
  (TR: transl_statement tyret nbrk ncnt s = OK ts)
  (MC: match_cont tyret nbrk ncnt k tk),
  match Clight.find_label lbl s k with
  | None => find_label lbl ts tk = None
  | Some (s', k') =>
      exists ts', exists tk', exists nbrk', exists ncnt',
      find_label lbl ts tk = Some (ts', tk')
      /\ transl_statement tyret nbrk' ncnt' s' = OK ts'
      /\ match_cont tyret nbrk' ncnt' k' tk'
  end

with transl_find_label_ls:
  forall ls nbrk ncnt k tls tk
  (TR: transl_lbl_stmt tyret nbrk ncnt ls = OK tls)
  (MC: match_cont tyret nbrk ncnt k tk),
  match Clight.find_label_ls lbl ls k with
  | None => find_label_ls lbl tls tk = None
  | Some (s', k') =>
      exists ts', exists tk', exists nbrk', exists ncnt',
      find_label_ls lbl tls tk = Some (ts', tk')
      /\ transl_statement tyret nbrk' ncnt' s' = OK ts'
      /\ match_cont tyret nbrk' ncnt' k' tk'
  end.

Proof.
  intro s; case s; intros; try (monadInv TR); simpl.
- (* skip *)
  auto.
- (* assign *)
  unfold make_store, make_memcpy in EQ3.
  destruct (access_mode (typeof e)); inv EQ3; auto.
- (* set *)
  auto.
- (* call *)
  simpl in TR. destruct (classify_fun (typeof e)); monadInv TR. auto.
- (* builtin *)
  auto.
- (* seq *)
  exploit (transl_find_label s0 nbrk ncnt (Clight.Kseq s1 k)); eauto. econstructor; eauto.
    destruct (Clight.find_label lbl s0 (Clight.Kseq s1 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H. eapply transl_find_label; eauto.
- (* ifthenelse *)
  exploit (transl_find_label s0); eauto. 
  destruct (Clight.find_label lbl s0 k) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H. eapply transl_find_label; eauto.
- (* loop *)
  exploit (transl_find_label s0 1%nat 0%nat (Kloop1 s0 s1 k)); eauto. econstructor; eauto.
    destruct (Clight.find_label lbl s0 (Kloop1 s0 s1 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H.
  eapply transl_find_label; eauto. econstructor; eauto.
  - (* break *)
  auto.
- (* continue *)
  auto.
- (* return *)
  simpl in TR. destruct o; monadInv TR. auto. auto. 
- (* switch *)
  assert (exists b, ts = Sblock (Sswitch b x x0)).
  { destruct (classify_switch (typeof e)); inv EQ2; econstructor; eauto. }
  destruct H as [b EQ3]; rewrite EQ3; simpl.
  eapply transl_find_label_ls with (k := Clight.Kswitch k); eauto. econstructor; eauto. 
- (* label *)
  destruct (ident_eq lbl l). 
  exists x; exists tk; exists nbrk; exists ncnt; auto.
  eapply transl_find_label; eauto.
- (* goto *)
  auto.
- intro ls; case ls; intros; monadInv TR; simpl. 
  auto.
  exploit (transl_find_label s nbrk ncnt (Clight.Kseq (seq_of_labeled_statement l) k)); eauto. 
  econstructor; eauto. apply transl_lbl_stmt_2; eauto.
    destruct (Clight.find_label lbl s (Clight.Kseq (seq_of_labeled_statement l) k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H.
  eapply transl_find_label_ls; eauto.
Qed.

End FIND_LABEL.

(** Properties of call continuations *)

Lemma match_cont_call_cont:
  forall tyret' nbrk' ncnt' tyret nbrk ncnt k tk,
    match_cont tyret nbrk ncnt k tk ->
    match_cont  tyret' nbrk' ncnt' (Clight.call_cont k) (call_cont tk).
Proof.
  induction 1; simpl; intros; auto.
  constructor.
  econstructor; eauto.
Qed.

Lemma match_cont_is_call_cont:
  forall tyret nbrk ncnt k tk tyret' nbrk' ncnt',
  match_cont tyret nbrk ncnt k tk ->
  Clight.is_call_cont k ->
  match_cont tyret' nbrk' ncnt' k tk /\ is_call_cont tk.
Proof.
  intros. inv H; simpl in H0; try contradiction; simpl.
  split; auto; constructor.
  split; auto; econstructor; eauto.
Qed.

(** The simulation proof *)

Lemma match_states_mem_equiv:
  forall f s ts k e e' te tf tk m1 m2 m2',
    mem_lessdef m2 m2' ->
    match_states (Clight.State f s k e te m1)
                 (State tf ts tk e' te m2) ->
        match_states (Clight.State f s k e te m1)
                     (State tf ts tk e' te m2').
Proof.
  intros f s ts k e e' te tf tk m1 m2 m2' ME MS.
  inv MS.
  econstructor; eauto.
  rewrite ME0; auto.
Qed.

Lemma eval_unop_same_eval:
  forall op v1 v sv',
     eval_unop op v1 = Some v ->
     Val.lessdef v1 sv' ->
     exists sv,
       eval_unop op sv' = Some sv /\
       Val.lessdef v sv.
Proof.
  intros op v1 v sv' EU SE.
  destruct op; simpl in *; inv EU;
  (eexists; split; eauto);
  try (apply Val.lessdef_unop; auto).
Qed.


Lemma eval_binop_same_eval:
  forall op v1 v2 v sv' sv2' m m',
     eval_binop op v1 v2 m = Some v ->
     Val.lessdef v1 sv' ->
     Val.lessdef v2 sv2' ->
     exists sv,
       eval_binop op sv' sv2' m' = Some sv /\
       Val.lessdef v sv.
Proof.
  intros op v1 v2 v sv' sv2' m m' EB SE SE2.
  destruct op; simpl in *; inv EB;
  (eexists; split; eauto);
  try (apply Val.lessdef_binop; auto).
Qed.

Lemma mem_equiv_eval_expr:
  forall ge e te m m' a sv,
    mem_lessdef m m' ->
    eval_expr ge e te m a sv ->
    exists sv',
      eval_expr ge e te m' a sv' /\
      Val.lessdef sv sv'.
Proof.
  intros ge0 e te m m' a sv ME EV.
  induction EV.
  - eexists; split; eauto. econstructor; eauto.
  - eexists; split; eauto. econstructor; eauto.
  - eexists; split; eauto. econstructor; eauto.
  - destruct IHEV as [sv' [A B]].
    destruct (eval_unop_same_eval _ _ _ _ H B) as [sv [C D]].
    eexists; split.
    econstructor; simpl; eauto.
    auto.
  - destruct IHEV1 as [sv' [A B]].
    destruct IHEV2 as [sv'' [A' B']].
    destruct (eval_binop_same_eval _ _ _ _ _ _ _ m' H B B') as [sv [C D]].
    eexists; split.
    econstructor; simpl; eauto.
    auto.
  - destruct IHEV as [sv' [A B]].
    unfold Mem.loadv in H.
    revert H; destr_cond_match; intros; try discriminate.
    destruct (mem_rel_load _ wf_mr_ld chunk m m' _ _ _ ME H) as [v' [C D]].
    eexists; split.
    econstructor; simpl; eauto.
    unfold Mem.loadv in *.
    setoid_rewrite <- mem_rel_norm with (m':=m'); eauto.
    generalize (Mem.lessdef_eqm m _ _ B).
    rewrite Heqv0. intro E; inv E;eauto.
    auto. 
Qed.

Lemma free_same_eval_cmp:
 forall ge e le m a v v',
    eval_expr ge e le m a v ->
    Val.lessdef v' v ->
    exists v'' : expr_sym,
      eval_expr ge e le m (make_cmp_ne_zero a) v'' /\
      Val.lessdef (Eunop OpBoolval Tint v') v''.
Proof.
  intros.
  inv H; try (eexists; split; [repeat (econstructor; simpl; eauto)|]; [idtac]);
  try (red; intros; rewrite nec_cmp_ne_zero; apply Val.lessdef_binop; auto).
  des op; try (eexists; split; [repeat (econstructor; simpl; eauto)|]; [idtac]);
  try (red; intros; rewrite nec_cmp_ne_zero; apply Val.lessdef_binop; auto);
  inv H3; red; intros;
  unfold Val.cmp,Val.cmpu,Val.cmp_bool, Val.cmpu_bool,
  Val.cmpf, Val.cmpfs, Val.cmpl, Val.cmplu,
  Val.cmpf_bool, Val.cmpfs_bool, Val.cmpl_bool, Val.cmplu_bool;
  try rewrite norm_boolval_cmp;
  apply Val.lessdef_unop; auto.
Qed.

Lemma alloc_variables_mem_equiv:
  forall m e1 vars e2 m2,
    alloc_variables e1 m vars e2 m2 ->
    forall m',
      mem_lessdef m m' ->
      exists m2',
        alloc_variables e1 m' vars e2 m2' /\
        mem_lessdef m2 m2'.
Proof.
  induction 1; simpl; intros.
  eexists; split; eauto.
  econstructor.
  eapply alloc_mem_rel in H; eauto.
  destruct H as [m2' [A B]].
  apply IHalloc_variables in B.
  destruct B as [m2'0 [B C]].
  eexists; split; eauto.
  econstructor; eauto.
  apply wf_mr_ld.
Qed.

Require Import VarSort.

Lemma var_sort_eq:
  forall l,
    varsort' (map transl_var l) = map transl_var (varsort l).
Proof.
  induction l. auto.
  simpl.
  rewrite IHl.
  generalize (varsort l).
  clear.
  induction l; simpl; auto.
  unfold le2, le1 in *. simpl.
  repeat destr.
Qed.

Instance lessdef_preorder: RelationClasses.PreOrder Val.lessdef.
Proof.
  constructor; red; intros; auto.
  eapply Val.lessdef_trans; eauto.
Qed.

Lemma mem_eq_ld:
  forall m1 m2,
    mem_equiv m1 m2 -> mem_lessdef m1 m2.
Proof.
  intros m1 m2 ME; inv ME; constructor; eauto.
  red; intros.
  generalize (mem_contents_eq b ofs).
  destr.
  
  apply se_ld; auto. apply H2.
  red in H2. destr.
Qed.

Hint Resolve wf_mr_ld wf_mr_norm_ld.

Lemma transl_step:
  forall S1 t S2, Clight.step2 ge needed_stackspace S1 t S2 ->
  forall T1, match_states S1 T1 ->
  exists T2, plus (fun ge => step ge needed_stackspace) tge T1 t T2 /\ match_states S2 T2.
Proof.
  induction 1; intros T1 MST; inv MST.

- (* assign *)
  monadInv TR. 
  assert (SAME: ts' = ts /\ tk' = tk).
  {
    inversion MTR. auto. 
    subst ts. unfold make_store, make_memcpy in EQ3. destruct (access_mode (typeof a1)); congruence.
  }   
  destruct SAME; subst ts' tk'.  
  eapply (temp_equiv_clight_eval_lvalue  _ wf_mr_ld wf_mr_norm_ld) in H; eauto.
  eapply (temp_equiv_clight_eval_expr  _ wf_mr_ld wf_mr_norm_ld ) in H0; eauto.
  destruct H0 as [vv [H0 EE]].
  destruct H as [ptr' [LV1 SEL1]].
  apply (mem_equiv_clight_eval_expr _ wf_mr_ld wf_mr_norm_ld) with (m':=m'0) in H0; auto.
  apply (mem_equiv_clight_eval_lvalue _ wf_mr_ld wf_mr_norm_ld) with (m':=m'0) in LV1; auto. 
  eapply (mem_equiv_assign_loc _ wf_mr_ld) in H2; eauto. 
  destruct H0 as [sv' [A B]].
  destruct H2 as [m2' [C D]].
  destruct LV1 as [ptr'0 [LV1 SEL2]].
  assert (Val.lessdef v2 sv') by (eapply Val.lessdef_trans; eauto).
  generalize (sem_cast_expr_ld _ wf_mr_ld (typeof a2) (typeof a1) _ _ EE). rewrite H1.
  destr_cond_match; intros; try intuition congruence.
  destruct (transl_expr_correct _ _ _ _ MENV _ _ A _ EQ1) as [v' [E F]]; eauto.
  destruct (transl_lvalue_correct _ _ _ _ MENV _ _ LV1 _ EQ) as [v'' [G I]]; eauto.
  destruct (make_cast_correct _ _ _ _ _ _ _ vv _ _ e0 EQ0 E)
    as [v''' [J K]]; auto.
  eapply Val.lessdef_trans; eauto.
  assert (SE: Val.lessdef v v''').
  {
    rewrite <- K.
    auto.
  } 
  destruct (val_equiv_assign_loc _ wf_mr_ld wf_mr_norm_ld _ _ _ _ _ _ C SE) as [m2'0 [L M]].
  generalize (addr_equiv_assign_loc _ wf_mr_ld wf_mr_norm_ld  _ _ _ _ _ _ L (Val.lessdef_trans _ _ _ SEL1
                                                                   (Val.lessdef_trans _ _ _ SEL2 I))).
  intro Z. 
  destruct (make_store_correct _ needed_stackspace _ _ _ _ _ _ _ _ _ _ tf tk
                               EQ3 G J Z) as [m2'1 [N O]].
  econstructor; split; eauto.
  apply plus_one. 
  eexact N. 
  eapply match_states_skip; eauto.
  rewrite D.
  rewrite M.
  eapply mem_eq_ld; eauto.
  
- (* set *)
  monadInv TR. inv MTR.
  eapply temp_equiv_clight_eval_expr in H; eauto.
  destruct H as [vv [A0 A1]].
  eapply mem_equiv_clight_eval_expr in A0; eauto.
  destruct A0 as [sv' [A B]].
  eapply transl_expr_correct in A; eauto.
  destruct A as [v' [C D]].
  econstructor; split.
  apply plus_one. econstructor. eauto. 
  eapply match_states_skip; eauto.
  apply temp_env_equiv_set; auto.
  rewrite A1. rewrite B. auto.
  
- (* call *)
  revert TR. simpl. case_eq (classify_fun (typeof a)); try congruence.
  intros targs tres cc CF TR. monadInv TR. inv MTR.  
  exploit functions_translated; eauto. intros [tfd [FIND TFD]].
  rewrite H in CF. simpl in CF. inv CF.
  eapply temp_equiv_clight_eval_exprlist in H1; eauto.
  eapply temp_equiv_clight_eval_expr in H0; eauto.
  destruct H1 as [vl' [A B]].
  destruct H0 as [v' [C D]].
  eapply mem_equiv_clight_eval_exprlist in A; eauto.
  eapply mem_equiv_clight_eval_expr in C; eauto.
  destruct A as [sv' [A E]].
  destruct C as [sv'0 [C F]]. 
  
  exploit transl_expr_correct; eauto.
  exploit transl_arglist_correct; eauto.
  erewrite typlist_of_arglist_eq by eauto.
  intros [vl'0 [G I]] [v'0 [J K]].
  econstructor; split.
  apply plus_one. econstructor; eauto. 
  erewrite Genv.find_funct_lessdef. eauto.
  eauto.
  rewrite <- K.  rewrite <- F. rewrite <- D. reflexivity. eauto.
  eapply transl_fundef_sig1; eauto.
  rewrite H3. auto.
  econstructor; eauto.  
  econstructor; eauto.
  simpl. auto.
  eapply list_forall2_ld_trans; eauto.
  eapply list_forall2_ld_trans; eauto.
  
- (* builtin *)
  monadInv TR. inv MTR. 
  eapply temp_equiv_clight_eval_exprlist in H; eauto.
  destruct H as [vl' [A B]].
  eapply mem_equiv_clight_eval_exprlist in A; eauto.
  destruct A as [sv' [A C]].
  eapply transl_arglist_correct in A; eauto.
  destruct A as [vl'0 [A D]]. 
  generalize (external_call_symbols_preserved_2
                ef transl_globvar ge tge _ _ _ _ _ H0
                symbols_preserved
                (Genv.find_var_info_transf_partial2 transl_fundef transl_globvar _ TRANSL)
                (Genv.find_var_info_rev_transf_partial2 transl_fundef transl_globvar _ TRANSL)).
  intro. eapply (external_call_rel) with (m':=m'0) (args':=vl'0) in H; eauto.
  + destruct H as [vres' [m2' [E [F G]]]].
    econstructor; split.
    * apply plus_one. econstructor; eauto. 
    * eapply match_states_skip; eauto.  
      unfold set_opttemp, set_optvar.
      destr_cond_match; auto.
      apply temp_env_equiv_set; auto.
  +   eapply list_forall2_ld_trans; eauto.
      eapply list_forall2_ld_trans; eauto. 

- (* seq *)
  monadInv TR. inv MTR.
  econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto. constructor. 
  econstructor; eauto.

- (* skip seq *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  apply plus_one. apply step_skip_seq. 
  econstructor; eauto. constructor.

- (* continue seq *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto. simpl. reflexivity. constructor.

- (* break seq *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto. simpl. reflexivity. constructor.

- (* ifthenelse *)
  monadInv TR. inv MTR.
  eapply temp_equiv_clight_eval_expr in H; eauto.
  destruct H as [v' [H I]].
  eapply mem_equiv_clight_eval_expr in H; eauto.
  destruct H as [sv' [H J]].
  eapply transl_expr_correct in H; eauto.
  destruct H as [v'0 [H K]].
  eapply make_boolean_correct with (v':=sv') (ty:=typeof a) in H; eauto.
  destruct H as [vb [H L]].
  econstructor; split.
  + apply plus_one. apply step_ifthenelse with (v := vb) (b := b); auto.
    trim (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ (bool_expr v1 (typeof a)) vb ME).
    etransitivity; [|eauto].

      Ltac ld_rew :=
    repeat ((apply (mr_unop _ wf_mr_ld) ;auto)
            ||
            (apply (mr_binop _ wf_mr_ld) ;auto)
            || apply (mr_refl _ wf_mr_ld) ; auto).
    
    des (typeof a); try des i; try des s; try des f0; ld_rew; (etransitivity; eauto).
    rewrite H0.
    generalize (Mem.norm_gr m' vb); simpl.
    intros GR H2.
    generalize (H2 (fun _ => Int.zero) (fun _ _ => Byte.zero)).
    simpl; intro A.
    inv A.
    des (Mem.mem_norm m' vb).
    generalize (H2 (fun _ => Int.one) (fun _ _ => Byte.zero)).
    simpl. intro A; inv A.
    apply inj_vint in H4.
    rewrite ! (Int.add_commut _ i) in H4.
    apply int_add_eq_l in H4; discriminate.
  + 
    destruct (negb (Int.eq b Int.zero)); econstructor; eauto;
    constructor.

- (* loop *)
  monadInv TR.
  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto. 
  eapply plus_left. constructor. 
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. traceEq.
  econstructor; eauto. constructor. econstructor; eauto. 

- (* skip-or-continue loop *)
  assert ((ts' = Sskip \/ ts' = Sexit ncnt) /\ tk' = tk).
    destruct H; subst x; monadInv TR; inv MTR; auto.
  destruct H0. inv MK.
  econstructor; split.
  eapply plus_left.
  destruct H0; subst ts'. 2:constructor. constructor.
  apply star_one. constructor. traceEq.
  econstructor; eauto. constructor. econstructor; eauto. 

- (* break loop1 *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  eapply plus_left. constructor.
  eapply star_left. constructor.
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. traceEq.
  eapply match_states_skip; eauto.

- (* skip loop2 *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto. 
  simpl. rewrite H5; simpl. rewrite H7; simpl. eauto. 
  constructor. 

- (* break loop2 *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  eapply plus_left. constructor.
  apply star_one. constructor.
  traceEq.
  eapply match_states_skip; eauto.

- (* return none *)
  monadInv TR. inv MTR.
  eapply free_list_mem_equiv in H; eauto.
  destruct H as [m2' [A B]].
  eapply MemReserve.release_boxes_rel in H0; eauto.
  destruct H0 as [m3' [C D]].
  econstructor; split.
  apply plus_one. econstructor.
  eapply match_env_free_blocks; eauto.
  replace (fn_id tf) with (Clight.fn_id f). eauto.
  unfold transl_function in TRF. monadInv TRF. reflexivity.
  econstructor; eauto.
  eapply match_cont_call_cont. eauto. 


- (* return some *)
  monadInv TR. inv MTR.
  eapply temp_equiv_clight_eval_expr in H; eauto.
  destruct H as [v'0 [A B]].
  eapply mem_equiv_clight_eval_expr in A; eauto.
  destruct A as [sv' [A B']].
  eapply transl_expr_correct in A; eauto.
  destruct A as [v'1 [A C]].
  generalize (sem_cast_expr_ld _ wf_mr_ld (typeof a) (fn_return f) _ _ B); rewrite H0.
  destr_cond_match; try intuition congruence.
  intros.
  eapply make_cast_correct in Heqo; eauto.
  destruct Heqo as [v'' [D E]].
  eapply free_list_mem_equiv in H1; eauto.
  destruct H1 as [m2' [F G]].
  eapply MemReserve.release_boxes_rel in H2; eauto.
  destruct H2 as [m3' [I J]].
  econstructor; split.
  apply plus_one. econstructor. eauto.
  eapply match_env_free_blocks; eauto.
  replace (fn_id tf) with (Clight.fn_id f). eauto.
  unfold transl_function in TRF. monadInv TRF. reflexivity.
  econstructor; eauto.
  eapply match_cont_call_cont. eauto. 
  rewrite H; auto.
  rewrite <- C. auto.

- (* skip call *)
  monadInv TR. inv MTR.
  eapply free_list_mem_equiv in H0; eauto.
  destruct H0 as [m2' [A B]].
  eapply MemReserve.release_boxes_rel in H1; eauto.
  destruct H1 as [m3' [C D]].
  exploit match_cont_is_call_cont; eauto. intros [E F].
  econstructor; split.
  apply plus_one. eapply step_skip_call. auto.
  eapply match_env_free_blocks; eauto.
  replace (fn_id tf) with (Clight.fn_id f). eauto.
  unfold transl_function in TRF. monadInv TRF. reflexivity.
  constructor; eauto.
    
- (* switch *)
  monadInv TR.
  eapply temp_equiv_clight_eval_expr in H; eauto.
  destruct H as [v' [A B]].
  eapply mem_equiv_clight_eval_expr in A; eauto.
  destruct A as [sv' [A C]].
  eapply transl_expr_correct in A; eauto.
  destruct A as [v'0 [A D]].
  
  assert (E: exists b, ts = Sblock (Sswitch b x x0) /\ Switch.switch_argument m' b v'0 n).
  { unfold sem_switch_arg_expr in H0.
    destruct (classify_switch (typeof a)); inv EQ2; econstructor; split; eauto;
    revert H0; destr_cond_match;  
    intro E; inv E; constructor; auto.
    generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ v v'0 ME).
    intro E; trim E. repeat (etransitivity; eauto).
    rewrite lessdef_val in E. rewrite Heqv0 in E.
    inv E; auto.
    generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ v v'0 ME).
    intro E; trim E. repeat (etransitivity; eauto).
    rewrite lessdef_val in E. rewrite Heqv0 in E.
    inv E; auto.
  }
  destruct E as (b & ? & ?). subst ts. 

  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto.
  apply plus_one. econstructor; eauto. traceEq. 
  econstructor; eauto.
  apply transl_lbl_stmt_2. apply transl_lbl_stmt_1. eauto. 
  constructor.
  econstructor. eauto.

- (* skip or break switch *)
  assert ((ts' = Sskip \/ ts' = Sexit nbrk) /\ tk' = tk).
    destruct H; subst x; monadInv TR; inv MTR; auto.
  destruct H0. inv MK.
  econstructor; split.
  apply plus_one. destruct H0; subst ts'. 2:constructor. constructor.
  eapply match_states_skip; eauto.


- (* continue switch *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto. simpl. reflexivity. constructor.

- (* label *)
  monadInv TR. inv MTR. 
  econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto. constructor.

- (* goto *)
  monadInv TR. inv MTR.
  generalize TRF. unfold transl_function. intro TRF'. monadInv TRF'.
  exploit (transl_find_label lbl). eexact EQ. eapply match_cont_call_cont. eauto.
  rewrite H. 
  intros [ts' [tk'' [nbrk' [ncnt' [A [B C]]]]]].
  econstructor; split.
  apply plus_one. constructor. simpl. eexact A. 
  econstructor; eauto. constructor.

- (* internal function *)
  inv H. monadInv TR. monadInv EQ. 
  exploit match_cont_is_call_cont; eauto. intros [A B]. 
  exploit match_env_alloc_variables; eauto. 
  apply match_env_empty.
  intros [te1 [C D]].
  eapply alloc_variables_mem_equiv in C; eauto.
  destruct C as [m2' [C E]]. simpl.
  eapply bind_parameter_temps_equiv in H4.
  destruct H4 as [le' [F G]].
  destruct (MemReserve.reserve_boxes_rel _ _ _ E _ _ H5) as [m1' [I J]].
  econstructor; split. 
  apply plus_one.
  eapply step_internal_function.  
  simpl. rewrite list_map_compose. simpl.  auto. simpl. auto.
  simpl. auto. 
  simpl. rewrite var_sort_eq. eauto. 
  simpl fn_params. simpl fn_temps.
  simpl. rewrite create_undef_temps_match. eapply bind_parameter_temps_match; eauto.
  eauto.
  simpl.
  econstructor; eauto.
  unfold transl_function. rewrite EQ0; simpl. auto.
  constructor; auto.
  auto.
  apply temp_env_equiv_refl; auto.
  
- (* external function *)
  simpl in TR.
  eapply external_call_rel in H; eauto.
  destruct H as [vres' [m2' [EC [VR ME']]]].
  destruct (signature_eq (ef_sig ef) (signature_of_type targs tres cconv)); inv TR.
  exploit match_cont_is_call_cont; eauto. intros [A B].
  econstructor; split.
  apply plus_one. constructor. eauto. 
  eapply external_call_symbols_preserved_2; eauto.
  exact symbols_preserved.
  eexact (Genv.find_var_info_transf_partial2 transl_fundef transl_globvar _ TRANSL).
  eexact (Genv.find_var_info_rev_transf_partial2 transl_fundef transl_globvar _ TRANSL).
  econstructor; eauto.

- (* returnstate *)
  inv MK. 
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto. simpl; reflexivity. constructor.
  unfold set_opttemp, set_optvar.
  destr_cond_match; auto.
  apply temp_env_equiv_set; auto.
Qed.

Lemma transl_initial_states:
  forall sg S, Clight.initial_state prog sg S ->
  exists R, initial_state tprog sg R /\ match_states S R.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  assert (C: Genv.find_symbol tge (prog_main tprog) = Some b).
  {
    rewrite symbols_preserved. replace (prog_main tprog) with (prog_main prog).
    auto. symmetry. unfold transl_program in TRANSL. 
    eapply transform_partial_program2_main; eauto.
  }
  assert (funsig tf = signature_of_type Tnil type_int32s cc_default).
  { eapply transl_fundef_sig2; eauto. }
  econstructor; split.
  - econstructor; eauto. eapply Genv.init_mem_transf_partial2; eauto.
    intros a b0 TR.
    unfold Clight.fid, fid. des a; des b0; try monadInv TR.
    unfold transl_function in EQ; monadInv EQ. auto.
    revert TR; destr.
  - econstructor; eauto. constructor; auto. exact I.
    reflexivity. constructor.
Qed.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> Clight.final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H. inv MK. constructor.
  generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ ME MRES).
  rewrite lessdef_val.
  rewrite H1. intro A; inv A. auto.
Qed.

Theorem transl_program_correct:
  forall sg,
    forward_simulation
      (Clight.semantics2 prog needed_stackspace sg)
      (Csharpminor.semantics tprog needed_stackspace sg).
Proof.
  intros.
  eapply forward_simulation_plus.
  eexact symbols_preserved.
  apply transl_initial_states.
  eexact transl_final_states.
  eexact transl_step.
Qed.

End CORRECTNESS.
