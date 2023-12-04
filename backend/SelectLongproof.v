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

(** Correctness of instruction selection for integer division *)

Require Import Coqlib.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import NormaliseSpec.
Require Import ExprEval.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.
Require Import SelectOpproof.
Require Import SelectLong.
Require Import Values_symbolictype.
Require Import Values_symbolic.
Require Import IntFacts.

Open Local Scope cminorsel_scope.

(** * Axiomatization of the helper functions *)

Section HELPERS.

Context {F V: Type} (ge: Genv.t (AST.fundef F) V).

Definition helper_implements (id: ident) (sg: signature) (vargs: list expr_sym) (vres: expr_sym) : Prop :=
  exists b, exists ef,
     Genv.find_symbol ge id = Some b
  /\ Genv.find_funct_ptr ge b = Some (External ef)
  /\ ef_sig ef = sg
  /\ forall m, external_call ef ge vargs m E0 vres m.

Definition builtin_implements (id: ident) (sg: signature) (vargs: list expr_sym) (vres: expr_sym) : Prop :=
  forall m, external_call (EF_builtin id sg) ge vargs m E0 vres m.

Definition i64_helpers_correct (hf: helper_functions) : Prop :=
    (forall x z, Val.longoffloat x = z -> helper_implements hf.(i64_dtos) sig_f_l (x::nil) z)
  /\(forall x z, Val.longuoffloat x = z -> helper_implements hf.(i64_dtou) sig_f_l (x::nil) z)
  /\(forall x z, Val.floatoflong x = z -> helper_implements hf.(i64_stod) sig_l_f (x::nil) z)
  /\(forall x z, Val.floatoflongu x = z -> helper_implements hf.(i64_utod) sig_l_f (x::nil) z)
  /\(forall x z, Val.singleoflong x = z -> helper_implements hf.(i64_stof) sig_l_s (x::nil) z)
  /\(forall x z, Val.singleoflongu x = z -> helper_implements hf.(i64_utof) sig_l_s (x::nil) z)
  /\(forall x, builtin_implements hf.(i64_neg) sig_l_l (x::nil) (Val.negl x))
  /\(forall x y, builtin_implements hf.(i64_add) sig_ll_l (x::y::nil) (Val.addl x y))
  /\(forall x y, builtin_implements hf.(i64_sub) sig_ll_l (x::y::nil) (Val.subl x y))
  /\(forall x y, builtin_implements hf.(i64_mul) sig_ii_l (x::y::nil) (Val.mull' x y))
  /\(forall x y z, Val.divls x y = z -> helper_implements hf.(i64_sdiv) sig_ll_l (x::y::nil) z)
  /\(forall x y z, Val.divlu x y = z -> helper_implements hf.(i64_udiv) sig_ll_l (x::y::nil) z)
  /\(forall x y z, Val.modls x y = z -> helper_implements hf.(i64_smod) sig_ll_l (x::y::nil) z)
  /\(forall x y z, Val.modlu x y = z -> helper_implements hf.(i64_umod) sig_ll_l (x::y::nil) z)
  /\(forall x y, helper_implements hf.(i64_shl) sig_li_l (x::y::nil) (Val.shll x y))
  /\(forall x y, helper_implements hf.(i64_shr) sig_li_l (x::y::nil) (Val.shrlu x y))
  /\(forall x y, helper_implements hf.(i64_sar) sig_li_l (x::y::nil) (Val.shrl x y))
  /\(forall x z, Val.intuoffloat x = z -> helper_implements hf.(helper_f2u) sig_f_i (x::nil) z)
  /\(forall x z, Val.floatofintu x = z -> helper_implements hf.(helper_u2f) sig_i_f (x::nil) z).
End HELPERS.

(** * Correctness of the instruction selection functions for 64-bit operators *)

Section CMCONSTR.

Variable hf: helper_functions.
Variable ge: genv.
Hypothesis HELPERS: i64_helpers_correct ge hf.
Variable sp: expr_sym.
Variable e: env.
Variable m: mem.

Ltac UseHelper :=
  red in HELPERS;
  repeat (eauto; match goal with | [ H: _ /\ _ |- _ ] => destruct H end).

Lemma eval_helper:
  forall le id sg args vargs vres,
  eval_exprlist ge sp e m le args vargs ->
  helper_implements ge id sg vargs vres ->
  eval_expr ge sp e m le (Eexternal id sg args) vres.
Proof.
  intros. destruct H0 as (b & ef & A & B & C & D). econstructor; eauto.
Qed.

Corollary eval_helper_1:
  forall le id sg arg1 varg1 vres,
  eval_expr ge sp e m le arg1 varg1 ->
  helper_implements ge id sg (varg1::nil) vres ->
  eval_expr ge sp e m le (Eexternal id sg (arg1 ::: Enil)) vres.
Proof.
  intros. eapply eval_helper; eauto. constructor; auto. constructor.
Qed.

Corollary eval_helper_2:
  forall le id sg arg1 arg2 varg1 varg2 vres,
  eval_expr ge sp e m le arg1 varg1 ->
  eval_expr ge sp e m le arg2 varg2 ->
  helper_implements ge id sg (varg1::varg2::nil) vres ->
  eval_expr ge sp e m le (Eexternal id sg (arg1 ::: arg2 ::: Enil)) vres.
Proof.
  intros. eapply eval_helper; eauto. constructor; auto. constructor; auto. constructor.
Qed.

Remark eval_builtin_1:
  forall le id sg arg1 varg1 vres,
  eval_expr ge sp e m le arg1 varg1 ->
  builtin_implements ge id sg (varg1::nil) vres ->
  eval_expr ge sp e m le (Ebuiltin (EF_builtin id sg) (arg1 ::: Enil)) vres.
Proof.
  intros. econstructor. econstructor. eauto. constructor. apply H0. 
Qed.

Remark eval_builtin_2:
  forall le id sg arg1 arg2 varg1 varg2 vres,
  eval_expr ge sp e m le arg1 varg1 ->
  eval_expr ge sp e m le arg2 varg2 ->
  builtin_implements ge id sg (varg1::varg2::nil) vres ->
  eval_expr ge sp e m le (Ebuiltin (EF_builtin id sg) (arg1 ::: arg2 ::: Enil)) vres.
Proof.
  intros. econstructor. constructor; eauto. constructor; eauto. constructor. apply H1.
Qed.

Definition unary_constructor_sound (cstr: expr -> expr) (sem: expr_sym -> expr_sym) : Prop :=
  forall le a x,
    eval_expr ge sp e m le a x ->
    exists v, eval_expr ge sp e m le (cstr a) v /\ Val.lessdef (sem x) v.

Definition binary_constructor_sound (cstr: expr -> expr -> expr) (sem: expr_sym -> expr_sym -> expr_sym) : Prop :=
  forall le a x b y,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  exists v, eval_expr ge sp e m le (cstr a b) v /\ Val.lessdef (sem x y) v.

Ltac EvalOp :=
  eauto;
  match goal with
  | [ |- eval_exprlist _ _ _ _ _ Enil _ ] => constructor
  | [ |- eval_exprlist _ _ _ _ _ (_:::_) _ ] => econstructor; EvalOp
  | [ |- eval_expr _ _ _ _ _ (Eletvar _) _ ] => constructor; simpl; eauto
  | [ |- eval_expr _ _ _ _ _ (Elet _ _) _ ] => econstructor; EvalOp
  | [ |- eval_expr _ _ _ _ _ (lift _) _ ] => apply eval_lift; EvalOp
  | [ |- eval_expr _ _ _ _ _ _ _ ] => eapply eval_Eop; [EvalOp | simpl; eauto]
  | _ => idtac
  end.

Lemma same_eval_longofwords_recompose:
  forall v,
    wt_expr v Tlong ->
    same_eval v (Val.longofwords (Val.hiword v) (Val.loword v)).
Proof.
  red.
  intros. simpl.
  generalize (expr_type _ _ H alloc em).
  seval.
  rewrite Int64.ofwords_recompose. auto.
Qed.

Lemma eval_splitlong:
  forall le a f v sem
         (same_eval_sem: forall v v', Val.lessdef v v' ->
                                      Val.lessdef (sem v) (sem v'))
         (sem_undef: forall v, (~ wt_expr v Tlong) ->
                               forall alloc em, eSexpr alloc em (sem v) = Vundef),
  (forall le a b x y
          (EXPRx: eval_expr ge sp e m le a x)
          (EXPRy: eval_expr ge sp e m le b y),
   exists v,
     eval_expr ge sp e m le (f a b) v /\
     Val.lessdef (sem (Val.longofwords x y)) v) ->
  eval_expr ge sp e m le a v ->
  exists v', eval_expr ge sp e m le (splitlong a f) v' /\ Val.lessdef (sem v) v'.
Proof.
  intros until sem; intros SEsem sem_undef EXEC.
  unfold splitlong. case (splitlong_match a); intros.
- InvEval. subst v.
  exploit EXEC. eexact H2. eexact H3.
  intros [v' [A B]]. 
  exists v'; split. auto. auto. 
- exploit (EXEC (v :: le) (Eop Ohighlong (Eletvar 0 ::: Enil)) (Eop Olowlong (Eletvar 0 ::: Enil))).
  EvalOp. EvalOp.
  intros [v' [A B]].
  exists v'; split. econstructor; eauto. ldt. 
  destruct (wt_expr_dec v Tlong).
  apply SEsem.
  red; intros.
  apply Val.lessdef_same.
  rewrite (same_eval_longofwords_recompose v ); auto.
  red; intros.
  rewrite sem_undef. constructor. auto.
Qed.


Lemma eval_lowlong: unary_constructor_sound lowlong Val.loword.
Proof.
  unfold lowlong; red. intros until x. destruct (lowlong_match a); intros.
  InvEval. subst x. exists v0; split; auto.
  ld.
  rewrite Int64.lo_ofwords. auto. 
  exists (Val.loword x); split; auto. EvalOp.  
Qed.

Lemma eval_highlong: unary_constructor_sound highlong Val.hiword.
Proof.
  unfold highlong; red. intros until x. destruct (highlong_match a); intros.
  InvEval. subst x. exists v1; split; auto. 
  ld. 
  rewrite Int64.hi_ofwords. auto. 
  exists (Val.hiword x); split; auto. EvalOp. 
Qed.


Lemma eval_splitlong_strict:
  forall le a f va v,
  eval_expr ge sp e m le a va ->
  (forall le a1 a2,
     (exists va1,
        eval_expr ge sp e m le a1 va1 
        /\ Val.lessdef (Val.hiword va) va1) ->
     (exists va2,
        eval_expr ge sp e m le a2 va2 
        /\ Val.lessdef (Val.loword va) va2) ->
     exists v',
       eval_expr ge sp e m le (f a1 a2) v' /\ Val.lessdef v v') ->
  exists v',
    eval_expr ge sp e m le (splitlong a f) v' /\
    Val.lessdef v v'.
Proof.
  intros until v. 
  unfold splitlong. case (splitlong_match a); intros.
- InvEval. subst. 
  eapply H0; eauto; eexists; split; eauto.
  red; intros; simpl; seval; auto. rewrite Int64.hi_ofwords; auto.
  red; intros; simpl; seval; auto. rewrite Int64.lo_ofwords; auto.
- exploit (eval_highlong (va::le) (Eletvar 0)). EvalOp.
  exploit (eval_lowlong (va::le) (Eletvar 0)). EvalOp.
  intros B A.
  exploit H0. eexact A. eexact B.
  intros [v' [C D]].
  eexists; split. EvalOp. auto.
Qed.

Lemma eval_splitlong2:
  forall le a b f va vb sem
         (same_eval_sem:
            forall v v' x x',
              Val.lessdef v v' ->
              Val.lessdef x x' ->
              Val.lessdef (sem v x) (sem v' x'))
         (sem_undef:
            forall v x,
              ~ wt_expr v Tlong \/ ~ wt_expr x Tlong ->
              forall alloc em, eSexpr alloc em (sem v x) = Vundef)
         (EXEC: forall le a1 a2 b1 b2 x1 x2 y1 y2
                       (EXPRx1: eval_expr ge sp e m le a1 x1)
                       (EXPRx2: eval_expr ge sp e m le a2 x2)
                       (EXPRy1: eval_expr ge sp e m le b1 y1)
                       (EXPRy2: eval_expr ge sp e m le b2 y2),
                exists v,
                  eval_expr ge sp e m le (f a1 a2 b1 b2) v /\
                  Val.lessdef (sem (Val.longofwords x1 x2) (Val.longofwords y1 y2)) v)
         (EXPR1: eval_expr ge sp e m le a va)
         (EXPR2: eval_expr ge sp e m le b vb),
  exists v, eval_expr ge sp e m le (splitlong2 a b f) v /\ Val.lessdef (sem va vb) v.
Proof.
  intros until sem; intros SEsem sem_undef EXEC.
  unfold splitlong2. case (splitlong2_match a b); intros.
  - InvEval. subst va vb.
    exploit (EXEC le h1 l1 h2 l2); eauto.
  - InvEval. subst va. 
    exploit (EXEC (vb :: le) (lift h1) (lift l1) 
                  (Eop Ohighlong (Eletvar 0 ::: Enil)) (Eop Olowlong (Eletvar 0 ::: Enil))).
    EvalOp. EvalOp. EvalOp. EvalOp.  
    intros [v [A B]].
    exists v; split.
    econstructor; eauto. ldt.
    destruct (wt_expr_dec vb Tlong).
    apply SEsem; auto. apply se_ld.
    apply same_eval_longofwords_recompose. auto.
    red; intros; rewrite sem_undef. constructor. auto.
  - InvEval. subst vb.
    exploit (EXEC (va :: le)
                  (Eop Ohighlong (Eletvar 0 ::: Enil)) (Eop Olowlong (Eletvar 0 ::: Enil))
                  (lift h2) (lift l2)).
    EvalOp. EvalOp. EvalOp. EvalOp. 
    intros [v [A B]].
    exists v; split.
    econstructor; eauto. ldt.
    destruct (wt_expr_dec va Tlong).
    apply SEsem; auto. apply se_ld. apply same_eval_longofwords_recompose. auto.
    red; intros; rewrite sem_undef; auto; constructor.
  - exploit (EXEC (vb :: va :: le)
                  (Eop Ohighlong (Eletvar 1 ::: Enil)) (Eop Olowlong (Eletvar 1 ::: Enil))
                  (Eop Ohighlong (Eletvar 0 ::: Enil)) (Eop Olowlong (Eletvar 0 ::: Enil))).
    EvalOp. EvalOp. EvalOp. EvalOp. 
    intros [v [A B]].
    exists v; split. EvalOp.
    ldt.
    destruct (wt_expr_dec va Tlong).
    destruct (wt_expr_dec vb Tlong).
    apply SEsem.
    apply se_ld. apply same_eval_longofwords_recompose. auto.
    apply se_ld. apply same_eval_longofwords_recompose. auto.
    red; intros. rewrite sem_undef; auto; constructor.
    red; intros. rewrite sem_undef; auto; constructor.
Qed.


Lemma eval_splitlong2_strict:
  forall le a b f va vb v,
    eval_expr ge sp e m le a va ->
    eval_expr ge sp e m le b vb ->
  (forall le a1 a2 b1 b2,
     (exists va1,
        eval_expr ge sp e m le a1 va1 
        /\ Val.lessdef (Val.hiword va) va1) ->
     (exists va2,
        eval_expr ge sp e m le a2 va2 
        /\ Val.lessdef (Val.loword va) va2) ->
     (exists vb1,
        eval_expr ge sp e m le b1 vb1 
        /\ Val.lessdef (Val.hiword vb) vb1) ->
     (exists vb2,
        eval_expr ge sp e m le b2 vb2 
        /\ Val.lessdef (Val.loword vb) vb2) ->
     exists v',
       eval_expr ge sp e m le (f a1 a2 b1 b2) v' /\ Val.lessdef v v') ->
  exists v',
    eval_expr ge sp e m le (splitlong2 a b f) v' /\
    Val.lessdef v v'.
Proof.
  assert (INV: forall v1 v2,
                 Val.lessdef (Val.hiword (Val.longofwords v1 v2)) v1
                 /\Val.lessdef (Val.loword (Val.longofwords v1 v2)) v2).
  {
    split; red; intros; simpl; seval; auto. 
    rewrite Int64.hi_ofwords; auto. rewrite Int64.lo_ofwords; auto.
  }
  intros until v. 
  unfold splitlong2. case (splitlong2_match a b); intros.
- InvEval. subst. 
  eapply H1; eauto; eexists; split; eauto.
  red; intros; simpl; seval; auto. rewrite Int64.hi_ofwords; auto.
  red; intros; simpl; seval; auto. rewrite Int64.lo_ofwords; auto.
  red; intros; simpl; seval; auto. rewrite Int64.hi_ofwords; auto.
  red; intros; simpl; seval; auto. rewrite Int64.lo_ofwords; auto.
- InvEval. subst.
  exploit (eval_highlong (vb::le) (Eletvar 0)). EvalOp.
  exploit (eval_lowlong (vb::le) (Eletvar 0)). EvalOp.
  exploit (eval_lift). eexact H4.
  exploit (eval_lift). eexact H5.
  intros D C B A.
  exploit H1.
  + eexists; split. eexact C. apply (proj1 (INV _ _ )).
  + eexists; split. eexact D. apply (proj2 (INV _ _ )).
  + eexact A.
  + eexact B.
  + intros [v' [E F]].
    eexists; split. EvalOp. auto.
- InvEval. subst.
  exploit (eval_highlong (va::le) (Eletvar 0)). EvalOp.
  exploit (eval_lowlong (va::le) (Eletvar 0)). EvalOp.
  exploit (eval_lift). eexact H4.
  exploit (eval_lift). eexact H5.
  intros D C B A.
  exploit H1.
  + eexact A.
  + eexact B.
  + eexists; split. eexact C. apply (proj1 (INV _ _ )).
  + eexists; split. eexact D. apply (proj2 (INV _ _ )).
  + intros [v' [E F]].
    eexists; split. EvalOp. auto.
- exploit (eval_highlong (vb::va::le) (Eletvar 0)). EvalOp.
  exploit (eval_highlong (vb::va::le) (Eletvar 1)). EvalOp.
  exploit (eval_lowlong (vb::va::le) (Eletvar 0)). EvalOp.
  exploit (eval_lowlong (vb::va::le) (Eletvar 1)). EvalOp.
  intros D C B A.
  exploit H1. eexact B. eexact D. eexact A. eexact C.
  intros [v' [E F]].
  eexists; split. EvalOp. auto.
Qed.



Lemma is_longconst_sound:
  forall le a x n,
  is_longconst a = Some n ->
  eval_expr ge sp e m le a x ->
  same_eval x (Eval (Vlong n)).
Proof.
  unfold is_longconst; intros until n; intros LC. 
  destruct (is_longconst_match a); intros.
  inv LC. InvEval. simpl in H5. inv H5. constructor; simpl; auto. 
  discriminate.
Qed.

Lemma is_longconst_zero_sound:
  forall le a x,
  is_longconst_zero a = true ->
  eval_expr ge sp e m le a x ->
  same_eval x (Eval (Vlong Int64.zero)).
Proof.
  unfold is_longconst_zero; intros. 
  destruct (is_longconst a) as [n|] eqn:E; try discriminate.
  revert H. predSpec Int64.eq Int64.eq_spec n Int64.zero.
  intros. subst. eapply is_longconst_sound; eauto. 
  congruence.
Qed.


Lemma eval_longconst: 
  forall le n,
  exists v, eval_expr ge sp e m le (longconst n) v /\
            same_eval v (Eval (Vlong n)).
Proof.
  intros. eexists; split. EvalOp.
  red; simpl; auto.
  intros; seval. rewrite Int64.ofwords_recompose; auto. 
Qed.

Theorem eval_intoflong: unary_constructor_sound intoflong Val.loword.
Proof eval_lowlong.

Theorem eval_longofintu: unary_constructor_sound longofintu Val.longofintu.
Proof.
  red; intros. unfold longofintu. econstructor; split. EvalOp. 
  ld. unfold convert_t. simpl.
  replace (Int64.repr (Int.unsigned i)) with (Int64.ofwords Int.zero i); auto.
  apply Int64.same_bits_eq; intros. 
  rewrite Int64.testbit_repr by auto.
  rewrite Int64.bits_ofwords by auto.
  fold (Int.testbit i i0).
  destruct (zlt i0 Int.zwordsize).
  auto.
  rewrite Int.bits_zero. rewrite Int.bits_above by omega. auto.
Qed.

Theorem eval_longofint: unary_constructor_sound longofint Val.longofint.
Proof.
  red; intros. unfold longofint.
  exploit (eval_shrimm ge sp e m (Int.repr 31) (x :: le) (Eletvar 0)). EvalOp. eauto.
  intros [v1 [A B]].
  econstructor; split. EvalOp. unfold Val.longofwords. ldt.
  ld. unfold convert_t; simpl. 
  replace (Int64.repr (Int.signed i))
  with (Int64.ofwords (Int.shr i (Int.repr 31)) i); auto.
  apply Int64.same_bits_eq; intros. 
  rewrite Int64.testbit_repr by auto.
  rewrite Int64.bits_ofwords by auto.
  rewrite Int.bits_signed by omega.
  destruct (zlt i0 Int.zwordsize).
  auto.
  assert (Int64.zwordsize = 2 * Int.zwordsize) by reflexivity. 
  rewrite Int.bits_shr by omega.
  change (Int.unsigned (Int.repr 31)) with (Int.zwordsize - 1).
  f_equal. destruct (zlt (i0 - Int.zwordsize + (Int.zwordsize - 1)) Int.zwordsize); omega.
Qed.

Ltac TrivialExists :=
  eexists; split; [repeat (econstructor; simpl; eauto)|eauto; try solve[constructor; simpl; auto]].

Theorem eval_negl: unary_constructor_sound (negl hf) Val.negl.
Proof.
  unfold negl; red; intros. destruct (is_longconst a) eqn:E.
  TrivialExists. ld. rewrite Int64.ofwords_recompose.
  erewrite is_longconst_sound in Heqv; eauto.
  simpl in Heqv. inv Heqv. auto.
  econstructor; split. eapply eval_builtin_1; eauto. UseHelper. auto. 
Qed.

Theorem eval_notl: unary_constructor_sound notl Val.notl.
Proof.
  red; intros. unfold notl.
  apply eval_splitlong; auto. 
  - intros v v'; apply Val.lessdef_unop; auto. 
  - intros.
    simpl. generalize (expr_type' alloc em v Tlong).
    seval.
  - intros. 
    exploit eval_notint. eexact EXPRx. intros [va [C D]].
    exploit eval_notint. eexact EXPRy. intros [vb [E F]].
    exists (Val.longofwords va vb); split. EvalOp.
    red; intros; simpl.
    specialize (D alloc em); specialize (F alloc em).
    inv D; inv F;  seval; try constructor.
    unfold Int.not. rewrite <- Int64.decompose_xor. auto.
Qed.

Theorem eval_longoffloat:
  unary_constructor_sound (longoffloat hf) Val.longoffloat.
Proof.
  red; intros; unfold longoffloat. econstructor; split. 
  eapply eval_helper_1; eauto. UseHelper. 
  auto. 
Qed.

Theorem eval_longuoffloat:
  unary_constructor_sound (longuoffloat hf) Val.longuoffloat. 
Proof.
  red; intros; unfold longuoffloat. econstructor; split. 
  eapply eval_helper_1; eauto. UseHelper. 
  auto.
Qed.

Theorem eval_floatoflong:
  unary_constructor_sound (floatoflong hf) Val.floatoflong.
Proof.
  red; intros; unfold floatoflong. econstructor; split. 
  eapply eval_helper_1; eauto. UseHelper. 
  auto. 
Qed.

Theorem eval_floatoflongu:
  unary_constructor_sound (floatoflongu hf) Val.floatoflongu.
Proof.
  intros; unfold floatoflongu. econstructor; split. 
  eapply eval_helper_1; eauto. UseHelper. 
  auto. 
Qed.

Theorem eval_longofsingle:
  unary_constructor_sound (longofsingle hf) Val.longofsingle.
Proof.
  red; intros; unfold longofsingle.
  exploit eval_floatofsingle; eauto. intros (v & A & B).
  exploit eval_longoffloat; eauto. intros [v' [C D]].
  eexists; split; eauto.
  ldt. unfold Val.longoffloat. ldt. ld. 
  unfold convert_t. simpl.
  change (Float.of_single f) with (Float32.to_double f).
  des (Float32.to_long f); try constructor.
  erewrite Float32.to_long_double; eauto. simpl; auto.
Qed.

Theorem eval_longuofsingle:
  unary_constructor_sound (longuofsingle hf) Val.longuofsingle.
Proof.
  red; intros; unfold longuofsingle.
  exploit eval_floatofsingle; eauto. intros (v & A & B).
  exploit eval_longuoffloat; eauto. 
  intros (v2 & C & D).
  eexists; split; eauto. ldt. unfold Val.longuoffloat. ldt. ld. 
  unfold convert_t.
  simpl.
  change (Float.of_single f) with (Float32.to_double f).
  des (Float32.to_longu f); try constructor.
  erewrite Float32.to_longu_double; simpl; eauto.
Qed.

Theorem eval_singleoflong:
  unary_constructor_sound (singleoflong hf) Val.singleoflong.
Proof.
  red; intros; unfold singleoflong. econstructor; split. 
  eapply eval_helper_1; eauto. UseHelper. 
  auto. 
Qed.

Theorem eval_singleoflongu:
  unary_constructor_sound (singleoflongu hf) Val.singleoflongu.
Proof.
  intros; unfold singleoflongu. econstructor; split. 
  eapply eval_helper_1; eauto. UseHelper. 
  auto. 
Qed.

Theorem eval_andl: binary_constructor_sound andl Val.andl.
Proof.
  red; intros. unfold andl. apply eval_splitlong2; auto.
  - intros.
    apply Val.lessdef_binop; auto.
  - intros. simpl.
    destruct H1.
    generalize (expr_type' alloc em v Tlong); seval.
    generalize (expr_type' alloc em x0 Tlong); seval.
  - intros.
    exploit eval_and. eexact EXPRx1. eexact EXPRy1.
    exploit eval_and. eexact EXPRx2. eexact EXPRy2.
    intros [vb [C D]] [va [A B]].
    exists (Val.longofwords va vb); split. EvalOp. 
    unfold Val.longofwords; ldt. ld.
    rewrite Int64.decompose_and. auto.
Qed.

Theorem eval_orl: binary_constructor_sound orl Val.orl.
Proof.
  red; intros. unfold orl. apply eval_splitlong2; auto.
  - intros.
    apply Val.lessdef_binop; auto.
  - intros. simpl.
    destruct H1.
    generalize (expr_type' alloc em v Tlong); seval.
    generalize (expr_type' alloc em x0 Tlong); seval.
  - intros.
    exploit eval_or. eexact EXPRx1. eexact EXPRy1.
    exploit eval_or. eexact EXPRx2. eexact EXPRy2.
    intros [vb [C D]] [va [A B]].
    exists (Val.longofwords va vb); split. EvalOp. 
    unfold Val.longofwords; ldt. ld.
    rewrite Int64.decompose_or. auto.  
Qed.

Theorem eval_xorl: binary_constructor_sound xorl Val.xorl.
Proof.
  red; intros. unfold xorl. apply eval_splitlong2; auto.
  - intros.
    apply Val.lessdef_binop; auto.
  - intros. simpl.
    destruct H1.
    generalize (expr_type' alloc em v Tlong); seval.
    generalize (expr_type' alloc em x0 Tlong); seval.
  - intros.
    exploit eval_xor. eexact EXPRx1. eexact EXPRy1.
    exploit eval_xor. eexact EXPRx2. eexact EXPRy2.
    intros [vb [C D]] [va [A B]].
    exists (Val.longofwords va vb); split. EvalOp. 
    unfold Val.longofwords; ldt. ld.
    rewrite Int64.decompose_xor. auto.
Qed.

Lemma is_intconst_sound:
  forall le a x n,
  is_intconst a = Some n ->
  eval_expr ge sp e m le a x ->
  x = (Eval (Vint n)).
Proof.
  unfold is_intconst; intros until n; intros LC. 
  destruct a; try discriminate. destruct o; try discriminate. destruct e0; try discriminate.
  inv LC. intros. InvEval. reflexivity. 
Qed.

Remark eval_shift_imm:
  forall (P: expr -> Prop) n a0 a1 a2 a3,
  (n = Int.zero -> P a0) ->
  (0 <= Int.unsigned n < Int.zwordsize ->
   Int.ltu n Int.iwordsize = true ->
   Int.ltu (Int.sub Int.iwordsize n) Int.iwordsize = true ->
   Int.ltu n Int64.iwordsize' = true ->
   P a1) ->
  (Int.zwordsize <= Int.unsigned n < Int64.zwordsize ->
   Int.ltu (Int.sub n Int.iwordsize) Int.iwordsize = true ->
   P a2) ->
  P a3 ->
  P (if Int.eq n Int.zero then a0
     else if Int.ltu n Int.iwordsize then a1
     else if Int.ltu n Int64.iwordsize' then a2
     else a3).
Proof.
  intros until a3; intros A0 A1 A2 A3.
  predSpec Int.eq Int.eq_spec n Int.zero.
  apply A0; auto.
  assert (NZ: Int.unsigned n <> 0). 
  { red; intros. elim H. rewrite <- (Int.repr_unsigned n). rewrite H0. auto. }
  destruct (Int.ltu n Int.iwordsize) eqn:LT.
  exploit Int.ltu_iwordsize_inv; eauto. intros RANGE.
  assert (0 <= Int.zwordsize - Int.unsigned n < Int.zwordsize) by omega.
  apply A1. auto. auto. 
  unfold Int.ltu, Int.sub. rewrite Int.unsigned_repr_wordsize. 
  rewrite Int.unsigned_repr. rewrite zlt_true; auto. omega. 
  generalize Int.wordsize_max_unsigned; omega. 
  unfold Int.ltu. rewrite zlt_true; auto. 
  change (Int.unsigned Int64.iwordsize') with 64.
  change Int.zwordsize with 32 in RANGE. omega.
  destruct (Int.ltu n Int64.iwordsize') eqn:LT'.
  exploit Int.ltu_inv; eauto. 
  change (Int.unsigned Int64.iwordsize') with (Int.zwordsize * 2).
  intros RANGE.
  assert (Int.zwordsize <= Int.unsigned n).
    unfold Int.ltu in LT. rewrite Int.unsigned_repr_wordsize in LT. 
    destruct (zlt (Int.unsigned n) Int.zwordsize). discriminate. omega. 
  apply A2. tauto. unfold Int.ltu, Int.sub. rewrite Int.unsigned_repr_wordsize. 
  rewrite Int.unsigned_repr. rewrite zlt_true; auto. omega. 
  generalize Int.wordsize_max_unsigned; omega. 
  auto.
Qed.

Lemma eval_shllimm:
  forall n,
  unary_constructor_sound (fun e => shllimm hf e n) (fun v => Val.shll v (Eval (Vint n))).
Proof.
  unfold shllimm; red; intros.
  apply eval_shift_imm; intros.
  - (* n = 0 *)
    subst n. exists x; split; auto.
    ld.
    change (Int64.shl' i Int.zero) with (Int64.shl i Int64.zero). 
    rewrite Int64.shl_zero. auto.
  - (* 0 < n < 32 *)
    apply eval_splitlong with (sem := fun x => Val.shll x (Eval (Vint n))); auto.
    + intros; eapply Val.lessdef_binop; eauto.
    + intros. simpl.
      generalize (expr_type' alloc em v Tlong). seval.
    + intros.
      exploit eval_shlimm. eexact EXPRx. intros [v1 [A1 B1]].
      exploit eval_shlimm. eexact EXPRy. intros [v2 [A2 B2]].
      exploit eval_shruimm. eexact EXPRy. intros [v3 [A3 B3]].
      exploit eval_or. eexact A1. eexact A3.
      intros [v4 [A4 B4]].
      econstructor; split. EvalOp. 
      * clear A1 A2 A3 A4 EXPRx EXPRy.
        apply Val.lessdef_trans
        with (v2:= Val.longofwords (Val.or (Val.shl x0 (Eval (Vint n))) (Val.shru y (Eval (Vint (Int.sub Int.iwordsize n))))) (Val.shl y (Eval (Vint n)))).
        ld. destr; try constructor.
        rewrite Int64.decompose_shl_1; auto.
        replace (Int.ltu n Int.iwordsize) with true.
        replace (Int.ltu (Int.sub Int.iwordsize n) Int.iwordsize) with true. simpl.
        auto.
        repeat (ldt; apply Val.lessdef_binop; auto).
  - (* 32 <= n < 64 *)
    exploit eval_lowlong. eexact H. intros [v1 [A1 B1]].
    exploit eval_shlimm. eexact A1. intros [v2 [A2 B2]].
    econstructor; split. EvalOp.
    apply Val.lessdef_trans with
    (v2:=Val.longofwords (Val.shl (Val.loword x) (Eval (Vint (Int.sub n Int.iwordsize)))) (Eval (Vint Int.zero))).
    ld. destr; try constructor.
    destr.
    erewrite <- Int64.decompose_shl_2. instantiate (1 := Int64.hiword i). 
    rewrite Int64.ofwords_recompose. auto. auto.
    repeat (ldt; apply Val.lessdef_binop; auto).
  - (* n >= 64 *)
    econstructor; split. eapply eval_helper_2; eauto. EvalOp. UseHelper. auto. 
Qed.

Theorem eval_shll: binary_constructor_sound (shll hf) Val.shll.
Proof.
  unfold shll; red; intros.
  destruct (is_intconst b) as [n|] eqn:IC.
- (* Immediate *)
  exploit is_intconst_sound; eauto. intros EQ; subst y; clear H0.
  eapply eval_shllimm; eauto.
- (* General case *)
  econstructor; split. eapply eval_helper_2; eauto. UseHelper. auto. 
Qed.

      Ltac build_trans e :=
        match e with
          | Eunop ?u ?t ?f => let e' := build_trans f in
                              constr:(Eunop u t e')
          | Ebinop ?b ?t ?s ?f1 ?f2 =>
            let f1' := build_trans f1 in
            let f2' := build_trans f2 in
            constr:(Ebinop b t s f1' f2')
          | _ =>
            let a' := 
                match goal with
                  | H: Val.lessdef ?a e |- _ => build_trans a
                  | |- _ => e
                end
            in  constr:(a')
        end.

      Ltac ldt' := repeat match goal with
                              |- Val.lessdef ?c (Ebinop ?o ?t ?s ?b ?d) =>
                              let b' := build_trans b in
                              let d' := build_trans d in
                              apply Val.lessdef_trans with
                              (v2:=Ebinop o t s b' d');
                                [|repeat (ldt; apply Val.lessdef_binop; auto)]
                          end.


Lemma eval_shrluimm:
  forall n,
    unary_constructor_sound (fun e => shrluimm hf e n)
                            (fun v => Val.shrlu v (Eval (Vint n))).
Proof.
  unfold shrluimm; red; intros. apply eval_shift_imm; intros.
  - (* n = 0 *)
    subst n. exists x; split; auto.
    ld. destr; try constructor. 
    change (Int64.shru' i Int.zero) with (Int64.shru i Int64.zero). 
    rewrite Int64.shru_zero. auto.
  -  (* 0 < n < 32 *)
    apply eval_splitlong with (sem := fun x => Val.shrlu x (Eval (Vint n))); auto.
    + intros. apply Val.lessdef_binop; auto.
    + intros; simpl.
      generalize (expr_type' alloc em v Tlong); seval.
    + intros.
      exploit eval_shruimm. eexact EXPRx. intros [v1 [A1 B1]].
      exploit eval_shruimm. eexact EXPRy. intros [v2 [A2 B2]].
      exploit eval_shlimm. eexact EXPRx. intros [v3 [A3 B3]].
      exploit eval_or. eexact A2. eexact A3. intros [v4 [A4 B4]].
      econstructor; split. EvalOp. 
      unfold Val.longofwords.
      unfold Val.or in B4.
      ldt'.
      red; intros; simpl; seval; try constructor.
      destr. destr. destr.
      rewrite Int64.decompose_shru_1; auto.
  - (* 32 <= n < 64 *)
    exploit eval_highlong. eexact H. intros [v1 [A1 B1]].
    exploit eval_shruimm. eexact A1. intros [v2 [A2 B2]].
    econstructor; split. EvalOp.
    unfold Val.hiword in B1; unfold Val.shru in B2;  unfold Val.longofwords. ldt'.
    red; intros; simpl; seval; try constructor.
    destr; try constructor. destr.
    erewrite <- Int64.decompose_shru_2. instantiate (1 := Int64.loword i). 
    rewrite Int64.ofwords_recompose. auto. auto.
  - (* n >= 64 *)
    econstructor; split. eapply eval_helper_2; eauto. EvalOp. UseHelper.
    auto.
Qed.

Theorem eval_shrlu: binary_constructor_sound (shrlu hf) Val.shrlu.
Proof.
  unfold shrlu; red; intros.
  destruct (is_intconst b) as [n|] eqn:IC.
- (* Immediate *)
  exploit is_intconst_sound; eauto. intros EQ; subst y; clear H0.
  eapply eval_shrluimm; eauto.
- (* General case *)
  econstructor; split. eapply eval_helper_2; eauto. UseHelper.
  auto. 
Qed.

Lemma eval_shrlimm:
  forall n,
    unary_constructor_sound
      (fun e => shrlimm hf e n)
      (fun v => Val.shrl v (Eval (Vint n))).
Proof.
  unfold shrlimm; red; intros. apply eval_shift_imm; intros.
  - (* n = 0 *)
    subst n. exists x; split; auto.
    red; intros; simpl; seval; try constructor. 
    change (Int64.shr' i Int.zero) with (Int64.shr i Int64.zero). 
    rewrite Int64.shr_zero. auto.
  - (* 0 < n < 32 *)
    apply eval_splitlong with (sem := fun x => Val.shrl x (Eval (Vint n))); auto.
    + intros.
      eapply Val.lessdef_binop; eauto.
    + intros.
      simpl; seval. destr.
      generalize (expr_type' alloc em v Tlong); rewrite Heqv0; simpl.
      intuition congruence.
    + intros. 
      exploit eval_shrimm. eexact EXPRx. intros [v1 [A1 B1]].
      exploit eval_shruimm. eexact EXPRy. intros [v2 [A2 B2]].
      exploit eval_shlimm. eexact EXPRx. intros [v3 [A3 B3]].
      exploit eval_or. eexact A2. eexact A3. intros [v4 [A4 B4]].
      econstructor; split. EvalOp. 
      unfold Val.longofwords, Val.or in *. ldt'.
      red; intros; simpl; seval; try constructor.
      destr. destr. destr.
      rewrite Int64.decompose_shr_1; auto.
  - (* 32 <= n < 64 *) 
    exploit eval_highlong. eexact H. intros [v1 [A1 B1]].
    assert (A0: eval_expr ge sp e m (v1 :: le) (Eletvar 0) v1) by EvalOp.
    exploit eval_shrimm. eexact A0. intros [v2 [A2 B2]].
    exploit eval_shrimm. eexact A0. intros [v3 [A3 B3]].
    econstructor; split. EvalOp.
    unfold Val.longofwords, Val.hiword, Val.or, Val.shr in *. ldt'.
    red; intros; simpl; seval; try constructor.
    destr; try constructor.
    change (Int.ltu (Int.repr 31) Int.iwordsize) with true. simpl.
    destr. 
    erewrite <- Int64.decompose_shr_2. instantiate (1 := Int64.loword i). 
    rewrite Int64.ofwords_recompose. auto. auto.
  - (* n >= 64 *)
    econstructor; split. eapply eval_helper_2; eauto. EvalOp. UseHelper.
    auto.
Qed.

Theorem eval_shrl: binary_constructor_sound (shrl hf) Val.shrl.
Proof.
  unfold shrl; red; intros.
  destruct (is_intconst b) as [n|] eqn:IC.
- (* Immediate *)
  exploit is_intconst_sound; eauto. intros EQ; subst y; clear H0.
  eapply eval_shrlimm; eauto.
- (* General case *)
  econstructor; split. eapply eval_helper_2; eauto. UseHelper. auto. 
Qed.

Theorem eval_addl: binary_constructor_sound (addl hf) Val.addl.
Proof.
  unfold addl; red; intros.
  set (default := Ebuiltin (EF_builtin (i64_add hf) sig_ll_l) (a ::: b ::: Enil)).
  assert (DEFAULT:
    exists v, eval_expr ge sp e m le default v /\ Val.lessdef (Val.addl x y) v).
  {
    econstructor; split. eapply eval_builtin_2; eauto. UseHelper. auto. 
  }
  destruct (is_longconst a) as [p|] eqn:LC1;
  destruct (is_longconst b) as [q|] eqn:LC2.
  - eapply (is_longconst_sound le a) in LC1; eauto.
    eapply (is_longconst_sound le b) in LC2; eauto. 
    destruct (eval_longconst le (Int64.add p q)) as [v [C D]].
    econstructor; split. eauto.
    red; intros; simpl.
    rewrite LC1, LC2, D. simpl; auto.
- predSpec Int64.eq Int64.eq_spec p Int64.zero; auto.
  subst p.
  eapply is_longconst_sound in LC1; eauto. 
  exists y; split; auto.
  red; intros; simpl. rewrite LC1. simpl.
  destr; try constructor.  rewrite Int64.add_zero_l; auto.
- predSpec Int64.eq Int64.eq_spec q Int64.zero; auto.
  subst q. eapply (is_longconst_sound le b) in LC2; eauto. 
  exists x; split; auto.
  red; intros; simpl. rewrite LC2; simpl.
  seval; try constructor.
  rewrite Int64.add_zero; auto.
- auto.
Qed.

Theorem eval_subl: binary_constructor_sound (subl hf) Val.subl.
Proof.
  unfold subl; red; intros.
  set (default := Ebuiltin (EF_builtin (i64_sub hf) sig_ll_l) (a ::: b ::: Enil)).
  assert (DEFAULT:
    exists v, eval_expr ge sp e m le default v /\ Val.lessdef (Val.subl x y) v).
  {
    econstructor; split. eapply eval_builtin_2; eauto. UseHelper. auto. 
  }
  destruct (is_longconst a) as [p|] eqn:LC1;
  destruct (is_longconst b) as [q|] eqn:LC2.
- eapply (is_longconst_sound le a) in LC1; eauto. 
  eapply (is_longconst_sound le b) in LC2; eauto. 
  destruct (eval_longconst le (Int64.sub p q)) as [v [C D]].
  econstructor; split. eauto.
  red; intros; simpl.
  rewrite LC1, LC2, D; simpl; auto.
- predSpec Int64.eq Int64.eq_spec p Int64.zero; auto. subst.
  destruct (eval_negl _ _ _  H0) as [v [A B]].
  eexists; split. eauto. ldt.
  red; intros; simpl; seval; try constructor.
  eapply is_longconst_sound in LC1; eauto. rewrite LC1 in Heqv0; simpl in Heqv0; inv Heqv0.
  rewrite Int64.sub_zero_r. auto.
- predSpec Int64.eq Int64.eq_spec q Int64.zero; auto.
  subst q. eapply (is_longconst_sound le b) in LC2; eauto. 
  eexists; split; eauto.
  red; intros; simpl; seval; try constructor.
  rewrite LC2 in Heqv0; simpl in Heqv0; inv Heqv0. rewrite Int64.sub_zero_l; auto.
- auto.
Qed.



Lemma eval_mull_base: binary_constructor_sound (mull_base hf) Val.mull.
Proof.
  unfold mull_base; red; intros. apply eval_splitlong2; auto.
  - intros. eapply Val.lessdef_binop; eauto.
  - intros; simpl; seval; auto.
    generalize (expr_type' alloc em v Tlong); rewrite Heqv0; simpl; destr.
    generalize (expr_type' alloc em x0 Tlong); rewrite Heqv1; simpl; destr.
  - intros. 
    set (p := Val.mull' x2 y2). set (le1 := p :: le0).
    assert (E1: eval_expr ge sp e m le1 (Eop Olowlong (Eletvar O ::: Enil)) (Val.loword p)) by EvalOp.
    assert (E2: eval_expr ge sp e m le1 (Eop Ohighlong (Eletvar O ::: Enil)) (Val.hiword p)) by EvalOp.
    refine ((fun xy => _) (eval_mul ge sp e m _ _ _ _ _  (eval_lift _ _ _ _ _ _ _ p EXPRx2)
                                    (eval_lift _ _ _ _ _ _ _ p EXPRy1))).
    refine ((fun xy => _) (eval_mul ge sp e m _ _ _ _ _  (eval_lift _ _ _ _ _ _ _ p EXPRx1)
                                    (eval_lift _ _ _ _ _ _ _ p EXPRy2))).
    fold le1 in xy, xy0.
    destruct xy as [v3 [E3 L3]].
    destruct xy0 as [v4 [E4 L4]].
    exploit eval_add. eexact E2. eexact E3. intros [v5 [E5 L5]].
    exploit eval_add. eexact E5. eexact E4. intros [v6 [E6 L6]].
    exists (Val.longofwords v6 (Val.loword p)); split.
    EvalOp. eapply eval_builtin_2; eauto. UseHelper.
    clear E1 E2 E3 E4 E5 E6 EXPRx1 EXPRx2 EXPRy1 EXPRy2 H H0. unfold p in *.
    unfold Val.longofwords, Val.loword, Val.mull', Val.add, Val.hiword in *.
    ldt'.
    clear.
    red; intros; simpl; seval; try constructor.
    rewrite Int64.decompose_mul.  auto.
Qed.

Lemma eval_mullimm:
  forall n, unary_constructor_sound 
              (fun a => mullimm hf a n)
              (fun v => Val.mull v (Eval (Vlong n))).
Proof.
  unfold mullimm; red; intros.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
  - subst n.
    destruct (eval_longconst le Int64.zero) as [v [A B]].
    eexists; split; eauto.
    red; intros; simpl. rewrite B; seval; try constructor.
    rewrite Int64.mul_zero. auto.
  - predSpec Int64.eq Int64.eq_spec n Int64.one.
    + subst n. exists x; split; auto. 
      red; intros; simpl; seval; try constructor.
      rewrite Int64.mul_one. auto.
    + destruct (Int64.is_power2 n) as [l|] eqn:P2. 
      * exploit eval_shllimm. eexact H. intros [v [A B]].
        exists v; split; auto.  eauto. ldt.
        red; intros; simpl; seval; try constructor. 
        assert (EQ: Int.unsigned (Int.repr (Int64.unsigned l)) = Int64.unsigned l).
        { apply Int.unsigned_repr.
          exploit Int64.is_power2_rng; eauto.
          assert (Int64.zwordsize < Int.max_unsigned) by (compute; auto). 
          omega.
        }
        replace (Int.ltu (Int.repr (Int64.unsigned l)) Int64.iwordsize')
        with (Int64.ltu l Int64.iwordsize).
        erewrite Int64.is_power2_range by eauto. 
        erewrite Int64.mul_pow2 by eauto.
        unfold Int64.shl' . rewrite EQ. simpl. auto.
        unfold Int64.ltu, Int.ltu. rewrite EQ. auto.
      * destruct (eval_longconst le n) as [v [A B]].
        destruct (eval_mull_base _ _ _ _ _  H A) as [v2 [C D]]; auto. 
        eexists; split; eauto.
        ldt. apply Val.lessdef_binop; auto.
        red; intros; simpl; rewrite B. simpl; auto. 
Qed.

Theorem eval_mull: binary_constructor_sound (mull hf) Val.mull.
Proof.
  unfold mull; red; intros.
  destruct (is_longconst a) as [p|] eqn:LC1;
  destruct (is_longconst b) as [q|] eqn:LC2.
- eapply (is_longconst_sound le a) in LC1; eauto.
  eapply (is_longconst_sound le b) in LC2; eauto.
  destruct (eval_longconst le (Int64.mul p q)) as [v [C D]].
  eexists; split; eauto. 
  red; intros; simpl. rewrite LC1, LC2, D. simpl; auto.
- eapply (is_longconst_sound le a) in LC1; eauto. 
  destruct (eval_mullimm p _ _ _ H0) as [v [B C]].
  eexists; split. eauto. ldt. red; intros; simpl. rewrite LC1. simpl.
  seval; try constructor.  rewrite Int64.mul_commut; auto.
- eapply (is_longconst_sound le b) in LC2; eauto. 
  destruct (eval_mullimm q _ _ _ H) as [v [B C]]; eauto.
  eexists; split; eauto. ldt. apply Val.lessdef_binop; auto.
  apply se_ld; auto. 
- apply eval_mull_base; auto.
Qed.

Lemma eval_binop_long:
  forall id sem le a b x y z,
    (forall p q, Val.lessdef x (Eval (Vlong p)) ->
                 Val.lessdef y (Eval (Vlong q)) ->
                 Val.lessdef z (Eval (Vlong (sem p q)))) ->
    helper_implements ge id sig_ll_l (x::y::nil) z ->
    eval_expr ge sp e m le a x ->
    eval_expr ge sp e m le b y ->
    exists v, eval_expr ge sp e m le (binop_long id sem a b) v /\ Val.lessdef z v.
Proof.
  intros. unfold binop_long. 
  destruct (is_longconst a) as [p|] eqn:LC1. 
  destruct (is_longconst b) as [q|] eqn:LC2.
  - eapply is_longconst_sound in LC1; eauto.
    eapply is_longconst_sound in LC2; eauto. 
    econstructor; split. EvalOp. red; intros; simpl. rewrite Int64.ofwords_recompose.
    apply H; red; intros; simpl.
    rewrite LC1; auto. rewrite LC2; auto.
  - econstructor; split. eapply eval_helper_2; eauto. auto.
  - econstructor; split. eapply eval_helper_2; eauto. auto.
Qed.

Theorem eval_divl:
  binary_constructor_sound (divl hf) Val.divls.
Proof.
  red; intros. unfold divl.
  eapply eval_binop_long; eauto. 
  red; intros; simpl; seval; try constructor.
  destr; try constructor.
  specialize (H1 alloc em). rewrite Heqv in H1.
  specialize (H2 alloc em). rewrite Heqv0 in H2. simpl in *.
  inv H1. inv H2. auto.
  UseHelper. 
Qed.

Theorem eval_modl:
  binary_constructor_sound (modl hf) Val.modls.
Proof.
  red; intros. eapply eval_binop_long; eauto.
  red; intros; simpl; seval; try constructor.
  destr; try constructor.
  specialize (H1 alloc em). rewrite Heqv in H1.
  specialize (H2 alloc em). rewrite Heqv0 in H2. simpl in *.
  inv H1. inv H2. auto.
  UseHelper. 
Qed.

Theorem eval_divlu:
  binary_constructor_sound (divlu hf) Val.divlu.
Proof.
  red; intros. unfold divlu. 
  set (default := Eexternal (i64_udiv hf) sig_ll_l (a ::: b ::: Enil)).
  assert (DEFAULT:
    exists v, eval_expr ge sp e m le default v /\ Val.lessdef (Val.divlu x y) v).
  {
    econstructor; split. eapply eval_helper_2; eauto. UseHelper. auto.
  }
  destruct (is_longconst a) as [p|] eqn:LC1;
  destruct (is_longconst b) as [q|] eqn:LC2.
  - eapply is_longconst_sound in LC1; eauto.
    eapply is_longconst_sound in LC2; eauto. 
    destruct (eval_longconst le (Int64.divu p q)) as [v [C D]].
    eexists; split; eauto. red; intros; simpl. rewrite D, LC1, LC2. 
    simpl. destr; auto. 
  - auto.
  - destruct (Int64.is_power2 q) as [l|] eqn:P2; auto.
    eapply is_longconst_sound in LC2; eauto. 
    exploit eval_shrluimm. eexact H. intros [v [B C]].
    eexists; split; eauto. ldt. red; intros; simpl; seval; try constructor.
    destr; auto. rewrite LC2 in Heqv1; inv Heqv1.
    assert (EQ: Int.unsigned (Int.repr (Int64.unsigned l)) = Int64.unsigned l).
    { apply Int.unsigned_repr.
      exploit Int64.is_power2_rng; eauto.
      assert (Int64.zwordsize < Int.max_unsigned) by (compute; auto). 
      omega.
    }
    replace (Int.ltu (Int.repr (Int64.unsigned l)) Int64.iwordsize')
    with (Int64.ltu l Int64.iwordsize).
    erewrite Int64.is_power2_range by eauto.
    simpl. erewrite Int64.divu_pow2 by eauto. 
    unfold Int64.shru', Int64.shru. rewrite EQ. auto. 
    unfold Int64.ltu, Int.ltu. rewrite EQ. auto.
  - auto.
Qed.

Theorem eval_modlu:
  binary_constructor_sound (modlu hf) Val.modlu.
Proof.
  red; intros. unfold modlu. 
  set (default := Eexternal (i64_umod hf) sig_ll_l (a ::: b ::: Enil)).
  assert (DEFAULT:
    exists v, eval_expr ge sp e m le default v /\ Val.lessdef (Val.modlu x y) v).
  {
    econstructor; split. eapply eval_helper_2; eauto. UseHelper.
    auto.
  }
  destruct (is_longconst a) as [p|] eqn:LC1;
    destruct (is_longconst b) as [q|] eqn:LC2.
  - eapply is_longconst_sound in LC1; eauto.
    eapply is_longconst_sound in LC2; eauto. 
    destruct (eval_longconst le (Int64.modu p q)) as [v [C D]].
    econstructor; split. eauto. red; intros; simpl.
    rewrite  LC1, LC2, D. simpl. 
    destr; auto.
  - auto.
  - destruct (Int64.is_power2 q) as [l|] eqn:P2; auto.
    eapply is_longconst_sound in LC2; eauto.
    destruct (eval_longconst le (Int64.sub q Int64.one)) as [v [B C]].
    exploit eval_andl. eexact H. eexact B. intros [v2 [D E]].
    eexists; split; eauto. ldt.
    red; intros; simpl. rewrite C. rewrite LC2. simpl. seval; try constructor.
    erewrite Int64.modu_and; eauto.
    destr; auto.
  - auto.
Qed.


Lemma eval_cmpl_eq_zero':
  unary_constructor_sound (cmpl_eq_zero) (fun x => Val.cmpl Ceq x (Eval (Vlong Int64.zero))).
Proof.
  red; intros. unfold cmpl_eq_zero.
  eapply eval_splitlong_strict. eauto.
  intros le0 a1 a2 [v1 [A1 B1]] [v2 [A2 B2]].
  exploit eval_or. eexact A1. eexact A2. intros [v3 [A3 B3]].
  assert (A0: eval_expr ge sp e m le0 (Eop (Ointconst Int.zero) Enil) (Eval (Vint Int.zero))) by EvalOp.
  exploit eval_comp. eexact A3. eexact A0.  intros [x1 [A B]].
  eexists; split; eauto. ldt.
  unfold Val.cmp, Val.cmp_bool, Val.or in *. ldt'.
  red; intros; simpl; seval; auto.
  rewrite <- decompose_cmpl_eq_zero.
  rewrite Int64.ofwords_recompose.
  destr; auto.
Qed.

Lemma eval_cmpl_ne_zero':
  unary_constructor_sound cmpl_ne_zero (fun x => Val.cmpl Cne x (Eval (Vlong Int64.zero))).
Proof.
  red; intros. unfold cmpl_ne_zero.
  eapply eval_splitlong_strict. eauto.
  intros le0 a1 a2 [v1 [A1 B1]] [v2 [A2 B2]].
  exploit eval_or. eexact A1. eexact A2. intros [v3 [A3 B3]].
  assert (A0: eval_expr ge sp e m le0 (Eop (Ointconst Int.zero) Enil) (Eval (Vint Int.zero))) by EvalOp.
  exploit eval_comp. eexact A3. eexact A0.  intros [x1 [A B]].
  eexists; split; eauto. ldt.
  unfold Val.cmp, Val.cmp_bool, Val.or in *. ldt'.
  red; intros; simpl; seval; auto.
  rewrite <- decompose_cmpl_eq_zero.
  rewrite Int64.ofwords_recompose. auto.
Qed.

Lemma eval_cmplu_gen':
  forall ch cl,
    binary_constructor_sound
      (cmplu_gen ch cl)
      (fun va vb =>
         (Val.add
            (Val.mul
               (Val.cmp Ceq (Val.hiword va) (Val.hiword vb))
               (Val.cmpu cl (Val.loword va) (Val.loword vb)))
            (Val.mul
               (Val.cmp Cne (Val.hiword va) (Val.hiword vb))
               (Val.cmpu ch (Val.hiword va) (Val.hiword vb))))).
Proof.
  red; intros. unfold cmplu_gen.
  eapply eval_splitlong2_strict. eexact H. eexact H0.
  intros le0 a1 a2 b1 b2 [v1 [A1 B1]] [v2 [A2 B2]] [v3 [A3 B3]] [v4 [A4 B4]].
  econstructor. split. repeat (econstructor; simpl; eauto).
  clear H H0 A1 A2 A3 A4. 
  unfold Val.add, Val.mul, Val.cmp, Val.cmpu, Val.cmp_bool, Val.cmpu_bool.
  ldt'.
  red; intros. simpl.
  seval; auto.
  repeat destr_no_dep; auto; try rewrite Int.add_zero; auto.
Qed.


Theorem eval_cmplu:
  forall c, binary_constructor_sound (cmplu c) (Val.cmplu c).
Proof.
  red; intros. unfold Val.cmplu, Val.cmplu_bool.
  destruct c; simpl.
- (* Ceq *)
  exploit eval_xorl. eexact H. eexact H0. intros [v1 [A B]]. 
  exploit eval_cmpl_eq_zero'. eexact A. intros [v2 [C D]].
  eexists; split; eauto. ldt.
  unfold Val.cmpl, Val.cmpl_bool. ldt'.
  red; intros; simpl; seval; auto. 
  rewrite int64_eq_xor. auto. 
- (* Cne *)
  exploit eval_xorl. eexact H. eexact H0.
  intros [v1 [A B]].
  exploit eval_cmpl_ne_zero'. eexact A.  intros [v2 [A2 B2]].
  eexists; split; eauto. ldt. unfold Val.cmpl, Val.cmpl_bool. ldt'.
  red; intros; simpl; seval; auto.
  rewrite int64_eq_xor. auto. 
- (* Clt *)
  exploit (eval_cmplu_gen' Clt Clt). eexact H. eexact H0.  
  intros [v [A B]]; eexists; split; eauto. ldt.
  clear.
  red; intros; simpl; seval; auto.
  rewrite int64_ltu_rew. rewrite Int64.decompose_ltu.
  repeat destr_no_dep; auto; clear_useless;
  try discriminate;
  generalize (expr_nu_type _ _ _ Tlong _ Heqv);
  generalize (expr_nu_type _ _ _ Tlong _ Heqv0); destr.
- (* Cle *)
  exploit (eval_cmplu_gen' Clt Cle). eexact H. eexact H0.  
  intros [v [A B]]; eexists; split; eauto.
  ldt. clear.
  red; intros; simpl; seval; auto.
  rewrite int64_ltu_rew. rewrite Int64.decompose_leu.
  repeat destr_no_dep; auto; clear_useless;
  try discriminate;
  generalize (expr_nu_type _ _ _ Tlong _ Heqv);
  generalize (expr_nu_type _ _ _ Tlong _ Heqv0); destr.

- (* Cgt *)
  exploit (eval_cmplu_gen' Cgt Cgt). eexact H. eexact H0.  
  intros [v [A B]]; eexists; split; eauto.
  ldt; clear.
  red; intros; simpl; seval; auto.
  rewrite int64_ltu_rew. rewrite Int64.decompose_ltu.
  rewrite Int.eq_sym.
  repeat destr_no_dep; auto; clear_useless;
  try discriminate;
  generalize (expr_nu_type _ _ _ Tlong _ Heqv);
  generalize (expr_nu_type _ _ _ Tlong _ Heqv0); destr.

- (* Cge *)
  exploit (eval_cmplu_gen' Cgt Cge). eexact H. eexact H0.
  intros [v [A B]]; eexists; split; eauto.
  ldt; clear.   red; intros; simpl; seval; auto.
  rewrite int64_ltu_rew. rewrite Int64.decompose_leu.
  rewrite Int.eq_sym.
  repeat destr_no_dep; auto; clear_useless;
  try discriminate;
  generalize (expr_nu_type _ _ _ Tlong _ Heqv);
  generalize (expr_nu_type _ _ _ Tlong _ Heqv0); destr.
Qed.

Lemma eval_cmpl_gen':
  forall ch cl,
    binary_constructor_sound
      (cmpl_gen ch cl)
      (fun va vb =>
         (Val.add
            (Val.mul
               (Val.cmp Ceq (Val.hiword va) (Val.hiword vb))
               (Val.cmpu cl (Val.loword va) (Val.loword vb)))
            (Val.mul
               (Val.cmp Cne (Val.hiword va) (Val.hiword vb))
               (Val.cmp ch (Val.hiword va) (Val.hiword vb))))).
Proof.
  red; intros. unfold cmpl_gen.
  eapply eval_splitlong2_strict.
  eexact H. eexact H0.
  intros le0 a1 a2 b1 b2 [v1 [A1 B1]] [v2 [A2 B2]] [v3 [A3 B3]] [v4 [A4 B4]].
  econstructor. split. repeat (econstructor; simpl; eauto).
  clear H H0 A1 A2 A3 A4.
  unfold Val.add, Val.mul, Val.cmp, Val.cmpu, Val.cmp_bool, Val.cmpu_bool.
  ldt'.
  red; intros. simpl.
  seval; auto.
  repeat destr_no_dep; auto; try rewrite Int.add_zero; auto.
Qed.

Theorem eval_cmpl:
  forall c,
    binary_constructor_sound (cmpl c) (Val.cmpl c). 
Proof.
  red; intros. unfold Val.cmpl, Val.cmpl_bool.
  destruct c; simpl.
- (* Ceq *)
  exploit eval_xorl. eexact H. eexact H0.  intros [v1 [A B]].
  exploit eval_cmpl_eq_zero'. eexact A.  intros [v2 [C D]].
  eexists; split; eauto. ldt. unfold Val.cmpl, Val.cmpl_bool. ldt'. clear.
  red; intros; simpl; seval; auto.
  rewrite int64_eq_xor. auto. 
- (* Cne *)
  exploit eval_xorl. eexact H. eexact H0.  intros [v1 [A B]].
  exploit eval_cmpl_ne_zero'. eexact A. intros [v2 [C D]].
  eexists; split; eauto. ldt. unfold Val.cmpl, Val.cmpl_bool. ldt'. clear.
  red; intros; simpl; seval; auto.
  rewrite int64_eq_xor. auto.
- (* Clt *) 
  destruct (is_longconst_zero b) eqn:LC.
  +
    assert (exists v, eval_expr ge sp e m le (Eop (Ointconst Int.zero) Enil) v /\
                      Val.lessdef (Eval (Vint Int.zero)) v).
    {
      eexists; split. EvalOp. auto. 
    } destruct H1 as [v [ A B]].
        exploit eval_highlong. eexact H. intros [v1 [A1 B1]]. 
    exploit eval_comp. eexact A1. eexact A. 
    instantiate (1 := Clt). intros [v2 [A2 B2]].
    eexists; split; eauto. ldt. unfold Val.cmp, Val.cmp_bool.
    ldt'.
    red; intros; simpl.
    erewrite (is_longconst_zero_sound le b y); eauto.
    seval; auto.
    erewrite <- decompose_cmpl_lt_zero.
    rewrite  (Int64.ofwords_recompose). auto. 
  + exploit (eval_cmpl_gen' Clt Clt). eexact H.  eexact H0. 
    intros [v [A B]]. eexists; split; eauto. ldt. clear.
    red; intros; simpl; seval; auto.
    rewrite int64_lt_rew. rewrite Int64.decompose_lt.
    repeat destr_no_dep; auto; clear_useless;
    try discriminate;
    generalize (expr_nu_type _ _ _ Tlong _ Heqv);
    generalize (expr_nu_type _ _ _ Tlong _ Heqv0); destr.
- (* Cle *)
  exploit (eval_cmpl_gen' Clt Cle). eexact H. eexact H0. 
  intros [v [A B]]. eexists; split; eauto.
  ldt. clear.
  red; intros; simpl; seval; auto.
  rewrite int64_lt_rew. rewrite Int64.decompose_le.
  repeat destr_no_dep; auto; clear_useless;
  try discriminate;
  generalize (expr_nu_type _ _ _ Tlong _ Heqv);
  generalize (expr_nu_type _ _ _ Tlong _ Heqv0); destr.
- (* Cgt *)
  exploit (eval_cmpl_gen' Cgt Cgt). eexact H.  eexact H0. 
  intros [v [A B]]. eexists; split; eauto. ldt. clear.
  red; intros; simpl; seval; auto.
  rewrite int64_lt_rew. rewrite Int64.decompose_lt. rewrite Int.eq_sym.
  repeat destr_no_dep; auto; clear_useless;
  try discriminate;
  generalize (expr_nu_type _ _ _ Tlong _ Heqv);
  generalize (expr_nu_type _ _ _ Tlong _ Heqv0); destr. 
- (* Cge *)
  destruct (is_longconst_zero b) eqn:LC.
  + assert (exists v, eval_expr ge sp e m le (Eop (Ointconst Int.zero) Enil) v /\
                      Val.lessdef (Eval (Vint Int.zero)) v).
    {
      eexists; split. EvalOp. auto. 
    } destruct H1 as [v [ A B]].
    exploit eval_highlong. eexact H.  intros [v1 [A1 B1]]. 
    exploit eval_comp. eexact A1. eexact A. 
    instantiate (1 := Cge). intros [v2 [A2 B2]].
    eexists; split; eauto. ldt. unfold Val.cmp, Val.cmp_bool. ldt'.
    red; intros; simpl.
    rewrite (is_longconst_zero_sound le b y); auto.
    simpl. seval; auto.
    erewrite <- decompose_cmpl_lt_zero.
    rewrite  (Int64.ofwords_recompose). auto. 
  + exploit (eval_cmpl_gen' Cgt Cge). eexact H. eexact H0. 
    intros [v [A B]]. eexists; split; eauto. ldt. clear.
    red; intros; simpl; seval; auto.
    rewrite int64_lt_rew. rewrite Int64.decompose_le. rewrite Int.eq_sym.
    repeat destr_no_dep; auto; clear_useless;
    try discriminate;
    generalize (expr_nu_type _ _ _ Tlong _ Heqv);
    generalize (expr_nu_type _ _ _ Tlong _ Heqv0); destr. 
Qed.

End CMCONSTR.

