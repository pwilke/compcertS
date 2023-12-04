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
Require Import Zquot.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import NormaliseSpec.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.
Require Import SelectOpproof.
Require Import SelectDiv.
Require Import Values_symbolictype.
Require Import Values_symbolic.
Require Import IntFacts.
Open Local Scope cminorsel_scope.

(** * Main approximation theorems *)

Section Z_DIV_MUL.

Variable N: Z.      (**r number of relevant bits *)
Hypothesis N_pos: N >= 0.
Variable d: Z.      (**r divisor *)
Hypothesis d_pos: d > 0.

(** This is theorem 4.2 from Granlund and Montgomery, PLDI 1994. *)

Lemma Zdiv_mul_pos:
  forall m l,
  l >= 0 ->
  two_p (N+l) <= m * d <= two_p (N+l) + two_p l ->
  forall n,
  0 <= n < two_p N ->
  Zdiv n d = Zdiv (m * n) (two_p (N + l)).
Proof.
  intros m l l_pos [LO HI] n RANGE.
  exploit (Z_div_mod_eq n d). auto. 
  set (q := n / d).
  set (r := n mod d).
  intro EUCL.
  assert (0 <= r <= d - 1).
    unfold r. generalize (Z_mod_lt n d d_pos). omega.
  assert (0 <= m). 
    apply Zmult_le_0_reg_r with d. auto.
    exploit (two_p_gt_ZERO (N + l)). omega. omega. 
  set (k := m * d - two_p (N + l)).
  assert (0 <= k <= two_p l). 
    unfold k; omega.
  assert ((m * n - two_p (N + l) * q) * d = k * n + two_p (N + l) * r).
    unfold k. rewrite EUCL. ring.
  assert (0 <= k * n).
    apply Zmult_le_0_compat; omega.
  assert (k * n <= two_p (N + l) - two_p l).
    apply Zle_trans with (two_p l * n).
    apply Zmult_le_compat_r. omega. omega.
    replace (N + l) with (l + N) by omega.
    rewrite two_p_is_exp. 
    replace (two_p l * two_p N - two_p l)
       with (two_p l * (two_p N - 1))
         by ring.
    apply Zmult_le_compat_l. omega. exploit (two_p_gt_ZERO l). omega. omega.
    omega. omega.
  assert (0 <= two_p (N + l) * r).
    apply Zmult_le_0_compat. 
    exploit (two_p_gt_ZERO (N + l)). omega. omega.
    omega.
  assert (two_p (N + l) * r <= two_p (N + l) * d - two_p (N + l)).
    replace (two_p (N + l) * d - two_p (N + l))
       with (two_p (N + l) * (d - 1)) by ring.
    apply Zmult_le_compat_l.
    omega.
    exploit (two_p_gt_ZERO (N + l)). omega. omega.
  assert (0 <= m * n - two_p (N + l) * q).
    apply Zmult_le_reg_r with d. auto. 
    replace (0 * d) with 0 by ring.  rewrite H2. omega. 
  assert (m * n - two_p (N + l) * q < two_p (N + l)).
    apply Zmult_lt_reg_r with d. omega.
    rewrite H2. 
    apply Zle_lt_trans with (two_p (N + l) * d - two_p l).
    omega. 
    exploit (two_p_gt_ZERO l). omega. omega.
  symmetry. apply Zdiv_unique with (m * n - two_p (N + l) * q). 
  ring. omega.
Qed.

Lemma Zdiv_unique_2:
  forall x y q, y > 0 -> 0 < y * q - x <= y -> Zdiv x y = q - 1.
Proof.
  intros. apply Zdiv_unique with (x - (q - 1) * y). ring. 
  replace ((q - 1) * y) with (y * q - y) by ring. omega. 
Qed.

Lemma Zdiv_mul_opp:
  forall m l,
  l >= 0 ->
  two_p (N+l) < m * d <= two_p (N+l) + two_p l ->
  forall n,
  0 < n <= two_p N ->
  Zdiv n d = - Zdiv (m * (-n)) (two_p (N + l)) - 1.
Proof.
  intros m l l_pos [LO HI] n RANGE.
  replace (m * (-n)) with (- (m * n)) by ring.
  exploit (Z_div_mod_eq n d). auto. 
  set (q := n / d).
  set (r := n mod d).
  intro EUCL.
  assert (0 <= r <= d - 1).
    unfold r. generalize (Z_mod_lt n d d_pos). omega.
  assert (0 <= m). 
    apply Zmult_le_0_reg_r with d. auto.
    exploit (two_p_gt_ZERO (N + l)). omega. omega.
  cut (Zdiv (- (m * n)) (two_p (N + l)) = -q - 1).
    omega.
  apply Zdiv_unique_2. 
  apply two_p_gt_ZERO. omega.
  replace (two_p (N + l) * - q - - (m * n))
     with (m * n - two_p (N + l) * q)
       by ring.
  set (k := m * d - two_p (N + l)).
  assert (0 < k <= two_p l). 
    unfold k; omega.
  assert ((m * n - two_p (N + l) * q) * d = k * n + two_p (N + l) * r).
    unfold k. rewrite EUCL. ring.
  split.
  apply Zmult_lt_reg_r with d. omega. 
  replace (0 * d) with 0 by omega.
  rewrite H2.
  assert (0 < k * n). apply Zmult_lt_0_compat; omega.
  assert (0 <= two_p (N + l) * r).
    apply Zmult_le_0_compat. exploit (two_p_gt_ZERO (N + l)); omega. omega.
  omega.
  apply Zmult_le_reg_r with d. omega.
  rewrite H2. 
  assert (k * n <= two_p (N + l)).
    rewrite Zplus_comm. rewrite two_p_is_exp; try omega. 
    apply Zle_trans with (two_p l * n). apply Zmult_le_compat_r. omega. omega. 
    apply Zmult_le_compat_l. omega. exploit (two_p_gt_ZERO l). omega. omega.
  assert (two_p (N + l) * r <= two_p (N + l) * d - two_p (N + l)).
    replace (two_p (N + l) * d - two_p (N + l))
       with (two_p (N + l) * (d - 1))
         by ring.
    apply Zmult_le_compat_l. omega. exploit (two_p_gt_ZERO (N + l)). omega. omega.
  omega.
Qed.

(** This is theorem 5.1 from Granlund and Montgomery, PLDI 1994. *)

Lemma Zquot_mul:
  forall m l,
  l >= 0 ->
  two_p (N+l) < m * d <= two_p (N+l) + two_p l ->
  forall n,
  - two_p N <= n < two_p N ->
  Z.quot n d = Zdiv (m * n) (two_p (N + l)) + (if zlt n 0 then 1 else 0).
Proof.
  intros. destruct (zlt n 0).
  exploit (Zdiv_mul_opp m l H H0 (-n)). omega. 
  replace (- - n) with n by ring.
  replace (Z.quot n d) with (- Z.quot (-n) d).
  rewrite Zquot_Zdiv_pos by omega. omega.
  rewrite Z.quot_opp_l by omega. ring.
  rewrite Zplus_0_r. rewrite Zquot_Zdiv_pos by omega. 
  apply Zdiv_mul_pos; omega.
Qed.

End Z_DIV_MUL.

(** * Correctness of the division parameters *)

Lemma divs_mul_params_sound:
  forall d m p,
  divs_mul_params d = Some(p, m) ->
  0 <= m < Int.modulus /\ 0 <= p < 32 /\
  forall n,
  Int.min_signed <= n <= Int.max_signed ->
  Z.quot n d = Zdiv (m * n) (two_p (32 + p)) + (if zlt n 0 then 1 else 0).
Proof with (try discriminate).
  unfold divs_mul_params; intros d m' p' EQ.
  destruct (find_div_mul_params Int.wordsize
               (Int.half_modulus - Int.half_modulus mod d - 1) d 32)
  as [[p m] | ]...
  destruct (zlt 0 d)...
  destruct (zlt (two_p (32 + p)) (m * d))...
  destruct (zle (m * d) (two_p (32 + p) + two_p (p + 1)))...
  destruct (zle 0 m)...
  destruct (zlt m Int.modulus)...
  destruct (zle 0 p)...
  destruct (zlt p 32)...
  simpl in EQ. inv EQ. 
  split. auto. split. auto. intros. 
  replace (32 + p') with (31 + (p' + 1)) by omega. 
  apply Zquot_mul; try omega.
  replace (31 + (p' + 1)) with (32 + p') by omega. omega.
  change (Int.min_signed <= n < Int.half_modulus). 
  unfold Int.max_signed in H. omega. 
Qed.

Lemma divu_mul_params_sound:
  forall d m p,
  divu_mul_params d = Some(p, m) ->
  0 <= m < Int.modulus /\ 0 <= p < 32 /\
  forall n,
  0 <= n < Int.modulus ->
  Zdiv n d = Zdiv (m * n) (two_p (32 + p)).
Proof with (try discriminate).
  unfold divu_mul_params; intros d m' p' EQ.
  destruct (find_div_mul_params Int.wordsize
               (Int.modulus - Int.modulus mod d - 1) d 32)
  as [[p m] | ]...
  destruct (zlt 0 d)...
  destruct (zle (two_p (32 + p)) (m * d))...
  destruct (zle (m * d) (two_p (32 + p) + two_p p))...
  destruct (zle 0 m)...
  destruct (zlt m Int.modulus)...
  destruct (zle 0 p)...
  destruct (zlt p 32)...
  simpl in EQ. inv EQ. 
  split. auto. split. auto. intros.
  apply Zdiv_mul_pos; try omega. assumption.
Qed.

Lemma divs_mul_shift_gen:
  forall x y m p,
  divs_mul_params (Int.signed y) = Some(p, m) ->
  0 <= m < Int.modulus /\ 0 <= p < 32 /\
  Int.divs x y = Int.add (Int.shr (Int.repr ((Int.signed x * m) / Int.modulus)) (Int.repr p))
                         (Int.shru x (Int.repr 31)).
Proof.
  intros. set (n := Int.signed x). set (d := Int.signed y) in *.
  exploit divs_mul_params_sound; eauto. intros (A & B & C).
  split. auto. split. auto.
  unfold Int.divs. fold n; fold d. rewrite C by (apply Int.signed_range). 
  rewrite two_p_is_exp by omega. rewrite <- Zdiv_Zdiv. 
  rewrite Int.shru_lt_zero. unfold Int.add. apply Int.eqm_samerepr. apply Int.eqm_add.
  rewrite Int.shr_div_two_p. apply Int.eqm_unsigned_repr_r. apply Int.eqm_refl2. 
  rewrite Int.unsigned_repr. f_equal.
  rewrite Int.signed_repr. rewrite Int.modulus_power. f_equal. ring.
  cut (Int.min_signed <= n * m / Int.modulus < Int.half_modulus). 
  unfold Int.max_signed; omega. 
  apply Zdiv_interval_1. generalize Int.min_signed_neg; omega. apply Int.half_modulus_pos. 
  apply Int.modulus_pos.
  split. apply Zle_trans with (Int.min_signed * m). apply Zmult_le_compat_l_neg. omega. generalize Int.min_signed_neg; omega.
  apply Zmult_le_compat_r. unfold n; generalize (Int.signed_range x); tauto. tauto.
  apply Zle_lt_trans with (Int.half_modulus * m). 
  apply Zmult_le_compat_r. generalize (Int.signed_range x); unfold n, Int.max_signed; omega. tauto.
  apply Zmult_lt_compat_l. generalize Int.half_modulus_pos; omega. tauto. 
  assert (32 < Int.max_unsigned) by (compute; auto). omega.
  unfold Int.lt; fold n. rewrite Int.signed_zero. destruct (zlt n 0); apply Int.eqm_unsigned_repr. 
  apply two_p_gt_ZERO. omega.
  apply two_p_gt_ZERO. omega.
Qed.

Theorem divs_mul_shift_1:
  forall x y m p,
  divs_mul_params (Int.signed y) = Some(p, m) ->
  m < Int.half_modulus ->
  0 <= p < 32 /\
  Int.divs x y = Int.add (Int.shr (Int.mulhs x (Int.repr m)) (Int.repr p))
                         (Int.shru x (Int.repr 31)).
Proof.
  intros. exploit divs_mul_shift_gen; eauto. instantiate (1 := x). 
  intros (A & B & C). split. auto. rewrite C. 
  unfold Int.mulhs. rewrite Int.signed_repr. auto.
  generalize Int.min_signed_neg; unfold Int.max_signed; omega.
Qed.

Theorem divs_mul_shift_2:
  forall x y m p,
  divs_mul_params (Int.signed y) = Some(p, m) ->
  m >= Int.half_modulus ->
  0 <= p < 32 /\
  Int.divs x y = Int.add (Int.shr (Int.add (Int.mulhs x (Int.repr m)) x) (Int.repr p))
                         (Int.shru x (Int.repr 31)).
Proof.
  intros. exploit divs_mul_shift_gen; eauto. instantiate (1 := x). 
  intros (A & B & C). split. auto. rewrite C. f_equal. f_equal.
  rewrite Int.add_signed. unfold Int.mulhs. set (n := Int.signed x).
  transitivity (Int.repr (n * (m - Int.modulus) / Int.modulus + n)).
  f_equal. 
  replace (n * (m - Int.modulus)) with (n * m +  (-n) * Int.modulus) by ring.
  rewrite Z_div_plus. ring. apply Int.modulus_pos. 
  apply Int.eqm_samerepr. apply Int.eqm_add; auto with ints. 
  apply Int.eqm_sym. eapply Int.eqm_trans. apply Int.eqm_signed_unsigned. 
  apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl2. f_equal. f_equal. 
  rewrite Int.signed_repr_eq. rewrite Zmod_small by assumption. 
  apply zlt_false. omega.
Qed.

Theorem divu_mul_shift:
  forall x y m p,
  divu_mul_params (Int.unsigned y) = Some(p, m) ->
  0 <= p < 32 /\
  Int.divu x y = Int.shru (Int.mulhu x (Int.repr m)) (Int.repr p).
Proof.
  intros. exploit divu_mul_params_sound; eauto. intros (A & B & C).
  split. auto. 
  rewrite Int.shru_div_two_p. rewrite Int.unsigned_repr. 
  unfold Int.divu, Int.mulhu. f_equal. rewrite C by apply Int.unsigned_range.
  rewrite two_p_is_exp by omega. rewrite <- Zdiv_Zdiv by (apply two_p_gt_ZERO; omega).
  f_equal. rewrite (Int.unsigned_repr m). 
  rewrite Int.unsigned_repr. f_equal. ring.
  cut (0 <= Int.unsigned x * m / Int.modulus < Int.modulus).
  unfold Int.max_unsigned; omega.
  apply Zdiv_interval_1. omega. compute; auto. compute; auto.
  split. simpl. apply Z.mul_nonneg_nonneg. generalize (Int.unsigned_range x); omega. omega. 
  apply Zle_lt_trans with (Int.modulus * m).
  apply Zmult_le_compat_r. generalize (Int.unsigned_range x); omega. omega. 
  apply Zmult_lt_compat_l. compute; auto. omega. 
  unfold Int.max_unsigned; omega.
  assert (32 < Int.max_unsigned) by (compute; auto). omega.
Qed.

(** * Correctness of the smart constructors for division and modulus *)

Section CMCONSTRS.

Variable ge: genv.
Variable sp: expr_sym.
Variable e: env.
Variable m: mem.


(* Lemma eval_divu_mul: *)
(*   forall le x y p M, *)
(*   divu_mul_params (Int.unsigned y) = Some(p, M) -> *)
(*   nth_error le O = Some x -> *)
(*   exists v, *)
(*     eval_expr ge sp e m le (divu_mul p M) v /\ *)
(*     same_eval v (Val.divu x (Eval (Vint y))). *)
(* Proof. *)
(*   intros. unfold divu_mul.  *)
(*   assert (exists v, *)
(*             eval_expr ge sp e m le *)
(*                       (Eop Omulhu (Eletvar 0 ::: Eop (Ointconst (Int.repr M)) Enil ::: Enil)) v *)
(*                       /\ same_eval v (Val.mulhu x (Eval (Vint (Int.repr M))))). *)
(*   { eexists; split. *)
(*     EvalOp. econstructor. econstructor; eauto. econstructor. EvalOp. simpl; reflexivity. constructor. *)
(*     simpl. eauto. reflexivity. } *)
(*   destruct H1 as [vv [C D]]. *)
(*   exploit eval_shruimm. eexact C.  *)
(*   instantiate (1 := Int.repr p).  *)
(*   intros [v [P Q]]. *)
(*   eexists; split. eauto. *)
(*   constructor; simpl; intros. *)
(*   specialize (Q alloc em). simpl in Q. *)
(*   inv D. rewrite se_eval in Q. simpl in Q. *)
(*   revert Q. seval. rewrite B. *)
(*   replace (Int.ltu (Int.repr p) Int.iwordsize) with true. *)
(*   intro D; inv D. auto. *)
(*   unfold Int.ltu. rewrite Int.unsigned_repr. rewrite zlt_true; auto. *)
(*   vm_compute; intuition congruence. *)
(*   assert (32 < Int.max_unsigned) by (compute; auto).  *)
(*   omega. *)
(* Qed. *)

Lemma eval_divu_mul:
  forall le x y p M,
  divu_mul_params (Int.unsigned y) = Some(p, M) ->
  nth_error le O = Some (Eval (Vint x)) ->
  exists v,
    eval_expr ge sp e m le (divu_mul p M) v /\
    same_eval v (Eval (Vint (Int.divu x y))).
Proof.
  intros. unfold divu_mul. exploit (divu_mul_shift x); eauto. intros [A B].
  assert (exists v,
            eval_expr ge sp e m le
                      (Eop Omulhu (Eletvar 0 ::: Eop (Ointconst (Int.repr M)) Enil ::: Enil)) v
                      /\ same_eval v (Eval (Vint (Int.mulhu x (Int.repr M))))).
  { eexists; split.
    EvalOp. econstructor. econstructor; eauto. econstructor. EvalOp. simpl; reflexivity. constructor.
    simpl. eauto.
    constructor; simpl; auto. }
  destruct H1 as [vv [C D]].
  exploit eval_shruimm. eexact C. 
  instantiate (1 := Int.repr p). 
  intros [v [P Q]].
  eexists; split. eauto.
  red; simpl; intros.
  specialize (Q alloc em). simpl in Q.
  rewrite D in Q. simpl in Q.
  revert Q. rewrite B.
  replace (Int.ltu (Int.repr p) Int.iwordsize) with true.
  intro E; inv E. auto.
  unfold Int.ltu. rewrite Int.unsigned_repr. rewrite zlt_true; auto.
  vm_compute; intuition congruence.
  assert (32 < Int.max_unsigned) by (compute; auto). 
  omega.
Qed.


Theorem eval_divuimm:
  forall n2, unary_constructor_sound ge sp e m (fun x => divuimm x n2) (fun x => Val.divu x (Eval (Vint n2))).
Proof.
  unfold divuimm; red; intros. 
  destruct (Int.is_power2 n2) as [l | ] eqn:P2.
  - exploit eval_shruimm. eexact EXPR.
    intros [v [A B]].
    eexists; split; eauto. ldt. ld.
    destr. constructor.
    erewrite Int.divu_pow2 by eauto. 
    erewrite Int.is_power2_range; eauto. 
  - destruct (Compopts.optim_for_size tt).
    + eapply eval_divu_base; eauto. EvalOp.
    + destruct (divu_mul_params (Int.unsigned n2)) as [[p M] | ] eqn:PARAMS.
      * unfold divu_mul.
        exploit (eval_shruimm ge sp e m (Int.repr p) (x::le)
                   (Eop Omulhu
                        (Eletvar 0 ::: Eop (Ointconst (Int.repr M)) Enil ::: Enil))).
        repeat (econstructor; simpl; eauto).
        intros [v [A B]].
        eexists; split.
        repeat (econstructor; simpl; eauto).
        ldt.
        ld.
        destr. constructor.
        exploit divu_mul_shift. eauto.
        intros [C D]. rewrite <- D.
        replace (Int.ltu (Int.repr p) Int.iwordsize) with true. auto.
        unfold Int.ltu.
        rewrite Int.unsigned_repr; unfsize; try omega.
        rewrite zlt_true; auto.
        vm_compute; intuition congruence.
      * eapply eval_divu_base; eauto. EvalOp.
Qed.

Theorem eval_divu:
  binary_constructor_sound ge sp e m divu Val.divu.
Proof.
  unfold divu; intros until b. destruct (divu_match b); intros.
- InvEval. eapply eval_divuimm; eauto.
- eapply eval_divu_base; eauto. 
Qed.

(* Lemma eval_mod_from_div: *)
(*   forall le a n x y v, *)
(*     eval_expr ge sp e m le a v -> *)
(*     same_eval v (Eval (Vint y)) -> *)
(*     nth_error le O = Some (Eval (Vint x)) -> *)
(*     exists v', *)
(*       eval_expr ge sp e m le (mod_from_div a n) v' /\ *)
(*       same_eval v' (Eval (Vint (Int.sub x (Int.mul y n)))). *)
(* Proof. *)
(*   unfold mod_from_div; intros.  *)
(*   exploit eval_mulimm; eauto. inv H0; rewrite se_typ; destr. *)
(*   instantiate (1 := n). intros [vv [A B]].  *)
(*   eexists; split; eauto. *)
(*   repeat (econstructor; simpl; eauto). *)
(*   constructor; simpl; auto. *)
(*   inv B; rewrite <- se_typ. simpl. *)
(*   inv H0; rewrite se_typ0; simpl; auto. *)
(*   intros; seval. *)
(*   rewrite <- se_eval0 in Heql. *)
(*   revert Heql; seval. *)
(*   rewrite se_eval in Heql. simpl in Heql. inv Heql. intros. auto. *)
(* Qed. *)

Theorem eval_moduimm:
  forall n2,
    unary_constructor_sound ge sp e m (fun x => moduimm x n2) (fun x => Val.modu x (Eval (Vint n2))).
Proof.
  unfold moduimm; red; intros. 
  destruct (Int.is_power2 n2) as [l | ] eqn:P2.
  - exploit eval_andimm. eexact EXPR.
    intros [v [A B]].
    eexists; split; eauto. ldt. ld.
    destr. constructor.
    erewrite Int.modu_and by eauto. auto.
  - destruct (Compopts.optim_for_size tt).
    + eapply eval_modu_base; eauto. EvalOp.
    + destruct (divu_mul_params (Int.unsigned n2)) as [[p M] | ] eqn:PARAMS.
      * unfold mod_from_div. unfold divu_mul.
        exploit (eval_shruimm ge sp e m (Int.repr p) (x::le)
                   (Eop Omulhu
                        (Eletvar 0 ::: Eop (Ointconst (Int.repr M)) Enil ::: Enil))).
        repeat (econstructor; simpl; eauto).
        intros [v [A B]].
        exploit eval_mulimm. eexact A.
        intros [v2 [C D]].
        eexists; split.
        repeat (econstructor; simpl; eauto).
        unfold Val.sub; ldt.
        eapply Val.lessdef_trans
        with (v2:=Val.sub x (Val.mul (Val.shru (Val.mulhu x (Eval (Vint (Int.repr M))))
                                               (Eval (Vint (Int.repr p)))) (Eval (Vint n2)))).
        {
          ld.
          destr. constructor.
          exploit divu_mul_shift. eauto.
          intros [E F]. rewrite <- F.
          replace (Int.ltu (Int.repr p) Int.iwordsize) with true. simpl.
          rewrite Int.modu_divu.
          auto.
          intro; subst. discriminate.
          unfold Int.ltu.
          rewrite Int.unsigned_repr; unfsize; try omega.
          rewrite zlt_true; auto.
          vm_compute; intuition congruence.
        }
        repeat apply Val.lessdef_binop; auto.
      * eapply eval_modu_base; eauto. EvalOp.
Qed.

Theorem eval_modu:
  binary_constructor_sound ge sp e m modu Val.modu.
Proof.
  unfold modu; red; intros until b. destruct (modu_match b); intros.
- InvEval. eapply eval_moduimm; eauto.
- eapply eval_modu_base; eauto. 
Qed.

(* Lemma eval_divs_mul: *)
(*   forall le x y p M, *)
(*   divs_mul_params (Int.signed y) = Some(p, M) -> *)
(*   nth_error le O = Some (Eval (Vint x)) -> *)
(*   exists v, *)
(*     eval_expr ge sp e m le (divs_mul p M) v /\ *)
(*     same_eval v (Eval (Vint (Int.divs x y))). *)
(* Proof. *)
(*   intros. unfold divs_mul. *)
(*   assert (V: eval_expr ge sp e m le (Eletvar O) (Eval (Vint x))). *)
(*   { constructor; auto. } *)
(*   assert (X: exists v, *)
(*                eval_expr ge sp e m le *)
(*                          (Eop Omulhs (Eletvar 0 ::: Eop (Ointconst (Int.repr M)) Enil ::: Enil)) *)
(*                          v /\ *)
(*                same_eval v (Eval (Vint (Int.mulhs x (Int.repr M))))). *)
(*   { eexists; split. EvalOp. econstructor. eauto. econstructor. EvalOp. simpl; reflexivity. *)
(*     constructor. *)
(*     simpl; auto. econstructor; simpl; auto. } *)
(*   exploit eval_shruimm. eexact V.  *)
(*   simpl; auto. *)
(*   instantiate (1 := Int.repr (Int.zwordsize - 1)).  *)
(*   intros [v1 [Y LD]]. simpl in LD.  *)
(*   (* change (Int.ltu (Int.repr 31) Int.iwordsize) with true in LD.  *) *)
(*   (* simpl in LD. inv LD.  *) *)
(*   assert (RANGE: 0 <= p < 32 -> Int.ltu (Int.repr p) Int.iwordsize = true). *)
(*   { intros. unfold Int.ltu. rewrite Int.unsigned_repr. rewrite zlt_true by tauto. auto. *)
(*     assert (32 < Int.max_unsigned) by (compute; auto). omega. } *)
(*   destruct X as [v [X ZZ]]. *)
(*   destruct (zlt M Int.half_modulus). *)
(* - exploit (divs_mul_shift_1 x); eauto. intros [A B]. *)
(*   exploit eval_shrimm. eexact X. *)
(*   inv ZZ; rewrite se_typ; simpl; auto. *)
(*   instantiate (1 := Int.repr p). intros [v1' [Z LD']]. *)
(*   (* simpl in LD. rewrite RANGE in LD by auto. inv LD. *) *)
(*   exploit eval_add. eexact Z. eexact Y.  *)
(*   inv LD'; rewrite <- se_typ; simpl; auto. *)
(*   inv ZZ; rewrite se_typ0; simpl; auto. *)
(*   inv LD; rewrite <- se_typ; simpl; auto. *)
(*   intros [v0 [W LD'']]. *)
(*   eexists; split. eauto.  rewrite <- LD''. rewrite B. *)
(*   clear - LD LD' ZZ A RANGE. *)
(*   inv LD; inv LD'; inv ZZ; constructor; simpl; auto. *)
(*   rewrite <- se_typ0. simpl. *)
(*   rewrite <- se_typ. simpl. *)
(*   rewrite se_typ1; auto. *)
(*   intros; seval. *)
(*   rewrite <- se_eval0 in Heql. *)
(*   intro A; rewrite <- A in Heql0. clear se_eval0 A. *)
(*   rewrite se_eval1 in Heql. simpl in *. inv Heql0. *)
(*   rewrite H2 in Heql. simpl in *. inv Heql. auto.  *)
(* - exploit (divs_mul_shift_2 x); eauto. intros [A B]. *)
(*   refine ((fun zld => _) (eval_add ge sp e m _ _ _ _ _ X V _ _)). *)
(*   destruct zld as [v0 [Z LD']]. *)
(*   refine ((fun zld => _) (eval_shrimm ge sp e m (Int.repr p) _ _ _ Z _)). *)
(*   destruct zld as [v2 [U LD'']]. *)
(*   refine ((fun zld => _) (eval_add ge sp e m _ _ _ _ _ U Y _ _)). *)
(*   destruct zld as [v3 [W LD''']]. *)
(*   rewrite B. eexists; split; eauto. *)
(*   + rewrite <- LD'''. *)
(*     clear - A RANGE LD' LD'' LD ZZ. *)
(*     intuition try congruence; simpl; simpwt; auto. *)
(*     intros; seval. *)
(*     intros. *)
(*     rew_eval. *)
(*     rewrite H1 in H3. simpl in H3. inv H3. auto. *)
(*   + intuition try congruence; simpl; simpwt; auto. *)
(*   + intuition try congruence; simpl; simpwt; auto. *)
(*   + intuition try congruence; simpl; simpwt; auto. *)
(*   + intuition try congruence; simpl; simpwt; auto. *)
(*   + intuition try congruence; simpl; simpwt; auto. *)
(* Qed. *)

Theorem eval_divsimm:
  forall n2, unary_constructor_sound ge sp e m (fun x => divsimm x n2) (fun x => Val.divs x (Eval (Vint n2))).
Proof.
  unfold divsimm; red; intros. 
  destruct (Int.is_power2 n2) as [l | ] eqn:P2.
  - destr.
    + exploit eval_shrximm. eexact EXPR.
      intros [v [A B]].
      eexists; split; eauto. ldt. ld.
      destr. constructor.
      rewrite Heqb.
      erewrite Int.divs_pow2 by eauto.  simpl; auto.
    + eapply eval_divs_base; eauto. EvalOp.
  - destruct (Compopts.optim_for_size tt).
    eapply eval_divs_base; eauto. EvalOp.
    destruct (divs_mul_params (Int.signed n2)) as [[p M] | ] eqn:PARAMS.
    + unfold divs_mul.
      destr. 
      * exploit (eval_shrimm ge sp e m (Int.repr p) (x::le)
                             (Eop Omulhs
                                  (Eletvar 0 ::: Eop (Ointconst (Int.repr M)) Enil ::: Enil))).
        repeat (econstructor; simpl; eauto).
        intros [v [A B]].
        exploit (eval_shruimm ge sp e m (Int.repr 31) (x::le) (Eletvar 0)).
        repeat (econstructor; simpl; eauto).
        intros [v2 [C D]].
        exploit eval_add.
        eexact A. eexact C.
        intros [v3 [E F]].
        eexists; split.
        repeat (econstructor; simpl; eauto).
        ldt. unfold Val.add. ldt.
        ld.
        destr. constructor.
        exploit divs_mul_shift_1. eauto. auto.
        intros [G I]. rewrite I.
        replace (Int.ltu (Int.repr p) Int.iwordsize) with true.
        replace (Int.ltu (Int.repr 31) Int.iwordsize) with true.
        simpl; auto.
        vm_compute; intuition congruence.
        unfold Int.ltu. rewrite zlt_true; auto.
        rewrite Int.unsigned_repr. vm_compute; intuition congruence.
        unfsize; omega.
      * assert (eval_expr ge sp e m (x::le) (Eletvar 0) x).
        repeat (econstructor; simpl; eauto).
        exploit (eval_add ge sp e m (x::le)
                          (Eop Omulhs
                               (Eletvar 0
                                        ::: Eop (Ointconst (Int.repr M)) Enil ::: Enil))).
        repeat (econstructor; simpl; eauto). eauto.
        intros [v0 [Y Z]].
        exploit eval_shrimm. eexact Y.
        intros [v [A B]].
        exploit (eval_shruimm ge sp e m (Int.repr 31) (x::le) (Eletvar 0)). eauto.
        intros [v2 [C D]].
        exploit eval_add.
        eexact A. eexact C.
        intros [v3 [E F]].
        eexists; split.
        repeat (econstructor; simpl; eauto).
        ldt. unfold Val.add. ldt. clear B C D E F Y A.
        eapply Val.lessdef_trans with
        (Ebinop OpAdd Tint Tint (Val.shr (Val.add (Val.mulhs x (Eval (Vint (Int.repr M)))) x) (Eval (Vint (Int.repr p)))) (Val.shru x (Eval (Vint (Int.repr 31))))).
        ld.
        destr. constructor.
        exploit divs_mul_shift_2. eauto. auto.
        intros [G I]. rewrite I.
        replace (Int.ltu (Int.repr p) Int.iwordsize) with true.
        replace (Int.ltu (Int.repr 31) Int.iwordsize) with true.
        simpl; auto.
        vm_compute; intuition congruence.
        unfold Int.ltu. rewrite zlt_true; auto.
        rewrite Int.unsigned_repr. vm_compute; intuition congruence.
        unfsize; omega.
        repeat apply Val.lessdef_binop; auto.
    + eapply eval_divs_base; eauto. EvalOp.
Qed.

Theorem eval_divs:
  binary_constructor_sound ge sp e m divs Val.divs.
Proof.
  unfold divs; intros until b. destruct (divs_match b); intros.
- InvEval. eapply eval_divsimm; eauto.
- eapply eval_divs_base; eauto. 
Qed.

Theorem eval_modsimm:
  forall n2,
    unary_constructor_sound ge sp e m (fun x => modsimm x n2) (fun x => Val.mods x (Eval (Vint n2))).
Proof.
  unfold modsimm; red; intros. 
  destruct (Int.is_power2 n2) as [l | ] eqn:P2.
  - destr.
    + assert (eval_expr ge sp e m (x::le) (Eletvar 0) x). econstructor; simpl; eauto.
      exploit eval_shrximm. eexact H.
      intros [v [A B]].
      unfold mod_from_div.
      exploit eval_mulimm. eexact A.
      intros [v0 [C D]].
      eexists; split.
      repeat (econstructor; simpl; eauto).
      unfold Val.sub. ldt.
      eapply Val.lessdef_trans with (Ebinop OpSub Tint Tint x (Val.mul (Val.shrx x (Eval (Vint l)))
                                                                       (Eval (Vint n2)))).
      ld. destr. constructor.
      rewrite Heqb. rewrite Int.mods_divs.
      erewrite Int.divs_pow2 by eauto.  simpl; auto.
      repeat (apply Val.lessdef_binop; auto).
    + eapply eval_mods_base; eauto. EvalOp.
  - destruct (Compopts.optim_for_size tt).
    eapply eval_mods_base; eauto. EvalOp.
    destruct (divs_mul_params (Int.signed n2)) as [[p M] | ] eqn:PARAMS.
    + unfold mod_from_div, divs_mul.
      destr. 
      * exploit (eval_shrimm ge sp e m (Int.repr p) (x::le)
                             (Eop Omulhs
                                  (Eletvar 0 ::: Eop (Ointconst (Int.repr M)) Enil ::: Enil))).
        repeat (econstructor; simpl; eauto).
        intros [v [A B]].
        exploit (eval_shruimm ge sp e m (Int.repr 31) (x::le) (Eletvar 0)).
        repeat (econstructor; simpl; eauto).
        intros [v2 [C D]].
        exploit eval_add.
        eexact A. eexact C.
        intros [v3 [E F]].
        exploit eval_mulimm.
        eexact E.
        intros [v4 [J K]].
        eexists; split.
        repeat (econstructor; simpl; eauto).
        unfold Val.sub. ldt. clear K J E C A.
        eapply Val.lessdef_trans with
        (Ebinop OpSub Tint Tint x (Val.mul (Val.add (Val.shr (Val.mulhs x (Eval (Vint (Int.repr M))))
           (Eval (Vint (Int.repr p)))) (Val.shru x (Eval (Vint (Int.repr 31))))) (Eval (Vint n2)))).
        ld.
        destr. constructor.
        exploit divs_mul_shift_1. eauto. auto.
        intros [G I]. rewrite Int.mods_divs. rewrite I.
        replace (Int.ltu (Int.repr p) Int.iwordsize) with true.
        replace (Int.ltu (Int.repr 31) Int.iwordsize) with true.
        simpl; auto.
        vm_compute; intuition congruence.
        unfold Int.ltu. rewrite zlt_true; auto.
        rewrite Int.unsigned_repr. vm_compute; intuition congruence.
        unfsize; omega.
        repeat (ldt; apply Val.lessdef_binop; auto).
      * assert (eval_expr ge sp e m (x::le) (Eletvar 0) x).
        repeat (econstructor; simpl; eauto).
        exploit (eval_add ge sp e m (x::le)
                          (Eop Omulhs
                               (Eletvar 0
                                        ::: Eop (Ointconst (Int.repr M)) Enil ::: Enil))).
        repeat (econstructor; simpl; eauto). eauto.
        intros [v0 [Y Z]].
        exploit eval_shrimm. eexact Y.
        intros [v [A B]].
        exploit (eval_shruimm ge sp e m (Int.repr 31) (x::le) (Eletvar 0)). eauto.
        intros [v2 [C D]].
        exploit eval_add.
        eexact A. eexact C.
        intros [v3 [E F]].
        exploit (eval_mulimm).
        eexact E.
        intros [v1 [J K]].
        eexists; split.
        repeat (econstructor; simpl; eauto).
        unfold Val.sub. ldt. clear J E C A Y K.
        eapply Val.lessdef_trans with
        (Ebinop OpSub Tint Tint x (Val.mul (Val.add (Val.shr (Val.add (Val.mulhs x (Eval (Vint (Int.repr M)))) x) (Eval (Vint (Int.repr p)))) (Val.shru x (Eval (Vint (Int.repr 31))))) (Eval (Vint n2)))).
        ld.
        destr. constructor.
        exploit divs_mul_shift_2. eauto. auto.
        intros [G I]. rewrite Int.mods_divs. rewrite I.
        replace (Int.ltu (Int.repr p) Int.iwordsize) with true.
        replace (Int.ltu (Int.repr 31) Int.iwordsize) with true.
        simpl; auto.
        vm_compute; intuition congruence.
        unfold Int.ltu. rewrite zlt_true; auto.
        rewrite Int.unsigned_repr. vm_compute; intuition congruence.
        unfsize; omega.
        repeat (ldt; apply Val.lessdef_binop; auto).
    + eapply eval_mods_base; eauto. EvalOp.
Qed.

Theorem eval_mods:
  binary_constructor_sound ge sp e m mods Val.mods.
Proof.
  unfold mods; intros until b. destruct (mods_match b); intros.
- InvEval. eapply eval_modsimm; eauto.
- eapply eval_mods_base; eauto. 
Qed.

(** * Floating-point division *)

Ltac TrivialExists :=
  eexists; split; [repeat (econstructor; simpl; eauto)|eauto; try solve[constructor; simpl; auto]].

Theorem eval_divf:
  binary_constructor_sound ge sp e m divf Val.divf.
Proof.
  red; intros until y. unfold divf. destruct (divf_match b); intros.
  - unfold divfimm. destruct (Float.exact_inverse n2) as [n2' | ] eqn:EINV.
    + InvEval.  econstructor; split.
      repeat (econstructor; simpl; eauto).
      ld.
      erewrite Float.div_mul_inverse; eauto. 
    + TrivialExists.
  - TrivialExists.
Qed.

Theorem eval_divfs:
  binary_constructor_sound ge sp e m divfs Val.divfs.
Proof.
  red; intros until y. unfold divfs. destruct (divfs_match b); intros.
  - unfold divfsimm. destruct (Float32.exact_inverse n2) as [n2' | ] eqn:EINV.
    + InvEval. econstructor; split.
      repeat (econstructor; simpl; eauto).
      ld. 
      erewrite Float32.div_mul_inverse; eauto. 
    + TrivialExists. 
  - TrivialExists.
Qed.

End CMCONSTRS.
