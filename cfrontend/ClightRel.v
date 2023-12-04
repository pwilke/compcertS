Require Import Coqlib.
Require Import Maps.
Require Import Values.
Require Import Globalenvs.
Require Import Events.
Require Import Ctypes.
Require Import Values_symbolictype.
Require Import Values_symbolic.
Require Import Normalise.
Require Import NormaliseSpec.
Require Import Memory.
Require Import Memdata.
Require Import Cop.
Require Import Integers.
Require Import Clight.
Require Import Equivalences.

Require Import MemRel.

(** This modules defines useful lemmas about equivalences of symbolic
expressions and memories, and in particular in relation with Clight semantics.
*)

Section RelClight.

  Variable mr : expr_sym -> expr_sym -> Prop.
  Hypothesis wf: wf_mr mr.
  
  (** We lift the notion of equivalence on temporary environments.  *)
  Definition temp_env_equiv (le le': temp_env) : Prop :=
    forall i,
      match PTree.get i le, PTree.get i le' with
        Some a, Some b => mr a b
      | None, None => True
      | _, _ => False
      end.

  Lemma temp_env_equiv_refl:
    forall t,
      temp_env_equiv t t.
  Proof.
    red; intros.
    destr; apply (mr_refl); auto.
  Qed.

  Lemma mr_trans:
    forall a b c, mr a b -> mr b c -> mr a c.
  Proof.
    intros a b c A B.
    destruct wf. destruct mr_se_or_ld.
    subst; congruence.
    subst; eapply Val.lessdef_trans; eauto.
  Qed.
  
  Lemma temp_env_equiv_trans:
    forall t1 t2 t3,
      temp_env_equiv t1 t2 ->
      temp_env_equiv t2 t3 ->
      temp_env_equiv t1 t3.
  Proof.
    intros t1 t2 t3 A B; red; intro i;
    specialize (A i); specialize (B i);
    repeat destr_cond_match; destruct (t2!i) eqn:?; simpl in *; auto.
    eapply mr_trans; eauto.
    easy.   
  Qed.

  Instance temp_env_equiv_equi : RelationClasses.PreOrder temp_env_equiv :=
    RelationClasses.Build_PreOrder  _ _
                                    (temp_env_equiv_refl)
                                    (temp_env_equiv_trans).


  Lemma temp_env_equiv_set:
    forall le le',
      temp_env_equiv le le' ->
      forall id v v',
        mr v v' ->
        temp_env_equiv (PTree.set id v le) (PTree.set id v' le').
  Proof.
    red; intros.
    rewrite ! PTree.gsspec.
    destruct (peq i id); subst; auto.
    apply H.
  Qed.

  Lemma bind_parameter_temps_equiv:
    forall args args',
      list_forall2 mr args args' ->
      forall par tmp tmp' le,
        temp_env_equiv tmp tmp' ->
        bind_parameter_temps par args tmp = Some le ->
        exists le',
          bind_parameter_temps par args' tmp' = Some le' /\ temp_env_equiv le le'.
  Proof.
    induction 1; simpl; intros.
    - destruct par; simpl in *.
      + inv H0. eexists; split; eauto.
      + destruct p; congruence.
    - destruct par; simpl in H2. congruence.
      destruct p.
      eapply IHlist_forall2 in H2; eauto.
      apply temp_env_equiv_set; auto.
  Qed.

  Hypothesis wfn: wf_mr_norm mr.
  
  Lemma deref_loc_same_eval:
    forall t m a a' v,
      deref_loc t m a v ->
      mr a a' ->
      exists v',
        deref_loc t m a' v' /\ mr v v'.
  Proof.
    intros t m a a' v DL SE; inv DL.
    - unfold Mem.loadv in H0; revert H0; destr_cond_match; try discriminate.
      intro.
      generalize (rel_norm _ wf wfn _ _ _ _ (mem_rel_refl _ wf m) SE). rewrite Heqv0.
      intro A. apply (mr_val_refl _ wf) in A; try congruence.
      eexists; split; eauto.
      econstructor; eauto.
      unfold Mem.loadv. rewrite <- A; eauto. apply mr_refl; auto.
    - eexists; split; eauto.
      eapply deref_loc_reference; eauto. 
    - eexists; split; eauto.
      eapply deref_loc_copy; eauto.
  Qed.

  Ltac ld_rew :=
    repeat ((apply (mr_unop _ wf) ;auto)
            ||
            (apply (mr_binop _ wf) ;auto)
            || apply (mr_refl _ wf) ; auto).

Lemma sem_unary_operation_expr_ld:
  forall u t e e',
    mr e e' ->
    mr (sem_unary_operation_expr u e t)
                (sem_unary_operation_expr u e' t).
Proof.
  destruct u; simpl; intros;
  unfold sem_notbool_expr, sem_notint_expr, sem_neg_expr, sem_absfloat_expr, expr_cast_gen;
  destr;
  ld_rew.
Qed.

Definition preserves_lessdef f :=
  forall a b a1 b1,
    mr a b ->
    mr a1 b1 ->
    match f a a1 with
    | Some c =>
      match f b b1 with
      | Some d => mr c d
      | None => False
      end
    | None => match f b b1 with
             | Some _ => False
             | None => True
             end
    end.


Definition preserves_lessdef_unary (f: expr_sym -> option expr_sym) : Prop :=
  forall e e',
    mr e e' ->
    match
      f e, f e'
    with
       | Some a, Some b => mr a b
       | None, None => True
       | _, _ => False
    end.


Lemma expr_cast_int_int_ld:
  forall sz2 si2 e e',
    mr e e' ->
    mr (expr_cast_int_int sz2 si2 e)
       (expr_cast_int_int sz2 si2 e').
Proof.
  intros.
  destruct sz2; destruct si2; unfold expr_cast_int_int; ld_rew.
Qed.

Lemma expr_cast_gen_ld:
  forall t s t' s' e e',
    mr e e' ->
    mr (expr_cast_gen t s t' s' e)
       (expr_cast_gen t s t' s' e').
Proof.
  intros.
  destruct t; destruct s; destruct t'; destruct s'; unfold expr_cast_gen;ld_rew.
Qed.


Ltac ld_rew' :=
  repeat ((apply (mr_unop _ wf); auto)
            ||
            (apply (mr_binop _ wf); eauto)
            ||
            (apply expr_cast_int_int_ld)
            ||
            (apply expr_cast_gen_ld)
            || apply (mr_refl _ wf); auto).


Lemma sem_cast_expr_ld:
  forall t t',
    preserves_lessdef_unary (fun e => sem_cast_expr e t t').
Proof.
  intros.
  unfold preserves_lessdef_unary; intros.
  unfold sem_cast_expr.
  destruct (classify_cast t t'); unfold Val.sign_ext, Val.loword;
  try apply expr_cast_int_int_ld; destr; ld_rew'.
Qed.

Lemma sem_binarith_expr_ld:
  forall si sl sf ss t t'
         (si_norm: forall s, preserves_lessdef (si s))
         (sl_norm: forall s, preserves_lessdef (sl s))
         (sf_norm: preserves_lessdef sf)
         (ss_norm: preserves_lessdef ss),
    preserves_lessdef (fun e f => sem_binarith_expr si sl sf ss e t f t').
Proof.
  red; intros.
  unfold sem_binarith_expr. 
  generalize (sem_cast_expr_ld t (binarith_type (classify_binarith t t')) _ _ H).
  generalize (sem_cast_expr_ld t' (binarith_type (classify_binarith t t')) _ _ H0).
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

Lemma sem_shift_expr_ld:
  forall si sl t t'
         (si_norm: forall s a b c d,
                     mr a b ->
                     mr c d ->
                     mr (si s a c) (si s b d))
         (sl_norm: forall s a b c d,
                     mr a b ->
                     mr c d ->
                     mr (sl s a c) (sl s b d)),
    preserves_lessdef (fun e f => sem_shift_expr si sl e t f t').
Proof.
  red; intros.
  unfold sem_shift_expr.
  destruct (classify_shift t t'); try discriminate.
  apply si_norm; auto.
  apply sl_norm; auto.
  apply si_norm; auto.
  apply expr_cast_gen_ld; auto.
  apply sl_norm; auto.
  apply expr_cast_gen_ld; auto.
  auto.
Qed.


Lemma sem_binary_operation_expr_ld:
  forall b t t' e e' f f',
    mr e e' ->
    mr f f' ->
    match sem_binary_operation_expr b e t f t', sem_binary_operation_expr b e' t f' t' with
        Some a, Some b => mr a b
      | None, None => True
      | _ , _ => False
    end.
Proof.
  destruct b; simpl; intros;
  unfold sem_add_expr, sem_sub_expr, sem_mul_expr, sem_div_expr, sem_mod_expr,
  sem_shl_expr, sem_shr_expr, sem_cmp_expr;
  try match goal with
      |- context [ match ?f ( _ :type) (_: type) with _ => _ end ] =>
      destruct (f t t'); ld_rew
      end;
  try (apply sem_binarith_expr_ld; auto; red; intros; try apply mr_binop; auto);
  try (apply sem_shift_expr_ld; auto; intros; auto; apply mr_binop; auto;
       apply expr_cast_gen_ld; auto).
Qed.

Lemma temp_equiv_clight_eval_expr_lvalue:
  forall ge m e le le',
    temp_env_equiv le le' ->
    (forall a v,
       Clight.eval_expr ge e le m a v ->
       exists v',
         Clight.eval_expr ge e le' m a v' /\
         mr v v')
    /\(forall a ptr,
         Clight.eval_lvalue ge e le  m a ptr ->
         exists ptr',
           Clight.eval_lvalue ge e le' m a ptr' /\
           mr ptr ptr').
Proof.
  intros ge m e le le' ME.
  apply eval_expr_lvalue_ind; intros;
  try (eexists; split; eauto; [econstructor; eauto| now ld_rew]; fail).
  - (* temp var *)
     specialize (ME id).
     rewrite H in ME.
     revert ME; destr_cond_match; try intuition congruence. 
     intros; eexists; split; eauto.
     constructor; eauto.
  - (* addrof *)
    destruct H0 as [v' [A B]].
    eexists; split; eauto.
    econstructor; simpl; eauto.
  - (* unop *) 
    destruct (H0) as [v' [A B]].
    eexists; split.
    econstructor; simpl; eauto.
    subst.
    apply sem_unary_operation_expr_ld; auto.
  - (* binop *)
    destruct (H0) as [v' [A B]].
    destruct (H2) as [v'' [C D]].
    generalize (sem_binary_operation_expr_ld op (typeof a1) (typeof a2) _ _ _ _
                                             B D).
    rewrite H3.
    destr_cond_match; intros; try intuition congruence.
    eexists; split.
    econstructor; simpl; eauto.
    auto.
  - (* cast *)
    destruct (H0) as [v' [A B]].
    generalize (sem_cast_expr_ld (typeof a) ty _ _ B).
    rewrite H1.
    destr_cond_match; intros; try intuition congruence.
    eexists; split; eauto.
    econstructor; simpl; eauto.
  - (* var local *)
    destruct H0 as [v' [A B]].
    apply (deref_loc_same_eval) with (a':=v') in H1; auto.
    destruct H1 as [v2 [C D]].
    eexists; split; eauto. econstructor; eauto.
  - (* var global *)
    eexists; split. apply eval_Evar_global; eauto.
    apply mr_refl; auto.
  - (* deref *)
    destruct H0 as [v' [A B]].
    eexists; split; eauto. econstructor; eauto.
  - (* field struct *)
    destruct (H0) as [v' [A B]].
    eexists; split.    econstructor; eauto.
    ld_rew.
  - (* field union *)
    destruct (H0) as [v' [A B]].
    eexists; split; eauto. econstructor; eauto.
Qed.


Lemma temp_equiv_clight_eval_expr:
  forall ge e le le' m,
    temp_env_equiv le le' ->
    forall a v,
       Clight.eval_expr ge e le m a v ->
       exists v',
         Clight.eval_expr ge e le' m a v' /\
         mr v v'.
Proof.
  intros ge e le le' m' TE.
  apply (proj1 (temp_equiv_clight_eval_expr_lvalue ge m' e le le' TE)).
Qed.

Lemma temp_equiv_clight_eval_exprlist:
  forall ge e le le' m,
    temp_env_equiv le le' ->
    forall al tl vl,
       Clight.eval_exprlist ge e le m al tl vl ->
       exists vl',
         Clight.eval_exprlist ge e le' m al tl vl' /\
         list_forall2 mr vl vl'.
Proof.
  induction al; simpl; intros.
  - inv H0. (exists nil; split; auto); constructor.
  - inv H0.
    apply IHal in H7.
    destruct H7 as [vl' [A B]].
    eapply temp_equiv_clight_eval_expr in H3; eauto.
    destruct H3 as [v' [C D]].
    generalize (sem_cast_expr_ld (typeof a) ty _ _ D); rewrite H4.
    destr_cond_match; try intuition congruence.
    intro.
    exists (  e0 :: vl'); split. 
    econstructor; eauto.
    constructor; auto.
Qed.

Lemma temp_equiv_clight_eval_lvalue:
  forall ge e le le' m,
    temp_env_equiv le le' ->
    forall a ptr,
      Clight.eval_lvalue ge e le  m a ptr ->
      exists ptr',
        Clight.eval_lvalue ge e le' m a ptr' /\
        mr ptr ptr'.
Proof.
  intros ge e le le' m' TE.
  apply (proj2 (temp_equiv_clight_eval_expr_lvalue ge m' e le le' TE)).
Qed.

Lemma mem_equiv_deref_loc:
  forall t m locofs v m',
    mem_rel mr m m' ->
    deref_loc t m locofs v ->
    exists v',
      deref_loc t m' locofs v' /\ mr v v'.
Proof.
  intros t m locofs v m' ME DL; inv DL.
  - apply (loadv_mem_rel _ wf _ m') in H0; auto.
    destruct H0 as [v' [LV B]].
    eexists; split; eauto.
    econstructor; eauto.
  - eexists; split; eauto.
    eapply deref_loc_reference; eauto.
    apply mr_refl; auto.
  - eexists; split; eauto.
    eapply deref_loc_copy; eauto.
    ld_rew.
Qed.

Lemma mem_equiv_clight_eval_expr_lvalue:
  forall ge e le m m',
    mem_rel mr m m' ->
    (forall a v,
       Clight.eval_expr ge e le m a v ->
       exists v',
         Clight.eval_expr ge e le m' a v' /\
         mr v v')
    /\(forall a v,
         Clight.eval_lvalue ge e le m a v ->
         exists v',
           Clight.eval_lvalue ge e le m' a v' /\
           mr v v').
Proof.
  intros ge e le m m' ME.
  apply eval_expr_lvalue_ind; intros.
- (* const int *)
  eexists; split; eauto.
  econstructor; eauto. ld_rew.
- (* const float *)
  eexists; split; eauto.
  econstructor; eauto. ld_rew.
- (* const single *)
    eexists; split; eauto.
  econstructor; eauto. ld_rew.
- (* const long *)
    eexists; split; eauto.
  econstructor; eauto. ld_rew.
- (* temp var *)
  eexists; split; eauto.
  constructor; eauto.  ld_rew.
- (* addrof *)
  destruct H0 as [v' [A B]].
  eexists; split; eauto.
  econstructor; simpl; eauto.
- (* unop *) 
  destruct (H0) as [v' [A B]].
  eexists; split.
  econstructor; simpl; eauto.
  subst.
  apply sem_unary_operation_expr_ld; auto.
- (* binop *)
  destruct (H0) as [v' [A B]].
  destruct (H2) as [v'' [C D]].
  generalize (sem_binary_operation_expr_ld op (typeof a1) (typeof a2) _ _ _ _
                                           B D).
  rewrite H3.
  destr_cond_match; intros; try intuition congruence.
  eexists; split.
  econstructor; simpl; eauto. auto.
- (* cast *)
  destruct (H0) as [v' [A B]].
  generalize (sem_cast_expr_ld (typeof a) ty _ _ B).
  rewrite H1.
  destr_cond_match; intros; try intuition congruence.
  eexists; split; eauto.
  econstructor; simpl; eauto.
- (* rvalue out of lvalue *)
  destruct H0 as [v' [A B]].
  apply (mem_equiv_deref_loc) with (m':=m')  in H1; auto.
  destruct H1 as [v'' [C D]].
  apply deref_loc_same_eval with (a':=v') in C; auto.
  destruct C as [v3 [E F]].
  eexists; split.
  econstructor; eauto.
  eapply mr_trans; eauto.
- (* var local *)
  eexists; split. econstructor; eauto.  ld_rew. 

- (* var global *)
  eexists; split. apply eval_Evar_global; eauto. 
  ld_rew.  
- (* deref *)
  destruct H0 as [v' [A B]].
  eexists; split; eauto.
  econstructor; eauto.
- (* field struct *)
  destruct (H0) as [v' [A B]].
  eexists; split.
  econstructor; eauto. ld_rew.
- (* field union *)
  destruct (H0) as [v' [A B]].
  eexists; split; eauto.
  eapply eval_Efield_union; eauto.
Qed.

Lemma mem_equiv_clight_eval_expr:
  forall ge e le m m',
    mem_rel mr m m' ->
    forall a sv,
    Clight.eval_expr ge e le m a sv ->
    exists sv',
      Clight.eval_expr ge e le m' a sv' /\
      mr sv sv'.
Proof.
  intros ge e le m m' ME.
  exact (proj1 (mem_equiv_clight_eval_expr_lvalue ge e le _ _ ME)).
Qed.

Lemma mem_equiv_clight_eval_exprlist:
  forall ge e le m m',
    mem_rel mr m m' ->
    forall al tl sv,
    Clight.eval_exprlist ge e le m al tl sv ->
    exists sv',
      Clight.eval_exprlist ge e le m' al tl sv' /\
      list_forall2 mr sv sv'.
Proof.
  induction al; simpl; intros.
  - inv H0. eexists; split; eauto; constructor.
  - inv H0. apply IHal in H7.
    destruct H7 as [sv' [A B]].
    eapply mem_equiv_clight_eval_expr in H3; eauto.
    destruct H3 as [sv'0 [C D]].
    generalize (sem_cast_expr_ld (typeof a) ty _ _ D); rewrite H4.
    destr_cond_match; try intuition congruence.
    intro.
    exists (e0 :: sv'); split; eauto.
    econstructor; eauto.
    constructor; auto.
Qed.

Lemma mem_equiv_clight_eval_lvalue:
  forall ge e le m m',
    mem_rel mr m m' ->
    forall a ptr,
      Clight.eval_lvalue ge e le m a ptr ->
      exists ptr',
        Clight.eval_lvalue ge e le m' a ptr' /\
        mr ptr ptr'.
Proof.
  intros ge e le m m' ME.
  exact (proj2 (mem_equiv_clight_eval_expr_lvalue ge e le _ _ ME)).
Qed.

Lemma mem_equiv_assign_loc:
  forall t m addr v m' m2,
    mem_rel mr m m' ->
    assign_loc t m addr v m2 ->
    exists m2',
      assign_loc t m' addr v m2' /\
      mem_rel mr m2 m2'.
Proof.
  intros t m addr v m' m2 ME AL; inv AL.
  - eapply storev_mem_rel in STOREV; eauto. 
    destruct STOREV as [v' [ST B]].
    eexists; split; eauto.
    econstructor; eauto.
  - 
    eapply mem_rel_loadbytes in LB; eauto.
    destruct LB as [v' [A B]].
    eapply storebytes_rel in SB; eauto.
    destruct SB as [m0 [C D]].
    exists m0; split; auto.
    eapply assign_loc_copy with (ofs':=ofs') (ofs:=ofs); eauto. 
    rewrite <- MNv. symmetry.
    eapply mem_rel_norm; eauto.
    rewrite <- MNaddr. symmetry.
    eapply mem_rel_norm; eauto.
  - eexists; split ; [econstructor 3; eauto|eauto].
Qed.

Lemma val_equiv_assign_loc:
  forall t m addr v v' m2,
    assign_loc t m addr v m2 ->
    mr v v' ->
    exists m2',
      assign_loc t m addr v' m2' /\
      mem_rel mr m2 m2'.
Proof.
  intros t m addr v v' m2 AL SE; inv AL.
  - eapply storev_val_rel in STOREV; eauto. 
    destruct STOREV as [m2' [ST B]].
    eexists; split; eauto.
    econstructor; eauto.
  - eexists; split.
    eapply (assign_loc_copy t m addr _ _ _ ofs' bytes m2); eauto.
    rewrite <- MNv.
    generalize (rel_norm _ wf wfn _ _ _ _ (mem_rel_refl _ wf m) SE).
    rewrite MNv.
    intro A. apply (mr_val_refl _ wf) in A; auto. congruence.
    apply mem_rel_refl; auto.
  - eexists; split ; [econstructor 3; eauto|eauto]. apply mem_rel_refl; auto. 
Qed.

Lemma addr_equiv_assign_loc:
  forall t m addr addr' v  m2,
    assign_loc t m addr v m2 ->
    mr addr addr' ->
    assign_loc t m addr' v m2.
Proof.
  intros t m addr addr' v m2 AL SE; inv AL.
  - eapply assign_loc_value; eauto.
    revert STOREV; unfold Mem.storev.
    generalize (rel_norm _ wf wfn _ _ _ _ (mem_rel_refl _ wf m) SE).
    intro A. destr.
    apply (mr_val_refl _ wf) in A; try congruence. rewrite <- A; auto.
  - 
    eapply (assign_loc_copy t m addr' _ _ _ ofs' bytes m2); eauto.
    rewrite <- MNaddr.
    generalize (rel_norm _ wf wfn _ _ _ _ (mem_rel_refl _ wf m) SE).
    intro A.
    rewrite MNaddr in A. apply (mr_val_refl _ wf) in A; congruence.
  - econstructor 3; eauto.
Qed.


Lemma deref_loc_se:
  forall m tm (EQ: mem_rel mr m tm)
    ty addr v addr',
    deref_loc ty m addr v ->
    mr addr addr' ->
    exists tv,
      deref_loc ty tm addr' tv
      /\ mr v tv.
Proof.
  intros m tm EQ ty addr v addr' DL SE.
  eapply deref_loc_same_eval in DL; eauto.
  destruct DL as [v' [DL A]].
  eapply mem_equiv_deref_loc in DL; eauto.
  destruct DL as [v'0 [DL B]].
  eexists; split; eauto.
  eapply mr_trans; eauto.
Qed.

Lemma mem_temp_equiv_expr_lvalue:
  forall ge e le le' m m',
    mem_rel mr m m' ->
    temp_env_equiv le le' ->
    (forall a v,
       Clight.eval_expr ge e le m a v ->
       exists v',
         Clight.eval_expr ge e le' m' a v' /\
         mr v v')
    /\(forall a v,
         Clight.eval_lvalue ge e le m a v ->
         exists v',
           Clight.eval_lvalue ge e le' m' a v' /\
           mr v v').
Proof.
  intros ge0 e le le' m m' ME TEE.
  apply eval_expr_lvalue_ind; intros.
  - eexists; split; eauto. econstructor; simpl; eauto. ld_rew.
  - eexists; split; eauto. econstructor; simpl; eauto. ld_rew.
  - eexists; split; eauto. econstructor; simpl; eauto. ld_rew.
  - eexists; split; eauto. econstructor; simpl; eauto. ld_rew.
  - specialize (TEE id); rewrite H in TEE.
    destruct (le'!id) eqn:?; try tauto.
    eexists; split; eauto. econstructor; simpl; eauto. 
  - destruct H0 as [v' [A B]].
    eexists; split; eauto. econstructor; simpl; eauto.
  - destruct H0 as [v' [A B]].
    eexists; split. econstructor; simpl; eauto.
    subst.
    apply sem_unary_operation_expr_ld; auto.
  - destruct H0 as [v' [A B]].
    destruct H2 as [v'' [C D]].
    generalize (sem_binary_operation_expr_ld op (typeof a1) (typeof a2) _ _ _ _ B D).
    rewrite H3.
    destr_cond_match; try tauto.
    intro; eexists; split; eauto. econstructor; simpl; eauto.
  - destruct H0 as [v' [A B]].
    generalize (sem_cast_expr_ld (typeof a) ty _ _ B).
    rewrite H1. destr_cond_match; try tauto.
    eexists; split; eauto. econstructor; simpl; eauto.
  - destruct H0 as [v' [A B]].
    eapply deref_loc_se in H1; eauto.
    destruct H1 as [tv [C D]].
    eexists; split; eauto. econstructor; simpl; eauto.
  - eexists; split; eauto. econstructor; simpl; eauto.  ld_rew.
  - eexists; split; eauto. eapply eval_Evar_global; eauto.  ld_rew. 
  - destruct H0 as [v' [A B]].
    eexists; split; eauto.
    econstructor. eauto.
  - destruct H0 as [v' [A B]].
    eexists; split.
    econstructor; eauto.  ld_rew.
  - destruct H0 as [v' [A B]].
    eexists; split; eauto.
    econstructor; eauto.
Qed.


Lemma mem_temp_equiv_expr:
  forall ge e le le' m m',
    mem_rel mr m m' ->
    temp_env_equiv le le' ->
    forall a v,
      Clight.eval_expr ge e le m a v ->
      exists v',
        Clight.eval_expr ge e le' m' a v' /\
        mr  v v'.
Proof.
  intros ge0 e le le' m m' ME TEE.
  apply (proj1 (mem_temp_equiv_expr_lvalue ge0 e _ _ _ _ ME TEE)).
Qed.
    
Lemma mem_temp_equiv_lvalue:
  forall ge e le le' m m',
    mem_rel mr m m' ->
    temp_env_equiv le le' ->
    forall a v,
      Clight.eval_lvalue ge e le m a v ->
      exists v',
        Clight.eval_lvalue ge e le' m' a v' /\
        mr v v'.
Proof.
  intros ge0 e le le' m m' ME TEE.
  apply (proj2 (mem_temp_equiv_expr_lvalue ge0 e _ _ _ _ ME TEE)).
Qed.


Lemma list_forall2_ld_trans:
  forall l1 l2,
    list_forall2 mr l1 l2 ->
    forall l3, 
    list_forall2 mr l2 l3 ->
    list_forall2 mr l1 l3.
Proof.
  induction 1; simpl; intros; eauto.
  inv H1.
  constructor.
  eapply mr_trans; eauto.
  eapply IHlist_forall2; eauto.
Qed.

Lemma mem_temp_equiv_exprlist:
  forall ge e le m al tl vl le' m',
    mem_rel mr m m' ->
    temp_env_equiv le le' ->
    eval_exprlist ge e le m al tl vl ->
    exists vl',
      eval_exprlist ge e le' m' al tl vl' /\
      list_forall2 mr vl vl'.
Proof.
  intros ge0 e le m al tl vl le' m' ME TEE EEL.
  eapply temp_equiv_clight_eval_exprlist in EEL; eauto.
  destruct EEL as [vl' [EEL B]].
  eapply mem_equiv_clight_eval_exprlist in EEL; eauto.
  destruct EEL as [vl2' [EEL C]].
  eexists; split; eauto.
  eapply list_forall2_ld_trans; eauto.
Qed.

End RelClight.