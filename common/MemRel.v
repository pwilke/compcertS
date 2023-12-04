
Require Import Zwf.
Require Import Axioms.
Require Import Coqlib.
Require Import Fappli_IEEE_bits.
Require Import Psatz.
Require Import PP.PpsimplZ.

Require Intv.
Require Import Maps.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Values_symbolictype.
Require Import Values_symbolic.
Require Export Memtype.
Require Import IntFacts.
Require Import Normalise.
Require Import NormaliseSpec.
Require Export Memdata.
Require Import Alloc.
Require Import Permutation.
Require Import ExprEval.
Require Export Memperm.
Require Import Memory Tactics.

Import Mem.

(** We lift this equivalence to memories. In addition to the equivalence of the
    contents, we demand that permissions, bounds, masks and next blocks are
    identical in both memories. *)

Record mem_rel (mr: expr_sym -> expr_sym -> Prop) (m1 m2: mem) : Prop :=
  mk_mem_equiv
    { mem_contents_eq :
        forall (b : positive) (ofs : ZIndexed.t),
          Mem.perm m1 b ofs Cur Readable ->
          memval_rel mr
            (ZMap.get ofs (Mem.mem_contents m1) !! b)
            (ZMap.get ofs (Mem.mem_contents m2) !! b);
      mem_access_eq : forall b, (Mem.mem_access m1) !! b = (Mem.mem_access m2) !! b;
      mem_blocksize_eq : forall b, (Mem.mem_blocksize m1) !! b = (Mem.mem_blocksize m2) !! b;
      mem_blocktype_eq : forall b, (Mem.mem_blocktype m1) !! b = (Mem.mem_blocktype m2) !! b;
      mem_mask_eq : forall b, (Mem.mem_mask m1) !! b = (Mem.mem_mask m2) !! b;
      mem_nextblock_eq : Mem.nextblock m1 = Mem.nextblock m2;
      mem_nb_extra_eq: Mem.nb_extra m1 = Mem.nb_extra m2
    }.

Definition mem_equiv := mem_rel same_eval.
Definition mem_lessdef := mem_rel Val.lessdef.

Lemma mem_equiv_refl:
  forall m mr (WF: wf_mr mr),
    mem_rel mr m m.
Proof.
  intros. inv WF.
  constructor; intros; simpl; try tauto.
  unfold memval_rel. split; eauto.
  left; red. destr.
Qed.


Lemma perm_rel:
  forall m m' mr (ME: mem_rel mr m m') b ofs k p,
    Mem.perm m b ofs k p <->
    Mem.perm m' b ofs k p.
Proof.
  intros.
  inv ME. unfold perm. rewrite <- mem_access_eq0.
  tauto.
Qed.

Lemma mem_equiv_sym:
  forall m1 m2,
    mem_equiv m1 m2 ->
    mem_equiv m2 m1.
Proof.
  intros m1 m2 A; constructor; intros; try (inv A; congruence).
  - destruct (mem_contents_eq _ _ _ A b ofs) as [B C].
    rewrite perm_rel; eauto. red; split; eauto.
    rewrite B; reflexivity.
    unfold same_type_memval in *.
    destr. destr.
  - inv A. auto.
Qed.

Lemma mem_equiv_trans:
  forall m1 m2 m3,
    mem_equiv m1 m2 ->
    mem_equiv m2 m3 ->
    mem_equiv m1 m3.
Proof.
  intros m1 m2 m3 A B. constructor; try (inv A; inv B; congruence).
  - intros.
    destruct (mem_contents_eq _ _ _ A b ofs) as [C D]; auto.
    destruct (mem_contents_eq _ _ _ B b ofs) as [E F].
    rewrite <- perm_rel; eauto.
    split. rewrite C, E; reflexivity.
    unfold same_type_memval in *; repeat destr.
    destr_in F.
  - intros.
    rewrite (mem_access_eq _ _ _ A), (mem_access_eq _ _ _ B); auto.
Qed.

Instance mem_equiv_equi : RelationClasses.Equivalence mem_equiv.
Proof.
  constructor; red.
  intros; apply mem_equiv_refl. apply wf_mr_se.
  apply mem_equiv_sym.
  apply mem_equiv_trans.
Qed.

Lemma mem_lessdef_refl:
  forall m,
    mem_lessdef m m.
Proof.
  constructor; intros; simpl; try tauto.
  split. constructor.
  left; red.  destr.
Qed.

Lemma mem_lessdef_trans:
  forall m1 m2 m3,
    mem_lessdef m1 m2 ->
    mem_lessdef m2 m3 ->
    mem_lessdef m1 m3.
Proof.
  intros m1 m2 m3 A B. constructor; try (inv A; inv B; congruence).
  - intros.
    destruct (mem_contents_eq _ _ _ A b ofs) as [C D]; auto.
    destruct (mem_contents_eq _ _ _ B b ofs) as [E F].
    rewrite <- perm_rel; eauto.
    split.
    eapply Val.lessdef_trans; eauto. 
    unfold same_type_memval in *; repeat destr.
    destr_in D. des D. des F.
    right; red; intros.
    specialize (C cm em). rewrite <- s in C. inv C; auto.
    simpl. rewrite H2. auto.
  - intros.
    rewrite (mem_access_eq _ _ _ A), (mem_access_eq _ _ _ B); auto.
Qed.

Instance mem_lessdef_equi : RelationClasses.PreOrder mem_lessdef.
Proof.
  constructor; red.
  apply mem_lessdef_refl.
  apply mem_lessdef_trans.
Qed.

Lemma mem_eq_ld_trans:
  forall m1 m2 m3,
    mem_equiv m1 m2 ->
    mem_lessdef m2 m3 ->
    mem_lessdef m1 m3.
Proof.
  intros m1 m2 m3 ME MLD.
  (* inv ME; inv MLD. *)
  constructor; simpl; intros; try (inv ME; inv MLD; congruence).
  - destruct (mem_contents_eq _ _ _ ME b ofs) as [A B]; auto.
    destruct (mem_contents_eq _ _ _ MLD b ofs) as [C D].
    rewrite <- perm_rel; eauto.
    split; intros.
    eapply Val.lessdef_trans; [|eauto].
    red; intros; rewrite A; constructor.
    unfold same_type_memval in *; repeat destr. destr_in D.
  - inv ME; inv MLD. rewrite mem_access_eq0, mem_access_eq1; auto.
Qed.


Lemma compat_mem_rel:
  forall mr m m'
    (MR: mem_rel mr m m')
    cm,
    compat_m m M32 cm <-> compat_m m' M32 cm.
Proof.
  intros. apply same_compat_bounds_mask.
  unfold bounds_of_block; intros; inv MR; rewrite mem_blocksize_eq0; eauto.
  unfold nat_mask, mask; intros; inv MR; rewrite mem_mask_eq0; eauto.
Qed.


Lemma good_result_m_rel:
  forall mr m m' e v
    (MR: mem_rel mr m m'),
    good_result_m m e v <->
    good_result_m m' e v.
Proof.
  intros.
  apply good_result_m_same_compat.
  eapply compat_mem_rel; eauto.
Qed.


Lemma is_norm_m_rel:
  forall mr m m' e v
    (MR: mem_rel mr m m'),
    is_norm_m m e v <->
    is_norm_m m' e v.
Proof.
  intros.
  apply is_norm_m_same_compat.
  apply (compat_mem_rel _ _ _ MR).
Qed.

Lemma mem_rel_norm:
  forall mr m m' e,
    mem_rel mr m m' ->
    Mem.mem_norm m e = Mem.mem_norm m' e.
Proof.
  intros mr m m' e ME.
  generalize (norm_correct m e) (norm_correct m' e).
  intros A B.
  apply lessdef_antisym; apply norm_complete.
  rewrite <- is_norm_m_rel; eauto.
  rewrite is_norm_m_rel; eauto.
Qed.

Lemma valid_block_rel:
  forall m m' mr (ME: mem_rel mr m m') b
    (VB: Mem.valid_block m b),
    Mem.valid_block m' b.
Proof.
  red; intros.
  inv ME. rewrite <- mem_nextblock_eq0.
  apply VB.
Qed.


Lemma range_perm_mem_rel:
  forall mr m m' b o n k p,
    mem_rel mr m m' ->
    Mem.range_perm m b o n k p ->
    Mem.range_perm m' b o n k p.
Proof.
  red; intros.
  red. red.
  inv H. rewrite <- mem_access_eq0.
  apply H0; auto.
Qed.

Lemma mem_rel_valid_access:
  forall mr chunk m m' b o p,
    mem_rel mr m m' ->
    Mem.valid_access m chunk b o p ->
    Mem.valid_access m' chunk b o p.
Proof.
  intros mr chunk m m' b o p ME VA.
  red in VA; red.
  destruct VA; split; auto.
  red; intros.
  red. red.
  inv ME.
  rewrite <- mem_access_eq0.
  apply H; auto.
Qed.

Lemma memval_rel_lf2:
  forall mr n o t t' b,
    (forall (ofs : ZIndexed.t),
        o <= ofs < o + Z.of_nat n ->
       memval_rel mr (ZMap.get ofs t !! b)
                    (ZMap.get ofs t' !! b)) ->
    list_forall2 (memval_rel mr)
                 (Mem.getN n o t !! b)
                 (Mem.getN n o t' !! b).
Proof.
  induction n; simpl; intros; constructor; auto.
  apply H. lia.
  apply IHn; auto.
  intros; apply H. lia.
Qed.


Lemma mem_rel_load:
  forall mr (WF: wf_mr mr) chunk m m' b o v,
    mem_rel mr m m' ->
    Mem.load chunk m b o = Some v ->
    exists v',
      Mem.load chunk m' b o = Some v' /\
      mr v v'.
Proof.
  intros mr WF chunk m m' b o v ME LOAD.
  destruct (Mem.valid_access_load m' chunk b o).
  eapply mem_rel_valid_access; eauto.
  eapply Mem.load_valid_access; eauto.
  eexists; split; eauto.
  Transparent Mem.load.
  unfold Mem.load in H, LOAD.
  revert LOAD; destr_cond_match;
  revert H; destr_cond_match; intros; try discriminate.
  inv H; inv LOAD.
  inv ME.
  eapply decode_val_eSexpr; eauto.
  apply memval_rel_lf2.
  intros; apply mem_contents_eq0. auto.
  des v0.
  apply r.
  rewrite size_chunk_conv. auto.
Qed.

Lemma loadv_mem_rel:
  forall mr (WF: wf_mr mr) m m' chunk ptr v,
    mem_rel mr m m' ->
    Mem.loadv chunk m ptr = Some v ->
    exists v',
      Mem.loadv chunk m' ptr = Some v' /\
      mr v v'.
Proof.
  intros mr Wf m m' chunk ptr v ME LV.
  unfold Mem.loadv in *.
  revert LV; destr_cond_match; try discriminate.
  intros.
  generalize (mem_rel_norm _ _ _ ptr ME).
  rewrite Heqv0. intro A; rewrite <- A.
  eapply mem_rel_load; eauto.
Qed.

Definition wf_mr_norm (mr: expr_sym -> expr_sym -> Prop) : Prop :=
  forall m v1 v2 (REL: mr v1 v2),
    mr (Eval (mem_norm m v1)) (Eval (mem_norm m v2)).

Lemma wf_mr_norm_se: wf_mr_norm same_eval.
Proof.
  red; intros.
  erewrite (same_eval_eqm _ _ _ REL); eauto.
  red; auto.
Qed.

Lemma wf_mr_norm_ld: wf_mr_norm Val.lessdef.
Proof.
  red; intros.
  exploit lessdef_eqm; eauto.
  intro A; inv A. rewrite H1; auto. rewrite <- H0; red; auto.
Qed.

Lemma rel_norm:
  forall mr (wf: wf_mr mr) (wfn: wf_mr_norm mr) m m' v v',
    mem_rel mr m m' ->
    mr v v' ->
    mr (Eval (Mem.mem_norm m v)) (Eval (Mem.mem_norm m' v')).
Proof.
  intros mr wf wfn m m' v v' ME LD.
  erewrite mem_rel_norm; eauto.
Qed.


Lemma loadv_addr_rel:
  forall mr (wf: wf_mr mr) (wfn: wf_mr_norm mr) m m' chunk ptr ptr' v,
    mem_rel mr m m' ->
    Mem.loadv chunk m ptr = Some v ->
    mr ptr ptr' ->
    exists v',
      Mem.loadv chunk m' ptr' = Some v' /\ mr v v'.
Proof.
  intros mr wf wfn m m' chunk ptr ptr' v MLD LV VLD.
  exploit loadv_mem_rel; eauto.
  intros [v' [A B]].
  exists v'; split; auto.
  revert A.
  unfold Mem.loadv.

  generalize (rel_norm _ wf wfn _ _ _ _ MLD VLD).
  rewrite (mem_rel_norm _ _ _ _ MLD).
  des (mem_norm m' ptr).
  inv wf. intros. apply mr_val_refl in H; try rewrite <- H; destr. 
Qed.

Lemma mem_rel_loadbytes:
  forall mr m m' b o n v,
    mem_rel mr m m' ->
    Mem.loadbytes m b o n = Some v ->
    exists v',
      Mem.loadbytes m' b o n = Some v' /\
      list_forall2 (memval_rel mr) v v'.
Proof.
  intros mr m m' b o n v ME LOAD.
  destruct (zle 0 n).
  destruct (Mem.range_perm_loadbytes m' b o n).
  eapply range_perm_mem_rel; eauto.
  eapply Mem.loadbytes_range_perm; eauto.
  eexists; split; eauto.
  Transparent Mem.loadbytes.
  unfold Mem.loadbytes in H, LOAD.
  revert LOAD; destr_cond_match;
  revert H; destr_cond_match; intros; try discriminate.
  inv H; inv LOAD.
  apply memval_rel_lf2. intros.
  apply mem_contents_eq; auto.
  apply r. rewrite nat_of_Z_eq in H; auto. lia.
  rewrite loadbytes_empty in * by lia. inv LOAD.
  eexists; split; eauto. constructor.
Qed.

Definition opt_mem_rel mr m1 m2 : Prop :=
  match m1, m2 with
      None, None => True
    | Some mm1, Some mm2 => mem_rel mr mm1 mm2
    | _, _ => False
  end.

Definition opt_mem_equiv := opt_mem_rel same_eval.
Definition opt_mem_lessdef := opt_mem_rel Val.lessdef. 

Lemma ome_omld:
  forall m1 m2,
    opt_mem_equiv m1 m2 ->
    opt_mem_lessdef m1 m2.
Proof.
  intros m1 m2 A.
  des m1; des m2; inv A; auto.
  constructor; intros; auto.
  specialize (mem_contents_eq0 b ofs).
  repeat red in mem_contents_eq0.
  red; intros.
  destruct mem_contents_eq0. auto. split.
  - red; intros. rewrite H0; auto.
  - destr.
Qed.

Local Notation "a # b" := (PMap.get b a) (at level 1).

Lemma met_rel:
  forall mr (wf: wf_mr mr) i1 i2,
    list_forall2 (memval_rel mr) i1 i2 ->
    forall m b ofs b0 ofs0,
    memval_rel mr
      (ZMap.get ofs0 ((PMap.set b (setN i1 ofs (mem_contents m) # b) (mem_contents m)) # b0))
      (ZMap.get ofs0 ((PMap.set b (setN i2 ofs (mem_contents m) # b) (mem_contents m)) # b0)).
Proof. 
  intros.
  repeat rewrite PMap.gsspec.
  destr; subst.
  assert ((ofs0 < ofs \/ ofs0 >= ofs + Z.of_nat (length i1)) \/
          ofs <= ofs0 < ofs + Z.of_nat (length i1)).
  intuition omega.
  destruct H0.
  rewrite setN_outside; auto.
  rewrite setN_outside.
  inv wf; eauto. split. apply mr_refl. left; apply same_type_memval_refl.
  rewrite <- (list_forall2_length H). auto.
  generalize (mem_contents m) # b. 
  revert i1 i2 H ofs ofs0 H0.
  clear -wf.  induction 1; simpl; intros.
  - unfold memval_equiv; destr. inv wf; split. apply mr_refl. left; apply same_type_memval_refl.
  - destruct (Z_eq_dec ofs0 ofs); subst.
    + repeat rewrite setN_outside by omega.
      repeat rewrite ZMap.gss. auto.
    + repeat rewrite get_setN_not_last; auto; try omega.
      apply IHlist_forall2. zify; omega.
  - inv wf; split. apply mr_refl. left; apply same_type_memval_refl.
Qed.

Transparent store.

Theorem store_int8_zero_ext:
  forall mr (wf: wf_mr mr) m b ofs n,
    opt_mem_rel mr
      (store Mint8unsigned m b ofs (Eval (Vint (Int.zero_ext 8 n))))
      (store Mint8unsigned m b ofs (Eval (Vint n))).
Proof. 
  intros. 
  unfold store.
  destr. simpl. destr.
  constructor; simpl; auto.
  intros; apply met_rel; auto.
  apply encode_val_int8_zero_ext; auto.
Qed.

Theorem store_int8_sign_ext:
  forall mr (wf: wf_mr mr) m b ofs n,
    opt_mem_rel mr
      (store Mint8signed m b ofs (Eval (Vint (Int.sign_ext 8 n))))
      (store Mint8signed m b ofs (Eval (Vint n))).
Proof. 
  intros. 
  unfold store.
  destr. constructor; simpl; auto. 
  intros; apply met_rel; auto.
  apply encode_val_int8_sign_ext; auto.
Qed.

Theorem store_int16_zero_ext:
  forall mr (wf: wf_mr mr) m b ofs n,
    opt_mem_rel mr
      (store Mint16unsigned m b ofs (Eval (Vint (Int.zero_ext 16 n))))
      (store Mint16unsigned m b ofs (Eval (Vint n))).
Proof.
  intros. 
  unfold store.
  destr; constructor; destr.
  intros; apply met_rel; auto.
  apply encode_val_int16_zero_ext; auto.
Qed.

Theorem store_int16_sign_ext:
  forall mr (wf: wf_mr mr) m b ofs n,
    opt_mem_rel mr
      (store Mint16signed m b ofs (Eval (Vint (Int.sign_ext 16 n))))
      (store Mint16signed m b ofs (Eval (Vint n))).
Proof. 
  intros. 
  unfold store.
  destr; constructor; destr.
  intros; apply met_rel; auto.
  apply encode_val_int16_sign_ext; auto.
Qed.


Lemma storebytes_val_rel:
  forall mr (wf: wf_mr mr) m1 b ofs bytes m2,
    Mem.storebytes m1 b ofs bytes = Some m2 ->
    forall bytes',
      list_forall2 (memval_rel mr) bytes bytes' ->
      exists m2',
        Mem.storebytes m1 b ofs bytes' = Some m2' /\
        mem_rel mr m2 m2'.
Proof.
  intros mr wf m1 b ofs bytes m2 STORE.
  intros bytes' SE.
  generalize (storebytes_range_perm _ _ _ _ _ STORE).
  rewrite  (list_forall2_length SE) .
  intro A; apply (range_perm_storebytes) in A.
  destruct A.
  (exists x; split; auto).
  constructor.
  - erewrite storebytes_mem_contents; eauto.
    erewrite (storebytes_mem_contents _ _ _ _ _ e); eauto.
    intros.
    apply memval_rel_set'; auto.
    inv wf; eauto. intros. split. apply mr_refl. left; apply same_type_memval_refl.
  - apply Mem.storebytes_access in e.
    apply Mem.storebytes_access in STORE.
    congruence.
  - 
    Transparent Mem.storebytes.
    unfold Mem.storebytes in *.
    repeat (revert e; destr_cond_match; intuition try discriminate).
    repeat (revert e0; destr_cond_match; intuition try discriminate).
    repeat (revert STORE; destr_cond_match; intuition try discriminate).
    inv e; inv STORE; simpl; auto.
  - unfold Mem.storebytes in *.
    repeat (revert e; destr_cond_match; intuition try discriminate).
    repeat (revert e0; destr_cond_match; intuition try discriminate).
    repeat (revert STORE; destr_cond_match; intuition try discriminate).
    inv e; inv STORE; simpl; auto.
  - unfold Mem.storebytes in *.
    repeat (revert e; destr_cond_match; intuition try discriminate).
    repeat (revert e0; destr_cond_match; intuition try discriminate).
    repeat (revert STORE; destr_cond_match; intuition try discriminate).
    inv e; inv STORE; simpl; auto.
  - apply Mem.nextblock_storebytes in e.
    apply Mem.nextblock_storebytes in STORE.
    congruence.
  - revert e STORE.
    unfold storebytes. repeat destr. intros A B; inv A; inv B. reflexivity.
Qed.

Lemma lf2_rel_refl:
  forall mr (wf: wf_mr mr) v,
    list_forall2 (memval_rel mr) v v.
Proof.
  intros mr wf; inv wf; induction v; simpl; intros; constructor; eauto.
  split. apply mr_refl. left; apply same_type_memval_refl.
Qed.

Lemma memval_rel_set':
  forall (access: block -> Z -> Prop)
         mr v v' ofs o t t' b b0,
    ( o <= ofs < o + Z.of_nat (length v) ->
                 memval_rel mr (ZMap.get ofs t !! b0) ( ZMap.get ofs t' !! b0)) ->
    (forall b' ofs, b' <> b \/ o > ofs \/ ofs >= o + Z.of_nat (length v) ->
                    access b' ofs ->
                    memval_rel mr (ZMap.get ofs t !! b') (ZMap.get ofs t' !! b')) ->
    list_forall2 (memval_rel mr) v v' ->
    access b0 ofs ->
    memval_rel mr
      (ZMap.get
         ofs
         (PMap.set b (Mem.setN v o t !! b) t) !! b0)
      (ZMap.get
         ofs
         (PMap.set b (Mem.setN v' o t' !! b) t') !! b0).
Proof.
  intros access mr v v' ofs o t t' b b0 ME ME' SE ACC.
  rewrite ! PMap.gsspec.
  destruct (peq b0 b); subst; try tauto; auto.
  assert (range: forall a b c, a <= b < c \/ (a > b \/ c <= b)) by (intros; omega).
  destruct (range o ofs (o + Z.of_nat (length v))).
  + generalize (Mem.get_setN_inside _ _ _ t !! b H).
    assert (o <= ofs < o + Z.of_nat (length v')).
    { rewrite <- (list_forall2_length SE); eauto. }
    generalize (Mem.get_setN_inside _ _ _ t' !! b H0).
    intros.
    eapply nth_error_property; eauto.
  + rewrite ! Mem.setN_outside; auto. 3: lia.
    2: rewrite <- (list_forall2_length SE); eauto. 2: lia.
    apply ME'. intuition. auto.
Qed.


Lemma storebytes_mem_rel:
  forall mr (wf: wf_mr mr) m m' b o v m1,
    mem_rel mr m m' ->
    Mem.storebytes m b o v = Some m1 ->
    exists m2,
      Mem.storebytes m' b o v = Some m2 /\
      mem_rel mr m1 m2.
Proof.
  intros mr wf m m' b o v  m1 ME STORE.
  generalize STORE; intro STORE0.
  generalize STORE; intro STORE1.
  apply Mem.storebytes_range_perm in STORE.
  generalize (range_perm_mem_rel _ _ _ _ _ _ _ _ ME STORE).
  intros.
  destruct (Mem.range_perm_storebytes _ _ _ _ H).
  eexists; split; eauto. 
  constructor; auto.
  - intros. apply Mem.storebytes_mem_contents in e.
    apply Mem.storebytes_mem_contents in STORE0.
    intros.
    rewrite e. rewrite STORE0.
    apply memval_rel_set' with (access := fun b ofs => perm m1 b ofs Cur Readable).
    + intros. eapply mem_contents_eq. auto.
      eapply perm_storebytes_2; eauto.
    + intros. eapply mem_contents_eq. auto.
      eapply perm_storebytes_2; eauto.
    + apply lf2_rel_refl; auto.
    + auto.
  - apply Mem.storebytes_access in e.
    apply Mem.storebytes_access in STORE0.
    intro; 
    inv ME. rewrite e, STORE0. rewrite <-  mem_access_eq0; auto.
  - 
    unfold Mem.storebytes in *.
    repeat (revert e; destr_cond_match; intuition try discriminate).
    repeat (revert STORE0; destr_cond_match; intuition try discriminate).
    repeat (revert e0; destr_cond_match; intuition try discriminate).
    inv e; inv STORE0; simpl; auto.
    inv ME; auto.
  - 
    unfold Mem.storebytes in *.
    repeat (revert e; destr_cond_match; intuition try discriminate).
    repeat (revert STORE0; destr_cond_match; intuition try discriminate).
    repeat (revert e0; destr_cond_match; intuition try discriminate).
    inv e; inv STORE0; simpl; auto.
    inv ME; auto.
  - 
    unfold Mem.storebytes in *.
    repeat (revert e; destr_cond_match; intuition try discriminate).
    repeat (revert STORE0; destr_cond_match; intuition try discriminate).
    repeat (revert e0; destr_cond_match; intuition try discriminate).
    inv e; inv STORE0; simpl; auto.
    inv ME; auto.
  - apply Mem.nextblock_storebytes in e.
    apply Mem.nextblock_storebytes in STORE0.
    inv ME; congruence.
  - revert e STORE0.
    unfold storebytes. repeat destr. intros A B; inv A; inv B. simpl. inv ME; auto. 
Qed.


Lemma storebytes_rel:
  forall mr (wf: wf_mr mr) m m' b o v v' m1,
    mem_rel mr m m' ->
    Mem.storebytes m b o v = Some m1 ->
    list_forall2 (memval_rel mr) v v' ->
    exists m2,
      Mem.storebytes m' b o v' = Some m2 /\
      mem_rel mr m1 m2.
Proof.
  intros mr wf m m' b o v v' m1 ME STORE LF.
  generalize STORE; intro STORE0.
  generalize STORE; intro STORE1.
  apply Mem.storebytes_range_perm in STORE.
  generalize (range_perm_mem_rel _ _ _ _ _ _ _ _ ME STORE).
  intros.
  destruct (Mem.range_perm_storebytes _ _ _ _ H).
  unfold storebytes.
  destr.
  eexists; split; eauto. 
  constructor; simpl; intros; auto.
  - intros. apply Mem.storebytes_mem_contents in e.
    apply Mem.storebytes_mem_contents in STORE0.
    intros.
    rewrite STORE0.
    apply memval_rel_set' with (access := fun b ofs => perm m b ofs Cur Readable); auto.
    + intros. eapply mem_contents_eq. auto.
      eapply perm_storebytes_2; eauto.
    + intros. eapply mem_contents_eq. auto. auto.
    + eapply perm_storebytes_2; eauto.
  
  - apply Mem.storebytes_access in e.
    apply Mem.storebytes_access in STORE0.
    inv ME.
    rewrite STORE0; auto.
  - 
    unfold Mem.storebytes in *.
    repeat (revert e; destr_cond_match; intuition try discriminate).
    repeat (revert STORE0; destr_cond_match; intuition try discriminate).
    repeat (revert e0; destr_cond_match; intuition try discriminate).
    inv e; inv STORE0; simpl; auto.
    inv ME; auto.
  - 
    unfold Mem.storebytes in *.
    repeat (revert e; destr_cond_match; intuition try discriminate).
    repeat (revert STORE0; destr_cond_match; intuition try discriminate).
    repeat (revert e0; destr_cond_match; intuition try discriminate).
    inv e; inv STORE0; simpl; auto.
    inv ME; auto.
  - 
    unfold Mem.storebytes in *.
    repeat (revert e; destr_cond_match; intuition try discriminate).
    repeat (revert STORE0; destr_cond_match; intuition try discriminate).
    repeat (revert e0; destr_cond_match; intuition try discriminate).
    inv e; inv STORE0; simpl; auto.
    inv ME; auto.
  - apply Mem.nextblock_storebytes in e.
    apply Mem.nextblock_storebytes in STORE0.
    inv ME; congruence.
  - revert e STORE0.
    unfold storebytes. repeat destr. intros A B; inv A; inv B. simpl. inv ME; auto. 


  - apply list_forall2_length in LF.
    congruence.
Qed.

Lemma mk_block_list_rel:
  forall mr m m',
    mem_rel mr m m' ->
    mk_block_list m = mk_block_list m'.
Proof.
  unfold mk_block_list. intros.
  inv H. rewrite mem_nextblock_eq0.
  apply mk_block_list_aux_ext.
  unfold size_block. intros. unfold get_size.
  rewrite mem_blocksize_eq0. auto.
Qed.

Lemma nb_blocks_used_rel:
  forall mr m m',
    mem_rel mr m m' ->
    nb_boxes_used_m m = nb_boxes_used_m m'.
Proof.
  unfold nb_boxes_used_m.
  intros.
  rewrite (mk_block_list_rel _ _ _ H).
  inv H; auto.
Qed.

Lemma alloc_mem_rel:
  forall mr (wf: wf_mr mr) m lo hi b m2 bt,
    Mem.alloc m lo hi bt = Some (m2,b) ->
    forall m',
      mem_rel mr m m' ->
      exists m2',
        Mem.alloc m' lo hi bt = Some (m2',b) /\
        mem_rel mr m2 m2'.
Proof.
  intros mr wf m lo hi b m2 bt ALLOC m' ME.
  Transparent Mem.alloc.
  unfold Mem.alloc, Mem.low_alloc in *.
  destr_in ALLOC. inv ALLOC.
  destr; generalize (nb_blocks_used_rel _ _ _ ME).
  eexists; split; eauto.
  inv ME; rewrite mem_nextblock_eq0.
  f_equal.
  inv ME. constructor; simpl; intros; eauto; try intuition congruence.
  red; intros; simpl; auto.
  - 
    rewrite ! PMap.gsspec.
    rewrite mem_nextblock_eq0.
    destruct (peq b (Mem.nextblock m')).
    + subst. inv wf; split. apply mr_refl. left; apply same_type_memval_refl.
    + apply mem_contents_eq0.
      unfold perm in *; simpl in *. rewrite PMap.gso in H0; auto.
      destr.
  - rewrite ! PMap.gsspec. rewrite mem_access_eq0; eauto.
    rewrite mem_nextblock_eq0; eauto.
  - rewrite ! PMap.gsspec. 
    rewrite mem_nextblock_eq0; eauto.
    eauto. destr.
  - rewrite ! PMap.gsspec. 
    rewrite mem_nextblock_eq0; eauto.
    eauto. destr.
  - rewrite mem_nextblock_eq0.
    rewrite ! PMap.gsspec.  destr.
  - intros; exfalso; lia.
Qed.

Lemma free_mem_rel:
  forall mr b lo hi m m' m2,
    mem_rel mr m m' ->
    Mem.free m b lo hi = Some m2 ->
    exists m2',
      Mem.free m' b lo hi = Some m2' /\
      mem_rel mr m2 m2'.
Proof.
  intros mr b lo hi m m' m2 ME FREE.
  destruct (Mem.range_perm_free m' b lo hi).
  eapply range_perm_mem_rel; eauto.
  eapply Mem.free_range_perm; eauto.
  Transparent Mem.free.
  unfold free in FREE; repeat destr_in FREE.
  unfold has_bounds in *; repeat destr_in Heqb0.
  unfold bounds_of_block in *.
  erewrite mem_blocksize_eq in Heqp; eauto. rewrite Heqp. rewrite Heqb1. auto.
  eexists; split; eauto.
  unfold Mem.free in *.
  repeat destr_in e. inv e.
  repeat destr_in FREE. inv FREE.
  constructor; 
  unfold Mem.unchecked_free; simpl; intros; eauto.
  - unfold perm in H; simpl in H.
    eapply mem_contents_eq; eauto.
    unfold perm; simpl.
    rewrite PMap.gsspec in H. destr_in H. destr_in H.
  - inv ME. rewrite ! PMap.gsspec. rewrite mem_access_eq0. destr. auto.
  - inv ME. rewrite mem_blocksize_eq0; auto.
    rewrite ! PMap.gsspec. destr.
  - inv ME. rewrite mem_blocktype_eq0; auto.
  - inv ME. rewrite mem_mask_eq0; auto.
  - inv ME. auto.
  - inv ME; auto.
Qed.

Lemma free_list_mem_equiv:
  forall mr bl m m' m2,
    mem_rel mr m m' ->
    Mem.free_list m bl = Some m2 ->
    exists m2',
      Mem.free_list m' bl = Some m2' /\
      mem_rel mr m2 m2'.
Proof.
  induction bl; simpl; intros.
  inv H0.
  eexists; split; eauto.
  destruct a; destruct p.
  revert H0; destr_cond_match; try intuition congruence.
  eapply free_mem_rel in Heqo; eauto.
  destruct Heqo as [m2' [A B]].
  rewrite A.
  intros.
  eapply IHbl; eauto.
Qed.


Lemma mem_equiv_same_eval_norm:
  forall m m' e1 e2,
    mem_equiv m m' ->
    same_eval e1 e2 ->
    Mem.mem_norm m e1 = Mem.mem_norm m' e2.
Proof.
  intros m m' e1 e2 ME SE.
  rewrite (mem_rel_norm _ _ _ _ ME).
  rewrite (Mem.same_eval_eqm _ _ _  SE); auto.
Qed.

Lemma mem_rel_drop_perm:
  forall m m' mr (WF: wf_mr mr) (MR: mem_rel mr m m')
    m1 b lo hi p
    (AB: drop_perm m b lo hi p = Some m1),
  exists m2 ,
    drop_perm m' b lo hi p = Some m2 /\
    mem_rel mr m1 m2.
Proof.
  intros.
  simp AB.
  unfold drop_perm.
  destr.
  eexists; split; eauto.
  constructor; simpl; auto; try (inv MR; simpl; auto).
  - unfold perm; simpl; intros.
    eapply mem_contents_eq0.
    rewrite PMap.gsspec in H; repeat destr_in H.
    apply zle_zlt in Heqb0.
    generalize (r _ Heqb0).
    intros; eapply perm_implies; eauto. constructor.
  - intros. rewrite ! PMap.gsspec. destr.
    rewrite mem_access_eq0. auto. auto.
  - exfalso; apply n. eapply range_perm_mem_rel; eauto.
Qed.

Lemma store_val_rel:
  forall mr (wf: wf_mr mr) m b o chunk v v' m1,
    mr v v' ->
    Mem.store chunk m b o v = Some m1 ->
    exists m2,
      Mem.store chunk m b o v' = Some m2 /\
      mem_rel mr m1 m2.
Proof.
  intros mr wf m b o chunk v v' m1 SE STORE.
  generalize STORE; intro STORE0.
  generalize STORE; intro STORE1.
  apply Mem.store_valid_access_3 in STORE.
  destruct (Mem.valid_access_store _ _ _ _ v' STORE).
  eexists; split; eauto.
  constructor.
  - apply Mem.store_mem_contents in e.
    apply Mem.store_mem_contents in STORE0.
    intros.
    rewrite e. rewrite STORE0.
    apply memval_rel_set' with (access := fun b ofs => perm m1 b ofs Cur Readable); auto.
    + intros. eapply mem_contents_eq. apply mem_equiv_refl. auto. 
      eapply perm_store_2; eauto.
    + intros. eapply mem_contents_eq. apply mem_equiv_refl. auto.
      eapply perm_store_2; eauto.
    + apply encode_val_memval_rel; auto.
    
  - apply Mem.store_access in e.
    apply Mem.store_access in STORE0. congruence.
  -     
    clear - e STORE0.
    Transparent Mem.store.
    unfold Mem.store in *.
    repeat (revert e; destr_cond_match; intuition try discriminate).
    repeat (revert STORE0; destr_cond_match; intuition try discriminate).
    inv e; inv STORE0; simpl; auto.
  - unfold Mem.store in *.
    repeat (revert e; destr_cond_match; intuition try discriminate).
    repeat (revert STORE0; destr_cond_match; intuition try discriminate).
    inv e; inv STORE0; simpl; auto.
  - unfold Mem.store in *.
    repeat (revert e; destr_cond_match; intuition try discriminate).
    repeat (revert STORE0; destr_cond_match; intuition try discriminate).
    inv e; inv STORE0; simpl; auto.
  - apply Mem.nextblock_store in e.
    apply Mem.nextblock_store in STORE0.
    congruence.
  - rewrite <- (nb_extra_store _ _ _ _ _ _ STORE0).
    rewrite <- (nb_extra_store _ _ _ _ _ _ e). auto.
Qed.

Lemma store_mem_rel:
  forall mr (wf: wf_mr mr)  m m' b o chunk v m1,
    mem_rel mr m m' ->
    Mem.store chunk m b o v = Some m1 ->
    exists m2,
      Mem.store chunk m' b o v = Some m2 /\
      mem_rel mr m1 m2.
Proof.
  intros mr wf m m' b o chunk v  m1 ME STORE.
  generalize STORE; intro STORE0.
  generalize STORE; intro STORE1.
  apply Mem.store_valid_access_3 in STORE. 
  edestruct (Mem.valid_access_store m' chunk b o v); eauto.
  eapply mem_rel_valid_access; eauto.
  eexists; split; eauto.
  constructor.
  - apply Mem.store_mem_contents in e.
    apply Mem.store_mem_contents in STORE0.
    intros.
    rewrite e. rewrite STORE0.
    apply memval_rel_set' with (access := fun b ofs => perm m1 b ofs Cur Readable).
    + intros. eapply mem_contents_eq. auto.  
      eapply perm_store_2; eauto.
    + intros. eapply mem_contents_eq. auto.
      eapply perm_store_2; eauto.
    + apply encode_val_memval_rel; auto.
      inv wf; eauto.
    + auto.
  - apply Mem.store_access in e.
    apply Mem.store_access in STORE0.
    inv ME. intros; eauto. rewrite STORE0, e. auto. 
  - clear - e STORE0 ME.
    Transparent Mem.store.
    unfold Mem.store in *.
    repeat (revert e; destr_cond_match; intuition try discriminate).
    repeat (revert STORE0; destr_cond_match; intuition try discriminate).
    inv e; inv STORE0; simpl; auto.
    inv ME; auto.
  - unfold Mem.store in *.
    repeat (revert e; destr_cond_match; intuition try discriminate).
    repeat (revert STORE0; destr_cond_match; intuition try discriminate).
    inv e; inv STORE0; simpl; auto.
    inv ME; auto.
  - unfold Mem.store in *.
    repeat (revert e; destr_cond_match; intuition try discriminate).
    repeat (revert STORE0; destr_cond_match; intuition try discriminate).
    inv e; inv STORE0; simpl; auto.
    inv ME; auto.
  - apply Mem.nextblock_store in e.
    apply Mem.nextblock_store in STORE0.
    inv ME; congruence.
  - rewrite <- (nb_extra_store _ _ _ _ _ _ STORE0).
    rewrite <- (nb_extra_store _ _ _ _ _ _ e). inv ME; auto.
Qed.

Lemma storev_mem_rel:
  forall mr (wf: wf_mr mr) m m' chunk ptr v m2,
    mem_rel mr m m' ->
    Mem.storev chunk m ptr v = Some m2 ->
    exists m2',
      Mem.storev chunk m' ptr v = Some m2' /\
      mem_rel mr m2 m2'.
Proof.
  intros mr wf m m' chunk ptr v m2 ME ST.
  unfold Mem.storev in *.
  revert ST; destr_cond_match; try discriminate.
  intros.
  rewrite <- (mem_rel_norm _ _  _ ptr ME).
  rewrite Heqv0. 
  eapply store_mem_rel; eauto. 
Qed.

Lemma storev_val_rel:
  forall mr (wf: wf_mr mr) m chunk ptr v v' m2,
    mr v v' ->
    Mem.storev chunk m ptr v = Some m2 ->
    exists m2',
      Mem.storev chunk m ptr v' = Some m2' /\
      mem_rel mr m2 m2'.
Proof.
  intros mr wf m chunk ptr v v' m2 SE ST.
  unfold Mem.storev in *.
  revert ST; destr_cond_match; try discriminate.
  intros.
  eapply store_val_rel; eauto.
Qed.

Lemma mem_rel_refl:
  forall mr (wf: wf_mr mr) m,
    mem_rel mr m m.
Proof.
  intros; constructor; simpl; intros; auto.
  apply memval_rel_refl; auto.
Qed.

Lemma store_rel:
  forall mr (wf: wf_mr mr) m m' b o chunk v v' m1
         (MRel: mem_rel mr m m')
         (VRel: mr v v')
         (STORE: store chunk m b o v = Some m1),
  exists m2,
    store chunk m' b o v' = Some m2 /\
    mem_rel mr m1 m2.
Proof.
  intros.
  unfold store in *.
  repeat destr_in STORE. inv STORE.
  exploit mem_rel_valid_access; eauto. intros. destr.
  eexists; split; eauto.
  inversion  MRel. constructor; simpl; auto.
  intros.
  apply memval_rel_set' with (access := fun b o => perm m b o Cur Readable); auto.
  apply encode_val_memval_rel; auto.
Qed.

Lemma storev_rel:
  forall mr (wf: wf_mr mr) (wfn: wf_mr_norm mr) m m' m2 chunk ptr ptr' v v',
    mem_rel mr m m' ->
    Mem.storev chunk m ptr v = Some m2 ->
    mr ptr ptr' ->
    mr  v v' ->
    exists m2',
      Mem.storev chunk m' ptr' v' = Some m2' /\ mem_rel mr m2 m2'.
Proof.
  intros mr wf wfn m m' m2 chunk ptr ptr' v v' MLD STR ALD VLD .
  unfold storev in *.
  generalize (rel_norm _ wf wfn _ _ _ _ MLD ALD).
  des (mem_norm m ptr).
  inversion wf. intro H; apply mr_val_refl in H; destr.
  inv H.
  eapply store_rel; eauto. 
Qed.

Lemma mem_lessdef_bounds:
  forall mr m m' b (MR: mem_rel mr m m'),
    Mem.bounds_of_block m b = Mem.bounds_of_block m' b.
Proof.
  intros mr  m m' b A; inv A; unfold Mem.bounds_of_block.
  rewrite mem_blocksize_eq0. auto.
Qed.


Lemma mem_lessdef_in_bound_m:
  forall mr m m' (MLD: mem_rel mr m m'),
  forall b o, Mem.in_bound_m o m b <-> Mem.in_bound_m o m' b.
Proof.
  split; red; intros; inv MLD; unfold Mem.bounds_of_block.
  rewrite <- mem_blocksize_eq0; auto.
  rewrite mem_blocksize_eq0; auto.
Qed.

Lemma unchecked_free_mem_rel:
  forall mr (wf: wf_mr mr)
    m1 m1' (MR: mem_rel mr m1 m1') b lo hi,
    mem_rel mr (unchecked_free m1 b lo hi)
                (unchecked_free m1' b lo hi).
Proof.
  intros.
  inv MR.
  constructor; simpl; intros; auto.
  apply mem_contents_eq0.
  unfold unchecked_free in H. unfold perm in H. simpl in H.
  rewrite PMap.gsspec in H; repeat destr_in H.
  rewrite ! PMap.gsspec. rewrite mem_access_eq0; auto. destr. auto.
  rewrite ! PMap.gsspec.  rewrite mem_blocksize_eq0; auto. destr; auto.
Qed.

Lemma storebytes_blocktype:
  forall m1 b ofs bytes m2
    (SB: storebytes m1 b ofs bytes = Some m2),
    mem_blocktype m2 = mem_blocktype m1.
Proof.
  intros; unfold storebytes in SB. destr_in SB. inv SB; auto.
Qed.


Theorem storebytes_int64_split:
  forall m b ofs v m' x x0 
    (H : store Mint64 m b ofs v = Some m')
    (SB : storebytes m b ofs (encode_val Mint64 v) = Some m')
    (e : storebytes m b ofs (encode_val Mint32 (if big_endian then Val.hiword v else Val.loword v)) = Some x)
    (e0 : storebytes x b (ofs + 4) (encode_val Mint32 (if big_endian then Val.loword v else Val.hiword v)) = Some x0),
    mem_equiv m' x0.
Proof.  
  intros.
  constructor; simpl; intros; auto.
  - assert (DEC: Decidable.decidable 
                   (b0 <> b
                    \/ ofs0 + size_chunk Mint64 <= ofs
                    \/ ofs + Z.of_nat (length (encode_val Mint64 v)) <= ofs0)).
    {
      unfold Decidable.decidable.
      destruct (eq_block b b0); subst; simpl; auto.
      destruct (Z_le_dec (ofs0 + size_chunk Mint64) ofs); simpl; auto.
      destruct (Z_le_dec (ofs + Z.of_nat (length (encode_val Mint64 v))) ofs0); simpl; auto.
      intuition congruence.
    }
    rewrite (storebytes_mem_contents _ _ _ _ _ SB).
    rewrite (storebytes_mem_contents _ _ _ _ _ e0).
    rewrite (storebytes_mem_contents _ _ _ _ _ e).
    rewrite ! PMap.gss.
    rewrite (encode_val_length) in *.
    change 4 with (Z.of_nat (length (encode_val Mint32 (if big_endian then Val.hiword v else Val.loword v)))).
    rewrite <- setN_concat.
    destruct DEC.
    + rewrite ! PMap.gsspec.
      destr.
      * subst.
        des H1.
        rewrite ! setN_other.
        {
          split.
          - apply same_eval_refl.
          - left; apply same_type_memval_refl.
        }
        {
          intros.
          revert H1.
          rewrite app_length. repeat rewrite encode_val_length. simpl. lia.
        }
        {
          intros. revert H1. rewrite encode_val_length. simpl. lia.
        }
      * split. apply same_eval_refl. left; apply same_type_memval_refl.
    (* + *)
    (*   intros. *)
    (*   revert H1; simpl. *)
    (*   rewrite app_length. repeat rewrite encode_val_length. simpl. lia. *)
    (*   intros. revert H1. rewrite encode_val_length. simpl. lia. *)
    (*   split. apply same_eval_refl. left; apply same_type_memval_refl. rewrite ! PMap.gsspec. destr. subst. rewrite ! setN_other. *)
    (*   split. apply same_eval_refl. left; apply same_type_memval_refl. *)
    (*   intros. revert H1. revert H2. rewrite app_length. *)
    (*   repeat rewrite encode_val_length. simpl. intros; intro; subst ofs0. *)
    (*   apply H1. subst. right. lia. *)
    (*   lia. *)
    (* (* + split.  *) *)
    (* (*   (* revert H1. *) *) *)
    (* (*   (* rewrite app_length. repeat rewrite encode_val_length. simpl. lia. *) *) *)
    (* (*   (* intros. revert H1. rewrite encode_val_length. simpl. lia. *) *) *)
    (* (*   split. apply same_eval_refl. left; apply same_type_memval_refl. *) *)
    (* (*   split. apply same_eval_refl. left; apply same_type_memval_refl. *) *)
    (* (*   split. apply same_eval_refl. left; apply same_type_memval_refl. *) *)

    + assert (b = b0 /\ ofs0 + size_chunk Mint64 > ofs /\ ofs + Z.of_nat (length (encode_val Mint64 v)) > ofs0).
      {
        clear - H1.
        destruct (peq b0 b); subst; auto.
        destruct (zle (ofs0 + size_chunk Mint64) ofs);
          destruct (zle (ofs + Z.of_nat (length (encode_val Mint64 v))) ofs0); auto;
          intuition.
        intuition.
      }
      clear H1; intuition.
      subst.
      rewrite ! PMap.gss.
      apply memval_rel_set. apply wf_mr_se.
      
      unfold encode_val.
      unfold inj_symbolic.
      rewrite <- rev_app_distr.
      apply list_forall2_rev.
      set (f:= (fun x =>
              inj_symbolic'
                (size_chunk_nat Mint32)
                (Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint x)
                None)).
      change
        (list_forall2
           memval_equiv
           (rev_if_be (inj_symbolic' (size_chunk_nat Mint64) (to_bits Mint64 v) None))
           (rev_if_be
              (f (if big_endian then Val.loword v else Val.hiword v)) ++
              rev_if_be
              (f
                 (if big_endian then Val.hiword v else Val.loword v)))). 
      rewrite rib_app.
      apply list_forall2_rib.
      simpl.
      apply list_forall2_sym.
      unfold memval_equiv, memval_rel, same_eval; intros; eauto.
      split; destr.
      des H1. des o. left; red in s; red. repeat destr.
      repeat (constructor; [apply memval_equiv_hiword || apply memval_equiv_loword; auto|]).
  constructor.
  - erewrite (storebytes_access _ _ _ _ _ SB); eauto.
    erewrite (storebytes_access _ _ _ _ _ e0); eauto.
    erewrite (storebytes_access _ _ _ _ _ e); eauto.
  - erewrite (storebytes_blocksize _ _ _ _ _ SB); eauto.
    erewrite (storebytes_blocksize _ _ _ _ _ e0); eauto.
    erewrite (storebytes_blocksize _ _ _ _ _ e); eauto.
  - erewrite (storebytes_blocktype _ _ _ _ _ SB); eauto.
    erewrite (storebytes_blocktype _ _ _ _ _ e0); eauto.
    erewrite (storebytes_blocktype _ _ _ _ _ e); eauto.
  - erewrite (storebytes_mask _ _ _ _ _ SB); eauto.
    erewrite (storebytes_mask _ _ _ _ _ e0); eauto.
    erewrite (storebytes_mask _ _ _ _ _ e); eauto.
  - erewrite (nextblock_storebytes _ _ _ _ _ SB); eauto.
    erewrite (nextblock_storebytes _ _ _ _ _ e0); eauto.
    erewrite (nextblock_storebytes _ _ _ _ _ e); eauto.
  - rewrite <- (nb_extra_storebytes _ _ _ _ _ SB).
    rewrite <- (nb_extra_storebytes _ _ _ _ _ e0).
    rewrite <- (nb_extra_storebytes _ _ _ _ _ e). auto.
Qed.

Theorem store_int64_split:
  forall m b ofs v m',
  store Mint64 m b ofs v = Some m' ->
  exists m1 m2,
     store Mint32 m b ofs (if Archi.big_endian then Val.hiword v else Val.loword v) = Some m1
     /\ store Mint32 m1 b (ofs + 4) (if Archi.big_endian then Val.loword v else Val.hiword v) = Some m2
     /\ mem_equiv m' m2.
Proof.
  intros. 
  exploit store_valid_access_3; eauto. intros [A B]. simpl in *.
  exploit store_storebytes. eexact H. intros SB.
  cut (range_perm m b ofs (ofs+Z.of_nat (length (encode_val Mint32 (if Archi.big_endian then Val.hiword v else Val.loword v)))) Cur Writable). intro.
  apply  range_perm_storebytes in H0; auto. destruct H0.
  cut (range_perm x b (ofs+4) ((ofs+4)+Z.of_nat (length (encode_val Mint32 (if Archi.big_endian then Val.loword v else Val.hiword v)))) Cur Writable). intro.
  apply  range_perm_storebytes in H0. destruct H0.
  erewrite storebytes_store with (m2:=x); eauto.
  exists x.
  erewrite storebytes_store with (m2:=x0); eauto.
  exists x0.
  split; auto. split; auto.
  - rewrite <- be_rew in *.
    eapply storebytes_int64_split; eauto. 
  - simpl.
    apply Zdivide_plus_r.
    apply Zdivides_trans with 8; auto. exists 2; auto.
    exists 1; auto.
  - simpl.
    apply Zdivides_trans with 8; auto. exists 2; auto.
  -  assert (forall b ofs n, range_perm m b ofs (ofs+n) Cur Writable ->
                            range_perm x b ofs (ofs+n) Cur Writable).
    intros.
    revert e; unfold storebytes. destruct range_perm_dec; try congruence.
    intro V; inv V. simpl.
    red; intros.
    red; intros. simpl. apply H0; auto.
    apply H0.
    rewrite encode_val_length; eauto. simpl.
    red; intros.
    apply A. omega.
  - unfold range_perm in *; intros.
    apply A.
    replace (Z.of_nat _) with 4 in H0.    
    simpl in H0. 
    split; try omega.
    erewrite encode_val_length; eauto.
Qed.

Lemma storev_int64_split:
  forall m ptr v m',
    Mem.storev Mint64 m ptr v = Some m' ->
    exists m1 m2,
      Mem.storev Mint32 m ptr (if Archi.big_endian then Val.hiword v else Val.loword v) = Some m1 /\
      Mem.storev Mint32 m1 (Val.add ptr (Eval (Vint (Int.repr 4))))
                 (if Archi.big_endian then Val.loword v else Val.hiword v) = Some m2 /\
      mem_equiv m' m2.
Proof.
  intros m ptr v m' SV.
  revert SV.
  unfold Mem.storev. des (Mem.mem_norm m ptr). intros.
  exploit store_int64_split; eauto. intros (m1 & m2 & B & C & D).
  exists m1, m2.
  cut (Mem.mem_norm m1 (Val.add ptr (Eval (Vint (Int.repr 4)))) = Vptr b (Int.add i (Int.repr 4))).
  intro A; rewrite A.
  replace (Int.unsigned (Int.add i (Int.repr 4))) with (Int.unsigned i + 4).
  auto.
  erewrite Mem.store_int64_eq_add; eauto.
  apply eq_norm; try congruence.
  constructor.
  - red; intros.
    exploit norm_ld; eauto.
    eapply store_compat with (q:=M32); eauto.
    intro E; inv E. simpl. rewrite <- H1. simpl.
    sint. auto.
Qed.

Lemma loadv_se:
  forall c m ptr ptr' v,
    Val.lessdef ptr ptr' ->
    Mem.loadv c m ptr = Some v ->
    Mem.loadv c m ptr' = Some v.
Proof.
  intros c m ptr ptr' v SE.
  unfold Mem.loadv.
  generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ (mem_lessdef_refl m) SE).
  rewrite lessdef_val.
  intro A.
  repeat destr; inv A; auto.
Qed.
