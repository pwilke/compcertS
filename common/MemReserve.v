Require Import Memory.

Import Mem.

Require Import Coqlib AST Values Arith ZArith BinPos Psatz MemRel Permutation Tactics.


Program Definition reserve_boxes (m: mem) (n: nat) : option mem :=
  if zlt (Z.of_nat (nb_boxes_used_m m + n)) nb_boxes_max
  then Some (mkmem (mem_contents m)
                   (mem_access m)
                   (mem_blocksize m)
                   (mem_mask m)
                   (mem_blocktype m)
                   (nextblock m)
                   (nb_extra m + n)
                   _ _ _ _ _ _ _ _ _)
  else None.
Solve Obligations using (destruct m; simpl; auto).
Next Obligation.
  unfold nb_boxes_used_m, mk_block_list in H.
  eapply Z.le_lt_trans. 2: apply H. rewrite plus_assoc. apply Zle_refl.
Qed.


Program Definition release_boxes (m: mem) (n: nat) : option mem :=
  if le_dec n (nb_extra m)
  then Some (mkmem (mem_contents m)
                   (mem_access m)
                   (mem_blocksize m)
                   (mem_mask m)
                   (mem_blocktype m)
                   (nextblock m)
                   (nb_extra m - n)
                   _ _ _ _ _ _ _ _ _)
  else None.
Solve Obligations using (destruct m; simpl; auto).
Next Obligation.
  destruct m. simpl in *.  lia.
Qed.


Lemma release_boxes_rel:
  forall mr m1 m2 (MR: mem_rel mr m1 m2)
    n m1'
    (REL: release_boxes m1 n = Some m1'),
  exists m2',
    release_boxes m2 n = Some m2' /\
    mem_rel mr m1' m2'.
Proof.
  intros.
  unfold release_boxes in *. destr_in REL. inv REL. inv MR. destr. eexists; split; eauto.
  constructor; simpl; auto.
Qed.


Lemma reserve_boxes_rel:
  forall mr m1 m2 (MR: mem_rel mr m1 m2)
    n m1'
    (REL: reserve_boxes m1 n = Some m1'),
  exists m2',
    reserve_boxes m2 n = Some m2' /\
    mem_rel mr m1' m2'.
Proof.
  intros.
  unfold reserve_boxes in *. destr_in REL. inv REL. inversion MR. destr. eexists; split; eauto.
  constructor; simpl; auto.
  exfalso; apply g. clear g.
  eapply Z.le_lt_trans. 2: apply l.
  unfold nb_boxes_used_m.
  replace (mk_block_list m2) with (mk_block_list m1). lia.
  eapply mk_block_list_rel; eauto.
Qed.

Lemma release_load:
  forall m b chunk o n m'
    (MR: release_boxes m n = Some m'),
    Mem.load chunk m b o = Mem.load chunk m' b o.
Proof.
  intros. Transparent Mem.load.
  unfold Mem.load.
  repeat destr.
  - unfold release_boxes in MR; destr_in MR; inv MR.
    simpl. auto.
  - exfalso; apply n0. unfold Mem.valid_access, Mem.range_perm, Mem.perm, release_boxes in *.
    destr_in MR. inv MR. simpl in *. auto.
  - exfalso; apply n0. unfold Mem.valid_access, Mem.range_perm, Mem.perm, release_boxes in *.
    destr_in MR. inv MR. simpl in *. auto.
Qed.


Lemma release_bounds_of_block:
  forall m b n m'
    (MR: release_boxes m n = Some m'),
    Mem.bounds_of_block m b = Mem.bounds_of_block m' b.
Proof.
  intros.
  unfold Mem.bounds_of_block.
  unfold release_boxes in MR; destr_in MR; inv MR.
  reflexivity.
Qed.

Lemma release_mask:
  forall m b n m'
    (MR: release_boxes m n = Some m'),
    Mem.mask m b = Mem.mask m' b.
Proof.
  intros.
  unfold Mem.mask.
  unfold release_boxes in MR; destr_in MR; inv MR.
  reflexivity.
Qed.

Lemma release_is_dynamic_block:
  forall m b n m'
    (MR: release_boxes m n = Some m'),
    Mem.is_dynamic_block m b = Mem.is_dynamic_block m' b.
Proof.
  intros.
  unfold Mem.is_dynamic_block.
  unfold release_boxes in MR; destr_in MR; inv MR.
  reflexivity.
Qed.


Lemma release_nextblock:
  forall m n m'
    (MR: release_boxes m n = Some m'),
    Mem.nextblock m = Mem.nextblock m'.
Proof.
  intros.
  unfold Mem.nextblock.
  unfold release_boxes in MR; destr_in MR; inv MR.
  reflexivity.
Qed.

Lemma reserve_load:
  forall m b chunk o n m'
    (MR: reserve_boxes m n = Some m'),
    Mem.load chunk m b o = Mem.load chunk m' b o.
Proof.
  intros.
  unfold Mem.load.
  repeat destr.
  - unfold reserve_boxes in MR; destr_in MR; inv MR.
    simpl. auto.
  - exfalso; apply n0. unfold Mem.valid_access, Mem.range_perm, Mem.perm, reserve_boxes in *.
    destr_in MR. inv MR. simpl in *. auto.
  - exfalso; apply n0. unfold Mem.valid_access, Mem.range_perm, Mem.perm, reserve_boxes in *.
    destr_in MR. inv MR. simpl in *. auto.
Qed.


Lemma reserve_bounds_of_block:
  forall m b n m'
    (MR: reserve_boxes m n = Some m'),
    Mem.bounds_of_block m b = Mem.bounds_of_block m' b.
Proof.
  intros.
  unfold Mem.bounds_of_block.
  unfold reserve_boxes in MR; destr_in MR; inv MR.
  reflexivity.
Qed.

Lemma reserve_mask:
  forall m b n m'
    (MR: reserve_boxes m n = Some m'),
    Mem.mask m b = Mem.mask m' b.
Proof.
  intros.
  unfold Mem.mask.
  unfold reserve_boxes in MR; destr_in MR; inv MR.
  reflexivity.
Qed.

Lemma reserve_is_dynamic_block:
  forall m b n m'
    (MR: reserve_boxes m n = Some m'),
    Mem.is_dynamic_block m b = Mem.is_dynamic_block m' b.
Proof.
  intros.
  unfold Mem.is_dynamic_block.
  unfold reserve_boxes in MR; destr_in MR; inv MR.
  reflexivity.
Qed.


Lemma reserve_nextblock:
  forall m n m'
    (MR: reserve_boxes m n = Some m'),
    Mem.nextblock m = Mem.nextblock m'.
Proof.
  intros.
  unfold Mem.nextblock.
  unfold reserve_boxes in MR; destr_in MR; inv MR.
  reflexivity.
Qed.

Lemma reserve_perm:
  forall m n m' b o k p
    (MR: reserve_boxes m n = Some m'),
    Mem.perm m b o k p <-> Mem.perm m' b o k p.
Proof.
  intros.
  unfold Mem.perm.
  unfold reserve_boxes in MR; destr_in MR; inv MR.
  tauto.
Qed.

Lemma release_perm:
  forall m n m' b o k p
    (MR: release_boxes m n = Some m'),
    Mem.perm m b o k p <-> Mem.perm m' b o k p.
Proof.
  intros.
  unfold Mem.perm.
  unfold release_boxes in MR; destr_in MR; inv MR.
  tauto.
Qed.

Lemma reserve_mem_contents:
  forall m n m'
    (MR: reserve_boxes m n = Some m'),
    Mem.mem_contents m = Mem.mem_contents m'.
Proof.
  intros.
  unfold Mem.mem_contents.
  unfold reserve_boxes in MR; destr_in MR; inv MR.
  reflexivity.
Qed.

Lemma reserve_nb_boxes_used_m:
  forall m n m'
    (MR: reserve_boxes m n = Some m'),
    (Mem.nb_boxes_used_m m + n = Mem.nb_boxes_used_m m')%nat.
Proof.
  intros.
  unfold Mem.nb_boxes_used_m, Mem.mk_block_list, Mem.size_block.
  unfold reserve_boxes in MR; destr_in MR; inv MR.
  simpl. lia. 
Qed.

Open Scope Z_scope.




Lemma nb_boxes_set0:
  forall l1 b sz l2,
    (Mem.nb_boxes_used (l1 ++ (b,sz) :: l2)  =
     Mem.nb_boxes_used (l1 ++ (b,Z0) :: l2) + Mem.box_span sz)%nat.
Proof.
  intros.
  rewrite <- (Mem.nb_used_permut _ _ (Permutation.Permutation_middle _ _ _)).
  rewrite <- (Mem.nb_used_permut _ _ (Permutation.Permutation_middle _ _ _)).
  rewrite ! Mem.nb_boxes_used_cons. replace (Mem.box_span Z0) with O. lia.
  unfold Mem.box_span. simpl.
  rewrite Mem.minus_1_div_eq. reflexivity. apply Mem.tpMA_pos.
Qed.

Lemma nb_bozes_free_eq:
  forall sz' sz n b
         (sz_ext: forall b',
                    b <> b' ->
                    sz' b' = sz b')
         (EQ: sz' b = 0),
    Mem.nb_boxes_used (mk_block_list_aux sz  n) =
    (Mem.nb_boxes_used (mk_block_list_aux sz' n)
     + if le_dec (Pos.to_nat b) n 
       then Mem.box_span (sz b)
       else 0)%nat.
Proof.
  intros. 
  destruct (le_dec (Pos.to_nat b) n).
  - specialize (mbla_suppr_below sz' sz b sz_ext n l).
    intros H.
    apply Permutation.Permutation_sym in H; auto.
    apply Mem.nb_used_permut in H. rewrite ! Mem.nb_boxes_used_cons in H.
    rewrite EQ in H.
    replace (Mem.box_span Z0) with O in H. lia.
    unfold Mem.box_span. simpl.
    rewrite Mem.minus_1_div_eq. reflexivity. apply Mem.tpMA_pos.
  - rewrite (mbla_suppr_above sz' sz b); auto; omega.
Qed.



Lemma unchecked_free_nb_boxes:
  forall m b lo hi,
    Mem.bounds_of_block m b = (lo, hi) ->
    (Mem.nb_boxes_used_m (Mem.unchecked_free m b lo hi) + Mem.box_span (Z.max 0 hi)
     = Mem.nb_boxes_used_m m)%nat.
Proof.
  unfold Mem.nb_boxes_used_m. simpl; intros.
  unfold Mem.mk_block_list.
  simpl.
  erewrite (@nb_bozes_free_eq (Mem.size_block (Mem.unchecked_free m b lo hi)) (Mem.size_block m)
           (pred (Pos.to_nat (Mem.nextblock m))) b).
  2: intros; rewrite Mem.size_block_unchecked_free.
  3: rewrite Mem.size_block_unchecked_free; destr.
  destr. rewrite <- Mem.size_block_snd, H; simpl. rewrite Z.max_r. lia.
  etransitivity. apply (Mem.size_block_pos m b).
  rewrite <- Mem.size_block_snd. rewrite H. apply Z.le_refl.
  rewrite Z.max_l.
  replace (Mem.box_span Z0) with O. lia.
  unfold Mem.box_span. simpl.
  rewrite Mem.minus_1_div_eq. reflexivity. apply Mem.tpMA_pos.
  unfold Mem.bounds_of_block in H. destr_in H. des p.
  rewrite Mem.bs_valid in Heqo. congruence. intro P. apply Pos2Nat.inj_lt in P. lia. 
  inv H; lia. destr. rewrite H. destruct zeq; destruct zeq; destr.
Qed.



Lemma free_nb_boxes_used':
  forall m b lo hi m',
    Mem.free m b lo hi = Some m' ->
    (Mem.nb_boxes_used_m m' + Mem.box_span (hi - lo))%nat = Mem.nb_boxes_used_m m.
Proof.
  Transparent Mem.free. unfold Mem.free.
  intros. repeat destr_in H. inv H.
  apply Mem.has_bounds_bounds in Heqb0.
  assert (lo = 0 /\ hi >= 0).
  unfold Mem.bounds_of_block in Heqb0. destr_in Heqb0. des p. eapply Mem.bounds_lo_inf0 in Heqo. inv Heqb0. destr; lia.
  inv Heqb0; lia.
  intuition subst.
  erewrite <- (unchecked_free_nb_boxes m b 0 hi). rewrite Z.max_r. rewrite Z.sub_0_r. auto.
  lia. auto.
Qed.

Definition size_list_blocks (bl : list Z) : nat :=
  fold_left Peano.plus (map Mem.box_span bl) O.

Definition size_of_block (blh: block * Z * Z) :=
  let '(b,lo,hi) := blh in
  (hi - lo)%Z.

Definition size_list l :=
  size_list_blocks (map size_of_block l).


Lemma free_list_nb_boxes_used:
  forall bl m m',
    Mem.free_list m bl = Some m' ->
    (Mem.nb_boxes_used_m m' + size_list bl = Mem.nb_boxes_used_m m)%nat.
Proof.
  unfold size_list, size_list_blocks. induction bl; simpl; intros. inv H. lia.
  repeat destr_in H.
  specialize (IHbl _ _ H).
  rewrite Mem.fold_left_plus_rew. rewrite plus_assoc. rewrite IHbl.
  exploit free_nb_boxes_used'; eauto.
Qed.

Lemma nb_boxes_release:
  forall m n m' (REL: release_boxes m n = Some m'),
    Mem.nb_boxes_used_m m = (Mem.nb_boxes_used_m m' + n)%nat.
Proof.
  unfold release_boxes. intros m n m'. destr. intro; inv REL.
  unfold Mem.nb_boxes_used_m, Mem.mk_block_list, Mem.size_block, Mem.bounds_of_block.
  simpl. lia.
Qed.

Lemma release_nb_boxes_used:
  forall m n m' (MR: release_boxes m n = Some m'),
    (Mem.nb_boxes_used_m m = Mem.nb_boxes_used_m m' + n)%nat.
Proof.
  intros. unfold release_boxes in *. destr_in MR; inv MR.
  unfold Mem.nb_boxes_used_m, Mem.mk_block_list, Mem.size_block in *; simpl in *; eauto.
  lia.
Qed.





Lemma release_boxes_mk_block_list:
  forall m n m' (REL: release_boxes m n = Some m'),
    Mem.mk_block_list m = Mem.mk_block_list m'.
Proof.
  unfold release_boxes; intros.
  destr_in REL; inv REL. unfold Mem.mk_block_list. simpl.
  reflexivity.
Qed.

Require Import Maps.

Definition is_static_block_b m b :=
  match (Mem.mem_blocktype m) !! b with
    Some Dynamic => false
  | _ => true
  end.

Definition is_dynamic_block_b m b :=
  match (Mem.mem_blocktype m) !! b with
    Some Dynamic => true
  | _ => false
  end.

Definition nb_boxes_static (m: mem) :=
  Mem.nb_boxes_used (filter (fun bsz => is_static_block_b m (fst bsz)) (Mem.mk_block_list m)).

Definition nb_boxes_dynamic (m: mem) :=
  Mem.nb_boxes_used (filter (fun bsz => is_dynamic_block_b m (fst bsz)) (Mem.mk_block_list m)).

Lemma nb_boxes_app:
  forall l1 l2,
    (Mem.nb_boxes_used (l1 ++ l2)  =
     Mem.nb_boxes_used l1 + Mem.nb_boxes_used l2)%nat.
Proof.
  induction l1; simpl; intros. lia.
  des a. rewrite ! Mem.nb_boxes_used_cons. rewrite IHl1. lia.
Qed.


Lemma partition_app_perm:
  forall {A: Type} f (l: list A) a b,
    partition f l = (a,b) ->
    Permutation l (a ++ b).
Proof.
  induction l; simpl; intros; eauto.
  - inv H. simpl; constructor.
  - repeat destr_in H.
    + inv H. specialize (IHl _ _ eq_refl).
      simpl. constructor. auto.
    + inv H. specialize (IHl _ _ eq_refl).
      eapply perm_trans. apply perm_skip. eauto.
      apply Permutation_middle.
Qed.




Lemma lnr_nin:
  forall {A: Type} (f: A -> bool) l a b,
    partition f l = (a, b) ->
    forall x, ~ In x l ->
         ~ In       x a /\ ~ In x b.
Proof.
  induction l; simpl; intros; eauto.
  - inv H; destr.
  - repeat destr_in H; inv H; specialize (IHl _ _ eq_refl); destr.
    trim (IHl x). destr. split; destr.
    trim (IHl x). destr. split; destr.
Qed.

Lemma lnr_partition:
  forall {A: Type} (f: A -> bool) l a b,
    partition f l = (a, b) ->
    list_norepet l ->
    list_norepet a /\ list_norepet b.
Proof.
  induction l; simpl; intros; eauto.
  - inv H. split; constructor.
  - repeat destr_in H; inv H; specialize (IHl _ _ eq_refl); inv H0; split; trim IHl; auto.
    constructor; auto.
    eapply lnr_nin in H2; eauto. destr.
    destr. destr. destr.
    constructor; auto.
    eapply lnr_nin in H2; eauto. destr. destr.
Qed.

Lemma in_partition_l:
  forall {A: Type} (f: A -> bool) l a b,
    partition f l = (a, b) ->
    forall x,
      In x a <->
      In x l /\ f x = true.
Proof.
  induction l; simpl; intros; eauto.
  - inv H. simpl; tauto. 
  - repeat destr_in H; inv H; specialize (IHl _ _ eq_refl).
    simpl.
    + split; intros.
      destruct H; auto. destr. apply IHl in H. destr.
      destruct H. destruct H; auto. right; rewrite IHl. destr.
    + split; intros.
      apply IHl in H. destr.
      destruct H. rewrite IHl.  destruct H; auto. congruence.   
Qed.



Lemma lnr_nin':
  forall {A B: Type} (f: A * B -> bool) (l: list (A*B)) a b,
    partition f l = (a, b) ->
    forall x, ~ In x (map fst l) ->
         ~ In       x (map fst a) /\ ~ In x (map fst b).
Proof.
  induction l; simpl; intros; eauto.
  - inv H; destr.
  - repeat destr_in H; inv H; specialize (IHl _ _ eq_refl); destr.
    trim (IHl x). destr. split; destr.
    trim (IHl x). destr. split; destr.
Qed.


Lemma lnr_partition':
  forall {A B: Type} (f: A * B -> bool) (l: list (A * B)) a b,
    partition f l = (a, b) ->
    list_norepet (map fst l) ->
    list_norepet (map fst a) /\ list_norepet (map fst b).
Proof.
  induction l; simpl; intros; eauto.
  - inv H. split; constructor.
  - repeat destr_in H; inv H; specialize (IHl _ _ eq_refl); inv H0; split; trim IHl; auto; simpl.
    constructor; auto.
    eapply lnr_nin' in H2; eauto. destr.
    destr. destr. destr.
    constructor; auto.
    eapply lnr_nin' in H2; eauto. destr. destr.
Qed.


Lemma permut_filter_map:
  forall {A B} (f: A -> option B) (l l': list A),
    Permutation l l' ->
    Permutation (filter_map f l) (filter_map f l').
Proof.
  induction 1; simpl; intros; eauto.
  - destr; auto.
  - repeat destr; auto. apply perm_swap.
  - rewrite IHPermutation1; auto.
Qed.

Lemma in_partition_r:
  forall {A: Type} (f: A -> bool) l a b,
    partition f l = (a, b) ->
    forall x,
      In x b <->
      In x l /\ f x = false.
Proof.
  induction l; simpl; intros; eauto.
  - inv H. simpl; tauto. 
  - repeat destr_in H; inv H; specialize (IHl _ _ eq_refl).
    simpl.
    + split; intros.
      apply IHl in H. destr.
      destruct H. rewrite IHl.  destr. 
    + split; intros.
      destruct H; auto. destr. apply IHl in H. destr.
      destruct H. destr. destruct H; auto. right; rewrite IHl. destr.
Qed.


Lemma not_inj_filter_map:
  forall {A B} (f: A -> option B) (l0: list A)
    (Spec: forall b, In b l0 -> f b = None),
    filter_map f l0 = nil.
Proof.
  induction l0; simpl; intros; eauto.
  des (f a). rewrite Spec in Heqo; destr.
  eapply IHl0; eauto.
Qed.



Lemma partition_filter:
  forall {A} (f: A -> bool) l l1 l2,
    partition f l = (l1,l2) ->
    l1 = filter f l.
Proof.
  induction l; simpl; intros.
  inv H; auto.
  destr_in H. specialize (IHl _ _ eq_refl). subst.
  destr_in H; inv H; auto.
Qed.

Lemma partition_filter_r:
  forall {A} (f: A -> bool) l l1 l2,
    partition f l = (l1,l2) ->
    l2 = filter (fun b => negb (f b)) l.
Proof.
  induction l; simpl; intros.
  inv H; auto.
  destr_in H. specialize (IHl _ _ eq_refl). subst.
  destr_in H; inv H; auto.
Qed.

Lemma filter_app:
  forall {A} f (l1 l2: list A),
    filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  induction l1; simpl; intros; eauto.
  rewrite IHl1. destr.
Qed.




Lemma filter_dynamic_static_permut:
  forall m l,
    Permutation
      (filter (fun bsz : positive * Z => is_static_block_b m (fst bsz)) l ++
              filter (fun bsz : positive * Z => is_dynamic_block_b m (fst bsz)) l)
      l.
Proof.
  intros.
  des (partition (fun bsz : positive * Z => is_static_block_b m (fst bsz)) l).
  exploit (partition_app_perm (A:= positive * Z)). eauto.
  intro A. etransitivity. 2: symmetry; apply A. apply Permutation_app.
  eapply partition_filter in Heqp. subst; reflexivity.
  eapply partition_filter_r in Heqp. subst.
  erewrite filter_ext. reflexivity. intros. des b.
  unfold is_dynamic_block_b, is_static_block_b. destr. destr.
Qed.

Lemma nb_boxes_sep:
  forall m,
    (Mem.nb_boxes_used_m m = nb_boxes_static m + nb_boxes_dynamic m + Mem.nb_extra m)%nat.
Proof.
  unfold Mem.nb_boxes_used_m. intros.
  f_equal.
  unfold nb_boxes_dynamic, nb_boxes_static.
  rewrite <- nb_boxes_app.
  rewrite (Mem.nb_used_permut _ _ (filter_dynamic_static_permut _ _)). auto.
Qed.



Lemma release_boxes_nb_static:
  forall m n m' (REL: release_boxes m n = Some m'),
    nb_boxes_static m = nb_boxes_static m'.
Proof.
  intros.
  unfold nb_boxes_static.
  erewrite release_boxes_mk_block_list; eauto. erewrite filter_ext. reflexivity.
  unfold is_static_block_b. simpl.
  unfold release_boxes in REL; destr_in REL; inv REL. reflexivity.
Qed.

Lemma nb_boxes_free_filter:
  forall sz' sz n b
    (sz_ext: forall b',
        b <> b' ->
        sz' b' = sz b')
    (EQ: sz' b = 0)
    f (F: forall z, f (b, z) = true),
    Mem.nb_boxes_used (filter f (mk_block_list_aux sz  n)) =
    (Mem.nb_boxes_used (filter f (mk_block_list_aux sz' n))
     + if le_dec (Pos.to_nat b) n 
       then Mem.box_span (sz b)
       else 0)%nat.
Proof.
  intros. 
  destruct (le_dec (Pos.to_nat b) n).
  - specialize (mbla_suppr_below sz' sz b sz_ext n l).
    intros H.
    apply Permutation.Permutation_sym in H; auto.
    eapply Mem.permut_filter with (f:=f) in H.
    apply Mem.nb_used_permut in H. simpl in H. rewrite ! F in H.
    rewrite ! Mem.nb_boxes_used_cons in H.
    rewrite EQ in H.
    replace (Mem.box_span Z0) with O in H. lia.
    unfold Mem.box_span. simpl.
    rewrite Mem.minus_1_div_eq. reflexivity. apply Mem.tpMA_pos.
  - rewrite (mbla_suppr_above sz' sz b); auto; omega.
Qed.


Lemma bounds_eq:
  forall m b,
    Mem.bounds_of_block m b = (0, Mem.size_block m b).
Proof.
  intros.
  rewrite (surjective_pairing (Mem.bounds_of_block _ _)).
  rewrite Mem.bounds_lo_0,
  Mem.size_block_snd. auto.
Qed.

Lemma box_span_0:
  0%nat = Mem.box_span 0.
Proof.
  intros.
  unfold box_span.
  simpl.
  unfold Z.div, Z.div_eucl.
  destr. repeat destr_in Heqp.
  - destr_in Heqp0. inv Heqp0.
    rewrite Z.leb_nle in Heqb.
    exfalso. apply Heqb. transitivity (two_power_nat 3). vm_compute; destr.
    rewrite ! two_power_nat_two_p. apply two_p_monotone.
    generalize MA_bound; lia.
  - destr_in Heqp0. inv Heqp0. inv Heqp. reflexivity.
  - destr_in Heqp0.
Qed.


Lemma free_static_nb_static:
  forall m b lo hi m'
    (DYN: ~ Mem.is_dynamic_block m b)
    (FREE: Mem.free m b lo hi = Some m'),
    nb_boxes_static m = (nb_boxes_static m' + Mem.box_span (hi - lo))%nat.
Proof.
  intros.
  unfold nb_boxes_static.
  unfold Mem.mk_block_list.
  erewrite (nb_boxes_free_filter (Mem.size_block m') (Mem.size_block m)
                                 (pred (Pos.to_nat (Mem.nextblock m))) b).
  - destr.
    erewrite <- Mem.nextblock_free; eauto. f_equal.
    erewrite filter_ext. reflexivity.
    unfold is_static_block_b. unfold Mem.free in FREE; repeat destr_in FREE; inv FREE; reflexivity.
    unfold Mem.free in FREE; repeat destr_in FREE; inv FREE.
    eapply Mem.has_bounds_bounds in Heqb0.
    erewrite bounds_eq in Heqb0. inv Heqb0. f_equal. lia.
    erewrite <- Mem.nextblock_free; eauto. f_equal.
    erewrite filter_ext. reflexivity.
    unfold is_static_block_b. unfold Mem.free in FREE; repeat destr_in FREE; inv FREE; reflexivity.
    unfold Mem.free in FREE; repeat destr_in FREE; inv FREE.
    eapply Mem.has_bounds_bounds in Heqb0.
    destruct (zeq lo hi). subst. rewrite Z.sub_diag.
    apply box_span_0.
    exploit Mem.bounds_of_block_valid. eauto. eauto. intro VB. red in VB.
    apply Pos2Nat.inj_lt in VB. lia.
  - unfold Mem.free in FREE; repeat destr_in FREE; inv FREE.
    unfold Mem.size_block. simpl.
    intros. unfold get_size. rewrite PMap.gso; auto.
  - rewrite <- Mem.size_block_snd. erewrite Mem.free_bounds_exact. 2: eauto.
    rewrite peq_true. reflexivity.
  - unfold is_static_block_b. simpl.
    unfold Mem.is_dynamic_block in DYN. repeat destr.
Qed.

Lemma free_list_nb_static:
  forall bl m m',
    Mem.free_list m bl = Some m' ->
    Forall (fun x => let '(b,_,_) := x in is_static_block_b m b = true) bl ->
    (nb_boxes_static m' + size_list bl = nb_boxes_static m)%nat.
Proof.
  unfold size_list, size_list_blocks. induction bl; simpl; intros. inv H. lia.
  repeat destr_in H.
  specialize (IHbl _ _ H). inv H0.
  trim IHbl.
  eapply Forall_impl. 2: apply H4.
  intros. des a. des p. unfold is_static_block_b in H0 |- *.
  unfold Mem.free in Heqo; repeat destr_in Heqo; inv Heqo. simpl. auto.
  rewrite Mem.fold_left_plus_rew. rewrite plus_assoc. rewrite IHbl.
  exploit (free_static_nb_static m b). unfold Mem.is_dynamic_block.
  unfold is_static_block_b in H3. destr_in H3. des b0. eauto. lia.
Qed.

Lemma nb_extra_release:
  forall m n m' (REL: release_boxes m n = Some m'),
    Mem.nb_extra m = (Mem.nb_extra m' + n)%nat.
Proof.
  unfold release_boxes. intros m n m'. destr. intro; inv REL.
  simpl. lia.
Qed.

Lemma free_list_nb_static':
  forall bl m m',
    Mem.free_list m bl = Some m' ->
    Forall (fun x => ~ Mem.is_dynamic_block m x) (map fst (map fst bl)) ->
    (nb_boxes_static m' + size_list bl = nb_boxes_static m)%nat.
Proof.
  intros.
  eapply free_list_nb_static; eauto.
  rewrite Forall_forall in H0 |- *.
  intros ((x & lo) & hi) IN.
  trim (H0 x). rewrite map_map, in_map_iff.
  eexists; split; eauto. reflexivity.
  unfold Mem.is_dynamic_block in H0; unfold is_static_block_b.
  repeat destr.
Qed.


Lemma size_list_cons:
  forall b lo hi l,
    size_list (((b,lo),hi)::l) = (size_list l + Mem.box_span (hi - lo))%nat.
Proof.
  unfold size_list, size_list_blocks. simpl.
  intros; rewrite Mem.fold_left_plus_rew. f_equal. 
Qed.

Lemma alloc_static_nb_static:
  forall m lo hi m' b (ALLOC: Mem.alloc m lo hi Normal = Some (m',b)),
    (nb_boxes_static m + Mem.box_span (Z.max 0 hi) = nb_boxes_static m')%nat.
Proof.
  intros.
  unfold nb_boxes_static.
  unfold Mem.mk_block_list.
  unfold Mem.size_block.
  Transparent Mem.alloc.
  unfold Mem.alloc, Mem.low_alloc in ALLOC. destr_in  ALLOC; inv ALLOC. simpl.
  unfold is_static_block_b. simpl.
  erewrite mk_block_list_aux_eq. simpl. rewrite PMap.gss.
  rewrite Mem.nb_boxes_used_cons.
  f_equal. f_equal. apply filter_ext. intros; rewrite PMap.gsspec.  destr. destr.  des b.
  erewrite Mem.blocktype_valid in Heqo. congruence. rewrite e. xomega.
  f_equal. lia. apply MA_bound.
Qed.

Lemma size_list_permut:
  forall l l' (P: Permutation l l'),
    size_list l = size_list l'.
Proof.
  unfold size_list, size_list_blocks in *. simpl.
  induction 1; simpl; intros; eauto.
  rewrite ! (Mem.fold_left_plus_rew _ (box_span _)). lia.
  rewrite ! (Mem.fold_left_plus_rew _ (plus _ _)). lia.
  lia.
Qed.

Lemma reserve_boxes_mk_block_list:
  forall m n m' (REL: reserve_boxes m n = Some m'),
    Mem.mk_block_list m = Mem.mk_block_list m'.
Proof.
  unfold reserve_boxes; intros.
  destr_in REL; inv REL. unfold Mem.mk_block_list. simpl.
  reflexivity.
Qed.

Lemma reserve_boxes_nb_static:
  forall m n m' (REL: reserve_boxes m n = Some m'),
    nb_boxes_static m = nb_boxes_static m'.
Proof.
  intros.
  unfold nb_boxes_static.
  erewrite reserve_boxes_mk_block_list; eauto. erewrite filter_ext. reflexivity.
  unfold is_static_block_b. simpl.
  unfold reserve_boxes in REL; destr_in REL; inv REL. reflexivity.
Qed.

Lemma release_nb_dynamic:
  forall m n m' (REL: release_boxes m n = Some m'),
    nb_boxes_dynamic m = nb_boxes_dynamic m'.
Proof.
  unfold release_boxes. intros. destr_in REL; inv REL. reflexivity.
Qed.

Lemma Permutation_intro:
  forall {A} (D: forall (a b: A), {a=b}+{a<>b}) (l1 l2: list A),
    list_norepet l1 ->
    list_norepet l2 ->
    (forall x, In x l1 <-> In x l2) ->
    Permutation l1 l2.
Proof.
  induction l1; simpl; intros; eauto.
  - des l2.
    + constructor.
    + des (H1 a). exfalso; apply f; auto.
  -

    destruct (in_split a l2). rewrite <- H1. auto. dex; subst.
    etransitivity.
    2: apply Permutation_middle.
    apply perm_skip.
    apply IHl1. inv H; auto.
    eapply permutation_norepet in H0.
    2: apply Permutation_sym, Permutation_middle. inv H0; auto. 
    split; intros.
    destruct (D a x0). subst. inv H. congruence.
    specialize (H1 x0); des H1. trim i. auto.
    rewrite in_app in i |- *. des i.
    destruct (D a x0). subst.
    eapply permutation_norepet in H0.
    2: apply Permutation_sym, Permutation_middle. inv H0; auto. congruence.    
    specialize (H1 x0); des H1. trim o. auto.
    rewrite in_app in H2 |- *. des H2. des o.
Qed.

Remark filter_norepet:
  forall (A: Type) (f: A -> bool) l,
  list_norepet l -> list_norepet (List.filter f l).
Proof.
  induction 1; simpl. constructor. 
  destruct (f hd); auto. constructor; auto. rewrite filter_In. tauto.
Qed.





Lemma in_mbla:
  forall b z sz n,
    In b (map fst (mk_block_list_aux sz n)) ->
    z = sz b ->
    In (b, z) (mk_block_list_aux sz n).
Proof.
  intros.
  rewrite in_map_iff in H. dex. des H.  des x.
  exploit mbla_in; eauto. intro; subst; auto.
Qed.
Lemma in_sz_ext:
  forall sz sz' n b,
    In b (map fst (mk_block_list_aux sz n)) ->
    In b (map fst (mk_block_list_aux sz' n)).
Proof.
  Opaque mk_block_list_aux.
  induction n; simpl; intros; auto.
  rewrite mbla_rew in *.
  simpl in *. des H. right; auto. 
Qed.

Lemma free_static_nb_dynamic:
  forall m b lo hi m' (FREE: Mem.free m b lo hi = Some m')
    (DYN: ~ Mem.is_dynamic_block m b),
    nb_boxes_dynamic m = nb_boxes_dynamic m'.
Proof.
  unfold Mem.free. intros.
  repeat destr_in FREE; inv FREE. simpl.
  unfold nb_boxes_dynamic.
  unfold Mem.mk_block_list.
  eapply Mem.nb_used_permut.
  eapply Permutation_intro. intros; repeat decide equality.
  apply  filter_norepet. apply mbla_norepet'.
  apply  filter_norepet. apply mbla_norepet'.
  intros.
  rewrite ! filter_In.
  unfold Mem.size_block.
  unfold is_dynamic_block_b. simpl.
  unfold Mem.is_dynamic_block in DYN.
  split; intros [A B].
  -  
    split. des x. exploit mbla_in. apply A. intro; subst.
    apply in_mbla.
    eapply in_sz_ext. eapply in_map with (f:=fst) in A. simpl in A. apply A.
    unfold get_size. rewrite Maps.PMap.gso. reflexivity. intro; subst. destr_in B. des b0. 
    auto.
  - des x. exploit mbla_in. apply A. intro; subst.
    split. apply in_mbla.
    eapply in_sz_ext. eapply in_map with (f:=fst) in A. simpl in A. apply A.
    unfold get_size. rewrite Maps.PMap.gso. reflexivity. intro; subst.
    repeat destr_in B. auto.      
Qed.

Lemma free_dynamic_nb_static:
  forall m b lo hi m'
    (DYN: Mem.is_dynamic_block m b)
    (FREE: Mem.free m b lo hi = Some m'),
    nb_boxes_static m = nb_boxes_static m'.
Proof.
  intros.
  unfold nb_boxes_static.
  unfold Mem.mk_block_list.
  eapply Mem.nb_used_permut.
  eapply Permutation_intro. intros; repeat decide equality.
  apply filter_norepet. apply mbla_norepet'.
  apply filter_norepet. apply mbla_norepet'.
  intros.
  rewrite ! filter_In.
  unfold Mem.size_block.
  unfold Mem.free in FREE. repeat destr_in FREE; inv FREE. simpl.
  unfold is_static_block_b. simpl.
  unfold Mem.is_dynamic_block in DYN.
  split; intros [A B].
  -  
    split. des x. exploit mbla_in. apply A. intro; subst.
    apply in_mbla.
    eapply in_sz_ext. eapply in_map with (f:=fst) in A. simpl in A. apply A.
    unfold get_size. rewrite PMap.gso. reflexivity. intro; subst. rewrite DYN in B. destr.
    destr. 
  - des x. exploit mbla_in. apply A. intro; subst.
    split. apply in_mbla.
    eapply in_sz_ext. eapply in_map with (f:=fst) in A. simpl in A. apply A.
    unfold get_size. rewrite PMap.gso. reflexivity. intro; subst. rewrite DYN in B. destr.
    destr. 
Qed.


Lemma free_dynamic_nb_dynamic:
  forall m b lo hi m'
    (DYN: Mem.is_dynamic_block m b)
    (FREE: Mem.free m b lo hi = Some m'),
    nb_boxes_dynamic m = (nb_boxes_dynamic m' + Mem.box_span (hi - lo))%nat.
Proof.
  intros.
  unfold nb_boxes_dynamic.
  unfold Mem.mk_block_list.
  erewrite (@nb_boxes_free_filter (Mem.size_block m') (Mem.size_block m)
                                 (pred (Pos.to_nat (Mem.nextblock m))) b).
  - destr.
    erewrite <- Mem.nextblock_free; eauto. f_equal.
    erewrite filter_ext. reflexivity.
    unfold is_dynamic_block_b.
    Transparent Mem.free.
    unfold Mem.free in FREE; repeat destr_in FREE; inv FREE; reflexivity.
    unfold Mem.free in FREE; repeat destr_in FREE; inv FREE.
    eapply Mem.has_bounds_bounds in Heqb0.
    erewrite bounds_eq in Heqb0. inv Heqb0. f_equal. lia.
    erewrite <- Mem.nextblock_free; eauto. f_equal.
    erewrite filter_ext. reflexivity.
    unfold is_dynamic_block_b. unfold Mem.free in FREE; repeat destr_in FREE; inv FREE; reflexivity.
    unfold Mem.free in FREE; repeat destr_in FREE; inv FREE.
    eapply Mem.has_bounds_bounds in Heqb0.
    destruct (zeq lo hi). subst. rewrite Z.sub_diag.
    apply  box_span_0.
    exploit Mem.bounds_of_block_valid. eauto. eauto. intro VB. red in VB.
    apply Pos2Nat.inj_lt in VB. lia.
  - unfold Mem.free in FREE; repeat destr_in FREE; inv FREE.
    unfold Mem.size_block. simpl.
    intros. unfold get_size. rewrite Maps.PMap.gso; auto.
  - rewrite <- Mem.size_block_snd. erewrite Mem.free_bounds_exact. 2: eauto.
    rewrite peq_true. reflexivity.
  - unfold is_dynamic_block_b. simpl.
    unfold Mem.is_dynamic_block in DYN. repeat destr.
Qed.

Lemma free_list_static_nb_dynamic:
  forall bl m m' (FREE: Mem.free_list m bl = Some m')
    (DYN: Forall (fun b => ~ Mem.is_dynamic_block m b) (map fst (map fst bl))),
    nb_boxes_dynamic m = nb_boxes_dynamic m'.
Proof.
  induction bl; simpl; intros; eauto. inv FREE; auto.
  repeat destr_in FREE.
  inv DYN. trim (IHbl _ _ FREE).
  revert H2. apply Forall_impl. unfold Mem.is_dynamic_block.
  unfold Mem.free in Heqo; repeat destr_in Heqo; inv Heqo. simpl. tauto.
  rewrite <- IHbl. eapply free_static_nb_dynamic; eauto.
Qed.

Lemma reserve_boxes_nb_extra:
  forall m n m' (REL: reserve_boxes m n = Some m'),
    (Mem.nb_extra m + n = Mem.nb_extra m')%nat.
Proof.
  intros.
  unfold nb_boxes_static.
  unfold reserve_boxes in REL; destr_in REL; inv REL. reflexivity.
Qed.

Lemma reserve_boxes_nb_dynamic:
  forall m n m' (RB: reserve_boxes m n = Some m'),
    nb_boxes_dynamic m = nb_boxes_dynamic m'.
Proof.
  unfold reserve_boxes. intros.
  destr_in RB; inv RB. 
  unfold nb_boxes_dynamic.
  eapply Mem.nb_used_permut.
  apply Permutation_intro.
  intros; repeat decide equality.
  apply filter_norepet. apply mbla_norepet'.
  apply filter_norepet. apply mbla_norepet'.
  intros. rewrite ! filter_In.
  unfold Mem.mk_block_list. simpl. 
  unfold is_dynamic_block_b, Mem.size_block. simpl.
  repeat destr.
Qed.


Lemma store_nb_dynamic:
  forall m chunk b ofs v m' (STORE: Mem.store chunk m b ofs v = Some m'),
    nb_boxes_dynamic m = nb_boxes_dynamic m'.
Proof.
  intros.
  unfold nb_boxes_dynamic.
  erewrite <- Mem.store_mk_block_list; eauto. erewrite filter_ext. reflexivity.
  unfold is_dynamic_block_b. simpl.
  Transparent Mem.store.
  unfold Mem.store in STORE; destr_in STORE; inv STORE. simpl. reflexivity.
Qed.


Lemma alloc_dynamic_nb_static:
  forall m lo hi m' b (ALLOC: Mem.alloc m lo hi Dynamic = Some (m',b)),
    nb_boxes_static m = nb_boxes_static m'.
Proof.
  intros.
  unfold nb_boxes_static.
  eapply Mem.nb_used_permut.
  eapply Permutation_intro. intros; repeat decide equality.
  apply filter_norepet. apply mbla_norepet'.
  apply filter_norepet. apply mbla_norepet'.
  intros.
  rewrite ! filter_In.
  unfold Mem.mk_block_list.
  unfold Mem.size_block.
  Transparent Mem.alloc.
  unfold Mem.alloc, Mem.low_alloc in ALLOC. destr_in  ALLOC; inv ALLOC. simpl.
  unfold is_static_block_b. simpl.
  erewrite mk_block_list_aux_eq. 2: apply MA_bound. simpl.
  split; intros [A B].
  split. right; auto. rewrite PMap.gsspec. destr. rewrite e in B. destr_in B. des b.
  erewrite Mem.blocktype_valid in Heqo. destr. xomega.
  exfalso. eapply mbla_not_above. 2: rewrite in_map_iff; eexists; split. 3: exact A. 2: exact e. lia.
  rewrite PMap.gsspec in B. 
  destr_in B. des b. destr_in Heqo.  rewrite Heqo. split; auto.
  des A. destr_in Heqo. rewrite Heqo. des A.
Qed.

Lemma store_nb_static:
  forall m chunk b ofs v m' (STORE: Mem.store chunk m b ofs v = Some m'),
    nb_boxes_static m = nb_boxes_static m'.
Proof.
  intros.
  unfold nb_boxes_static.
  erewrite <- Mem.store_mk_block_list; eauto. erewrite filter_ext. reflexivity.
  unfold is_static_block_b. simpl.
  unfold Mem.store in STORE; destr_in STORE; inv STORE. simpl. reflexivity.
Qed.


Lemma storebytes_nb_dynamic:
  forall m b ofs v m' (STOREBYTES: Mem.storebytes m b ofs v = Some m'),
    nb_boxes_dynamic m = nb_boxes_dynamic m'.
Proof.
  intros.
  unfold nb_boxes_dynamic.
  erewrite <- Mem.storebytes_mk_block_list; eauto. erewrite filter_ext. reflexivity.
  unfold is_dynamic_block_b. simpl.
  Transparent Mem.storebytes.
  unfold Mem.storebytes in STOREBYTES; destr_in STOREBYTES; inv STOREBYTES. simpl. reflexivity.
Qed.

Lemma storebytes_nb_static:
  forall m b ofs v m' (STOREBYTES: Mem.storebytes m b ofs v = Some m'),
    nb_boxes_static m = nb_boxes_static m'.
Proof.
  intros.
  unfold nb_boxes_static.
  erewrite <- Mem.storebytes_mk_block_list; eauto. erewrite filter_ext. reflexivity.
  unfold is_static_block_b. simpl.
  unfold Mem.storebytes in STOREBYTES; destr_in STOREBYTES; inv STOREBYTES. simpl. reflexivity.
Qed.

Lemma filter_ext':
  forall {A} (l: list A) p p' (P: forall b, In b l -> p b = p' b),
    filter p l = filter p' l.
Proof.
  induction l; simpl; intros; auto.
  rewrite P; auto. destr; rewrite (IHl p p'); eauto.
Qed.

Lemma alloc_dynamic_nb_dynamic:
  forall m lo hi m' b (ALLOC: Mem.alloc m lo hi Dynamic = Some (m',b)),
    (nb_boxes_dynamic m + Mem.box_span (Z.max 0 hi) = nb_boxes_dynamic m')%nat.
Proof.
  intros.
  unfold nb_boxes_dynamic.
  unfold Mem.mk_block_list.
  unfold Mem.size_block.
  Transparent Mem.alloc.
  unfold Mem.alloc, Mem.low_alloc in ALLOC. destr_in  ALLOC; inv ALLOC. simpl.
  unfold is_dynamic_block_b. simpl.
  erewrite mk_block_list_aux_eq. simpl. rewrite Maps.PMap.gss.
  2: apply MA_bound.
  rewrite Mem.nb_boxes_used_cons.
  rewrite Z.sub_0_r. f_equal. f_equal.
  change (   filter
     (fun bsz : positive * Z =>
      (fun b => match (Mem.mem_blocktype m) !! b with
      | Some Normal => false
      | Some Dynamic => true
      | None => false
      end) (fst bsz)) (mk_block_list_aux (fun b : block => get_size (Mem.mem_blocksize m) b) (pred (Pos.to_nat (Mem.nextblock m)))) =
   filter
     (fun bsz : positive * Z =>
        (fun b =>
           match (PMap.set (Mem.nextblock m) (Some Dynamic) (Mem.mem_blocktype m)) !! b with
           | Some Normal => false
           | Some Dynamic => true
           | None => false
           end) (fst bsz)) (mk_block_list_aux (fun b0 : block => get_size (Mem.mem_blocksize m) b0) (pred (Pos.to_nat (Mem.nextblock m))))).
  apply filter_ext'.
  intros; rewrite Maps.PMap.gsspec.
  destr.  des b. subst.
  exfalso.
  eapply mbla_not_above. Focus 2.
  rewrite in_map_iff. eexists; split. 2: eauto.  reflexivity. simpl. lia. 
Qed.

Lemma fold_left_plus_in_le:
  forall l x,
    In x l ->
    (x <= fold_left plus l O)%nat.
Proof.
  induction l; simpl; intros; eauto. easy.
  rewrite fold_left_plus_rew. des H. lia. trim (IHl x); auto. lia.
Qed.

Lemma size_block_mu:
  forall m b,
    Mem.size_block m b <= Integers.Int.max_unsigned.
Proof.
  intros.
  generalize (Mem.wfm_alloc m). intros.
  destruct (zle (size_block m b) 0). etransitivity. eauto. vm_compute; destr.

  unfold nb_boxes_max in H.

  transitivity (two_power_nat MA * Z.of_nat (nb_boxes_used_m m)).
  unfold nb_boxes_used_m.
  transitivity (two_power_nat MA * Z.of_nat (Mem.box_span (size_block m b))).
  rewrite box_span_align. apply align_le. apply tpMA_pos. lia.
  apply Z.mul_le_mono_pos_l. apply Z.gt_lt, tpMA_pos. apply inj_le.
  transitivity (nb_boxes_used (mk_block_list m)). 2: lia.
  unfold nb_boxes_used.
  apply fold_left_plus_in_le. rewrite in_map_iff.
  simpl. exists (b, size_block m b); split; auto.
  apply mbla_below_in'.
  unfold size_block, get_size in g.  Opaque Z.sub minus. destr_in g.  des p.
  destruct (valid_block_dec m b). red in v. apply Pos2Nat.inj_lt in v. lia.
  rewrite bounds_mask_consistency in Heqo. destr. eapply msk_valid. eauto. lia.
  rewrite (Z.mul_lt_mono_pos_l (two_power_nat MA)) in H.
  transitivity (two_power_nat MA * (two_power_nat (32 - MA) - 2)). lia. 2: apply Z.gt_lt , tpMA_pos.
  change Integers.Int.max_unsigned with (two_power_nat 32 - 1).
  rewrite ! two_power_nat_two_p.
  rewrite Z.mul_sub_distr_l. rewrite <- two_p_is_exp by lia.
  replace (Z.of_nat MA + Z.of_nat (32 - MA)) with 32.
  2: generalize MA_bound; lia. simpl.
  cut ( 1 <= two_p (Z.of_nat MA)). lia.
  generalize (two_p_monotone 0 (Z.of_nat MA)), MA_bound. simpl. lia.
Qed.


Lemma match_cont_sm:
  forall bl m m' m'' N,
  Mem.free_list m bl = Some m' ->
  release_boxes m' N = Some m'' ->
  (Mem.nb_boxes_used_m m'' =
   Mem.nb_boxes_used_m m - size_list bl - N)%nat.
Proof.
  intros bl m m' m'' N FL REL.
  generalize (release_nb_boxes_used _ _ _ REL).
  generalize (free_list_nb_boxes_used _ _ _ FL). lia. 
Qed.

Lemma free_nb_boxes_used:
  forall m b lo hi m',
    Mem.free m b lo hi = Some m' ->
    (Mem.nb_boxes_used_m m' + Mem.box_span hi)%nat = Mem.nb_boxes_used_m m.
Proof.
  Transparent Mem.free. unfold Mem.free.
  intros. repeat destr_in H. inv H.
  erewrite <- (unchecked_free_nb_boxes m b lo hi). rewrite Z.max_r. auto.
  apply Mem.has_bounds_bounds in Heqb0.
  unfold Mem.bounds_of_block in Heqb0. destr_in Heqb0. des p. eapply Mem.bounds_lo_inf0 in Heqo. inv Heqb0. destr; lia.
  inv Heqb0; lia.
  eapply Mem.has_bounds_bounds; eauto.
Qed.

Lemma store_nb_boxes_used_m:
  forall chunk m b ofs v m' (STORE: Mem.store chunk m b ofs v = Some m'),
    Mem.nb_boxes_used_m m' = Mem.nb_boxes_used_m m.
Proof.
  intros. Transparent Mem.store. unfold Mem.store in STORE.
  destr_in STORE. inv STORE. reflexivity.
Qed.

Lemma storev_nb_boxes_used_m:
  forall chunk m vaddr v m' (STOREV: Mem.storev chunk m vaddr v = Some m'),
    Mem.nb_boxes_used_m m' = Mem.nb_boxes_used_m m.
Proof.
  unfold Mem.storev; intros; destr_in STOREV.
  eapply store_nb_boxes_used_m; eauto.
Qed.

Lemma storev_nb_extra:
  forall chunk m vaddr v m' (STOREV: Mem.storev chunk m vaddr v = Some m'),
    Mem.nb_extra m = Mem.nb_extra m'.
Proof.
  unfold Mem.storev; intros; destr_in STOREV.
  eapply Mem.nb_extra_store; eauto.
Qed.

Lemma nb_boxes_reserve:
  forall m n m' (RES: reserve_boxes m n = Some m'),
    (Mem.nb_boxes_used_m m' = Mem.nb_boxes_used_m m + n)%nat.
Proof.
  unfold reserve_boxes. intros m n m' RES.
  destr_in RES.
  inv RES.
  unfold Mem.nb_boxes_used_m, Mem.mk_block_list, Mem.size_block.
  simpl. lia.
Qed.


Remark map_filter:
  forall (A B: Type) (f: A -> B) (pa: A -> bool) (pb: B -> bool),
  (forall a, pb (f a) = pa a) ->
  forall l, List.map f (List.filter pa l) = List.filter pb (List.map f l).
Proof.
  induction l; simpl.
  auto.
  rewrite H. destruct (pa a); simpl; congruence.
Qed.

Lemma perm_free_eq:
  forall (m : mem) (b : block) (lo hi : Z) (m' : mem),
  Mem.free m b lo hi = Some m' ->
  forall (b' : block) (o : Z) (k : perm_kind) (p : permission), Mem.perm m' b' o k p -> Mem.perm m b' o k p /\ b <> b'.
Proof.
  intros.
  eapply Mem.perm_free_eq; eauto.
  Transparent Mem.free. unfold Mem.free in H.
  intros. repeat destr_in H.  eapply Mem.has_bounds_bounds; eauto. 
Qed.


Lemma release_abi :
  forall j m (ABI: Mem.all_blocks_injected j m) n m',
    release_boxes m n = Some m' ->
    Mem.all_blocks_injected j m'.
Proof.
  intros.
  red. intros b lo hi Bnd Nnul.
  rewrite <- (release_bounds_of_block _ _ _ _ H) in Bnd. eauto.
Qed.



Lemma release_bounds:
  forall o b m n m',
    release_boxes m n = Some m' ->
    Mem.in_bound_m o m' b ->
    Mem.in_bound_m o m b.
Proof.
  intros.
  unfold Mem.in_bound_m.
  rewrite (release_bounds_of_block _ _ _ _ H). eauto.
Qed.

Lemma free_in_bound:
  forall m b lo hi m'
    (FREE: Mem.free m b lo hi = Some m')
    o b'
    (IB: Mem.in_bound_m o m' b'),
    Mem.in_bound_m o m b'.
Proof.
  unfold Mem.in_bound_m.
  intros m b lo hi m' FREE o b' IB.
  destruct (Mem.free_bounds' _ _ _ _ _ b' FREE).
  congruence.
  rewrite H in IB; red in IB; simpl in IB; omega.
Qed.

Lemma reserve_boxes_nb_boxes_used:
  forall m n m' (REL: reserve_boxes m n = Some m'),
    (Mem.nb_boxes_used_m m + n = Mem.nb_boxes_used_m m')%nat.
Proof.
  intros.
  rewrite ! nb_boxes_sep.
  rewrite (reserve_boxes_nb_dynamic _ _ _ REL).
  rewrite (reserve_boxes_nb_static _ _ _ REL).
  rewrite <- (reserve_boxes_nb_extra _ _ _ REL).
  lia.
Qed.


Lemma alloc_static_nb_dynamic:
  forall m lo hi m' b (ALLOC: Mem.alloc m lo hi Normal = Some (m',b)),
    (nb_boxes_dynamic m = nb_boxes_dynamic m')%nat.
Proof.
  intros.
  unfold nb_boxes_dynamic.
  
  unfold Mem.mk_block_list.
  unfold Mem.size_block.
  Transparent Mem.alloc.
  unfold Mem.alloc, Mem.low_alloc in ALLOC. destr_in  ALLOC; inv ALLOC. simpl.
  unfold is_dynamic_block_b. simpl.
  erewrite mk_block_list_aux_eq. simpl. rewrite Maps.PMap.gss.
  erewrite filter_ext. reflexivity.
  intros; simpl. rewrite Maps.PMap.gsspec.  destr. destr.  des b.
  erewrite Mem.blocktype_valid in Heqo. congruence. rewrite e. xomega.
  apply MA_bound.
Qed.


Lemma storev_in_bound_m:
  forall chunk m addr v m' (STOREV: Mem.storev chunk m addr v = Some m')
    b o,
    Mem.in_bound_m o m b <-> Mem.in_bound_m o m' b.
Proof.
  intros.
  unfold Mem.storev in STOREV; revert STOREV; destr_cond_match; try easy.
  split. eapply (Mem.store_in_bound_m_1); eauto.
  eapply (Mem.store_in_bound_m_2); eauto.
Qed.

Lemma storev_size_mem:
  forall chunk m addr v m' (STOREV: Mem.storev chunk m addr v = Some m'),
    Mem.nb_boxes_used_m m' = Mem.nb_boxes_used_m m.
Proof.
  unfold Mem.storev. intros. destr_in STOREV. inv STOREV.
  eapply Mem.nb_boxes_used_same.
  eapply Mem.store_mk_block_list; eauto.
  symmetry; eapply Mem.nb_extra_store; eauto.
Qed.

Lemma release_nb_static:
  forall m n m' (MR: release_boxes m n = Some m'),
    (nb_boxes_static m = nb_boxes_static m')%nat.
Proof.
  intros. unfold release_boxes in *. destr_in MR; inv MR.
  unfold Mem.nb_boxes_used_m, Mem.mk_block_list, Mem.size_block in *; simpl in *; eauto.
Qed.

Lemma box_span_add:
  forall a b, b >= 0 -> a >= 0 ->
    (Mem.box_span (a + b) <= Mem.box_span a + Mem.box_span b)%nat.
Proof.
  intros.
  unfold Mem.box_span.
  apply Nat2Z.inj_le.
  rewrite Z2Nat.id.
  rewrite Nat2Z.inj_add.
  rewrite ! Z2Nat.id.
  
  cut ((a + b - 1) / two_power_nat MA <= (a - 1) / two_power_nat MA + (b - 1) / two_power_nat MA + 1). lia.

  2 : cut (-1 <= (b - 1) / two_power_nat MA). 2: lia. 2: etransitivity.
  3: eapply Z.div_le_mono with (a:= -1). 3: apply Z.gt_lt, Mem.tpMA_pos. 3: lia.
  2: rewrite Mem.minus_1_div_eq. 2: lia. 2: apply Mem.tpMA_pos.

  2 : cut (-1 <= (a - 1) / two_power_nat MA). 2: lia. 2: etransitivity.
  3: eapply Z.div_le_mono with (a:= -1). 3: apply Z.gt_lt, Mem.tpMA_pos. 3: lia.
  2: rewrite Mem.minus_1_div_eq. 2: lia. 2: apply Mem.tpMA_pos.

  2 : cut (-1 <= (a + b - 1) / two_power_nat MA). 2: lia. 2: etransitivity.
  3: eapply Z.div_le_mono with (a:= -1). 3: apply Z.gt_lt, Mem.tpMA_pos. 3: lia.
  2: rewrite Mem.minus_1_div_eq. 2: lia. 2: apply Mem.tpMA_pos.


  apply Z.mul_le_mono_pos_l with (p:=two_power_nat MA). apply Z.gt_lt, Mem.tpMA_pos.

  rewrite ! Z.mul_add_distr_l.

  assert (forall a b, b > 0 -> (b * (a/b)) = a - a mod b).
  {
    intros.
    rewrite (Z_div_mod_eq a0 _ H1) at 2. lia.
  }
  rewrite ! H1 by apply Mem.tpMA_pos.
  ring_simplify.
  (* cut (  - 1 - (a + b - 1) mod two_power_nat MA <= *)
  (*        - 1 - (a - 1) mod two_power_nat MA + -1 - (b - 1) mod two_power_nat MA + two_power_nat MA * 1). lia. *)

  cut ((a + b - 1) mod two_power_nat MA  + two_power_nat MA >=
       (a - 1) mod two_power_nat MA + (b - 1) mod two_power_nat MA  + 1). lia.
  
  assert (forall z: Z, z >= 0 -> exists a b, z = two_power_nat MA * a + b).
  {
    intros. exists (z / two_power_nat MA), (z mod two_power_nat MA).
    rewrite H1. lia. apply tpMA_pos. 
  }

  rewrite ! (Zminus_mod _ 1).
  rewrite Zplus_mod.
  IntFacts.elim_div.
  intros.
  generalize tpMA_pos. intro.
  cut (two_power_nat MA <> 0). intro.

  repeat match goal with
           H : _ |- _ => trim H; [ now auto | ]
         | H : _ /\ _ |- _ => destruct H
         | H : _ \/ _ |- _ => destruct H; [ | lia ]

         end.
  subst.
  cut (7 < two_power_nat MA). intros.
  assert (z7 = 0). nia. subst. 
  assert (z8 = 1). lia. subst.

  assert (z = 0 \/ z = -1). nia.
  clear H5. 
  Opaque Z.mul.
  des H7. 
  - replace z0 with (z2 - 1) in * by lia. clear H9.
    replace z12 with (z6 - 1 - two_power_nat MA * z11) in * by lia. clear H3.
    replace z10 with (z4 - 1 - two_power_nat MA * z9) in * by lia. clear H4.
    ring_simplify. 
    cut (z2 - (z4 + z6) >= two_power_nat MA * ( - z9 - z11 - 1 ) ). lia.
    rewrite H8. 
    cut (0 >= two_power_nat MA * (z1 - z9 - z11 - 1)). lia.
    cut (0 >= (z1 - z9 - z11 - 1)). nia. nia.
  - replace z0 with (z2 - 1 + two_power_nat MA) in * by lia. clear H9.
    replace z12 with (z6 - 1 - two_power_nat MA * z11) in * by lia. clear H3.
    replace z10 with (z4 - 1 - two_power_nat MA * z9) in * by lia. clear H4.
    ring_simplify.
    cut (z2 - (z4 + z6) >= two_power_nat MA * ( - z9 - z11 - 2 ) ). lia.
    rewrite H8. nia.
  - eapply Z.lt_le_trans.
    2: rewrite two_power_nat_two_p. 2: apply two_p_monotone.
    2: split.
    3: apply Nat2Z.inj_le. 3: apply MA_bound. vm_compute. destr. lia.
  - generalize tpMA_pos. lia.
Qed.





















