Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Globalenvs.
Require Import Values_symbolictype.
Require Import Values_symbolic.
Require Import Normalise.
Require Import NormaliseSpec.
Require Import ExprEval.
Require Import Memory.
Require Import Psatz.
Require Import MemRel Align Tactics.
Require Import Permutation PpsimplZ MemReserve.

Fixpoint nat_range' lo n : list nat :=
  match n with
    O => lo :: nil
  | S m => lo :: nat_range' (S lo) m
  end.

Definition nat_range lo hi : list nat :=
  if le_dec lo hi then nat_range' lo (hi-lo)%nat else nil.

Opaque minus.
Lemma nat_range_rew: forall lo hi,
    nat_range lo hi =
    if le_dec lo hi
    then lo :: nat_range (S lo) hi
    else nil.
Proof.
  intros.
  unfold nat_range. destr. destr.
  des hi. lia.
  rewrite <- minus_Sn_m. simpl. f_equal. lia.
  replace hi with lo by lia. rewrite minus_diag. reflexivity.
Qed.

Definition concat {A} := fold_right (@app A) nil.

Fixpoint remove_dbl {A} (D: forall (a b: A), {a = b} + {a <> b}) l :=
  match l with
    nil => nil
  | a::r => if in_dec D a r then remove_dbl D r
           else a :: remove_dbl D r
  end.

Definition box_range cm (bz : block * Z) :=
  let (b,sz) := bz in
  if zlt 0 sz
  then nat_range (Z.to_nat (Int.unsigned (cm b) / 8))
                 (Z.to_nat ((Int.unsigned (cm b) + sz - 1) / 8))
  else nil.

Definition nb_boxes_used_cm m (cm : block -> int) : nat :=
  length
    (remove_dbl eq_nat_dec (concat (map (box_range cm) (Mem.mk_block_list m)))).

Lemma alloc_compat' : forall m l,
    Mem.is_block_list (Mem.mem_blocksize m) (pred (Pos.to_nat (Mem.nextblock m))) l ->
    { al : block -> nat |
      Mem.mk_cm l (Mem.nb_extra m) = Some al /\ Mem.compat_m m Mem.M31 (Mem.box_alloc_to_cm al) }.
Proof.
  intros.
  generalize (Mem.wfm_alloc m).
  intros. unfold Mem.mk_cm.
  des (Mem.make_box_allocation l).
  destr.
  - eexists; split; eauto.
    eapply Mem.box_alloc_to_cm_compat. 3: eauto.
    apply Z2Nat.inj_lt in l0. rewrite Nat2Z.id in l0. lia. lia. lia. auto.
  - eapply Mem.nb_boxes_used_thr in Heqp.
    subst. 
    unfold Mem.nb_boxes_used_m in H0.
    erewrite Mem.nb_used_permut in H0. apply g in H0. easy.
    apply Permutation_sym, Mem.is_block_list_permut_mk_block_list; auto.
Qed.

Definition canon_cm (m:mem) : block -> int.
Proof.
  destruct (alloc_compat' m (Mem.mk_block_list m)).
  apply Mem.is_block_list_mk_block_list.
  destruct a.
  apply Mem.box_alloc_to_cm. apply x.
Defined.

Lemma nat_range_same:
  forall n,
    nat_range n n = n :: nil.
Proof.
  intros.
  unfold nat_range. destr; try lia. rewrite minus_diag; simpl. auto.
Qed.
Opaque Z.mul.

Lemma canon_cm_mul8:
  forall m b,
    exists k,
      Int.unsigned (canon_cm m b) = 8 * k.
Proof.
  intros.
  unfold canon_cm. destr. des a.
  unfold Mem.box_alloc_to_cm.
  rewrite Int.unsigned_repr_eq.
  unfold Int.modulus.
  rewrite ! (two_power_nat_two_p).
  replace (Z.of_nat Int.wordsize) with (Z.of_nat MA + (Z.of_nat Int.wordsize - Z.of_nat MA)).
  rewrite two_p_is_exp.
  rewrite Zmult_mod_distr_l.
  generalize ((Z.of_nat (x b) + 1) mod two_p (Z.of_nat Int.wordsize - Z.of_nat MA)).
  intros.
  replace (Z.of_nat MA) with (3 + Z.of_nat (MA - 3)%nat). rewrite two_p_is_exp.
  change (two_p 3) with 8.
  rewrite <- Z.mul_assoc. eexists; eauto. lia. lia. generalize (MA_bound); lia. lia.
  change Int.wordsize with 32%nat. generalize (MA_bound); lia. 
  change Int.wordsize with 32%nat. generalize (MA_bound); lia. 
Qed.

Lemma int_and_two_p_m1_mul:
  forall i n,
    (0 <= n <= MA)%nat ->
    Int.and i (Int.not (Int.repr (two_power_nat n - 1))) = i ->
    exists k,
      i = Int.mul (Int.repr (two_power_nat n)) k.
Proof.
  Opaque two_power_nat.
  intros. rewrite <- H0.
  exists (Int.shr i (Int.repr (Z.of_nat n))).
  IntFacts.solve_int.
  rewrite Int.bits_not; auto. rewrite Int.testbit_repr; auto.
  rewrite two_power_nat_two_p. rewrite Int.Ztestbit_two_p_m1 by lia.
  rewrite Int.mul_commut.
  rewrite <- (Int.unsigned_repr (Z.of_nat n)).
  rewrite <- Int.shl_mul_two_p. rewrite Int.bits_shl; auto.
  destr. ring.
  rewrite andb_true_r.
  rewrite Int.bits_shr.
  rewrite (Int.unsigned_repr (Int.unsigned _)).
  destr. f_equal. lia. lia.
  apply Int.unsigned_range_2. split. lia. generalize (Int.unsigned_range (Int.repr (Z.of_nat n))). lia.
  split. lia. transitivity 12. generalize MA_bound. lia. vm_compute; congruence.
Qed.

Lemma int_and_two_p_m1_mul_Z:
  forall i n,
    (n <= MA)%nat ->
    Int.and i (Int.not (Int.repr (two_power_nat n - 1))) = i ->
    exists k,
      Int.unsigned i = (two_power_nat n) * k.
Proof.
  intros.
  destruct (fun pf => int_and_two_p_m1_mul _ _ (conj pf H) H0) as [k EQ]. lia.
  rewrite EQ.
  unfold Int.mul.
  rewrite Int.unsigned_repr_eq.
  rewrite Int.unsigned_repr. 
  unfold Int.modulus.
  rewrite ! (two_power_nat_two_p).
  replace (Z.of_nat Int.wordsize) with (Z.of_nat n + (Z.of_nat Int.wordsize - Z.of_nat n)).
  rewrite two_p_is_exp.
  rewrite Zmult_mod_distr_l.
  eexists; eauto.
  lia. 
  change Int.wordsize with 32%nat. generalize (MA_bound); lia. 
  change Int.wordsize with 32%nat. generalize (MA_bound); lia. 
  unfold Int.max_unsigned. split. generalize (two_power_nat_pos n); lia.
  cut (two_power_nat n < Int.modulus). lia.
  unfold Int.modulus. rewrite ! two_power_nat_two_p.
  apply two_p_monotone_strict. split. lia.
  change Int.wordsize with 32%nat. generalize (MA_bound); lia. 
Qed.


Lemma canon_cm_box_range:
  forall cm m b z,
    Mem.compat_m m Mem.M32 cm ->
    0 < z -> z = Mem.size_block m b ->
    length (box_range cm (b,z)) = length (box_range (canon_cm m) (b,z)).
Proof.
  intros.
  unfold box_range.
  destruct (zle z 8).
  - destr. subst.
    generalize (alignment _ _ _ _ H b).
    intros.
    replace (Int.unsigned (cm b) / 8) with
        ((Int.unsigned (cm b) + Mem.size_block m b - 1) / 8).
    rewrite nat_range_same. simpl.
    replace (Z.to_nat (Int.unsigned (canon_cm m b) / 8)) with (Z.to_nat ((Int.unsigned (canon_cm m b) + Mem.size_block m b - 1) / 8)).
    rewrite nat_range_same. simpl. auto.
    destruct (canon_cm_mul8 m b). rewrite H2.
    rewrite (Z.mul_comm 8). rewrite Z_div_mult_full by lia.
    replace (x * 8 + Mem.size_block m b - 1) with (x * 8 + (Mem.size_block m b - 1)) by lia.
    rewrite Z_div_plus_full_l by lia. rewrite Z2Nat.inj_add.
    rewrite Z.div_small. simpl. lia.
    lia. eapply Z.mul_le_mono_pos_l with 8. lia. rewrite <- H2.  change (8*0) with 0. apply Int.unsigned_range.
    apply Z_div_pos. lia. lia.

    revert H1. unfold Mem.nat_mask. unfold Mem.mask.
    Opaque two_power_nat. destr.

    + apply Mem.alignment_ok in Heqo.
      destruct Heqo.
      intros.
      destruct (int_and_two_p_m1_mul_Z _ _ H1 H3). rewrite H4.

      replace (get_size (Mem.mem_blocksize m) b) with (Mem.size_block m b) in H2 by reflexivity.

      destruct (le_dec 3 n).


      (* rewrite ! two_power_nat_two_p. *)
      (* replace (Z.of_nat n) with (Z.of_nat (alignment_of_size (Mem.size_block m b)) + (Z.of_nat n - Z.of_nat (alignment_of_size (Mem.size_block m b)))) by lia. *)
      (* rewrite two_p_is_exp by lia. *)
      (* rewrite <- Z.mul_assoc. *)
      (* generalize (two_p (Z.of_nat n - Z.of_nat (alignment_of_size (Mem.size_block m b))) * x). intros. *)
      (* unfold alignment_of_size in H2. repeat destr_in H2; try lia. *)
      (* IntFacts.elim_div. ppsimpl; lia. *)
      (* IntFacts.elim_div. ppsimpl; lia. *)
      (* IntFacts.elim_div. ppsimpl; lia. *)


      rewrite ! two_power_nat_two_p.
      replace (Z.of_nat n) with (3 + (Z.of_nat n - 3)) by lia.
      rewrite two_p_is_exp by lia.
      change (two_p 3) with 8.

      rewrite <- Z.mul_assoc.
      rewrite (Z.mul_comm 8). rewrite Z_div_mult_full by lia.
      replace (two_p (Z.of_nat n - 3) * x * 8 + Mem.size_block m b - 1) with ((two_p (Z.of_nat n - 3) * x)* 8 + (Mem.size_block m b - 1)) by lia.
      rewrite Z_div_plus_full_l by lia. 
      rewrite Z.div_small. lia.
      lia.

      unfold alignment_of_size in H2. repeat destr_in H2; try lia.
      replace (Mem.size_block m b) with 1 by lia. f_equal. lia.
      replace (Mem.size_block m b) with 2 by lia.
      rewrite ! two_power_nat_two_p.
      replace (Z.of_nat n) with (1 + (Z.of_nat n - 1)) by lia.
      rewrite two_p_is_exp by lia.
      change (two_p 1) with 2.
      rewrite <- Z.mul_assoc.
      generalize (two_p (Z.of_nat n - 1) * x). intros.

      IntFacts.elim_div. ppsimpl; lia.

      rewrite ! two_power_nat_two_p.
      replace (Z.of_nat n) with (2 + (Z.of_nat n - 2)) by lia.
      rewrite two_p_is_exp by lia.
      change (two_p 2) with 4.
      rewrite <- Z.mul_assoc.
      generalize (two_p (Z.of_nat n - 2) * x). intros.

      IntFacts.elim_div. ppsimpl; lia.

    + apply Mem.bounds_mask_consistency in Heqo.
      unfold Mem.size_block, get_size in H0. rewrite Heqo in H0. lia.
  - destr. subst.
    generalize (alignment _ _ _ _ H b).
    intros.
    (* replace (Int.unsigned (cm b) / 8) with *)
    (*     ((Int.unsigned (cm b) + Mem.size_block m b - 1) / 8). *)
    (* rewrite nat_range_same. simpl. *)
    (* replace (Z.to_nat (Int.unsigned (canon_cm m b) / 8)) with (Z.to_nat ((Int.unsigned (canon_cm m b) + Mem.size_block m b - 1) / 8)). *)
    (* rewrite nat_range_same. simpl. auto. *)
    destruct (canon_cm_mul8 m b). rewrite H2.
    rewrite (Z.mul_comm 8). rewrite Z_div_mult_full by lia.
    replace (x * 8 + Mem.size_block m b - 1) with (x * 8 + (Mem.size_block m b - 1)) by lia.
    rewrite Z_div_plus_full_l by lia. rewrite Z2Nat.inj_add.
    2: eapply Z.mul_le_mono_pos_l with 8. 2: lia. 2: rewrite <- H2. 2: change (8*0) with 0. 2: apply Int.unsigned_range.
    2: apply Z_div_pos; lia.
    
    revert H1. unfold Mem.nat_mask. unfold Mem.mask.
    destr.
    + apply Mem.alignment_ok in Heqo.
      destruct Heqo.
      intros.
      destruct (int_and_two_p_m1_mul_Z _ _ H1 H4). rewrite H5.

      rewrite ! two_power_nat_two_p.
      replace (Z.of_nat n) with (3 + (Z.of_nat n - 3)) by lia.
      assert ( 3 <= n )%nat. unfold alignment_of_size in H3.
      replace (get_size (Mem.mem_blocksize m) b) with (Mem.size_block m b) in H3 by reflexivity.
      repeat destr_in H3. lia. lia. lia.
      rewrite two_p_is_exp by lia.
      change (two_p 3) with 8.

      rewrite <- Z.mul_assoc.
      rewrite (Z.mul_comm 8). rewrite Z_div_mult_full by lia.
      replace (two_p (Z.of_nat n - 3) * x0 * 8 + Mem.size_block m b - 1) with ((two_p (Z.of_nat n - 3) * x0)* 8 + (Mem.size_block m b - 1)) by lia.
      rewrite Z_div_plus_full_l by lia. 

      Lemma nat_range_plus_map:
        forall n m p,
          nat_range (n + p) (m + p) = map (fun x => x + p)%nat (nat_range n m).
      Proof.
        unfold nat_range. intros.
        destr. destr; try lia.
        replace (m + p - (n + p))%nat with (m - n)%nat by lia.
        generalize (m - n)%nat.
        clear. intro n0. revert n p. induction n0; simpl; intros; auto.
        f_equal. rewrite <- IHn0. f_equal.
        destr. lia.
      Qed.

      Lemma length_nat_range:
        forall m n,
          (n <= m)%nat ->
          length (nat_range n m)%nat = S (m - n)%nat.
      Proof.
        unfold nat_range.
        intros m n.
        intros. destr.
        generalize (m - n)%nat.
        intro n0; clear. revert n; induction n0; simpl; intros; eauto.
      Qed.

      Lemma length_nat_range_S:
        forall n m p,
          (n <= m)%nat ->
          length (nat_range n m) = length (nat_range (n + p) (m + p)).
      Proof.
        intros. rewrite ! length_nat_range. lia. lia. lia.
      Qed.

      rewrite ! Z2Nat.inj_add. 
      rewrite ! length_nat_range. lia. lia. lia.
      rewrite <- (Z.mul_nonneg_cancel_l (two_p 3)).
      rewrite Z.mul_assoc.
      rewrite <- two_p_is_exp by lia. replace (3 + (Z.of_nat n - 3)) with (Z.of_nat n) by lia.
      rewrite <- two_power_nat_two_p. rewrite <- H5.
      apply Int.unsigned_range. change (two_p 3) with 8; lia.
      apply Z_div_pos. lia. lia.       

    + apply Mem.bounds_mask_consistency in Heqo.
      unfold Mem.size_block, get_size in H0. rewrite Heqo in H0. lia.
Qed.

Lemma canon_cm_box_range':
  forall cm m b z,
    Mem.compat_m m Mem.M32 cm ->
    z = Mem.size_block m b ->
    length (box_range cm (b,z)) = length (box_range (canon_cm m) (b,z)).
Proof.
  intros.
  destruct (zlt 0 z).
  eapply canon_cm_box_range; eauto.
  unfold box_range. destr.
Qed.

Lemma nat_range'_range:
  forall n lo b,
    (In b (nat_range' lo n) ->
     (lo <= b <= lo + n)%nat).
Proof.
  induction n; simpl; intros.
  des H. lia.
  des (eq_nat_dec lo b). lia.
  des H.
  apply IHn in i. lia.
Qed.

Lemma nat_range_range:
  forall lo hi b,
    (In b (nat_range lo hi) ->
     (lo <= b <= hi)%nat).
Proof.
  unfold nat_range. intros. destr_in H.
  apply nat_range'_range in H. lia.
Qed.

Lemma range_nat_range':
  forall n lo b,
    (lo <= b <= lo + n)%nat  ->
    In b (nat_range' lo n).
Proof.
  induction n; simpl; intros.
  des H. lia.
  des (eq_nat_dec lo b). clear Heqs.
  right. apply IHn. lia. 
Qed.

Lemma range_nat_range_range:
  forall lo hi b,
    (lo <= b <= hi)%nat ->
    In b (nat_range lo hi).
Proof.
  unfold nat_range. intros. destr.
  apply range_nat_range'. lia. lia.
Qed.

Lemma lnr_nat_range':
  forall n lo,
    list_norepet (nat_range' lo n).
Proof.
  induction n; simpl; intros.
  repeat constructor. destr.
  constructor. intro IN. apply nat_range'_range in IN. lia.
  eauto.
Qed.

Lemma lnr_nat_range:
  forall lo hi,
    list_norepet (nat_range lo hi).
Proof.
  unfold nat_range. intros. destr.
  apply lnr_nat_range'. constructor.
Qed.

Lemma lnr_box_range:
  forall m a,
    list_norepet (box_range (canon_cm m) a).
Proof.
  unfold box_range. intros. des a.
  destr.
  apply lnr_nat_range.
  constructor.
Qed.

Lemma two_p_div_rew:
  forall n m (LE: (m <= n)%nat)
    x y,
    (two_power_nat n * x +y) / two_power_nat m =
    (two_power_nat n * x) / two_power_nat m + y / two_power_nat m.
Proof.
  intros.
  replace (two_power_nat n * x +y) with (y + x * two_power_nat n) by lia.
  rewrite ! two_power_nat_two_p.
  replace (two_p (Z.of_nat n)) with ((two_p (Z.of_nat n - Z.of_nat m)) * two_p (Z.of_nat m)).
  rewrite Z.mul_assoc.
  rewrite Z_div_plus.
  rewrite Z.add_comm. f_equal.
  rewrite Z.mul_comm.
  replace (two_p (Z.of_nat n - Z.of_nat m) * two_p (Z.of_nat m) * x )
  with ((two_p (Z.of_nat n - Z.of_nat m) * x) * two_p (Z.of_nat m)) by lia.
  rewrite Z_div_mult_full. lia.
  generalize (two_p_gt_ZERO (Z.of_nat m)); lia.
  generalize (two_p_gt_ZERO (Z.of_nat m)); lia.
  rewrite <- two_p_is_exp. f_equal. lia. lia. lia.
Qed.

Lemma two_p_div_rew':
  forall n m (LE: (m <= n)%nat) x,
    (two_power_nat n * x) / two_power_nat m =
    (two_power_nat (n - m) * x).
Proof.
  intros.
  replace (two_power_nat n * x) with (x * two_power_nat n) by lia.
  rewrite ! two_power_nat_two_p.
  replace (two_p (Z.of_nat n)) with ((two_p (Z.of_nat n - Z.of_nat m)) * two_p (Z.of_nat m)).
  rewrite Z.mul_assoc.
  rewrite Z_div_mult_full. rewrite Nat2Z.inj_sub. lia. lia.
  generalize (two_p_gt_ZERO (Z.of_nat m)); lia.
  rewrite <- two_p_is_exp. f_equal. lia. lia. lia.
Qed.

Lemma in_concat:
  forall {A} l (x:A),
    In x (concat l) <-> exists l', In l' l /\ In x l'.
Proof.
  induction l; simpl; intros; eauto.
  - split; intros. easy. dex; destr.
  - rewrite in_app.
    split; intros.
    des H. eexists; split. left; eauto. auto.
    rewrite IHl in i. dex; repeat destr_and.
    eexists; split. right; eauto. auto.
    dex; destr. des H. des o. rewrite IHl. right; eexists; split; eauto.
Qed.

Lemma lnr_canon:
  forall m,
    list_norepet (concat (map (box_range (canon_cm m)) (Mem.mk_block_list m))).
Proof.
  intros.
  unfold canon_cm.
  destr. des a. clear Heqs.
  revert e. unfold Mem.mk_cm.
  destr. destr. intro A; inv A.
  cut (list_norepet (map fst (Mem.mk_block_list m))).
  assert (forall x, In x (Mem.mk_block_list m) -> In x (Mem.mk_block_list m)). auto.
  revert H.
  generalize (Mem.mk_block_list m) at 1 3 4.
  clear - Heqp l. rename l into LT.
  induction l; simpl; intros INIMPL H; eauto. constructor. inv H. trim IHl; auto.
  trim IHl; auto. 
  apply list_norepet_append; auto.
  unfold box_range. destr. destr. apply lnr_nat_range. constructor.
  red; intros.
  rewrite in_concat in H0. dex; destr_and.
  generalize (proj1 (in_map_iff _ _ _) H0).
  intros ((b,z)&BR & IN). subst.
  destruct (zlt 0 (snd a)).
  destruct (zlt 0 z).
  exploit Mem.make_box_allocation_disjoint. 2: eauto. eapply mbla_norepet.
  instantiate (1:= snd a). instantiate (1 := fst a). apply INIMPL. left; apply surjective_pairing.
  instantiate (1:=z). instantiate (1:=b). apply INIMPL. right; auto.
  intro; subst.
  simpl in IN. rewrite in_map_iff in H2. apply H2.
  exists (fst a, z). simpl; auto.
  lia. lia.
  intros.
  revert H; unfold box_range. des a. destr.
  intros IN'; apply nat_range_range in IN'.
  destr_in H0.
  apply nat_range_range in H1.
  revert IN' H1.
  unfold Mem.box_alloc_to_cm.
  rewrite Int.unsigned_repr.
  2: eapply Mem.box_alloc_unsigned_range. 4: apply Heqp. 3: apply Mem.is_block_list_mk_block_list.
  Focus 2.
  rewrite Nat2Z.inj_add in LT. apply Nat2Z.inj_lt. rewrite Z2Nat.id. lia. lia.
  rewrite Int.unsigned_repr.
  2: eapply Mem.box_alloc_unsigned_range. 4: apply Heqp. 3: apply Mem.is_block_list_mk_block_list.
  Focus 2.
  rewrite Nat2Z.inj_add in LT. apply Nat2Z.inj_lt. rewrite Z2Nat.id. lia. lia.
  replace (two_power_nat MA * (Z.of_nat (x b0) + 1) + z0 - 1) with (two_power_nat MA * (Z.of_nat (x b0) + 1) + (z0 - 1)) by lia.
  replace (two_power_nat MA * (Z.of_nat (x b) + 1) + z - 1) with (two_power_nat MA * (Z.of_nat (x b) + 1) + (z - 1)) by lia.
  change 8 with (two_power_nat 3).
  generalize (MA_bound). intros MB.
  rewrite ! two_p_div_rew by lia.
  rewrite ! two_p_div_rew' by lia.
  intros. intro; subst.
  des H4.
  - contradict l4.
    apply lt_not_le.
    apply Nat2Z.inj_lt.
    apply Z.add_lt_mono_r with (p:=1).
    rewrite Z.mul_lt_mono_pos_l with (p:= (two_power_nat (MA-3))).
    eapply Z.le_lt_trans.
    des H1. apply Nat2Z.inj_le in l4.
    rewrite Z2Nat.id in l4. apply l4.
    apply Z.mul_nonneg_nonneg.
    generalize (two_power_nat_pos (MA-3)); lia. lia.
    2: generalize (two_power_nat_pos (MA-3)); lia.
    eapply Z.le_lt_trans.
    des IN'.
    apply Nat2Z.inj_le in l5.
    rewrite Z2Nat.id in l5. apply l5.
    apply Z.add_nonneg_nonneg.
    apply Z.mul_nonneg_nonneg.
    generalize (two_power_nat_pos (MA-3)); lia. lia.
    apply Z.div_pos. lia.
    generalize (two_power_nat_pos 3); lia.
    cut ((z0-1)/two_power_nat 3 < two_power_nat (MA-3) * Z.of_nat (Mem.box_span z0)). lia.
    unfold Mem.box_span. rewrite Z2Nat.id. 
    replace (two_power_nat MA) with (two_power_nat 3 * two_power_nat (MA - 3)%nat).
    rewrite <- Zdiv_Zdiv.
    Focus 2. apply two_power_nat_pos.
    Focus 2. apply two_power_nat_pos.
    Focus 2. rewrite ! two_power_nat_two_p, <- two_p_is_exp. f_equal. generalize MA_bound; lia.
    lia.
    lia.
    Focus 2. apply Z.add_nonneg_nonneg. apply Z.div_pos. lia. apply Z.gt_lt, two_power_nat_pos. lia.
    assert (MOD: forall a b, b > 0 -> a - a mod b = (a / b) * b).
    {
      intros. rewrite Zmod_eq_full. lia. lia.                    
    }
    replace (   two_power_nat (MA - 3) * ((z0 - 1) / two_power_nat 3 / two_power_nat (MA - 3) + 1))
    with (
      ((z0 - 1) / two_power_nat 3 / two_power_nat (MA - 3)) * two_power_nat (MA - 3) + two_power_nat (MA - 3)) by lia.
    rewrite <- (MOD _ (two_power_nat (MA - 3)) (two_power_nat_pos _)).
    cut (((z0-1) / two_power_nat 3) mod two_power_nat (MA - 3) < two_power_nat (MA - 3) ). lia.
    apply Z_mod_lt.
    apply two_power_nat_pos.

  - contradict l4.
    apply lt_not_le.
    apply Nat2Z.inj_lt.
    apply Z.add_lt_mono_r with (p:=1).
    rewrite Z.mul_lt_mono_pos_l with (p:= (two_power_nat (MA-3))).
    eapply Z.le_lt_trans.
    des IN'. apply Nat2Z.inj_le in l4.
    rewrite Z2Nat.id in l4. apply l4.
    apply Z.mul_nonneg_nonneg.
    generalize (two_power_nat_pos (MA-3)); lia. lia.
    2: generalize (two_power_nat_pos (MA-3)); lia.
    eapply Z.le_lt_trans.
    des H1.
    apply Nat2Z.inj_le in l5.
    rewrite Z2Nat.id in l5. apply l5.
    apply Z.add_nonneg_nonneg.
    apply Z.mul_nonneg_nonneg.
    generalize (two_power_nat_pos (MA-3)); lia. lia.
    apply Z.div_pos. lia.
    generalize (two_power_nat_pos 3); lia.
    cut ((z-1)/two_power_nat 3 < two_power_nat (MA-3) * Z.of_nat (Mem.box_span z)). lia.
    unfold Mem.box_span. rewrite Z2Nat.id. 
    replace (two_power_nat MA) with (two_power_nat 3 * two_power_nat (MA - 3)%nat).
    rewrite <- Zdiv_Zdiv.
    Focus 2. apply two_power_nat_pos.
    Focus 2. apply two_power_nat_pos.
    Focus 2. rewrite ! two_power_nat_two_p, <- two_p_is_exp. f_equal. generalize MA_bound; lia.
    lia.
    lia.
    Focus 2. apply Z.add_nonneg_nonneg. apply Z.div_pos. lia. apply Z.gt_lt, two_power_nat_pos. lia.
    assert (MOD: forall a b, b > 0 -> a - a mod b = (a / b) * b).
    {
      intros. rewrite Zmod_eq_full. lia. lia.                    
    }
    replace (   two_power_nat (MA - 3) * ((z - 1) / two_power_nat 3 / two_power_nat (MA - 3) + 1))
    with (
      ((z - 1) / two_power_nat 3 / two_power_nat (MA - 3)) * two_power_nat (MA - 3) + two_power_nat (MA - 3)) by lia.
    rewrite <- (MOD _ (two_power_nat (MA - 3)) (two_power_nat_pos _)).
    cut (((z-1) / two_power_nat 3) mod two_power_nat (MA - 3) < two_power_nat (MA - 3) ). lia.
    apply Z_mod_lt.
    apply two_power_nat_pos.

  - exploit INIMPL. right; eauto. intro INMBL.
    unfold Mem.mk_block_list in INMBL. eapply mbla_in in INMBL.
    subst. rewrite bounds_eq.
    red; simpl. instantiate (1 := Int.zero). rewrite Int.unsigned_zero; lia.
  - exploit INIMPL. left; eauto. intro INMBL.
    unfold Mem.mk_block_list in INMBL. eapply mbla_in in INMBL.
    subst. rewrite bounds_eq.
    red; simpl. instantiate (1 := Int.zero). rewrite Int.unsigned_zero; lia.
  - revert H1.
    unfold box_range. destr.
  - revert H.
    unfold box_range. destr. destr.
  - eapply mbla_norepet.
Qed.

Lemma lnr_remove:
  forall l,
    list_norepet l ->
    remove_dbl eq_nat_dec l = l.
Proof.
  induction 1; simpl; intros; eauto.
  destr.
Qed.

Lemma length_concat:
  forall {A} (l: list (list A)),
    length (concat l) = fold_right Peano.plus O (map (@length A) l).
Proof.
  unfold concat. induction l; simpl; intros; eauto.
  rewrite app_length. auto.
Qed.

Lemma length_remove:
  forall l,
    (length (remove_dbl eq_nat_dec l) <= length l)%nat.
Proof.
  induction l; simpl; intros; eauto.
  destr. lia. lia.
Qed.

Lemma eq_le: forall  (n m: nat), n = m -> (n <= m)%nat.
Proof. intros; lia. Qed.

Lemma canon_cm_more_boxes:
  forall cm m,
    Mem.compat_m m Mem.M32 cm ->
    (nb_boxes_used_cm m cm <= nb_boxes_used_cm m (canon_cm m))%nat.
Proof.
  unfold nb_boxes_used_cm.
  intros.
  rewrite (lnr_remove _ (lnr_canon _)).
  etransitivity. eapply length_remove.
  rewrite ! length_concat.
  apply eq_le.
  f_equal.
  rewrite ! map_map. simpl.
  apply list_map_exten.
  intros.
  des x.
  symmetry; eapply canon_cm_box_range'; eauto.
  unfold Mem.mk_block_list in H0. eapply mbla_in in H0. auto.
Qed.

Definition inject_well_behaved (f: meminj) (m: mem) :=
  forall b, f b = None -> Mem.size_block m b <= 8 /\ (Mem.mask m b <= 3)%nat.

Definition is_injected (f: meminj) (b: block * Z) :=
  match f (fst b) with
    Some b2  => true
  | None => false
  end.
Record inj_well_behaved f m1 m2 :=
  {
    iwb_o2o: Mem.one2oneinject f;
    iwb_wb: inject_well_behaved f m1;
    iwb_bounds: forall b b' delta, f b = Some (b',delta) -> Mem.size_block m1 b = Mem.size_block m2 b';
    iwb_mask: forall b b' delta, f b = Some (b',delta) -> Mem.mask m1 b = Mem.mask m2 b';
    iwb_no_oota: forall b', Mem.valid_block m2 b' -> exists b delta, f b = Some (b', delta);
    iwb_inj: forall b1 b2 b' delta1 delta2, f b1 = Some (b', delta1) -> f b2 = Some (b', delta2) -> b1 = b2
  }.


Lemma in_bl:
  forall m b1 z1
    (i: In (b1, z1) (Mem.mk_block_list m)),
    (Pos.to_nat b1 <= pred (Pos.to_nat (Mem.nextblock m)))%nat.
Proof.
  intro m.
  unfold Mem.mk_block_list.
  generalize (pred (Pos.to_nat (Mem.nextblock m))).
  intros.
  destruct (le_dec (Pos.to_nat b1) n); auto.
  apply (in_map fst) in i.
  contradict i.
  eapply Alloc.mbla_not_above. simpl. lia.
Qed.

Lemma nin_list_ints:
  forall n m (ME: (m > n)%nat),
    ~
      In (Pos.of_nat m)
      (map (fun x : nat => Pos.of_nat x) (Alloc.list_ints n)).
Proof.
  Local Opaque Pos.of_nat.
  induction n; simpl; intros; eauto.
  trim (IHn m). lia.
  intro IN. destruct IN as [IN|IN]; eauto.
  apply Nat2Pos.inj in IN. lia. auto. lia.
Qed.


Lemma lnr_mbl:
  forall m,
    list_norepet (map fst (Mem.mk_block_list m)).
Proof.
  unfold Mem.mk_block_list.
  intros.
  generalize (pred (Pos.to_nat (Mem.nextblock m))).
  Local Opaque Pos.of_nat.
  induction n; simpl; intros; eauto.
  constructor.
  constructor; auto.
  rewrite map_map. simpl.
  apply nin_list_ints. lia.
Qed.

Lemma part_inj_permut:
  forall sm ei f m1 m2
    (IWB: inj_well_behaved f m1 m2)
    (MINJ: Mem.inject sm ei f m1 m2),
    let (l1,l2) := partition (is_injected f) (Mem.mk_block_list m1) in
    Permutation (Mem.mk_block_list m1) (l1 ++ l2) ->
    Permutation
      (map fst (Mem.mk_block_list m2))
      (filter_map (fun b : block =>
                     match f b with
                       Some (b',delta) => Some b'
                     | None => None
                     end) (map fst (Mem.mk_block_list m1))).
Proof.
  intros.
  destr. rename l into l1.
  rename Heqp into PI.
  intro P.
  assert (Forall (fun b : block =>
                    exists b',
                      f b = Some (b',0) /\
                      In b' (map fst (Mem.mk_block_list m2))) (map fst l1)).
  {
    rewrite Forall_forall.
    intros b IN.
    rewrite in_map_iff in IN. dex; destr_and. des x.
    erewrite in_partition_l in H0. 2: eauto.
    destruct H0 as [IN FB].
    unfold is_injected in FB. destr_in FB. des p.
    exists b. exploit iwb_o2o. eauto. apply Heqo. intro; subst.
    repSplit; auto.
    eapply mbla_below_in.
    exploit Mem.mi_mappedblocks. eauto. eauto. intros.
    apply Pos2Nat.inj_lt in H. lia.
  }

  assert (Forall
            (fun b' : block  =>
               exists b, f b = Some (b',0) /\
                    In b (map fst l1))
            (map fst (Mem.mk_block_list m2))).
  {
    rewrite Forall_forall. intros b' IN.
    apply in_map_iff in IN. dex. des x. des IN.
    exploit in_bl.  apply i. intro LE.
    assert (Mem.valid_block m2 b'). red.
    apply Pos2Nat.inj_lt. lia.
    destruct (iwb_no_oota _ _ _ IWB _ H0).
    dex.
    exploit iwb_o2o; eauto. intro; subst.
    exists x; repSplit; auto.

    rewrite in_map_iff. eexists. split.
    2: erewrite in_partition_l. 3: eauto. 2: split.
    2: apply Alloc.mbla_below_in'. simpl; eauto.
    2: unfold is_injected; simpl; rewrite H1; auto.
    exploit Mem.valid_block_inject_1. apply H1. eauto. intro v.
    red in v. rewrite Pos2Nat.inj_lt in v. lia.
  }
  
  assert (list_norepet (map fst l1)).
  {
    eapply lnr_partition' in PI. destr.
    apply lnr_mbl.
  }
  assert (list_norepet (map fst (Mem.mk_block_list m2))).
  {
    apply lnr_mbl.
  }
  
  rewrite <- permut_filter_map.
  2: apply Permutation_sym; apply Permutation_map; apply P.

  generalize (in_partition_r _ _ _ _ PI). intros.
  assert (forall b, In b (map fst l0) <-> (In b (map fst (Mem.mk_block_list m1)) /\ f b = None)).
  {
    intros.
    rewrite ! in_map_iff.
    split; intros; dex; destr_and; des x; eauto.
    apply H3 in H5. split. exists (b0,z); repSplit; destr.
    unfold is_injected in H5; destr_in H5.
    exists (b0,z). split; auto. rewrite H3. unfold is_injected. destr.
  }
  clear H3.

  revert H H0 H1 H2 H4.
  rewrite map_app.
  generalize (map fst l1).
  generalize (map fst (Mem.mk_block_list m2)). clear - MINJ IWB.
  induction l; simpl; intros l2 Fl1 Fl LNR1 LNR2 SpecL0; eauto.
  - inv Fl1. erewrite not_inj_filter_map. constructor. simpl. intros.
    rewrite SpecL0 in H.  destr. 
    dex; destr.
  - inv Fl.
    destruct H1 as (b & FB & IN).
    inv LNR2.
    inv Fl1. destr. repeat destr. destr_in Heqo. des p. inv Heqo.
    dex. des H. inv e. inv LNR1.
    des (peq b x).
    + rewrite FB in Heqo0. inv Heqo0.
      apply perm_skip.
      apply IHl; auto.
      * rewrite Forall_forall in *.
        intros x0 i.
        exploit H0. apply i.
        intros [b'0 [A B]].
        exists b'0; repSplit; auto. des B. 
        cut (x = x0). destr.
        eapply iwb_inj; eauto.
      * rewrite Forall_forall in *.
        intros x0 i.
        exploit H2. apply i.
        intros [b'0 [A C]].
        exists b'0; repSplit; auto. des C.
    + des IN. des o.
      exploit iwb_inj. eauto. apply Heqo0. apply FB. destr.
      rewrite Forall_forall in H0, H2.
      generalize (in_split _ _ i0). intros [l2' [l3 EQ]].
      generalize (in_split _ _ i). intros [l4 [l5 EQ']].
      subst. simpl in *.
      generalize (H2 _ i0) (H0 _ i). intros; dex; repeat destr_and.

      Lemma filter_map_app:
        forall {A B:Type} (f: A -> option B) a b,
          filter_map f (a ++ b) = filter_map f a ++ filter_map f b.
      Proof.
        induction a; simpl; intros; eauto.
        destr.
      Qed.
      rewrite filter_map_app.

      cut (Permutation (l2' ++ l3)
                       (filter_map (fun x => match f x with
                                            Some (b'0,_) => Some b'0
                                          | None => None
                                          end) (l4 ++ l5 ++ map fst l0))).
      {
        simpl; intros.
        eapply perm_trans.
        apply perm_skip.
        eapply perm_trans.
        apply Permutation_sym.
        apply Permutation_middle. apply Permutation_refl.
        eapply perm_trans. apply perm_swap.
        apply perm_skip.
        rewrite <- filter_map_app.
        erewrite permut_filter_map.
        Focus 2.
        apply Permutation_sym. apply Permutation_app. apply Permutation_middle.
        apply Permutation_refl. simpl. rewrite H4.
        des (peq a b'0).
        apply perm_skip.
        rewrite app_ass. auto.
      }

      des (peq a b'0).
      clear H7 Heqs0. clear H4.
      exploit iwb_inj. eauto. apply Heqo0. apply H. intro; subst.
      clear H8. clear Heqo0.
      assert (b' <> b'0). destr.

      specialize (IHl ((l4 ++ b0 :: l5))).
      
      trim IHl.
      {
        rewrite Forall_forall. intros x IN.
        des (peq b0 x). rewrite H. eexists; split; eauto.
        exploit H0.  rewrite in_app in IN.  des IN. apply in_app. left; eauto.
        des i1. apply in_app. right. right. auto. 
        intros [b'1 [A  C]].
        des (peq x b).
        clear - H6 IN n. exfalso.
        - eapply permutation_norepet in H6. Focus 2.
          apply Permutation_sym. apply Permutation_middle.
          inv H6.
          rewrite in_app in *; destr.
        - des C.
          exploit iwb_inj. eauto. apply A. apply FB. intro; subst. destr.
          rewrite A. eexists; split; eauto.
      }
      trim IHl.
      {
        clear IHl.
        rewrite Forall_forall. intros x IN.
        des (peq b' x).
        - rewrite <- H. exists b0; split; auto.
          rewrite in_app. destr.
        - 
          assert (In x (l2' ++ l3)).
          {
            rewrite in_app in IN |- *; destr.
          }
          clear IN.

          exploit H2.
          rewrite in_app in H7 |- *. destruct H7. left; apply H7. destr. 
          intros (b1 & DB1 & IN1).
          rewrite <- DB1.
          exists b1; split; auto.
          des (peq b1 b0).
          {
            des IN1.
            rewrite in_app in *.
            des i1.
          }
      } 
      trim IHl.
      eapply permutation_norepet. apply Permutation_middle.
      eapply permutation_norepet in H6. 2: apply Permutation_sym, Permutation_middle.
      inv H6. constructor; auto.
      clear - H5. rewrite in_app in *; destr.
      trim IHl. auto.

      trim IHl.
      auto. 

      move IHl at bottom.

      rewrite ! filter_map_app in IHl |- *. simpl in IHl.
      rewrite H in IHl.
      rewrite <- Permutation_middle in IHl.
      rewrite app_ass in IHl. simpl in IHl.
      rewrite <- Permutation_middle in IHl.
      eapply Permutation_cons_inv in IHl. auto.
    + dex. destr_and. rewrite H in Heqo. destr.
Qed.



Definition box_range' m cm b :=
  let sz := (Mem.size_block m b) in
  box_range cm (b,sz).

Lemma box_range'_eq:
  forall cm m,
  map (box_range cm) (Mem.mk_block_list m) =
  map (box_range' m cm) (map fst (Mem.mk_block_list m)).
Proof.
  unfold box_range'.
  intros.
  unfold Mem.mk_block_list.
  generalize (mbla_in (Mem.size_block m) (pred (Pos.to_nat (Mem.nextblock m)))).
  generalize (mk_block_list_aux (Mem.size_block m) (pred (Pos.to_nat (Mem.nextblock m)))).
  induction l; simpl; intros; eauto.
  f_equal. des a. rewrite (H _ _ (or_introl eq_refl)). auto. auto.
Qed.

Lemma perm_concat:
  forall {A} (l l': list (list A)) (P: list_forall2 (@Permutation A) l l'),
    Permutation (concat l) (concat l').
Proof.
  induction 1; simpl; intros; eauto. apply Permutation_app; auto.
Qed.

Lemma fold_right_plus_permut:
  forall l l' (P: Permutation l l'),
    fold_right Peano.plus O l = fold_right Peano.plus O l'.
Proof.
  induction 1; simpl; intros; eauto.
  lia.
  lia.
Qed.

Lemma fold_right_plus_app:
  forall l l' ,
    fold_right Peano.plus O (l ++ l') = (fold_right Peano.plus O l + fold_right Peano.plus O l')%nat.
Proof.
  induction l; simpl; intros; eauto.
  rewrite IHl. lia.
Qed.

Lemma filter_map_ext:
  forall {A B} (f f': A -> option B) l
    (EXT: forall x, In x l -> f x = f' x),
    filter_map f l = filter_map f' l.
Proof.
  induction l; simpl; intros; eauto.
  rewrite EXT; auto.
  trim IHl. intros; apply EXT; auto. destr.
Qed.

Lemma partition_l:
  forall {A} (l: list A) f ll lr,
    partition f l = (ll,lr) ->
    ll = filter_map (fun b => if f b then Some b else None) l.
Proof.
  induction l; simpl; intros; eauto. inv H; auto.
  repeat destr_in H; inv H; f_equal; eauto.
Qed.

Lemma map_filter_map:
  forall {A B C D}
    (f: B -> C) (g: A -> option B)
    (f': A -> D) (g': D -> option C)
    (EQ: forall a b, g a = Some b -> exists c, g' (f' a) = Some c /\ f b = c)
    (EQ': forall a c, g' (f' a) = Some c -> exists b, g a = Some b)
    (l: list A),
    map f (filter_map g l) = filter_map g' (map f' l).
Proof.
  induction l; simpl; intros; eauto.
  repeat destr.
  - exploit ((EQ a b)). eauto. rewrite Heqo0. intros (c0 & ? & ?). inv H. f_equal; auto.
  - apply EQ in Heqo. dex; destr.
  - apply EQ' in Heqo0. dex; destr.
Qed.

Lemma map_filter_map':
  forall {A B C} (g: A -> option B) (f: B -> C) l,
    map f (filter_map g l) = filter_map (fun x => match g x with
                                                 Some gx => Some (f gx)
                                               | None => None
                                               end) l.
Proof.
  induction l; simpl; intros; eauto.
  destr.
Qed.

Lemma inject_well_behaved_diff_blocks:
  forall sm ei f m1 m2
    (MINJ: Mem.inject sm ei f m1 m2)
    (IWB: inj_well_behaved f m1 m2)
    l0 l1
    (PART: partition (is_injected f) (Mem.mk_block_list m1) = (l0,l1))
  ,
    (* exists F, *)
      (length ((concat (map (box_range (canon_cm m2)) (Mem.mk_block_list m2)))) +
       fold_right Peano.plus O (map (fun x => length (box_range' m1 (canon_cm m1) x)) (map fst l1)))%nat =
      length (concat (map (box_range (canon_cm m1)) (Mem.mk_block_list m1))).
Proof.
  intros.
  generalize (part_inj_permut _ _ _ _ _ IWB MINJ).
  rewrite PART. intros.
  exploit (partition_app_perm (A:= block*Z)). eauto. intro PERM.
  trim H. auto.
  rewrite ! box_range'_eq.
  rewrite ! length_concat.
  rewrite ! (map_map (box_range' _ _) (@length _)).
  generalize (Permutation_map (fun x => length (box_range' m1 (canon_cm m1) x))
                              (Permutation_map fst PERM)). intro P.
  rewrite (fold_right_plus_permut _ _ P).
  rewrite map_app.
  rewrite map_app.
  rewrite fold_right_plus_app.
  generalize (Permutation_map (fun x => length (box_range' m2 (canon_cm m2) x)) H). intro P'.
  rewrite (fold_right_plus_permut _ _ P').
  f_equal.
  rewrite (partition_l _ _ _ _ PART).
  erewrite map_filter_map with (f':=fst) (g':=fun b => match f b with
                                                     Some (b',delta) => Some b
                                                   | None => None
                                                   end).
  Focus 2.
  intros. unfold is_injected in H0. destr. inv H0. des b. des p. eexists; split; eauto.
  Focus 2.
  intros. unfold is_injected. des a. des (f b). des p. inv H0. eexists; eauto.
  f_equal.
  erewrite ! map_filter_map'.
  apply filter_map_ext.
  {
    clear - IWB.
    intros. des (f x). des p.
    unfold box_range'.
    unfold box_range.
    erewrite <- iwb_bounds; eauto.
    destr.
    destruct (canon_cm_mul8 m2 b). rewrite H0.
    rewrite (Z.mul_comm 8). rewrite Z_div_mult_full by lia.
    replace (x0 * 8 + Mem.size_block m1 x - 1) with (x0 * 8 + (Mem.size_block m1 x - 1)) by lia.
    rewrite Z_div_plus_full_l by lia. rewrite Z2Nat.inj_add.
    2: eapply Z.mul_le_mono_pos_l with 8. 2: lia. 2: rewrite <- H0. 2: change (8*0) with 0.
    2: apply Int.unsigned_range.
    2: apply Z_div_pos; lia.
    destruct (canon_cm_mul8 m1 x). rewrite H1.
    rewrite (Z.mul_comm 8). rewrite Z_div_mult_full by lia.
    replace (x1 * 8 + Mem.size_block m1 x - 1) with (x1 * 8 + (Mem.size_block m1 x - 1)) by lia.
    rewrite Z_div_plus_full_l by lia. rewrite Z2Nat.inj_add.
    2: eapply Z.mul_le_mono_pos_l with 8. 2: lia. 2: rewrite <- H1. 2: change (8*0) with 0.
    2: apply Int.unsigned_range.
    2: apply Z_div_pos; lia.
    rewrite ! length_nat_range by lia. f_equal. lia.
  }
Qed.

Lemma inject_well_behaved_diff_blocks_num:
  forall sm ei f m1 m2
    (MINJ: Mem.inject sm ei f m1 m2)
    (IWB: inj_well_behaved f m1 m2)
    l0 l1
    (PART: partition (is_injected f) (Mem.mk_block_list m1) = (l0,l1)),
    (nb_boxes_used_cm m2 (canon_cm m2) + fold_right Peano.plus O (map (fun x => length (box_range' m1 (canon_cm m1) x)) (map fst l1)) = nb_boxes_used_cm m1 (canon_cm m1))%nat.
Proof.
  intros.
  unfold nb_boxes_used_cm.
  rewrite ! (lnr_remove _ (lnr_canon _)).
  eapply inject_well_behaved_diff_blocks. eauto. eauto. eauto.
Qed.


Lemma length_box_range_canon_cm:
  forall m b z, 0 < z ->
    length (box_range (canon_cm m) (b,z)) = (S (Z.to_nat ((z - 1)/ 8))).
Proof.
  intros m b z LT.
  unfold box_range.
  destr.
  destruct (canon_cm_mul8 m b). rewrite H.
  rewrite (Z.mul_comm 8). rewrite Z_div_mult_full by lia.
  replace (x * 8 + z - 1) with (x * 8 + (z - 1)) by lia.
  rewrite Z_div_plus_full_l by lia. rewrite Z2Nat.inj_add.
  2: eapply Z.mul_le_mono_pos_l with 8. 2: lia. 2: rewrite <- H. 2: change (8*0) with 0.
  2: apply Int.unsigned_range.
  2: apply Z_div_pos; lia.
  rewrite ! length_nat_range by lia.
  lia.
Qed.

Lemma nb_boxes_used_cm_nb_boxes_used_m:
  forall m,
    (nb_boxes_used_cm m (canon_cm m) <= Mem.nb_boxes_used_m m * NPeano.pow 2 (MA-3))%nat.
Proof.
  intros.
  unfold Mem.nb_boxes_used_m, nb_boxes_used_cm.
  intros. rewrite ! (lnr_remove _ (lnr_canon _)).
  rewrite length_concat.
  etransitivity.
  Focus 2.
  apply NPeano.Nat.mul_le_mono_nonneg_r. lia.
  apply NPeano.Nat.le_add_r.
  generalize (Mem.mk_block_list m).
  induction l; simpl; intros. lia.  destruct a.
  destruct (zlt 0 z).
  rewrite Mem.nb_boxes_used_cons.
  rewrite length_box_range_canon_cm; auto.
  cut (S (Z.to_nat ((z-1)/8)) <= Mem.box_span z * NPeano.pow 2 (MA - 3))%nat. lia.
  unfold Mem.box_span.
  rewrite Z2Nat.inj_add.
  replace (two_power_nat MA) with (two_power_nat 3 * two_power_nat (MA - 3)%nat).
  rewrite <- Zdiv_Zdiv.
  Focus 2. apply two_power_nat_pos.
  Focus 2. apply two_power_nat_pos.
  Focus 2. rewrite ! two_power_nat_two_p, <- two_p_is_exp. f_equal. generalize MA_bound; lia.
  lia.
  lia.
  Focus 2. apply Z.div_pos. lia. apply Z.gt_lt, two_power_nat_pos.
  Focus 2. lia.
  simpl.
  change (two_power_nat 3) with 8.
  cut (0 <= (z-1)/8). 
  generalize ((z-1)/8). simpl; intros.
  apply Nat2Z.inj_le.
  rewrite Nat2Z.inj_mul.
  replace (Z.of_nat (Z.to_nat (z0 / two_power_nat (MA - 3)) + Pos.to_nat 1))
  with ((z0 / two_power_nat (MA - 3)) + 1).
  transitivity ((z0 /two_power_nat (MA - 3) * two_power_nat (MA - 3)) + two_power_nat (MA - 3)).
  assert (MOD: forall a b, b > 0 -> a - a mod b = (a / b) * b).
  {
    intros. rewrite Zmod_eq_full. lia. lia.                    
  }
  rewrite <- (MOD z0 (two_power_nat (MA - 3)) (two_power_nat_pos _)).
  rewrite Nat2Z.inj_succ by lia. rewrite Z2Nat.id by lia.
  cut (z0 mod two_power_nat (MA - 3) < two_power_nat (MA - 3) ). lia.
  apply Z_mod_lt.
  apply two_power_nat_pos.
  rewrite Z.mul_add_distr_r.
  rewrite (InstanceZ.npow_inj 2 (MA-3)).
  simpl. rewrite <- two_p_correct.
  rewrite <- two_power_nat_two_p.
  lia.
  rewrite Nat2Z.inj_add. simpl. rewrite Z2Nat.id. lia.
  apply Z.div_pos. lia.
  apply Z.gt_lt, two_power_nat_pos.
  apply Z.div_pos. lia. lia.
  unfold box_range at 1. destr.
  rewrite Mem.nb_boxes_used_cons.
  replace (Mem.box_span z) with O. lia.
  unfold Mem.box_span.
  cut ((z - 1)/ two_power_nat MA + 1 <= 0). unfold Z.to_nat. destr. lia. 
  cut ((z - 1)/ two_power_nat MA < 0). lia.
  apply BigNumPrelude.Zdiv_neg. lia. apply Z.gt_lt, two_power_nat_pos.
Qed.

Definition has_free_boxes m cm N :=
  (nb_boxes_used_cm m cm + N < Z.to_nat Mem.nb_boxes_max * NPeano.pow 2 (MA-3))%nat.

Lemma mult_lt_le_mono:
  forall (a b c d: nat),
    (a < c)%nat -> (O < b <= d)%nat ->
    (a * b < c * d)%nat.
Proof.
  intros.
  eapply lt_le_trans.
  apply mult_lt_compat_r. apply H. apply H0.
  apply NPeano.Nat.mul_le_mono_nonneg_l. lia. lia.
Qed.

Definition nb_boxes8_max := (Z.to_nat Mem.nb_boxes_max * NPeano.pow 2 (MA - 3))%nat.

Definition get_free_boxes m cm :=
  fold_left
    (fun (acc: list nat) b =>
       filter (fun x => negb (in_dec eq_nat_dec x (box_range' m cm b))) acc)
    (map fst (Mem.mk_block_list m))
    (list_ints nb_boxes8_max).

Lemma in_fold_left_filter:
  forall {A B} (f: A -> B -> bool) l lacc x ,
    In x (fold_left (fun acc b => filter (f b) acc) l lacc) ->
    In x lacc /\ Forall (fun y => f y x = true) l.
Proof.
  induction l; simpl; intros; eauto.
  apply IHl in H. rewrite filter_In in H.
  des H. des a0. repeat constructor; auto.
Qed.

Lemma in_gfb:
  forall x m cm ,
    In x (get_free_boxes m cm) ->
    In x (list_ints nb_boxes8_max) /\
    Forall (fun y => negb (in_dec eq_nat_dec x (box_range' m cm y)) = true) (map fst (Mem.mk_block_list m)).
Proof.
  intros. unfold get_free_boxes in H. apply in_fold_left_filter in H. auto.
Qed.

Lemma below_in_list_ints:
  forall m b0,
    (0 < b0 <= m)%nat ->
    In b0 (list_ints m).
Proof.
  induction m; simpl; intros; eauto. lia.
  destruct (eq_nat_dec (S m) b0); auto.
  right. apply IHm. lia.
Qed.

Lemma below_in_list_ints':
  forall m b0,
    In b0 (list_ints m) ->
    (0 < b0 <= m)%nat.
Proof.
  induction m; simpl; intros; eauto. easy. 
  destruct (eq_nat_dec (S m) b0); auto.
  subst. lia. des H. apply IHm in i. lia.
Qed.

Lemma list_ints_In:
  forall m b,
    In b (list_ints m) <-> (0 < b <= m)%nat.
Proof.
  split. apply below_in_list_ints'.
  apply below_in_list_ints.
Qed.

Lemma box_span_mu:
  (Mem.box_span Int.max_unsigned - 2)%nat = Z.to_nat Mem.nb_boxes_max.
Proof.
  unfold Mem.box_span, Mem.nb_boxes_max.
  apply Nat2Z.inj. rewrite ! Z2Nat.id.
  rewrite Nat2Z.inj_sub.
  rewrite ! Z2Nat.id.
  simpl. f_equal.
  replace (Int.max_unsigned - 1) with (two_power_nat MA * two_power_nat (32 - MA) + (- 2)).
  rewrite two_p_div_rew.
  rewrite Z.mul_comm, Z_div_mult_full.
  replace (-2 / two_power_nat MA) with (-1). lia.
  - unfold Z.div, Z.div_eucl.
    repeat destr.
    generalize Mem.tpMA_pos.
    generalize Mem.tpMA_sup8.

    repeat destr_in Heqp; try lia; intros;
      inv Heqp.
    repeat destr_in Heqp0. inv Heqp0.
    destr_in Heqp1. inv Heqp1. lia.
    inv Heqp1.
    apply Z.leb_nle in Heqb0. lia. inv Heqp0.
    destr_in Heqp1. inv Heqp1.
    apply Z.ltb_nlt in Heqb. lia. inv Heqp1. lia.
    repeat destr_in Heqp0. inv Heqp0.
    destr_in Heqp1. inv Heqp1. lia.
    inv Heqp1.
    apply Z.leb_nle in Heqb0. lia. inv Heqp0.
    destr_in Heqp1. inv Heqp1.
    apply Z.ltb_nlt in Heqb. lia. inv Heqp1. lia.
    repeat destr_in Heqp0. inv Heqp0.
    destr_in Heqp1. inv Heqp1. lia.
    inv Heqp1.
    apply Z.leb_nle in Heqb0. lia. inv Heqp0.
    destr_in Heqp1. inv Heqp1.
    apply Z.ltb_nlt in Heqb. lia. inv Heqp1.
    apply Z.ltb_nlt in Heqb. lia.

  - generalize Mem.tpMA_pos. lia.
  - lia.
  - rewrite ! two_power_nat_two_p, <- two_p_is_exp by lia.
    generalize MA_bound. intros.
    replace (Z.of_nat MA + Z.of_nat (32 - MA)) with 32.
    change Int.max_unsigned with (two_power_nat 32 - 1).   rewrite two_power_nat_two_p. lia. lia.
  - apply Z.add_nonneg_nonneg.
    apply Z.div_pos. vm_compute. destr.
    apply Z.gt_lt, Mem.tpMA_pos. lia.
  - change 2%nat with (1+1)%nat.
    rewrite Z2Nat.inj_add.
    apply NPeano.Nat.add_le_mono_r.
    transitivity (Z.to_nat ((Int.max_unsigned - 1) / two_power_nat 12)).
    rewrite two_power_nat_two_p.
    apply Nat2Z.inj_le. rewrite Z2Nat.id. vm_compute. destr.
    apply Z.div_pos. vm_compute; destr. apply Z.gt_lt, two_p_gt_ZERO. lia.
    apply Nat2Z.inj_le. rewrite ! Z2Nat.id. apply Z.div_le_compat_l.
    vm_compute; destr. generalize MA_bound.
    split. apply Z.gt_lt, Mem.tpMA_pos. rewrite ! two_power_nat_two_p. apply two_p_monotone; auto. lia.
    apply Z.div_pos. vm_compute; destr. apply Z.gt_lt, Mem.tpMA_pos.
    apply Z.div_pos. vm_compute; destr. apply Z.gt_lt, two_power_nat_pos.
    apply Z.div_pos. vm_compute; destr. apply Z.gt_lt, Mem.tpMA_pos. lia.
  - transitivity (two_power_nat 20 - 2). vm_compute; destr.
    generalize (two_p_monotone 20 (Z.of_nat (32 - MA))).
    rewrite ! two_power_nat_two_p. generalize MA_bound. lia.
Qed.


Lemma in_gfb':
  forall x m cm ,
    Mem.compat_m m Mem.M32 cm ->
    In x (get_free_boxes m cm) ->
    (0 < x <= nb_boxes8_max)%nat /\
    forall b o o',
      Mem.in_bound_m (Int.unsigned o) m b ->
      0 <= Int.unsigned o' < 8 ->
      Int.unsigned (Int.add (cm b) o) <> Int.unsigned (Int.add (Int.repr (8 * Z.of_nat x)) o').  
Proof.
  intros x m cm COMP IN.
  apply in_gfb in IN. des IN.
  rewrite list_ints_In in i.
  split; auto.
  intros b o o' IB IB'.
  rewrite Forall_forall in f. trim (f b).
  eapply mbla_below_in.
  eapply Mem.in_bound_valid in IB. red in IB. apply Pos2Nat.inj_lt in IB. lia.
  generalize IB; intro MIB.
  des (in_dec eq_nat_dec x (box_range' m cm b)).

  unfold box_range', box_range in n.
  red in IB. rewrite bounds_eq in IB.
  red in IB. simpl in IB. 
  clear Heqs. destr_in n; [| lia].

  assert (~ (Z.to_nat (Int.unsigned (cm b) / 8) <= x <= Z.to_nat ((Int.unsigned (cm b) + Mem.size_block m b - 1)/8)))%nat as RNG.
  intro RNG. apply range_nat_range_range in RNG. destr.

  clear n.
  intro EQ.
  apply RNG. clear RNG.

  unfold Int.add in EQ.
  rewrite (Int.unsigned_repr ( 8 * _ )) in EQ.
  rewrite ! Int.unsigned_repr in EQ.
  - replace (Int.unsigned (cm b)) with ((Int.unsigned o' - Int.unsigned o) + Z.of_nat x * 8) by lia.
    clear EQ.
    rewrite Z_div_plus_full by lia.
    replace ((Int.unsigned o' - Int.unsigned o) + Z.of_nat x * 8 + Mem.size_block m b - 1)
      with ((Int.unsigned o' - Int.unsigned o + (Mem.size_block m b - 1)) + Z.of_nat x * 8) by lia.
    rewrite Z_div_plus_full by lia.
    split.
    + apply Nat2Z.inj_le.

      assert ( forall n : Z, Z.of_nat (Z.to_nat n) = Z.max 0 n).
      {
        intros.
        rewrite Zmax_spec. destr. des n. lia.
        apply Z2Nat.id. lia. 
      }
      rewrite H.
      rewrite Zmax_spec. destr. lia.
      cut ((Int.unsigned o' - Int.unsigned o) / 8 <= 0). lia.
      destruct (zlt (Int.unsigned o' - Int.unsigned o) 0).
      eapply BigNumPrelude.Zdiv_neg in l0.
      apply Z.lt_le_incl; eauto. lia.
      rewrite Z.div_small. lia. lia.
    + apply Nat2Z.inj_le.
      rewrite Z2Nat.id.
      cut (0 <= (Int.unsigned o' - Int.unsigned o + (Mem.size_block m b - 1)) / 8). lia.
      apply Z.div_pos. 2: lia.
      transitivity ((Mem.size_block m b - Int.unsigned o - 1) + Int.unsigned o'). 2: lia.
      lia.
      apply Z.add_nonneg_nonneg.
      apply Z.div_pos. 2: lia.
      transitivity ((Mem.size_block m b - Int.unsigned o - 1) + Int.unsigned o'). 2: lia.
      lia.
      lia.
  - split. lia. transitivity (8 * Z.of_nat nb_boxes8_max + Int.unsigned o'). lia.
    unfold nb_boxes8_max.
    replace (Z.to_nat Mem.nb_boxes_max) with (Mem.box_span Int.max_unsigned - 2)%nat.
    replace (8 * Z.of_nat ((Mem.box_span Int.max_unsigned - 2) * NPeano.pow 2 (MA - 3)))
      with (two_power_nat MA * (Z.of_nat (Mem.box_span Int.max_unsigned) - 2)).
    rewrite Zmult_minus_distr_l.
    rewrite Mem.box_span_align.
    cut (align Int.max_unsigned (two_power_nat MA) + Int.unsigned o' <= (Int.max_unsigned + two_power_nat MA) + two_power_nat MA). lia.
    apply Z.add_le_mono.
    rewrite Mem.align_ge2.
    apply Z.add_le_mono_l.
    cut (   - 1  <= (Int.max_unsigned - 1) mod two_power_nat MA ). lia.
    etransitivity. 
    2: apply Z_mod_lt. lia.
    apply two_power_nat_pos.
    apply two_power_nat_pos. transitivity (two_power_nat 3). change (two_power_nat 3) with 8. lia.
    rewrite ! two_power_nat_two_p. apply two_p_monotone. generalize MA_bound; lia.
    vm_compute; destr.
    change 8 with (Z.of_nat 8).
    rewrite <- Nat2Z.inj_mul.

    replace (8 * ((Mem.box_span Int.max_unsigned - 2) * NPeano.pow 2 (MA - 3)))%nat
      with (((8 * NPeano.pow 2 (MA - 3)) * (Mem.box_span Int.max_unsigned - 2)))%nat by lia.
    replace (8 * NPeano.pow 2 (MA - 3))%nat with (Z.to_nat (two_power_nat MA)).
    rewrite Nat2Z.inj_mul.
    rewrite Z2Nat.id. f_equal. rewrite Nat2Z.inj_sub. lia.
    unfold Mem.box_span.
    apply Nat2Z.inj_le.  rewrite Z2Nat.id.
    etransitivity. 2: apply Z.add_le_mono_r.
    2: apply Zdiv_le_compat_l.
    3: split. 3: apply Z.gt_lt, two_power_nat_pos. 3: rewrite two_power_nat_two_p; apply two_p_monotone_strict.
    3: split. 3: lia. 3: instantiate (1:= 13). 3: generalize MA_bound; lia.
    vm_compute. destr.
    vm_compute; destr.
    apply Z.add_nonneg_nonneg. apply Z.div_pos. vm_compute; destr.
    apply Z.gt_lt, two_power_nat_pos. lia.
    generalize Mem.tpMA_pos; lia.

    rewrite <- (Nat2Z.id (mult _ _)).
    f_equal.
    rewrite Nat2Z.inj_mul. simpl. rewrite InstanceZ.npow_inj.
    rewrite <- two_p_correct.
    change 8 with (two_p 3). rewrite <- two_p_is_exp.
    rewrite two_power_nat_two_p. f_equal. generalize MA_bound; lia. lia. lia.
    rewrite box_span_mu. auto.
  - erewrite <- compat_add_unsigned. 3: apply COMP. 3: apply MIB.
    exploit addr_space. apply COMP. apply MIB. simpl. lia.
    intros; rewrite bounds_eq; reflexivity.
  - split. lia. transitivity (8 * Z.of_nat nb_boxes8_max). lia.
    unfold nb_boxes8_max.
    replace (Z.to_nat Mem.nb_boxes_max) with (Mem.box_span Int.max_unsigned - 2)%nat.
    
    replace (8 * Z.of_nat ((Mem.box_span Int.max_unsigned - 2) * NPeano.pow 2 (MA - 3)))
      with (two_power_nat MA * (Z.of_nat (Mem.box_span Int.max_unsigned) - 2)).
    rewrite Zmult_minus_distr_l.
    rewrite Mem.box_span_align.
    cut (align Int.max_unsigned (two_power_nat MA) + 0 <= (Int.max_unsigned + two_power_nat MA) + two_power_nat MA). lia.
    apply Z.add_le_mono.
    rewrite Mem.align_ge2.
    apply Z.add_le_mono_l.
    cut (   - 1  <= (Int.max_unsigned - 1) mod two_power_nat MA ). lia.
    etransitivity. 
    2: apply Z_mod_lt. lia.
    apply two_power_nat_pos.
    apply two_power_nat_pos. transitivity (two_power_nat 3). change (two_power_nat 3) with 8. lia.
    rewrite ! two_power_nat_two_p. apply two_p_monotone. generalize MA_bound; lia.
    vm_compute; destr.
    change 8 with (Z.of_nat 8).
    rewrite <- Nat2Z.inj_mul.

    replace (8 * ((Mem.box_span Int.max_unsigned - 2) * NPeano.pow 2 (MA - 3)))%nat
      with (((8 * NPeano.pow 2 (MA - 3)) * (Mem.box_span Int.max_unsigned - 2)))%nat by lia.
    replace (8 * NPeano.pow 2 (MA - 3))%nat with (Z.to_nat (two_power_nat MA)).
    rewrite Nat2Z.inj_mul.
    rewrite Z2Nat.id. f_equal. rewrite Nat2Z.inj_sub. lia.
    unfold Mem.box_span.
    apply Nat2Z.inj_le.  rewrite Z2Nat.id.
    etransitivity. 2: apply Z.add_le_mono_r.
    2: apply Zdiv_le_compat_l.
    3: split. 3: apply Z.gt_lt, two_power_nat_pos. 3: rewrite two_power_nat_two_p; apply two_p_monotone_strict.
    3: split. 3: lia. 3: instantiate (1:= 13). 3: generalize MA_bound; lia.
    vm_compute. destr.
    vm_compute; destr.
    apply Z.add_nonneg_nonneg. apply Z.div_pos. vm_compute; destr.
    apply Z.gt_lt, two_power_nat_pos. lia.
    generalize Mem.tpMA_pos; lia.
    rewrite <- (Nat2Z.id (mult _ _)).
    f_equal.
    rewrite Nat2Z.inj_mul. simpl. rewrite InstanceZ.npow_inj.
    rewrite <- two_p_correct.
    change 8 with (two_p 3). rewrite <- two_p_is_exp.
    rewrite two_power_nat_two_p. f_equal. generalize MA_bound; lia. lia. lia.
    rewrite box_span_mu. auto.
Qed.


Lemma nin_list_ints' : forall n m : nat,
    (m > n)%nat -> ~ In m (list_ints n).
Proof.
  induction n; simpl; intros; eauto.
  des m. lia. intro A. des A.  lia.
  apply IHn in i. auto. lia.
Qed.

Lemma lnr_list_ints:
  forall n,
    list_norepet (list_ints n).
Proof.
  induction n; simpl; intros. constructor.
  constructor; auto.
  apply nin_list_ints'. lia.
Qed.


Lemma lnr_gfb:
  forall m cm,
    list_norepet (get_free_boxes m cm).
Proof.
  unfold get_free_boxes.
  intros.
  match goal with
    |- context [ fold_left ?g ?a ?b ] => set (f := g)
  end.
  cut (list_norepet (list_ints nb_boxes8_max)).
  generalize (list_ints nb_boxes8_max) as ints.
  generalize (lnr_mbl m).
  generalize (map fst (Mem.mk_block_list m)).
  induction l; simpl; intros; auto.
  - trim IHl. inv H; auto.
    apply IHl. unfold f.
    apply filter_norepet. auto.
  - apply lnr_list_ints.
Qed.


Lemma in_gfb_addrspace:
  forall x m cm ,
    In x (get_free_boxes m cm) ->
    forall o, 0 <= Int.unsigned o < 8 -> 0 < (8 * Z.of_nat x) + Int.unsigned o < Int.max_unsigned.
Proof.
  intros x m cm IN.
  apply in_gfb in IN. des IN.
  rewrite list_ints_In in i.
  intros.
  split. apply Z.add_pos_nonneg. lia. lia.
  eapply Z.le_lt_trans with (8 * Z.of_nat nb_boxes8_max + Int.unsigned o). lia.
  unfold nb_boxes8_max.
  replace (Z.to_nat Mem.nb_boxes_max) with (Mem.box_span Int.max_unsigned - 2)%nat.
  replace (8 * Z.of_nat ((Mem.box_span Int.max_unsigned - 2) * NPeano.pow 2 (MA - 3)))
    with (two_power_nat MA * (Z.of_nat (Mem.box_span Int.max_unsigned) - 2)).
  rewrite Zmult_minus_distr_l.
  rewrite Mem.box_span_align.
  cut (align Int.max_unsigned (two_power_nat MA) + Int.unsigned o < (Int.max_unsigned + two_power_nat MA) + two_power_nat MA). lia.
  apply Z.add_lt_mono.
  rewrite Mem.align_ge2.
  apply Z.add_lt_mono_l.
  cut (   - 1  < (Int.max_unsigned - 1) mod two_power_nat MA ). lia.
  eapply Z.lt_le_trans with 0. lia.
  apply Z_mod_lt. 
  apply two_power_nat_pos.
  apply two_power_nat_pos. eapply Z.lt_le_trans with (two_power_nat 3). change (two_power_nat 3) with 8. lia.
  rewrite ! two_power_nat_two_p. apply two_p_monotone. generalize MA_bound. lia.
  vm_compute; destr.
  change 8 with (Z.of_nat 8).
  rewrite <- Nat2Z.inj_mul.

    replace (8 * ((Mem.box_span Int.max_unsigned - 2) * NPeano.pow 2 (MA - 3)))%nat
      with (((8 * NPeano.pow 2 (MA - 3)) * (Mem.box_span Int.max_unsigned - 2)))%nat by lia.
    replace (8 * NPeano.pow 2 (MA - 3))%nat with (Z.to_nat (two_power_nat MA)).
    rewrite Nat2Z.inj_mul.
    rewrite Z2Nat.id. f_equal. rewrite Nat2Z.inj_sub. lia.
    unfold Mem.box_span.
    apply Nat2Z.inj_le.  rewrite Z2Nat.id.
    etransitivity. 2: apply Z.add_le_mono_r.
    2: apply Zdiv_le_compat_l.
    3: split. 3: apply Z.gt_lt, two_power_nat_pos. 3: rewrite two_power_nat_two_p; apply two_p_monotone_strict.
    3: split. 3: lia. 3: instantiate (1:= 13). 3: generalize MA_bound; lia.
    vm_compute. destr.
    vm_compute; destr.
    apply Z.add_nonneg_nonneg. apply Z.div_pos. vm_compute; destr.
    apply Z.gt_lt, two_power_nat_pos. lia.
    generalize Mem.tpMA_pos; lia.

    rewrite <- (Nat2Z.id (mult _ _)).
    f_equal.
    rewrite Nat2Z.inj_mul. simpl. rewrite InstanceZ.npow_inj.
    rewrite <- two_p_correct.
    change 8 with (two_p 3). rewrite <- two_p_is_exp.
    rewrite two_power_nat_two_p. f_equal. generalize MA_bound; lia. lia. lia.
    apply box_span_mu.
Qed.

Lemma list_ints_length:
  forall n,
    length (list_ints n) = n.
Proof.
  induction n; simpl; intros; auto.
Qed.

Lemma filter_filter:
  forall {A} f f' (l: list A),
    filter f (filter f' l) = filter (fun x => f x && f' x) l.
Proof.
  induction l; simpl; intros; eauto.
  destr. destr. rewrite andb_false_r. auto. 
Qed.

Lemma filter_ext:
  forall {A} f f' (EXT: forall x, f x = f' x) (l: list A),
    (filter f l) = (filter f' l).
Proof.
  induction l; simpl; intros; eauto. rewrite EXT; destr.
Qed.

Lemma filter_true:
  forall {A} (l: list A),
    filter (fun x => true) l = l.
Proof.
  induction l; destr.
Qed.

Lemma get_free_boxes_filter:
  forall m cm,
  Permutation
    (get_free_boxes m cm)
    (filter
       (fun box => negb
                  (existsb
                     (fun b => in_dec eq_nat_dec box (box_range' m cm b))
                     (map fst (Mem.mk_block_list m))))
       (list_ints nb_boxes8_max)).
Proof.
  unfold get_free_boxes.
  intros.
  generalize (list_ints nb_boxes8_max).
  generalize (map fst (Mem.mk_block_list m)).
  induction l; simpl; intros.
  - rewrite filter_true; reflexivity.
  - rewrite IHl.
    rewrite filter_filter.
    erewrite filter_ext. reflexivity.
    simpl; intros.
    rewrite negb_orb. ring.
Qed.


Lemma remove_dbl_In:
  forall {A} D (l: list A) a,
    (In a l <-> In a (remove_dbl D l)).
Proof.
  induction l; simpl; split; intros; auto.
  rewrite IHl in H. destr. des H. eauto.
  apply IHl; auto. destr_in H; eauto; destr;
  rewrite IHl; eauto.
Qed.

Lemma remove_dbl_lnr:
  forall {A} D (l: list A),
    list_norepet (remove_dbl D l).
Proof.
  induction l; simpl; destr. constructor.
  constructor; auto.
  intro IN. apply n.
  eapply remove_dbl_In; eauto.
Qed.


Lemma get_used_boxes_filter:
  forall m cm (COMP: Mem.compat_m m Mem.M32 cm),
    Permutation (remove_dbl eq_nat_dec (concat (map (box_range cm) (Mem.mk_block_list m))))
                (filter (fun x : nat => existsb (fun b : block => in_dec eq_nat_dec x (box_range' m cm b)) (map fst (Mem.mk_block_list m)))
                        (list_ints nb_boxes8_max ++ O :: nat_range (S nb_boxes8_max) (Z.to_nat (Int.max_unsigned / 8)))).
Proof.
  intros m cm COMP.
  eapply Permutation_intro. apply eq_nat_dec.
  apply remove_dbl_lnr.
  apply filter_norepet.
  {
    apply list_norepet_append; auto.
    apply lnr_list_ints. constructor.
    intro IN; apply nat_range_range in IN. destruct IN. clear - H. lia.
    apply lnr_nat_range.
    red; intros. rewrite list_ints_In in H.
    simpl in H0. des H0. lia. apply nat_range_range in i. des i. clear l0. lia.
  }
  intros.
  rewrite <- remove_dbl_In.
  rewrite filter_In.
  rewrite in_concat.
  rewrite existsb_exists.
  split; intros.
  - dex; destr_and.
    rewrite in_map_iff in H. dex; destr_and. subst.
    split.
    + des x0. destr_in H0.
      rewrite in_app, list_ints_In.
      apply nat_range_range in H0.
      cut (x <= Z.to_nat (Int.max_unsigned / 8))%nat. intros. simpl.
      destruct (lt_dec O x). destruct (le_dec x nb_boxes8_max); auto.
      right. right. apply range_nat_range_range. lia. right; left; lia. 
      
      exploit mbla_in. apply H1. intro; subst.
      assert (Mem.size_block m b <= Int.max_unsigned) by eauto using size_block_mu.

      etransitivity. apply H0.
      apply Nat2Z.inj_le. rewrite Z2Nat.id.
      exploit compat_add_unsigned. 2: apply COMP.
      intros; rewrite bounds_eq; simpl; auto.
      rewrite bounds_eq. red; simpl. instantiate (2:= Int.repr (Mem.size_block m b - 1)).
      split. apply Int.unsigned_range.
      rewrite Int.unsigned_repr.
      instantiate (1:=b). lia. split. lia.
      lia.
      rewrite Int.unsigned_repr by lia. intro A.
      replace (Int.unsigned (cm b) + Mem.size_block m b - 1) with
      (Int.unsigned (cm b) + (Mem.size_block m b - 1)) by lia.
      rewrite <- A.
      etransitivity.
      apply Z.div_le_mono. lia. apply Int.unsigned_range_2.
      rewrite Z2Nat.id. lia. vm_compute; destr.
      apply Z.div_pos. generalize (Int.unsigned_range (cm b)). lia.
      lia.

    + exists (fst x0); split.
      rewrite in_map_iff. exists x0. split; auto.
      destruct (in_dec eq_nat_dec x (box_range' m cm (fst x0))); auto.
      unfold box_range' in n. Opaque box_range. simpl in n.
      destruct x0.  simpl in *.
      replace (Mem.size_block m b) with z in *. congruence.
      eapply mbla_in. eauto.
  - des H. dex; destr_and.
    rewrite in_map_iff in H. dex; destr_and. subst.
    eexists; split.
    rewrite in_map_iff. eexists; split. eauto. eauto.
    des (in_dec eq_nat_dec x (box_range' m cm (fst x1))).
    unfold box_range' in i0.
    destruct x1. simpl in *.
    replace z with (Mem.size_block m b). congruence.
    symmetry. eapply mbla_in. eauto.
Qed.


Lemma length_filters:
  forall {A} f (l: list A),
    length l = length (filter f l ++ filter (fun x => negb (f x)) l).
Proof.
  intros.
  des (partition f l).
  exploit (partition_app_perm (A:=A)). eauto.
  exploit (partition_filter (A:= A)). eauto. intro; subst.
  exploit (partition_filter_r (A:=A)). eauto. intro; subst.
  intros.
  apply Permutation_length. auto.
Qed.

Lemma length_get_free_boxes:
  forall m cm,
    Mem.compat_m m Mem.M32 cm ->
    (Z.to_nat Mem.nb_boxes_max * NPeano.pow 2 (MA - 3) <= length (get_free_boxes m cm) + nb_boxes_used_cm m cm)%nat.
Proof.
  unfold nb_boxes_used_cm.
  intros m cm COMP. 
  transitivity (length (list_ints nb_boxes8_max)).
  unfold nb_boxes8_max. rewrite list_ints_length. lia.

  rewrite (Permutation_length (get_free_boxes_filter m cm)).
  rewrite (Permutation_length (get_used_boxes_filter m cm COMP)).
  rewrite filter_app.
  rewrite app_length.
  rewrite plus_assoc.
  apply le_plus_trans.
  rewrite plus_comm.
  rewrite <- app_length.
  rewrite <- length_filters. lia.
Qed.

Lemma has_free_boxes_correct:
  forall m cm n,
    Mem.compat_m m Mem.M32 cm ->
    has_free_boxes m cm n ->
    exists l,
      (length l >= n)%nat /\
      list_norepet l /\
      Forall (fun z : Z => forall b o o',
                  Mem.in_bound_m (Int.unsigned o) m b ->
                  0 <= Int.unsigned o' < 8 ->
                  Int.unsigned (Int.add (cm b) o) <> Int.unsigned (Int.add (Int.repr z) o')) l /\
      Forall (fun z => forall o, 0 <= Int.unsigned o < 8 -> 0 < z + Int.unsigned o < Int.max_unsigned) l /\
      Forall (fun z => exists k, z = 8 * k) l.
Proof.
  intros m cm n COMP HFB.
  set (l := get_free_boxes m cm).
  exists (map (fun n => 8 * Z.of_nat n) l).
  repSplit.
  - rewrite map_length. red in HFB.
    cut (Z.to_nat Mem.nb_boxes_max * NPeano.pow 2 (MA - 3)  <= length l + nb_boxes_used_cm m cm)%nat. lia.
    unfold l. apply length_get_free_boxes. auto.
  - apply list_map_norepet. apply lnr_gfb.
    intros. lia.
  - rewrite Forall_forall. intros x.
    rewrite in_map_iff. intros (x0 & EQ & IN). subst.
    intros b o o' IB IB'.
    exploit in_gfb'; eauto. intros (RNG & NOOV).
    apply NOOV; auto.
  - rewrite Forall_forall. intros x.
    rewrite in_map_iff. intros (x0 & EQ & IN). subst.
    unfold l in *. intros.
    exploit in_gfb_addrspace; eauto.
  - rewrite Forall_forall. intros x.
    rewrite in_map_iff. intros (x0 & EQ & IN). eauto.
Qed.


Lemma list_nth_z_succeeds:
  forall {A} (l: list A) n,
    0 <= n < Z.of_nat (length l) ->
    exists x, list_nth_z l n = Some x.
Proof.
  induction l; simpl; intros; eauto.
  lia.
  destr. eauto.
  edestruct IHl; eauto. split. unfold Z.pred. lia.
  unfold Z.pred. lia.
Qed.

Fixpoint find {A} (eq_dec: forall (a b: A), {a = b} + {a <> b}) x l :=
  match l with
    nil => None
  | a :: r => if eq_dec a x then Some O else option_map S (find eq_dec x r)
  end.


Lemma iwb_in_bound:
  forall f m1 m2 (IWF: inj_well_behaved f m1 m2)
    b b0 z (FB: f b = Some (b0,z))
    o (IB: in_bound o (Mem.bounds_of_block m1 b)),
    in_bound o (Mem.bounds_of_block m2 b0).
Proof.
  intros.
  rewrite bounds_eq in *.
  erewrite <- iwb_bounds; eauto.
Qed.

Lemma in_map_filter:
  forall {A B} b0 (f: A -> option B) l,
    In b0 (filter_map f l) <->
    (exists a0, In a0 l /\ f a0 = Some b0).
Proof.
  induction l; simpl; intros. split; intros; dex; easy.
  des (f a); eauto.
  - split; intros.
    + destruct H; subst; eauto.
      rewrite IHl in H. dex.
      exists a0; destr.
    + dex. destruct H as [[C|C] D].
      subst; auto. left; congruence. right; rewrite IHl.
      exists a0; destr.
  - rewrite IHl.
    split; intros [a0 [C D]]; exists a0; destr.
Qed.

Lemma find_in:
  forall {A} eq_dec l (x:A),
    In x l ->
    exists n, find eq_dec x l = Some n /\
         (n < length l)%nat.
Proof.
  induction l; simpl; intros; eauto. easy.
  destr. eexists; split; eauto. lia.
  edestruct IHl; eauto. des H. eauto.
  destruct H0. rewrite H0. simpl. eexists; split; eauto. lia.
Qed.

Lemma lnr_list_nth_z_diff:
  forall {A} (l: list A) (LNR: list_norepet l)
    n1 n2 (d: n1 <> n2)
    x1 x2
    (NTH1: list_nth_z l n1 = Some x1)
    (NTH2: list_nth_z l n2 = Some x2),
    x1 <> x2.
Proof.
  induction 1; simpl; intros; eauto. easy.
  - intro; subst. destr_in NTH1; destr_in NTH2.
    inv NTH1. eapply list_nth_z_in in NTH2. destr.
    inv NTH2. eapply list_nth_z_in in NTH1. destr.
    specialize (IHLNR (Z.pred n1) (Z.pred n2)). trim IHLNR. unfold Z.pred. lia.
    exploit IHLNR; eauto.
Qed.

Lemma not_inj_in_bound_in_filter_map:
  forall f m1 l l0 b' o'
    (PART: partition (is_injected f) (Mem.mk_block_list m1) = (l,l0))
    (FB: f b' = None)
    (IB: in_bound (Int.unsigned o') (Mem.bounds_of_block m1 b')),
    In b' (filter_map (fun bsz : block * Z => let (b,sz) := bsz in
                                           if zlt 0 sz
                                           then Some b
                                           else None) l0).
Proof.
  intros.
  rewrite in_map_filter.  exists (b', Mem.size_block m1 b'). simpl; split; auto.
  rewrite in_partition_r; eauto. split.
  eapply mbla_below_in'.
  eapply Mem.in_bound_valid in IB. red in IB. apply Pos2Nat.inj_lt in IB. lia.
  unfold is_injected; simpl; rewrite FB. auto.
  rewrite bounds_eq in IB. red in IB. destr. lia.
Qed.

Lemma find_diff_diff:
  forall {A} E (a1 a2:A) (d: a1 <> a2) l n1 n2,
    find E a1 l = Some n1 ->
    find E a2 l = Some n2 ->
    n1 <> n2.
Proof.
  induction l; simpl; intros; eauto. congruence.
  destr_in H. inv H.
  destr_in H0. des (find E a2 l).
  des (find E a1 l). inv H. destr_in H0.
  des (find E a2 l). inv H0. specialize (IHl _ _ eq_refl eq_refl). congruence.
Qed.

Lemma length_filter_map_fold_right:
  forall f m1 m2 l l0  
    (IWB: inj_well_behaved f m1 m2)
    (PART: partition (is_injected f) (Mem.mk_block_list m1) = (l,l0)),
    length (filter_map (fun bsz : block * Z => let (b0, sz) := bsz in if zlt 0 sz then Some b0 else None) l0)
    = fold_right Peano.plus 0%nat (map (fun x : block => length (box_range' m1 (canon_cm m1) x)) (map fst l0)).
Proof.
  intros. generalize (fun b => (proj1 (in_partition_r _ _ _ _ PART b))).
  clear - IWB. 
  induction l0; simpl; intros; eauto.
  des a.
  destr.
  rewrite IHl0. simpl.
  replace (length (box_range' m1 (canon_cm m1) b)) with 1%nat. lia.
  unfold box_range'.
  unfold is_injected in H.
  specialize (H _ (or_introl eq_refl)). Opaque box_range.
  destr_in H.
  destruct H.
  unfold Mem.mk_block_list in H. eapply mbla_in in H. subst.
  rewrite length_box_range_canon_cm.
  rewrite Z.div_small.  reflexivity. 
  exploit iwb_wb; eauto. lia. lia.
  intros; apply H; eauto.
  rewrite IHl0. 2: intros; apply H; auto.
  replace (length (box_range' m1 (canon_cm m1) b)) with O. lia.
  unfold box_range'. Transparent box_range. simpl. destr. exfalso.
  unfold is_injected in H.
  specialize (H _ (or_introl eq_refl)). Opaque box_range.
  destr_in H.
  destruct H.
  unfold Mem.mk_block_list in H. eapply mbla_in in H. subst.
  lia.
Qed.

Lemma not_inj_in_bound_get_addr:
  forall f m1 m2 l l0 b' o'
    (IWB: inj_well_behaved f m1 m2)
    (PART: partition (is_injected f) (Mem.mk_block_list m1) = (l,l0))
    (FB: f b' = None)
    (IB: in_bound (Int.unsigned o') (Mem.bounds_of_block m1 b')),
    let l' := (filter_map (fun bsz : block * Z => let (b,sz) := bsz in
                                               if zlt 0 sz
                                               then Some b
                                               else None) l0) in
    forall l1 (LEN: (length l1 >= fold_right Peano.plus 0%nat (map (fun x : block => length (box_range' m1 (canon_cm m1) x)) (map fst l0)))%nat),
    exists n (x: Z),
      find peq b' l' = Some n /\
      (n < length l')%nat /\
      list_nth_z l1 (Z.of_nat n) = Some x
.
Proof.
  intros.
  exploit not_inj_in_bound_in_filter_map; eauto. intro H.
  destruct (find_in peq _ _ H) as (n & EQ & LT). unfold l'. rewrite EQ.
  destruct (list_nth_z_succeeds l1 (Z.of_nat n)) as (A & EQA).
  split. lia. apply inj_lt.
  eapply lt_le_trans. apply LT.
  erewrite length_filter_map_fold_right;eauto.
  eexists; eexists; eauto.
Qed.

Lemma find_some_range:
  forall {A} E (x:A) l n,
    find E x l = Some n ->
    0 <= Z.of_nat n < Z.of_nat (length l).
Proof.
  induction l; simpl; intros; eauto. congruence.
  destr_in H. inv H. lia.
  des (find E x l). specialize (IHl _ eq_refl). inv H. lia.
Qed.

Lemma nb_boxes_max_pos:
  0 <= Mem.nb_boxes_max.
Proof.
  unfold Mem.nb_boxes_max.
  transitivity (two_power_nat 20 - 2). vm_compute; destr.
  generalize (two_p_monotone 20 (Z.of_nat (32 - MA))).
  rewrite ! two_power_nat_two_p. generalize MA_bound. lia.
Qed.


Theorem forget_compat:
  forall sm ei f m1 m2
    (MINJ: Mem.inject sm ei f m1 m2)
    (IWB: inj_well_behaved f m1 m2)
    cm2
    (COMP: Mem.compat_m m2 Mem.M32 cm2),
  exists cm1,
    Mem.compat_m m1 Mem.M32 cm1 /\
    (forall b b' : block, f b = Some (b',0) -> cm1 b = cm2 b').
Proof.
  intros.
  des (partition (is_injected f) (Mem.mk_block_list m1)).
  assert (has_free_boxes
            m2 cm2
            (fold_right Peano.plus O
                        (map (fun x : block => length (box_range' m1 (canon_cm m1) x)) (map fst l0)))).
  red.
  eapply le_lt_trans.
  eapply NPeano.Nat.add_le_mono.
  eapply canon_cm_more_boxes. eauto. apply eq_le; eauto.
  rewrite plus_0_r. erewrite inject_well_behaved_diff_blocks_num; eauto.
  eapply le_lt_trans.
  eapply nb_boxes_used_cm_nb_boxes_used_m.
  apply mult_lt_le_mono.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id.
  apply Mem.wfm_alloc.
  apply nb_boxes_max_pos.
  
  Lemma two_power : forall n, (1 <= NPeano.pow 2 n)%nat.
  Proof.
    intro.
    change (1%nat) with (NPeano.pow 2 0)%nat at 1.
    intros.
    apply NPeano.Nat.pow_le_mono_r ; lia.
  Qed.

  split. apply two_power. lia.

  apply has_free_boxes_correct in H.
  destruct H as (l1 & LEN & LNR & PROP & ADDRSPACE & ALIGN).
  exists (fun b =>
       match f b with
         Some (b', delta) => cm2 b'
       | None =>
         match map_option (fun n => list_nth_z l1 (Z.of_nat n)) (find peq b (filter_map (fun bsz : block * Z => let (b,sz) := bsz in
                                      if zlt 0 sz
                                      then Some b
                                      else None) l0)) with
           Some A => Int.repr A
         | None => Int.zero
         end
       end
    ).
  split.
  Focus 2.
  intros. rewrite H. auto.
  constructor.
  - intros b o IB.
    destr. des p.
    inv COMP. apply addr_space.
    eapply iwb_in_bound; eauto.
    exploit not_inj_in_bound_get_addr. eauto. eauto. eauto. eauto. apply LEN.
    intros (n & A & EQ & LT & EQA).
    rewrite EQ. simpl. rewrite EQA.
    rewrite Forall_forall in ADDRSPACE.
    trim (ADDRSPACE A).
    eapply list_nth_z_in; eauto.
    generalize (ADDRSPACE o). intro AO. trim AO.
    rewrite bounds_eq in IB.
    red in IB. simpl in IB.
    exploit iwb_wb; eauto. lia.

    generalize (ADDRSPACE Int.zero). intro A0. trim A0.
    rewrite Int.unsigned_zero. lia.
    rewrite Int.unsigned_zero in A0.

    rewrite Int.add_unsigned.
    rewrite (Int.unsigned_repr A).
    rewrite Int.unsigned_repr.
    lia. lia. 
    lia.

  - intros b b' o o' DIFF IB IB'.
    destr. des p.
    + destr. des p.
      * inv COMP. apply overlap; auto.
        intro; subst.
        exploit iwb_inj. eauto. apply Heqo1. apply Heqo0. destr.
        eapply iwb_in_bound; eauto.
        eapply iwb_in_bound; eauto.
      * exploit not_inj_in_bound_get_addr. eauto. eauto. eauto. eauto. apply LEN.
        intros (n & A & EQ & LT & EQA).
        rewrite EQ. simpl. rewrite EQA.
        rewrite Forall_forall in PROP. apply PROP. 
        eapply list_nth_z_in; eauto.
        eapply iwb_in_bound; eauto.
        rewrite bounds_eq in IB'.
        red in IB'. simpl in IB'.
        exploit iwb_wb; eauto. lia.
    + destr.
      * exploit not_inj_in_bound_get_addr. eauto. eauto. eauto. eauto. apply LEN.
        intros (n & A & EQ & LT & EQA).
        revert Heqo1. rewrite EQ. simpl. rewrite EQA. intro B; inv B.
        rewrite Forall_forall in PROP.
        generalize (PROP z). intro PZ.
        trim PZ. eapply list_nth_z_in; eauto.
        specialize (fun LT b2 d pf => PZ _ _ o (iwb_in_bound _ _ _ IWB b' b2 d pf _ IB') LT).
        trim PZ.
        rewrite bounds_eq in IB.
        red in IB. simpl in IB.
        exploit iwb_wb; eauto. lia.
        destr.
        {
          des p. specialize (PZ _ _ eq_refl). auto.
        }
        {
          exploit not_inj_in_bound_get_addr. eauto. eauto. apply Heqo1. eauto. apply LEN.
          intros (n2 & A2 & EQ2 & LT2 & EQA2).
          rewrite EQ2. simpl. rewrite EQA2. intro B; inv B. 
          assert (n <> n2) by eauto using find_diff_diff.
          rewrite bounds_eq in IB, IB'.
          red in IB, IB'. simpl in IB, IB'.
          exploit iwb_wb. eauto.  apply Heqo0.
          exploit iwb_wb. eauto.  apply Heqo1.
          assert (z <> A2) by (eapply lnr_list_nth_z_diff; eauto; lia).
          intros. 
          rewrite Forall_forall in ADDRSPACE.
          specialize (fun o pf x pf' => ADDRSPACE x pf' o pf).
          generalize (ADDRSPACE o). intro ASo.
          trim ASo. lia.
          trim (ASo z).
          eapply list_nth_z_in; eauto.
          generalize (ADDRSPACE o'). intro ASo'.
          trim ASo'. lia.
          trim (ASo' A2).
          eapply list_nth_z_in; eauto.
          generalize (ADDRSPACE Int.zero). intro AS0.
          trim AS0. rewrite Int.unsigned_zero. lia.
          generalize (AS0 _ (list_nth_z_in _ _ EQA)).
          generalize (AS0 _ (list_nth_z_in _ _ EQA2)). rewrite Int.unsigned_zero. intros A2rng Zrng.
          intros; revert H0.
          unfold Int.add.
          rewrite (Int.unsigned_repr z) by lia.
          rewrite (Int.unsigned_repr A2) by lia.
          rewrite ! Int.unsigned_repr by lia.
          rewrite Forall_forall in ALIGN.
          destruct (ALIGN _ (list_nth_z_in _ _ EQA)) as (k & EQk).
          destruct (ALIGN _ (list_nth_z_in _ _ EQA2)) as (k2 & EQk2).
          subst. 
          clear - H1 H2 H3 IB IB'. lia.
        }
      * des (find peq b (filter_map (fun bsz : block * Z => let (b0, sz) := bsz in if zlt 0 sz then Some b0 else None) l0)).

        eapply find_some_range in Heqo2.
        erewrite length_filter_map_fold_right in Heqo2; eauto.
        exploit (list_nth_z_succeeds (A:=Z)). split.
        2: eapply Z.lt_le_trans. 2: apply Heqo2. lia.
        apply inj_le. instantiate (1 := l1). lia.
        intros (x & EQ). destr.

        assert (~ In b (filter_map (fun bsz : block * Z =>
                                      let (b0, sz) := bsz in
                                      if zlt 0 sz
                                      then Some b0
                                      else None) l0)).
        intro IN.
        eapply find_in with (eq_dec:=peq) (x:=b) in IN. dex; destr. 
        rewrite in_map_filter in H.
        exfalso; apply H.
        exists (b, Mem.size_block m1 b).
        rewrite in_partition_r. 2: eauto. unfold is_injected. simpl. rewrite Heqo0.
        repSplit; auto.
        eapply mbla_below_in'.
        eapply Mem.in_bound_valid in IB. red in IB. apply Pos2Nat.inj_lt in IB. lia.
        destr.
        contradict IB. rewrite bounds_eq. unfold in_bound. simpl. lia.
  - intros.
    destr. des p.
    unfold Mem.nat_mask. erewrite iwb_mask; eauto.
    inv COMP; eauto.
    destr.
    des (find peq b (filter_map (fun bsz : block * Z => let (b0, sz) := bsz in if zlt 0 sz then Some b0 else None) l0)).
    rewrite Forall_forall in ALIGN.
    destruct (ALIGN _ (list_nth_z_in _ _ Heqo0)) as (k & EQk).
    subst.
    exploit iwb_wb; eauto. intros (B & M).
    IntFacts.solve_int.
    rewrite Int.testbit_repr; auto.
    replace (8*k) with (k * 2 ^ 3) by lia.
    rewrite Z.mul_pow2_bits by lia.
    des (Z.testbit k (i-3)).
    assert (i-3 >= 0). destruct (zle 0 (i-3)). lia. rewrite Z.testbit_neg_r in Heqb0. congruence. lia.
    unfold Mem.nat_mask.
    rewrite Int.bits_not; auto. rewrite Int.testbit_repr; auto.
    rewrite two_power_nat_two_p, Int.Ztestbit_two_p_m1; auto. destr. lia. lia.
  - auto.
Qed.

Definition depends_m (m: mem) (e: expr_sym) (b: block) :=
  depends Int.max_unsigned (Mem.bounds_of_block m) (Mem.nat_mask m) e b.

Definition sep_inj (m: mem) (f: meminj) e :=
  forall b, f b = None -> ~ depends_m m e b.

Lemma forget_norm:
  forall sm ei (wf: wf_inj ei) (f : meminj) (m1 m2 : mem),
  Mem.inject sm ei f m1 m2 ->
  inj_well_behaved f m1 m2 ->
  forall e1 e2 (EI: ei f e1 e2) (BA: sep_inj m1 f e1),
    val_inject f (Mem.mem_norm m1 e1) (Mem.mem_norm m2 e2).
Proof.
  intros.
  destruct (Val.eq_val_dec (Mem.mem_norm m1 e1) Vundef) as [MN|NMN]; auto.
  rewrite MN; auto.
  assert (exists x, val_inject f (Mem.mem_norm m1 e1) x /\ x <> Vundef).
  {
    des (Mem.mem_norm m1 e1); eauto.
    des (f b). des p. eexists; econstructor. econstructor; eauto. destr.
    exploit BA; eauto. 2: easy.
    red; red; intros.
    generalize (Mem.norm_ld _ _ _ Heqv _ em COMP).    generalize (Mem.norm_ld _ _ _ Heqv _ em COMP').
    simpl.  intros A B; inv A; inv B.
    intro C. apply inj_vint in C.
    rewrite <- ! (Int.add_commut i) in C. apply int_add_eq_l in C. destr.
  }
  dex. des H1.
  replace x with (Mem.mem_norm m2 e2) in v. auto.
  apply Mem.eq_norm; auto.
  constructor.
  intros cm2 em COMPAT.
  exploit forget_compat; eauto.
  intros [cm1 [A B]].
  assert  (eSval cm2 x = eSval cm1 (Mem.mem_norm m1 e1)).
  des (Mem.mem_norm m1 e1); inv v; simpl; auto.
  exploit iwb_o2o; eauto. intros; subst.
  erewrite B; eauto. rewrite Int.add_zero; auto.
  simpl; rewrite H1.
  eapply Values.Val.lessdef_trans. eapply Mem.norm_ld. eauto. eauto.
  eapply ei_ld'_expr; eauto.
  red; intros. exploit iwb_o2o; eauto; intros; subst. subst.
  rewrite Int.add_zero; eauto.
  apply em_inj_inj_em.
Qed.

Lemma norm_forget:
  forall sm ei (wf: wf_inj ei) f m m' e1 v1 e1'
    (O2O: inj_well_behaved f m m')
    (INJ: Mem.inject sm ei f m m')
    (EI: ei f e1 e1')
    (NU: v1 <> Vundef),
  forall (MN:Mem.mem_norm m e1 = v1) (BA: sep_inj m f e1),
    Mem.mem_norm m' e1' <> Vundef /\    
    ei f (Eval v1) (Eval (Mem.mem_norm m' e1')).
Proof.  
  intros.
  assert (N:= Mem.norm_ld m e1 _ MN).
  assert (GR:= Mem.norm_gr m e1). rewrite MN in GR.
  destruct (Val.apply_inj f (Eval v1)) eqn:?; try congruence.
  - clear MN. destruct (inj_eval_eval _ _ _ Heqo). subst.
    cut (Mem.mem_norm m' e1' = x).
    intro MNV; subst.
    + split. 
      * unfold Val.apply_inj, Val.inj_ptr in Heqo. 
        intro H. rewrite H in Heqo.
        des v1. des (f b). des p.
      * apply vi_ei. auto.  auto.
    + apply Mem.eq_norm. constructor.
      * intros cm2 em COMPAT.
        exploit forget_compat; eauto. 
        intros [cm1 [A B]].
        assert  (eSval cm2 x = eSval cm1 v1).
        des v1; inv Heqo; simpl; auto.
        unfold Val.inj_ptr in H0; des (f b); des p.
        inv H0. simpl.
        exploit iwb_o2o; eauto. intros; subst.
        erewrite B; eauto. rewrite Int.add_zero; auto.
        simpl; rewrite H.
        (* setoid_rewrite <- (Val.apply_inj_eSexpr f alloc0 em _ _ Heqo); eauto. *)
        eapply Values.Val.lessdef_trans. apply N. auto.
        eapply ei_ld'_expr; eauto.
        red; intros. exploit iwb_o2o; eauto; intros; subst. subst.
        rewrite Int.add_zero; eauto.
        apply em_inj_inj_em.
      * des v1.  unfold Val.inj_ptr in Heqo; des (f b); des p.
  - exfalso.
    des v1; 
    unfold Val.inj_ptr in Heqo;
    des (f b); try des p.
    exploit BA; eauto.
Qed.

Lemma storev_inject:
  forall sm ei (wf: wf_inj ei) f chunk m1 a1 v1 n1 m2 a2 v2
    (IWB: inj_well_behaved f m1 m2)
    (INJ: Mem.inject sm ei f m1 m2)
    (STOREV: Mem.storev chunk m1 a1 v1 = Some n1)
    (EIaddr: ei f a1 a2)
    (SI: sep_inj m1 f a1)
    (EIval: ei f v1 v2),
  exists n2,
    Mem.storev chunk m2 a2 v2 = Some n2 /\ Mem.inject sm ei f n1 n2.
Proof.
  intros.
  unfold Mem.storev in *; revert STOREV; destr.
  generalize (forget_norm _ _ wf _ _ _ INJ IWB _ _ EIaddr SI).
  rewrite Heqv; intro A; inv A. intro.
  exploit Mem.store_mapped_inject; eauto.
  intros [n2 [A B]]; exists n2; split; auto.
  rewrite <- A.
  f_equal.
  eapply Mem.address_inject'; eauto.
  eapply Mem.store_valid_access_1; eauto.
  eapply Mem.valid_access_implies; eauto.
  eapply Mem.store_valid_access_3; eauto.
  constructor.
Qed.

Lemma loadv_inject:
  forall sm ei (wf: wf_inj ei) f chunk m1 a1 v1 m2 a2 
    (IWB: inj_well_behaved f m1 m2)
    (INJ: Mem.inject sm ei f m1 m2)
    (LOADV: Mem.loadv chunk m1 a1 = Some v1)
    (EIaddr: ei f a1 a2)
    (SI: sep_inj m1 f a1),
  exists v2,
    Mem.loadv chunk m2 a2 = Some v2 /\ ei f v1 v2.
Proof.
  intros.
  unfold Mem.loadv in *; destr_in LOADV.
  generalize (forget_norm _ _ wf _ _ _ INJ IWB _ _ EIaddr SI).
  rewrite Heqv; intro A; inv A.
  exploit Mem.load_inject; eauto.
  intros [v2 [A B]]; exists v2; split; auto.
  rewrite <- A.
  f_equal.
  eapply Mem.address_inject'; eauto.
  eapply Mem.valid_access_implies; eauto.
  eapply Mem.load_valid_access; eauto.
  constructor.
Qed.

Lemma expr_inj_not_dep:
  forall f v v'
    (EI: expr_inj f v v') b
    (Fb: f b = None), ~ block_appears v b.
Proof.
  induction 1; simpl; intros; eauto.
  - des v1. subst. inv VI. congruence.
  - intro A; intuition try congruence; eauto.
Qed.

Lemma not_block_appears_same_eval:
  forall e b (NA: ~ block_appears e b),
  forall cm cm'
    (diff_b: cm b <> cm' b)
    (same_other : forall b' : block, b <> b' -> cm b' = cm' b'),
  forall em,
    eSexpr cm em e = eSexpr cm' em e.
Proof.
  induction e; simpl; intros; auto.
  - des v.
    rewrite same_other; auto.
  - erewrite IHe; eauto.
  - erewrite IHe1, IHe2; eauto.    
Qed.

Lemma dep_block_appears:
  forall m e b
    (dep: depends_m m e b),
    block_appears e b.
Proof.
  intros. red in dep.
  destruct (block_appears_dec b e); auto.
  exfalso.
  destruct (Mem.exists_two_cms m b) as [cm [cm' [A [B [C D]]]]].
  specialize (dep _ A _ B C dummy_em).
  exfalso. apply dep.
  eapply not_block_appears_same_eval; eauto.
Qed.

Lemma norm_unforgeable:
  forall m e b o
    (MN: Mem.mem_norm m e = Vptr b o),
    depends_m m e b.
Proof.
  intros.
  eapply norm_unforgeable; eauto.
  unfold Mem.nat_mask; intros; eauto.
  instantiate (1:=o); rewrite <- MN; apply norm_correct.
Qed.

Lemma dep_block_appears':
  forall m
    (e : expr_sym) (b : block),
    ~ block_appears e b -> ~  depends_m m e b.
Proof.
  red; intros.
  eapply dep_block_appears in H0; eauto.
Qed.

Lemma list_ints_le:
  forall m n,
    (0 < n <= m)%nat ->
    In n (Alloc.list_ints m).
Proof.
  induction m; simpl;intros.
  omega.
  destruct (eq_nat_dec n (S m)).
  subst; auto.
  right; apply IHm; auto.  omega.
Qed.

Remark filter_charact:
  forall (A: Type) (f: A -> bool) x l,
  In x (List.filter f l) <-> In x l /\ f x = true.
Proof.
  induction l; simpl. tauto. 
  destruct (f a) eqn:?. 
  simpl. rewrite IHl. intuition congruence.
  intuition congruence.
Qed.

Lemma o2oinj_inverse:
  forall f m tm (IWB: inj_well_behaved f m tm)
    sm ei (MINJ: Mem.inject sm ei f m tm),
  exists g, forall b b', f b = Some (b',0) -> g b' = Some b.
Proof.
  intros.
  (* lists of possibly injected blocks *)
  set (bl := Alloc.list_ints (Pos.to_nat (Mem.nextblock m))).
  (* association list (block, (injection)) *)
  set (bl' := map (fun x => let b := Pos.of_nat x in (b, f b)) bl).
  (* filter: keep only pair that injects into a given block b *)
  set (filter_fun := fun (b:block) (x: block * option (block*Z)) =>
                                match snd x with
                                  Some (b',delta) => if peq b b' then true else false
                                | _ => false
                                end).
  (* the pre image of a block b' is in this list *)
  exists (fun b => head (map fst (filter (filter_fun b) bl'))).
  intros.
  (* the association we look for is in the original list *)
  assert (ISIN: In (b, Some (b', 0)) bl').
  {
    destruct (Mem.valid_block_dec m b).
    apply in_map_iff.
    exists (Pos.to_nat b).
    rewrite Pos2Nat.id. simpl. unfold block. split; auto.
    f_equal; auto.
    apply list_ints_le.
    split. zify; omega.
    apply Pos2Nat.inj_le.
    unfold Mem.valid_block in v. xomega.
    eapply Mem.mi_freeblocks in n; eauto. congruence.
  }
  (* no other block injects into b', since f is injective *)
  assert (UNIQUE: forall bb delta, In (bb, Some (b', delta)) bl' -> b = bb /\ delta = 0).
  {
    intros bb delta IN.
    generalize IN; intro IN'.
    unfold bl' in IN. rewrite in_map_iff in IN.
    dex; destr. des IN. inv e.
    exploit iwb_o2o; eauto. intros; subst.
    destruct (peq b (Pos.of_nat x)); auto.
    exploit iwb_inj. eauto. apply H. apply H2. auto.
  }
  (* every element of the filtered list is the association we are looking for *)
  assert (ALL: Forall (fun x => x = (b, Some (b',0))) (filter (filter_fun b') bl')). {
    rewrite Forall_forall.
    intros x IN.
    apply filter_charact in IN. destruct IN as [IN INEQ].
    revert INEQ. unfold filter_fun; simpl. 
    des x. des o. des p. destr. intros _.  subst. apply UNIQUE in IN. destr.
  }
  des (filter (filter_fun b') bl').
  (* the list can't be empty, we have at least our known association *)
  generalize (filter_charact _ (filter_fun b') (b , Some (b',0)) bl').
  rewrite Heql.  destr. intros [A B].
  exfalso; apply B; unfold filter_fun;  simpl. rewrite peq_true; auto.
  (* this is what we are looking for. *)
  inv ALL; reflexivity. 
Qed.

Lemma o2oinj_cm_inj:
  forall f sm ei m tm
    (IWB: inj_well_behaved f m tm)
    (MINJ: Mem.inject sm ei f m tm) cm,
  exists cm',
    cm_inj cm' f cm.
Proof.
  intros.
  exploit o2oinj_inverse; eauto.
  intros [g SPEC].
  exists (fun bb => match g bb with
              Some b => cm b
            | None => Int.zero
            end); simpl.
  red; intros.
  exploit iwb_o2o; eauto. intros; subst. rewrite Int.add_zero.
  erewrite SPEC; eauto.
Qed.

Lemma o2oinj_em_inj:
  forall f sm ei m tm
    (IWB: inj_well_behaved f m tm)
    (MINJ: Mem.inject sm ei f m tm)
    em,
  exists em',
    em_inj em' f em.
Proof.
  intros.
  exploit o2oinj_inverse; eauto.
  intros [g SPEC].
  exists (fun bb i => match g bb with
              Some b => em b i
            | None => Byte.zero
            end); simpl.
  red; intros.
  exploit iwb_o2o; eauto. intros; subst. rewrite Int.add_zero.
  erewrite SPEC; eauto.
Qed.

Lemma expr_inj_se_not_dep:
  forall sm ei f m tm v v'
    (IWB: inj_well_behaved f m tm)
    (MINJ: Mem.inject sm ei f m tm)
    (EI: expr_inj_se f v v'),
    sep_inj m f v.
Proof.
  intros sm ei f m tm v v' IWB MINJ (a & b & A & B & C).
  red. intros b0 Fb.
  generalize (expr_inj_not_dep _ _ _ C _ Fb). intros NBA DEP.
  eapply (dep_block_appears' m) in NBA; eauto.
  apply NBA.
  red; red; intros.
  specialize (DEP _ COMP _ COMP' SameB em).
  (* inv DEP. *)
  (* apply NBA; clear NBA. *)
  (* apply (mkDep _ _ _ _ _ dep_cm dep_cm'); auto. *)
  destruct (o2oinj_inverse _ _ _ IWB _ ei MINJ) as [g SPEC].
  intros.
  edestruct (o2oinj_em_inj) with (em:=em) as [em' EMINJ]; eauto.
  edestruct (o2oinj_cm_inj) with (cm:=cm) as [dep_cmi CMINJ]; eauto.
  edestruct (o2oinj_cm_inj) with (cm:=cm') as [dep_cmi' CMINJ']; eauto.
  erewrite <- ! A; eauto.
Qed.

Lemma list_expr_inj_se_not_dep:
  forall sm ei f m tm v v'
    (IWB: inj_well_behaved f m tm)
    (MINJ: Mem.inject sm ei f m tm)
    (EI: list_ei expr_inj_se f v v'),
    Forall (sep_inj m f) v.
Proof.
  induction 3;simpl; intros; auto.
  constructor; auto.
  eapply expr_inj_se_not_dep; eauto.
Qed.

Lemma sep_inj_load_result:
  forall f m v (SI: sep_inj m f v)
    chunk, sep_inj m f (Val.load_result chunk v).
Proof.
  unfold sep_inj; simpl; intros.
  intro DEP.
  eapply SI; eauto.
  red; red; intros.
  specialize (DEP _ COMP _ COMP' SameB em).
  intro EQ. apply DEP.
  des chunk.
  rewrite EQ; auto.
  repeat destr. 
Qed.

Lemma iwb_inv:
  forall f m tm (IWB: inj_well_behaved f m tm)
    m' tm'
    (BND: forall b, Mem.bounds_of_block m b = Mem.bounds_of_block m' b)
    (BNDt: forall b, Mem.bounds_of_block tm b = Mem.bounds_of_block tm' b)
    (MSK: forall b, Mem.mask m b = Mem.mask m' b)
    (MSKt: forall b, Mem.mask tm b = Mem.mask tm' b)
    (PLE: forall b', Ple (Mem.nextblock tm) b' -> Plt b' (Mem.nextblock tm') ->
                exists b delta, f b = Some (b', delta)),
    inj_well_behaved f m' tm'.
Proof.
  intros.
  inv IWB; constructor; auto.
  - red in iwb_wb0 |- *; intros.
    rewrite <- Mem.size_block_snd.
    rewrite <- BND, <- MSK.
    rewrite Mem.size_block_snd.
    eauto.
  - intros.
    rewrite <- ! Mem.size_block_snd.
    rewrite <- BND, <- BNDt.
    rewrite ! Mem.size_block_snd.
    eauto.
  - intros; rewrite <- MSK, <- MSKt. eauto.
  - intros. 
    unfold Mem.valid_block in iwb_no_oota0, H. 
    destruct (plt b' (Mem.nextblock tm)). auto.
    apply PLE; auto. xomega.
Qed.

Lemma free_inject:
  forall f sm
    m tm (ME: Mem.inject sm expr_inj_se f m tm)
    (IWB: inj_well_behaved f m tm)
    b lo hi
    m' (FREE: Mem.free m b lo hi = Some m')
    b'
    (FB: f b = Some (b',0))
    tm'
    (FREE': Mem.free tm b' lo hi = Some tm'),
    Mem.inject sm expr_inj_se f m' tm' /\
    inj_well_behaved f m' tm'.
Proof.
  clear.
  intros. Transparent Mem.free.
  unfold Mem.free in *.
  repeat destr_in FREE. repeat destr_in FREE'.
  inv FREE; inv FREE'.
  inv ME.
  split.
  constructor; simpl; intros; auto.
  - inv mi_inj; constructor; simpl; intros; auto.
    +  rewrite Mem.perm_unchecked_free in H0; try reflexivity; auto.
       rewrite Mem.perm_unchecked_free; try reflexivity.
       destruct H0.
       split.
       intro; subst. exploit (iwb_inj _ _ _ IWB b b1); eauto. 
       exploit iwb_o2o; eauto.
       eapply Mem.has_bounds_bounds; eauto.
       eapply Mem.has_bounds_bounds; eauto.
    + red in H0; red.
      rewrite Mem.unchecked_free_bounds' in *.
      repeat destr_in H0.
      * red in H0. simpl in H0. lia.
      * red in H0. simpl in H0. 
        eapply Mem.has_bounds_bounds in Heqb0; eauto. rewrite Heqb0 in Heqp. inv Heqp.
        des (zeq z z); des (zeq z0 z0).
      * apply Mem.has_bounds_bounds in Heqb0. apply Mem.has_bounds_bounds in Heqb1.
        rewrite Heqb1.
        destr. subst.
        exploit iwb_inj. eauto. apply FB. apply H. intro; subst. destr.
        exploit iwb_o2o; eauto. intro; subst.
        eapply mi_bounds; eauto.
    + rewrite ! Mem.unchecked_free_mask. eauto.
    + eapply mi_memval; eauto.
      rewrite Mem.perm_unchecked_free in H0; try reflexivity; eauto. destr.
       eapply Mem.has_bounds_bounds; eauto.
    + generalize (unchecked_free_nb_boxes m b _ _ (Mem.has_bounds_bounds _ _ _ _ Heqb0)).
      generalize (unchecked_free_nb_boxes tm b' _ _ (Mem.has_bounds_bounds _ _ _ _ Heqb1)).
      intuition omega.
  - red; unfold Mem.unchecked_free; simpl.
    eapply mi_mappedblocks in H; eauto.
  - red. intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 diff FB1 FB2 IB1 IB2.
    red in IB1, IB2.
    rewrite Mem.unchecked_free_bounds' in *.
    rewrite (Mem.has_bounds_bounds _ _ _ _ Heqb0) in *.
    des (zeq lo lo); des (zeq hi hi).
    red in IB1, IB2.
    des (eq_block b1 b); des (eq_block b2 b); try omega.
    eapply mi_no_overlap'.
    2: eauto. 2: eauto. auto. red. red.  omega.
    red; red; auto.
  - eapply mi_delta_pos; eauto.
  - specialize (mi_inj_dynamic _ _ _ H). des mi_inj_dynamic. des a.
    repSplit. eauto.
    intros. trim a0. auto. repSplit; destr.
    rewrite ! Mem.unchecked_free_bounds'.
    destr. subst. rewrite H in FB; inv FB. rewrite peq_true. des a0.
    rewrite e1. destr.
    destr. subst. trim e; destr. apply e in FB. destr.
    intros. apply e in H1; auto.
  - inv IWB; constructor; simpl; intros; eauto.
    + red in iwb_wb0 |- *. intros.
      rewrite <- ! Mem.size_block_snd, ! Mem.unchecked_free_bounds'.
      destr. rewrite Mem.unchecked_free_mask.
      rewrite Mem.size_block_snd. eauto.
    + rewrite <- ! Mem.size_block_snd, ! Mem.unchecked_free_bounds'.
      destr.
      * subst. assert (b' = b'0) by destr. subst.
        rewrite peq_true. apply Mem.has_bounds_bounds in Heqb1. rewrite Heqb1.
        apply Mem.has_bounds_bounds in Heqb0; rewrite Heqb0. auto.
      * assert (b' <> b'0). intro; subst. exploit iwb_inj0. apply H. apply FB. destr.
        destr. rewrite ! Mem.size_block_snd; eauto.
    + rewrite ! Mem.unchecked_free_mask. eauto.
Qed. 

Lemma iwb_ext:
  forall j j' m tm (IWB: inj_well_behaved j m tm)
    (EXT: forall b, j b = j' b),
    inj_well_behaved j' m tm.
Proof.
  intros; inv IWB; constructor; simpl; intros; eauto.
  - red in iwb_o2o0 |- *; simpl; intros; eauto.
    eapply iwb_o2o0. rewrite EXT. eauto.
  - red in iwb_wb0 |- *; simpl; intros; eauto.
    eapply iwb_wb0. rewrite EXT; auto.
  - rewrite <- EXT in H; eauto.
  - rewrite <- EXT in H; eauto.
  - apply iwb_no_oota0 in H. dex. rewrite EXT in H; eauto.
  - rewrite <- EXT in *; eauto.
Qed.

