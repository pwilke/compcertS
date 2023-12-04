Require Import Zwf.
Require Import Axioms.
Require Import Coqlib.
Require Intv.
Require Import Maps.
Require Archi.
Require Import Integers.
Require Import IntFacts.
Require Import Values.
Require Import List Sorted Orders.
Require Import Mergesort.
Require Import Permutation.
Require Import NormaliseSpec.
Local Notation "a # b" := (PMap.get b a) (at level 1).
Require Import Align Psatz PpsimplZ.

(** This module defines a greedy allocation algorithm that ensures that a
    concrete memory exists for a given abstract memory. *)


(** Properties of the [align] function. *)

(** Helper functions. *)
Definition get_mask (m: PMap.t (option nat)) (b:block) : nat :=
  (match PMap.get b m with
       Some m => m | None => O  
   end).

Definition get_size (bs: PMap.t (option (Z*Z))) (b:block) : Z :=
  match PMap.get b bs with
      Some (lo, hi) => hi-lo
    | None => 0
  end.

Definition get_bounds (bs: PMap.t (option (Z*Z))) (b:block) : Z*Z :=
  match PMap.get b bs with
      Some (lo, hi) => (lo,hi)
    | None => (0,0)
  end.

Require Import Compat.

Definition alignment_of_size (sz:Z) : nat :=
  (if zlt sz 2 then O
   else if zlt sz 3
        then 1
        else if zle sz 4 then 2
             else 3)%nat.

(* Lemma align_of_size_match: *)
(*   forall z, *)
(*     align_of_size 3%nat (Z.to_nat z) = *)
(*     alignment_of_size z. *)
(* Proof. *)
(*   intros. *)
(*   unfold align_of_size, alignment_of_size. *)
(*   change (sz_box 3) with 8%nat. *)
(*   destr. *)
(*   rewrite NPeano.ltb_lt in Heqb. *)
(*   destr. des z. des p; lia. *)
(*   destr. des z; try lia. des p; try lia. des p0; try lia. *)
(*   destr. des z; try lia. des p; try lia. des p0; try lia. *)
(*   des p0; try lia. des p; try lia. *)
(*   des z; try lia. des p; try lia; des p0; try lia; des p; try lia. *)
(*   generalize (NPeano.ltb_lt (Z.to_nat z) 8). *)
(*   rewrite Heqb. *)
(*   intros [A B]. *)
(*   assert (8 <= Z.to_nat z)%nat. rewrite NPeano.Nat.le_ngt. intro AA; specialize (B AA); congruence. *)
(*   change 8%nat with (Z.to_nat 8) in H. *)
(*   rewrite <- Z2Nat.inj_le in H; try lia. *)
(*   repeat destr; try lia. *)
(*   des z; try lia. *)
(* Qed. *)


Fixpoint list_ints (b:nat) : list nat :=
  match b with 
      O => nil
    | S m => b :: list_ints m
  end.

Definition mk_block_list_aux (sz:block -> Z) (b:nat) :=
  map (fun n => let b':= Pos.of_nat n in
                (b',sz b'))
              (list_ints b).

Definition size_mem_al (al:Z) (lb: list (block*Z)) (b:Z) :=
  List.fold_left 
    (fun acc (bsz:block*Z) =>
       let (b,sz) := bsz in
       align (align acc al + Z.max 0 sz) al
    ) lb b.

Lemma size_mem_al_permut:
  forall al lb lb',
    al > 0 ->
    Permutation lb lb' ->
    forall b,
      size_mem_al al lb b = size_mem_al al lb' b.
Proof.
  induction 2; simpl; intros; auto.
  - destruct x. destruct y.
    f_equal.
    generalize (align_divides b al H).
    generalize (align b al).
    intros.
    rewrite ! align_align; auto. 
    destruct (align_divides (z1 + Z.max 0 z0) al H).
    destruct (align_divides (z1 + Z.max 0 z) al H).
    rewrite H1; rewrite H2.
    destruct H0 as [x1 H0]. subst.
    assert (forall x z a (apos: a > 0),
              align (x*a+z) a = x*a + align z a).
    {
      clear; intros.
      unfold align.
      rewrite <- Z.add_opp_r.
      rewrite <- ! Z.add_assoc.
      rewrite Z_div_plus_full_l; try omega.
      rewrite Z.add_assoc.
      rewrite Z.add_opp_r.
      rewrite Z.mul_add_distr_r. 
      auto.
    }
    rewrite H0 in H1; auto.
    rewrite H0 in H2; auto.
    rewrite ! H0; auto.
    rewrite <- H1; auto. rewrite <- H2; auto. omega.
  - rewrite IHPermutation1. auto.
Qed.

Lemma size_mem_al_add:
  forall l b b' al,
    al > 0 -> 
    0 <= b <= b' ->
    0 <= size_mem_al al l b <=
    size_mem_al al l b'.
Proof.
  induction l; simpl; intros; auto. 
  destruct a.
  apply IHl; auto.
  split.
  generalize (align_le (align b al + Z.max 0 z) al H).
  generalize (align_le b al H).
  generalize (Zmax_spec 0 z).
  destr; omega.
  apply align_add; auto.
  split.
  generalize (align_le b al H).
  generalize (Zmax_spec 0 z).
  destr; omega.
  generalize (align_add al b b' H H0). omega.
Qed.

Lemma size_mem_al_pos:
  forall l b  al,
    al > 0 -> 0 <= b ->
    b <= size_mem_al al l b.
Proof.
  induction l; simpl; intros; auto.
  omega. destruct a.
  apply Zle_trans with (align (align b al + Z.max 0 z) al).
  generalize (align_le b al H).
  generalize (align_le (align b al + Z.max 0 z) al H).
  generalize (Zmax_spec 0 z). destr; omega.
  apply IHl; auto.
  generalize (align_le b al H).
  generalize (align_le (align b al + Z.max 0 z) al H).
  generalize (Zmax_spec 0 z). destr; omega.
Qed.


Definition alloc_mem_al (al:Z) (lb: list (block*Z)) (b : Z * (block -> Z)) :=
  List.fold_left 
    (fun (acc:Z*(block-> Z)) (bsz:block*Z) =>
       let (cur,fn) := acc in
       let (b,sz) := bsz in
       let new := align cur al in
       (align (new + Z.max 0 sz) al,
        (fun bb => if peq bb b 
                   then new 
                   else fn bb))
    ) lb b.


  Lemma alloc_size_mem_al:
    forall al bl zi mi z m,
      alloc_mem_al al bl (zi, mi) = (z, m) ->
      size_mem_al al bl zi = z.
  Proof.
    induction bl; simpl; intros.
    inv H; auto.
    destruct a.
    apply IHbl in H; auto.
  Qed.

Remark permutation_norepet:
  forall (A: Type) (l l': list A),
    Permutation l l' -> 
    list_norepet l -> 
    list_norepet l'.
Proof.
  induction 1; intros.
  - constructor.
  - inv H0. constructor; auto. red; intros; elim H3.
    apply Permutation_in with l'; auto. apply Permutation_sym; auto.
  - inv H. simpl in H2. inv H3. 
    constructor. simpl; intuition. constructor. intuition. auto.
  - eauto.
Qed.

Lemma mk_block_list_aux_ext:
  forall sz sz' m
         (same_sz: forall i, 
                     Ple i (Pos.of_nat m) ->
                     sz i = sz' i
         ),
    mk_block_list_aux sz  m =
    mk_block_list_aux sz' m.
Proof.
  Opaque Pos.of_nat.
  induction m; simpl; auto.
  unfold mk_block_list_aux. simpl.
  intros.
  rewrite same_sz by xomega.
  trim IHm.
  - intros. apply same_sz.
    unfold Ple in *. 
    rewrite Pos2Nat.inj_le in *.
    rewrite Nat2Pos.id_max in *.
    des m. omega.
  - destr.
    f_equal.
    apply IHm. 
Qed. 



Lemma if_false:
  forall {A} b (a c: A),
    b = false ->
    (if b then a else c) = c.
Proof.
  destruct b; auto. congruence.
Qed.

Lemma if_true:
  forall {A} b (a c: A),
    b = true ->
    (if b then a else c) = a.
Proof.
  destruct b; auto. congruence.
Qed.

Lemma get_size_same:
  forall b p t,
    get_size (PMap.set b (Some p) t) b = snd p - fst p.
Proof.
  intros; unfold get_size. 
  rewrite PMap.gss. des p. 
Qed.


Lemma mbla_rew:
  forall sz n,
    mk_block_list_aux sz (S n) =
    let s := sz (Pos.of_nat (S n)) in
    (Pos.of_nat (S n), s) :: mk_block_list_aux sz n.
Proof.
  reflexivity.
Qed.

Lemma blocks_not_empty:
  forall b sz,
    forall n,
      (Pos.to_nat b <= n)%nat ->
      (mk_block_list_aux sz n) <> nil.
Proof.
  induction n; intros. xomega.
  rewrite mbla_rew; simpl. discriminate. 
Qed.


Lemma mbla_suppr_above:
  forall sz' sz b
         (sz_ext: forall b',
                    b <> b' ->
                    sz' b' = sz b')
         n
         (sup: (Pos.to_nat b > n)%nat),             
    (mk_block_list_aux sz' n) = 
    (mk_block_list_aux sz n).
Proof.
  induction n; simpl; auto.
  intro sup.
  assert (b <> Pos.of_nat (S (n))).
  {
    intro; subst. rewrite Nat2Pos.id in  sup; omega.
  }
  rewrite ! mbla_rew.
  rewrite IHn by omega.
  rewrite sz_ext by auto.
  reflexivity.
Qed.

Lemma mbla_suppr_below:
  forall sz' sz b
         (sz_ext: forall b',
                    b <> b' ->
                    sz' b' = sz b')
         n
         (inf: (Pos.to_nat b <= n)%nat),
    Permutation ((b,sz b)::(mk_block_list_aux sz' n))
                ((b,sz' b)::(mk_block_list_aux sz n)).
Proof.
  induction n; simpl; auto.
  xomega.
  intros. 
  apply le_lt_or_eq in inf.
  destruct inf as [inf|eq].
  - rewrite ! mbla_rew. simpl.
    assert (Pos.of_nat (S n) <> b).
    { intro; subst. rewrite Nat2Pos.id in inf; omega. }
    rewrite sz_ext by auto.
    repeat rewrite (perm_swap (Pos.of_nat _,_)).
    apply perm_skip.
    apply IHn. omega.
  - clear IHn.
    assert (b = Pos.of_nat (S n)).
    { rewrite <- eq. rewrite Pos2Nat.id. auto. }
    rewrite ! mbla_rew.
    rewrite <- H. 
    rewrite (mbla_suppr_above sz' sz b); auto. 
    apply perm_swap. omega.
Qed.



Lemma size_mem_al_last:
  forall al (AlPos: al > 0) szb l b o,
    size_mem_al al (l ++ (b, szb) :: nil) (align o al) =
    size_mem_al al l (align o al) +
    align (Z.max 0 (szb)) al.
Proof.
  induction l; simpl; intros.
  - repeat rewrite <- ! align_distr. rewrite align_align. auto. auto. auto. 
  - destruct a. rewrite IHl. auto.
Qed.



Lemma Zle_add:
  forall a b,
    0 <= b ->
    a <= a + b.
Proof.
  intros; omega.
Qed.

Lemma alloc_mem_al_pos:
  forall l al s m s' m',
    alloc_mem_al al l (s,m) = (s',m') ->
    forall b,
      ~ In b (map fst l) ->
      m' b = m b.
Proof.
  induction l; simpl; intros.
  inv H; auto.
  des a.
  apply IHl with (b:=b) in H; auto.
  rewrite H. destr.
Qed.

Lemma mbla_not_above:
  forall sz n b,
    (n < Pos.to_nat b)%nat ->
    ~ In b (map fst (mk_block_list_aux sz n)).
Proof.
  induction n. simpl; intros; auto.
  intros.
  rewrite mbla_rew. simpl.
  destr.
  subst. rewrite Nat2Pos.id in H; omega.
  apply IHn in H1; auto. omega.
Qed.

Lemma compat_alloc_range_al:
  forall al (AlPos: al > 0) sz l 
         (lSpec: forall b z, In (b,z) l -> z = sz b)
         m0 size m
         size0 
         (ALLOC : alloc_mem_al al l (size0,m0) =
                  (size, m))
         (size0pos: 0 <= size0)
         b
         (IN: In b (map fst l)),
    size0 <= m b /\ m b + Z.max 0 (sz b) <= size.
Proof.
  induction l. 
  - simpl; intros. contradiction. 
  - intros. simpl in ALLOC.
    simpl in IN.
    destruct (in_dec peq b (map fst l)).
    + destruct a. simpl in *.
      eapply IHl with (b:=b) in ALLOC; eauto.
      destruct ALLOC; split; auto.
      * refine (Zle_trans _ _ _ _ H).
        rewrite <- align_distr.
        refine (Zle_trans _ _ _ (align_le _ al _) _); try omega.
        apply Zle_add.
        refine (Zle_trans _ _ _ (Zmax_bound_l 0 _ _ _) (align_le _ _ _)); try omega. auto.
      * rewrite <- align_distr; auto.
        transitivity size0; auto.
        refine (Zle_trans _ _ _ (align_le size0 al AlPos) _); try omega.
        apply Zle_add.
        refine (Zle_trans _ _ _ (Zmax_bound_l 0 _ _ _) (align_le _ _ _)); try omega.
    + destruct IN. subst. destruct a; simpl in *; subst.
      generalize (alloc_mem_al_pos _ _ _ _ _ _ ALLOC b).
      intro A; specialize (A n).
      rewrite peq_true in A.
      rewrite A.
      apply alloc_size_mem_al in ALLOC. subst.
      split. 
      * apply align_le; omega.
      * rewrite <- align_distr.
        refine (Zle_trans _ _ _ _ (size_mem_al_pos _ _ _ _ _)); try omega.
        apply Z.add_le_mono; try omega.
        specialize (lSpec b z (or_introl eq_refl)). subst.
        apply align_le; omega.
        specialize (lSpec b z (or_introl eq_refl)). subst.
        generalize (align_le size0 al AlPos)
                   (align_le (Z.max 0 (sz b)) al AlPos)
                   (Zmax_bound_l 0 0 (sz b)). omega. auto.
      * intuition.
Qed.


Lemma compat_alloc_range_al':
  forall al (AlPos: al > 0) l (nr: list_norepet (map fst l))
         size0 m0 size m
         (size0pos: 0 <= size0)
         (ALLOC : alloc_mem_al al l (size0,m0) = (size, m))
         b szb 
         (inf: In (b,szb) l),
    size0 <= m b /\ m b + Z.max 0 szb <= size.
Proof.
  induction l; simpl; intros. exfalso; auto.
  destruct a.
  destruct inf as [inf|inf].
  - inv inf.
    simpl in ALLOC.
    generalize ALLOC; apply alloc_mem_al_pos with (b:=b) in ALLOC.
    rewrite peq_true in ALLOC.
    rewrite ALLOC. intro.
    split.
    * apply align_le; omega. 
    * apply alloc_size_mem_al in ALLOC0.
      subst.
      refine (Zle_trans _ _ _ (align_le _ _ AlPos) _).
      apply size_mem_al_pos.
      omega.
      refine (Zle_trans _ _ _ _ (align_le _ _ AlPos)).
      transitivity (align size0 al).
      apply (Zle_trans _ _ _ size0pos). apply align_le; omega.
      rewrite Zmax_spec; destr; omega.
    * inv nr; auto.  
  - eapply IHl in ALLOC; eauto.
    + destruct ALLOC; split; auto.
      etransitivity; eauto.
      refine (Zle_trans _ _ _ (align_le _ _ AlPos) _); try omega.
      refine (Zle_trans _ _ _ (align_le _ _ AlPos) _); try omega.
      apply align_add. omega. 
      split.
      refine (Zle_trans _ _ _ size0pos (align_le _ _ AlPos)).
      rewrite Zmax_spec; destr; omega.
    + inv nr; auto. 
    + transitivity size0; auto.
      refine (Zle_trans _ _ _ (align_le _ _ AlPos) _). 
      refine (Zle_trans _ _ _ (align_le _ _ AlPos) _). 
      apply align_add. omega. 
      split.
      refine (Zle_trans _ _ _ size0pos (align_le _ al _)). omega.
      rewrite Zmax_spec; destr; omega.
Qed.

Lemma compat_alloc_aligned_al:
  forall al (AlPos: al > 0) l size0 m0 size m b
         (i: In b (map fst l))
         (ALLOC : alloc_mem_al al l (size0,m0) =
                  (size, m)),
    Z.divide al (m b).
Proof.
  induction l; simpl; intros.
  exfalso; auto.
  destruct (in_dec peq b (map fst l)).
  destruct a.
  - apply IHl with (b:=b) in ALLOC; auto.
  - des a. subst.
    apply alloc_mem_al_pos with (b:=b) in ALLOC; auto.
    rewrite ALLOC.
    rewrite peq_true.
    apply align_divides. auto. 
Qed.

Lemma mbla_in:
  forall sz n (b0 : block) (z : Z),
    In (b0, z) (mk_block_list_aux sz n) -> z = sz b0.
Proof.
  induction n; simpl; intros.
  contradiction.
  destruct H. inv H. auto.
  apply IHn. auto.
Qed.

Definition f_perm f (sz': positive -> Z)  n:=
  forall l
    (all_in: forall b, (Pos.to_nat b <= n)%nat -> In (b,sz' b) l)
    (lnr: list_norepet l),
    Permutation l (f l).

Lemma mbla_below_in:
  forall sz n b,
    (Pos.to_nat b <= n)%nat ->
    In b (map fst (mk_block_list_aux sz n)).
Proof.
  induction n; simpl; intros.
  xomega.
  apply le_lt_or_eq in H.
  destruct H as [inf|eq]; [right|left]; auto.
  apply IHn. omega.
  rewrite <- eq.
  apply Pos2Nat.id.
Qed.

Lemma mbla_below_in':
  forall sz n b,
    (Pos.to_nat b <= n)%nat ->
    In (b, sz b) (mk_block_list_aux sz n).
Proof.
  intros.
  exploit mbla_below_in; eauto.
  rewrite in_map_iff.
  intros [[bb zz] [EQ IN]]. simpl in *; subst.
  exploit  mbla_in. eauto. intros ->. eauto.
Qed.

Opaque mk_block_list_aux.

Lemma mbla_norepet:
  forall sz n,
    list_norepet (map fst (mk_block_list_aux sz n)).
Proof.
  induction n; simpl; intros.
  constructor.
  rewrite mbla_rew; simpl.
  destr.
  constructor; auto.
  eapply mbla_not_above; eauto. 
  rewrite Nat2Pos.id; auto.
Qed.

Lemma mbla_norepet':
  forall sz n,
    list_norepet (mk_block_list_aux sz n).
Proof.
  intros.
  eapply PTree_Properties.list_norepet_map.
  apply mbla_norepet.  
Qed.


Lemma fperm_mbla:
  forall f sz n (fperm: f_perm f sz n),
    Permutation (mk_block_list_aux sz n) (f (mk_block_list_aux sz n)).
Proof.
  intros.
  apply fperm.
  apply mbla_below_in'.
  apply mbla_norepet'.
Qed.


Lemma f_mbla_in:
  forall f sz n (fperm: f_perm f sz n) (b0 : block) (z : Z),
    In (b0, z) (f (mk_block_list_aux sz n)) -> z = sz b0.
Proof.
  intros.
  eapply Permutation_in in H.
  eapply mbla_in. eexact H.
  apply Permutation_sym. apply fperm_mbla; auto.
Qed.

Lemma compat_alloc_overlap_al:
  forall al (AlPos: al > 0) sz l b b'
         s0 m0 s m
         (s0sup: 0 <= s0)
         (ALLOC: alloc_mem_al al l (s0, m0) = (s, m))
         (nr: list_norepet (map fst l))
         (SZb': sz b' > 0)
         (diff: b <> b') 
         (i1: In (b', sz b') l)
         (i0: In (b, sz b) l),
    ~ m b <= m b' < m b + Z.max 0 (sz b).
Proof.
  induction l; simpl; intros; auto.
  destruct a.
  inv nr.
  des i0.
  - inv e. 
    generalize (alloc_mem_al_pos _ _ _ _ _ _ ALLOC _ H1); auto.
    rewrite peq_true. intro A; rewrite A in H0, H3.
    apply (compat_alloc_range_al') with (b:=b') (szb:=sz b') in ALLOC; eauto.
    + destruct ALLOC. 
      assert (m b' < m b').
      eapply Z.lt_le_trans; eauto.  
      etransitivity; eauto.
      apply align_le; omega. omega. 
    + refine (Z.le_trans _ _ _ _ (align_le _ al _)); try omega.
      transitivity (align s0 al).
      refine (Z.le_trans _ _ _ s0sup (align_le _ al _)); try omega.
      rewrite Zmax_spec; destr; omega.
  - inv H.
    generalize (alloc_mem_al_pos _ _ _ _ _ _ ALLOC _ H1); auto.
    rewrite peq_true. intro A; rewrite A in H0 , H3.
    apply (compat_alloc_range_al') with (b:=b) (szb:=sz b) in ALLOC; eauto. 
    * destruct ALLOC.
      assert (m b < m b); try omega.
      eapply Z.lt_le_trans; eauto.
      eapply Z.le_lt_trans; eauto.
      rewrite <- align_distr. 
      assert (align 1 al <= align (Z.max 0 (sz b')) al).
      apply align_add; auto. lia.
      generalize (align_le (Z.max 0 (sz b')) _ AlPos). lia.
      auto.       
    * refine (Z.le_trans _ _ _ _ (align_le _ al _)); try omega.
      transitivity (align s0 al).
      refine (Z.le_trans _ _ _ s0sup (align_le _ al _)); try omega.
      rewrite Zmax_spec; destr; omega.
  - apply IHl with (b:=b) (b':=b') in ALLOC; eauto. 
    refine (Z.le_trans _ _ _ _ (align_le _ al _)); try omega.
    transitivity (align s0 al).
    refine (Z.le_trans _ _ _ s0sup (align_le _ al _)); try omega.
    rewrite Zmax_spec; destr; omega.
Qed.


Section MaxAlign.
  Variable MA: nat.
  Hypothesis MA_bound: (3 <= MA)%nat.
  Let tpMA := two_power_nat MA.
  Let tpMA_pos := two_power_nat_pos MA.
  
  Definition size_mem_aux (t : list (block *Z)) : Z :=
    size_mem_al tpMA t tpMA.

  Definition alloc_mem_aux (t : list (block *Z)) : Z * (block -> Z) :=
    alloc_mem_al tpMA t (tpMA, (fun _ => 0)).


  Lemma alloc_size_mem_aux:
    forall  bl  z m,
      alloc_mem_aux bl  = (z, m) ->
      size_mem_aux  bl  = z.
  Proof.
    unfold alloc_mem_aux, size_mem_aux.
    intros until 0.
    apply alloc_size_mem_al.
  Qed.

  Lemma size_mem_aux_alloc :
    forall t p,
      size_mem_aux t <=
      size_mem_aux (p::t).
  Proof.
    intros.
    unfold size_mem_aux.
    destruct p as [b z].
    Opaque Z.add.
    simpl. 
    apply size_mem_al_add. auto.
    split. auto. unfold tpMA; Psatz.lia.
    rewrite <- align_distr; auto.
    rewrite align_refl; auto.
    generalize (align_le (Z.max 0 z) tpMA).
    rewrite Zmax_spec; destr; omega.
  Qed.

Lemma  size_mem_aux_permut:
  forall t t',
    Permutation t t' ->
    size_mem_aux t = size_mem_aux t'.
Proof.
  intros.
  unfold size_mem_aux.
  apply size_mem_al_permut; auto. 
Qed.

Lemma size_mem_aux_last:
  forall szb l b,
    size_mem_aux (l ++ (b, szb) :: nil) =
    size_mem_aux l +
    align (Z.max 0 (szb)) tpMA.
Proof.
  unfold size_mem_aux; intros.
  rewrite <- (align_refl tpMA) at 2 4; auto.
  rewrite size_mem_al_last; auto.
Qed.

Lemma size_mem_aux_first:
  forall szb l b,
    size_mem_aux ((b, szb) :: l) =
    size_mem_aux l + align (Z.max 0 (szb)) tpMA.
Proof.
  intros.
  rewrite <- (size_mem_aux_last _ _ b).
  apply size_mem_aux_permut.
  rewrite Permutation_rev.
  simpl.
  apply Permutation_app; auto.
  rewrite Permutation_rev.
  rewrite rev_involutive; auto.
Qed.

Lemma size_mem_free_eq:
  forall sz' sz n b
         (sz_ext: forall b',
                    b <> b' ->
                    sz' b' = sz b'),
    size_mem_aux (mk_block_list_aux sz  n) =
    size_mem_aux (mk_block_list_aux sz' n)
    + if le_dec (Pos.to_nat b) n 
      then align (Z.max 0 (sz b)) tpMA - align (Z.max 0 (sz' b)) tpMA
      else 0.
Proof.
  intros. 
  destruct (le_dec (Pos.to_nat b) n).
  - specialize (mbla_suppr_below sz' sz b sz_ext n l). simpl in *.
    intros H.
    apply Permutation_sym in H; auto.
    apply size_mem_aux_permut in H.
    rewrite ! size_mem_aux_first in H.
    omega.
  - rewrite (mbla_suppr_above sz' sz b); auto; omega.
Qed.

Lemma size_mem_free_eq':
  forall sz' sz n b
         (sz_ext: forall b',
                    b <> b' ->
                    sz' b' = sz b')
         (new_sz: sz' b = 0),
    size_mem_aux (mk_block_list_aux sz  n) =
    size_mem_aux (mk_block_list_aux sz' n)
    + if le_dec (Pos.to_nat b) n 
      then align (Z.max 0 (sz b)) tpMA
      else 0.
Proof.
  intros. 
  erewrite size_mem_free_eq; eauto.
  rewrite new_sz.
  rewrite Z.max_id.
  rewrite align_0; auto.
  rewrite Z.sub_0_r; auto. 
Qed.

Lemma compat_alloc_range:
  forall sz n size m f (fperm: f_perm f sz n)
         (ALLOC: alloc_mem_aux (f (mk_block_list_aux sz n)) = (size,m)),
  forall b,
    (Pos.to_nat b <= n)%nat ->
    tpMA <= m b /\ m b + Z.max 0 (sz b) <= size.
Proof.
  unfold alloc_mem_aux; simpl.
  intros.
  eapply compat_alloc_range_al; eauto.
  apply f_mbla_in. auto.
  unfold tpMA;omega.
  exploit (mbla_below_in sz). eauto.
  rewrite ! in_map_iff.
  intros ((b0 & z) & A & B).
  simpl in *. subst.
  exists (b,z); simpl; split; auto.
  eapply Permutation_in.
  apply fperm_mbla; auto.
  auto.
Qed.

Lemma blocks_not_empty_in:
  forall b sz,
    forall n,
      (Pos.to_nat b <= n)%nat ->
      In (b,sz b) (mk_block_list_aux sz n).
Proof.
  induction n; intros. xomega. 
  apply le_lt_or_eq in H; destruct H.
  - rewrite mbla_rew. simpl. 
    right. apply IHn; omega.
  - clear IHn.
    rewrite mbla_rew; simpl. 
    rewrite <- H.
    rewrite Pos2Nat.id. auto.
Qed.

Lemma compat_alloc_aligned_f:
  forall sz n size m f (fperm: f_perm f sz n)
         (ALLOC: alloc_mem_aux (f (mk_block_list_aux sz n)) = (size,m)),
  forall b,
    (Pos.to_nat b <= n)%nat ->
    Z.divide tpMA (m b).
Proof.
  intros.
  eapply compat_alloc_aligned_al; eauto.
  generalize (blocks_not_empty_in b sz _ H).       
  intro MBL.
  apply in_map with (f:=fst) in MBL; simpl in *; auto.
  revert MBL.
  apply Permutation_in.
  apply Permutation_map.
  apply fperm_mbla; auto.
Qed.

Lemma compat_alloc_aligned:
  forall sz n size m
         (ALLOC: alloc_mem_aux (mk_block_list_aux sz n) = (size,m)),
  forall b,
    (Pos.to_nat b <= n)%nat ->
    Z.divide tpMA (m b).
Proof.
  intros.
  eapply compat_alloc_aligned_f with (f:=id); eauto.
  red; simpl; intros. unfold id. reflexivity.
Qed.

Opaque mk_block_list_aux.

Lemma compat_alloc_no_overlap:
  forall sz l (lSpec: forall b z, In (b,z) l -> z = sz b)
         (lnr: list_norepet (map fst l))
         size m
         (ALLOC: alloc_mem_aux l = (size,m)),
  forall b b',
    b <> b' ->
    In b (map fst l) ->
    In b' (map fst l) ->
    sz b' > 0 ->
    ~ (m b <= m b' < m b + Z.max 0 (sz b)).
Proof.
  unfold alloc_mem_aux; simpl.
  intros.
  rewrite in_map_iff in H0, H1.
  destruct H0 as ((b0 & z0) & A & B).
  destruct H1 as ((b1 & z1) & C & D).
  simpl in *; subst.
  generalize (lSpec _ _ D); intro; subst; auto.
  generalize (lSpec _ _ B); intro; subst; auto.
  eapply compat_alloc_overlap_al. 3: eauto.
  auto. unfold tpMA; lia. auto. auto. auto. auto. auto.
Qed.

Lemma compat_alloc_no_overlap_mbla:
  forall sz n size m
         (ALLOC: alloc_mem_aux (mk_block_list_aux sz n) = (size,m)),
  forall b b',
    b <> b' ->
    (Pos.to_nat b <= n)%nat ->
    (Pos.to_nat b' <= n)%nat ->
    sz b' > 0 ->
    ~ (m b <= m b' < m b + Z.max 0 (sz b)).
Proof.
  intros.
  eapply compat_alloc_no_overlap; eauto.
  eapply mbla_in.
  apply mbla_norepet.
  apply mbla_below_in; auto.
  apply mbla_below_in; auto.
Qed.

Lemma perm_in:
  forall A l l' (x:A),
    Permutation l l' ->
    (In x l <-> In x l').
Proof.
  split; intros.
  eapply Permutation_in; eauto.
  apply Permutation_sym in H.
  eapply Permutation_in; eauto.
Qed.

Lemma f_mbla_norepet:
  forall f sz n (fperm: f_perm f sz n),
    list_norepet (map fst (f (mk_block_list_aux sz n))).
Proof.
  intros.
  generalize (mbla_norepet sz n).
  generalize (Permutation_map fst (fperm_mbla _ _ _ fperm)).
  apply permutation_norepet. 
Qed.

Lemma compat_alloc_no_overlap_f_mbla:
  forall sz n size m
         f (fperm: f_perm f sz n)
         (ALLOC: alloc_mem_aux (f (mk_block_list_aux sz n)) = (size,m)),
  forall b b',
    b <> b' ->
    (Pos.to_nat b <= n)%nat ->
    (Pos.to_nat b' <= n)%nat ->
    sz b' > 0 ->
    ~ (m b <= m b' < m b + Z.max 0 (sz b)).
Proof.
  intros.
  eapply compat_alloc_no_overlap; eauto.
  - intros b0 z. erewrite <- perm_in. eapply mbla_in.
    apply fperm_mbla; auto.
  - apply f_mbla_norepet; auto. 
  - generalize ( mbla_below_in sz n b H0).
    generalize (Permutation_map fst (fperm_mbla _ _ _ fperm)).
    eapply Permutation_in.
  - generalize ( mbla_below_in sz n b' H1).
    generalize (Permutation_map fst (fperm_mbla _ _ _ fperm)).
    eapply Permutation_in.
Qed.


Lemma mk_block_list_aux_ext':
  forall (m : nat) (sz sz' : positive -> Z),
    (forall i : positive, Plt i (Pos.of_nat m) -> sz i = sz' i) ->
    mk_block_list_aux sz  (pred m) =
    mk_block_list_aux sz' (pred m).
Proof.
  intros.
  des m. des n.
  apply mk_block_list_aux_ext.
  intros. apply H; auto.  
  rewrite Nat2Pos.inj_succ; try omega.
  xomega.
Qed.


Inductive appears_before {A: Type} : A -> A -> list A -> Prop :=
| ab_intro: forall a b l l1 l2 l3,
              l = l1 ++ (a :: l2) ++ b :: l3 ->
              ~ In b l1 ->
              appears_before a b l.

Lemma ab_rev:
  forall A l (a b: A) (Aeq: forall a b : A , {a = b} + { a <> b }),
    list_norepet l ->
    appears_before a b l ->
    appears_before b a (rev l).
Proof.
  induction l; simpl; intros.
  - inv H0. contradict H1; clear.
    apply app_cons_not_nil.
  - inv H.
    inv H0.
    generalize (f_equal (@rev A) H).
    simpl.
    intro B; rewrite B. rewrite ! rev_app_distr. simpl.
    rewrite ! rev_app_distr. simpl.
    rewrite <- ! app_assoc.
    eapply ab_intro.
    instantiate (1:= rev l1).
    instantiate (1:= rev l2).
    instantiate (1:= rev l3).
    simpl. auto.

    des (Aeq a0 a).
    des l1. inv H.
    simpl in *.
    apply H3.
    rewrite in_app.
    right. simpl; auto.
    right. apply in_rev; auto.
    inv H.
    simpl in *.
    apply H3.
    rewrite in_app.
    right. simpl; auto.

    des l1. inv H.
    clear - H4 H0.
    rewrite ! list_norepet_app in H4.
    intuition.
    inv H2. 
    clear - H0 H5.
    apply H5.
    apply in_app. simpl. apply in_rev in H0; auto.
Qed.

Lemma ab_in2:
  forall A l (a b: A)
         (AB : appears_before a b (a :: l)),
    In b l.
Proof.
  intros.
  inv AB.
  des l1; inv H;
  repeat (rewrite in_app; simpl; auto).
Qed.


Lemma ab_inl:
  forall (b b': block) l
         (APB : appears_before b b' (map fst l)),
    exists szb':Z, In (b',szb') l.
Proof.
  intros.
  inv APB.
  assert (In b' (map fst l)).
  rewrite H.
  repeat (rewrite in_app; simpl; auto).
  rewrite in_map_iff in H1.
  destruct H1 as ((bb & zz) & A & B). simpl in *; subst.
  eexists; eauto.
Qed.


Lemma ab_first_in:
  forall (b b': block) l
         (APB : appears_before b b' (map fst l)),
    exists szb:Z, In (b,szb) l.
Proof.
  intros.
  inv APB.
  assert (In b (map fst l)).
  rewrite H.
  repeat (rewrite in_app; simpl; auto).
  rewrite in_map_iff in H1.
  destruct H1 as ((bb & zz) & A & B). simpl in *; subst.
  eexists; eauto.
Qed.


Lemma alloc_mem_al_order:
  forall aa (AlPos: aa > 0) l al sz z cur
         (AMA: alloc_mem_al aa l (z,cur) = (sz,al))
         (Zpos: 0 <= z)
         (lnr: list_norepet (map fst l))
         b b'
         (AB: appears_before b b' (map fst l))
         z z'
         (I1: In (b,z) l) (I2: In (b',z') l)
         (Zpos: z > 0) (Zpos': z' > 0),
    al b < al b' \/ b = b'.
Proof.
  induction l; simpl; intros.
  contradiction.
  destruct a. simpl in *.
  inv lnr. 
  destruct (peq b b'); auto.
  left.
  destruct (peq b b0).
  - subst. 
    destruct I1. inv H.
    generalize (alloc_mem_al_pos _ _ _ _ _ _ AMA _ H1).
    rewrite peq_true.
    intro A; rewrite A.
    assert (In b' (map fst l)). eapply ab_in2. eauto. 
    generalize H; rewrite in_map_iff.
    intros ((b & z1) & B & C). simpl in *; subst.
    generalize (fun pos => compat_alloc_range_al' _ AlPos _ H2 _ _ _ _ pos AMA _ _ C).

    intro D; trim D.
    generalize (align_le z _ AlPos) (Z.le_max_l 0 z0).
    generalize (align_le (align z aa + Z.max 0 z0) aa).
    omega.
    destruct D.
    rewrite <- align_distr in H0.
    apply Z.lt_le_trans with (m:=align z aa + align (Z.max 0 z0) aa).
    generalize (Z.le_max_r 0 z0) (align_le (Z.max 0 z0) aa). omega.
    auto. auto.
    apply (in_map fst) in H. simpl in H; congruence.

  - destruct I1. inv H. congruence.
    exploit IHl. eexact AMA. 
    generalize (align_le z aa) (Z.le_max_l 0 z1).
    generalize (align_le (align z aa + Z.max 0 z1) _ AlPos).
    omega. auto. 
    inv AB.
    des l1.
    apply (ab_intro _ _ _ l0 l2 l3). inv H0.
    rewrite H8; simpl; eauto.
    auto. eauto.
    inv AB. des l1. inv H0. eauto.
    auto. auto.
    intros [A|A]; auto. congruence.
Qed.

Lemma norepet_eq:
  forall {A B} l,
    list_norepet (map fst l) ->
    forall (b: A) (z z': B),
    In (b, z) l ->
    In (b, z') l ->
    z = z'.
Proof.
  induction l; simpl; intros.
  contradiction.
  inv H.
  destruct a; simpl in *.
  trim IHl. auto.
  destruct H0, H1.
  inv H. inv H0; auto.
  inv H. apply (in_map fst) in H0. simpl in H0. congruence.
  inv H0. apply (in_map fst) in H. simpl in H. congruence.
  eauto.
Qed.



      
Lemma ab_dec:
  forall A (Aeq: forall (a b : A), {a=b} + {a <> b}) (l: list A) b b' 
    (diff: b <> b')
    (IN1: In b l)
    (IN2: In b' l),
    appears_before b b' l \/ appears_before b' b l.
Proof.
  induction l; simpl; intros; auto.
  contradiction.
  destruct IN1 as [IN1|IN1], IN2 as [IN2|IN2]; subst; try congruence.
  - left.
    destruct (in_split _ _ IN2) as (l1 & l2 & EQ).
    apply (ab_intro _ _ _ nil l1 l2). subst. simpl. auto.
    simpl; auto.
  - right.
    destruct (in_split _ _ IN1) as (l1 & l2 & EQ).
    apply (ab_intro _ _ _ nil l1 l2). subst. simpl. auto.
    simpl; auto.
  - specialize (IHl _ _ diff IN1 IN2).
    destruct (Aeq b a); destruct (Aeq b' a); subst; try congruence.
    + left.
      destruct (in_split _ _ IN2) as (l1 & l2 & EQ). 
      apply (ab_intro _ _ _ nil l1 l2); subst; simpl; auto.
    + right.
      destruct (in_split _ _ IN1) as (l1 & l2 & EQ). 
      apply (ab_intro _ _ _ nil l1 l2); subst; simpl; auto.
    + destruct IHl as [I|I]; [left|right];
      inversion I as [? ? ? X Y Z]; subst;
      apply (ab_intro _ _ _ (a::X) Y Z); subst; simpl; auto;
      intro G; destruct G; try congruence.
Qed.

Lemma list_norepet_rev:
  forall A (l:list A),
    list_norepet l -> list_norepet (rev l).
Proof.
  intros A l.
  apply permutation_norepet.
  apply Permutation_rev.
Qed.

Lemma mk_block_list_aux_eq:
  forall  lo hi b' bs ,
    mk_block_list_aux
      (fun b0 : block =>
         get_size
           (PMap.set b' (Some (lo, hi)) bs)
           b0)
      (pred (Pos.to_nat (Pos.succ b'))) =
    (b',hi-lo):: mk_block_list_aux
               (fun b0 => get_size bs b0)
               (pred (Pos.to_nat b')).
Proof.
  intros.
  replace (pred (Pos.to_nat (Pos.succ b'))) with (S (pred (Pos.to_nat b'))) by (zify; omega).
  rewrite mbla_rew; simpl.
  replace (Pos.of_nat (S (pred (Pos.to_nat b')))) with b'. 
  unfold get_size. rewrite PMap.gss.
  f_equal.
  erewrite mk_block_list_aux_ext'; eauto.
  intro i.
  rewrite Pos2Nat.id; auto. intro. 
  rewrite PMap.gso; auto. intro; subst. xomega.
  rewrite <- S_pred with (n:=Pos.to_nat b') (m:=O) by xomega.
  rewrite Pos2Nat.id; auto. 
Qed.





Lemma size_mem_inf_add_larger:
  forall m1 m2 (p1 p2: block) (lo hi lo' hi': Z),
    hi >= 0 -> hi' >= 0 -> hi >= lo ->
    hi' - lo' >= hi - lo ->
    size_mem_aux
      (mk_block_list_aux (get_size m2) 
                         (pred (Pos.to_nat p2))) <=
   size_mem_aux
     (mk_block_list_aux (get_size m1) 
                        (pred (Pos.to_nat p1))) ->
   size_mem_aux
     (mk_block_list_aux
        (get_size
           (PMap.set (p2) (Some (lo, hi)) (m2)))
        (Pos.to_nat p2)) <=
   size_mem_aux
     (mk_block_list_aux
        (get_size
           (PMap.set (p1) (Some (lo', hi')) (m1)))
        (Pos.to_nat p1)).
Proof.
  intros m1 m2 p1 p2 lo hi lo' hi' Hpos Hpos' Hhilo Hsizes sizes.
  replace (Pos.to_nat p2) with (pred (Pos.to_nat (Pos.succ p2))) by (zify; omega).
  replace (Pos.to_nat p1) with (pred (Pos.to_nat (Pos.succ p1))) by (zify; omega).
  rewrite ! mk_block_list_aux_eq; auto.  
  rewrite ! size_mem_aux_first.
  apply Z.add_le_mono; auto.
  apply align_add; auto. 
  split.
  apply Zmax_bound_l; omega.
  apply Z.max_le_compat_l. omega.
Qed. 


Lemma size_mem_inf_add':
  forall m1 m2 (p1 p2: block) (lo hi : Z),
    hi >= 0 -> lo <= hi ->
    size_mem_aux
      (mk_block_list_aux (get_size m2) 
                         (pred (Pos.to_nat p2))) <=
   size_mem_aux
     (mk_block_list_aux (get_size m1) 
                        (pred (Pos.to_nat p1))) ->
   size_mem_aux
     (mk_block_list_aux
        (get_size
           (PMap.set (p2) (Some (lo, hi)) (m2)))
         (Pos.to_nat (p2))) <=
   size_mem_aux
     (mk_block_list_aux
        (get_size
           (PMap.set (p1) (Some (lo, hi)) (m1)))
        (Pos.to_nat (p1))).
Proof.
  intros.
  apply size_mem_inf_add_larger; auto. omega. omega.
Qed. 


Section AllocBlocks.
  Variable memsize: Z.
  Hypothesis memsize_int: memsize <= Int.max_unsigned.
  
  Definition alloc_blocks (t: list (block*Z)) : option (block -> int) :=
    let (sz,m) := alloc_mem_aux t in
    if zlt sz memsize
    then Some (fun b => Int.repr (m b))
    else None.

  Lemma allocs_blocks_free':
    forall sz' sz n b
      (sz_ext: forall b',
          b <> b' ->
          sz' b' = sz b')
      (new_sz: sz' b = 0),
      alloc_blocks (mk_block_list_aux sz n) <> None ->
      alloc_blocks (mk_block_list_aux sz' n) <> None.
  Proof.
    intros sz' sz n b sz_ext new_sz.
    unfold alloc_blocks.
    destr.
    revert H; destr. 
    repeat (revert H0; destr).
    apply alloc_size_mem_aux in Heqp.
    apply alloc_size_mem_aux in Heqp0.
    cut (z1 <= z). omega.
    subst.
    rewrite (size_mem_free_eq' sz' sz n b); eauto.
    destr; try omega.
    apply Zle_add.
    generalize (align_le (Z.max 0 (sz b)) tpMA)
               tpMA_pos
               (Zmax_bound_l 0 0 (sz b)). unfold tpMA. lia. 
  Qed.

  Lemma allocs_blocks_free:
    forall sz' sz n b
      (sz_ext: forall b',
          b <> b' ->
          sz' b' = sz b')
      (new_sz_msk: (sz' b = sz b) \/
                   ( sz' b = 0)),
      alloc_blocks (mk_block_list_aux sz n) <> None ->
      alloc_blocks (mk_block_list_aux sz' n) <> None.
  Proof.
    intros.
    destruct new_sz_msk as [A|A].
    - rewrite <- mk_block_list_aux_ext with (sz:=sz); auto.
      intros; destruct (peq i b); subst; auto.
      rewrite sz_ext; auto.
    - eapply allocs_blocks_free'; eauto.
  Qed.    

  
  Lemma compat_alloc:
  forall (sz: block -> Z*Z) sz' msk
         (MSKeq: forall b,
                 exists n,
                   (n <= MA)%nat /\
                   msk b = Int.not (Int.repr (two_power_nat n - 1))) 
         (lo0: forall b, fst (sz b) <= 0)
         (SZeq: forall b, let (lo,hi) := sz b in sz' b = hi - lo)
         n al 
         (SZabove:
            forall b, (Pos.to_nat b > n)%nat -> sz b = (0, 0))
         f
         (fperm: f_perm f sz' n)
         (ALLOC: alloc_blocks (f (mk_block_list_aux sz' n)) = Some al),
    compat memsize sz msk al.
Proof.
  intros.
  constructor.
  - intros.
    clear MSKeq.
    unfold alloc_blocks in ALLOC.
    destruct (alloc_mem_aux (f (mk_block_list_aux sz' n))) eqn:?.
    destruct (le_dec (Pos.to_nat b) n).
    + generalize (compat_alloc_range _ _ _ _ _ fperm Heqp 
                                     b l).
      unfold in_bound in H.
      specialize (SZeq b).
      destruct (sz b) eqn:?.
      simpl in *.
      rewrite SZeq.
      intro A.
      destruct (zlt z memsize); try congruence.
      inv ALLOC.
      unfold Int.add.
      rewrite (Int.unsigned_repr (z0 b)).
      rewrite Int.unsigned_repr.
      split. 
      * apply Z.lt_le_trans with (m:=z0 b); auto.
        generalize (tpMA_pos); unfold tpMA in *; lia.
        generalize (Int.unsigned_range o); omega.
      * apply Z.le_lt_trans with (m:=z); auto.
        destruct A; etransitivity; eauto.
        apply Z.add_le_mono; try omega.
        rewrite Zmax_spec. destr_no_dep; try omega. 
        specialize (lo0 b). rewrite Heqp0 in lo0; simpl in lo0. omega.
      * split.
        generalize (tpMA_pos); unfold tpMA in *.
        generalize  (Int.unsigned_range o); lia. 
        transitivity z; auto. destruct A; etransitivity; eauto.
        apply Z.add_le_mono_l.
        rewrite Zmax_spec. destr_no_dep; try omega. 
        specialize (lo0 b). rewrite Heqp0 in lo0. simpl in lo0. omega.
        omega.
      * destruct A; split; try omega.
        generalize (tpMA_pos); unfold tpMA in *; lia.
        transitivity z; auto.
        etransitivity ; eauto.
        rewrite Zmax_spec; destr; omega. omega.
    + destruct (eq_nat_dec n O).
      * subst. rewrite SZabove in H.
        unfold in_bound in H; simpl in H; omega. omega.
      * rewrite SZabove in H.
        unfold in_bound in H; simpl in H; omega. 
        omega.
  - intros b b' o o' diff IB1 IB2.
    unfold alloc_blocks in ALLOC.
    repeat (revert ALLOC; destr).
    generalize (compat_alloc_no_overlap_f_mbla sz' n z z0 _ fperm Heqp _ _ diff).
    assert (diff': b' <> b) by auto.
    generalize (compat_alloc_no_overlap_f_mbla sz' n z z0 _ fperm Heqp _ _ diff').
    destruct (le_dec (Pos.to_nat b) n).
    destruct (le_dec (Pos.to_nat b') n).
    + intros B A; specialize (A l0 l1);
      specialize (B l1 l0).
      generalize (SZeq b) (SZeq b').    
      generalize (compat_alloc_range _ _ _ _ _ fperm Heqp 
                                     b l0 ).
      generalize (compat_alloc_range _ _ _ _ _ fperm Heqp 
                                     b' l1).
      destruct (sz b) eqn:?; destruct (sz b') eqn:?.
      unfold in_bound in *. simpl in *.
      intros C D E F. 
      trim A. clear - F IB2. omega.
      trim B. clear - E IB1. omega.
      inv ALLOC.
      unfold Int.add in H. 
      generalize (lo0 b) (lo0 b').
      rewrite Heqp0, Heqp1. simpl; intros; subst. 
      rewrite (Int.unsigned_repr (z0 b)) in H.
      rewrite (Int.unsigned_repr (z0 b')) in H.
      rewrite Int.unsigned_repr in H.
      rewrite Int.unsigned_repr in H.
      destruct (zlt (Int.unsigned o) (Int.unsigned o')).
      * apply B.
        assert (z0 b = z0 b' + Int.unsigned o' - Int.unsigned o) by omega.
        rewrite H2.
        split. omega.
        rewrite F. rewrite Zmax_spec. destr; try omega.
        cut (Int.unsigned o' < z4 - z3).
        cut (Int.unsigned o >= 0); try omega.
        generalize (Int.unsigned_range o); omega.
        omega.
      * apply A.
        assert (z0 b' = z0 b + Int.unsigned o - Int.unsigned o') by omega.
        rewrite H2.
        split. omega.
        rewrite E. rewrite Zmax_spec. destr; try omega.
        cut (Int.unsigned o < z2 - z1).
        cut (Int.unsigned o' >= 0); try omega.
        generalize (Int.unsigned_range o'); omega.
        omega.
      * generalize (Int.unsigned_range_2 o').
        destruct C. intro.
        split. generalize (tpMA_pos); unfold tpMA in *. lia. 
        transitivity z; auto. 
        etransitivity; eauto. rewrite F.
        rewrite Zmax_spec; destr; try omega. omega.
      * generalize (Int.unsigned_range_2 o).
        destruct D. intro.
        split. generalize (tpMA_pos); unfold tpMA in *. lia. 
        transitivity z; auto. 
        etransitivity; eauto. rewrite E.
        rewrite Zmax_spec; destr; omega. omega.
      * split. generalize (tpMA_pos); unfold tpMA in *. lia. 
        transitivity z; auto.
        destruct C; etransitivity; eauto.
        rewrite Zmax_spec; destr; omega. omega.
      * split. generalize (tpMA_pos); unfold tpMA in *. lia. 
        transitivity z; auto.
        destruct D; etransitivity; eauto.
        rewrite Zmax_spec; destr; omega. omega.
    + rewrite SZabove in IB2. unfold in_bound in IB2; simpl in IB2. omega. omega.
    + rewrite SZabove in IB1. 
      unfold in_bound in IB1; simpl in IB1; omega.
      omega.
  - intros.
    destruct (le_dec (Pos.to_nat b) n). 
    * unfold alloc_blocks in ALLOC.
        Opaque two_power_nat.
        repeat (revert ALLOC; destr).
        generalize (compat_alloc_aligned_f _ _ _ _ _ fperm Heqp  _ l ).
        intros [x A].
        inv ALLOC.
        rewrite A.
        destruct (MSKeq b) as [nn [B C]].
        rewrite C.
        simpl.
        {
          solve_int. 
          rewrite Int.bits_not; auto.        
          rewrite ! Int.testbit_repr; auto.
          rewrite two_power_nat_two_p.
          rewrite Int.Ztestbit_two_p_m1; auto; try omega.
          destr; try ring.
          generalize (Int.Ztestbit_mod_two_p (Z.of_nat MA) (x*tpMA) i).
          destr; try omega. 
          rewrite <- H; auto with zarith.
          unfold tpMA.
          rewrite two_power_nat_two_p.
          rewrite Z.mod_mul; auto.
          rewrite Int.Ztestbit_0. reflexivity. generalize tpMA_pos. rewrite two_power_nat_two_p.
          lia.
        }
    *
      unfold alloc_blocks in ALLOC.
      destruct (alloc_mem_aux (f (mk_block_list_aux sz' n))) eqn:?; try discriminate.
      destruct (zlt z memsize) eqn:?; try discriminate.
      unfold alloc_mem_aux in Heqp.
      eapply alloc_mem_al_pos in Heqp; eauto.
      inv ALLOC.
      rewrite Heqp. rewrite Int.and_zero_l. reflexivity.
      generalize (mbla_not_above sz' n b).  intro A; trim A. omega.
      intro.
      apply A.
      revert H.
      generalize (Permutation_sym  (Permutation_map fst (fperm_mbla _ _ _ fperm))). 
      eapply Permutation_in.
Qed.

Lemma compat_alloc'':
  forall (sz: block -> Z*Z) sz' msk
         (MSKeq: forall b,
                 exists n,
                   (n <= MA)%nat /\
                   msk b = Int.not (Int.repr (two_power_nat n - 1))) 
         (lo0: forall b, fst (sz b) <= 0)
         (SZeq: forall b, let (lo,hi) := sz b in sz' b = hi - lo)
         n al 
         (SZabove:
            forall b, (Pos.to_nat b > n)%nat -> sz b = (0, 0))
         f
         (fperm: forall l, Permutation l (f l))
         (ALLOC: alloc_blocks (f (mk_block_list_aux sz' n)) = Some al),
    compat memsize sz msk al.
Proof.
  intros.
  eapply compat_alloc; eauto.
  red; intros; auto.
Qed.

Lemma compat_alloc':
  forall (sz: block -> Z*Z) sz' msk
         (MSKeq: forall b,
                 exists n,
                   (n <= MA)%nat /\
                   msk b = Int.not (Int.repr (two_power_nat n - 1))) 
         (lo0: forall b, fst (sz b) <= 0)
         (SZeq: forall b, let (lo,hi) := sz b in sz' b = hi - lo)
         n al 
         (SZabove:
            forall b, (Pos.to_nat b > n)%nat -> sz b = (0, 0))
         (ALLOC: alloc_blocks (mk_block_list_aux sz' n) = Some al),
    compat memsize sz msk al.
Proof.
  intros.
  eapply compat_alloc'' with (f:=id); simpl; eauto.
Qed.

Lemma alloc_blocks_order:
  forall l al,
    list_norepet (map fst l) ->
    alloc_blocks l = Some al ->
    forall b b' z z',
      appears_before b b' (map fst l) ->
      In (b, z) l ->
      In (b', z') l -> z > 0 -> z' > 0 ->
      Int.ltu (al b) (al b') = true \/ b = b'.
Proof.
  intros l al.
  unfold alloc_blocks, alloc_mem_aux.
  intros lnr AB b b' z z' APB I1 I2 Zpos Z'pos.
  des (alloc_mem_al tpMA l (tpMA, fun _ => 0)).
  des (zlt z0 memsize).
  inv AB. 
  exploit ab_inl; eauto.
  intros (szb' & I).
  exploit ab_first_in; eauto.
  intros (szb & J).
  assert (o8 : 0 <= tpMA).
  unfold tpMA; lia.
  generalize (norepet_eq l lnr _ _ _ I I2).
  generalize (norepet_eq l lnr _ _ _ J I1). intros; subst.
  generalize (alloc_mem_al_order _ tpMA_pos _ _ _ _ _ Heqp o8 lnr _ _ APB _ _ J I Zpos Z'pos).
  generalize (compat_alloc_range_al' _ tpMA_pos _ lnr _ _ _ _ o8 Heqp _ _ I).
  generalize (compat_alloc_range_al' _ tpMA_pos _ lnr _ _ _ _ o8 Heqp _ _ J).
  generalize (Z.le_max_l 0 z').
  intros M0 [X Y] [A B] C.
  destruct C as [C|C]; auto.
  unfold Int.ltu.
  rewrite ! Int.unsigned_repr by omega.
  destr.
Qed.

End AllocBlocks.

End MaxAlign.