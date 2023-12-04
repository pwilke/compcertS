Require Import Coqlib ZArith Psatz PpsimplZ IntFacts.

Open Scope Z_scope.

Lemma align_plus:
  forall al z,
    al = 1 \/ al = 2 \/ al = 4 \/ al = 8 ->
    align (align z al) 8 = align z 8.
Proof.
  intros al z.
  unfold align. intros.
  elim_div. assert (al <> 0) by lia.
  intuition subst; lia.
Qed.

Lemma align_align:
  forall z a (apos: a > 0),
    align (align z a) a = align z a.
Proof.
  intros.
  generalize (align_divides z a apos).
  intro A; destruct A as (x & A).
  rewrite A.
  unfold align.
  rewrite <- Z.div_unique with (q:=x) (r:= a-1).
  auto.
  left; omega.  
  rewrite Z.mul_comm. omega.
Qed.

Lemma align_ge1:
  forall sz al,
    al > 0 ->
    exists b, 0 <= b < al /\
         align sz al = sz + b /\ 
         b = (al - 1 - (sz - 1 - al * ((sz - 1) / al))).
Proof.
  intros.
  generalize (align_le sz al H).
  destruct (align_divides sz al H).
  rewrite H0.
  intros. 
  unfold align in H0.
  rewrite <- H0.
  replace ((sz+al-1)/al) with (1+ ((sz-1)/al)).
  {
    replace ((1+ ((sz-1)/al))*al) with (al + (sz -1)/al *al).
    {
      rewrite Z.mul_comm.
      replace (al * ((sz - 1) / al)) with
      (al * ((sz - 1) / al) + (sz-1) mod al - (sz-1) mod al) by omega.
      rewrite <- Z.div_mod by omega.
      rewrite Z.mod_eq by omega.
      exists (al - 1 - (sz - 1 - al * ((sz - 1) / al))).
      split; try omega.
      {
        elim_div. assert (al <> 0) by omega. intuition.
      }
    }
    rewrite Z.mul_add_distr_r. omega.
  }
  {
    replace (sz + al - 1) with ((sz -1) + 1*al) by omega.
    rewrite Z_div_plus_full by omega.
    omega.
  }
Qed.

Lemma align_add:
  forall al sz sz',
    al > 0 ->
    0 <= sz <= sz' ->
    align sz al <= align sz' al.
Proof.
  intros.
  generalize (align_ge1 sz al H)
             (align_ge1 sz' al H).
  intros [b [A [B C]]] [c [D [E F]]].
  destruct (zlt (sz'-sz) al); try intuition omega.
  assert (exists d, 0 <= d < al /\ sz' = sz + d).
  {
    clear - H0 H l.
    exists (sz'-sz). intuition try omega.
  }
  destruct H1 as [d [ENC EQ]]. rewrite EQ in *.
  clear EQ.
  rewrite B; rewrite E.
  cut (      al * ((sz - 1) / al) <=
             (   al * ((sz + d - 1) / al))); intros; try omega.  
  apply Z.mul_le_mono_nonneg_l; try  omega.
  apply Z.div_le_mono; try omega.
Qed.


Lemma align_distr:
  forall al (AlPos: al > 0) z z1,
    align z al + align z1 al = align (align z al + z1) al.
Proof.
  intros.
  generalize (align_divides z al AlPos).
  generalize (align z al).
  unfold align.  intros z0 [x EQ]. subst.
  rewrite <- Z.mul_add_distr_r.
  f_equal. replace (x*al + z1 + al - 1) with ((x*al) + (z1 + al - 1)) by lia.
  rewrite BigNumPrelude.Z_div_plus_l. auto. lia.
Qed.

Lemma align_refl:
  forall al (AlPos: al > 0),
    align al al = al.
Proof.
  intros.
  unfold align. elim_div.
  intuition.
  assert (al * (2 - z) - 1 = z0) by lia.
  subst.
  assert (al * (2-z) <= al) by lia. clear H2.
  assert (al * (1 - z) <= 0). lia.
  assert (1 - z <= 0). apply Z.le_mul_0 in H2.
  destr.
  assert (z >= 1) by lia.
  destruct (zlt z 2).
  assert (z = 1) by lia. subst; lia.
  assert (2 - z <= 0) by lia.
  apply Z.mul_le_mono_nonneg_l with (p:=al) in H5; try lia.
Qed.

Lemma align_0:
  forall al, al > 0 -> 
        align 0 al = 0.
Proof.
  intros.
  unfold align.
  elim_div. intuition.
  assert (al * (1 - z) - 1 = z0) by lia.
  subst. clear H0.
  assert (al * (1 - z) <= al * 1) by lia.
  assert (0 <= al * (1 - (1-z))) by lia.
  apply Z.mul_nonneg_cancel_l in H1; try lia.
  assert (z >= 0) by lia.
  clear H1 H0 H3.
  destruct (zlt z 1). assert (z = 0). lia. subst. lia.
  assert (1 - z <= 0) by lia.
  apply Z.mul_le_mono_nonneg_l with (p:=al) in H0; try lia.
Qed.
