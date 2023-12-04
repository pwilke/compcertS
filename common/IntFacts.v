Require Import Coqlib.
Require Import Axioms.
Require Import Integers.
Require Import Floats.
Require Import Psatz.


Lemma nat_ge_le:
  forall n m,
    (m >= n)%nat ->
    (n <= m)%nat.
Proof.
  intros; lia.
Qed.


Ltac assert_val val :=
  match goal with
      |- context [if ?a then _ else _] => let x:= fresh in assert (x: a=val);[|rewrite x in *; clear x]
  end.


Ltac destr_no_dep :=
  destr; repeat match goal with
                    H: _ = left _ |- _ => clear H
                  | H: _ = right _ |- _ => clear H
                end.

Lemma shl_zero_l:
  forall i,
    Int.shl Int.zero i = Int.zero.
Proof.
  intros.
  apply Int.same_bits_eq.
  intros.
  rewrite Int.bits_shl; simpl; auto.
  repeat rewrite Int.bits_zero. 
  destr.
Qed.

Ltac solve_int :=
  repeat 
    match goal with
      | |- context [Int.shl _ (Int.repr 0)] => rewrite Int.shl_zero
      | |- context [Int.shl Int.zero _] => rewrite shl_zero_l
      | |- context [Int.add Int.zero _] => rewrite Int.add_zero_l
      | |- context [Int.shru (Int.shl ?i (Int.repr ?n)) (Int.repr ?n)] =>
        change n with (Int.zwordsize - (Int.zwordsize - n));
          rewrite <- Int.zero_ext_shru_shl by (unfold Int.zwordsize; simpl; lia)
      | |- context [Int.shru (Int.shl ?i (Int.repr ?n)) (Int.repr ?m)] =>
        change (Int.shru (Int.shl i (Int.repr n)) (Int.repr m)) with
        (Int.shru (Int.shl i (Int.repr (Int.zwordsize - (Int.zwordsize - n)))) (Int.add (Int.repr n) (Int.sub (Int.repr m) (Int.repr n))));
          rewrite <- Int.shru_shru by (vm_compute; auto); 
          rewrite <- Int.zero_ext_shru_shl by (unfold Int.zwordsize; simpl; lia)
      | |- context [Int.sub (Int.repr ?i) (Int.repr ?j)] =>
        change (Int.sub (Int.repr i) (Int.repr j)) with (Int.repr (i - j)); simpl
      | |- context [Int.add (Int.repr ?i) (Int.repr ?j)] =>
        change (Int.add (Int.repr i) (Int.repr j)) with (Int.repr (i + j)); simpl
      | |- context [Int.testbit (Int.add _ _) _] => rewrite Int.add_is_or; simpl; auto; try lia
      | |- context [Int.testbit (Int.and _ _) _] => rewrite Int.bits_and; simpl; auto
      | |- context [Int.testbit (Int.or _ _) _] => rewrite Int.bits_or; simpl; auto; try lia; [idtac]
      | |- context [Int.testbit (Int.shl _ _) _] => rewrite Int.bits_shl; simpl; auto; try lia;  [idtac]
      | |- context [Int.testbit (Int.shru _ _) _] => rewrite Int.bits_shru; simpl; auto; try lia; [idtac]
      | |- context [Int.testbit (Int.zero_ext _ _) _] => rewrite Int.bits_zero_ext; simpl
      | |- context [Int.testbit (Int.sign_ext _ _) _] => f_equal; apply Int.sign_ext_equal_if_zero_equal; try lia
      | H: context[Int.unsigned (Int.repr _)]|- _ => rewrite Int.unsigned_repr in H by (unfold Int.max_unsigned; simpl; lia)
      | |- context[Int.unsigned (Int.repr _)] => rewrite Int.unsigned_repr by (unfold Int.max_unsigned; simpl; lia)
      | |- context [_ || false] => rewrite orb_false_r
      | |- context [_ && false] => rewrite andb_false_r
      | |- context [Int.testbit Int.zero ?i] => rewrite Int.bits_zero
      | |- context [?n - ?i + ?i] => replace (n - i + i) with n by (rewrite Z.sub_simpl_r; auto)
      | |- Int.testbit ?e ?i = Int.testbit ?e ?j => f_equal; lia
      | |- @eq int _ _ => apply Int.same_bits_eq; simpl; intros
      | |- _ => destr; repeat match goal with
                                | H: _ = left _ |- _ => clear H
                                | H: _ = right _ |- _ => clear H
                              end; try lia
      | |- _ => progress simpl
    end.

Lemma shl_zero_r_64:
  forall i,
    Int64.shl' i (Int.repr 0) = i.
Proof.
  intros.
  apply Int64.same_bits_eq; intros; auto.
  rewrite Int64.bits_shl'; simpl; auto; try lia.
  rewrite Int.unsigned_repr by (unfold Int.max_unsigned; simpl; lia).
  destr; try lia.
  f_equal; lia.
Qed.

Lemma shl_zero_l_64:
  forall i,
    Int64.shl' Int64.zero i = Int64.zero.
Proof.
  intros.
  apply Int64.same_bits_eq; intros; auto.
  rewrite Int64.bits_shl'; simpl; auto; try lia.
  repeat rewrite Int64.bits_zero.
  destr; try lia.
Qed.

Lemma shru'_shru:
  forall l i,
    0 <= Int.unsigned i <= 64 ->
    Int64.shru' l i = Int64.shru l (Int64.repr (Int.unsigned i)).
Proof.
  intros.
  unfold Int64.shru', Int64.shru.
  f_equal.
  f_equal.
  rewrite Int64.unsigned_repr; auto.
  unfold Int64.max_unsigned; simpl; lia.
Qed.

Lemma shl'_shl:
  forall l i,
    0 <= Int.unsigned i <= 64 ->
    Int64.shl' l i = Int64.shl l (Int64.repr (Int.unsigned i)).
Proof.
  intros.
  unfold Int64.shl', Int64.shl.
  f_equal.
  f_equal.
  rewrite Int64.unsigned_repr; auto.
  unfold Int64.max_unsigned; simpl; lia.
Qed.

Ltac solve_long :=
  repeat 
    match goal with
      | |- context [Int64.shl' _ (Int.repr 0)] => rewrite shl_zero_r_64
      | |- context [Int64.shl' Int64.zero _] => rewrite shl_zero_l_64
      | |- context [Int64.add Int64.zero _] => rewrite Int64.add_zero_l
      | |- context [Int64.mul Int64.zero _] => rewrite Int64.mul_commut; rewrite Int64.mul_zero
      | |- context [Int64.shru (Int64.shl ?i (Int64.repr ?n)) (Int64.repr ?n)] =>
        change n with (Int64.zwordsize - (Int64.zwordsize - n));
          rewrite <- Int64.zero_ext_shru_shl by (unfold Int64.zwordsize; simpl; lia)
      | |- context [Int64.shru (Int64.shl ?i (Int64.repr ?n)) (Int64.repr ?m)] =>
        change (Int64.shru (Int64.shl i (Int64.repr n)) (Int64.repr m)) with
        (Int64.shru (Int64.shl i (Int64.repr (Int64.zwordsize - (Int64.zwordsize - n)))) (Int64.add (Int64.repr n) (Int64.sub (Int64.repr m) (Int64.repr n))));
          rewrite <- Int64.shru_shru by (vm_compute; auto); 
          rewrite <- Int64.zero_ext_shru_shl by (unfold Int64.zwordsize; simpl; lia)
      | |- context [Int64.sub (Int64.repr ?i) (Int64.repr ?j)] =>
        change (Int64.sub (Int64.repr i) (Int64.repr j)) with (Int64.repr (i - j)); simpl
      | |- context [Int64.add (Int64.repr ?i) (Int64.repr ?j)] =>
        change (Int64.add (Int64.repr i) (Int64.repr j)) with (Int64.repr (i + j)); simpl
      (* | |- context [Int64.testbit (Int64.add _ _) _] => rewrite Int64.add_is_or; simpl; auto; try lia *)
      | |- context [Int64.testbit (Int64.and _ _) _] => rewrite Int64.bits_and; simpl; auto
      | |- context [Int64.testbit (Int64.or _ _) _] => rewrite Int64.bits_or; simpl; auto; try lia; [idtac]
      | |- context [Int64.testbit (Int64.shl _ _) _] => rewrite Int64.bits_shl; simpl; auto; try lia;  [idtac]
      | |- context [Int64.testbit (Int64.shru _ _) _] => rewrite Int64.bits_shru; simpl; auto; try lia; [idtac]
      | |- context [Int64.testbit (Int64.zero_ext _ _) _] => rewrite Int64.bits_zero_ext; simpl
      | |- context [Int64.testbit (Int64.sign_ext _ _) _] => f_equal; apply Int64.sign_ext_equal_if_zero_equal; try lia; [idtac]
      | H: context[Int64.unsigned (Int64.repr _)]|- _ => rewrite Int64.unsigned_repr in H by (unfold Int64.max_unsigned; simpl; lia)
      | |- context[Int64.unsigned (Int64.repr _)] => rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; simpl; lia)
      | H: context[Int.unsigned (Int.repr _)]|- _ => rewrite Int.unsigned_repr in H by (unfold Int.max_unsigned; simpl; lia)
      | |- context[Int.unsigned (Int.repr _)] => rewrite Int.unsigned_repr by (unfold Int.max_unsigned; simpl; lia)
      | |- context [_ || false] => rewrite orb_false_r
      | |- context [_ && false] => rewrite andb_false_r
      | |- context [Int64.testbit Int64.zero ?i] => rewrite Int64.bits_zero
      | |- context [?n - ?i + ?i] => replace (n - i + i) with n by (rewrite Z.sub_simpl_r; auto)
      | |- Int64.testbit ?e ?i = Int64.testbit ?e ?j => f_equal; lia
      | |- @eq int64 _ _ => apply Int64.same_bits_eq; simpl; intros
      | |- _ => destr; repeat match goal with
                                | H: _ = left _ |- _ => clear H
                                | H: _ = right _ |- _ => clear H
                              end; try lia
      | |- _ => progress simpl
    end.


Lemma Forall_rev:
  forall A P (l:list A),
    Forall P (rev l) ->
    Forall P l.
Proof.
  intros.
  apply Forall_forall.
  intros.
  eapply Forall_forall in H ; eauto.
  apply -> in_rev; auto.
Qed.

Lemma int_zwordsize:
  Int.zwordsize = 32.
Proof. 
  reflexivity.
Qed.

Lemma int64_zwordsize:
  Int64.zwordsize = 64.
Proof. 
  reflexivity.
Qed.

Lemma list_forall2_sym:
  forall {A} (P: A -> A -> Prop) 
         (Psym: forall a b, P a b -> P b a)
         la lb,
    list_forall2 P la lb ->
    list_forall2 P lb la.
Proof.
  intros.
  induction H.
  constructor.
  constructor; auto.
Qed.

Lemma list_forall2_rev:
  forall {A} (P:A -> A -> Prop) (l l': list A),
    list_forall2 P l l' ->
    list_forall2 P (rev l) (rev l').
Proof.
  induction l; intros.
  - inv H. simpl; constructor.
  - simpl.
    inv H.
    apply IHl in H4.
    simpl.
    apply list_forall2_app; auto.
    constructor; auto.
    constructor.
Qed.

Lemma bits_255_below:
  forall i0, 0 <= i0 < 8 -> Int.testbit (Int.repr 255) i0 = true.
Proof.
  intros.
  rewrite Int.testbit_repr; auto.
  change 255 with (two_p 8 - 1).
  rewrite Int.Ztestbit_two_p_m1; destr; lia.
  unfold Int.zwordsize, Int.wordsize, Wordsize_32.wordsize; simpl; lia.
Qed.

Lemma bits_255_above:
  forall i0, 8 <= i0 < Int.zwordsize -> Int.testbit (Int.repr 255) i0 = false.
Proof.
  intros.
  rewrite Int.testbit_repr; auto.
  change 255 with (two_p 8 - 1).
  rewrite Int.Ztestbit_two_p_m1; destr; lia.
  lia.
Qed.

Lemma bits64_255_below:
  forall i0, 0 <= i0 < 8 -> Int64.testbit (Int64.repr 255) i0 = true.
Proof.
  intros.
  rewrite Int64.testbit_repr; auto.
  change 255 with (two_p 8 - 1).
  rewrite Int64.Ztestbit_two_p_m1; destr; lia.
  unfold Int64.zwordsize, Int64.wordsize, Wordsize_32.wordsize; simpl; lia.
Qed.

Lemma bits64_255_above:
  forall i0, 8 <= i0 < Int64.zwordsize -> Int64.testbit (Int64.repr 255) i0 = false.
Proof.
  intros.
  rewrite Int64.testbit_repr; auto.
  change 255 with (two_p 8 - 1).
  rewrite Int64.Ztestbit_two_p_m1; destr; lia.
  lia.
Qed.

Lemma sign_ext_8_id:
  forall i0,
      (Int.sign_ext 8
                    (Int.add (Int.and i0 (Int.repr 255)) (Int.shl Int.zero (Int.repr 8)))) =
    (Int.sign_ext 8 i0).
Proof.
  intros.
  rewrite shl_zero_l.
  rewrite Int.add_zero.
  solve_int.
  rewrite bits_255_below; auto. ring.
Qed.

Lemma zero_ext_8_id:
  forall i0,
      (Int.zero_ext 8
                    (Int.add (Int.and i0 (Int.repr 255)) (Int.shl Int.zero (Int.repr 8)))) =
       (Int.zero_ext 8 i0).
Proof.
  intros.
  rewrite shl_zero_l.
  rewrite Int.add_zero.
  solve_int.
  rewrite bits_255_below; auto. ring.
Qed.

Lemma sign_ext_16_id:
  forall i0,
      (Int.sign_ext 16
                    (Int.add (Int.and i0 (Int.repr 255))
                             (Int.shl
                                (Int.add (Int.and (Int.shru i0 (Int.repr 8)) (Int.repr 255))
                                         (Int.shl Int.zero (Int.repr 8))) (Int.repr 8)))) =
      (Int.sign_ext 16 i0).
Proof.
  intros.
  solve_int.
  rewrite bits_255_below; try lia; ring.
  rewrite bits_255_above; try lia.
  rewrite bits_255_below; try lia.
  rewrite <- andb_orb_distrib_r.
  ring.
  rewrite bits_255_above; try lia.
  ring.
Qed.

Ltac unfsize :=
  change Int.zwordsize with 32 in *; change Int64.zwordsize with 64 in *;
  change Int.max_unsigned with 4294967295 in *;
  change Int64.max_unsigned with 18446744073709551615 in *;
  change Int.modulus with 4294967296 in *;
  change Int64.max_unsigned with 18446744073709551616 in *.

Lemma sign_ext_16_id_long:
  forall i,
    Int.sign_ext 16
                 (Int64.loword
                    (Int64.add (Int64.and (Int64.repr (Int.unsigned i)) (Int64.repr 255))
                               (Int64.shl'
                                  (Int64.add
                                     (Int64.and
                                        (Int64.shru' (Int64.repr (Int.unsigned i)) (Int.repr 8))
                                        (Int64.repr 255)) (Int64.shl' Int64.zero (Int.repr 8)))
                                  (Int.repr 8)))) = Int.sign_ext 16 i.
Proof.
  intros.
  solve_int.
  solve_long.
  rewrite Int64.bits_loword; auto.
  rewrite Int64.add_is_or; auto;
  solve_long; unfsize; try lia.
  - rewrite Int64.bits_or; unfsize; try lia; auto.
    solve_long; unfsize; try lia.
    rewrite shl'_shl by (vm_compute; intuition congruence).
    rewrite shru'_shru by (vm_compute; intuition congruence).
    solve_long.
    rewrite Int64.add_is_or; auto;
    solve_long; unfsize; try lia.
    rewrite Int64.bits_shl; unfsize; try lia; auto.
    destr.
    + solve_long.
      rewrite bits64_255_below; auto.
      rewrite Int64.testbit_repr; unfsize; try lia.
      rewrite <- Int.testbit_repr; auto.
      rewrite Int.repr_unsigned; auto. ring.
    + solve_long; unfsize; try lia.
      rewrite Int64.bits_or; unfsize; try lia. 
      solve_long; unfsize; try lia.
      rewrite bits64_255_above; unfsize; try lia.
      rewrite andb_false_r. rewrite orb_false_l.
      rewrite Int64.bits_shru; unfsize; try lia.
      solve_long.
      rewrite bits64_255_below; unfsize; try lia.
      rewrite Int64.testbit_repr; unfsize; try lia.
      rewrite <- Int.testbit_repr; auto.
      rewrite Int.repr_unsigned; auto. ring.
  - rewrite shl'_shl by (vm_compute; intuition congruence).
    rewrite shru'_shru by (vm_compute; intuition congruence).
    solve_long.
    rewrite Int64.add_is_or; auto;
    solve_long; unfsize; try lia.
    rewrite Int64.bits_or; unfsize; try lia. 
    solve_long; unfsize; try lia.
    rewrite bits64_255_above; unfsize; try lia.
    rewrite andb_false_r. rewrite andb_false_l. auto.
Qed.

Lemma zero_ext_16_id_long:
  forall i,
    Int.zero_ext 16
      (Int64.loword
         (Int64.add
            (Int64.and (Int64.repr (Int.unsigned i)) (Int64.repr 255))
            (Int64.shl'
               (Int64.add
                  (Int64.and
                     (Int64.shru' (Int64.repr (Int.unsigned i)) (Int.repr 8))
                     (Int64.repr 255)) (Int64.shl' Int64.zero (Int.repr 8)))
               (Int.repr 8)))) = Int.zero_ext 16 i.
Proof.
  intros.
  solve_int. 
  solve_long.
  rewrite Int64.bits_loword; auto.
  rewrite Int64.add_is_or; auto;
  solve_long; unfsize; try lia.
  - rewrite Int64.bits_or; unfsize; try lia; auto.
    solve_long; unfsize; try lia.
    rewrite shl'_shl by (vm_compute; intuition congruence).
    rewrite shru'_shru by (vm_compute; intuition congruence).
    solve_long.
    rewrite Int64.add_is_or; auto;
    solve_long; unfsize; try lia.
    rewrite Int64.bits_shl; unfsize; try lia; auto.
    destr.
    + solve_long.
      rewrite bits64_255_below; auto.
      rewrite Int64.testbit_repr; unfsize; try lia.
      rewrite <- Int.testbit_repr; auto.
      rewrite Int.repr_unsigned; auto. ring.
    + solve_long; unfsize; try lia.
      rewrite Int64.bits_or; unfsize; try lia. 
      solve_long; unfsize; try lia.
      rewrite bits64_255_above; unfsize; try lia.
      rewrite andb_false_r. rewrite orb_false_l.
      rewrite Int64.bits_shru; unfsize; try lia.
      solve_long.
      rewrite bits64_255_below; unfsize; try lia.
      rewrite Int64.testbit_repr; unfsize; try lia.
      rewrite <- Int.testbit_repr; auto.
      rewrite Int.repr_unsigned; auto. ring.
  - rewrite shl'_shl by (vm_compute; intuition congruence).
    rewrite shru'_shru by (vm_compute; intuition congruence).
    solve_long.
    rewrite Int64.add_is_or; auto;
    solve_long; unfsize; try lia.
    rewrite Int64.bits_or; unfsize; try lia. 
    solve_long; unfsize; try lia.
    rewrite bits64_255_above; unfsize; try lia.
    rewrite andb_false_r. rewrite andb_false_l. auto.
Qed.

Lemma zero_ext_16_id:
  forall i0,
      (Int.zero_ext 16
                    (Int.add (Int.and i0 (Int.repr 255))
                             (Int.shl
                                (Int.add (Int.and (Int.shru i0 (Int.repr 8)) (Int.repr 255))
                                         (Int.shl Int.zero (Int.repr 8))) (Int.repr 8)))) =
      (Int.zero_ext 16 i0).
Proof.
  intros.
  solve_int.
  rewrite bits_255_below; try lia; ring.
  rewrite bits_255_above; try lia.
  rewrite bits_255_below; try lia.
  rewrite <- andb_orb_distrib_r.
  ring.
  rewrite bits_255_above; try lia.
  ring.
Qed.

Ltac sl := solve_long; unfsize; try lia.

Lemma int32_decomp:
  forall i,
    Int64.loword
        (Int64.add (Int64.and (Int64.repr (Int.unsigned i)) (Int64.repr 255))
           (Int64.shl'
              (Int64.add
                 (Int64.and
                    (Int64.shru' (Int64.repr (Int.unsigned i)) (Int.repr 8))
                    (Int64.repr 255))
                 (Int64.shl'
                    (Int64.add
                       (Int64.and
                          (Int64.shru'
                             (Int64.shru' (Int64.repr (Int.unsigned i))
                                (Int.repr 8)) (Int.repr 8)) 
                          (Int64.repr 255))
                       (Int64.shl'
                          (Int64.add
                             (Int64.and
                                (Int64.shru'
                                   (Int64.shru'
                                      (Int64.shru'
                                         (Int64.repr (Int.unsigned i))
                                         (Int.repr 8)) 
                                      (Int.repr 8)) 
                                   (Int.repr 8)) (Int64.repr 255))
                             (Int64.shl' Int64.zero (Int.repr 8)))
                          (Int.repr 8))) (Int.repr 8))) 
              (Int.repr 8))) = Int.sign_ext 32 i.
Proof.
  intros.
  rewrite Int.sign_ext_above; sl.
  solve_int.
  sl. 
  rewrite Int64.bits_loword; auto.
  rewrite Int64.add_is_or; auto; sl.
  - rewrite Int64.bits_or; sl.
    rewrite ! shl'_shl by (vm_compute; intuition congruence).
    rewrite ! shru'_shru by (vm_compute; intuition congruence).
    sl.
    rewrite Int64.add_is_or; auto;
    sl.
    rewrite Int64.bits_shl;sl.  
    + rewrite bits64_255_below; auto.
      rewrite Int64.testbit_repr; unfsize; try lia.
      rewrite <- Int.testbit_repr; auto.
      rewrite Int.repr_unsigned; auto. ring.
    + rewrite Int64.bits_or; sl. 
      rewrite bits64_255_above; sl.
      rewrite Int64.bits_shru; sl. 
      * rewrite bits64_255_below; try lia.
        rewrite Int64.testbit_repr; unfsize; try lia.
        rewrite <- Int.testbit_repr; auto.
        rewrite Int.repr_unsigned; auto. ring.
      * rewrite bits64_255_above; unfsize; try lia.
        rewrite andb_false_r. rewrite orb_false_l.
        rewrite Int64.add_is_or; sl. 
        rewrite Int64.bits_or; sl. 
        rewrite Int64.bits_shru; sl.
        {
          rewrite bits64_255_below; try lia.
          rewrite Int64.testbit_repr; unfsize; try lia.
          rewrite <- Int.testbit_repr; auto.
          rewrite Int.repr_unsigned; auto. ring.
        }
        {
          rewrite bits64_255_above; sl.
          rewrite Int64.add_is_or; sl. 
          rewrite Int64.bits_or; sl. 
          rewrite Int64.bits_shru; sl.
          rewrite bits64_255_below; try lia.
          rewrite Int64.testbit_repr; unfsize; try lia.
          rewrite <- Int.testbit_repr; auto.
          rewrite Int.repr_unsigned; auto. ring.
        }
        {
          rewrite bits64_255_above; sl.
        }
    + rewrite bits64_255_above; sl.
  - rewrite ! shl'_shl by (vm_compute; intuition congruence).
    rewrite ! shru'_shru by (vm_compute; intuition congruence).
    sl. 
    repeat rewrite Int64.add_is_or; auto; sl.
    rewrite bits64_255_above; sl.
    rewrite bits64_255_above; sl.
    rewrite bits64_255_above; sl.
    rewrite bits64_255_above; sl.
    rewrite bits64_255_above; sl.
Qed.

Lemma add_and_shl_rew:
  forall i i' j,
    0 <= j < Int64.zwordsize ->
    Int64.testbit 
      (Int64.add (Int64.and i (Int64.repr 255)) (Int64.shl i' (Int64.repr 8)))
      j = if zlt j 8 then Int64.testbit i j
          else Int64.testbit i' ( j - 8 ).
Proof.
  intros.
  rewrite Int64.add_is_or.
  rewrite Int64.bits_or; auto.
  rewrite Int64.bits_and; auto.
  rewrite Int64.bits_shl; auto.
  change (Int64.unsigned (Int64.repr 8)) with 8.
  destr.
  rewrite orb_false_r.
  rewrite Int64.testbit_repr; auto.
  change 255 with (two_p 8 - 1).
  rewrite Int64.Ztestbit_two_p_m1; auto; try lia.
  destr. ring.
  rewrite Int64.testbit_repr; auto.
  change 255 with (two_p 8 - 1).
  rewrite Int.Ztestbit_two_p_m1; destr; try lia.
  rewrite andb_false_r.
  rewrite orb_false_l; auto.
  solve_long.
  rewrite Int64.testbit_repr; auto.
  change 255 with (two_p 8 - 1).
  rewrite Int.Ztestbit_two_p_m1; destr; try lia.
  ring.
Qed.

Lemma int64_decomp:
  forall i0,
    Int64.add (Int64.and i0 (Int64.repr 255))
              (Int64.shl
                 (Int64.add
                    (Int64.and (Int64.shru i0 (Int64.repr 8)) (Int64.repr 255))
                    (Int64.shl
                       (Int64.add
                          (Int64.and (Int64.shru i0 (Int64.repr 16)) (Int64.repr 255))
                          (Int64.shl
                             (Int64.add
                                (Int64.and (Int64.shru i0 (Int64.repr 24))
                                           (Int64.repr 255))
                                (Int64.shl
                                   (Int64.add
                                      (Int64.and (Int64.shru i0 (Int64.repr 32))
                                                 (Int64.repr 255))
                                      (Int64.shl
                                         (Int64.add
                                            (Int64.and (Int64.shru i0 (Int64.repr 40))
                                                       (Int64.repr 255))
                                            (Int64.shl
                                               (Int64.add
                                                  (Int64.and
                                                     (Int64.shru i0 (Int64.repr 48))
                                                     (Int64.repr 255))
                                                  (Int64.shl
                                                     (Int64.add
                                                        (Int64.and
                                                           (Int64.shru i0
                                                                       (Int64.repr 56))
                                                           (Int64.repr 255))
                                                        (Int64.shl Int64.zero
                                                                   (Int64.repr 8)))
                                                     (Int64.repr 8))) 
                                               (Int64.repr 8))) 
                                         (Int64.repr 8))) (Int64.repr 8)))
                             (Int64.repr 8))) (Int64.repr 8))) 
                 (Int64.repr 8)) = i0.
Proof.
  intros.
  solve_long.
  repeat (rewrite add_and_shl_rew; auto; try lia; [idtac]; destr);
    try (rewrite Int64.bits_shru; auto; try lia; 
         repeat rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; simpl; lia); destr; try lia; f_equal; lia).
  exfalso.
  rewrite int64_zwordsize in *.
  lia.
Qed.

Lemma alignment_inj:
  forall i i0 i1 i2
         (A : Int.and i (Int.not (Int.repr (two_power_nat i0 - 1))) = i)
         (B : Int.and (Int.not (Int.repr (two_power_nat i0 - 1)))
                      (Int.not (Int.repr (two_power_nat i1 - 1))) =
              Int.not (Int.repr (two_power_nat i0 - 1)))
         (C : Int.and i2 (Int.not (Int.repr (two_power_nat i1 - 1))) = i2),
   Int.and (Int.add i i2) (Int.not (Int.repr (two_power_nat i1 - 1))) =
   Int.add i i2.
Proof.
  intros.
  assert (AND_ZEROS: forall i1 i,
                       Int.and i (Int.not (Int.repr (two_power_nat i1 - 1))) = i <->
                       (forall j, 0 <= j < Z.of_nat i1 -> 
                                  Int.testbit i j = false)).
  {
    clear; split; intros.
    - apply (f_equal (fun x => Int.testbit x j)) in H.
      destruct (zlt j Int.zwordsize).
      + rewrite Int.bits_and in H by lia.
        rewrite Int.bits_not in H by lia.
        rewrite Int.testbit_repr in H by lia.
        rewrite two_power_nat_two_p in H.
        rewrite Int.Ztestbit_two_p_m1 in H by lia.
        revert H; destr.
        des (Int.testbit i j).
      + rewrite Int.bits_above; auto.
    - apply Int.same_bits_eq; intros.
      rewrite Int.bits_and; auto.
      rewrite Int.bits_not; auto.
      rewrite Int.testbit_repr; auto.
      rewrite two_power_nat_two_p.
      rewrite Int.Ztestbit_two_p_m1; try lia.
      destr.
      rewrite H; auto.
      ring.
  }
  rewrite AND_ZEROS in A.
  rewrite AND_ZEROS in B.
  rewrite AND_ZEROS in C.
  rewrite AND_ZEROS.
  intros.
  generalize (B j H).
  intros.
  destruct (zlt j Int.zwordsize); try (rewrite Int.bits_above by lia; auto).
  rewrite Int.bits_not in H0 by lia.
  rewrite Int.testbit_repr in H0 by lia.
  rewrite two_power_nat_two_p in H0.
  rewrite Int.Ztestbit_two_p_m1 in H0 by lia.
  revert H0; destr.
  unfold Int.add.
  rewrite Int.testbit_repr by lia.
  rewrite Int.Z_add_is_or; try lia.
  rewrite <- ! Int.testbit_repr by lia.
  rewrite ! Int.repr_unsigned.
  rewrite C; auto.
  rewrite A; auto.
  intros.
  rewrite <- ! Int.testbit_repr by lia.
  rewrite ! Int.repr_unsigned.
  rewrite C; auto. ring.
  lia. 
Qed.


Ltac elim_div :=
  unfold Zdiv, Zmod in *;
  repeat
    match goal with
      |  H : context[ Zdiv_eucl ?X ?Y ] |-  _ =>
         generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
      |  |-  context[ Zdiv_eucl ?X ?Y ] =>
         generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
    end; unfold Remainder.

Ltac unf_modulus :=
  change (Int.modulus) with 4294967296 in *.


Lemma int_add_diff_range_plus:
  forall o z o' z0 i,
    o + z <> o' + z0 ->
    z0 >= 0 -> z >= 0 ->
    0 <= o' + z0 <= Int.modulus - 1 ->
    0 <= o + z <= Int.modulus - 1 ->
    (( i + z) mod Int.modulus + o) mod Int.modulus <>
    (( i + z0) mod Int.modulus + o') mod Int.modulus.
Proof.
  intros.
  rewrite !Zplus_mod_idemp_l.
  revert H. revert H2 H3.
  replace (i+z+o) with (i + (o + z)) by lia.
  replace (i+z0+o') with (i + (o' + z0)) by lia.
  generalize (o + z) (o' + z0). clear.
  intros.
  intro.
  unf_modulus.
  elim_div. lia.
Qed.


Lemma int_add_rew:
  forall a b,
    Int.repr (Int.unsigned a + Int.unsigned b) = Int.add a b.
Proof.
  unfold Int.add; auto.
Qed.

Lemma two_p_abs:
  forall n n0,
    (n >= n0)%nat ->
    Int.and (Int.not (Int.repr (two_power_nat n - 1)))
            (Int.not (Int.repr (two_power_nat n0 - 1))) =
    Int.not (Int.repr (two_power_nat n - 1)).
Proof.
  intros.
  rewrite <- ! Int.not_or_and_not in *.
  f_equal.
  rewrite ! two_power_nat_two_p.
  solve_int.
  rewrite ! Int.testbit_repr; auto.
  rewrite ! Int.Ztestbit_two_p_m1; auto; try lia.
  apply inj_ge in H.
  repeat destr; lia.
Qed.


Lemma ge_trans:
 ( forall (a b c: nat),
    a >= b -> b >= c -> a >= c)%nat.
Proof.
  intros. lia.
Qed.


Lemma odd_not_2_divides:
  forall z,
    Z.odd z = true ->
    ~ (2 | z).
Proof.
  intros.
  destruct 1. subst.
  unfold Z.odd in H.
  destruct x; simpl in *; try congruence;
  destruct p; simpl in *; try congruence.
Qed.


Lemma pos2nat_not_zero:
  forall b, Pos.to_nat b <> O.
Proof.
  clear.
  intros. lia.
Qed.

Remark decompose_cmpl_eq_zero:
  forall h l,
  Int64.eq (Int64.ofwords h l) Int64.zero = Int.eq (Int.or h l) Int.zero.
Proof.
  intros. 
  assert (Int64.zwordsize = Int.zwordsize * 2) by reflexivity.
  predSpec Int64.eq Int64.eq_spec (Int64.ofwords h l) Int64.zero.
  replace (Int.or h l) with Int.zero. rewrite Int.eq_true. auto.
  apply Int.same_bits_eq; intros. 
  rewrite Int.bits_zero. rewrite Int.bits_or by auto. 
  symmetry. apply orb_false_intro. 
  transitivity (Int64.testbit (Int64.ofwords h l) (i + Int.zwordsize)).
  rewrite Int64.bits_ofwords by lia. rewrite zlt_false by lia. f_equal; lia.
  rewrite H0. apply Int64.bits_zero. 
  transitivity (Int64.testbit (Int64.ofwords h l) i).
  rewrite Int64.bits_ofwords by lia. rewrite zlt_true by lia. auto. 
  rewrite H0. apply Int64.bits_zero.
  symmetry. apply Int.eq_false. red; intros; elim H0. 
  apply Int64.same_bits_eq; intros. 
  rewrite Int64.bits_zero. rewrite Int64.bits_ofwords by auto. 
  destruct (zlt i Int.zwordsize).
  assert (Int.testbit (Int.or h l) i = false) by (rewrite H1; apply Int.bits_zero). 
  rewrite Int.bits_or in H3 by lia. exploit orb_false_elim; eauto. tauto. 
  assert (Int.testbit (Int.or h l) (i - Int.zwordsize) = false) by (rewrite H1; apply Int.bits_zero). 
  rewrite Int.bits_or in H3 by lia. exploit orb_false_elim; eauto. tauto.
Qed.


Remark int64_eq_xor:
  forall p q, Int64.eq p q = Int64.eq (Int64.xor p q) Int64.zero.
Proof.
  intros.
  predSpec Int64.eq Int64.eq_spec p q.
  subst q. rewrite Int64.xor_idem. rewrite Int64.eq_true. auto.
  predSpec Int64.eq Int64.eq_spec (Int64.xor p q) Int64.zero.
  elim H. apply Int64.xor_zero_equal; auto.
  auto.
Qed.


Lemma int64_ltu_rew:
  forall a b,
    Int64.ltu a b = Int64.ltu
                      (Int64.ofwords (Int64.hiword a) (Int64.loword a))
                      (Int64.ofwords (Int64.hiword b) (Int64.loword b)).
Proof.
  intros.
  rewrite ! Int64.ofwords_recompose; auto.
Qed.


Lemma int64_lt_rew:
  forall a b,
    Int64.lt a b = Int64.lt
                      (Int64.ofwords (Int64.hiword a) (Int64.loword a))
                      (Int64.ofwords (Int64.hiword b) (Int64.loword b)).
Proof.
  intros.
  rewrite ! Int64.ofwords_recompose; auto.
Qed.


Remark decompose_cmpl_lt_zero:
  forall h l,
  Int64.lt (Int64.ofwords h l) Int64.zero = Int.lt h Int.zero.
Proof.
  intros. 
  generalize (Int64.shru_lt_zero (Int64.ofwords h l)).
  change (Int64.shru (Int64.ofwords h l) (Int64.repr (Int64.zwordsize - 1)))
    with (Int64.shru' (Int64.ofwords h l) (Int.repr 63)).
  rewrite Int64.decompose_shru_2. 
  change (Int.sub (Int.repr 63) Int.iwordsize)
    with (Int.repr (Int.zwordsize - 1)). 
  rewrite Int.shru_lt_zero. 
  destruct (Int64.lt (Int64.ofwords h l) Int64.zero); destruct (Int.lt h Int.zero); auto; intros.
  elim Int64.one_not_zero. auto. 
  elim Int64.one_not_zero. auto.
  vm_compute. intuition congruence.
Qed.


Lemma two_p_inj_div:
  forall n m,
    0 <= n <= m ->
    Z.divide (two_p n) (two_p m).
Proof.
  intros.
  unfold Z.divide.
  exists (two_p (m-n)).
  rewrite <- two_p_is_exp by lia.
  f_equal. lia.
Qed.
