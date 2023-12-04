(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*          with contributions from Andrew Appel, Rob Dockins,         *)
(*          and Gordon Stewart (Princeton University)                  *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This file develops the memory model that is used in the dynamic
  semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

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
Require Import Alloc Align.
Require Import Permutation.
Require Import ExprEval.
Require Export Memperm.

Parameter MA : nat.
Hypothesis MA_bound: (3 <= MA <= 12)%nat.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Local Notation "a # b" := (PMap.get b a) (at level 1).

Lemma align_le_two_p:
  forall al al' (AlGt: (al <= al')%nat) x,
    align (align x (two_power_nat al)) (two_power_nat al') = align x (two_power_nat al').
Proof.
  intros.
  unfold align.
  elim_div.
  generalize (two_power_nat_pos al) (two_power_nat_pos al'). intuition.
  assert (EQ: two_power_nat al' = two_power_nat al * two_power_nat (al' - al)).
  rewrite ! two_power_nat_two_p. rewrite <- two_p_is_exp; try lia.
  f_equal. lia.
  generalize (two_power_nat_pos (al' - al)).
  rewrite EQ in *. clear EQ.
  generalize dependent (two_power_nat (al' - al)). intros.
  assert (x = two_power_nat al * z1 + z2 - two_power_nat al + 1) by lia. subst.
  clear H2.
  assert (z0 = z1 * two_power_nat al + two_power_nat al * z5 - 1 - two_power_nat al * z5 * z) by lia.
  subst. clear H3.
  assert (two_power_nat al * z1 + z2 - two_power_nat al + 1 +
          two_power_nat al * z5 - 1 - two_power_nat al * z5 * z3 = z4) by lia. clear H1. subst.
  generalize dependent (two_power_nat al). intros.
  f_equal.
  remember (z1 - z5 * z3 - 1) as V1.
  assert (V1 = 0 \/ V1 < 0 \/ V1 > 0) by lia.
  intuition ; try nia.  
Qed.


Module Mem <: MEM.

Definition perm_order' (po: option permission) (p: permission) := 
  match po with
  | Some p' => perm_order p' p
  | None => False
 end.

Definition perm_order'' (po1 po2: option permission) := 
  match po1, po2 with
  | Some p1, Some p2 => perm_order p1 p2
  | _, None => True
  | None, Some _ => False
  end.

Inductive msz := M31 | M32.

Definition comp_size q :=
  match q with
    M31 => Int.max_unsigned - two_power_nat MA
  | M32 => Int.max_unsigned
  end.


Definition __szmem := comp_size M31.

Lemma tpMA_pos:
  two_power_nat MA > 0.
Proof.
  apply two_power_nat_pos.
Qed.


Definition box_span (z:Z) :=
  Z.to_nat ((z - 1) / two_power_nat MA + 1).
Lemma s32_ma:
  Int.max_unsigned = two_power_nat MA * (two_power_nat (32 - MA)) - 1.
Proof.
  unfold Int.max_unsigned. f_equal.
  rewrite ! two_power_nat_two_p.
  rewrite <- two_p_is_exp by lia.
  rewrite <- Nat2Z.inj_add.
  rewrite <- two_power_nat_two_p.
  unfold Int.modulus. f_equal.
  change Int.wordsize with 32%nat.
  rewrite NPeano.Nat.add_sub_assoc.
  rewrite NPeano.Nat.add_sub_swap by lia. lia. generalize MA_bound; lia.
Qed.


Lemma box_span_mul z:
  box_span (two_power_nat MA * z - 1) = Z.to_nat z.
Proof.
  unfold box_span.
  generalize (BigNumPrelude.Z_div_plus_l z (two_power_nat MA) (-2) (Z.gt_lt _ _ tpMA_pos)).
  intros.
  replace (two_power_nat MA * z - 1 - 1) with (z* two_power_nat MA + -2) by lia. rewrite H.
  f_equal. cut (-2 / two_power_nat MA = -1). intro A; rewrite A. lia.
  unfold Z.div. simpl. 
  generalize tpMA_pos. 
  intros. Opaque two_power_nat. repeat destr. 
  apply Z.leb_le in Heqb.
  apply Z.ltb_ge in Heqb0. assert (two_power_nat MA = 2) by lia. rewrite H1 in *. simpl in *. inv Heqp; auto.
  apply Z.leb_gt in Heqb. apply Z.ltb_lt in Heqb0. assert (two_power_nat MA = 1) by lia.
  rewrite H1 in *.
  assert (MA < S O)%nat. des (lt_dec MA 1).
  generalize (two_p_monotone (Z.of_nat 1) (Z.of_nat MA)).
  intro A; trim A. split. lia. apply inj_le. rewrite NPeano.Nat.le_ngt. auto.
  rewrite <- ! two_power_nat_two_p in A. change (two_power_nat 1) with 2 in A. lia.
  generalize MA_bound; lia.
  apply Z.ltb_ge in Heqb0. clear - Heqb0.
  generalize tpMA_pos. lia.
Qed.

Lemma tpMA_sup8:
  8 <= two_power_nat MA.
Proof.
  change 8 with (two_power_nat 3).
  rewrite ! two_power_nat_two_p.
  apply two_p_monotone. generalize MA_bound. lia.
Qed.


Lemma tpMA'_sup8:
  8 <= two_power_nat (32-MA).
Proof.
  change 8 with (two_power_nat 3).
  rewrite ! two_power_nat_two_p.
  apply two_p_monotone. generalize MA_bound. lia.
Qed.

(* Definition nb_boxes_max : nat := *)
(*   pred (pred (box_span Int.max_unsigned)). *)

Definition nb_boxes_max : Z :=
  two_power_nat (32 - MA) - 2.

(* Lemma nb_boxes_max_eq: *)
(*   Z.of_nat nb_boxes_max = two_power_nat (32 - MA) - 2. *)
(* Proof. *)
(*   unfold nb_boxes_max. *)
(*   rewrite s32_ma. *)
(*   rewrite box_span_mul. *)
(*   rewrite <- ! Z2Nat.inj_pred. rewrite Z2Nat.id. unfold Z.pred.  lia. *)
(*   unfold Z.pred. generalize tpMA'_sup8; lia. *)
(* Qed. *)

Record is_block_list (m: PMap.t (option (Z*Z))) (nb: nat) l :=
  {
    ibl_lnr: list_norepet (map fst l);
    ibl_size: forall b sz, In (b, sz) l -> get_size m b = sz;
    ibl_length: length l = nb;
    ibl_valid: forall b, (Pos.to_nat b <= nb)%nat -> In (b, get_size m b) l
  }.

Definition nb_boxes_used (lb: list (block * Z)) := (* (m: PMap.t (option (Z*Z))) (nb: nat) := *)
  fold_left
    plus
    (map (fun bsz : block * Z =>
         let (b,sz) := bsz in
         box_span sz
      ) lb) O.

Record mem' : Type := mkmem {
  mem_contents: PMap.t (ZMap.t memval);  (**r [block -> offset -> memval] *)
  mem_access: PMap.t (Z -> perm_kind -> option permission);
                                         (**r [block -> offset -> kind -> option permission] *)
  mem_blocksize: PMap.t (option (Z*Z)); (**r [block -> option(Z*Z)]  *)
  mem_mask: PMap.t (option nat); (**r [block -> option mask]; the number of 0-trailing-bits *)
  mem_blocktype: PMap.t (option block_type);
  nextblock: block;
  nb_extra: nat;
  access_max: 
    forall b ofs, perm_order'' (mem_access#b ofs Max) (mem_access#b ofs Cur);
  nextblock_noaccess:
    forall b ofs k, ~(Plt b nextblock) -> mem_access#b ofs k = None;
  access_bounds_ok:             (**r permissions and bounds agree  *)
    forall b ofs k,
      (mem_access#b ofs k) <> None 
      -> in_bound ofs (get_bounds mem_blocksize b);
  msk_valid:                    (**r only valid blocks have non-empty masks  *)
    forall b, ~ (Plt b nextblock) -> mem_mask#b = None;
  blocktype_valid:                    (**r only valid blocks have non-empty masks  *)
    forall b, ~ (Plt b nextblock) -> mem_blocktype#b = None;
  wfm_alloc_ok:                 (**r the allocation algorithm succeeds on this memory  *)
    Z.of_nat (nb_boxes_used (mk_block_list_aux (get_size mem_blocksize) (pred (Pos.to_nat nextblock))) + nb_extra)%nat < nb_boxes_max;
  alignment_ok:
    forall b al,
      mem_mask#b = Some al -> (al <= MA)%nat /\
                              (al >= alignment_of_size (get_size (mem_blocksize) b))%nat;
  bounds_mask_consistency:      (**r bounds and masks information are present together, or not at all  *)
    forall b,
      mem_mask#b = None -> mem_blocksize#b = None;
  bounds_lo_inf0:               (**r the lower bound of a block is 0 *)
    forall b lo hi, 
      mem_blocksize#b = Some (lo,hi) ->
      lo = 0 /\ hi >= 0
}.

Definition mem := mem'.



Lemma bs_valid:                     (**r only valid blocks have non-empty bounds  *)
  forall m b,
    ~ (Plt b m.(nextblock)) ->
    m.(mem_blocksize) # b = None.
Proof.
  intros. apply bounds_mask_consistency; auto.
  apply msk_valid; auto.
Qed.

(* Helper functions *)

Definition size_block (m: mem) (b:block) : Z :=
  get_size (m.(mem_blocksize)) b.

Definition size_of_block (m:mem) (b:block) :=
  match PMap.get b m.(mem_blocksize) with
      | Some (lo,hi) => (Int.repr (hi-lo))
      | None =>  (Int.repr 0)
  end.

Definition bounds_of_block (m:mem) (b:block) : Z*Z :=
  match PMap.get b m.(mem_blocksize) with
      | Some (lo,hi) => (lo,hi)
      | None =>  (0,0)
  end.  

Definition mask (m:mem) (b:block) :=
  match PMap.get b m.(mem_mask) with
      | Some mask => mask
      | None =>  O
  end.

(** The mask of a block is $2^n-1$  *)
Definition nat_mask (m:mem) (b:block) :=
  Int.not (Int.repr (two_power_nat (mask m b) - 1)).

Definition mk_block_list (m:mem) : (list (block * Z)) :=
  mk_block_list_aux (size_block m) (pred (Pos.to_nat (Mem.nextblock m))).

Definition nb_boxes_used_m (m: mem) :=
  (nb_boxes_used (mk_block_list m) + nb_extra m)%nat.

(** [alloc_mem] computes a concrete memory for memory [m]. [size_mem] is the
    first available address after the allocation of [m].  *)

(* Definition size_mem (m: mem) : Z := *)
(*   size_mem_aux MA (mk_block_list m) + two_power_nat MA * Z.of_nat (nb_extra m). *)

(* Definition alloc_mem (m:mem) : option (block -> int) := *)
(*   alloc_blocks MA __szmem (mk_block_list m). *)

(** Normalisation in a given memory. This is what is called [normalise] in the
    paper.  *)

Definition mem_norm (m:mem) (e: expr_sym) :  val :=
  Normalise.normalise (bounds_of_block m) (nat_mask m) e.

Definition max_def v e :=
  match v with
    Vundef => e
  | _ => Eval v
  end.

Definition try_norm m e := max_def (mem_norm m e) e.

Lemma same_eval_same_eval_on:
  forall e e' (SE: same_eval e e') P,
    same_eval_on P e e'.
Proof.
  red; intros; eauto.
Qed.

Lemma same_eval_eqm:
  forall m v1 v2,
    same_eval v1 v2 ->
    Mem.mem_norm m v1 = Mem.mem_norm m v2.
Proof.
  intros m v1 v2 A.
  apply Normalise.norm_eq''; eauto.
  eapply same_eval_same_eval_on; eauto.
Qed.

Lemma lessdef_eqm:
  forall m v1 v2,
    Val.lessdef v1 v2 ->
    Values.Val.lessdef (mem_norm m v1) (mem_norm m v2).
Proof.
  intros m v1 v2 LD.
  apply NormaliseSpec.normalise_ld.
  apply norm_correct.
  apply norm_complete.
  red; intros; eauto.
Qed.


(** Encoding functions (from [Memdata]) are also morphisms for [same_eval].  *)


Definition compat_m (m: mem) (q: msz) :=
  compat (comp_size q) (Mem.bounds_of_block m) (Mem.nat_mask m).

Lemma lessdef_on_P_impl:
  forall (P Q : (block -> int) -> Prop) e e' (LD: lessdef_on P e e') (PQ: forall cm, Q cm -> P cm),
    lessdef_on Q e e'.
Proof.
  red; intros; eauto.
Qed.

Ltac unfsize :=
  IntFacts.unfsize.

Lemma size31_inf:
  comp_size M31 <= Int.max_unsigned.
Proof.
  Opaque two_power_nat. 
  simpl. unfsize.
  generalize (two_power_nat_pos MA); lia.
Qed.

Lemma fold_left_plus_rew:
  forall l n,
    (fold_left plus l n = fold_left plus l O + n)%nat.
Proof.
  induction l; simpl; intros; auto.
  rewrite (IHl (n + a))%nat.
  rewrite (IHl a). lia.
Qed.


Definition make_box_allocation (lb : list (block * Z)) :=
  fold_right (fun (bsz: block * Z)
                (acc: nat * (block -> nat)) =>
               let '(b, sz) := bsz in
               let '(curbox, curalloc) := acc in
               (curbox + box_span sz,
                fun bb => if peq bb b then curbox else curalloc bb)%nat
             )
             (O, fun _ : block => O)
             lb.

Definition box_alloc_to_cm (ba: block -> nat) (b: block) : int :=
  Int.repr (two_power_nat MA * ((Z.of_nat (ba b)) + 1)).


Lemma make_box_allocation_cons:
  forall b sz r,
  make_box_allocation ((b,sz) :: r) =
  let (cb, ca) := make_box_allocation r in
  (cb + box_span sz,
   fun bb => if peq bb b then cb else ca bb)%nat.
Proof.
  simpl. auto.
Qed.


Lemma is_block_list_permut:
  forall sz l l' (PERM: Permutation l l') n
    (IBL: is_block_list sz n l),
    is_block_list sz n l'.
Proof.
  intros.
  inv IBL; constructor; auto.
  + eapply permutation_norepet. apply Permutation_map. apply PERM. auto.
  + intros. apply ibl_size0. rewrite perm_in. eauto. auto.
  + apply Permutation_length. apply Permutation_sym; auto.
  + intros. rewrite perm_in. eauto. apply Permutation_sym; auto.
Qed.

Lemma is_block_list_S:
  forall sz n l
    (IBL': is_block_list sz (S n) l),
  exists l',
    is_block_list sz n l' /\
    Permutation ((Pos.of_nat (S n), get_size sz (Pos.of_nat (S n))) :: l') l.
Proof.
  intros sz n l IBL'.
  exploit (ibl_valid _ _ _ IBL' (Pos.of_nat (S n))). rewrite Nat2Pos.id; auto.
  intro H. apply in_split in H.
  destruct H as (l1 & l2 & SUBST); subst.
  exists (l1 ++ l2).
  split.
  - eapply is_block_list_permut in IBL'.
    2: apply Permutation_sym, Permutation_middle.
    inv IBL'. Opaque Pos.of_nat.
    simpl in *. inv ibl_lnr0. inv ibl_length0.
    constructor; auto.
    intros.
    exploit (ibl_valid0 b). lia. intros [A|A].
    inv A. rewrite Nat2Pos.id in H. lia. lia. auto.
  - apply Permutation_middle.
Qed.


Lemma is_block_list_is_permut:
  forall sz n l l'
    (IBL: is_block_list sz n l)
    (IBL': is_block_list sz n l')
  ,
    Permutation l l'.
Proof.
  induction n; simpl; intros.
  - inv IBL; inv IBL'. des l; des l'. constructor.
  - apply is_block_list_S in IBL.
    apply is_block_list_S in IBL'.
    dex. destr. rewrite <- H0, <- H2. apply perm_skip.
    eauto.
Qed.

Lemma is_block_list_permut_mk_block_list:
  forall sz n l,
  is_block_list sz n l ->
  Permutation l (mk_block_list_aux (get_size sz) n).
Proof.
  induction n; simpl; intros.
  - inv H; des l. unfold mk_block_list_aux. constructor.
  - rewrite mbla_rew. apply is_block_list_S in H.
    destruct H as (l' & IBL & PERM).
    apply IHn in IBL. rewrite <- PERM. apply perm_skip. auto.
Qed.

Lemma is_block_list_S':
  forall sz n l l'
    (IBL: is_block_list sz n l)
    (IBL': is_block_list sz (S n) l'),
    Permutation ((Pos.of_nat (S n), get_size sz (Pos.of_nat (S n))) :: l) l'.
Proof.
  intros.
  apply is_block_list_S in IBL'. dex; destr. rewrite <- H0. apply perm_skip.
  eapply is_block_list_is_permut; eauto.
Qed.

Lemma fold_left_plus_permut:
  forall l l' (PERM: Permutation l l') n,
    fold_left plus l n = fold_left plus l' n.
Proof.
  induction 1; simpl; intros; auto.
  - f_equal. lia.
  - congruence.
Qed.

Lemma nb_boxes_used_S:
  forall l l' sz n,
    is_block_list sz n l ->
    is_block_list sz (S n) l' ->
    (nb_boxes_used l' = nb_boxes_used l + box_span (get_size sz (Pos.of_nat (S n))))%nat.
Proof.
  Opaque Pos.of_nat.
  unfold nb_boxes_used.
  simpl.
  intros.
  eapply is_block_list_S' in H0; eauto.
  erewrite <- fold_left_plus_permut. 2: apply Permutation_map. 2: eassumption.
  simpl.
  rewrite fold_left_plus_rew. reflexivity.
Qed.

Lemma nb_boxes_used_thr:
  forall l curbox curalloc,
    make_box_allocation l = (curbox, curalloc) ->
    (nb_boxes_used l = curbox)%nat.
Proof.
  induction l.
  simpl; intros. inv H. reflexivity.
  intros. destruct a.
  rewrite make_box_allocation_cons in H.
  Opaque Pos.of_nat.
  des (make_box_allocation l). inv H.
  unfold nb_boxes_used in *. simpl.
  rewrite fold_left_plus_rew. erewrite IHl. 2: eauto. auto.
Qed.

Lemma make_box_allocation_le:
  forall l curbox curalloc,
    make_box_allocation l = (curbox, curalloc) ->
    forall b, (curalloc b <= curbox)%nat.
Proof.
  induction l; simpl; intros.
  - inv H; auto.
  - des (make_box_allocation l). des a. inv H.
    specialize (IHl _ _ eq_refl).
    destr. lia. specialize (IHl b). lia.
Qed.

Require Import Tactics.

Lemma make_box_allocation_le_in:
  forall l curbox curalloc,
    list_norepet (map fst l) ->
    make_box_allocation l = (curbox, curalloc) ->
    forall b sz, In (b,sz) l -> (curalloc b + box_span sz <= curbox)%nat.
Proof.
  induction l; simpl; intros.
  - easy.
  - des (make_box_allocation l). des a. inv H. inv H0.
    specialize (IHl _ _ H5 eq_refl).
    des H1. inv e. rewrite peq_true. lia.
    destr. subst.
    exfalso; apply H4. rewrite in_map_iff. eexists; split; eauto. reflexivity.
    specialize (IHl _ _ i). lia.
Qed.

Lemma make_box_allocation_disjoint:
  forall l cb ca,
    list_norepet (map fst l) ->
    make_box_allocation l = (cb, ca) ->
    forall b1 sz1 b2 sz2 (i1: In (b1, sz1) l) (i2: In (b2, sz2) l)
      (d: b1 <> b2) (pos1: sz1 > 0) (pos2: sz2 > 0),
      (ca b1 + box_span sz1 <= ca b2 \/ ca b2 + box_span sz2 <= ca b1)%nat.
Proof.
  induction l; simpl; intros.
  - easy.
  - des a. des (make_box_allocation l). inv H0.
    inv H.
    specialize (IHl _ _ H3 eq_refl).
    repeat destr.
    + subst. assert (z = sz1). des i1. exfalso; apply H2. rewrite in_map_iff. eexists; split; eauto. reflexivity. subst.
      clear i1. des i2.
      right; eapply make_box_allocation_le_in; eauto.
    + subst. assert (z = sz2). des i2. exfalso; apply H2. rewrite in_map_iff. eexists; split; eauto. reflexivity. subst.
      clear i2. des i1.
      left; eapply make_box_allocation_le_in; eauto.
    + des i1. des i2. eauto.
Qed.

Lemma minus_1_div_eq:
  forall z, z > 0 -> -1 / z = -1.
Proof.
  unfold Z.div. simpl. intros.
  des z. lia.
  destr. lia.
Qed.

Lemma box_span_align:
  forall z,
    z >= 0 ->
    two_power_nat MA * Z.of_nat (box_span z) = align z (two_power_nat MA).
Proof.
  unfold box_span, align.
  intros.
  generalize (BigNumPrelude.Z_div_plus_l 1 (two_power_nat MA) (z-1) (Z.gt_lt _ _ tpMA_pos)).
  rewrite Z2Nat.id.
  intros. rewrite Z.add_comm. rewrite <- H0.
  rewrite Z.mul_comm. f_equal. f_equal. lia.
  destruct (zlt 0 z).
  generalize (Z.div_pos (z-1) (two_power_nat MA)). intro A. trim A. lia. trim A.
  generalize tpMA_pos. lia. lia.
  assert (z = 0) by lia. subst. simpl.
  rewrite minus_1_div_eq. lia. apply tpMA_pos.
Qed.


Lemma s31_ma:
  comp_size M31 = two_power_nat MA * (two_power_nat (32 - MA) - 1) - 1.
Proof.
  unfold comp_size. rewrite s32_ma. lia.
Qed.

Lemma lt_le_minus1:
  forall a b : Z,
    a < b ->
    a <= b - 1.
Proof.
  intros. lia.
Qed.

Lemma in_bound_in_mk:
  forall o m b l,
    in_bound (Int.unsigned o) (bounds_of_block m b) ->
    is_block_list (mem_blocksize m) (pred (Pos.to_nat (nextblock m))) l ->
    In (b, size_block m b) l /\
    Int.unsigned o < two_power_nat MA * Z.of_nat (box_span (size_block m b)) /\
    size_block m b > 0.
Proof.
  intros.
  assert (Pos.to_nat b <= pred (Pos.to_nat (nextblock m)))%nat.
  {
    destruct (plt b (nextblock m)).
    apply Pos2Nat.inj_lt in p. lia.
    unfold bounds_of_block in H.
    rewrite bounds_mask_consistency in H.
    unfold in_bound in H; simpl in H; lia.
    apply msk_valid; auto.
  }
  split. rewrite perm_in. apply mbla_below_in'. apply H1.
  apply is_block_list_permut_mk_block_list. eauto. 
  split.
  red in H.
  eapply Z.lt_le_trans. apply H.
  unfold size_block, get_size, bounds_of_block.
  destr. des p. eapply bounds_lo_inf0 in Heqo0. destruct Heqo0; subst. rewrite Z.sub_0_r.
  rewrite box_span_align. apply align_le. apply tpMA_pos. auto.
  unfold box_span. simpl. rewrite minus_1_div_eq. simpl. lia. apply tpMA_pos.
  red in H.
  revert H.
  unfold size_block, get_size, bounds_of_block.
  destr. des p. eapply bounds_lo_inf0 in Heqo0. destruct Heqo0; subst. rewrite Z.sub_0_r. lia. lia.
Qed.

Lemma box_alloc_unsigned_range:
  forall thr m ba
    (THR : (thr < Z.to_nat nb_boxes_max)%nat)
    l
    (IBL: is_block_list (mem_blocksize m) (pred (Pos.to_nat (nextblock m))) l)
    (MBA : make_box_allocation l = (thr, ba)) b o
    (IB : in_bound (Int.unsigned o) (bounds_of_block m b)),
    0 <= two_power_nat MA * (Z.of_nat (ba b) + 1) <= Int.max_unsigned.
Proof.
  intros. split.
  * apply Z.lt_le_incl. apply Z.mul_pos. left. split. generalize tpMA_pos. lia. lia.
  * exploit in_bound_in_mk. eauto. eauto. intros [IN RNG].
    generalize (make_box_allocation_le_in _ _ _ (ibl_lnr _ _ _ IBL) MBA _ _ IN).
    intros LE.
    rewrite s32_ma.
    apply lt_le_minus1.
    rewrite <- Z.mul_lt_mono_pos_l. 2: generalize tpMA_pos; lia. 
    cut (Z.of_nat (ba b) < two_power_nat (32 - MA) - 1). lia.
    eapply Z.le_lt_trans with (Z.of_nat thr). apply inj_le. lia.
    apply Nat2Z.inj_lt in THR. eapply Z.lt_le_trans. eauto.
    unfold nb_boxes_max.
    rewrite Z2Nat.id. lia.
    generalize tpMA'_sup8; lia.
Qed.

Lemma box_alloc_in_range:
  forall thr m ba
    (THR : (thr < Z.to_nat nb_boxes_max)%nat)
    l
    (IBL: is_block_list (mem_blocksize m) (pred (Pos.to_nat (nextblock m))) l)
    (MBA : make_box_allocation l = (thr, ba))
    b o
    (IB : in_bound (Int.unsigned o) (bounds_of_block m b)),
    0 < Int.unsigned (Int.repr (two_power_nat MA * (Z.of_nat (ba b) + 1))) + Int.unsigned o < comp_size M31.
Proof.
  intros. 
  rewrite Int.unsigned_repr.
  + split.
    * change 0 with (0+0). apply Z.add_lt_le_mono.
      apply Z.mul_pos_pos. generalize tpMA_pos. lia.
      lia.
      generalize (Int.unsigned_range o). lia.
    * exploit in_bound_in_mk. eauto. eauto. intros [IN [RNG POS]].
      generalize (make_box_allocation_le_in _ _ _ (ibl_lnr _ _ _ IBL) MBA _ _ IN).
      intro LE.
      eapply Z.lt_le_trans.
      apply Z.add_lt_mono_l. eauto.
      transitivity (two_power_nat MA * (1 + Z.of_nat (ba b + box_span (size_block m b))%nat)).
      rewrite Nat2Z.inj_add. lia.
      eapply Z.le_trans.
      apply Z.mul_le_mono_nonneg_l. generalize tpMA_pos; lia.
      apply Z.add_le_mono_l. apply Nat2Z.inj_le. eauto.
      rewrite s31_ma.
      apply lt_le_minus1.
      rewrite <- Z.mul_lt_mono_pos_l. 2: generalize tpMA_pos; lia.
      cut (Z.of_nat thr < two_power_nat (32 - MA) - 2). lia.
      eapply Z.lt_le_trans. apply inj_lt. eauto.
      unfold nb_boxes_max.
      rewrite Z2Nat.id. lia.
      generalize tpMA'_sup8; lia.
  + eapply box_alloc_unsigned_range; eauto.
Qed.

Lemma box_alloc_in_range':
  forall thr m ba
    (THR : (thr < Z.to_nat nb_boxes_max)%nat)
    l
    (IBL: is_block_list (mem_blocksize m) (pred (Pos.to_nat (nextblock m))) l)
    (MBA : make_box_allocation l = (thr, ba))
    b o
    (IB : in_bound (Int.unsigned o) (bounds_of_block m b)),
    0 <= Int.unsigned (Int.repr (two_power_nat MA * (Z.of_nat (ba b) + 1))) + Int.unsigned o <= Int.max_unsigned.
Proof.
  intros.
  exploit box_alloc_in_range; eauto. intros. split. lia.
  generalize size31_inf; lia.
Qed.

Lemma zlt_neq: forall a b : Z, a < b -> a <> b.
Proof.
  intros. intro; subst. lia.
Qed.

Lemma zgt_neq: forall a b : Z, b < a -> a <> b.
Proof.
  intros. intro; subst. lia.
Qed.

Lemma box_alloc_to_cm_compat:
  forall m thr ba
    (THR: (thr < Z.to_nat nb_boxes_max)%nat)
    l
    (IBL: is_block_list (mem_blocksize m) (pred (Pos.to_nat (nextblock m))) l)
    (MBA: make_box_allocation l = (thr, ba)),
    compat_m m M31 (box_alloc_to_cm ba).
Proof.
  intros; split.
  - unfold box_alloc_to_cm. intros. rewrite Int.add_unsigned.
    cut (   0 < Int.unsigned (Int.repr (two_power_nat MA * (Z.of_nat (ba b) + 1))) + Int.unsigned o < comp_size M31).
    {
      intro.
      rewrite Int.unsigned_repr; auto. split. lia. transitivity (comp_size M31). lia. apply size31_inf.
    } 
    eapply box_alloc_in_range;eauto.
  - intros.
    exploit in_bound_in_mk. apply H0. eauto. intros (IN & RNG & POS).
    exploit in_bound_in_mk. apply H1. eauto. intros (IN' & RNG' & POS').
    generalize (make_box_allocation_disjoint
                  _ _ _
                  (ibl_lnr _ _ _ IBL) MBA _ _ _ _ IN IN' H POS POS').
    unfold box_alloc_to_cm. intros. rewrite ! Int.add_unsigned.
    rewrite Int.unsigned_repr. 2: eapply box_alloc_in_range'; eauto.
    rewrite (Int.unsigned_repr (Int.unsigned _ + _)). 2: eapply box_alloc_in_range'; eauto.
    rewrite Int.unsigned_repr. 2: eapply box_alloc_unsigned_range; eauto.
    rewrite Int.unsigned_repr. 2: eapply box_alloc_unsigned_range; eauto.
    cut (two_power_nat MA * (Z.of_nat (ba b)) + Int.unsigned o <> two_power_nat MA * (Z.of_nat (ba b')) + Int.unsigned o').
    lia.
    destruct H2.
    + apply zlt_neq.
      eapply Z.lt_le_trans. apply Z.add_lt_mono_l. apply RNG.
      transitivity (two_power_nat MA * Z.of_nat (ba b')).
      apply inj_le in H2. apply Z.mul_le_mono_nonneg_l with (p := two_power_nat MA) in H2. lia. generalize tpMA_pos; lia.
      generalize (Int.unsigned_range o'); lia.
    + apply zgt_neq.
      eapply Z.lt_le_trans. apply Z.add_lt_mono_l. apply RNG'.
      transitivity (two_power_nat MA * Z.of_nat (ba b)).
      apply inj_le in H2. apply Z.mul_le_mono_nonneg_l with (p := two_power_nat MA) in H2. lia. generalize tpMA_pos; lia.
      generalize (Int.unsigned_range o); lia.
  - intros. unfold box_alloc_to_cm.
    generalize (Z.of_nat (ba b) + 1). intro.
    unfold nat_mask, mask.
    Opaque minus.
    destr.
    + exploit alignment_ok. eauto. intros [NMA AOS].
      solve_int. 
      rewrite Int.bits_not; auto.        
      rewrite ! Int.testbit_repr; auto.
      rewrite ! two_power_nat_two_p.
      rewrite Int.Ztestbit_two_p_m1; auto; try omega.
      destr; try ring.
      generalize (Int.Ztestbit_mod_two_p (Z.of_nat MA) (two_p (Z.of_nat MA) * z) i).
      destr; try omega. 
      intro H. rewrite <- H; auto with zarith.
      rewrite Z.mul_comm. rewrite Z.mod_mul; auto.
      rewrite Int.Ztestbit_0. reflexivity. generalize tpMA_pos. rewrite two_power_nat_two_p.
      lia.
    + change (two_power_nat 0 - 1) with 0.
      change (Int.repr 0) with Int.zero.
      rewrite Int.not_zero. rewrite Int.and_mone. auto.
Qed.

Definition mk_cm l nbe :=
  let (thr,al) := make_box_allocation l in
  if zlt (Z.of_nat (thr + nbe)) nb_boxes_max
  then Some al
  else None.

Lemma nb_used_permut:
  forall l l' (P: Permutation l l'),
    nb_boxes_used l = nb_boxes_used l'.
Proof.
  intros.
  apply fold_left_plus_permut. apply Permutation_map. auto.
Qed.

Lemma alloc_compat:
  forall m l
    (IBL: is_block_list (mem_blocksize m) (pred (Pos.to_nat (nextblock m))) l),
    exists al,
      mk_cm l (nb_extra m) = Some al /\
      compat_m m M31 (box_alloc_to_cm al).
Proof.
  intros.
  generalize (wfm_alloc_ok m).
  intros. unfold mk_cm.
  des (make_box_allocation l).
  destr.
  - eexists; split; eauto.
    eapply box_alloc_to_cm_compat. 3: eauto. apply Nat2Z.inj_lt. rewrite Nat2Z.inj_add in l0.
    rewrite Z2Nat.id. lia. lia. auto.
  - eapply nb_boxes_used_thr in Heqp.
    subst. 
    erewrite nb_used_permut in H. apply g in H. easy.
    apply Permutation_sym, is_block_list_permut_mk_block_list; auto.
Qed.

Lemma length_mbla:
  forall sz n, length (mk_block_list_aux sz n) = n.
Proof.
  induction n; simpl; intros. auto. rewrite <- IHn at 2.
  f_equal.
Qed.

Lemma is_block_list_mk_block_list:
  forall sz n,
    is_block_list sz n (mk_block_list_aux (get_size sz) n).
Proof.
  intros.
  constructor.
  apply mbla_norepet.
  intros; symmetry; eapply mbla_in; eauto.
  apply length_mbla.
  eapply mbla_below_in'.
Qed.

Lemma concrete_mem':
  forall m, exists al, compat_m m M31 al.
Proof.
  intros.
  edestruct (alloc_compat m) as [al [A B]].
  apply is_block_list_mk_block_list.
  eexists; eauto.
Qed.

Lemma compat31_32:
  forall m cm, compat_m m M31 cm -> compat_m m M32 cm.
Proof.
  intros.
  eapply compat_larger. 2: eauto.
  simpl. generalize (two_power_nat_pos MA); lia.
Qed.

Lemma concrete_mem:
  forall m, exists al, compat_m m M32 al.
Proof.
  intros.
  destruct (concrete_mem' m) as [al A].
  exists al. eapply compat31_32; eauto.
Qed.


Definition good_result_m m e v :=
  good_result Int.max_unsigned (bounds_of_block m) (nat_mask m) e v.

Record is_norm_m m e v :=
  mkIsNormM {
    eval_ok_m: lessdef_on (compat_m m M32) (Eval v) e
  }.

Lemma norm_complete:
  forall m e v
    (INM: is_norm_m m e v),
    Values.Val.lessdef v (mem_norm m e).
Proof.
  intros.
  apply Normalise.norm_complete.
  inv INM; constructor; auto.
Qed.

Lemma norm_correct:
  forall m e,
    is_norm_m m e (mem_norm m e).
Proof.
  intros.
  destruct (Normalise.norm_correct (bounds_of_block m) (nat_mask m) e).
  constructor; auto.
Qed.

Lemma norm_ld:
  forall m e v,
    mem_norm m e = v ->
    forall cm em,
      compat_m m M32 cm ->
      Values.Val.lessdef (eSval cm v) (eSexpr cm em e).
Proof.
  intros.
  destruct (norm_correct m e).
  subst.
  apply eval_ok_m0; auto. 
Qed.

Lemma norm_gr:
  forall m e,
    good_result_m m e (mem_norm m e).
Proof.
  intros. apply norm_gr.
Qed.

Lemma eq_norm:
  forall m e v,
    is_norm_m m e v ->
    v <> Vundef ->
    Mem.mem_norm m e = v.
Proof.
  intros m e v IS.
  generalize (norm_complete m e v IS). intro A; inv A; destr.
Qed.

Lemma same_compat_bounds_mask:
  forall m1 m2
    (Bnds: forall b, bounds_of_block m1 b = bounds_of_block m2 b)
    (Msk:  forall b, nat_mask m1 b = nat_mask m2 b)
    cm,
    compat_m m1 M32 cm <-> compat_m m2 M32 cm.
Proof.
  split; eapply compat_same_bounds; eauto.
Qed.

Lemma good_result_m_same_compat:
  forall m m' e v
    (MR: forall cm, compat_m m M32 cm <-> compat_m m' M32 cm),
    good_result_m m e v <->
    good_result_m m' e v.
Proof.
  split; red; intros; des v;
  red; intros.
  eapply MR in COMP; eauto.
  eapply MR in COMP'; eauto.
  apply H; auto.
  setoid_rewrite <- MR; eauto.
  setoid_rewrite <- MR; eauto.
Qed.

Lemma is_norm_m_same_compat:
  forall m m' e v
    (C: forall cm, compat_m m M32 cm <-> compat_m m' M32 cm),
    is_norm_m m e v <->
    is_norm_m m' e v.
Proof.
  intros.
  generalize (good_result_m_same_compat _ _ e v C).
  intros GR.
  split; intros INM; inv INM; constructor.
  - eapply lessdef_on_P_impl; eauto.
    intros; rewrite C; eauto.
  - eapply lessdef_on_P_impl; eauto.
    intros; rewrite <- C; eauto.
Qed.

Lemma norm_same_compat:
  forall m1 m2 e
    (Bnds: forall b, bounds_of_block m1 b = bounds_of_block m2 b)
    (Msk:  forall b, nat_mask m1 b = nat_mask m2 b),
    mem_norm m1 e = mem_norm m2 e.
Proof. 
  intros.
  generalize (norm_correct m1 e) (norm_correct m2 e).
  intros A B.
  generalize (same_compat_bounds_mask _ _ Bnds Msk); intro SC; clear Bnds Msk.
  apply lessdef_antisym; apply norm_complete.
  rewrite <- is_norm_m_same_compat; eauto.
  rewrite  is_norm_m_same_compat; eauto.
Qed.


Definition in_bound_m (o: Z) (m: mem) (b: block) : Prop :=
  in_bound o (bounds_of_block m b).

Definition in_bound_m_dec:
  forall o m b,
    in_bound_m o m b \/ ~ in_bound_m o m b.
Proof.
  intros; apply in_bound_dec.
Defined.


Definition pair_eq {A B} (eqA: forall (a b : A), {a = b} + {a<>b})
           (eqB: forall (a b: B), {a = b} + {a<>b}) :
  forall (a b : (A*B)),
    {a = b} + {a<>b}.
Proof.
  decide equality.
Qed.

Definition put_front (bl: list (positive * Z))  (b: positive) (sz: Z) :=
  (b,sz) :: remove (pair_eq peq zeq) (b,sz) bl.

Lemma remove_app:
  forall {A} (eqA: forall (a b : A), {a = b} + {a<>b})
    a l1 l2,
    remove eqA a (l1 ++ l2) = remove eqA a l1 ++ remove eqA a l2.
Proof.
  induction l1; simpl. auto.
  destr.
Qed.

Lemma remove_not_in:
    forall {A} (eqA: forall (a b : A), {a = b} + {a<>b})
      a l (NIN: ~ In a l),
      remove eqA a l = l.
Proof.
  induction l; simpl; intros; auto.
  destr.
Qed.

Lemma put_front_permut:
  forall b sz bl (IN: In (b,sz) bl)
    (LNR: list_norepet bl),
    Permutation bl (put_front bl b sz).
Proof.
  intros.
  cut (exists a c, bl = a ++ (b,sz) :: c).
  clear IN.
  intros [a [c EQ]].
  subst.
  apply list_norepet_app in LNR.
  destruct LNR as [LNRA [LNRB LDSIJ]].
  inversion LNRB as [|? ? NIN LNRB']; subst.
  unfold put_front.
  rewrite ! remove_app.
  rewrite Permutation_middle.
  rewrite remove_not_in.
  simpl. destr.
  rewrite remove_not_in. reflexivity. auto. intro IN.
  red in LDSIJ. specialize (LDSIJ _ _ IN (or_introl eq_refl)). congruence.
  apply in_split. auto.
Qed.

Definition other_cm cm b :=
  fun bb =>
    if peq b bb
    then Int.add (cm b) (Int.repr (two_power_nat MA))
    else cm bb.


Lemma two_power_nat_inf_mod:
  forall x y,
    (x < y)%nat ->
    two_power_nat x = two_power_nat x mod two_power_nat y.
Proof.
  intros.
  symmetry. apply Zmod_small.
  split.
  generalize (two_power_nat_pos x); lia.
  rewrite ! two_power_nat_two_p.
  apply two_p_monotone_strict.
  ppsimpl; lia.
Qed.


Lemma add_bounded_plus8:
  forall i o
    (H : 0 < Int.unsigned (Int.add i o) < comp_size M31),
    0 < Int.unsigned (Int.add (Int.add i (Int.repr (two_power_nat MA))) o) < Int.max_unsigned.
Proof.
  intros.
  rewrite Int.add_assoc. rewrite (Int.add_commut _ o).
  rewrite <- Int.add_assoc.
  generalize dependent (Int.add i o).
  intro.
  rewrite <- ! int_add_rew in *.
  rewrite ! Int.unsigned_repr_eq in *. 
  replace ((two_power_nat MA)  mod Int.modulus) with (two_power_nat MA).
  elim_div.  unfold comp_size.  unfsize. 
  generalize (two_power_nat_pos MA).
  intros.
  lia.
  apply two_power_nat_inf_mod. generalize (MA_bound); unfsize. change (Int.wordsize) with 32%nat. lia.
Qed.

Lemma i_bounded_plus8:
   forall i : int,
   0 < Int.unsigned i < comp_size M31 ->
   Int.unsigned (Int.add i (Int.repr (two_power_nat MA))) < Int.unsigned i -> False.
Proof.
  intro.
  rewrite <- ! int_add_rew in *.
  rewrite ! Int.unsigned_repr_eq in *.
  elim_div.  unfold comp_size. unfsize.
  Opaque two_power_nat. 
  generalize (two_power_nat_pos MA). 
  generalize (two_power_nat MA). intro.
  intros.
  assert (z1 = 0 \/ z1 = 1) by lia.
  assert (z = 0 \/ z = 1) by lia. lia.
Qed.

Lemma compat_shift:
  forall m cm b
    (LAST: forall b' o o', b <> b' ->
                      in_bound (Int.unsigned o)  (bounds_of_block m b) ->
                      in_bound (Int.unsigned o') (bounds_of_block m b') ->
                      Int.unsigned (Int.add (cm b') o') < Int.unsigned (Int.add (cm b) o))
    (COMP : compat_m m M31 cm),
  exists cm',
    cm b <> cm' b /\
    (forall b' (diff: b' <> b), cm b' = cm' b') /\
    compat_m m M32 cm'.
Proof.
  intros.
  exists (other_cm cm b); repSplit; auto.
  - unfold other_cm; rewrite peq_true; auto.
    rewrite <- Int.add_zero at 1.
    intro ADD.
    apply int_add_eq_l in ADD. apply f_equal with (f:=Int.unsigned) in ADD.
    rewrite Int.unsigned_zero in ADD. rewrite Int.unsigned_repr in ADD.
    generalize (two_power_nat_pos MA); lia.
    generalize (two_power_nat_pos MA); split. lia.
    unfold Int.max_unsigned.
    unfold Int.modulus.
    rewrite ! two_power_nat_two_p.
    generalize (two_p_monotone_strict (Z.of_nat MA) (Z.of_nat Int.wordsize)).
    intro A. trim A. clear A. split. lia.
    generalize (MA_bound). change (Int.wordsize) with (32%nat). lia.
    lia.
  - unfold other_cm; intros; rewrite peq_false; auto.
  -
    destruct COMP; constructor; simpl; intros.
    + apply addr_space in H. unfsize.
      unfold other_cm. destr_cond_match; subst. 
      apply add_bounded_plus8. auto. 
      generalize (size31_inf); unfsize. lia.
    + specialize (overlap _ _ _ _ H H0 H1).
      generalize (addr_space _ _ H0).
      generalize (addr_space _ _ H1). intros A2 A1.
      unfold other_cm.
      repeat destr_cond_match; subst; try congruence.
      * specialize (LAST _ _ _ n H0 H1).
        intro EQ.
        rewrite <- EQ in LAST.
        revert LAST.
        rewrite Int.add_assoc. rewrite (Int.add_commut _ o).
        rewrite <- Int.add_assoc. 
        apply i_bounded_plus8. auto.
      * specialize (LAST _ _ _ n H1 H0).
        intro EQ.
        rewrite EQ in LAST.
        revert LAST.
        rewrite Int.add_assoc. rewrite (Int.add_commut _ o').
        rewrite <- Int.add_assoc. clear EQ overlap.
        apply i_bounded_plus8. auto.
    + generalize (alignment b0).
      unfold other_cm; destr. subst.
      unfold nat_mask. intros.
      eapply alignment_inj with (i1:=mask m b0).
      apply H.
      apply two_p_abs. lia.
      Opaque two_power_nat.
      revert H; unfold nat_mask, mask.
      destr. intros.
      * apply alignment_ok in Heqo. 
        destruct Heqo as [C D].
        apply Int.same_bits_eq.
        intros.
        rewrite Int.bits_and; auto.
        rewrite Int.bits_not; auto.
        replace (Int.testbit (Int.repr (two_power_nat MA)) i)
        with (if zeq i (Z.of_nat MA) then true else false).
        rewrite  Int.testbit_repr; auto.
        rewrite two_power_nat_two_p.
        rewrite Int.Ztestbit_two_p_m1; auto; try lia.
        destr. destr. subst. generalize (MA_bound); lia.
        rewrite Int.testbit_repr; auto.
        rewrite two_power_nat_two_p. rewrite two_p_equiv.
        rewrite Z.pow2_bits_eqb; auto. 2: lia.
        destr_cond_match. subst; auto. rewrite Z.eqb_refl. auto.
        clear Heqs. rewrite <- Z.eqb_neq in n0. rewrite Z.eqb_sym. auto.
      * rewrite two_power_nat_O. change (Int.repr (1-1)) with Int.zero.
        rewrite Int.not_zero. rewrite ! Int.and_mone. auto.
Qed.

Lemma remove_in:
  forall {A} (eqA: forall (a b: A), {a=b}+{a<>b}) a b l,
    a <> b ->
    In a l ->
    In a (remove eqA b l).
Proof.
  induction l; simpl; intros; eauto.
  destr.
Qed.

Lemma in_bound_plt:
  forall b m o,
    in_bound o (bounds_of_block m b) ->
    Plt b (nextblock m).
Proof.
  intros.
  destruct (plt b (nextblock m)); auto.
  apply msk_valid in n.
  apply bounds_mask_consistency in n.
  unfold bounds_of_block in H; rewrite n in H. red in H; destr; lia.
Qed.

Lemma remove_in_before:
  forall {A} (pdec: forall (a b : A), {a=b}+{a<>b})
    a b l,
    In a (remove pdec b l) ->
    In a l.
Proof.
  induction l; simpl; intros; auto.
  revert H; destr.
Qed.

Lemma remove_P:
  forall {A B} (pdec: forall (a b : A*B), {a=b}+{a<>b}) f
    (p: A*B) (l: list (A*B))
    (Pr: forall a b, In (a,b) l -> b = f a)
    a b
    (IN:In (a,b) (remove pdec p l)),
    b = f a.
Proof.
  intros.
  apply remove_in_before in IN.
  auto.
Qed.


Lemma bounds_lo_0:
  forall m b,
    fst (bounds_of_block m b) = 0.
Proof.
  intros; unfold bounds_of_block; destr. des p.
  eapply bounds_lo_inf0 in Heqo. destr.
Qed.

Lemma in_bound_zero:
  forall o m b,
    in_bound o (bounds_of_block m b) ->
    in_bound (Int.unsigned Int.zero) (bounds_of_block m b).
Proof.
  intros.
  eapply in_bound_zero; eauto.
  apply bounds_lo_0.
Qed.

Lemma compat_add_unsigned:
  forall m cm (COMP: compat_m m M32 cm) b
    o (IB: in_bound (Int.unsigned o) (bounds_of_block m b)),
    Int.unsigned (Int.add (cm b) o) = Int.unsigned (cm b) + Int.unsigned o.
Proof.
  intros.
  eapply compat_add_unsigned; eauto.
  apply bounds_lo_0.
Qed.

Lemma make_box_allocation_order:
  forall l sz al
    (AMA: make_box_allocation l = (sz,al))
    (lnr: list_norepet (map fst l))
    b b'
    (AB: appears_before b b' (map fst l)),
    (al b' <= al b)%nat.
Proof.
  induction l; simpl; intros.
  inv AMA. lia.
  destruct a. simpl in *.
  inv lnr. 
  destruct (peq b b'). subst. lia.
  des (make_box_allocation l).
  specialize (IHl _ _ eq_refl H2). inv AMA.
  destr.
  - subst. destr.     
    inv AB. des l1.
  - destr. subst.
    eapply make_box_allocation_le; eauto.
    apply IHl.
    inv AB. des l1. inv H. econstructor. eauto. destr.
Qed.


Lemma map_app_cons {A B}:
  forall (f: A -> B) l fa fb fc,
    map f l = fa ++ fb :: fc ->
    exists a b c, l = a ++ b :: c /\ fa = map f a /\ fb = f b /\ fc = map f c.
Proof.
  induction l; simpl; intros.
  - apply app_cons_not_nil in H. easy.
  - des fa. inv H. exists nil, a, l. simpl. auto.
    inv H. apply IHl in H2. dex; destr_and. subst.
    exists (a::a0), b, c. auto.
Qed.

Lemma put_front_appears_before:
  forall b sz l b',
    In b' (map fst l) -> b <> b' ->
    appears_before b b' (map fst (put_front l b sz)).
Proof.
  simpl.
  intros.
  exploit in_split; eauto. intro; dex; destr_and.
  apply map_app_cons in H1. dex. destr_and. subst.
  eapply (ab_intro _ _ _ nil); simpl; auto. f_equal.
  rewrite remove_app. simpl. destr. subst; destr.
  rewrite map_app. simpl. eauto.  
Qed.

Opaque put_front.

Lemma box_span_pos:
  forall z, z > 0 -> (0 < box_span z)%nat.
Proof.
  intros. rewrite Nat2Z.inj_lt.
  rewrite (Z.mul_lt_mono_pos_l _ _ _ (Z.gt_lt _ _ tpMA_pos)).
  simpl. rewrite box_span_align by lia.
  eapply Z.lt_le_trans. rewrite Z.mul_0_r. apply Z.gt_lt. eauto.
  apply align_le. generalize tpMA_pos; lia.
Qed.


Theorem exists_two_cms:
  forall m b,
  exists cm cm' : block -> int,
    compat_m m M32 cm  /\
    compat_m m M32 cm' /\
    cm b <> cm' b /\
    forall b', b <> b' -> cm b' = cm' b'.
Proof.
  intros.
  destruct (plt b (nextblock m)).
  - destruct (alloc_compat m (put_front (mk_block_list m) b (size_block m b))) as [al [CONSTR A]].
    eapply is_block_list_permut. apply put_front_permut. eapply mbla_below_in'. apply Pos2Nat.inj_lt in p. lia.
    apply mbla_norepet'. apply is_block_list_mk_block_list.

    exists (box_alloc_to_cm al).
    destruct (compat_shift m (box_alloc_to_cm al) b) as (cm' & DIFF & SAME & COMPAT); auto.
    + intros.

      assert (IBL:  is_block_list (mem_blocksize m) (pred (Pos.to_nat (nextblock m))) (put_front (mk_block_list m) b (size_block m b))).
      {
        eapply is_block_list_permut. apply put_front_permut. eapply mbla_below_in'.
        apply Pos2Nat.inj_lt in p. apply NPeano.Nat.lt_le_pred. eauto. 
        apply mbla_norepet'. apply is_block_list_mk_block_list.
      } 


      exploit in_bound_in_mk. apply H0. eauto. intros (IN & RNG & SZ).
      exploit in_bound_in_mk. apply H1. eauto. intros (IN' & RNG' & SZ').

      unfold mk_cm in CONSTR.
      repeat destr_in CONSTR.
      generalize Heqp0; intro MBA.
      eapply make_box_allocation_order in Heqp0.
      2: eapply permutation_norepet. 2: apply Permutation_map, put_front_permut.
      2: eapply mbla_below_in'. 2: apply Pos2Nat.inj_lt in p. 2: lia.
      2: apply mbla_norepet'. 2: apply mbla_norepet.

      2: apply put_front_appears_before. 3: apply H.
      2: apply mbla_below_in.
      2: apply NPeano.Nat.lt_le_pred. 2: apply Pos2Nat.inj_lt. 2: eapply in_bound_plt. 2: apply H1.

      inv CONSTR.

      exploit make_box_allocation_disjoint. 2: eexact MBA.
      eapply permutation_norepet. apply Permutation_map, put_front_permut.
      eapply mbla_below_in'. apply Pos2Nat.inj_lt in p. lia.
      apply mbla_norepet'. apply mbla_norepet.
      apply IN. apply IN'. auto. auto. auto. intro DISJ. des DISJ.
      eapply box_span_pos in SZ; lia.
      unfold box_alloc_to_cm. rewrite ! Int.add_unsigned.
      rewrite Int.unsigned_repr. 2: eapply box_alloc_in_range'. 4: eauto.
      Focus 2.
      rewrite Nat2Z.inj_add in l. apply Nat2Z.inj_lt. rewrite Z2Nat.id. lia. lia.
      2: eauto. 2: eauto.
      rewrite (Int.unsigned_repr (Int.unsigned _ + _)). 2: eapply box_alloc_in_range'. 4: eauto.
      Focus 2.
      rewrite Nat2Z.inj_add in l. apply Nat2Z.inj_lt. rewrite Z2Nat.id. lia. lia.
      2: eauto. 2: eauto.
      rewrite Int.unsigned_repr. 2: eapply box_alloc_unsigned_range. 4: eauto.
      Focus 2.
      rewrite Nat2Z.inj_add in l. apply Nat2Z.inj_lt. rewrite Z2Nat.id. lia. lia.
      2: eauto. 2: eauto.
      rewrite Int.unsigned_repr. 2: eapply box_alloc_unsigned_range. 4: eauto.
      Focus 2.
      rewrite Nat2Z.inj_add in l. apply Nat2Z.inj_lt. rewrite Z2Nat.id. lia. lia.
      2: eauto. 2: eauto.
      cut (two_power_nat MA * (Z.of_nat (al b')) + Int.unsigned o' < two_power_nat MA * (Z.of_nat (al b)) + Int.unsigned o).
      lia.
      eapply Z.lt_le_trans. apply Z.add_lt_mono_l. apply RNG'.
      transitivity (two_power_nat MA * Z.of_nat (al b)).
      apply inj_le in l0. apply Z.mul_le_mono_nonneg_l with (p := two_power_nat MA) in l0. lia. generalize tpMA_pos; lia.
      generalize (Int.unsigned_range o); lia.

    + eexists; repSplit; eauto.
      apply compat31_32; auto.
  - 
    destruct (alloc_compat m (mk_block_list m)) as [al [CONSTR A]].
    apply is_block_list_mk_block_list.
    exists (box_alloc_to_cm al).
    generalize (compat_shift m (box_alloc_to_cm al) b); intro B.
    trim B. intros.
    apply in_bound_plt in H0; congruence.
    trim B; auto.
    dex; destr_and. eexists; repSplit; eauto.
    apply compat31_32; auto.
Qed.

Lemma norm_val:
  forall m v,
    mem_norm m (Eval v) = v.
Proof.
  intros. eapply normalise_val; eauto.
  intros. generalize (exists_two_cms m b1). eauto.
Qed.

Lemma norm_vundef:
  forall m,
    mem_norm m (Eval Vundef) = Vundef.
Proof.
  intros; apply norm_val.
Qed.

Lemma same_Eval_norm:
  forall m vn v, 
    same_eval vn (Eval v) ->
    Mem.mem_norm m vn = v.
Proof.
  intros m vn v SE.
  erewrite Mem.same_eval_eqm; eauto.
  apply norm_val.
Qed.

Lemma norm_ptr_same:
  forall m b o b' o',
    Mem.mem_norm m (Eval (Vptr b o)) = Vptr b' o' ->
    Vptr b o = Vptr b' o'.
Proof.
  intros m b o b' o' MN.
  rewrite (norm_val) in MN; auto.
Qed.

Lemma norm_type:
  forall m e v t,
    Mem.mem_norm m e = v ->
    v <> Vundef ->
    wt_val v t ->
    wt_expr e t.
Proof.
  intros m e v t MN NU WT. subst. 
  assert (N:= norm_ld m e _ eq_refl).
  destruct (Mem.concrete_mem m).
  specialize (N _ Normalise.dummy_em H).
  inv N; auto.
  generalize (expr_nu_type x dummy_em e t _ (eq_sym H2)).
  des (mem_norm m e).
  des (mem_norm m e).
Qed.

Lemma same_val_ofbool_norm:
  forall m vn b, 
    same_eval vn (Val.of_bool b) ->
    Mem.mem_norm m vn = Vint (if b then Int.one else Int.zero).
Proof.
  clear.
  intros m vn b SE.
  erewrite same_Eval_norm; eauto.
  rewrite SE. des b; red; simpl; auto.
Qed.

Lemma norm_boolval:
  forall m v i,
    Mem.mem_norm m v = Vint i ->
    Mem.mem_norm m (Val.boolval v) = Values.Val.of_bool (negb (Int.eq i Int.zero)).
Proof.
  intros m v i N.
  apply eq_norm.
  constructor.
  - red; intros. eapply norm_ld in Pcm;[|eauto].
    unfold Val.boolval. simpl.
    inv Pcm.
    rewrite <- H1. simpl.
    destruct negb; destr; auto.
  - destruct negb; destr; intro A; inv A.
Qed.

Lemma normalise_int_notbool:
  forall m b i,
    Mem.mem_norm m b = Vint i ->
    Mem.mem_norm m (Eunop OpNotbool Tint b) = Vint (Int.notbool i).
Proof.
  intros m b i N.
  apply eq_norm.
  constructor.
  - red; intros. eapply norm_ld in Pcm;[|eauto].
    simpl.
    inv Pcm.
    rewrite <- H1. simpl. unfold Int.notbool.
    destr; auto.
  - congruence. 
Qed.

Lemma mkmem_ext:
 forall cont1 cont2 acc1 acc2 next1 next2 bt1 bt2 nbe1 nbe2
        a1 a2 b1 b2 bs1 bs2 
        mask1 mask2  Pabo1 Pabo2  comp2 comp1 vm1 vm2 vbt1 vbt2
        const1 const2 bb1 bb2 
        bli1 bli2,
   cont1=cont2 -> acc1=acc2 -> next1=next2 -> 
   bs1=bs2 -> mask1=mask2 -> bt1 = bt2 -> nbe1 = nbe2 ->
   mkmem cont1 acc1 bs1 mask1 bt1 next1 nbe1
         a1 b1 Pabo1 vm1 vbt1 
         comp1 bb1 const1 bli1 = 
   mkmem cont2 acc2 bs2 mask2 bt2 next2 nbe2
         a2 b2 Pabo2 vm2 vbt2
         comp2 bb2 const2 bli2.
Proof.
  intros. subst.
  rewrite (proof_irr a1 a2).
  rewrite (proof_irr b1 b2).
  rewrite (proof_irr Pabo1 Pabo2).
  rewrite (proof_irr vm1 vm2).
  rewrite (proof_irr vbt1 vbt2).
  rewrite (proof_irr comp1 comp2).
  rewrite (proof_irr bb1 bb2).
  rewrite (proof_irr bli1 bli2).
  rewrite (proof_irr const1 const2).
  reflexivity.
Qed.

(** * Validity of blocks and accesses *)

(** A block address is valid if it was previously allocated. It remains valid
  even after being freed. *)

Definition valid_block (m: mem) (b: block) := Plt b (nextblock m).

Definition valid_block_dec (m:mem) (b:block) : {valid_block m b} + {~ valid_block m b}.
Proof.
  unfold valid_block; apply plt.
Defined.

Theorem valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.
Proof.
  intros; red; intros. subst b'. contradiction.
Qed.

Hint Local Resolve valid_not_valid_diff: mem.

(** Permissions *)

Definition perm (m: mem) (b: block) (ofs: Z) (k: perm_kind) (p: permission) : Prop :=
   perm_order' (m.(mem_access)#b ofs k) p.

Theorem perm_implies:
  forall m b ofs k p1 p2, perm m b ofs k p1 -> perm_order p1 p2 -> perm m b ofs k p2.
Proof.
  unfold perm, perm_order'; intros.
  destruct (m.(mem_access)#b ofs k); auto.
  eapply perm_order_trans; eauto.
Qed.

Hint Local Resolve perm_implies: mem.

Theorem perm_cur_max:
  forall m b ofs p, perm m b ofs Cur p -> perm m b ofs Max p.
Proof.
  assert (forall po1 po2 p,
          perm_order' po2 p -> perm_order'' po1 po2 -> perm_order' po1 p).
  unfold perm_order', perm_order''. intros. 
  destruct po2; try contradiction.
  destruct po1; try contradiction. 
  eapply perm_order_trans; eauto.
  unfold perm; intros.
  generalize (access_max m b ofs). eauto. 
Qed.

Theorem perm_cur:
  forall m b ofs k p, perm m b ofs Cur p -> perm m b ofs k p.
Proof.
  intros. destruct k; auto. apply perm_cur_max. auto.
Qed.

Theorem perm_max:
  forall m b ofs k p, perm m b ofs k p -> perm m b ofs Max p.
Proof.
  intros. destruct k; auto. apply perm_cur_max. auto.
Qed.

Hint Local Resolve perm_cur perm_max: mem.

Theorem perm_valid_block:
  forall m b ofs k p, perm m b ofs k p -> valid_block m b.
Proof.
  unfold perm; intros. 
  destruct (plt b m.(nextblock)).
  auto.
  assert (m.(mem_access)#b ofs k = None).
  eapply nextblock_noaccess; eauto. 
  rewrite H0 in H.
  contradiction.
Qed.

Hint Local Resolve perm_valid_block: mem.

Remark perm_order_dec:
  forall p1 p2, {perm_order p1 p2} + {~perm_order p1 p2}.
Proof.
  intros. destruct p1; destruct p2; (left; constructor) || (right; intro PO; inversion PO).
Defined.

Remark perm_order'_dec:
  forall op p, {perm_order' op p} + {~perm_order' op p}.
Proof.
  intros. destruct op; unfold perm_order'.
  apply perm_order_dec.
  right; tauto.
Defined.

Theorem perm_dec:
  forall m b ofs k p, {perm m b ofs k p} + {~ perm m b ofs k p}.
Proof.
  unfold perm; intros.
  apply perm_order'_dec.
Defined.



Definition range_perm (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs k p.

Theorem range_perm_implies:
  forall m b lo hi k p1 p2,
  range_perm m b lo hi k p1 -> perm_order p1 p2 -> range_perm m b lo hi k p2.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Theorem range_perm_cur:
  forall m b lo hi k p,
  range_perm m b lo hi Cur p -> range_perm m b lo hi k p.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Theorem range_perm_max:
  forall m b lo hi k p,
  range_perm m b lo hi k p -> range_perm m b lo hi Max p.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.






Hint Local Resolve range_perm_implies range_perm_cur range_perm_max: mem.

Lemma range_perm_dec:
  forall m b lo hi k p, {range_perm m b lo hi k p} + {~ range_perm m b lo hi k p}.
Proof.
  intros. 
  induction lo using (well_founded_induction_type (Zwf_up_well_founded hi)).
  destruct (zlt lo hi).
  destruct (perm_dec m b lo k p).
  destruct (H (lo + 1)). red. omega. 
  left; red; intros. destruct (zeq lo ofs). congruence. apply r. omega. 
  right; red; intros. elim n. red; intros; apply H0; omega.
  right; red; intros. elim n. apply H0. omega. 
  left; red; intros. omegaContradiction.
Defined.

(** [valid_access m chunk b ofs p] holds if a memory access
    of the given chunk is possible in [m] at address [b, ofs]
    with current permissions [p].
    This means:
- The range of bytes accessed all have current permission [p].
- The offset [ofs] is aligned.
*)

Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) Cur p
  /\ (align_chunk chunk | ofs).

Theorem valid_access_implies:
  forall m chunk b ofs p1 p2,
  valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2.
Proof.
  intros. inv H. constructor; eauto with mem.
Qed.

Theorem valid_access_freeable_any:
  forall m chunk b ofs p,
  valid_access m chunk b ofs Freeable ->
  valid_access m chunk b ofs p.
Proof.
  intros.
  eapply valid_access_implies; eauto. constructor.
Qed.

Hint Local Resolve valid_access_implies: mem.



Theorem valid_access_valid_block:
  forall m chunk b ofs,
  valid_access m chunk b ofs Nonempty ->
  valid_block m b.
Proof.
  intros. destruct H.
  assert (perm m b ofs Cur Nonempty).
    apply H. generalize (size_chunk_pos chunk). omega.
  eauto with mem.
Qed.

Hint Local Resolve valid_access_valid_block: mem.

Lemma valid_access_perm:
  forall m chunk b ofs k p,
  valid_access m chunk b ofs p ->
  perm m b ofs k p.
Proof.
  intros. destruct H. apply perm_cur. apply H. generalize (size_chunk_pos chunk). omega.
Qed.

Lemma valid_access_compat:
  forall m chunk1 chunk2 b ofs p,
  size_chunk chunk1 = size_chunk chunk2 ->
  align_chunk chunk2 <= align_chunk chunk1 ->
  valid_access m chunk1 b ofs p->
  valid_access m chunk2 b ofs p.
Proof.
  intros. inv H1. rewrite H in H2. constructor; auto.
  eapply Zdivide_trans; eauto. eapply align_le_divides; eauto.
Qed.

Lemma valid_access_dec:
  forall m chunk b ofs p,
  {valid_access m chunk b ofs p} + {~ valid_access m chunk b ofs p}.
Proof.
  intros. 
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Cur p).
  destruct (Zdivide_dec (align_chunk chunk) ofs (align_chunk_pos chunk)).
  left; constructor; auto.
  right; red; intro V; inv V; contradiction.
  right; red; intro V; inv V; contradiction.
Defined.

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)
Definition valid_pointer (m: mem) (b: block) (ofs: Z): bool :=
  perm_dec m b ofs Cur Nonempty.

Theorem valid_pointer_nonempty_perm:
  forall m b ofs,
  valid_pointer m b ofs = true <-> perm m b ofs Cur Nonempty.
Proof.
  intros. unfold valid_pointer. 
  destruct (perm_dec m b ofs Cur Nonempty); simpl;
  intuition congruence.
Qed.

Theorem valid_pointer_valid_access:
  forall m b ofs,
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty.
Proof.
  intros. rewrite valid_pointer_nonempty_perm. 
  split; intros.
  split. simpl; red; intros. replace ofs0 with ofs by omega. auto.
  simpl. apply Zone_divide. 
  destruct H. apply H. simpl. omega.
Qed.

(** C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)

Definition weak_valid_pointer (m: mem) (b: block) (ofs: Z) :=
  valid_pointer m b ofs || valid_pointer m b (ofs - 1).

Lemma weak_valid_pointer_spec:
  forall m b ofs,
  weak_valid_pointer m b ofs = true <->
    valid_pointer m b ofs = true \/ valid_pointer m b (ofs - 1) = true.
Proof.
  intros. unfold weak_valid_pointer. now rewrite orb_true_iff.
Qed.
Lemma valid_pointer_implies:
  forall m b ofs,
  valid_pointer m b ofs = true -> weak_valid_pointer m b ofs = true.
Proof.
  intros. apply weak_valid_pointer_spec. auto.
Qed.

(** * Operations over memory stores *)

(** The initial store *)

Program Definition empty: mem :=
  mkmem (PMap.init (ZMap.init (Symbolic (Eval (Vint Int.zero)) None O)))
        (PMap.init (fun ofs k => None))
        (PMap.init None)
        (PMap.init None)
        (PMap.init None)
        1%positive O _ _ _ _ _ _ _ _ _.
Next Obligation.
  repeat rewrite PMap.gi. red; auto.
Qed.
Next Obligation.
  rewrite PMap.gi. auto.
Qed.
(* Next Obligation. *)
(*   rewrite PMap.gi.  rewrite ZMap.gi. *)
(*   simpl. exists Tint; simpl; auto. *)
(*   constructor. *)
(* Qed. *)
Next Obligation.
  repeat rewrite PMap.gi in H.
  congruence.
Qed.
Next Obligation.
  rewrite PMap.gi. auto.
Qed.
Next Obligation.
  rewrite PMap.gi. auto.
Qed.
Next Obligation.
  unfold nb_boxes_max. simpl.
  eapply (Z.lt_le_trans _ (two_power_nat 20 - 2) _). reflexivity.
  cut (two_power_nat 20 <= two_power_nat (32 - MA)). lia.
  rewrite ! two_power_nat_two_p.
  apply two_p_monotone. generalize MA_bound. lia.
Qed.
Next Obligation.
  rewrite PMap.gi in H. congruence. 
Qed.
Next Obligation.
  rewrite PMap.gi.
  reflexivity. 
Qed.
Next Obligation.
  rewrite PMap.gi in H. congruence.
Qed.

(** Reading N adjacent bytes in a block content. *)

Fixpoint getN (n: nat) (p: Z) (c: ZMap.t memval) {struct n}: list memval :=
  match n with
  | O => nil
  | S n' => ZMap.get p c :: getN n' (p + 1) c
  end.


Lemma memval_rel_lf2:
  forall mr n o t t' b,
    (forall (b0 : positive) (ofs : ZIndexed.t),
       memval_rel mr (ZMap.get ofs t !! b0)
                    (ZMap.get ofs t' !! b0)) ->
    list_forall2 (memval_rel mr)
                 (Mem.getN n o t !! b)
                 (Mem.getN n o t' !! b).
Proof.
  induction n; simpl; intros; constructor; auto.
Qed.

Lemma getN_Nlist : forall n p c, length (getN n p c) = n.
  Proof.
    induction n.
    intros; reflexivity.
    intros.
    simpl.
    rewrite IHn.
    reflexivity.
  Qed.

  


(** Writing N adjacent bytes in a block content. *)

Fixpoint setN (vl: list memval) (p: Z) (c: ZMap.t memval) {struct vl}: ZMap.t memval :=
  match vl with
  | nil => c
  | v :: vl' => setN vl' (p + 1) (ZMap.set p v c)
  end.

Remark setN_other:
  forall vl c p q,
  (forall r, p <= r < p + Z_of_nat (length vl) -> r <> q) ->
  ZMap.get q (setN vl p c) = ZMap.get q c.
Proof.
  induction vl; intros; simpl.
  auto. 
  simpl length in H. rewrite inj_S in H.
  transitivity (ZMap.get q (ZMap.set p a c)).
  apply IHvl. intros. apply H. omega.
  apply ZMap.gso. apply not_eq_sym. apply H. omega. 
Qed.

Remark setN_outside:
  forall vl c p q,
  q < p \/ q >= p + Z_of_nat (length vl) ->
  ZMap.get q (setN vl p c) = ZMap.get q c.
Proof.
  intros. apply setN_other. 
  intros. omega. 
Qed.

Remark getN_setN_same:
  forall vl p c,
  getN (length vl) p (setN vl p c) = vl.
Proof.
  induction vl; intros; simpl.
  auto.
  decEq. 
  rewrite setN_outside. apply ZMap.gss. omega. 
  apply IHvl. 
Qed.

Remark getN_exten:
  forall c1 c2 n p,
  (forall i, p <= i < p + Z_of_nat n -> ZMap.get i c1 = ZMap.get i c2) ->
  getN n p c1 = getN n p c2.
Proof.
  induction n; intros. auto. rewrite inj_S in H. simpl. decEq. 
  apply H. omega. apply IHn. intros. apply H. omega.
Qed.

Remark getN_setN_disjoint:
  forall vl q c n p,
  Intv.disjoint (p, p + Z_of_nat n) (q, q + Z_of_nat (length vl)) ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply getN_exten. intros. apply setN_other.
  intros; red; intros; subst r. eelim H; eauto. 
Qed.

Remark getN_setN_outside:
  forall vl q c n p,
  p + Z_of_nat n <= q \/ q + Z_of_nat (length vl) <= p ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply getN_setN_disjoint. apply Intv.disjoint_range. auto. 
Qed.

Remark setN_default:
  forall vl q c, fst (setN vl q c) = fst c.
Proof.
  induction vl; simpl; intros. auto. rewrite IHvl. auto. 
Qed.



Require Import Setoid.

Lemma get_setN_inside:
  forall vl ofs lo t,
    lo <= ofs < lo + Z.of_nat (length vl) ->
    Some (ZMap.get ofs (setN vl lo t)) = nth_error vl (Z.to_nat (ofs - lo)).
Proof.
  induction vl; simpl; intros.
  - omega.
  - des (zlt lo ofs).
    rewrite IHvl by (zify; omega).
    replace (Z.to_nat (ofs - lo)) with (S (Z.to_nat (ofs - (lo + 1)))).
    simpl. auto.
    zify. repeat rewrite Z2Nat.id by omega. omega.
    replace lo with ofs by omega.
    rewrite setN_outside by omega.
    rewrite ZMap.gss. 
    replace (ofs - ofs) with 0 by omega. simpl.
    reflexivity.
Qed.


Lemma same_type_memval_refl:
  forall m,
    same_type_memval m m.
Proof.
  des m.
Qed.

Lemma memval_rel_set:
  forall mr (WF: wf_mr mr) v v' o ofs t b0,
    list_forall2 (memval_rel mr) v v' ->
   memval_rel mr
     (ZMap.get ofs (setN v o t # b0))
     (ZMap.get ofs (setN v' o t # b0)).
Proof.
  intros mr WF v v' o ofs t b0 SE.  
  assert (range: forall a b c, a <= b < c \/ (a > b \/ c <= b)) by (intros; omega).
  destruct (range o ofs (o + Z.of_nat (length v))).
  + generalize (Mem.get_setN_inside _ _ _ t # b0 H).
    assert (o <= ofs < o + Z.of_nat (length v')).
    { rewrite <- (list_forall2_length SE); eauto. }
    generalize (Mem.get_setN_inside _ _ _ t # b0 H0).
    intros.
    eapply nth_error_property; eauto.
  + rewrite ! Mem.setN_outside.  unfold memval_rel; inv WF; eauto.
    split; eauto.
    left; apply same_type_memval_refl.
    rewrite <- (list_forall2_length SE); eauto. omega.
    omega.
Qed.


Lemma memval_rel_set':
  forall mr v v' ofs o t t' b b0,
    (forall b o, memval_rel mr (ZMap.get o t !! b) ( ZMap.get o t' !! b)) ->
    list_forall2 (memval_rel mr) v v' ->
    memval_rel mr
      (ZMap.get
         ofs
         (PMap.set b (Mem.setN v o t !! b) t) !! b0)
      (ZMap.get
         ofs
         (PMap.set b (Mem.setN v' o t' !! b) t') !! b0).
Proof.
  intros mr v v' ofs o t t' b b0 ME SE.
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
  + rewrite ! Mem.setN_outside.  apply ME. auto.
    rewrite <- (list_forall2_length SE); eauto. omega.
    omega.
Qed.

(** We initialise the memory of allocated blocks with the appropriate [Eundef] values.  *)

Fixpoint init_block' (n:nat) (b:block) (cur:int) : list memval :=
  match n with
      O   => (* Symbolic ((Eundef b cur)) O ::  *) nil
    | S m => Symbolic ( (Eundef b cur)) None O :: (init_block' m b (Int.add cur (Int.repr 1)))
  end.

Definition init_block (lo hi: Z) (b: block) : memval * PTree.t memval :=
  ZMap.init (Symbolic (Eval Vundef) None O).
  (* let sz := hi - lo in *)
  (* if zlt sz  0 *)
  (* then (ZMap.init (Symbolic (Eval Vundef) None O)) *)
  (* else setN (init_block' (Z.to_nat sz) b (Int.repr lo)) lo (ZMap.init (Symbolic (Eval Vundef) None O)). *)


Lemma pos_ex_index:
  forall p,
    exists z,
      ZIndexed.index z = p.
Proof.
  induction p; unfold ZIndexed.index; simpl.
  exists (Z.neg p); auto.
  exists (Z.pos p); auto.
  exists 0; auto.
Qed.

Lemma zle_zlt:
  forall a b c,
    zle a b && zlt b c = true <->
    a <= b < c.
Proof.
  unfold zle, zlt.
  intros.
  destruct (Z_le_gt_dec a b).
  destruct (Z_lt_dec b c).
  intuition omega.
  split; try discriminate; try omega.
  split; try discriminate; try omega.
Qed.

(* PW:

change this allocation algorithm. Consider only boxes of size 2^MA and count those.

Later provide a concrete memory construction from a box allocation maybe.





 *)


(* (** Run the allocation algorithm on [m] plus an hypothetical new block.  *) *)
(* Definition conc_mem_alloc (m: mem) (lo hi : Z) (alignment: nat) : *)
(*   option (block -> int) :=  *)
(*   alloc_blocks MA __szmem *)
(*     (mk_block_list_aux *)
(*        (get_size *)
(*           (PMap.set (nextblock m) (Some (0, Z.max 0 hi)) (mem_blocksize m))) *)
(*        (Pos.to_nat (nextblock m))). *)



(* Definition alloc_mem_dec: *)
(*   forall sz l , *)
(*     {alloc_blocks MA sz l <> None} + {alloc_blocks MA sz l = None}. *)
(* Proof. *)
(*   unfold alloc_blocks. intros. *)
(*   destruct (alloc_mem_aux MA l). *)
(*   destruct (zlt z sz). *)
(*   left; congruence. *)
(*   right; reflexivity. *)
(* Defined. *)

(* Definition conc_mem_alloc_dec (m:mem) (lo hi: Z) (alignment: nat) :  *)
(*   {conc_mem_alloc m lo hi alignment <> None} + *)
(*   {conc_mem_alloc m lo hi alignment = None}. *)
(* Proof. *)
(*   unfold conc_mem_alloc. *)
(*   apply alloc_mem_dec. *)
(* Defined. *)

Lemma maxspec:
  forall (n m: nat),
    max n m = if lt_dec n m then m else n.
Proof.
  intros.
  generalize (Max.max_spec n m).
  repeat destr. lia.
Qed.

Lemma minspec:
  forall (n m: nat),
    min n m = if lt_dec n m then n else m.
Proof.
  intros.
  generalize (Min.min_spec n m).
  repeat destr. lia.
Qed.

Lemma alignment_of_size_bnd sz:
  (alignment_of_size sz <= 3)%nat.
Proof.
  unfold alignment_of_size; repeat destr; lia.
Qed.

Opaque min max.
(** The allocation is now guarded by the success of [conc_mem_alloc].  *)
Program Definition low_alloc (m: mem) (lo hi: Z) (al: nat) bt : option (mem * block) :=
  let lo := 0 in 
  let al := (min MA (max al (alignment_of_size (hi-lo)))) in
  if zlt (Z.of_nat (nb_boxes_used_m m + box_span (Z.max 0 hi))) nb_boxes_max
  then
    Some (mkmem (PMap.set m.(nextblock) 
                              (init_block lo hi m.(nextblock))
                              m.(mem_contents))
                (PMap.set m.(nextblock)
                              (fun ofs k => if zle lo ofs && zlt ofs hi then Some Freeable else None)
                              m.(mem_access))
                (PMap.set m.(nextblock)
                              (Some (0,Z.max 0 hi))
                              m.(mem_blocksize))
                (PMap.set m.(nextblock)
                              (Some al)
                              m.(mem_mask))
                (PMap.set m.(nextblock)
                              (Some bt)
                              m.(mem_blocktype))
                (Psucc m.(nextblock)) (nb_extra m)
                _ _ _ _ _ _ _ _ _,
          m.(nextblock))
  else None.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b (nextblock m)). 
  subst b. destruct (zle 0 ofs && zlt ofs hi); red; auto with mem. 
  apply access_max. 
Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b (nextblock m)). 
  subst b. elim H0. apply Plt_succ. 
  apply nextblock_noaccess. red; intros; elim H0. 
  apply Plt_trans_succ; auto.
Qed.
(* Next Obligation. *)
(*   rewrite PMap.gsspec. *)
(*   destruct (peq b (nextblock m)). *)
(*   subst. *)
(*   apply init_block_wt_memval'. *)
(*   apply contents_wt_memval. *)
(* Qed. *)
Next Obligation.
  unfold get_bounds. 
  repeat rewrite PMap.gsspec in *.
  destruct (peq b (nextblock m)); subst.
  unfold in_bound; simpl.
  destruct (zle 0 ofs && zlt ofs hi) eqn:?; try congruence.
  apply zle_zlt in Heqb. rewrite Zmax_spec. destr.  lia. 
  eapply access_bounds_ok; eauto.
Qed.
Next Obligation.
  rewrite PMap.gsspec.
  destr. subst. xomega.
  apply msk_valid; auto. xomega. 
Qed.
Next Obligation.
  rewrite PMap.gsspec.
  destr. subst. xomega.
  apply blocktype_valid; auto. xomega. 
Qed.
Next Obligation.
  erewrite mk_block_list_aux_eq. 2: apply MA_bound.
  unfold nb_boxes_used_m, nb_boxes_used in *; simpl in *.
  rewrite fold_left_plus_rew.
  eapply Z.le_lt_trans. 2: eauto.
  rewrite Z.sub_0_r. unfold mk_block_list.
  rewrite <- ! plus_assoc. rewrite (plus_comm (nb_extra _)).
  apply Z.le_refl.
Qed.
Next Obligation.
  unfold get_size.
  rewrite PMap.gsspec in *.
  des (peq b (nextblock m)); split.
  - inv H0. apply Min.le_min_l.
  - inv H0. clear H.
    rewrite Zmax_spec.
    rewrite ! Z.sub_0_r.
    destr. unfold alignment_of_size.
    des (zlt 0 2); lia.
    generalize MA_bound (alignment_of_size_bnd hi).
    rewrite minspec, maxspec.
    repeat destr; try destr_in l; try lia.
  - revert H0; apply alignment_ok.
  - revert H0; apply alignment_ok.
Qed.
Next Obligation.
  rewrite ! PMap.gsspec in *.
  des (peq b (nextblock m)).
  eapply bounds_mask_consistency; eauto.
Qed.
Next Obligation.
  rewrite ! PMap.gsspec in *.
  destruct (peq b (nextblock m)). inv H0; split; auto.
  apply Z.le_ge. apply Z.le_max_l.
  apply bounds_lo_inf0 in H0; auto.
Qed.

Definition alloc (m: mem) (lo hi: Z) bt :=
  low_alloc m lo hi (alignment_of_size hi) bt.

Lemma alloc_nat_mask:
  forall m lo hi m' b bt,
    Mem.alloc m lo hi bt = Some (m',b) ->
    Mem.nat_mask m' b = Int.not (Int.repr (two_power_nat (alignment_of_size hi) - 1)).
Proof.
  intros m lo hi m' b bt ALLOC.
  Transparent Mem.alloc Mem.low_alloc.
  unfold Mem.alloc, Mem.low_alloc in ALLOC.
  destr_in ALLOC.
  inv ALLOC.
  unfold Mem.nat_mask, Mem.mask. simpl.
  rewrite PMap.gss. rewrite Z.sub_0_r in *; auto.
  rewrite Max.max_idempotent. rewrite Min.min_r. auto.
  generalize MA_bound (alignment_of_size_bnd hi); lia. 
Qed.

Lemma alloc_contents:
  forall m lo hi m' b bt,
    alloc m lo hi bt = Some (m',b) ->
    forall b', b <> b' ->
          (mem_contents m') !! b' = (mem_contents m) !! b'.
Proof.
  intros m lo hi m' b bt ALLOC b' DIFF.
  unfold Mem.alloc, Mem.low_alloc in ALLOC.
  destr_in ALLOC.
  inv ALLOC. simpl.
  rewrite PMap.gso; auto. 
Qed.

Require Import Tactics.

Lemma box_span_le:
  forall x y, 0 <= x <= y ->
         (box_span x <= box_span y)%nat.
Proof.
  intros.
  apply Nat2Z.inj_le.
  apply (Z.mul_le_mono_pos_l _ _ _ (Zgt_lt _ _ (two_power_nat_pos MA))).
  rewrite ! box_span_align by lia.
  apply align_add; try lia. apply tpMA_pos.
Qed.

Lemma nb_boxes_used_le:
  forall l l',
    list_forall2 (fun x x' => 0 <= snd x <= snd x') l l' ->
    (nb_boxes_used l <= nb_boxes_used l')%nat.
Proof.
  unfold nb_boxes_used. induction 1; simpl; intros; eauto.
  repeat destr.
  rewrite ! (fold_left_plus_rew _ (box_span _)).
  apply box_span_le in H. lia.
Qed.

Lemma mbla_le:
  forall sz sz' (SZspec: forall b, 0 <= sz b <= sz' b) n,
   list_forall2 (fun x x' : block * Z => 0 <= snd x <= snd x')
     (mk_block_list_aux sz n)
     (mk_block_list_aux sz' n).
Proof.
  induction n; simpl; intros.
  constructor.
  rewrite ! mbla_rew. constructor; auto.
  simpl. auto.
Qed.


(** Freeing a block between the given bounds. *)
(** We only free the block when [lo] and [hi] corresponds to the exact bounds of [b]. *)
Opaque zeq. 
Program Definition unchecked_free (m: mem) (b: block) (lo hi: Z): mem :=
  mkmem m.(mem_contents)
            (PMap.set b 
                      (fun ofs k => if zle lo ofs && zlt ofs hi then None else m.(mem_access)#b ofs k)
                      m.(mem_access))
            (PMap.set b (match m.(mem_blocksize)#b with
                             Some (l,h) => if zeq l lo && zeq h hi then
                                             None
                                           else m.(mem_blocksize)#b
                           | None => None
                      end)
                      m.(mem_blocksize))
            m.(mem_mask)
            m.(mem_blocktype)
            m.(nextblock) (nb_extra m) _ _ _ _ _ _ _ _ _ .
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b).
  destruct (zle lo ofs && zlt ofs hi). red; auto. apply access_max. 
  apply access_max.
Qed.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b). subst.
  destruct (zle lo ofs && zlt ofs hi). auto. apply nextblock_noaccess; auto.
  apply nextblock_noaccess; auto.
Qed.
(* Next Obligation. *)
(*   apply contents_wt_memval. *)
(* Qed. *)
Next Obligation.  
  unfold get_bounds in *.
  repeat rewrite PMap.gsspec in *. repeat destr_in H. 
  - generalize H; intro H1.
    apply access_bounds_ok in H; auto.
    destr; repeat destr_in Heqo; inv Heqo. unfold get_bounds in H; rewrite Heqo0 in H. auto.
    unfold get_bounds in H; rewrite Heqo0 in H.
    unfold in_bound in *. simpl in *.
    des (zeq z lo); des (zeq z0 hi).
    des (zle lo ofs); des (zlt ofs hi).
    unfold get_bounds in H; rewrite Heqo0 in H. auto.
  - eapply access_bounds_ok; eauto.
Qed.
Next Obligation.
  rewrite msk_valid; auto.
Qed.
Next Obligation.
  rewrite blocktype_valid; auto.
Qed.
Next Obligation.
  eapply Z.le_lt_trans. 2: apply wfm_alloc_ok.
  rewrite ! Nat2Z.inj_add.
  apply Z.add_le_mono_r.
  apply inj_le.
  apply nb_boxes_used_le.
  apply mbla_le. unfold get_size. simpl; intros.
  rewrite PMap.gsspec.
  destr.
  - subst. repeat destr.
    destr_in Heqo. inv Heqo. eapply bounds_lo_inf0 in Heqo0. lia.
    eapply bounds_lo_inf0 in Heqo0. lia. lia.
  - destr. destr. eapply bounds_lo_inf0 in Heqo. lia. lia.
Qed.
Next Obligation.
  unfold get_size. rewrite PMap.gsspec.
  destruct (peq b0 b); subst; auto;
  try eapply alignment_ok; eauto.
  apply alignment_ok in H; eauto.
  destruct H; split; auto.
  unfold get_size in H0.
  destruct (mem_blocksize m) #b eqn:?; try omega.
  destruct p.
  destruct (zeq z lo && zeq z0 hi). change (alignment_of_size 0) with O. omega.
  auto.
Qed.
Next Obligation.
  revert H.
  rewrite PMap.gsspec.
  des (peq b0 b); intros.
  - eapply bounds_mask_consistency in H; eauto.
    rewrite H. auto.
  - eapply bounds_mask_consistency; eauto. 
Qed.
Next Obligation.
  revert H.
  rewrite PMap.gsspec.
  destruct (peq b0 b).
  - destruct (mem_blocksize m) # b eqn:?; try easy.
    destruct p. destr_cond_match; intro A; inv A. 
    apply bounds_lo_inf0 in Heqo; eauto. 
  - apply bounds_lo_inf0; auto.
Qed.

Lemma unchecked_free_mask:
  forall m b lo hi b',
    mask (unchecked_free m b lo hi) b' =
    mask m b'.
Proof.
  intros. 
  Opaque zeq.
  unfold unchecked_free, mask, eq_block; simpl.
  reflexivity.
Qed.

Lemma unchecked_free_nat_mask:
  forall m b lo hi b',
    nat_mask (unchecked_free m b lo hi) b' =
    nat_mask m b'.
Proof.
  intros. reflexivity.
Qed.

Definition has_bounds m b lo hi :=
  let (lo',hi') := Mem.bounds_of_block m b in
  if zeq lo lo' && zeq hi hi' then true else false.

Definition free (m: mem) (b: block) (lo hi: Z): option mem :=
  if range_perm_dec m b lo hi Cur Freeable 
  then if has_bounds m b lo hi
       then Some (unchecked_free m b lo hi)
       else None
  else None.


Lemma free_bounds:
  forall b lo hi m m1 m' m1'
         (SB: Mem.mem_blocksize m = Mem.mem_blocksize m1)
         (FL : Mem.free m1 b lo hi = Some m')
         (FL' : Mem.free m b lo hi = Some m1'),
    Mem.mem_blocksize m' = Mem.mem_blocksize m1'.
Proof.
  intros b lo hi m m1 m' m1' SB FL FL'.
  unfold Mem.free, Mem.unchecked_free in *.
  repeat destr_in FL. repeat destr_in FL'. inv FL; inv FL'; simpl.
  rewrite SB. reflexivity.
Qed.

Lemma unchecked_free_bounds:
  forall b lo hi m m1
         (SB: Mem.mem_blocksize m = Mem.mem_blocksize m1),
    Mem.mem_blocksize (Mem.unchecked_free m1 b lo hi) = Mem.mem_blocksize (Mem.unchecked_free m b lo hi).
Proof.
  intros b lo hi m m1 SB.
  unfold Mem.unchecked_free in *.
  intros. simpl. 
  rewrite SB. reflexivity.
Qed.


Lemma free_contents:
  forall m b lo hi m',
    Mem.free m b lo hi = Some m' ->
    Mem.mem_contents m' = Mem.mem_contents m.
Proof.
  Transparent Mem.free.
  unfold Mem.free.
  simpl.
  intros.
  repeat destr_in H; inv H; simpl; auto. 
Qed.


Fixpoint free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

Lemma bounds_of_block_valid:
  forall m b lo hi,
    bounds_of_block m b = (lo,hi) ->
    lo <> hi ->
    valid_block m b.
Proof.
  intros.
  destruct (valid_block_dec m b); auto.
  unfold bounds_of_block in H.
  rewrite bs_valid in H; auto. inv H; congruence.
Qed.


Lemma size_mem_aux_sup1:
  forall m,
    Alloc.size_mem_aux MA m >= two_power_nat MA.
Proof.
  unfold Alloc.size_mem_aux.
  intros.
  apply Zle_ge.
  apply Alloc.size_mem_al_pos. apply two_power_nat_pos. generalize (two_power_nat_pos MA); omega.
Qed.


(** Memory reads. *)

(** [load chunk m b ofs] perform a read in memory state [m], at address
  [b] and offset [ofs].  It returns the value of the memory chunk
  at that address.  [None] is returned if the accessed bytes
  are not readable. *)

Definition load (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z): option expr_sym :=
  if valid_access_dec m chunk b ofs Readable
  then Some (decode_val chunk (getN (size_chunk_nat chunk) ofs (m.(mem_contents)#b)))
  else None.

(** [loadv chunk m addr] is similar, but the address and offset are given as a
     single value [addr], which must be a pointer value.  
     We normalise the address beforehand.  *)

Definition loadv (chunk: memory_chunk) (m: mem) (addr: expr_sym) : option expr_sym :=
  match mem_norm m addr with 
    Vptr b ofs => load chunk m b (Int.unsigned ofs)
  | _ => None
  end.

(** [loadbytes m b ofs n] reads [n] consecutive bytes starting at
  location [(b, ofs)].  Returns [None] if the accessed locations are
  not readable. *)

Definition loadbytes (m: mem) (b: block) (ofs n: Z): option (list memval) :=
  if range_perm_dec m b ofs (ofs + n) Cur Readable
  then Some (getN (nat_of_Z n) ofs (m.(mem_contents)#b))
  else None.



(** Memory stores. *)

(** [store chunk m b ofs v] perform a write in memory state [m].
  Value [v] is stored at address [b] and offset [ofs].
  Return the updated memory store, or [None] if the accessed bytes
  are not writable. *)

Program Definition store (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: expr_sym): option mem :=
  if valid_access_dec m chunk b ofs Writable then
      Some (mkmem (PMap.set b 
                            (setN (encode_val chunk v) ofs (m.(mem_contents)#b))
                            m.(mem_contents))
                  m.(mem_access)
                      m.(mem_blocksize)
                          m.(mem_mask)
                              m.(mem_blocktype)
                              m.(nextblock) (nb_extra m)
                                  _ _ _ _ _ _ _ _ _ )
  else
    None.
Next Obligation. apply access_max. Qed.
Next Obligation. apply nextblock_noaccess; auto. Qed.
Next Obligation.
  apply access_bounds_ok in H0; auto.
Qed.
Next Obligation.
  destruct m. simpl. auto.
Qed.
Next Obligation.
  destruct m. simpl. auto.
Qed.
Next Obligation.
  destruct m. simpl. auto.
Qed.
Next Obligation.
  destruct m. simpl. auto.
Qed.
Next Obligation.
  destruct m. simpl. eauto.
Qed.
Next Obligation.
  destruct m. simpl. eauto.
Qed.

(** [storev chunk m addr v] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. We normalise the address beforehand. *)

Definition storev (chunk: memory_chunk) (m: mem) (addr v: expr_sym) : option mem :=
  match mem_norm m addr with
      Vptr b ofs => store chunk m b (Int.unsigned ofs) v
    | _ => None
  end.

(** [storebytes m b ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)

Program Definition storebytes (m: mem) (b: block) (ofs: Z) (bytes: list memval) : option mem :=
    if range_perm_dec m b ofs (ofs + Z_of_nat (length bytes)) Cur Writable then
      Some (mkmem
              (PMap.set b (setN bytes ofs (m.(mem_contents)#b)) m.(mem_contents))
              m.(mem_access)
                  m.(mem_blocksize)
                      m.(mem_mask)
                          m.(mem_blocktype)
                          m.(nextblock) (nb_extra m)
                              _ _ _ _ _ _ _ _ _)
  else
    None.
Next Obligation. apply access_max. Qed.
Next Obligation. apply nextblock_noaccess; auto. Qed.
Next Obligation.
  apply access_bounds_ok in H0; auto.
Qed.
Next Obligation.
  destruct m. simpl. auto.
Qed.
Next Obligation.
  destruct m. simpl. auto.
Qed.
Next Obligation.
  destruct m. simpl. auto.
Qed.
Next Obligation.
  destruct m. simpl. auto.
Qed.
Next Obligation.
  destruct m. simpl. eauto.
Qed.
Next Obligation.
  destruct m. simpl in *. eauto.
Qed.

(** [drop_perm m b lo hi p] sets the max permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have current permissions
    [Freeable] in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

Program Definition drop_perm (m: mem) (b: block) (lo hi: Z) (p: permission): option mem :=
  if range_perm_dec m b lo hi Cur Freeable then
    Some (mkmem m.(mem_contents)
                (PMap.set b
                        (fun ofs k => if zle lo ofs && zlt ofs hi then Some p else m.(mem_access)#b ofs k)
                        m.(mem_access))
                m.(mem_blocksize)
                    m.(mem_mask)
                        m.(mem_blocktype)
                            m.(nextblock)
                                (nb_extra m)
                                _ _ _ _ _ _ _ _ _)
  else None.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b). subst b0.
  destruct (zle lo ofs && zlt ofs hi). red; auto with mem. apply access_max. 
  apply access_max.
Qed.
Next Obligation.
  specialize (nextblock_noaccess m b0 ofs k H0). intros. 
  rewrite PMap.gsspec. destruct (peq b0 b). subst b0.
  destruct (zle lo ofs). destruct (zlt ofs hi).
  assert (perm m b ofs k Freeable). apply perm_cur. apply H; auto. 
  unfold perm in H2. rewrite H1 in H2. contradiction.
  auto. auto. auto. 
Qed.
Next Obligation.
  repeat rewrite PMap.gsspec in *.
  repeat destr_in H0.
  unfold range_perm in H.
  unfold perm, perm_order' in H.
  apply zle_zlt in Heqb0. apply H in Heqb0. destr_in Heqb0.
  eapply access_bounds_ok. instantiate (1:=Cur); rewrite Heqo; eauto. destr.
  eapply access_bounds_ok in H0; eauto.
  eapply access_bounds_ok in H0; eauto.
Qed.
Next Obligation.
  destruct m. simpl. auto.
Qed.
Next Obligation.
  destruct m. simpl. auto.
Qed.
Next Obligation.
  destruct m. simpl. auto.
Qed.
Next Obligation.
  destruct m. simpl. eauto.
Qed.
Next Obligation.
  destruct m. simpl. eauto.
Qed.
Next Obligation.
  destruct m. simpl in *. eauto.
Qed.

Definition drop_perm_list m (bl: list (block * Z * Z)) p :=
  fold_right (fun (elt: block*Z*Z) m =>
                let (blo,hi) := elt in
                let (b,lo) := blo in
                match m with
                  None => None
                | Some m => drop_perm m b lo hi p
                end) (Some m) bl.

(** * Properties of the memory operations *)
(** Properties of the empty store. *)

Theorem nextblock_empty: nextblock empty = 1%positive.
Proof. reflexivity. Qed.

Theorem perm_empty: forall b ofs k p, ~perm empty b ofs k p.
Proof. 
  intros. unfold perm, empty; simpl. rewrite PMap.gi. simpl. tauto. 
Qed.

Theorem valid_access_empty: forall chunk b ofs p, ~valid_access empty chunk b ofs p.
Proof.
  intros. red; intros. elim (perm_empty b ofs Cur p). apply H. 
  generalize (size_chunk_pos chunk); omega.
Qed.

(** ** Properties related to [load] *)

Lemma Forall_rib:
  forall {A} (P : A -> Prop) l,
    Forall P l ->
    Forall P (rev_if_be l).
Proof.
  unfold rev_if_be; destr_cond_match; intuition try congruence.
  apply Forall_rev.
  rewrite rev_involutive; auto.
Qed.

Theorem valid_access_load:
  forall m chunk b ofs,
  valid_access m chunk b ofs Readable ->
  exists v, load chunk m b ofs = Some v.
Proof.
  intros. unfold load.
  rewrite pred_dec_true; eauto.
Qed.

Theorem load_valid_access:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs Readable.
Proof.
  intros until v. unfold load. 
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  auto. 
  congruence.
Qed.

Lemma load_result:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  v = decode_val chunk (getN (size_chunk_nat chunk) ofs (m.(mem_contents)#b)).
Proof.
  intros until v. unfold load. 
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  congruence.
  congruence.
Qed.




Lemma load_int64_eq_add:
  forall m b i v , 
    Mem.load Mint64 m b (Int.unsigned i) = Some v ->
    Int.unsigned (Int.add i (Int.repr 4)) = Int.unsigned i + 4.
Proof.
  intros.
  rewrite Int.add_unsigned. rewrite Int.unsigned_repr. auto.
  exploit Mem.load_valid_access. eexact H. intros [P Q]. simpl in Q.
  exploit (Zdivide_interval (Int.unsigned i) Int.modulus 8).
  omega. apply Int.unsigned_range. auto. exists (two_p (32-3)); reflexivity. 
  change (Int.unsigned (Int.repr 4)) with 4. unfold Int.max_unsigned. omega. 
Qed.

Hint Local Resolve load_valid_access valid_access_load: mem.

Theorem load_type:
  forall m chunk b ofs v,
    load chunk m b ofs = Some v ->
    wt v (type_of_chunk chunk).
Proof.
  intros. exploit load_result; eauto; intros.
  subst.
  eapply decode_val_type; eauto.
Qed.

Lemma loadv_type:
  forall m c a v (L: Mem.loadv c m a = Some v), wt v (type_of_chunk c).
Proof.
  unfold Mem.loadv; intros.
  des (Mem.mem_norm m a).
  eapply Mem.load_type; eauto.
Qed.

Theorem load_cast:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  match chunk with
  | Mint8signed => same_eval v (Val.sign_ext 8 v)
  | Mint8unsigned => same_eval v (Val.zero_ext 8 v)
  | Mint16signed => same_eval v (Val.sign_ext 16 v)
  | Mint16unsigned => same_eval v (Val.zero_ext 16 v)
  | Mint32 => same_eval v (Val.sign_ext 32 v)
  | _ => True
  end.
Proof.
  intros. exploit load_result; eauto.
  set (l := getN (size_chunk_nat chunk) ofs m.(mem_contents)#b).
  intro; subst.
  generalize (decode_val_cast chunk l).
  des chunk; simpl.
  red; intros; seval. rewrite Int.sign_ext_above; auto. unfsize. lia.
Qed.

Theorem load_int8_signed_unsigned:
  forall m b ofs v1 v2,
  load Mint8signed m b ofs = Some v1 ->
  option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs) = Some v2 ->
  same_eval v1 v2.
Proof.
  intros until v2. unfold load.
  change (size_chunk_nat Mint8signed) with (size_chunk_nat Mint8unsigned).
  set (cl := getN (size_chunk_nat Mint8unsigned) ofs m.(mem_contents)#b).
  destruct (valid_access_dec m Mint8signed b ofs Readable); try discriminate.
  rewrite pred_dec_true; auto. unfold decode_val. simpl.
  intros A B; inv A; inv B.
  red; simpl; intros; auto.
  destr.
  seval.
  rewrite Int.sign_ext_zero_ext; auto; omega.
Qed.

Theorem load_int8_signed_unsigned_none:
  forall m b ofs,
    load Mint8signed m b ofs = None ->
    load Mint8unsigned m b ofs = None.
Proof.
  intros m b ofs.
  unfold load.
  destr.
  rewrite pred_dec_false; auto.
Qed.

Theorem load_int16_signed_unsigned:
  forall m b ofs v1 v2,
  load Mint16signed m b ofs = Some v1 ->
  option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs) = Some v2 ->
  same_eval v1 v2.
Proof.
  intros until v2. unfold load.
  change (size_chunk_nat Mint16signed) with (size_chunk_nat Mint16unsigned).
  set (cl := getN (size_chunk_nat Mint16unsigned) ofs m.(mem_contents)#b).
  destruct (valid_access_dec m Mint16signed b ofs Readable).
  - rewrite pred_dec_true; auto. unfold decode_val. 
    red; intros A B; inv A; inv B. simpl; intros. 
    seval.
    rewrite Int.sign_ext_zero_ext; auto; omega.
  - rewrite pred_dec_false; auto. destr.
Qed.

Theorem load_int16_signed_unsigned_none:
  forall m b ofs,
    load Mint16signed m b ofs = None ->
    load Mint16unsigned m b ofs = None.
Proof.
  intros m b ofs.
  unfold load.
  destr. rewrite pred_dec_false; auto.
Qed.

(** ** Properties related to [loadbytes] *)

Theorem range_perm_loadbytes:
  forall m b ofs len,
  range_perm m b ofs (ofs + len) Cur Readable ->
  exists bytes, loadbytes m b ofs len = Some bytes.
Proof.
  intros. econstructor. unfold loadbytes. rewrite pred_dec_true; eauto. 
Qed.

Theorem loadbytes_range_perm:
  forall m b ofs len bytes,
  loadbytes m b ofs len = Some bytes ->
  range_perm m b ofs (ofs + len) Cur Readable.
Proof.
  intros until bytes. unfold loadbytes.
  destruct (range_perm_dec m b ofs (ofs + len) Cur Readable). auto. congruence.
Qed.

Theorem loadbytes_load:
  forall chunk m b ofs bytes,
  loadbytes m b ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs = Some (decode_val chunk bytes).
Proof.
  unfold loadbytes, load; intros. 
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Cur Readable);
  try congruence.
  inv H. rewrite pred_dec_true. auto. 
  split; auto.
Qed.

Theorem load_loadbytes:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes
             /\ v = decode_val chunk bytes.
Proof.
  intros. exploit load_valid_access; eauto. intros [A B].
  exploit load_result; eauto. intros. 
  exists (getN (size_chunk_nat chunk) ofs m.(mem_contents)#b); split.
  unfold loadbytes. rewrite pred_dec_true; auto. 
  auto.
Qed.

Lemma getN_length:
  forall c n p, length (getN n p c) = n.
Proof.
  induction n; simpl; intros. auto. decEq; auto.
Qed.

Theorem loadbytes_length:
  forall m b ofs n bytes,
  loadbytes m b ofs n = Some bytes ->
  length bytes = nat_of_Z n.
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + n) Cur Readable); try congruence.
  inv H. apply getN_length.
Qed.

Theorem loadbytes_empty:
  forall m b ofs n,
  n <= 0 -> loadbytes m b ofs n = Some nil.
Proof.
  intros. unfold loadbytes. rewrite pred_dec_true. rewrite nat_of_Z_neg; auto.
  red; intros. omegaContradiction.
Qed.



Lemma getN_concat:
  forall c n1 n2 p,
  getN (n1 + n2)%nat p c = getN n1 p c ++ getN n2 (p + Z_of_nat n1) c.
Proof.
  induction n1; intros.
  simpl. decEq. omega.
  rewrite inj_S. simpl. decEq.
  replace (p + Zsucc (Z_of_nat n1)) with ((p + 1) + Z_of_nat n1) by omega.
  auto. 
Qed.

Theorem loadbytes_concat:
  forall m b ofs n1 n2 bytes1 bytes2,
  loadbytes m b ofs n1 = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) = Some(bytes1 ++ bytes2).
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + n1) Cur Readable); try congruence.
  destruct (range_perm_dec m b (ofs + n1) (ofs + n1 + n2) Cur Readable); try congruence.
  rewrite pred_dec_true. rewrite nat_of_Z_plus; auto.
  rewrite getN_concat. rewrite nat_of_Z_eq; auto.
  congruence.
  red; intros. 
  assert (ofs0 < ofs + n1 \/ ofs0 >= ofs + n1) by omega.
  destruct H4. apply r; omega. apply r0; omega.
Qed.

Theorem loadbytes_split:
  forall m b ofs n1 n2 bytes,
  loadbytes m b ofs (n1 + n2) = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 = Some bytes1 
  /\ loadbytes m b (ofs + n1) n2 = Some bytes2
  /\ bytes = bytes1 ++ bytes2.
Proof.
  unfold loadbytes; intros. 
  destruct (range_perm_dec m b ofs (ofs + (n1 + n2)) Cur Readable);
  try congruence.
  rewrite nat_of_Z_plus in H; auto. rewrite getN_concat in H.
  rewrite nat_of_Z_eq in H; auto. 
  repeat rewrite pred_dec_true.
  econstructor; econstructor.
  split. reflexivity. split. reflexivity. congruence.
  red; intros; apply r; omega.
  red; intros; apply r; omega.
Qed.

Lemma Forall_dec:
  forall {A} (P: A -> Prop)
         (Pdec: forall a, P a \/ ~ P a) 
         l,
    Forall P l \/ ~ Forall P l.
Proof.
  induction l; simpl; intros.
  left; constructor.
  destruct (Pdec a); destruct IHl; intuition try congruence.
  left; constructor; auto.
  right; intro C; inv C; congruence.
  right; intro C; inv C; congruence.
  right; intro C; inv C; congruence.
Qed.

Lemma Forall_app_l:
  forall {A} (P: A -> Prop) l1 l2,
    Forall P (l1 ++ l2) ->
    Forall P l1.
Proof.
  induction l1; try constructor.
  change ((a::l1)++ l2) with (a:: (l1 ++ l2)) in H.
  inv H; auto.
  change ((a::l1)++ l2) with (a:: (l1 ++ l2)) in H.
  inv H; auto.
  apply IHl1 with (l2:=l2); auto.
Qed.

Lemma Forall_rev':
  forall {A} (P: A -> Prop) l,
    Forall P l ->
    Forall P (rev l).
Proof.
  intros; apply Forall_rev.
  rewrite rev_involutive; auto.
Qed.

Lemma Forall_app_r:
  forall {A} (P: A -> Prop) l1 l2,
    Forall P (l1 ++ l2) ->
    Forall P l2.
Proof.
  intros.
  apply Forall_rev' in H.
  rewrite rev_app_distr in H.
  apply Forall_app_l in H.
  apply Forall_rev; auto.
Qed.

Theorem load_int64_split:
  forall m b ofs v,
  load Mint64 m b ofs = Some v ->
  exists v1 v2,
     load Mint32 m b ofs = Some (if Archi.big_endian then v1 else v2)
  /\ load Mint32 m b (ofs + 4) = Some (if Archi.big_endian then v2 else v1)
  /\ same_eval v (Val.longofwords v1 v2).
Proof.
  Opaque decode_val.
  intros. 
  exploit load_valid_access; eauto. intros [A B]. simpl in *.
  exploit load_loadbytes. eexact H. simpl. intros [bytes [LB EQ]]. 
  change 8 with (4 + 4) in LB. 
  exploit loadbytes_split. eexact LB. omega. omega. 
  intros (bytes1 & bytes2 & LB1 & LB2 & APP). 
  change 4 with (size_chunk Mint32) in LB1.
  exploit loadbytes_load. eexact LB1.
  simpl. apply Zdivides_trans with 8; auto. exists 2; auto.
  intros L1.
  change 4 with (size_chunk Mint32) in LB2.
  exploit loadbytes_load. eexact LB2.
  simpl. apply Zdivide_plus_r. apply Zdivides_trans with 8; auto. exists 2; auto. exists 1; auto.
  intros L2.
  rewrite L1.
  simpl in L2.
  rewrite L2.
  rewrite APP in EQ.
  exists (if Archi.big_endian then decode_val Mint32 bytes1 else decode_val Mint32 bytes2).
  exists (if Archi.big_endian then decode_val Mint32 bytes2 else decode_val Mint32 bytes1).
  split. destruct Archi.big_endian; auto.
  split. destruct Archi.big_endian; auto. subst.
  rewrite decode_val_int64; auto.
  constructor; simpl; intros; auto.
  rewrite (loadbytes_length m b ofs (size_chunk Mint32)); auto.
  rewrite (loadbytes_length m b (ofs+size_chunk Mint32) (size_chunk Mint32)); auto.
Qed. 

Lemma perm_bounds:
  forall m b ofs p k,
    Mem.perm m b ofs k p ->
    in_bound_m ofs m b.
Proof.
  unfold Mem.perm, Mem.perm_order'.
  intros.
  destruct ((Mem.mem_access m) !! b ofs k) eqn:?; intuition try congruence.
  generalize (Mem.access_bounds_ok m b ofs k).
  rewrite Heqo.
  intros. unfold in_bound_m, Mem.bounds_of_block, get_bounds.
  destruct ((Mem.mem_blocksize m) !! b) eqn:?; eauto.
  destruct p1.
  unfold get_bounds in H0.
  rewrite Heqo0 in H0.
  apply H0; congruence.
  unfold get_bounds in H0.
  rewrite Heqo0 in H0.
  exfalso; exploit H0; eauto. congruence. unfold in_bound. simpl. omega. 
Qed.



Lemma range_perm_bounds:
  forall m b o1 o2 k p
    (RP: Mem.range_perm m b o1 o2 k p)
    ofs
    (OFS: o1 <= ofs < o2),
    in_bound ofs (Mem.bounds_of_block m b).
Proof.
  intros.
  apply RP in OFS.
  eapply Mem.perm_bounds; eauto.
Qed.

Lemma range_perm_bounds':
  forall m b o1 o2 k p
    (RP: Mem.range_perm m b o1 o2 k p)
    (OFS: o1 < o2),
    let (z0,z1) := Mem.bounds_of_block m b in
    z0 <= o1 /\ o2 <= z1.
Proof.
  intros.
  generalize (range_perm_bounds _ _ _ _ _ _ RP o1).
  generalize (range_perm_bounds _ _ _ _ _ _ RP (o2-1)).
  intros A B; trim A. lia. trim B. lia.
  destr; unfold in_bound in *; simpl in *; lia.
Qed.


Lemma loadv_int64_split:
  forall m a v,
  Mem.loadv Mint64 m a = Some v ->
  exists v1 v2,
     Mem.loadv Mint32 m a = Some (if Archi.big_endian then v1 else v2)
  /\ Mem.loadv  Mint32 m (Val.add a (Eval (Vint (Int.repr 4)))) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef (Val.hiword v) v1
  /\ Val.lessdef (Val.loword v) v2.
Proof.
  intros.
  revert H; unfold Mem.loadv. des (Mem.mem_norm m a).
  cut (Mem.mem_norm m (Val.add a (Eval (Vint (Int.repr 4)))) =
       Vptr b (Int.add i (Int.repr 4))).
  intro A; rewrite A. intros.
  replace (Int.unsigned (Int.add i (Int.repr 4))) with (Int.unsigned i + 4). intros.
  exploit Mem.load_int64_split; eauto. intros (v1 & v2 & B & C & D).
  exists v1, v2. split; auto. split; auto.
  split; red; intros; simpl; rewrite D; simpl; seval; auto.
  rewrite Int64.hi_ofwords; auto. rewrite Int64.lo_ofwords; auto.
  erewrite load_int64_eq_add; eauto.
  apply eq_norm; try congruence.
  constructor.
  - red; intros.
    exploit norm_ld; eauto. simpl.
    intro A; inv A. rewrite <- H1. simpl.
    sint. auto.
Qed.

(** ** Properties related to [store] *)
  
Theorem valid_access_store:
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable -> 
  { m2: mem | store chunk m1 b ofs v = Some m2 }.
Proof.
  intros.
  unfold store.  
  destruct (valid_access_dec m1 chunk b ofs Writable); [|contradiction].
  eauto.
Defined.  

Hint Local Resolve valid_access_store: mem.
 
Section STORE.
Variable chunk: memory_chunk.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable v: expr_sym.
Variable m2: mem.
Hypothesis STORE: store chunk m1 b ofs v = Some m2.
 
Lemma store_access: mem_access m2 = mem_access m1.
Proof.
  unfold store in STORE.
  destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Lemma store_mem_contents: 
  mem_contents m2 = PMap.set b (setN (encode_val chunk v) ofs m1.(mem_contents)#b) m1.(mem_contents).
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem perm_store_1:
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Proof.
  intros. 
 unfold perm in *. rewrite store_access; auto.
Qed.

Theorem perm_store_2:
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Proof.
  intros. unfold perm in *.  rewrite store_access in H; auto.
Qed.

Local Hint Resolve perm_store_1 perm_store_2: mem.

Theorem size_of_block_store:
  forall b',
    size_of_block m1 b' = size_of_block m2 b'.
Proof.
  intros.
  revert STORE.
  unfold store.
  destr_cond_match; try congruence.
  intro A; inv A.
  unfold size_of_block; simpl.
  reflexivity.
Qed.

Theorem mask_store:
  forall b',
    mask m1 b' = mask m2 b'.
Proof.
  intros.
  revert STORE.
  unfold store.
  destr_cond_match; try congruence.
  intro A; inv A; unfold mask; reflexivity.
Qed.

Theorem bounds_of_block_store:
  forall b',
    bounds_of_block m1 b' = bounds_of_block m2 b'.
Proof.
  intros; revert STORE; unfold store; repeat (destr_cond_match; try congruence).
  intro A; inv A; reflexivity.
Qed.

Theorem nat_mask_store:
  forall b',
    nat_mask m1 b' = nat_mask m2 b'.
Proof.
  intros; revert STORE; unfold store; repeat destr_cond_match; try congruence.
  intro A; inv A; reflexivity.
Qed.


Lemma store_compat:
  forall cm q,
    Mem.compat_m m2 q cm ->
    Mem.compat_m m1 q cm.
Proof.
  intros cm q COMP.
  unfold Mem.compat_m in *.
  des q;
    (eapply Normalise.compat_same_bounds;
      [intros; rewrite <- bounds_of_block_store; eauto|
       intros; rewrite <- nat_mask_store; eauto|auto]).
Qed.

Theorem nextblock_store:
  nextblock m2 = nextblock m1.
Proof.
  intros.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem store_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_store; auto.
Qed.

Theorem store_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_store in H; auto.
Qed.

Local Hint Resolve store_valid_block_1 store_valid_block_2: mem.

Theorem store_valid_access_1:
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem store_valid_access_2:
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem store_valid_access_3:
  valid_access m1 chunk b ofs Writable.
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 chunk b ofs Writable).
  auto. 
  congruence.
Qed.



Local Hint Resolve store_valid_access_1 store_valid_access_2 store_valid_access_3: mem.

Theorem load_store_similar:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_expr_sym v chunk chunk' v'.
Proof.
  intros.
  destruct (valid_access_load m2 chunk' b ofs).
  eapply valid_access_compat. symmetry; eauto. auto. eauto with mem.
  exists x; split; auto.
  exploit load_result; eauto. intros B.
  rewrite store_mem_contents in B; simpl in B. 
  rewrite PMap.gss in B.
  replace (size_chunk_nat chunk') with (length (encode_val chunk v)) in B.
  rewrite getN_setN_same in B.
  subst.
  apply decode_encode_val_general; auto.
  rewrite encode_val_length.
  repeat rewrite size_chunk_conv in H.  
  apply inj_eq_rev; auto.
Qed.

Theorem load_store_similar_2:
  forall chunk' v1,
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  type_of_chunk chunk' = type_of_chunk chunk ->
  load chunk' m2 b ofs = Some v1 ->
  same_eval v1 (Val.load_result chunk' v).
Proof.
  intros. destruct (load_store_similar chunk') as [v' [A B]]; auto.
  rewrite A in H2; inv H2. 
  des chunk; des chunk'; try (rewrite se_eval; simpl; auto).
  unfold get_type in B.
  repeat destr. destr_in B. destr_in Heqs. destr_in Heqs.
  - rewrite B. red; intros; symmetry; destr.
    erewrite (wt_expr_2_is_undef _ Tsingle Tfloat); destr.
  - repeat destr_in B; repeat destr_in Heqs. 
    rewrite B. red; intros; symmetry; destr.
    rewrite nwt_expr_undef; auto.
    intro; dex. des t.
Qed.

Theorem load_store_same:
  exists v1, load chunk m2 b ofs = Some v1 /\
             same_eval v1 (Val.load_result chunk v).
Proof.
  intros. 
  exploit load_store_similar; eauto. omega.   
  intros [v' [A B]]. rewrite A. exists v'; split; auto.
  des chunk.
  destruct (get_type_correct v).
  - des (get_type v); repeat destr.
    + rewrite B.
      red; intros; simpl; erewrite (wt_expr_2_is_undef _ _ _ H w); auto. congruence.
    + rewrite B.
      red; intros; simpl; erewrite (wt_expr_2_is_undef _ _ _ H w); auto. congruence.
    + rewrite B.
      red; intros; simpl; erewrite (wt_expr_2_is_undef _ _ _ H w); auto. congruence.
    + rewrite B.
      red; intros; simpl; erewrite (wt_expr_2_is_undef _ _ _ H w); auto. congruence.
  - des (get_type v); repeat destr; rewrite B; red; intros;
    simpl; rewrite ! nwt_expr_undef; auto.
Qed.

Theorem load_store_other:
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs'.
Proof.
  intros. unfold load. 
  destruct (valid_access_dec m1 chunk' b' ofs' Readable).
  rewrite pred_dec_true. 
  decEq. rewrite store_mem_contents; simpl; auto.
  rewrite PMap.gsspec. destruct (peq b' b); auto. subst b'.  f_equal.
  apply getN_setN_outside. rewrite encode_val_length. repeat rewrite <- size_chunk_conv.
  intuition.
  auto.
  eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem. 
Qed.

Theorem loadbytes_store_same:
  loadbytes m2 b ofs (size_chunk chunk) = Some (encode_val chunk v).
Proof.
 intros.
  assert (valid_access m2 chunk b ofs Readable) by eauto with mem.
  unfold loadbytes. rewrite pred_dec_true. rewrite store_mem_contents; simpl. 
  rewrite PMap.gss.
  replace (nat_of_Z (size_chunk chunk)) with (length (encode_val chunk v)).
  rewrite getN_setN_same. auto. 
  rewrite encode_val_length. auto.
  apply H. 
Qed.

Theorem loadbytes_store_other:
  forall b' ofs' n,
  b' <> b
  \/ n <= 0
  \/ ofs' + n <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n.
Proof.
   intros. unfold loadbytes. 
  destruct (range_perm_dec m1 b' ofs' (ofs' + n) Cur Readable).
  rewrite pred_dec_true. 
  decEq. rewrite store_mem_contents; simpl.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'. 
  destruct H. congruence.
  destruct (zle n 0) as [z | n0].
  rewrite (nat_of_Z_neg _ z). auto.
  destruct H. omegaContradiction.
  apply getN_setN_outside. rewrite encode_val_length. rewrite <- size_chunk_conv.
  rewrite nat_of_Z_eq. auto. omega. 
  auto.
  red; intros. eauto with mem.
  rewrite pred_dec_false. auto.
  red; intro; elim n0; red; intros; eauto with mem.
Qed.

Lemma setN_property:
  forall (P: memval -> Prop) vl p q c,
  (forall v, In v vl -> P v) ->
  p <= q < p + Z_of_nat (length vl) ->
  P(ZMap.get q (setN vl p c)).
Proof.
  induction vl; intros.
  simpl in H0. omegaContradiction.
  simpl length in H0. rewrite inj_S in H0. simpl. 
  destruct (zeq p q). subst q. rewrite setN_outside. rewrite ZMap.gss. 
  auto with coqlib. omega.
  apply IHvl. auto with coqlib. omega.
Qed.

Lemma getN_in:
  forall c q n p,
  p <= q < p + Z_of_nat n ->
  In (ZMap.get q c) (getN n p c).
Proof.
  induction n; intros.
  simpl in H; omegaContradiction.
  rewrite inj_S in H. simpl. destruct (zeq p q).
  subst q. auto.
  right. apply IHn. omega. 
Qed.

Lemma psa_ptr:
  forall l b o, proj_symbolic_aux_le l = Eval (Vptr b o) -> False.
Proof.
  unfold proj_symbolic_le.
  induction l; destr.
Qed.

Lemma ps_ptr:
  forall l b o, proj_symbolic_le l = Eval (Vptr b o) -> False.
Proof.
  intros.
  eapply psa_ptr; eauto.
Qed.

Theorem load_pointer_store:
  forall chunk' b' ofs' v_b v_o,
    load chunk' m2 b' ofs' = Some(Eval (Vptr v_b v_o)) ->
    (chunk = Mint32 /\ v = Eval (Vptr v_b v_o) /\ chunk' = Mint32 /\ b' = b /\ ofs' = ofs)
    \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').
Proof.
  intros.
  assert (True) by (destruct m1; auto).
  contradict H.
  unfold load.
  destr_cond_match; try congruence.
  Transparent decode_val.
  unfold decode_val. intro H. inv H.
  des chunk'.
  - inv H2.
  - repeat destr_in H2.
  - repeat destr_in H2. repeat destr_in Heqo. inv H2.
Qed.



Lemma store_size_block:
  forall chunk m b o v m',
    store chunk m b o v = Some m' ->
    size_block  m' = size_block m.
Proof.
  unfold store; intros.
  destr_in H; inv H.
  unfold size_block. simpl. auto.
Qed.


Lemma store_mask:
  forall chunk m b o v m',
    store chunk m b o v = Some m' ->
    mask  m' = mask m.
Proof.
  unfold store; intros.
  destr_in H.
  inv H; simpl.
  unfold mask. simpl. auto.
Qed.


Lemma store_mk_block_list:
  forall chunk m b o v m',
    store chunk m b o v = Some m' ->
    mk_block_list  m' = mk_block_list m.
Proof.
  intros. 
  exploit store_size_block; eauto.
  exploit store_mask; eauto.
  unfold store in H.
  destr_in H. 
  inv H; simpl. intros.
  unfold mk_block_list. simpl.
  rewrite H0. auto. 
Qed.

(* Lemma store_size_mem: *)
(*   forall chunk m b o v m', *)
(*     store chunk m b o v = Some m' -> *)
(*     size_mem m' = size_mem m. *)
(* Proof. *)
(*   intros. *)
(*   exploit store_mk_block_list; eauto. *)
(*   unfold store in H; intros. *)
(*   destr_in H. inv H.  *)
(*   unfold size_mem.  *)
(*   rewrite H0. auto. *)
(* Qed. *)




Lemma size_block_store:
  forall chunk m1 b1 ofs v1 n1,
    store chunk m1 b1 ofs v1 = Some n1 ->
    forall b',
      size_block n1 b' = size_block m1 b'.
Proof.
  intros.
  unfold size_block, get_size.
  unfold store in H.
  repeat destr_in H; inv H; simpl. auto. 
Qed.

Lemma store_in_bound_m_1:
  forall b' ofs',
    in_bound_m ofs' m1 b' ->
    in_bound_m ofs' m2 b'.
Proof.
  unfold in_bound_m.
  intros.
  erewrite <- bounds_of_block_store; eauto.
Qed.

Lemma store_in_bound_m_2:
  forall b' ofs',
    in_bound_m ofs' m2 b' ->
    in_bound_m ofs' m1 b'.
Proof.
  unfold in_bound_m.
  intros.
  erewrite bounds_of_block_store; eauto.
Qed.


End STORE.

Lemma store_norm:
  forall chunk m1 b o v m2 e,
    Mem.store chunk m1 b o v = Some m2 ->
    Mem.mem_norm m1 e = Mem.mem_norm m2 e.
Proof.
  intros.
  generalize (bounds_of_block_store _ _ _ _ _ _ H).
  generalize (Mem.nat_mask_store _ _ _ _ _ _ H).
  intros M B.
  apply norm_same_compat; auto.
Qed.

Lemma storev_norm:
  forall chunk m1 bo v m2 e,
    Mem.storev chunk m1 bo v = Some m2 ->
    Mem.mem_norm m1 e = Mem.mem_norm m2 e.
Proof.
  intros.
  unfold Mem.storev in H; revert H; destr.
  eapply store_norm; eauto.
Qed.

Local Hint Resolve perm_store_1 perm_store_2: mem.
Local Hint Resolve store_valid_block_1 store_valid_block_2: mem.
Local Hint Resolve store_valid_access_1 store_valid_access_2
             store_valid_access_3: mem.

Lemma store_similar_chunks:
  forall chunk1 chunk2 v1 v2 m b ofs,
  encode_val chunk1 v1 = encode_val chunk2 v2 ->
  align_chunk chunk1 = align_chunk chunk2 ->
  store chunk1 m b ofs v1 = store chunk2 m b ofs v2.
Proof.
  intros. unfold store. 
  assert (size_chunk chunk1 = size_chunk chunk2).
  {
    repeat rewrite size_chunk_conv.
    erewrite <- (encode_val_length chunk1 v1); eauto.
    erewrite <- (encode_val_length chunk2 v2); eauto.
    rewrite H. auto.
  }
  destruct (valid_access_dec m chunk1 b ofs Writable);
  destruct (valid_access_dec m chunk2 b ofs Writable); auto.
  erewrite (mkmem_ext); eauto.
  rewrite H; auto.
  elim n. apply valid_access_compat with chunk1; auto. omega.
  elim n. apply valid_access_compat with chunk2; auto. omega.
Qed.

Theorem store_signed_unsigned_8:
  forall m b ofs v,
  store Mint8signed m b ofs v = store Mint8unsigned m b ofs v.
Proof. 
  intros. 
  apply store_similar_chunks.
  apply encode_val_int8_signed_unsigned.
  simpl. omega.
Qed.

Theorem store_signed_unsigned_16:
  forall m b ofs v,
  store Mint16signed m b ofs v = store Mint16unsigned m b ofs v.
Proof. 
  intros. 
  apply store_similar_chunks.
  apply encode_val_int16_signed_unsigned.
  simpl. omega.
Qed. 

Lemma get_setN_not_last:
  forall al ofs0 ofs o a t,
    ofs0 <> ofs ->
    (ZMap.get ofs0 (setN al o (ZMap.set ofs a t))) = ZMap.get ofs0 (setN al o t).
Proof.
  induction al; simpl; intros.
  rewrite ZMap.gso; auto.
  destruct (Z_eq_dec o ofs); subst.
  rewrite ZMap.set2. auto.
  destruct (Z_eq_dec o ofs0); subst.
  repeat rewrite setN_outside by omega.
  repeat rewrite ZMap.gss. auto.
  repeat rewrite IHal; auto.
Qed.


(** ** Properties related to [storebytes]. *)

Theorem range_perm_storebytes:
  forall m1 b ofs bytes,
  range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable ->
  { m2 : mem | storebytes m1 b ofs bytes = Some m2 }.
Proof.
  intros. unfold storebytes.
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable).
  econstructor; reflexivity. 
  contradiction.
Defined.

Theorem storebytes_store:
  forall m1 b ofs chunk v m2,
  storebytes m1 b ofs (encode_val chunk v) = Some m2 ->
  (align_chunk chunk | ofs) ->
  store chunk m1 b ofs v = Some m2.
Proof.
  unfold storebytes, store. intros. 
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length (encode_val chunk v))) Cur Writable); inv H;
  destruct (valid_access_dec m1 chunk b ofs Writable).
  - erewrite mkmem_ext; eauto.
  - elim n. constructor; auto. 
    erewrite encode_val_length in r; eauto. rewrite size_chunk_conv. auto.
Qed.

Theorem store_storebytes:
  forall m1 b ofs chunk v m2 ,
  store chunk m1 b ofs v = Some m2 ->
  storebytes m1 b ofs (encode_val chunk v) = Some m2.
Proof.
  unfold storebytes, store. intros. 
  destruct (valid_access_dec m1 chunk b ofs Writable); inv H.
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length (encode_val chunk v))) Cur Writable).
  erewrite mkmem_ext; eauto.
  destruct v0.  elim n. 
  erewrite encode_val_length;eauto. rewrite <- size_chunk_conv. auto.
Qed.
  
Section STOREBYTES.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable bytes: list memval.
Variable m2: mem.
Hypothesis STORE: storebytes m1 b ofs bytes = Some m2.

Lemma storebytes_access: mem_access m2 = mem_access m1.
Proof.
  unfold storebytes in STORE. 
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Lemma storebytes_mem_contents:
   mem_contents m2 = PMap.set b (setN bytes ofs m1.(mem_contents)#b) m1.(mem_contents).
Proof.
  unfold storebytes in STORE. 
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Theorem perm_storebytes_1:
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Proof.
  intros. unfold perm in *. rewrite storebytes_access; auto.
Qed.

Theorem perm_storebytes_2:
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Proof.
  intros. unfold perm in *. rewrite storebytes_access in H; auto.
Qed.

Local Hint Resolve perm_storebytes_1 perm_storebytes_2: mem.

Theorem storebytes_valid_access_1:
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem storebytes_valid_access_2:
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Local Hint Resolve storebytes_valid_access_1 storebytes_valid_access_2: mem.

Theorem size_of_block_storebytes:
  forall b',
    size_of_block m1 b' = size_of_block m2 b'.
Proof.
  intros; revert STORE.
  unfold storebytes; repeat destr_cond_match; try congruence.
  intro A; inv A; unfold size_of_block; reflexivity.
Qed.

Theorem mask_storebytes:
  forall b',
    mask m1 b' = mask m2 b'.
Proof.
  intros; revert STORE.
  unfold storebytes; repeat destr_cond_match; try congruence.
  intro A; inv A; unfold mask; reflexivity.
Qed.

Theorem bounds_of_block_storebytes:
  forall b',
    bounds_of_block m1 b' = bounds_of_block m2 b'.
Proof.
  intros; revert STORE; unfold storebytes; repeat destr_cond_match; try congruence.
  intro A; inv A; reflexivity.
Qed.

Theorem nat_mask_storebytes:
  forall b',
    nat_mask m1 b' = nat_mask m2 b'.
Proof.
  intros; revert STORE; unfold storebytes; repeat destr_cond_match; try congruence.
  intro A; inv A; reflexivity.
Qed.

Theorem nextblock_storebytes:
  nextblock m2 = nextblock m1.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Theorem storebytes_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_storebytes; auto.
Qed.

Theorem storebytes_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_storebytes in H; auto.
Qed.

Local Hint Resolve storebytes_valid_block_1 storebytes_valid_block_2: mem.

Theorem storebytes_range_perm:
  range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable.
Proof.
  intros. 
  unfold storebytes in STORE. 
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Theorem loadbytes_storebytes_same:
  loadbytes m2 b ofs (Z_of_nat (length bytes)) = Some bytes.
Proof.
  intros. unfold storebytes in STORE. unfold loadbytes. 
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  try discriminate.
  rewrite pred_dec_true. 
  decEq. inv STORE; simpl. rewrite PMap.gss. rewrite nat_of_Z_of_nat. 
  apply getN_setN_same. 
  red; eauto with mem. 
Qed.

Theorem loadbytes_storebytes_disjoint:
  forall b' ofs' len,
  len >= 0 ->
  b' <> b \/ Intv.disjoint (ofs', ofs' + len) (ofs, ofs + Z_of_nat (length bytes)) ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs' (ofs' + len) Cur Readable).
  rewrite pred_dec_true. 
  rewrite storebytes_mem_contents. decEq. 
  rewrite PMap.gsspec. destruct (peq b' b). subst b'. 
  apply getN_setN_disjoint. rewrite nat_of_Z_eq; auto. intuition congruence.
  auto.
  red; auto with mem.
  apply pred_dec_false. 
  red; intros; elim n. red; auto with mem.
Qed.

Theorem loadbytes_storebytes_other:
  forall b' ofs' len,
  len >= 0 ->
  b' <> b
  \/ ofs' + len <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len.
Proof.
  intros. apply loadbytes_storebytes_disjoint; auto. 
  destruct H0; auto. right. apply Intv.disjoint_range; auto. 
Qed.

Theorem load_storebytes_other:
  forall chunk b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  load chunk m2 b' ofs' = load chunk m1 b' ofs'.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m1 chunk b' ofs' Readable).
  rewrite pred_dec_true. 
  rewrite storebytes_mem_contents. decEq.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  rewrite getN_setN_outside. auto. rewrite <- size_chunk_conv. intuition congruence.
  auto.
  destruct v; split; auto. red; auto with mem.
  apply pred_dec_false. 
  red; intros; elim n. destruct H0. split; auto. red; auto with mem.
Qed.


Lemma storebytes_size_block:
  size_block m2 = size_block m1.
Proof.
  unfold storebytes in STORE. destr_in STORE. 
  inv STORE; auto. 
Qed.

Lemma storebytes_blocksize:
  mem_blocksize m2 = mem_blocksize m1.
Proof.
  unfold storebytes in STORE. destr_in STORE. 
  inv STORE; auto. 
Qed.


Lemma storebytes_mask:
    mem_mask m2 = mem_mask m1.
Proof.
  unfold storebytes in STORE. destr_in STORE. 
  inv STORE; auto. 
Qed.

  
Lemma storebytes_mk_block_list:
  mk_block_list  m2 = mk_block_list m1.
Proof.
  intros.
  unfold mk_block_list.
  erewrite storebytes_size_block; eauto.
  rewrite nextblock_storebytes; auto.
Qed.

(* Lemma storebytes_size_mem: *)
(*   size_mem m2 = size_mem m1. *)
(* Proof. *)
(*   intros. *)
(*   unfold size_mem. *)
(*   rewrite storebytes_mk_block_list; eauto. *)
(* Qed. *)

Lemma size_block_storebytes:
  forall b',
    size_block m2 b' = size_block m1 b'.
Proof.
  intros.
  unfold size_block, get_size.
  rewrite storebytes_blocksize; auto.
Qed.

Lemma storebytes_in_bound_m_1:
    forall b' ofs',
      in_bound_m ofs' m1 b' ->
      in_bound_m ofs' m2 b'.
Proof.
  unfold in_bound_m.
  intros.
  erewrite <- bounds_of_block_storebytes; eauto.
Qed.

Lemma storebytes_in_bound_m_2:
    forall b' ofs',
      in_bound_m ofs' m2 b' ->
      in_bound_m ofs' m1 b'.
Proof.
  unfold in_bound_m.
  intros.
  erewrite bounds_of_block_storebytes; eauto.
Qed.


End STOREBYTES.

Definition all_blocks_injected (f:meminj) (m:mem) : Prop :=
  forall b lo hi, 
    bounds_of_block m b = (lo,hi) ->
    hi - lo <> 0 ->
    f b <> None.



Lemma store_abi:
  forall chunk m b ofs v m',
    Mem.store chunk m b ofs v = Some m' ->
    forall j,
      Mem.all_blocks_injected j m ->
      Mem.all_blocks_injected j m'.
Proof.
  intros chunk m b ofs v m' STORE j ABI.
  red; intros.
  eapply ABI.
  erewrite Mem.bounds_of_block_store; eauto.
  auto.
Qed.


Lemma storev_abi:
  forall chunk m bofs v m',
    Mem.storev chunk m bofs v = Some m' ->
    forall j,
      Mem.all_blocks_injected j m ->
      Mem.all_blocks_injected j m'.
Proof.
  intros chunk m bofs v m'.
  unfold Mem.storev.
  destr.
  eapply store_abi; eauto.
Qed.


Lemma storebytes_abi:
  forall m b ofs v m'
    (SB: Mem.storebytes m b ofs v = Some m')
    j (ABI: Mem.all_blocks_injected j m),
    Mem.all_blocks_injected j m'.
Proof.
  red; intros.
  eapply ABI.
  erewrite Mem.bounds_of_block_storebytes; eauto.
  auto.
Qed.


Lemma setN_concat:
  forall bytes1 bytes2 ofs c,
  setN (bytes1 ++ bytes2) ofs c = setN bytes2 (ofs + Z_of_nat (length bytes1)) (setN bytes1 ofs c).
Proof.
  induction bytes1; intros.
  simpl. decEq. omega.
  simpl length. rewrite inj_S. simpl. rewrite IHbytes1. decEq. omega.
Qed.

Lemma Forall_app_not:
  forall {A} P (a b:list A),
  (~ Forall P a) \/ (~ Forall P b) ->
  ~ Forall P (a++b).
Proof.
  intros.
  destruct H.
  intro.
  apply Forall_app_l in H0; congruence.
  intro.
  apply Forall_app_r in H0; congruence.
Qed.

Theorem storebytes_concat:
  forall m b ofs bytes1 m1 bytes2 m2,
  storebytes m b ofs bytes1 = Some m1 ->
  storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2 ->
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2.
Proof.
  intros. generalize H; intro ST1. generalize H0; intro ST2.
  unfold storebytes; unfold storebytes in ST1; unfold storebytes in ST2.
  destruct (range_perm_dec m b ofs (ofs + Z_of_nat(length bytes1)) Cur Writable); try congruence.
  destruct (range_perm_dec m1 b (ofs + Z_of_nat(length bytes1)) (ofs + Z_of_nat(length bytes1) + Z_of_nat(length bytes2)) Cur Writable); try congruence.
  destruct (range_perm_dec m b ofs (ofs + Z_of_nat (length (bytes1 ++ bytes2))) Cur Writable).
  inv ST1; inv ST2; simpl. 
  erewrite mkmem_ext; eauto.
  simpl.
  rewrite PMap.gss.  rewrite setN_concat. symmetry. apply PMap.set2.
  elim n.   
  rewrite app_length. rewrite inj_plus. red; intros.
  destruct (zlt ofs0 (ofs + Z_of_nat(length bytes1))).
  apply r. omega. 
  eapply perm_storebytes_2; eauto. apply r0. omega.
Qed.

Theorem storebytes_split:
  forall m b ofs bytes1 bytes2 m2,
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2 ->
  exists m1,
     storebytes m b ofs bytes1 = Some m1
  /\ storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2.
Proof.
  intros. 
  destruct (range_perm_storebytes m b ofs bytes1) as [m1 ST1].
  red; intros. exploit storebytes_range_perm; eauto. rewrite app_length. 
  rewrite inj_plus. omega.
  destruct (range_perm_storebytes m1 b (ofs + Z_of_nat (length bytes1)) bytes2) as [m2' ST2].
  red; intros. eapply perm_storebytes_1; eauto. exploit storebytes_range_perm. 
  eexact H. instantiate (1 := ofs0). rewrite app_length. rewrite inj_plus. omega.
  auto.
  assert (Some m2 = Some m2').
  rewrite <- H. eapply storebytes_concat; eauto.
  inv H0.
  exists m1; split; auto. 
Qed.

Lemma load_align_chunk:
  forall m b ofs chunk v,
    load chunk m b ofs = Some v ->
    (align_chunk chunk | ofs).
Proof.
  intros until v.
  unfold load.
  destr_cond_match; try congruence.
  destruct v0.
  intros; auto.
Qed.

Lemma loadbytes_one:
  forall m b o n bytes,
    loadbytes m b o n = Some bytes ->
    n > 0 ->
    exists b1 b2,
      loadbytes m b o 1 = Some b1 /\
      loadbytes m b (o+1) (n-1) = Some b2 /\
      bytes = b1 ++ b2.
Proof.
  intros.
  generalize (loadbytes_range_perm _ _ _ _ _ H); intro r.
  assert (r1 : range_perm m b o (o + 1) Cur Readable).
  {
    unfold range_perm in *.
    intros.
    apply r; omega.
  }
  assert (r2 : range_perm m b (o + 1) (o + n) Cur Readable).
  {
    unfold range_perm in *.
    intros.
    apply r; omega.
  }
  generalize (range_perm_loadbytes m b o 1 r1).
  generalize (range_perm_loadbytes m b (o+1) (n-1)).
  replace (o+1 +(n-1)) with (o+n) by omega.
  intros A B; specialize (A r2).
  destruct A; destruct B.
  rewrite H2; rewrite H1.
  repeat eexists; repeat split; eauto.
  replace n with (1 + (n - 1)) in H by omega.
  erewrite loadbytes_concat in H; eauto.
  inv H; auto.
  omega.
  omega.
Qed.

Lemma int_range_int64:
  forall i,
  0 <= Int.unsigned i <= Int64.max_unsigned.
Proof.
  intros.
  generalize (Int.unsigned_range i). split. omega.
  transitivity Int.modulus. omega.
  vm_compute. congruence.
Qed.

Lemma int_inf_two_p_32:
  forall i,
    0 <= Int.unsigned i < two_power_nat 32.
Proof.
  intros.
  change (two_power_nat 32) with Int.modulus.
  generalize (Int.unsigned_range i). omega. 
Qed.

Lemma store_int64_eq_add:
  forall m b i v m', 
    store Mint64 m b (Int.unsigned i) v = Some m' ->
    Int.unsigned (Int.add i (Int.repr 4)) = Int.unsigned i + 4.
Proof.
  intros.
  rewrite Int.add_unsigned. rewrite Int.unsigned_repr. auto.
  exploit store_valid_access_3. eexact H. intros [P Q]. simpl in Q.
  exploit (Zdivide_interval (Int.unsigned i) Int.modulus 8).
  omega. apply Int.unsigned_range. auto. exists (two_p (32-3)); reflexivity. 
  change (Int.unsigned (Int.repr 4)) with 4. unfold Int.max_unsigned. omega. 
Qed.



(** ** Properties related to [alloc]. *)

Lemma pos2nat_id:
  forall p,
    Pos.of_nat (S (pred (Pos.to_nat p))) = p.
Proof.
  intro.
  rewrite <- (S_pred (Pos.to_nat p) (pred (Pos.to_nat p))).
  rewrite Pos2Nat.id; auto.
  zify. omega.
Qed.


Section ALLOC.

Variable m1: Mem.mem.
Variables lo hi: Z.
Variable m2: Mem.mem.
Variable b: block.
Variable bt: block_type.
Hypothesis ALLOC: alloc m1 lo hi bt = Some (m2, b).

Theorem mask_alloc_other:
  forall b',
    b <> b' ->
    mask m1 b' = mask m2 b'.
Proof. 
  unfold alloc, low_alloc in ALLOC.
destr_in ALLOC.  injection ALLOC; intros; subst; unfold mask; simpl in *. 
  rewrite PMap.gso by congruence.
  reflexivity.
Qed.

Theorem size_of_block_alloc_other:
  forall b',
    b <> b' ->
    size_of_block m1 b' = size_of_block m2 b'.
Proof.
  unfold alloc, low_alloc in ALLOC.
destr_in ALLOC.  injection ALLOC; intros; subst; unfold size_of_block; simpl. 
  rewrite PMap.gso by congruence.
  reflexivity.
Qed.

Theorem bounds_of_block_alloc_other:
  forall b',
    b <> b' ->
    bounds_of_block m1 b' = bounds_of_block m2 b'.
Proof.
  unfold alloc, low_alloc in ALLOC.
destr_in ALLOC.  injection ALLOC; intros; subst; unfold bounds_of_block; simpl.
  rewrite PMap.gso by congruence.
  reflexivity.
Qed.

Theorem nat_mask_alloc_other:
  forall b',
    b <> b' ->
    nat_mask m1 b' = nat_mask m2 b'.
Proof.
  intros; unfold nat_mask.
  f_equal; f_equal. f_equal. f_equal.
  apply mask_alloc_other; auto.
Qed.

Theorem nextblock_alloc:
  nextblock m2 = Psucc (nextblock m1).
Proof.
  unfold alloc, low_alloc in ALLOC.
destr_in ALLOC.  injection ALLOC; intros. rewrite <- H0; auto.
Qed.

Theorem alloc_result:
  b = nextblock m1.
Proof.
  unfold alloc, low_alloc in ALLOC.
  destr_in ALLOC.
Qed.

Theorem valid_block_alloc:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_alloc. 
  apply Plt_trans_succ; auto.
Qed.

Theorem fresh_block_alloc:
  ~(valid_block m1 b).
Proof.
  unfold valid_block. rewrite alloc_result. apply Plt_strict. 
Qed.

Theorem valid_new_block:
  valid_block m2 b.
Proof.
  unfold valid_block. rewrite alloc_result. rewrite nextblock_alloc. apply Plt_succ.
Qed.

Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.

Theorem valid_block_alloc_inv:
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.
Proof.
  unfold valid_block; intros. 
  rewrite nextblock_alloc in H. rewrite alloc_result. 
  exploit Plt_succ_inv; eauto. tauto.
Qed.

Theorem perm_alloc_1:
  forall b' ofs k p, perm m1 b' ofs k p -> perm m2 b' ofs k p.
Proof.
  unfold perm; intros. 
  unfold alloc, low_alloc in ALLOC.
destr_in ALLOC.  injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite PMap.gsspec. destruct (peq b' (nextblock m1)); auto.
  rewrite nextblock_noaccess in H. contradiction. subst b'. apply Plt_strict. 
Qed.

Theorem perm_alloc_2:
  forall ofs k, 0 <= ofs < hi -> perm m2 b ofs k Freeable.
Proof.
  unfold perm; intros. 
  unfold alloc, low_alloc in ALLOC.
destr_in ALLOC.  injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite PMap.gss. unfold proj_sumbool. rewrite zle_true.
  rewrite zlt_true. simpl. auto with mem. omega. omega.
Qed.

Theorem perm_alloc_inv:
  forall b' ofs k p, 
  perm m2 b' ofs k p ->
  if eq_block b' b then 0 <= ofs < hi else perm m1 b' ofs k p.
Proof.
  intros until p; unfold perm. 
  unfold alloc, low_alloc in ALLOC.
destr_in ALLOC.  inv ALLOC. simpl. 
  rewrite PMap.gsspec. unfold eq_block. destruct (peq b' (nextblock m1)); intros.
  destruct (zle 0 ofs); try contradiction. destruct (zlt ofs hi); try contradiction.
  split; auto. 
  auto.
Qed.

Theorem perm_alloc_3:
  forall ofs k p, perm m2 b ofs k p -> 0 <= ofs < hi.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_true; auto. 
Qed.

Theorem perm_alloc_4:
  forall b' ofs k p, perm m2 b' ofs k p -> b' <> b -> perm m1 b' ofs k p.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_false; auto.
Qed.

Local Hint Resolve perm_alloc_1 perm_alloc_2 perm_alloc_3 perm_alloc_4: mem.

Theorem valid_access_alloc_other:
  forall chunk b' ofs p,
  valid_access m1 chunk b' ofs p ->
  valid_access m2 chunk b' ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; auto with mem.
Qed.

Theorem valid_access_alloc_same:
  forall chunk ofs,
  0 <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable.
Proof.
  intros. constructor; auto with mem.
  red; intros. apply perm_alloc_2. omega. 
Qed.

Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

Theorem valid_access_alloc_inv:
  forall chunk b' ofs p,
  valid_access m2 chunk b' ofs p ->
  if eq_block b' b
  then 0 <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p.
Proof.
  intros. inv H.
  generalize (size_chunk_pos chunk); intro.
  destruct (eq_block b' b). subst b'.
  assert (perm m2 b ofs Cur p). apply H0. omega. 
  assert (perm m2 b (ofs + size_chunk chunk - 1) Cur p). apply H0. omega. 
  exploit perm_alloc_inv. eexact H2. rewrite dec_eq_true. intro.
  exploit perm_alloc_inv. eexact H3. rewrite dec_eq_true. intro. 
  intuition omega. 
  split; auto. red; intros. 
  exploit perm_alloc_inv. apply H0. eauto. rewrite dec_eq_false; auto. 
Qed.

Theorem load_alloc_unchanged:
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b' ofs Readable).
  exploit valid_access_alloc_inv; eauto. destruct (eq_block b' b); intros.
  subst b'. elimtype False. eauto with mem.
  rewrite pred_dec_true; auto.
  unfold alloc, low_alloc in ALLOC.
destr_in ALLOC.  injection ALLOC; intros. rewrite <- H2; simpl.
  rewrite PMap.gso. auto. rewrite H1. apply sym_not_equal; eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.

Theorem load_alloc_other:
  forall chunk b' ofs v,
  load chunk m1 b' ofs = Some v ->
  load chunk m2 b' ofs = Some v.
Proof.
  intros. rewrite <- H. apply load_alloc_unchanged. eauto with mem.
Qed.

Require Import Classical. 

Lemma init_block'_eundef:
  forall n b cur o,
    (0 <= o < n)%nat ->
    nth_error (init_block' n b cur) o =
    Some (Symbolic
            ( (Eundef b (Int.add cur (Int.repr (Z.of_nat o)))))
            None O).
Proof.
  induction n; simpl; intros. lia.
  destruct H.
  destruct o.
  simpl.
  rewrite Int.add_zero; auto.
  simpl.
  rewrite IHn; auto.
  rewrite Int.add_assoc.
  f_equal. f_equal. f_equal.
  f_equal.
  rewrite Val.int_add_repr. f_equal. lia.
  lia.
Qed.

Lemma in_nth_error:
  forall (A: Type) (vl: list A) (x:A),
    In x vl ->
    exists n, nth_error vl n = Some x.
Proof.
  induction vl; simpl; intros.
  exfalso; auto.
  destruct H; subst; auto.
  exists O; auto.
  destruct (IHvl _ H).
  exists (S x0); auto.
Qed.

Lemma nth_error_length:
  forall (A:Type) (l:list A) x v,
    nth_error l x = Some v ->
    (length l > x)%nat.
Proof.
  induction l; simpl; intros.
  rewrite nth_error_nil in H; congruence.
  destruct x. omega.
  simpl in H.
  apply IHl in H. omega.
Qed.

Lemma init_block'_length:
  forall n b c,
    length (init_block' n b c) = n.
Proof.
  induction n; simpl; intros; eauto.
Qed.

Lemma init_block_eundef:
  forall n o lo hi c,
    (* lo <= o -> o + Z.of_nat n <= hi -> *)
    (* Forall (fun x => exists y z, x = Symbolic ((Eundef y z)) None O) (getN n o (init_block lo hi c)). *)
    Forall (fun x => x = Symbolic ((Eval Vundef)) None O) (getN n o (init_block lo hi c)).
Proof.
  induction n; simpl; intros.
  constructor.
  constructor; auto.
  - unfold init_block.
    rewrite ZMap.gi. auto.
    (*zify.
    destr; try omega.
    set (P:=fun mv => exists y z, mv = Symbolic ( (Eundef y z)) None O).
    refine (setN_property P _ _ _ _ _ _).
    intros. apply in_nth_error in H2.
    destruct H2.
    rewrite init_block'_eundef in H2. inv H2.
    unfold P; simpl.
    eauto.
    split. lia.
    apply nth_error_length in H2.
    rewrite init_block'_length in H2. lia.
    rewrite init_block'_length. split. lia.
    rewrite Z2Nat.id; try omega.*)
  (* - apply IHn; lia. *)
Qed.

Theorem loadbytes_alloc_unchanged:
  forall b' ofs n,
  valid_block m1 b' ->
  loadbytes m2 b' ofs n = loadbytes m1 b' ofs n.
Proof.
  intros. unfold loadbytes. 
  destruct (range_perm_dec m1 b' ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  unfold alloc, low_alloc in ALLOC.
destr_in ALLOC.  injection ALLOC; intros A B. rewrite <- B; simpl. 
  rewrite PMap.gso. auto. rewrite A. eauto with mem.
  red; intros. eapply perm_alloc_1; eauto. 
  rewrite pred_dec_false; auto.
  red; intros; elim n0. red; intros. eapply perm_alloc_4; eauto. eauto with mem. 
Qed.

Theorem loadbytes_alloc_same:
  forall n ofs bytes byte,
  loadbytes m2 b ofs n = Some bytes ->
  In byte bytes ->
  byte = Symbolic (Eval Vundef) None O.
  (* exists x y, byte = Symbolic ( (Eundef x y)) None O. *)
Proof.
  unfold loadbytes; intros. destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable); inv H.
  revert H0.
  unfold alloc, low_alloc in ALLOC.
destr_in ALLOC.  injection ALLOC; intros A B. rewrite <- A; rewrite <- B; simpl. rewrite PMap.gss. 
  revert byte.
  rewrite <- Forall_forall.
  destruct (zle n 0).
  rewrite nat_of_Z_neg.  simpl; constructor. auto.
  apply init_block_eundef.
(*  - inv ALLOC. clear - r g.
    unfold range_perm, perm in r; simpl in r.
    rewrite PMap.gss in r.
    specialize (r ofs).
    trim r. omega.
    des (zle 0 ofs).
  - inv ALLOC. clear - r g.
    unfold range_perm, perm in r; simpl in r.
    rewrite PMap.gss in r.
    specialize (r (ofs + n - 1)).
    trim r. omega.
    revert r; destr.
    apply andb_true_iff in Heqb. destr_and.
    destruct (zlt (ofs + n - 1) hi) eqn:?; destr.
    destruct (zle 0 (ofs + n - 1)) eqn:?; destr.
    rewrite nat_of_Z_eq; auto; lia. *)
Qed.


Opaque Pos.of_nat.
(* Lemma alloc_size_mem': *)
(*   size_mem m2 = size_mem m1 + align (Z.max 0 hi) (two_power_nat MA). *)
(* Proof. *)
(*   intros.  *)
(*   unfold alloc, low_alloc in ALLOC. *)
(* destr_in ALLOC.  injection ALLOC; intros; subst. *)
(*   unfold size_mem.  *)
(*   unfold mk_block_list, mask.  *)
(*   unfold size_block at 1. *)
(*   simpl in *. clear ALLOC. *)
(*   rewrite Pos2Nat.inj_succ. *)
(*   rewrite <- pred_Sn. *)
(*   rewrite (S_pred (Pos.to_nat (nextblock m1)) (pred (Pos.to_nat (nextblock m1)))) at 1 *)
(*           by (zify; omega). *)
(*   rewrite mbla_rew; simpl. *)
(*   rewrite pos2nat_id.  *)
(*   rewrite get_size_same. simpl. *)
(*   rewrite Z.sub_0_r. *)
(*   destr. *)
(*   rewrite size_mem_aux_first. f_equal. *)
(*   rewrite mk_block_list_aux_ext' with (MA:=MA) (sz':=size_block m1); auto. *)
(*   apply MA_bound. *)
(*   intro. unfold get_size.  *)
(*   rewrite Pos2Nat.id. intro. rewrite PMap.gso.  *)
(*   reflexivity. *)
(*   xomega. *)
(*   f_equal. *)
(*   rewrite ! Zmax_spec. repeat destr. *)
(* Qed. *)

(* Lemma alloc_size_mem: *)
(*   size_mem m1 <= size_mem m2. *)
(* Proof. *)
(*   intros.  *)
(*   rewrite alloc_size_mem'. *)
(*   destr.  *)
(*   generalize (Zmax_bound_l 0 0 hi). *)
(*   generalize (align_le (Z.max 0 hi) _ (two_power_nat_pos MA)). *)
(*   omega. *)
(* Qed. *)

Lemma bounds_of_block_alloc:
    bounds_of_block m2 b = (0,Z.max 0 hi).
Proof.
  intros. 
  unfold alloc, low_alloc in ALLOC.
destr_in ALLOC.  unfold bounds_of_block; inv ALLOC; simpl.
  rewrite PMap.gss. auto.
Qed.


Lemma bounds_of_block_alloc_old:
  bounds_of_block m1 b = (0,0).
Proof.
  intros.
  unfold alloc, low_alloc in ALLOC.
destr_in ALLOC.  unfold bounds_of_block; inv ALLOC; simpl.
  rewrite bs_valid; auto. xomega.
Qed.

Lemma alloc_mask:
  mask m2 b = alignment_of_size hi. 
Proof.
  unfold alloc, low_alloc in ALLOC.
  destr_in ALLOC.
  inv ALLOC.
  unfold mask; simpl.
  rewrite PMap.gss. auto.
  rewrite Z.sub_0_r; auto.
  rewrite Max.max_idempotent.
  rewrite Min.min_r. auto.
  generalize MA_bound (alignment_of_size_bnd hi); lia.   
Qed.


Lemma bounds_of_block_alloc_eq:
  forall b',
    bounds_of_block m2 b' = if eq_block b' b
                              then (0,Z.max 0 hi)
                              else if plt b' (nextblock m2)
                                   then bounds_of_block m1 b'
                                   else (0,0).
Proof.
  intros.
  destr.
  subst.
  erewrite bounds_of_block_alloc; eauto.
  destr.
  erewrite <- bounds_of_block_alloc_other; eauto.
  unfold bounds_of_block; rewrite bs_valid; auto.
Qed.



Lemma alloc_in_bound:
  forall b0 o,
    in_bound_m (Int.unsigned o) m1 b0 ->
    in_bound_m (Int.unsigned o) m2 b0.
Proof.
  intros b0 o IB.
  unfold in_bound_m in *.
  erewrite bounds_of_block_alloc_eq; eauto.
  destr_cond_match; subst; auto.
  + erewrite bounds_of_block_alloc_old in IB; eauto.
    unfold NormaliseSpec.in_bound in IB; simpl in IB; omega.
  + destr_cond_match; simpl; auto.
    destruct (bounds_of_block m1 b0) eqn:?; simpl in *.
    destruct IB; simpl in *.
    destruct (zeq z z0); subst. omega.
    apply Mem.bounds_of_block_valid in Heqp; auto.
    unfold Mem.valid_block in Heqp. clear Heqs0.
    rewrite nextblock_alloc in n0.
    xomega.
Qed.



Lemma mask_alloc_old:
  mask m1 b = O.
Proof.
  intros.
  unfold alloc, low_alloc in ALLOC.
destr_in ALLOC.  unfold nat_mask, mask; inv ALLOC; simpl.
  rewrite msk_valid; auto. xomega.
Qed.

Lemma nat_mask_alloc_old:
  nat_mask m1 b = Int.mone.
Proof.
  unfold nat_mask. 
  erewrite mask_alloc_old; eauto.
  rewrite two_power_nat_O. change (Int.repr (1-1)) with Int.zero.
  apply Int.not_zero.
Qed.

Lemma compat_alloc:
  forall cm q,
    compat_m m2 q cm ->
    compat_m m1 q cm.
Proof.
  intros cm q COMPAT.
  inv COMPAT. constructor; simpl; intros; eauto.
  - eapply addr_space.
    eapply alloc_in_bound; eauto.
  - eapply overlap; eauto.
    eapply alloc_in_bound; eauto.
    eapply alloc_in_bound; eauto.
  -  generalize nat_mask_alloc_old; intro A.
     destruct (peq b b0); subst.
    + rewrite A. apply Int.and_mone.
    + rewrite nat_mask_alloc_other; eauto.
Qed.

Lemma norm_alloc:
  forall e v,
    Mem.mem_norm m1 e = v ->
    v <> Vundef ->
    Mem.mem_norm m2 e = v.
Proof.
  intros e v MN NU.
  generalize (norm_correct m1 e).
  rewrite MN.
  intro A; inv A.
  assert (is_norm_m m2 e (Mem.mem_norm m1 e)).
  {
    constructor.
    - red; intros.
      eapply lessdef_on_P_impl; eauto.
      eapply compat_alloc with (q:=M32); eauto.
  }
  generalize (norm_complete m2 e _ H).
  intro A; inv A; congruence.
Qed.

Lemma normalise_alloc:
  forall e,
    Values.Val.lessdef (Mem.mem_norm m1 e) (Mem.mem_norm m2 e).
Proof.
  intros. 
  generalize (norm_alloc e _ eq_refl). intros B.
  des (mem_norm m1 e); auto; try rewrite <- B; auto; destr.
Qed.

Definition block_undefs lo hi delta m2 b2 :=
  forall ofs : Z,
    lo <= ofs < hi ->
    ZMap.get (ofs + delta) (mem_contents m2) # b2 =
    Symbolic ( (* (Eundef b2 (Int.repr (ofs + delta))) *) Eval Vundef ) None 0.

Lemma nth_error_init_block':
  forall n b cur ofs,
    (ofs < n)%nat ->
    nth_error (init_block' n b cur) ofs = Some (Symbolic ((Eundef b (Int.add cur (Int.repr (Z.of_nat ofs))))) None O).
Proof.
  induction n; simpl; intros.
  - omega.
  - des (eq_nat_dec ofs O). 
    + rewrite Int.add_zero. reflexivity.
    + des ofs.
      rewrite IHn by omega.
      f_equal. f_equal. f_equal.
      rewrite Int.add_assoc.
      f_equal.
      zify.  rewrite <- Z.add_1_l.
      rewrite Val.int_add_repr.
      auto.
Qed.

Lemma init_block_length:
  forall n b i,
    length (init_block'  n b i) = n.
Proof.
  induction n; simpl; intros; try omega.
  rewrite IHn; omega.
Qed.

Lemma get_init_block:
  forall ofs lo hi b,
    ZMap.get ofs (init_block lo hi b) = Symbolic (Eval Vundef) None O.
Proof.
  clear.
  unfold init_block. intros; rewrite ZMap.gi. auto.
Qed.

Lemma mem_alloc_block_undefs:
  block_undefs 0 hi 0 m2 b.
Proof.
  unfold Mem.alloc, Mem.low_alloc  in ALLOC.
  destr_in ALLOC. 
  inv ALLOC.
  red; simpl. intros.
  rewrite PMap.gss.
  intros; rewrite Z.add_0_r.
  apply get_init_block; auto.
Qed.

Lemma alloc_contents_old:
  forall b' (DIFF: b' <> b),
    (mem_contents m2) # b' = (mem_contents m1) # b'.
Proof.
  unfold alloc, low_alloc in ALLOC. destr_in ALLOC. inv ALLOC; simpl.
  intros; 
  rewrite PMap.gso; auto.
Qed.

End ALLOC.

Lemma bounds_size:
  forall m b lo hi,
    Mem.bounds_of_block m b = (lo,hi) ->
    Mem.size_block m b = hi - lo.
Proof.
  unfold Mem.bounds_of_block, Mem.size_block, get_size.
  intros. repeat destr_in H; inv H; auto.
Qed.

Lemma mbla_pred_nextblock:
  forall sz n,
    (forall b, Ple (Pos.of_nat n) b -> sz b = (0)) ->
    Alloc.size_mem_aux MA (Alloc.mk_block_list_aux sz n) =
    Alloc.size_mem_aux MA (Alloc.mk_block_list_aux sz (pred n)).
Proof.
  Local Opaque Pos.of_nat.
  induction n; simpl; intros.
  unfold Alloc.mk_block_list_aux. simpl. auto.
  rewrite Alloc.mbla_rew.
  destr.
  rewrite H; [|xomega].
  rewrite Alloc.size_mem_aux_first.
  rewrite Z.max_r by lia. rewrite align_0. lia.
  apply two_power_nat_pos.
Qed.

Lemma fold_left_align:
  let f := fun acc (bsz: block * Z) => let (_, sz) := bsz in align (align acc (two_power_nat MA) + Z.max 0 sz) (two_power_nat MA) in
  forall l z,
    fold_left f l (align z (two_power_nat MA)) =
    fold_left f l 0 + align z (two_power_nat MA).
Proof.
  induction l; simpl; intros; eauto.
  unfold f at 2. des a.
  rewrite ! IHl.
  generalize tpMA_pos. intro. rewrite <- ! align_distr by lia.
  rewrite align_align by lia. rewrite align_0 by lia. simpl. lia.
Qed.
Lemma size_block_pos:
  forall m b,
    0 <= Mem.size_block m b.
Proof.
  unfold Mem.size_block, Alloc.get_size.
  intros.
  repeat destr. 2: lia.
  exploit Mem.bounds_lo_inf0; eauto. lia.
Qed.

Lemma mbl_pos:
  forall m,
    Forall (fun x : block * Z => 0 <= snd x) (mk_block_list m).
Proof.
  unfold mk_block_list.
  intros; generalize (pred (Pos.to_nat (nextblock m))).
  induction n; simpl; intros. constructor.
  rewrite mbla_rew; constructor; auto. simpl. apply size_block_pos.
Qed.

Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.
Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

(** ** Properties related to [free]. *)

Theorem range_perm_free:
  forall m1 b lo hi,
  range_perm m1 b lo hi Cur Freeable ->
  has_bounds m1 b lo hi = true ->
  { m2: mem | free m1 b lo hi = Some m2 }.
Proof.
  intros; unfold free. rewrite pred_dec_true; auto.
  rewrite H0. 
  econstructor; eauto.
Defined.

Section FREE.

Variable m1: mem.
Variable bf: block.
Variables lo hi: Z.
Variable m2: mem.
Hypothesis FREE: free m1 bf lo hi = Some m2.

Theorem free_range_perm:
  range_perm m1 bf lo hi Cur Freeable.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 bf lo hi Cur Freeable); auto.
  congruence.
Qed.

Lemma free_result:
  m2 = unchecked_free m1 bf lo hi.
Proof.
  unfold free in FREE.
  repeat destr_in FREE. 
Qed.

Lemma mask_free:
  forall b', Mem.mask m1 b' = Mem.mask m2 b'.
Proof.
  intros.
  unfold Mem.free in FREE. repeat destr_in FREE; inv FREE.
  reflexivity.
Qed.

Theorem size_of_block_free:
  forall b',
    bf <> b' -> 
    size_of_block m1 b' = size_of_block m2 b'.
Proof.
  intros.
  rewrite free_result.
  unfold size_of_block, unchecked_free; try reflexivity.
  simpl.
  rewrite PMap.gso by congruence; reflexivity.
Qed.

Theorem nextblock_free:
  nextblock m2 = nextblock m1.
Proof.
  rewrite free_result; reflexivity.
Qed.

Theorem valid_block_free_1:
  forall b, valid_block m1 b -> valid_block m2 b.
Proof.
  intros. rewrite free_result. assumption.
Qed.

Theorem valid_block_free_2:
  forall b, valid_block m2 b -> valid_block m1 b.
Proof.
  intros. rewrite free_result in H. assumption.
Qed.

Local Hint Resolve valid_block_free_1 valid_block_free_2: mem.

Theorem perm_free_1:
  forall b ofs k p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs k p ->
  perm m2 b ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf). subst b.
  destruct (zle lo ofs); simpl. 
  destruct (zlt ofs hi); simpl.
  elimtype False; intuition.
  auto. auto.
  auto.
Qed.

Theorem perm_free_2:
  forall ofs k p, lo <= ofs < hi -> ~ perm m2 bf ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gss. unfold proj_sumbool. rewrite zle_true. rewrite zlt_true. 
  simpl. tauto. omega. omega.
Qed.

Theorem perm_free_3:
  forall b ofs k p,
  perm m2 b ofs k p -> perm m1 b ofs k p.
Proof.
  intros until p. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf). subst b.
  destruct (zle lo ofs); simpl. 
  destruct (zlt ofs hi); simpl. tauto. 
  auto. auto. auto. 
Qed.

Theorem perm_free_inv:
  forall b ofs k p,
  perm m1 b ofs k p ->
  (b = bf /\ lo <= ofs < hi) \/ perm m2 b ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf); auto. subst b.
  destruct (zle lo ofs); simpl; auto.
  destruct (zlt ofs hi); simpl; auto.
Qed.

Theorem valid_access_free_1:
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p -> 
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; intros. eapply perm_free_1; eauto.
  destruct (zlt lo hi). intuition. right. omega. 
Qed.

Theorem valid_access_free_2:
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p).
Proof.
  intros; red; intros. inv H2. 
  generalize (size_chunk_pos chunk); intros.
  destruct (zlt ofs lo).
  elim (perm_free_2 lo Cur p).
  omega. apply H3. omega. 
  elim (perm_free_2 ofs Cur p).
  omega. apply H3. omega. 
Qed.

Theorem valid_access_free_inv_1:
  forall chunk b ofs p,
  valid_access m2 chunk b ofs p ->
  valid_access m1 chunk b ofs p.
Proof.
  intros. destruct H. split; auto. 
  red; intros. generalize (H ofs0 H1). 
  rewrite free_result. unfold perm, unchecked_free; simpl. 
  rewrite PMap.gsspec. destruct (peq b bf). subst b.
  destruct (zle lo ofs0); simpl.
  destruct (zlt ofs0 hi); simpl.
  tauto. auto. auto. auto. 
Qed.

Theorem valid_access_free_inv_2:
  forall chunk ofs p,
  valid_access m2 chunk bf ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.
Proof.
  intros.
  destruct (zlt lo hi); auto. 
  destruct (zle (ofs + size_chunk chunk) lo); auto.
  destruct (zle hi ofs); auto.
  elim (valid_access_free_2 chunk ofs p); auto. omega.
Qed.

Theorem load_free:
  forall chunk b ofs,
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs = load chunk m1 b ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b ofs Readable).
  rewrite pred_dec_true. 
  rewrite free_result; auto.
  eapply valid_access_free_inv_1; eauto. 
  rewrite pred_dec_false; auto.
  red; intro; elim n. eapply valid_access_free_1; eauto. 
Qed.

Theorem load_free_2:
  forall chunk b ofs v,
  load chunk m2 b ofs = Some v -> load chunk m1 b ofs = Some v.
Proof.
  intros. unfold load. rewrite pred_dec_true. 
  rewrite (load_result _ _ _ _ _ H). rewrite free_result; auto. 
  apply valid_access_free_inv_1. eauto with mem.
Qed.

Theorem loadbytes_free:
  forall b ofs n,
  b <> bf \/ lo >= hi \/ ofs + n <= lo \/ hi <= ofs ->
  loadbytes m2 b ofs n = loadbytes m1 b ofs n.
Proof.
  intros. unfold loadbytes. 
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true. 
  rewrite free_result; auto. 
  red; intros. eapply perm_free_3; eauto. 
  rewrite pred_dec_false; auto. 
  red; intros. elim n0; red; intros. 
  eapply perm_free_1; eauto. destruct H; auto. right; omega. 
Qed.

Theorem loadbytes_free_2:
  forall b ofs n bytes,
  loadbytes m2 b ofs n = Some bytes -> loadbytes m1 b ofs n = Some bytes.
Proof.
  intros. unfold loadbytes in *.
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable); inv H.
  rewrite pred_dec_true. rewrite free_result; auto.
  red; intros. apply perm_free_3; auto. 
Qed.

End FREE.

Lemma unchecked_free_bounds':
  forall m b lo hi b',
    bounds_of_block (unchecked_free m b lo hi) b' =
    if eq_block b' b
    then match bounds_of_block m b with
             (lo',hi') => (if zeq lo' lo && zeq hi' hi 
                           then (0,0)
                           else (lo',hi'))
         end
    else bounds_of_block m b'.
Proof.
  intros. 
  Opaque zeq.
  unfold unchecked_free, bounds_of_block, eq_block; simpl.
  rewrite PMap.gsspec.
  unfold get_size.
  des (mem_blocksize m) # b;
    destruct (peq b' b); subst; destr; try des p;
    unfold bounds_of_block; try rewrite Heqo; destr;
    try rewrite Heqo0; auto.  
  inv Heqo0. auto.
Qed.

Lemma free_bounds':
  forall m b lo hi m' b',
    free m b lo hi = Some m' ->
    bounds_of_block m' b' = bounds_of_block m b' \/ bounds_of_block m' b' = (0,0).
Proof.
  intros m b lo hi m' b' FREE.
  unfold Mem.free in FREE. repeat destr_in FREE; inv FREE.
  rewrite unchecked_free_bounds'.
  repeat destr.
Qed.

Lemma free_abi:
  forall m b lo hi m'
    (FREE: Mem.free m b lo hi = Some m')
    j (ABI: Mem.all_blocks_injected j m),
    Mem.all_blocks_injected j m'.
Proof.
  red; intros.
  destruct (Mem.free_bounds' _ _ _ _ _ b0 FREE).
  eapply ABI; eauto. congruence. 
  rewrite H in H1; inv H1. omega.
Qed.

Lemma free_mask:
  forall m b lo hi m' b',
    free m b lo hi = Some m' ->
    mask m' b' = mask m b'.
Proof.
  intros m b lo hi m' b' FREE.
  unfold Mem.free in FREE. repeat destr_in FREE; inv FREE.
  reflexivity.
Qed.


Lemma freelist_mask:
  forall l m m' b',
    free_list m l = Some m' ->
    mask m' b' = mask m b'.
Proof.
  induction l; simpl; intros; eauto.
  inv H; auto.
  des a; des p.
  destr_in H.
  specialize (IHl _ _ b' H).
  rewrite IHl.
  eapply free_mask; eauto.
Qed.

Lemma freelist_abi:
  forall l m m'
    (FREE: Mem.free_list m l = Some m')
    j (ABI: Mem.all_blocks_injected j m),
    Mem.all_blocks_injected j m'.
Proof.
  induction l; simpl; intros; eauto.
  inv FREE; auto.
  destruct a as [[b lo] hi].
  des (Mem.free m b lo hi).
  eapply IHl; eauto.
  eapply free_abi; eauto.
Qed.


Lemma compat_free:
  forall m b lo hi m'
         (FREE: Mem.free m b lo hi = Some m')
         cm q (COMP: Mem.compat_m m q cm),
    Mem.compat_m m' q cm.
Proof.
  intros.
  inv COMP.
  constructor; simpl; intros.
  - destruct (free_bounds' _ _ _ _ _ b0 FREE).
    + rewrite H0 in H; eauto.
    + rewrite H0 in H.
      unfold in_bound in H; simpl in H; omega.
  - destruct (Mem.free_bounds' _ _ _ _ _ b0 FREE);
    rewrite H2 in H0; eauto;
    destruct (Mem.free_bounds' _ _ _ _ _ b' FREE);
      rewrite H3 in H1; eauto;
      unfold in_bound in *; simpl in *; try omega.
  - unfold Mem.nat_mask.
    erewrite Mem.free_mask; eauto.
Qed.


Lemma compat_unchecked_free:
  forall m b lo hi
    q cm (COMP: Mem.compat_m m q cm),
    Mem.compat_m (unchecked_free m b lo hi) q cm.
Proof.
  intros.
  inv COMP.
  constructor; simpl; intros.
  - rewrite unchecked_free_bounds' in H.
    destruct (eq_block b0 b); eauto.
    subst.
    destruct (bounds_of_block m b) eqn:?.
    destruct (zeq z lo && zeq z0 hi); eauto.
    red in H; simpl in H; omega.
    apply addr_space; auto. congruence.
  - rewrite unchecked_free_bounds' in *. 
    destruct (eq_block b0 b), (eq_block b' b); subst; eauto;
    destruct (bounds_of_block m b) eqn:?;
             destruct (zeq z lo && zeq z0 hi); eauto.
    red in H0; simpl in H0; omega.
    apply overlap; auto. congruence.
    red in H1; simpl in H1; omega.
    apply overlap; auto. congruence.
  - unfold Mem.nat_mask.
    erewrite unchecked_free_mask; eauto.
Qed.


Lemma norm_free:
  forall m1 bf lo hi m2 (FREE: free m1 bf lo hi = Some m2),
  forall e v,
    Mem.mem_norm m2 e = v ->
    v <> Vundef ->
    Mem.mem_norm m1 e = v.
Proof.
  intros m1 bf lo hi m2 FREE e v MN NU.
  generalize (norm_correct m2 e).
  rewrite MN.
  intro A; inv A.
  assert (is_norm_m m1 e (Mem.mem_norm m2 e)).
  {
    constructor.
    - eapply lessdef_on_P_impl; eauto. intro.
      eapply compat_free with (q:=M32); eauto.
  }
  generalize (norm_complete m1 e _ H).
  intro A; inv A; congruence.
Qed.

Lemma norm_unchecked_free:
  forall m1 bf lo hi,
  forall e v,
    Mem.mem_norm (unchecked_free m1 bf lo hi) e = v ->
    v <> Vundef ->
    Mem.mem_norm m1 e = v.
Proof.
  intros m1 bf lo hi e v MN NU.
  generalize (norm_correct (unchecked_free m1 bf lo hi) e).
  rewrite MN.
  intro A; inv A.
  assert (is_norm_m m1 e (Mem.mem_norm (unchecked_free m1 bf lo hi) e)).
  {
    constructor.
    - eapply lessdef_on_P_impl; eauto.
      intro; 
        eapply compat_unchecked_free with (q:=M32); eauto.
  }
  generalize (norm_complete m1 e _ H).
  intro A; inv A; congruence.
Qed.

Lemma normalise_free:
  forall m1 bf lo hi m2 (FREE: free m1 bf lo hi = Some m2),
  forall e,
    Values.Val.lessdef (Mem.mem_norm m2 e) (Mem.mem_norm m1 e).
Proof.
  intros.
  generalize (norm_free _ _ _ _ _ FREE e _ eq_refl).
  intro H0.
  des (mem_norm m2 e); auto; rewrite <- H0; auto; destr.
Qed.

Lemma unchecked_free_bounds_of_block:
  forall m b lo hi,
    bounds_of_block (unchecked_free m b lo hi) b = 
    match (bounds_of_block m b) with
        (lo',hi') => if zeq lo' lo && zeq hi' hi then (0,0) else (lo',hi')
    end.
Proof.
  intros; unfold unchecked_free, bounds_of_block; simpl.
  rewrite PMap.gss.
  des ((mem_blocksize m) # b). des p.
  destr.
  repeat destr.
Qed.

Lemma unchecked_free_bounds_of_block_other:
  forall m b lo hi b', b <> b' ->
    bounds_of_block (unchecked_free m b lo hi) b' = 
    bounds_of_block m b'.
Proof.
  intros; unfold unchecked_free, bounds_of_block; simpl.
  rewrite PMap.gso; auto.
Qed.


Lemma bounds_free:
  forall  m m' b b' lo hi ,
  Mem.free m b lo hi = Some m' ->
  b <> b' ->
  Mem.bounds_of_block m' b' = Mem.bounds_of_block m b'.
Proof.
  intros.
  unfold Mem.free in H.
  repeat destr_in H. inv H.
  unfold Mem.unchecked_free. unfold Mem.bounds_of_block; simpl.
  rewrite PMap.gso by congruence. auto.
Qed.

Lemma bounds_freelist:
  forall fbl m m' b ,
  Mem.free_list m fbl = Some m' ->
  ~ In b (map (fun a => fst (fst a)) fbl) ->
  Mem.bounds_of_block m' b = Mem.bounds_of_block m b.
Proof.
  induction fbl; simpl; intros.
  inv H. auto.
  destruct a as [[b' lo] hi]. destruct (Mem.free m b' lo hi) eqn:?; try congruence.
  intros. intuition try congruence. simpl in *.
  generalize (IHfbl _ _ _ H H2).
  intro A; rewrite A.
  erewrite bounds_free; eauto.
Qed.

Lemma range_perm_freelist:
  forall fbl m m' b,
    Mem.free_list m fbl = Some m' ->
    ~ In b (map (fun a => fst (fst a)) fbl) ->
    forall lo hi k p,
      Mem.range_perm m' b lo hi k p ->
      Mem.range_perm m b lo hi k p.
Proof.
  induction fbl; simpl; intros.
  inv H. auto.
  destruct a as [[b' lo'] hi']. destruct (Mem.free m b' lo' hi') eqn:?; try congruence.
  intros. intuition try congruence. simpl in *.
  generalize (IHfbl _ _ _ H H3 _ _ _ _ H1).
  unfold Mem.range_perm. intros.
  specialize (H0 ofs H4).
  eapply Mem.perm_free_3; eauto.
Qed.

Lemma contents_free:
  forall m b lo hi m' b',
    Mem.free m b lo hi = Some m' ->
    b <> b' ->
    (Mem.mem_contents m) !! b' = (Mem.mem_contents m') !! b'.
Proof.
  intros.
  unfold free in H. 
  repeat destr_in H. 
  inv H.
  unfold Mem.unchecked_free; simpl. auto.
Qed.



Lemma contents_freelist:
  forall (fbl : list (block * Z * Z)) (m m' : mem) (b' : block),
  Mem.free_list m fbl = Some m' ->
  (Mem.mem_contents m) !! b' = (Mem.mem_contents m') !! b'.
Proof.
  induction fbl; simpl; intros; eauto.
  inv H; auto.
  repeat destr_in H.
  rewrite <- (IHfbl _ _ _ H).
  rewrite (Mem.free_contents _ _ _ _ _ Heqo). auto.
Qed.

Lemma freelist_valid:
  forall fbl m m' b,
    Mem.free_list m fbl = Some m' ->
    ~ Mem.valid_block m' b ->
    ~ Mem.valid_block m b.
Proof.
  induction fbl; simpl; intros.
  inv H; auto.
  destruct a as [[b0 lo] hi].
  destruct (Mem.free m b0 lo hi) eqn:?; try congruence.
  generalize (IHfbl _ _ _ H H0).
  intros.
  intro. 
  generalize (Mem.valid_block_free_1 _ _ _ _ _ Heqo _ H2); auto.
Qed.


Lemma permut_filter:
  forall A f (l l' : list A)
    (P: Permutation l l'),
    Permutation (filter f l) (filter f l').
Proof.
  induction 1; simpl; intros; eauto.
  destr. constructor; auto.
  destr; destr; try reflexivity.
  apply perm_swap.
  eapply Permutation_trans; eauto.
Qed.

Definition size_mem_blocks (bl: list (block * Z * Z)) (z:Z) : Z :=
  fold_left
    (fun acc x =>
       align acc (two_power_nat MA) + Z.max 0 (snd x - snd (fst x))) bl z.

Definition list_of_blocks (bl: list (block*Z*Z)) : list (block*Z) :=
  map (fun a : ident * Z * Z => (fst (fst a), snd a - snd (fst a))) bl.

Lemma size_mem_blocks_al:
  forall l z,
    size_mem_al (two_power_nat MA) (list_of_blocks l) (align z (two_power_nat MA)) =
    align (size_mem_blocks l z) (two_power_nat MA).
Proof.
  induction l; simpl; intros. auto.
  rewrite IHl. 
  rewrite align_align. auto. apply two_power_nat_pos.
Qed.

Lemma size_mem_al_rev:
  forall l z,
    size_mem_al (two_power_nat MA) l z = size_mem_al (two_power_nat MA) (rev l) z.
Proof.
  intros.
  apply size_mem_al_permut; try omega.
  apply two_power_nat_pos.
  apply Permutation.Permutation_rev.
Qed.

Lemma size_mem_app:
  forall a b c,
    size_mem_al (two_power_nat MA) (a++b) c = size_mem_al (two_power_nat MA) b (size_mem_al (two_power_nat MA) a c).
Proof.
  intros.
  unfold size_mem_al.
  rewrite fold_left_app. auto.
Qed.

Lemma size_mem_al_aligned:
  forall l z,
    z = align z (two_power_nat MA) ->
    size_mem_al (two_power_nat MA) l z = align (size_mem_al (two_power_nat MA) l z) (two_power_nat MA).
Proof.
  induction l; simpl; intros; auto.
  apply IHl.
  destruct a.
  rewrite <- ! align_distr.
  rewrite align_align; try lia.
  apply two_power_nat_pos.
  apply two_power_nat_pos.
  apply two_power_nat_pos.
Qed.

Lemma size_mem_aux_aligned:
  forall l,
    size_mem_aux MA l = align (size_mem_aux MA l) (two_power_nat MA).
Proof.
  intros; unfold size_mem_aux.
  apply size_mem_al_aligned; auto.
  rewrite align_refl; auto.
  apply two_power_nat_pos.
Qed.


(* Lemma size_mem_alloc_0: *)
(*   forall tm1 tm2 sp bt *)
(*          (ALLOC: alloc tm1 0 0 bt = Some (tm2, sp)), *)
(*     size_mem tm1 = size_mem tm2. *)
(* Proof. *)
(*   intros. *)
(*   apply alloc_size_mem' in ALLOC. *)
(*   rewrite Z.max_id in ALLOC. *)
(*   rewrite ALLOC. rewrite align_0. lia. *)
(*   apply two_power_nat_pos. *)
(* Qed. *)

(* Lemma size_mem_aligned: *)
(*   forall m z, *)
(*     size_mem m = z -> *)
(*     align z (two_power_nat MA) = z. *)
(* Proof. *)
(*   intros; subst; symmetry; apply size_mem_aux_aligned. *)
(* Qed. *)

(* Lemma size_mem_aligned': *)
(*   forall m, *)
(*     Mem.size_mem m = align (Mem.size_mem m) (two_power_nat MA). *)
(* Proof. *)
(*   intros. *)
(*   rewrite (size_mem_aligned _ _ eq_refl); auto. *)
(* Qed. *)

(* Lemma freelist_size_mem: *)
(*   forall bl m m' *)
(*          (bnds: Forall (fun bbnds : ident*Z*Z => Mem.bounds_of_block m (fst (fst bbnds)) *)
(*                                                  = (snd (fst bbnds), snd (bbnds)) ) bl) *)
(*          (FL: Mem.free_list m bl = Some m') *)
(*          (NR: list_norepet (map fst (map fst bl))), *)
(*     size_mem m = align (size_mem_blocks bl (size_mem m')) (two_power_nat MA). *)
(* Proof. *)
(*   induction bl; simpl; intros.  *)
(*   inv FL. apply size_mem_aligned'. *)
(*   des a; des p. *)
(*   des (free m i z0 z). *)
(*   inv NR. *)
(*   generalize (fun pf => IHbl m0 m' pf FL H2). *)
(*   intro G; trim G. *)
(*   { *)
(*     rewrite Forall_forall in *. *)
(*     intros. rewrite <- bnds; simpl; auto. *)
(*     eapply bounds_free; eauto. *)
(*     intro; subst. *)
(*     rewrite map_map in H1. *)
(*     eapply in_map with (f:= fun x => fst (fst x))in H; eauto. *)
(*   } *)
(*   inv bnds. simpl in *. *)
(*   eapply free_size_mem in Heqo; eauto. *)
(*   rewrite Heqo, G.  *)
(*   destr; try omega. *)
(*   generalize (two_power_nat_pos MA); intro TPNP. *)
(*   rewrite align_distr; auto. *)
(*   rewrite <- ! size_mem_blocks_al. *)
(*   setoid_rewrite (size_mem_al_rev *)
(*                     ((xH,z-z0)::(list_of_blocks *)
(*                                 bl)) (size_mem m')). *)
(*   simpl. *)
(*   rewrite size_mem_app. simpl. *)
(*   rewrite <- (size_mem_al_rev (list_of_blocks bl) (size_mem m')). *)
(*   rewrite <- align_distr; auto. *)
(*   erewrite (size_mem_aligned _ _ eq_refl); eauto. *)
(*   rewrite  (size_mem_al_aligned _ _) at 1. *)
(*   rewrite <- align_distr; auto. *)
(*   symmetry. eapply size_mem_aligned; eauto. *)
(* Qed. *)

Local Hint Resolve valid_block_free_1 valid_block_free_2
             perm_free_1 perm_free_2 perm_free_3 
             valid_access_free_1 valid_access_free_inv_1: mem.

(** ** Properties related to [drop_perm] *)

Theorem range_perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' -> range_perm m b lo hi Cur Freeable.
Proof.
  unfold drop_perm; intros. 
  destruct (range_perm_dec m b lo hi Cur Freeable). auto. discriminate.
Qed.

Theorem range_perm_drop_2:
  forall m b lo hi p,
  range_perm m b lo hi Cur Freeable -> {m' | drop_perm m b lo hi p = Some m' }.
Proof.
  unfold drop_perm; intros. 
  destruct (range_perm_dec m b lo hi Cur Freeable). econstructor. eauto. contradiction.
Defined.



Section DROP.

Variable m: mem.
Variable b: block.
Variable lo hi: Z.
Variable p: permission.
Variable m': mem.
Hypothesis DROP: drop_perm m b lo hi p = Some m'.

Theorem mask_drop_perm:
  forall b',
    mask m b' = mask m' b'.
Proof.
  revert DROP; unfold drop_perm; destr_cond_match; try congruence.
  intro A; inv A.
  intros.
  unfold mask; reflexivity.
Qed.

Theorem size_of_block_drop_perm:
  forall b',
    size_of_block m b' = size_of_block m' b'.
Proof.
  revert DROP; unfold drop_perm; destr_cond_match; try congruence.
  intro A; inv A.
  intros.
  unfold size_of_block; reflexivity.
Qed.

Theorem nextblock_drop:
  nextblock m' = nextblock m.
Proof.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP; auto.
Qed.

Theorem drop_perm_valid_block_1:
  forall b', valid_block m b' -> valid_block m' b'.
Proof.
  unfold valid_block; rewrite nextblock_drop; auto.
Qed.

Theorem drop_perm_valid_block_2:
  forall b', valid_block m' b' -> valid_block m b'.
Proof.
  unfold valid_block; rewrite nextblock_drop; auto.
Qed.

Theorem perm_drop_1:
  forall ofs k, lo <= ofs < hi -> perm m' b ofs k p.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  unfold perm. simpl. rewrite PMap.gss. unfold proj_sumbool. 
  rewrite zle_true. rewrite zlt_true. simpl. constructor.
  omega. omega. 
Qed.
  
Theorem perm_drop_2:
  forall ofs k p', lo <= ofs < hi -> perm m' b ofs k p' -> perm_order p p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  revert H0. unfold perm; simpl. rewrite PMap.gss. unfold proj_sumbool. 
  rewrite zle_true. rewrite zlt_true. simpl. auto. 
  omega. omega. 
Qed.

Theorem perm_drop_3:
  forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs k p' -> perm m' b' ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  unfold perm; simpl. rewrite PMap.gsspec. destruct (peq b' b). subst b'. 
  unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi). 
  byContradiction. intuition omega.
  auto. auto. auto.
Qed.

Theorem perm_drop_4:
  forall b' ofs k p', perm m' b' ofs k p' -> perm m b' ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  revert H. unfold perm; simpl. rewrite PMap.gsspec. destruct (peq b' b).
  subst b'. unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi).
  simpl. intros. apply perm_implies with p. apply perm_implies with Freeable. apply perm_cur.
  apply r. tauto. auto with mem. auto.
  auto. auto. auto.
Qed.

Lemma valid_access_drop_1:
  forall chunk b' ofs p', 
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p p' ->
  valid_access m chunk b' ofs p' -> valid_access m' chunk b' ofs p'.
Proof.
  intros. destruct H0. split; auto. 
  red; intros.
  destruct (eq_block b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto. 
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. omega. 
  generalize (size_chunk_pos chunk); intros. intuition.
  eapply perm_drop_3; eauto.
Qed.

Lemma valid_access_drop_2:
  forall chunk b' ofs p', 
  valid_access m' chunk b' ofs p' -> valid_access m chunk b' ofs p'.
Proof.
  intros. destruct H; split; auto. 
  red; intros. eapply perm_drop_4; eauto. 
Qed.

Theorem load_drop:
  forall chunk b' ofs, 
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs = load chunk m b' ofs.
Proof.
  intros.
  unfold load.
  destruct (valid_access_dec m chunk b' ofs Readable).
  rewrite pred_dec_true.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP. simpl. auto.
  eapply valid_access_drop_1; eauto. 
  rewrite pred_dec_false. auto.
  red; intros; elim n. eapply valid_access_drop_2; eauto.
Qed.

Theorem loadbytes_drop:
  forall b' ofs n, 
  b' <> b \/ ofs + n <= lo \/ hi <= ofs \/ perm_order p Readable ->
  loadbytes m' b' ofs n = loadbytes m b' ofs n.
Proof.
  intros.
  unfold loadbytes.
  destruct (range_perm_dec m b' ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP. simpl. auto.
  red; intros.
  destruct (eq_block b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto. 
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. omega. intuition.
  eapply perm_drop_3; eauto. 
  rewrite pred_dec_false; eauto. 
  red; intros; elim n0; red; intros. 
  eapply perm_drop_4; eauto. 
Qed.



Lemma drop_perm_bounds:
  forall b',
    bounds_of_block m b' = bounds_of_block m' b'.
Proof.
  simp DROP.
Qed.

Lemma nat_mask_drop_perm:
  forall b',
    nat_mask m b' = nat_mask m' b'.
Proof.
  simp DROP.
Qed.

Lemma drop_perm_blocksize:
  mem_blocksize  m' = mem_blocksize m.
Proof.
  simp DROP.
Qed.

Lemma drop_perm_size_block:
  size_block  m' = size_block m.
Proof.
  simp DROP.
Qed.

Lemma drop_perm_mask:
  mask  m' = mask m.
Proof.
  simp DROP.
Qed.

Lemma drop_perm_nextblock:
  nextblock  m' = nextblock m.
Proof.
  simp DROP.
Qed.

Lemma drop_perm_mk_block_list:
  mk_block_list m = mk_block_list m'.
Proof.
  simp DROP.
Qed.

(* Lemma drop_perm_size_mem: *)
(*   size_mem m' = size_mem m. *)
(* Proof. *)
(*   simp DROP. *)
(* Qed. *)

End DROP.

Section DROPLIST.


  Variable bl: list (block*Z*Z).
  Variable m: mem.
Variable p: permission.
Variable m': mem.
Hypothesis DROP: drop_perm_list m bl p = Some m'.

Theorem mask_drop_perm_list:
  forall b',
    mask m b' = mask m' b'.
Proof.
  revert bl m p m' DROP; induction bl; simpl in *; intros; eauto.
  inv DROP; auto.
  repeat destr_in DROP. 
  erewrite IHl; [|eauto]. eapply mask_drop_perm; eauto.
Qed.

Theorem size_of_block_drop_perm_list:
  forall b',
    size_of_block m b' = size_of_block m' b'.
Proof.
  revert bl m p m' DROP; induction bl; simpl in *; intros; eauto.
  inv DROP; auto.
  repeat destr_in DROP. 
  erewrite IHl; [|eauto]. eapply size_of_block_drop_perm; eauto.
Qed.

Theorem nextblock_drop_list:
  nextblock m' = nextblock m.
Proof.
  revert bl m p m' DROP; induction bl; simpl in *; intros; eauto.
  inv DROP; auto.
  repeat destr_in DROP. 
  rewrite (nextblock_drop _ _ _ _ _ _ DROP).
  eauto.
Qed.

Theorem drop_perm_valid_block_1_list:
  forall b', valid_block m b' -> valid_block m' b'.
Proof.
  revert bl m p m' DROP; induction bl; simpl in *; intros; eauto.
  inv DROP; auto.
  repeat destr_in DROP. 
  eapply drop_perm_valid_block_1 in DROP; eauto.
Qed.

Theorem drop_perm_valid_block_2_list:
  forall b', valid_block m' b' -> valid_block m b'.
Proof.
  revert bl m p m' DROP; induction bl; simpl in *; intros; eauto.
  inv DROP; auto.
  repeat destr_in DROP. 
  eapply drop_perm_valid_block_2 in DROP; eauto.
Qed.



Theorem perm_drop_perm:
  forall m b lo hi p m',
    Mem.drop_perm m b lo hi p = Some m' ->
  forall bb ofs k p',
    perm m' bb ofs k p' <->
    (if eq_block b bb
     then
       if zle lo ofs && zlt ofs hi
       then perm_order p p'
       else perm m bb ofs k p'
     else perm m bb ofs k p').
Proof.
  clear; intros.
  repeat destr.
  - split; intros; destr. eapply perm_drop_2 with (ofs:=ofs); eauto.
    apply andb_true_iff in Heqb0. destr_and.
    destruct (zle lo ofs); destruct (zlt ofs hi); try discriminate; lia.
    subst; eauto.
    subst.
    revert H0; destr.
    eapply perm_drop_1 in H; eauto.
    eapply perm_implies; eauto.
    apply zle_zlt in Heqb0. auto.
  - apply andb_false_iff in Heqb0.
    des Heqb0.
    split; intros.
    eapply perm_drop_4; eauto.
    eapply perm_drop_3; eauto.
    des (zle lo ofs). right; left; lia.
    des (zlt ofs hi).
    split; intros.
    eapply perm_drop_4; eauto.
    eapply perm_drop_3; eauto.
    right; right; lia. 
  - split; intros. eapply perm_drop_4; eauto.
    eapply perm_drop_3; eauto.
Qed.


Lemma zle_zlt_false:
  forall a b c,
    zle a b && zlt b c = false -> b < a \/ b >= c.
Proof.
  intros.
  rewrite andb_false_iff in H.
  intuition.
  destruct (zle a b); try discriminate; lia.
  destruct (zlt b c); try discriminate; lia.
Qed.

Theorem perm_drop_perm_list:
  list_norepet (map fst (map fst bl)) ->
  forall b ofs k p',
    perm m' b ofs k p' <->
    ((In b (map fst (map fst bl)) ->
     forall lo hi,
       In (b,lo,hi) bl ->
       (lo <= ofs < hi ->
        perm_order p p') /\
       (~ (lo <= ofs < hi) -> perm m b ofs k p')) /\
     (~ In b (map fst (map fst bl)) -> perm m b ofs k p')).
Proof.
  revert bl m p m' DROP; induction bl; simpl in *; intros; eauto.
  inv DROP. tauto.
  destruct a as [[bb lo] hi].
  destruct (drop_perm_list m l p) eqn:?; try congruence.
  simpl in *. inv H.
  rewrite (perm_drop_perm _ _ _ _ _ _ DROP).
  repeat destr_cond_match; subst.
  - split; intros; auto.
    + split; intros; try congruence.
      destruct H1.
      inv H1.
      rewrite zle_zlt in Heqb0. tauto.
      rewrite map_map in H2.
      rewrite in_map_iff in H2.
      exfalso; apply H2.
      eexists; split; eauto.
      simpl; auto.
      exfalso; apply H0; auto.
    + destruct H as [A B].
      trim A; auto.
      specialize (A _ _ (or_introl eq_refl)).
      destruct A as [A C].
      apply A.
      apply zle_zlt; auto.
  - rewrite IHl; eauto.
    apply zle_zlt_false in Heqb0.
    split; intros; eauto.
    split; intros.
    repeat destr_and.
    destruct H1. inv H1.
    split; intros; try lia.
    apply H4.
    rewrite map_map, in_map_iff.
    intro; dex; destr_and. apply H2.
    rewrite map_map, in_map_iff.
    eexists; split; eauto.
    rewrite map_map, in_map_iff in H2.
    exfalso; apply H2.
    exists (b, lo0, hi0); split; simpl; auto.
    exfalso; apply H0; auto.
    destruct H.
    trim H; auto.
    specialize (H _ _ (or_introl eq_refl)).
    destruct H .
    split; try congruence.
    intros. apply H1. lia.
  - rewrite IHl; eauto.
    repeat split; intros; repeat destr_and; eauto;    destr; try des H0;
    try des H1.
    specialize (H i _ _ i0); destr_and; auto.
    specialize (H i _ _ i0); destr_and; auto.
    specialize (H (or_intror H0) _ _ (or_intror H1)); destr_and; auto.
    specialize (H (or_intror H0) _ _ (or_intror H1)); destr_and; auto.
Qed.

Lemma drop_perm_bounds_list:
  forall b',
    bounds_of_block m b' = bounds_of_block m' b'.
Proof.
  revert bl m p m' DROP; induction bl; simpl in *; intros; eauto.
  congruence.
  repeat destr_in DROP. 
  eapply drop_perm_bounds in DROP; eauto.
  erewrite IHl; eauto.
Qed.

Lemma nat_mask_drop_perm_list:
  forall b',
    nat_mask m b' = nat_mask m' b'.
Proof.
  revert bl m p m' DROP; induction bl; simpl in *; intros; eauto.
  congruence.
  repeat destr_in DROP. 
  eapply nat_mask_drop_perm in DROP; eauto.
  erewrite IHl; eauto.
Qed.

Lemma drop_perm_blocksize_list:
  mem_blocksize  m' = mem_blocksize m.
Proof.
  revert bl m p m' DROP; induction bl; simpl in *; intros; eauto.
  congruence.
  repeat destr_in DROP. 
  eapply drop_perm_blocksize in DROP; eauto.
  eapply IHl in Heqo; eauto.
  congruence. 
Qed.

Lemma drop_perm_size_block_list:
  size_block  m' = size_block m.
Proof.
  revert bl m p m' DROP; induction bl; simpl in *; intros; eauto.
  congruence.
  repeat destr_in DROP. 
  eapply drop_perm_size_block in DROP; eauto.
  rewrite DROP. erewrite IHl; eauto.
Qed.

Lemma drop_perm_mask_list:
  mask  m' = mask m.
Proof.
  revert bl m p m' DROP; induction bl; simpl in *; intros; eauto.
  congruence.
  repeat destr_in DROP. 
  eapply drop_perm_mask in DROP; eauto.
  apply IHl in Heqo; eauto. congruence.
Qed.

Lemma drop_perm_nextblock_list:
  nextblock  m' = nextblock m.
Proof.
  revert bl m p m' DROP; induction bl; simpl in *; intros; eauto.
  congruence.
  repeat destr_in DROP. 
  eapply drop_perm_nextblock in DROP; eauto.
  rewrite DROP; eapply IHl; eauto.
Qed.

Lemma drop_perm_mk_block_list_list:
  mk_block_list m = mk_block_list m'.
Proof.
  revert bl m p m' DROP; induction bl; simpl in *; intros; eauto.
  congruence.
  repeat destr_in DROP. 
  eapply drop_perm_mk_block_list in DROP; eauto.
  rewrite <- DROP; eapply IHl; eauto.
Qed.

(* Lemma drop_perm_size_mem_list: *)
(*   size_mem m' = size_mem m. *)
(* Proof. *)
(*   unfold size_mem. *)
(*   f_equal. intros. symmetry; eapply drop_perm_mk_block_list_list. *)
(* Qed. *)

Lemma drop_perm_contents:
  forall m b lo hi p m',
    drop_perm m b lo hi p = Some m' ->
    mem_contents m = mem_contents m'.
Proof.
  clear; intros.
  simp H.
Qed.

Lemma drop_perm_list_contents:
  mem_contents m = mem_contents m'.
Proof.
  revert bl m p m' DROP; induction bl; simpl in *; intros; eauto.
  congruence.
  repeat destr_in DROP. 
  eapply drop_perm_contents in DROP.
  apply IHl in Heqo. congruence.
Qed.

End DROPLIST.

(** * Generic injections *)

(** A memory state [m1] generically injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address.
*)

Lemma load_in_bound:
  forall chunk b ofs m v,
    load chunk m b ofs = Some v ->
    in_bound_m ofs m b.
Proof.
  intros.
  apply load_valid_access in H.
  destruct H as [A B].
  eapply perm_bounds.
  apply A; auto. destruct chunk; simpl; omega.
Qed.

Lemma alignment_of_size_inj:
  forall n n0,
    Z.max 0 n >= Z.max 0 n0 ->
    (alignment_of_size n >= alignment_of_size n0)%nat.
Proof.
  intros.
  rewrite ! Zmax_spec in H.
  unfold alignment_of_size.
  repeat destr_in H; repeat destr; omega.
Qed.

Ltac egt H :=
  match type of H with
  | context [get_type ?v = get_type ?v'] =>
      unfold get_type in H; destruct (wt_expr_dec v Tint);
       destruct (wt_expr_dec v Tfloat); destruct (wt_expr_dec v Tsingle);
       destruct (wt_expr_dec v Tlong); destruct (wt_expr_dec v' Tint);
       destruct (wt_expr_dec v' Tfloat); destruct (wt_expr_dec v' Tsingle);
       destruct (wt_expr_dec v' Tlong); destr
  end.


Lemma mr_vundef_get_type:
  forall mr (wf: wf_mr mr) v v'
    (Rel: mr v v'),
    same_eval v (Eval Vundef) \/
    get_type v = get_type v'.
Proof.
  intros.
  destruct (styp_eq (get_type v) (get_type v')); auto.
  left.
  
  destruct (mr_se_or_ld _ wf); subst.
  - 
    red; intros.
    specialize (Rel cm em).
    destruct (get_type_correct v), (get_type_correct v').
    + generalize (expr_type _ _ H cm em), (expr_type _ _ H0 cm em).
      rewrite Rel.
      seval; des (get_type v); des (get_type v').
    + rewrite (nwt_expr_undef cm em v') in Rel; auto.
    + rewrite (nwt_expr_undef cm em v) ; auto.
    + rewrite (nwt_expr_undef cm em v) ; auto.
  - 
    red; intros.
    specialize (Rel cm em).
    inv Rel; auto.
    destruct (get_type_correct v), (get_type_correct v').
    + generalize (expr_type _ _ H cm em), (expr_type _ _ H0 cm em).
      rewrite H1.
      seval; des (get_type v); des (get_type v').
    + rewrite (nwt_expr_undef cm em v') in H1; auto.
    + rewrite (nwt_expr_undef cm em v) ; auto.
    + rewrite (nwt_expr_undef cm em v) ; auto.
Qed.
    
Lemma list_forall2_and:
  forall A B P Q (l: list A) (l': list B),
    list_forall2 (fun a b => P a b) l l' ->
    list_forall2 (fun a b => Q a b) l l' ->
    list_forall2 (fun a b => P a b /\ Q a b) l l'.
Proof.
  induction 1; simpl; intros.
  constructor.
  inv H1.
  constructor; auto.
Qed.

Lemma match_eSexpr:
  forall al em a b c d e,
    eSexpr al em match a with
                   Tint => b
                 | Tlong => c
                 | Tfloat => d
                 | Tsingle => e
                 end =
    match a with
      Tint => eSexpr al em b
    | Tlong => eSexpr al em c
    | Tfloat => eSexpr al em d
    | Tsingle => eSexpr al em e
    end.
Proof.
  intros. 
  repeat destr.
Qed.

Lemma encode_val_memval_rel:
  forall mr (wf: wf_mr mr) v v' chunk,
    mr v v' ->
    list_forall2 (memval_rel mr) (encode_val chunk v) (encode_val chunk v').
Proof.
  intros mr wf v v' chunk SE.
  assert ((chunk = Many32 \/ chunk = Many64) \/ (chunk <> Many32 /\ chunk <> Many64)) by des chunk.
  destruct H as [ANY|NANY].
  Focus 2.
  inv wf; des chunk; repeat constructor; destr; try rewrite H; destr; eauto 11.
  
  des chunk.
  - destruct (mr_vundef_get_type _ wf _ _ SE) as [SU|GT].
    + apply list_forall2_and.
      * destruct (get_type_correct v') as [WT|NWT].
        generalize (expr_type _ _ WT). intros WTv.
        inv wf; destruct mr_se_or_ld; subst;
        repeat (apply list_forall2_cons || apply list_forall2_nil); red; intros; simpl;
        rewrite ! (match_eSexpr); simpl; try rewrite <- SE; rewrite SU; simpl; repeat destr; auto.
        assert (SU' : same_eval v' (Eval Vundef)).
        {
          red; intros; rewrite nwt_expr_undef; auto.
        }
        inv wf; destruct mr_se_or_ld; subst;
        repeat (apply list_forall2_cons || apply list_forall2_nil); red; intros; simpl;
        rewrite ! (match_eSexpr); simpl; try rewrite <- SE; rewrite SU; simpl; repeat destr; auto.
      * repeat (apply list_forall2_cons || apply list_forall2_nil);repeat destr;eauto; right; red; intros; destr; rewrite SU; destr.
    +   inv wf; repeat constructor; destr; rewrite GT; destr; eauto 10.
  - destruct (mr_vundef_get_type _ wf _ _ SE) as [SU|GT].
    + apply list_forall2_and.
      * destruct (get_type_correct v') as [WT|NWT].
        generalize (expr_type _ _ WT). intros WTv.
        inv wf; destruct mr_se_or_ld; subst;
        repeat (apply list_forall2_cons || apply list_forall2_nil); red; intros; simpl;
        rewrite ! (match_eSexpr); simpl; try rewrite <- SE; rewrite SU; simpl; repeat destr; auto.
        assert (SU' : same_eval v' (Eval Vundef)).
        {
          red; intros; rewrite nwt_expr_undef; auto.
        }
        inv wf; destruct mr_se_or_ld; subst;
        repeat (apply list_forall2_cons || apply list_forall2_nil); red; intros; simpl;
        rewrite ! (match_eSexpr); simpl; try rewrite <- SE; rewrite SU; simpl; repeat destr; auto.
      * repeat (apply list_forall2_cons || apply list_forall2_nil);repeat destr;eauto; right; red; intros; destr; rewrite SU; destr.
    +   inv wf; repeat constructor; destr; rewrite GT; destr; eauto 11.
Qed.

Lemma free_list_bounds_after:
  forall bl m m',
    Mem.free_list m bl = Some m' ->
    forall b lo0 hi0,
      Mem.bounds_of_block m' b = (lo0, hi0) ->
      hi0 - lo0 <> 0 ->
      Mem.bounds_of_block m b = (lo0, hi0).
Proof.
  induction bl; simpl; intros; auto.
  - inv H; auto.
  - destruct a as [[b' lo] hi].
    destruct (Mem.free m b' lo hi) eqn:?; try discriminate.
    eapply IHbl in H; eauto.
    destruct (Mem.free_bounds' _ _ _ _ _ b Heqo); auto.
    congruence.
    rewrite H in H2; inv H2; omega.
Qed.




Ltac genAlloc :=
  repeat match goal with
         | H: Mem.alloc ?m ?lo ?hi ?bt = Some (?m',?b') |- _ =>
           generalize (Mem.nextblock_alloc _ _ _ _ _ _ H);
             generalize (Mem.alloc_result _ _ _ _ _ _ H);
             let x := fresh in let y := fresh "NA" in
                               intros x y; subst; clear H;
                               try rewrite y in *
         end.

Lemma align_small:
  forall al (AlPos: al > 0) x (Xsmall: 0 < x <= al),
    align x al = al.
Proof.
  intros.
  unfold align.
  elim_div.
  intuition. 
  assert (z0 = x - 1 + al * (1 - z)) by lia. clear H; subst.
  assert (al * z >= 0) by lia.
  destruct (zeq 0 (al*z)).
  symmetry in e. apply Zmult_integral in e.
  destruct e. lia. subst.
  change (1 - 0) with 1 in *.
  rewrite Z.mul_1_r in *.
  assert (x - 1 < 0) by lia. assert (x = 0) by lia. subst.
  lia.
  generalize (Zmult_gt_0_lt_0_reg_r _ z AlPos).
  intro A. trim A. lia.

  destruct (zlt z 2).
  assert (z=1) by lia.
  subst; lia.
  clear - H3 H1 H0 g AlPos.
  exfalso.
  assert (x - 1 + al * (1 - z) < al * (2 - z)). lia.
  assert (2 - z <= 0). lia.

  apply Zmult_le_compat_l with (p:=al) in H2; lia.
Qed.

Lemma mul_lt_slack:
  forall a b c d,
    0 <= d < a ->
    a * b < a * c ->
    a * b < a * c - d.
Proof.
  intros.
  eapply (Z.le_lt_trans _ (a * (c-1))). 2: lia.
  assert (b < c). nia. nia.
Qed.

Lemma align_mul:
  forall al (AlPos: al > 0) x,
    align (x * al) al = x * al.
Proof.
  intros.
  unfold align. f_equal.
  eapply Zdiv_unique with (al - 1). lia. lia.
Qed.

Lemma align_big_smaller:
  forall z n, n >= 0 -> z >= 0 ->
         align (z+n) (two_power_nat MA) <= (two_power_nat MA) * n + align z (two_power_nat MA).
Proof.
  clear.
  intros.
  generalize (align_add _ (z+n) (z+ two_power_nat MA * n) (two_power_nat_pos MA)).
  intros.
  trim H1. split. lia. apply Zplus_le_compat_l.
  replace n with (1*n) at 1 by lia.
  apply Zmult_le_compat_r. generalize (two_power_nat_pos MA); lia. lia.
  etransitivity; eauto.
  replace (two_power_nat MA * n) with (align (two_power_nat MA * n) (two_power_nat MA)) at 1.
  rewrite (Z.add_comm z).
  rewrite <- align_distr.
  rewrite Z.mul_comm. rewrite align_mul. lia. apply two_power_nat_pos.
  apply two_power_nat_pos.
  rewrite Z.mul_comm. rewrite align_mul. auto.
  apply two_power_nat_pos.
Qed.

Lemma alloc_perm:
  forall m n m' b' bt
    (AB: Mem.alloc m 0 n bt = Some (m',b'))
    b o k p
    (Cond: Mem.perm m b o k p \/
           (b = b' /\ 0 <= o < n)),
    Mem.perm m' b o k p.
Proof.
  clear; intros.
  des Cond. 
  eapply Mem.perm_alloc_1; eauto.
  subst. des a. 
  eapply Mem.perm_implies. eapply Mem.perm_alloc_2; eauto. 
  constructor.
Qed.

Lemma alloc_perm_inv:
  forall m n m' b' bt
    (AB: Mem.alloc m 0 n bt = Some (m',b'))
    b o k p
    (PERM: Mem.perm m' b o k p),
    Mem.perm m b o k p \/
    (b = b' /\ 0 <= o < n).
Proof.
  clear; intros.
  eapply Mem.perm_alloc_inv in PERM; eauto.
  revert PERM; destr.
Qed.

Lemma alloc_lo_0:
  forall m lo hi bt,
    alloc m lo hi bt = alloc m 0 hi bt.
Proof.
  unfold alloc, low_alloc.
  intros; repeat destr.
  f_equal. f_equal.
  apply mkmem_ext; auto.
Qed.

Lemma in_bound_valid:
  forall m b o,
    Mem.in_bound_m o m b ->
    Mem.valid_block m b.
Proof.
  clear. intros.
  destruct (Mem.valid_block_dec m b).
  auto.
  unfold Mem.in_bound_m, Mem.bounds_of_block in H.
  rewrite Mem.bounds_mask_consistency in H.
  unfold in_bound in H; simpl in H; lia.
  apply Mem.msk_valid; auto.
Qed.

Lemma a_mask:
  forall m sz m' sp bt,
    Mem.alloc m 0 sz bt = Some (m',sp) ->
    forall b, Mem.mask m' b = if plt b sp then Mem.mask m b
                         else if peq b sp then Alloc.alignment_of_size sz
                              else O.
Proof.
  clear; intros.
  repeat destr.
  symmetry; eapply Mem.mask_alloc_other; eauto.
  intro; subst; xomega.
  subst.
  eapply Mem.alloc_mask; eauto.
  unfold Mem.mask. rewrite Mem.msk_valid; auto.
  rewrite (Mem.alloc_result _ _ _ _ _ _ H) in *.
  apply Mem.nextblock_alloc in H. rewrite H in *.
  xomega.
Qed.

Lemma a_mem_contents:
  forall m1 sz m2 sp bt (ALLOC: Mem.alloc m1 0 sz bt = Some (m2, sp)),
    Maps.PMap.get sp (Mem.mem_contents m2) = Mem.init_block 0 sz sp.
Proof.
  clear.
  Transparent Mem.alloc.
  unfold Mem.alloc, Mem.low_alloc.
  intros; destr_in ALLOC.
  inv ALLOC.
  simpl.
  rewrite Maps.PMap.gss. auto.
Qed.

Lemma a_mem_contents':
  forall m1 sz m2 sp bt (ALLOC: Mem.alloc m1 0 sz bt = Some (m2, sp)),
    (Mem.mem_contents m2) =
    Maps.PMap.set sp (Mem.init_block 0 sz sp) (Mem.mem_contents m1).
Proof.
  clear.
  intros.
  destr.
  subst.
  unfold Mem.alloc, Mem.low_alloc in ALLOC.
  destr_in ALLOC; inv ALLOC; simpl. auto.
Qed.

Lemma init_block_spec_out:
  forall ofs sz b,
    ofs < 0 \/ ofs >= sz ->
   Maps.ZMap.get ofs (Mem.init_block 0 sz b) = Symbolic (Eval Vundef) None 0.
Proof.
  clear.
  unfold Mem.init_block.
  intros. destr.
  rewrite Maps.ZMap.gi. auto.
Qed.

Lemma init_block_spec:
  forall ofs sz b,
    Maps.ZMap.get ofs (Mem.init_block 0 sz b) =
    Symbolic (if zle 0 ofs && zlt ofs sz
              then Eval Vundef (* Eundef b (Int.repr ofs) *)
              else Eval Vundef) None 0.
Proof.
  clear; intros.
  des (zle 0 ofs).
  des (zlt ofs sz).
  apply Mem.get_init_block. auto.
  rewrite init_block_spec_out; auto.
  rewrite init_block_spec_out; auto. lia.
Qed.

Require Import IntFacts.

Lemma get_getN:
  forall t1 t2
    (CONT : forall ofs, Maps.ZMap.get ofs t1 = Maps.ZMap.get ofs t2),
  forall n o, Mem.getN n o t1 = Mem.getN n o t2.
Proof.
  induction n; simpl; intros; eauto.
  f_equal; auto.
Qed.

Lemma same_access_same_perm:
  forall m1 m2
    (ACC: Mem.mem_access m1 = Mem.mem_access m2)
    b o k p,
    Mem.perm m1 b o k p <-> Mem.perm m2 b o k p.
Proof.
  intros.
  unfold Mem.perm.
  rewrite ACC; tauto.
Qed.

Lemma same_access:
  forall m1 m2
    (ACC: Mem.mem_access m1 = Mem.mem_access m2)
    chunk b ofs p,
    Mem.valid_access m1 chunk b ofs p <->
    Mem.valid_access m2 chunk b ofs p.
Proof.
  intros.
  unfold Mem.valid_access; split; intros; destr_and; split; auto;
  red; intros; rewrite same_access_same_perm; auto.
Qed.

Lemma load_contents_access:
  forall m1 m2 
    (CONT: forall b ofs,
        Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m1)) =
        Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m2)))
    (ACC: Mem.mem_access m1 = Mem.mem_access m2)
    b ofs chunk,
    Mem.load chunk m1 b ofs = Mem.load chunk m2 b ofs.
Proof.
  intros.
  Transparent Mem.load.
  unfold Mem.load.
  repeat destr.
  erewrite get_getN; eauto.
  rewrite same_access in v; eauto. congruence.
  rewrite <- same_access in v; eauto. congruence.
Qed.

Lemma perm_freelist:
  forall fbl m m' b ofs k p,
  Mem.free_list m fbl = Some m' ->
  Mem.perm m' b ofs k p ->
  Mem.perm m b ofs k p.
Proof.
  induction fbl; simpl; intros until p.
  congruence.
  destruct a as [[b' lo] hi]. case_eq (Mem.free m b' lo hi); try congruence.
  intros. eauto with mem.
Qed.

Lemma nextblock_freelist:
  forall fbl m m',
  Mem.free_list m fbl = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction fbl; intros until m'; simpl.
  congruence.
  destruct a as [[b lo] hi]. 
  case_eq (Mem.free m b lo hi); intros; try congruence.
  transitivity (Mem.nextblock m0). eauto. eapply Mem.nextblock_free; eauto.
Qed.

Hint Resolve two_power_nat_pos.

Lemma size_mem_blocks_rew:
  forall l z,
    align (Mem.size_mem_blocks l z) (two_power_nat MA) =
    align z (two_power_nat MA) + align (Mem.size_mem_blocks l 0) (two_power_nat MA).
Proof.
  induction l; simpl; intros; auto.
  rewrite align_0; eauto. lia. 
  rewrite IHl at 1.
  rewrite <- align_distr; auto.
  rewrite <- Z.add_assoc. f_equal.
  rewrite <- IHl. rewrite align_0; auto.
Qed.

Lemma exact_bounds_perm_free_list:
  forall e m m'
         (* (BOUNDS: forall b lo hi,  *)
         (*            In (b,lo,hi) e -> *)
         (*            Mem.bounds_of_block m b = (lo,hi)) *)
         (LNR: list_norepet (map (fun a => fst (fst a)) e))
         (FREELIST: Mem.free_list m e = Some m'),
  forall b, 
    In b (map (fun a => fst (fst a)) e) ->
    Mem.bounds_of_block m' b = (0,0).
Proof.
  induction e; simpl in *; intros; auto.
  intuition congruence. 
  destruct a as [[b' lo] hi].
  simpl in *.
  destruct (Mem.free m b' lo hi) eqn:?; try congruence.
  (* generalize (BOUNDS _ _ _ (or_introl eq_refl)). intro BOUNDSb'. *)
  unfold Mem.free in Heqo.

  repeat destr_in Heqo; inv Heqo.
  destruct H; subst; auto.
  - (* generalize (BOUNDS b lo hi (or_introl eq_refl)). intros. *)
    erewrite Mem.bounds_freelist; eauto.
    clear FREELIST.
    rewrite Mem.unchecked_free_bounds'.
    rewrite! pred_dec_true; auto.
    unfold has_bounds in Heqb0; repeat destr_in Heqb0. 
    des (zeq lo z); des (zeq hi z0); auto.
    des (zeq z z); des (zeq z0 z0); auto.
    inv LNR; auto.
  - apply IHe with (m := Mem.unchecked_free m b' lo hi) (m':=m') ; eauto.
    intros.
    clear FREELIST.
    inv LNR; auto.
Qed.

Lemma exact_bounds_free_list:
  forall e m m'
         (LNR: list_norepet (map (fun a => fst (fst a)) e))
         (FREELIST: Mem.free_list m e = Some m'),
  forall b, 
    In b (map (fun a => fst (fst a)) e) ->
    Mem.bounds_of_block m' b = (0,0) /\
    (forall k p ofs,
      ~ Mem.perm m' b ofs k p).
Proof.
  intros.
  eapply exact_bounds_perm_free_list in FREELIST; eauto.
  split; auto.
  intros. intro.
  apply Mem.perm_bounds in H0.
  unfold Mem.in_bound_m in *.
  rewrite FREELIST in H0.
  unfold in_bound in H0; simpl in H0; omega.
Qed.

Lemma free_list_freeable:
  forall l m m',
  Mem.free_list m l = Some m' ->
  forall b lo hi,
  In (b, lo, hi) l -> Mem.range_perm m b lo hi Cur Freeable.
Proof.
  induction l; simpl; intros.
  contradiction.
  repeat destr_in H. des H0. inv e.  
  eapply free_range_perm; eauto.
  red; intros. eapply Mem.perm_free_3; eauto. exploit IHl; eauto.
Qed.

Lemma nextblock_storev:
  forall chunk m addr v m',
  Mem.storev chunk m addr v = Some m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  unfold Mem.storev; intros.
  destruct (Mem.mem_norm m addr); try discriminate.
  eapply Mem.nextblock_store; eauto.
Qed.


Remark free_list_nextblock:
  forall l m m',
  Mem.free_list m l = Some m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction l; simpl; intros.
  congruence.
  destruct a. destruct p. destruct (Mem.free m b z0 z) as [m1|] eqn:?; try discriminate.
  transitivity (Mem.nextblock m1). eauto. eapply Mem.nextblock_free; eauto. 
Qed.

Remark free_list_load:
  forall chunk b' l m m',
  Mem.free_list m l = Some m' ->
  (forall b lo hi, In (b, lo, hi) l -> Plt b' b) ->
  Mem.load chunk m' b' 0 = Mem.load chunk m b' 0.
Proof.
  induction l; simpl; intros.
  inv H; auto.
  destruct a. destruct p. destruct (Mem.free m b z0 z) as [m1|] eqn:?; try discriminate.
  transitivity (Mem.load chunk m1 b' 0). eauto. 
  eapply Mem.load_free. eauto. left. assert (Plt b' b) by eauto. unfold block; xomega.
Qed.




Lemma store_storev:
  forall m c b v m',
    Mem.store c m b (Int.unsigned Int.zero) v = Some m' ->
    Mem.storev c m (Eval (Vptr b Int.zero)) v = Some m'.
Proof.
  intros.
  unfold Mem.storev.
  rewrite norm_val. auto. 
Qed.

Lemma free_list_perm':
  forall b lo hi l m m',
  Mem.free_list m l = Some m' ->
  In (b, lo, hi) l ->
  Mem.range_perm m b lo hi Cur Freeable.
Proof.
  induction l; simpl; intros.
  contradiction.
  destruct a as [[b1 lo1] hi1]. 
  destruct (Mem.free m b1 lo1 hi1) as [m1|] eqn:?; try discriminate.
  destruct H0. inv H0. eapply Mem.free_range_perm; eauto. 
  red; intros. eapply Mem.perm_free_3; eauto. eapply IHl; eauto. 
Qed.

Lemma memval_rel_refl:
  forall mr mv (WF: wf_mr mr),
    memval_rel mr mv mv.
Proof.
  split. apply mr_refl; auto.
  left; apply same_type_memval_refl.
Qed.

Lemma storev_bounds:
  forall chunk m1 ptr v m2,
    Mem.storev chunk m1 ptr v = Some m2 ->
    forall b,
      Mem.bounds_of_block m1 b = Mem.bounds_of_block m2 b.
Proof.
  intros chunk m1 ptr v m2.
  unfold Mem.storev; repeat destr.
  eapply Mem.bounds_of_block_store; eauto.
Qed.


Lemma storev_addr_lessdef:
  forall m chunk vaddr vaddr' v m',
    Val.lessdef vaddr vaddr' ->
    storev chunk m vaddr  v = Some m' ->
    storev chunk m vaddr' v = Some m'.
Proof.
  intros m chunk vaddr vaddr' v m' SE.
  unfold storev; destr_cond_match; try discriminate.
  generalize (lessdef_eqm m  _ _ SE). rewrite Heqv0.
  intro A; inv A.
  tauto.
Qed.



Lemma perm_unchecked_free:
  forall 
    m bb lo hi
    (Bnds: Mem.bounds_of_block m bb = (lo,hi))
    m'
    (UFL: Mem.unchecked_free m bb lo hi = m')
    b o k p,
    Mem.perm m' b o k p <->
    (b <> bb /\ Mem.perm m b o k p).
Proof.
  intros.
  unfold Mem.unchecked_free in UFL.
  inv UFL.
  unfold Mem.perm. simpl.
  rewrite Maps.PMap.gsspec.
  repeat destr.
  apply zle_zlt_false in Heqb0. subst.
  split; intros; destr.
  des (Maps.PMap.get bb (Mem.mem_access m) o k).
  trim (Mem.access_bounds_ok m bb o k).
  congruence. unfold Alloc.get_bounds.
  unfold Mem.bounds_of_block in Bnds.
  rewrite Bnds. unfold in_bound; simpl.
  des (zle lo o); des (zlt o hi); lia.
Qed.

Lemma perm_free_eq:
  forall m b lo hi m'
    (FREE: Mem.free m b lo hi = Some m')
    (BND: Mem.bounds_of_block m b = (lo,hi))
    b' o k p
    (PERM: Mem.perm m' b' o k p),
    Mem.perm m b' o k p /\ b <> b'.
Proof.
  intros.
  split. eauto with mem.
  Transparent Mem.free.
  unfold Mem.free in FREE.
  repeat destr_in FREE. inv FREE.
  rewrite perm_unchecked_free in PERM; eauto.
  destr.
Qed.


Lemma free_bounds_exact:
  forall m b lo hi m' 
    (Free: Mem.free m b lo hi = Some m')
    b',
    Mem.bounds_of_block m' b' =
    if eq_block b b'
    then (0,0)
    else Mem.bounds_of_block m b'.
Proof.
  intros.
  generalize (Mem.bounds_free _ _ _ b' _ _ Free).
  Local Transparent Mem.free.
  unfold Mem.free in Free.
  repeat destr_in Free;
  inv Free.
  destr.
  subst. intros _.
  rewrite unchecked_free_bounds'.
  repeat destr.
  unfold has_bounds in Heqb0; repeat destr_in Heqb0; inv Heqb0. inv Heqp.
  des (zeq lo z); des (zeq hi z0).
  des (zeq z z); des (zeq z0 z0).
Qed.



Lemma unchecked_free_contents:
  forall m bb lo hi,
    Mem.mem_contents (Mem.unchecked_free m bb lo hi) = Mem.mem_contents m.
Proof.
  reflexivity.
Qed.


Lemma nextblock_unchecked_free:
  forall b lo hi m,
    Mem.nextblock m = Mem.nextblock (Mem.unchecked_free m b lo hi).
Proof.
  intros.
  reflexivity.
Qed.


Lemma Zeq_ge:
  forall x y, x = y -> x >= y.
Proof. intros; lia. Qed.

Lemma bounds_dec:
  forall m b lo hi,
    {bounds_of_block m b = (lo,hi)} + {bounds_of_block m b <> (lo,hi)}.
Proof.
  decide equality. 
Qed.

(** Preservation of [drop_perm] operations. *)


Definition meminj_no_overlap (f: meminj) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
    b1 <> b2 ->
    f b1 = Some (b1', delta1) ->
    f b2 = Some (b2', delta2) ->
      perm m b1 ofs1 Max Nonempty ->
      perm m b2 ofs2 Max Nonempty ->
      b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

  Definition meminj_no_overlap' (f: meminj) (m: mem) : Prop :=
    forall b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
      b1 <> b2 ->
      f b1 = Some (b1', delta1) ->
      f b2 = Some (b2', delta2) ->
      in_bound_m ofs1 m b1 ->
      in_bound_m ofs2 m b2 ->
      b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

  Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
    (two_power_nat (alignment_of_size size) | delta).
  
Section MEMINJ.

  Variable sm: bool.
  Variable ei: meminj -> expr_sym -> expr_sym -> Prop.
  Hypothesis WF : wf_inj ei.
  
  Record mem_inj  (f: meminj) (m1 m2: mem) : Prop :=
    mk_mem_inj {
        mi_perm:
          forall b1 b2 delta ofs k p,
            f b1 = Some(b2, delta) ->
            perm m1 b1 ofs k p ->
            perm m2 b2 (ofs + delta) k p;
        mi_bounds:                  (**r we mimic [mi_perm] with bounds instead of permissions.  *)
          forall b1 b2 delta ofs,
            f b1 = Some(b2, delta) ->
            in_bound_m ofs m1 b1 ->
            in_bound_m (ofs+delta) m2 b2;
        mi_align':
          forall b b0 z,            (**r we can now talk of the alignment of blocks  *)
            f b = Some (b0, z) ->
            (mask m2 b0 >= mask m1 b)%nat /\
            Z.divide (two_p (Z.of_nat (mask m1 b))) z;
        mi_memval:
          forall b1 ofs b2 delta,
            f b1 = Some(b2, delta) ->
            perm m1 b1 ofs Cur Readable ->
            memval_inject ei f 
                       (ZMap.get ofs m1.(mem_contents)#b1) 
                       (ZMap.get (ofs+delta) m2.(mem_contents)#b2);
        mi_size_mem:                (**r [m2] must be ``smaller'' than [m1].  *)
          sm = true ->
          (nb_boxes_used_m m2 <= nb_boxes_used_m m1)%nat
      }.
  
  (* The old invariant is now provable. *)
  Lemma mi_align:
    forall f m1 m2,
      mem_inj f m1 m2 ->
      forall (b1 b2: block) delta, 
        f b1 = Some (b2, delta) ->
        forall chunk ofs p,
          range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p ->
          (align_chunk chunk | delta).
  Proof.
    intros.
    assert (size_block m1 b1 >= size_chunk chunk).
    {
      generalize (H1 ofs).
      generalize (H1 (ofs + size_chunk chunk - 1)).
      intros A B.
      trim A. des chunk; omega.
      trim B. des chunk; omega.
      apply perm_bounds in A.
      apply perm_bounds in B.
      unfold in_bound_m in *.
      unfold bounds_of_block in *.
      unfold size_block, get_size.
      destr; try des p0; unfold in_bound_m, in_bound in *; des chunk; simpl in *; try omega.
    }
    generalize (mi_align' _ _ _ H _ _ _ H0).
    intros [_ A].
    eapply Zdivides_trans; eauto.
    unfold mask.
    destr.
    - apply alignment_ok in Heqo. destruct Heqo as [B C]. 
      unfold size_block in H2. unfold get_size in *.
      revert C; destr.
      des p0.
      intros. apply Zdivides_trans with (y:=two_p (Z.of_nat (alignment_of_size (size_chunk chunk)))).
      des chunk; 
        try (exists 1; simpl; auto; fail);
        try (exists 2; simpl; auto; fail).
      apply Zdivides_trans with (y:=two_p (Z.of_nat (alignment_of_size (z0-z)))).
      exists (two_p (Z.of_nat (alignment_of_size (z0-z) - alignment_of_size (size_chunk chunk)))).
      rewrite <- two_p_is_exp; try omega.
      rewrite <- Nat2Z.inj_add. f_equal. f_equal. 
      generalize (alignment_of_size_inj (z0-z) (size_chunk chunk)).
      intro D; trim D.
      rewrite ! Zmax_spec. repeat destr;omega. omega.
      exists (two_p (Z.of_nat (n - alignment_of_size (z0-z)))).
      rewrite <- two_p_is_exp; try omega.
      rewrite <- Nat2Z.inj_add. f_equal. f_equal. 
      omega.
      intros; des chunk; omega.
    - eapply bounds_mask_consistency in Heqo.
      unfold size_block, get_size in H2.
      rewrite Heqo in H2.
      des chunk; omega.
  Qed.

  (** Preservation of permissions *)

  Lemma perm_inj:
    forall f m1 m2 b1 ofs k p b2 delta,
      mem_inj f m1 m2 ->
      perm m1 b1 ofs k p ->
      f b1 = Some(b2, delta) ->
      perm m2 b2 (ofs + delta) k p.
  Proof.
    intros. eapply mi_perm; eauto. 
  Qed.

  Lemma range_perm_inj:
    forall f m1 m2 b1 lo hi k p b2 delta,
      mem_inj f m1 m2 ->
      range_perm m1 b1 lo hi k p ->
      f b1 = Some(b2, delta) ->
      range_perm m2 b2 (lo + delta) (hi + delta) k p.
  Proof.
    intros; red; intros.
    replace ofs with ((ofs - delta) + delta) by omega.
    eapply perm_inj; eauto. apply H0. omega.
  Qed.

  Lemma valid_access_inj:
    forall f m1 m2 b1 b2 delta chunk ofs p,
      mem_inj f m1 m2 ->
      f b1 = Some(b2, delta) ->
      valid_access m1 chunk b1 ofs p ->
      valid_access m2 chunk b2 (ofs + delta) p.
  Proof.
    intros. destruct H1 as [A B]. constructor.
    replace (ofs + delta + size_chunk chunk)
    with ((ofs + size_chunk chunk) + delta) by omega.
    eapply range_perm_inj; eauto.
    apply Z.divide_add_r; auto. eapply mi_align; eauto with mem.
  Qed.

  (** Preservation of loads. *)

  Lemma getN_inj:
    forall f m1 m2 b1 b2 delta,
      mem_inj f m1 m2 ->
      f b1 = Some(b2, delta) ->
      forall n ofs,
        range_perm m1 b1 ofs (ofs + Z_of_nat n) Cur Readable ->
        list_forall2 (memval_inject ei f) 
                     (getN n ofs (m1.(mem_contents)#b1))
                     (getN n (ofs + delta) (m2.(mem_contents)#b2)).
  Proof.
    induction n; intros; simpl.
    constructor.
    rewrite inj_S in H1. 
    constructor. 
    eapply mi_memval; eauto.
    apply H1. omega.  
    replace (ofs + delta + 1) with ((ofs + 1) + delta) by omega.
    apply IHn. red; intros; apply H1; omega. 
  Qed.

  Lemma load_inj:
    forall f m1 m2 chunk b1 ofs b2 delta v1
           (MIG: mem_inj f m1 m2)
           (LOAD: load chunk m1 b1 ofs = Some v1)
           (FB: f b1 = Some (b2, delta)),
    exists v2,
      load chunk m2 b2 (ofs + delta) = Some v2 /\
      ei f v1 v2.
  Proof.
    intros.
    exists (decode_val chunk (getN (size_chunk_nat chunk) (ofs + delta) (m2.(mem_contents)#b2))).
    split.
    - unfold load. apply pred_dec_true. 
      eapply valid_access_inj; eauto with mem.
    - exploit load_result; eauto. intro C; rewrite C.
      apply decode_val_inject; auto.
      apply getN_inj; auto. 
      rewrite <- size_chunk_conv.
      exploit load_valid_access; eauto. intros [A B]. auto.
  Qed.

  Lemma loadbytes_inj:
    forall f m1 m2 len b1 ofs b2 delta bytes1,
      mem_inj f m1 m2 ->
      loadbytes m1 b1 ofs len = Some bytes1 ->
      f b1 = Some (b2, delta) ->
      exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
                     /\ list_forall2 (memval_inject ei f) bytes1 bytes2.
  Proof.
    intros. unfold loadbytes in *. 
    destruct (range_perm_dec m1 b1 ofs (ofs + len) Cur Readable); inv H0.
    exists (getN (nat_of_Z len) (ofs + delta) (m2.(mem_contents)#b2)).
    split. apply pred_dec_true.  
    replace (ofs + delta + len) with ((ofs + len) + delta) by omega.
    eapply range_perm_inj; eauto with mem. 
    apply getN_inj; auto. 
    destruct (zle 0 len). rewrite nat_of_Z_eq; auto. omega. 
    rewrite nat_of_Z_neg. simpl. red; intros; omegaContradiction. omega.
  Qed.

  (** Preservation of stores. *)

  Lemma setN_inj:
    forall (access: Z -> Prop) delta m f vl1 vl2,
      list_forall2 (memval_inject m f) vl1 vl2 ->
      forall p c1 c2,
        (forall q, access q -> memval_inject m f (ZMap.get q c1) (ZMap.get (q + delta) c2)) ->
        (forall q, access q -> memval_inject m f (ZMap.get q (setN vl1 p c1)) 
                                             (ZMap.get (q + delta) (setN vl2 (p + delta) c2))).
  Proof.
    induction 1; intros; simpl. 
    auto.
    replace (p + delta + 1) with ((p + 1) + delta) by omega.
    apply IHlist_forall2; auto. 
    intros. rewrite ZMap.gsspec at 1. destruct (ZIndexed.eq q0 p). subst q0.
    rewrite ZMap.gss. auto. 
    rewrite ZMap.gso. auto. unfold ZIndexed.t in *. omega.
  Qed.
  

  Lemma filter_ext:
    forall A p p' (l: list A),
      (forall b, p b = p' b) ->
      filter p l = filter p' l.
  Proof.
    induction l; simpl; intros; eauto.
    rewrite H; destr. 
  Qed.

  Lemma nb_extra_store:
    forall chunk m1 b ofs v m2 (STORE: store chunk m1 b ofs v = Some m2),
      nb_extra m1 = nb_extra m2.
  Proof.
    intros.
    unfold store in STORE. destr_in STORE. inv STORE. reflexivity.
  Qed.


  Lemma nb_extra_storebytes:
    forall m1 b ofs v m2 (STORE: storebytes m1 b ofs v = Some m2),
      nb_extra m1 = nb_extra m2.
  Proof.
    intros.
    unfold storebytes in STORE. destr_in STORE. inv STORE. reflexivity.
  Qed.


  Lemma nb_extra_low_alloc:
    forall m1 lo hi bt al b m2 (STORE: low_alloc m1 lo hi al bt = Some (m2, b)),
      nb_extra m1 = nb_extra m2.
  Proof.
    intros.
    unfold alloc, low_alloc in STORE. destr_in STORE. inv STORE. reflexivity.
  Qed.

  Lemma nb_extra_alloc:
    forall m1 lo hi bt b m2 (STORE: alloc m1 lo hi bt = Some (m2, b)),
      nb_extra m1 = nb_extra m2.
  Proof.
    intros.
    unfold alloc, low_alloc in STORE. destr_in STORE. inv STORE. reflexivity.
  Qed.


  Lemma nb_extra_unchecked_free:
    forall m1 lo hi b,
      nb_extra m1 = nb_extra (unchecked_free m1 b lo hi).
  Proof.
    intros.
    unfold unchecked_free. reflexivity.
  Qed.

  Lemma nb_extra_free:
    forall m1 lo hi b m2 (STORE: free m1 b lo hi = Some m2),
      nb_extra m1 = nb_extra m2.
  Proof.
    intros.
    unfold free in STORE. destr_in STORE. destr_in STORE. inv STORE. reflexivity.
  Qed.

  
  Lemma nb_extra_drop_perm:
    forall m1 b lo hi p m2 (STORE: drop_perm m1 b lo hi p = Some m2),
      nb_extra m1 = nb_extra m2.
  Proof.
    intros.
    unfold drop_perm in STORE. destr_in STORE. inv STORE. reflexivity.
  Qed.



  Lemma nb_extra_free_list:
    forall bl m1 m2 (STORE: free_list m1 bl = Some m2),
      nb_extra m1 = nb_extra m2.
  Proof.
    induction bl; simpl; intros; auto.
    inv STORE; auto.
    repeat destr_in STORE.
    apply IHbl in STORE.
    erewrite (nb_extra_free m1). 2: eauto. auto.
  Qed.




  Lemma nb_boxes_used_same:
    forall m1 m2,
      mk_block_list m1 = mk_block_list m2 ->
      nb_extra m1 = nb_extra m2 ->
      nb_boxes_used_m m1 = nb_boxes_used_m m2.
  Proof.
    unfold nb_boxes_used_m; intros. congruence.
  Qed.


  Ltac rew_nb_extra :=
    repeat
      match goal with
      | H: store _ ?m1 _ _ _ = Some ?m2 |- context [nb_extra ?m2] => rewrite <- (nb_extra_store _ _ _ _ _ _ H)
      | H: storebytes ?m1 _ _ _ = Some ?m2 |- context [nb_extra ?m2] => rewrite <-  (nb_extra_storebytes _ _ _ _ _ H)
      | H: drop_perm ?m1 _ _ _ _ = Some ?m2 |- context [nb_extra ?m2] => rewrite <-  (nb_extra_drop_perm _ _ _ _ _ _ H)
      end.


  Ltac rew_mk_block_list :=
    repeat
      match goal with
      | H: store _ ?m1 _ _ _ = Some ?m2 |- context [mk_block_list ?m2] => rewrite (store_mk_block_list _ _ _ _ _ _ H)
      | H: storebytes ?m1 _ _ _ = Some ?m2 |- context [mk_block_list ?m2] => rewrite (storebytes_mk_block_list _ _ _ _ _ H)
      | H: drop_perm ?m1 _ _ _ _ = Some ?m2 |- context [mk_block_list ?m2] => rewrite <- (drop_perm_mk_block_list _ _ _ _ _ _ H)
      end.



  Lemma nb_boxes_used_cons:
    forall a b l,
      nb_boxes_used ((a,b)::l) = (nb_boxes_used l + box_span b)%nat.
  Proof.
    unfold nb_boxes_used. simpl. intros. apply fold_left_plus_rew.
  Qed.

  Lemma nb_boxes_alloc:
    forall m1 lo hi bt b m2,
      alloc m1 lo hi bt = Some (m2, b) ->
      nb_boxes_used_m m2 = (nb_boxes_used_m m1 + box_span (Z.max 0 hi))%nat.
  Proof.
    unfold nb_boxes_used_m.
    intros.
    rewrite (nb_extra_alloc _ _ _ _ _ _ H).
    unfold mk_block_list.
    unfold alloc, low_alloc in H. destr_in H. inv H. simpl. unfold size_block; simpl.
    erewrite mk_block_list_aux_eq. 2: apply MA_bound.
    rewrite nb_boxes_used_cons. rewrite Z.sub_0_r. lia.
  Qed.


  Ltac solve_size_mem :=
    match goal with
    | H: alloc ?m1 _ _ _ = Some (?m2,_) |- context [nb_boxes_used_m ?m2] => rewrite (nb_boxes_alloc _ _ _ _ _ _ H)
    | H: mem_inj _ _ _ |- _ => unfold nb_boxes_used_m; rew_mk_block_list; rew_nb_extra; inv H; auto
    | |- _ => unfold nb_boxes_used_m; rew_mk_block_list; rew_nb_extra; auto
    end.



  
  Lemma store_mapped_inj:
    forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2
      (* (Trel: chunk = Many32 \/ chunk = Many64 -> get_type v1 = get_type v2) *),
      mem_inj f m1 m2 ->
      store chunk m1 b1 ofs v1 = Some n1 ->
      meminj_no_overlap f m1 ->
      f b1 = Some (b2, delta) ->
      ei f v1 v2 ->
      exists n2,
        store chunk m2 b2 (ofs + delta) v2 = Some n2
        /\ mem_inj f n1 n2.
  Proof.
    intros.
    assert (valid_access m2 chunk b2 (ofs + delta) Writable).
    { eapply valid_access_inj; eauto with mem. }
    destruct (valid_access_store _ _ _ _ v2 H4) as [n2 STORE]. 
    exists n2; split. auto.
    constructor.
    - (* perm *)
      intros. eapply perm_store_1; [eexact STORE|].
      eapply mi_perm; eauto.
      eapply perm_store_2; eauto. 
    - (* bounds *)
      intros. eapply store_in_bound_m_2 in H6; eauto.
      eapply store_in_bound_m_1; eauto.
      eapply mi_bounds; eauto.
    - intros. erewrite store_mask; eauto.
      erewrite store_mask with (m':=n1); eauto.
      eapply mi_align'; eauto.
    - (* mem_contents *)
      intros.
      rewrite (store_mem_contents _ _ _ _ _ _ H0).
      rewrite (store_mem_contents _ _ _ _ _ _ STORE).
      rewrite ! PMap.gsspec. 
      destruct (peq b0 b1). subst b0.
      + (* block = b1, block = b2 *)
        assert (b3 = b2) by congruence. subst b3.
        assert (delta0 = delta) by congruence. subst delta0.
        rewrite peq_true.
        apply setN_inj with (access := fun ofs => perm m1 b1 ofs Cur Readable).
        apply encode_val_inject; auto. intros. eapply mi_memval; eauto. eauto with mem. 
      + destruct (peq b3 b2). subst b3.
        * (* block <> b1, block = b2 *)
          rewrite setN_other. eapply mi_memval; eauto. eauto with mem. 
          erewrite encode_val_length; eauto. rewrite <- size_chunk_conv. intros. 
          assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
          eapply H1; eauto. eauto 6 with mem.
          exploit store_valid_access_3. eexact H0. intros [A B].
          eapply perm_implies. apply perm_cur_max. apply A. omega. auto with mem.
          destruct H8. congruence. omega.
        * (* block <> b1, block <> b2 *)
          eapply mi_memval; eauto. eauto with mem. 
    - solve_size_mem. 
  Qed.

  Lemma store_unmapped_inj:
    forall f chunk m1 b1 ofs v1 n1 m2,
      mem_inj f m1 m2 ->
      store chunk m1 b1 ofs v1 = Some n1 ->
      f b1 = None ->
      mem_inj f n1 m2.
  Proof.
    intros. constructor.
    - (* perm *)
      intros. eapply mi_perm; eauto with mem.
    - (* bounds *)
      intros.
      eapply store_in_bound_m_2 in H3; eauto.
      eapply mi_bounds; eauto.
    - intros.
      erewrite store_mask with (m':=n1); eauto.
      eapply mi_align'; eauto.
    - (* mem_contents *)
      intros. 
      rewrite (store_mem_contents _ _ _ _ _ _ H0).
      rewrite PMap.gso. eapply mi_memval; eauto with mem. 
      congruence.
    - solve_size_mem. 
  Qed.

  Lemma store_outside_inj:
    forall f m1 m2 chunk b ofs v m2',
      mem_inj f m1 m2 ->
      (forall b' delta ofs',
         f b' = Some(b, delta) ->
         perm m1 b' ofs' Cur Readable -> 
         ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
      store chunk m2 b ofs v = Some m2' ->
      mem_inj f m1 m2'.
  Proof.
    intros. inv H. constructor; eauto with mem.
    - (* bounds *)
      intros. eapply store_in_bound_m_1 ; eauto.
    - intros. erewrite store_mask; eauto.
    - (* mem_contents *)
      intros. 
      rewrite (store_mem_contents _ _ _ _ _ _ H1).
      rewrite PMap.gsspec. destruct (peq b2 b). subst b2. 
      rewrite setN_outside. auto. 
      erewrite encode_val_length; eauto. rewrite <- size_chunk_conv. 
      destruct (zlt (ofs0 + delta) ofs); auto.
      destruct (zle (ofs + size_chunk chunk) (ofs0 + delta)). omega. 
      byContradiction. eapply H0; eauto. omega. 
      eauto with mem.
    - solve_size_mem. 
  Qed.

Lemma storebytes_mapped_inj:
  forall f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  mem_inj f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  meminj_no_overlap f m1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject ei f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ mem_inj f n1 n2.
Proof.
  intros. inversion H. 
  assert (range_perm m2 b2 (ofs + delta) (ofs + delta + Z_of_nat (length bytes2)) Cur Writable).
  {
    replace (ofs + delta + Z_of_nat (length bytes2))
    with ((ofs + Z_of_nat (length bytes1)) + delta).
    eapply range_perm_inj; eauto with mem. 
    eapply storebytes_range_perm; eauto.
    rewrite (list_forall2_length H3). omega.
  }
  destruct (range_perm_storebytes _ _ _ _ H4) as [n2 STORE]. 
  exists n2; split. eauto.
  constructor.
  - (* perm *)
    intros.
    eapply perm_storebytes_1; [apply STORE |].
    eapply mi_perm0; eauto.
    eapply perm_storebytes_2; eauto.
  - intros.
    eapply storebytes_in_bound_m_2 in H6; eauto.
    eapply storebytes_in_bound_m_1; eauto.
  - intros.
    erewrite <- mask_storebytes; eauto.
    erewrite <- mask_storebytes with (m2:=n1); eauto.
  - (* mem_contents *)
    intros.
    assert (perm m1 b0 ofs0 Cur Readable). eapply perm_storebytes_2; eauto. 
    rewrite (storebytes_mem_contents _ _ _ _ _ H0).
    rewrite (storebytes_mem_contents _ _ _ _ _ STORE).
    rewrite ! PMap.gsspec. destruct (peq b0 b1). subst b0.
    + (* block = b1, block = b2 *)
      assert (b3 = b2) by congruence. subst b3.
      assert (delta0 = delta) by congruence. subst delta0.
      rewrite peq_true.
      apply setN_inj with (access := fun ofs => perm m1 b1 ofs Cur Readable); auto.
    + destruct (peq b3 b2). subst b3.
      * (* block <> b1, block = b2 *)
        rewrite setN_other. auto.
        intros.
        assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
        eapply H1; eauto 6 with mem.
        exploit storebytes_range_perm. eexact H0. 
        instantiate (1 := r - delta). 
        rewrite (list_forall2_length H3). omega.
        eauto 6 with mem.
        destruct H9. congruence. omega.
      * (* block <> b1, block <> b2 *)
        eauto.
    - solve_size_mem. 
Qed.

Lemma storebytes_unmapped_inj:
  forall f m1 b1 ofs bytes1 n1 m2,
    mem_inj f m1 m2 ->
    storebytes m1 b1 ofs bytes1 = Some n1 ->
    f b1 = None ->
    mem_inj f n1 m2.
Proof.
  intros. inversion H.
  constructor.
  - (* perm *)
    intros. eapply mi_perm0; eauto. eapply perm_storebytes_2; eauto. 
  -  intros.
     eapply storebytes_in_bound_m_2 in H3; eauto. 
  - intros. 
    erewrite <- mask_storebytes with (m2:=n1); eauto.
  -(* mem_contents *)
    intros. 
    rewrite (storebytes_mem_contents _ _ _ _ _ H0).
    rewrite PMap.gso. eapply mi_memval0; eauto. eapply perm_storebytes_2; eauto.
    congruence.
  - solve_size_mem. 
Qed.

Lemma storebytes_outside_inj:
  forall f m1 m2 b ofs bytes2 m2',
    mem_inj f m1 m2 ->
    (forall b' delta ofs',
       f b' = Some(b, delta) ->
       perm m1 b' ofs' Cur Readable -> 
       ofs <= ofs' + delta < ofs + Z_of_nat (length bytes2) -> False) ->
    storebytes m2 b ofs bytes2 = Some m2' ->
    mem_inj f m1 m2'.
Proof.
  intros. inversion H. constructor.
  - (* perm *)
    intros. eapply perm_storebytes_1; eauto with mem.
  - intros.
    eapply storebytes_in_bound_m_1; eauto.
  - intros. erewrite <- mask_storebytes; eauto.
  - (* mem_contents *)
    intros. 
    rewrite (storebytes_mem_contents _ _ _ _ _ H1).
    rewrite PMap.gsspec. destruct (peq b2 b). subst b2.
    rewrite setN_outside. auto. 
    destruct (zlt (ofs0 + delta) ofs); auto.
    destruct (zle (ofs + Z_of_nat (length bytes2)) (ofs0 + delta)). omega. 
    byContradiction. eapply H0; eauto. omega. 
    eauto with mem.
  - solve_size_mem. 
Qed.

Lemma storebytes_empty_inj:
  forall f m1 b1 ofs1 m1' m2 b2 ofs2 m2',
    mem_inj f m1 m2 ->
    storebytes m1 b1 ofs1 nil = Some m1' ->
    storebytes m2 b2 ofs2 nil = Some m2' ->
    mem_inj f m1' m2'.
Proof.
  intros. destruct H. constructor. 
  - (* perm *)
    intros.
    eapply perm_storebytes_1; eauto. 
    eapply mi_perm0; eauto.
    eapply perm_storebytes_2; eauto.
  - intros.
    eapply storebytes_in_bound_m_2 in H2; eauto.
    eapply storebytes_in_bound_m_1; eauto.
  - intros.
    erewrite <- mask_storebytes with (m2:=m2'); eauto.
    erewrite <- mask_storebytes with (m2:=m1'); eauto.
  - (* mem_contents *)
    intros.
    assert (perm m1 b0 ofs Cur Readable). eapply perm_storebytes_2; eauto. 
    rewrite (storebytes_mem_contents _ _ _ _ _ H0).
    rewrite (storebytes_mem_contents _ _ _ _ _ H1).
    simpl. rewrite ! PMap.gsspec. 
    destruct (peq b0 b1); destruct (peq b3 b2); subst; eapply mi_memval0; eauto.
  - solve_size_mem.
Qed.

(** Preservation of allocations *)



Lemma alloc_left_unmapped_inj:
  forall f m1 m2 lo hi m1' b1 bt,
  mem_inj f m1 m2 ->
  alloc m1 lo hi bt = Some (m1', b1) ->
  f b1 = None ->
  forall (VB: forall b, ~ valid_block m1 b -> f b = None),
  mem_inj f m1' m2.
Proof.
  intros. inversion H. constructor.
- (* perm *)
  intros. exploit perm_alloc_inv; eauto. intros. 
  destruct (eq_block b0 b1). congruence. eauto. 
- intros.
  unfold in_bound_m in H3. erewrite <- bounds_of_block_alloc_other in H3; eauto.
  congruence.
- intros. 
  erewrite <- mask_alloc_other with (m2:=m1'); eauto.
  congruence. 
- (* mem_contents *)
  generalize H0; intro ALLOC.
  unfold alloc, low_alloc in ALLOC.
  destr_in ALLOC.  injection ALLOC; intros NEXT MEM. intros. 
  rewrite <- MEM; simpl. rewrite NEXT.
  exploit perm_alloc_inv; eauto. intros.
  rewrite PMap.gsspec. unfold eq_block in H4. destruct (peq b0 b1). subst.
  congruence.   
  eauto.
-
  solve_size_mem. intuition lia.
Qed.

Lemma drop_unmapped_inj:
  forall f m1 m2 b lo hi p m1',
  mem_inj f m1 m2 ->
  drop_perm m1 b lo hi p = Some m1' ->
  f b = None ->
  mem_inj f m1' m2.
Proof.
  intros. inv H. constructor. 
- (* perm *)
  intros. eapply mi_perm0; eauto. eapply perm_drop_4; eauto. 
- intros. eapply mi_bounds0; eauto. unfold in_bound_m. erewrite drop_perm_bounds; eauto.
- intros. erewrite <- mask_drop_perm with (m':=m1'); eauto.
- (* contents *)
  intros.
  replace (ZMap.get ofs m1'.(mem_contents)#b1) with (ZMap.get ofs m1.(mem_contents)#b1).
  apply mi_memval0; auto. eapply perm_drop_4; eauto. 
  unfold drop_perm in H0; destruct (range_perm_dec m1 b lo hi Cur Freeable); inv H0; auto.
- solve_size_mem. 
Qed.

Lemma drop_mapped_inj:
  forall f m1 m2 b1 b2 delta lo hi p m1',
    mem_inj f m1 m2 ->
    drop_perm m1 b1 lo hi p = Some m1' ->
    meminj_no_overlap f m1 ->
    f b1 = Some(b2, delta) ->
    exists m2',
      drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2'
      /\ mem_inj f m1' m2'.
Proof.
  intros. 
  assert ({ m2' | drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2' }).
  apply range_perm_drop_2. red; intros. 
  replace ofs with ((ofs - delta) + delta) by omega.
  eapply perm_inj; eauto. eapply range_perm_drop_1; eauto. omega. 
  destruct X as [m2' DROP]. exists m2'; split; auto.
  inv H.
  constructor.
  - (* perm *)
    intros. 
    assert (perm m2 b3 (ofs + delta0) k p0).
    eapply mi_perm0; eauto. eapply perm_drop_4; eauto. 
    destruct (eq_block b1 b0).
    + (* b1 = b0 *)
      subst b0. rewrite H2 in H; inv H.
      destruct (zlt (ofs + delta0) (lo + delta0)). eapply perm_drop_3; eauto.
      destruct (zle (hi + delta0) (ofs + delta0)). eapply perm_drop_3; eauto.
      assert (perm_order p p0).
      eapply perm_drop_2.  eexact H0. instantiate (1 := ofs). omega. eauto. 
      apply perm_implies with p; auto. 
      eapply perm_drop_1. eauto. omega.
    + (* b1 <> b0 *)
      eapply perm_drop_3; eauto.
      destruct (eq_block b3 b2); auto.
      destruct (zlt (ofs + delta0) (lo + delta)); auto.
      destruct (zle (hi + delta) (ofs + delta0)); auto.
      exploit H1; eauto.
      instantiate (1 := ofs + delta0 - delta). 
      apply perm_cur_max. apply perm_implies with Freeable.
      eapply range_perm_drop_1; eauto. omega. auto with mem. 
      eapply perm_drop_4; eauto. eapply perm_max. apply perm_implies with p0. eauto.  
      eauto with mem.
      intuition.
  - intros.
    unfold in_bound_m in *. erewrite <- drop_perm_bounds in H3; eauto.
    erewrite <- drop_perm_bounds; eauto.
  - intros. erewrite <- mask_drop_perm with (m':=m1'); eauto.
    erewrite <- mask_drop_perm with (m':=m2'); eauto.
  - (* memval *)
    intros.
    replace (m1'.(mem_contents)#b0) with (m1.(mem_contents)#b0).
    replace (m2'.(mem_contents)#b3) with (m2.(mem_contents)#b3).
    apply mi_memval0; auto. eapply perm_drop_4; eauto. 
    unfold drop_perm in DROP; destruct (range_perm_dec m2 b2 (lo + delta) (hi + delta) Cur Freeable); inv DROP; auto.
    unfold drop_perm in H0; destruct (range_perm_dec m1 b1 lo hi Cur Freeable); inv H0; auto.
- solve_size_mem. 
Qed.

Lemma drop_outside_inj: 
  forall f m1 m2 b lo hi p m2',
    mem_inj f m1 m2 -> 
    drop_perm m2 b lo hi p = Some m2' -> 
    (forall b' delta ofs' k p,
       f b' = Some(b, delta) ->
       perm m1 b' ofs' k p -> 
       lo <= ofs' + delta < hi -> False) ->
    mem_inj f m1 m2'.
Proof.
  intros. inv H. constructor.
  -  (* perm *)
  intros. eapply perm_drop_3; eauto. 
  destruct (eq_block b2 b); auto. subst b2. right. 
  destruct (zlt (ofs + delta) lo); auto.
  destruct (zle hi (ofs + delta)); auto.
  byContradiction. exploit H1; eauto. omega.
  - intros.
    unfold in_bound_m in *. erewrite <- drop_perm_bounds; eauto.
  - intros; erewrite <- mask_drop_perm with (m':=m2'); eauto.
  - (* contents *)
  intros. 
  replace (m2'.(mem_contents)#b2) with (m2.(mem_contents)#b2).
  apply mi_memval0; auto.
  unfold drop_perm in H0; destruct (range_perm_dec m2 b lo hi Cur Freeable); inv H0; auto.
- solve_size_mem. 
Qed.

Lemma drop_left_inj:
  forall f m1 m2 b lo hi p m1',
    mem_inj f m1 m2 -> 
    drop_perm m1 b lo hi p = Some m1' -> 
    mem_inj f m1' m2.
Proof.
  intros f m1 m2 b lo hi p m1' INJ DP.
  inv INJ; constructor; auto.
  - intros.
    eapply mi_perm0; eauto.
    eapply perm_drop_4; eauto.
  - intros.
    eapply mi_bounds0; eauto.
    unfold in_bound_m in *.
    erewrite drop_perm_bounds; eauto.
  - intros.
    eapply mi_align'0 in H; eauto.
    erewrite (drop_perm_mask _ _ _ _ _ _ DP); eauto.
  - intros.
    erewrite <- (drop_perm_contents _ _ _ _ _ _ DP); eauto.
    apply mi_memval0; eauto.
    eapply perm_drop_4; eauto.
- solve_size_mem. 
Qed.

End MEMINJ.

(** * Memory injections *)

(** A memory state [m1] injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address;
- unallocated blocks in [m1] must be mapped to [None] by [f];
- if [f b = Some(b', delta)], [b'] must be valid in [m2];
- distinct blocks in [m1] are mapped to non-overlapping sub-blocks in [m2];
- the sizes of [m2]'s blocks are representable with unsigned machine integers;
- pointers that could be represented using unsigned machine integers remain
  representable after the injection.
*)

Opaque Z.add. Opaque Pos.of_nat.


Lemma size_sup_one_block:
  forall m bs b z0
         (BS: bs # b = Some (0, z0))
         (PLE:  ((Pos.to_nat b) <= m)%nat)
         (* (PLT: Plt 1 b) *),
    z0 <=
    size_mem_aux MA
      (mk_block_list_aux (get_size bs) m).
Proof.
  induction m; simpl; intros.
  xomega. 
  rewrite mbla_rew. simpl.
  apply le_lt_or_eq in PLE.
  destruct PLE.
  + unfold size_mem_aux. simpl.
    specialize (IHm _ _ _ BS).
    trim IHm. omega.
    unfold size_mem_aux in IHm.
    etransitivity; eauto.
    refine (proj2 (size_mem_al_add _ _ _ _ _  _)). auto. 
    split. generalize (two_power_nat_pos MA); lia.
    refine (Z.le_trans _ _ _ _ (align_le _ (two_power_nat MA) _)); auto.
    rewrite align_refl; auto.
    apply Zle_add.
    apply Zmax_bound_l. omega. 
  + rewrite <- H. rewrite Pos2Nat.id. 
    unfold get_size. rewrite BS.
    rewrite Z.sub_0_r.
    unfold size_mem_aux. simpl. 
    refine (Z.le_trans _ _ _ _ (size_mem_al_pos _ _ _ _ _)); auto.
    rewrite <- align_distr; auto.
    generalize (Zmax_bound_r z0 0 z0). 
    generalize (align_le (Z.max 0 z0) (two_power_nat MA)). intros.
    etransitivity. eapply H1. lia. etransitivity. eapply H0; auto.
    rewrite align_refl. generalize (two_power_nat_pos MA); lia. auto.
    rewrite <- align_distr; auto.
    generalize (Zmax_bound_l 0 0 z0). 
    generalize (align_le (Z.max 0 z0) (two_power_nat MA)). intros.
    etransitivity. eapply H1. lia. etransitivity. eapply H0; auto.
    rewrite align_refl. generalize (two_power_nat_pos MA); lia. auto.
Qed.

Lemma nb_boxes_used_le_one:
  forall b z0 l, In (b, z0) l ->
            (box_span z0 <= nb_boxes_used l)%nat.
Proof.
  induction l; simpl; intros. easy.
  des H. unfold nb_boxes_used. simpl. rewrite fold_left_plus_rew. lia.
  etransitivity. apply IHl; auto. des a. rewrite nb_boxes_used_cons. lia.
Qed.

Lemma in_bound_rep_aux:
  forall m b o,
    in_bound_m o m b ->
    0 <= o < __szmem. 
Proof.
  intros m b o IB. 
  unfold in_bound_m, in_bound, bounds_of_block in IB.
  repeat destr_in IB; try lia.
  generalize (bounds_lo_inf0 _ _ _ _ Heqo0). simpl in IB. intro. des H. 
  split. lia.
  eapply Z.lt_le_trans. apply IB. clear IB.
  generalize (wfm_alloc_ok m). intro NB.
  unfold nb_boxes_max in NB. 
  unfold __szmem. rewrite s31_ma.

  eapply Z.mul_lt_mono_pos_l in NB. 2: apply Z.gt_lt, tpMA_pos.
  etransitivity.
  2: etransitivity.
  2: apply Z.lt_le_incl. 2: apply NB.
  Focus 2.
  transitivity (   two_power_nat MA * (two_power_nat (32 - MA) - 1) - two_power_nat MA ). lia.
  apply Z.sub_le_mono_l. generalize (tpMA_sup8). lia.

  transitivity (two_power_nat MA * Z.of_nat (box_span z0)).
  rewrite box_span_align. apply align_le. apply tpMA_pos. auto.
  apply Z.mul_le_mono_pos_l. apply Z.gt_lt, tpMA_pos.
  apply inj_le.
  generalize (mbla_below_in' (size_block m) (pred (Pos.to_nat (nextblock m))) b). intros.
  assert (size_block m b = z0).
  {
    unfold size_block, get_size. rewrite Heqo0. lia.
  }
  etransitivity. eapply nb_boxes_used_le_one.
  subst. apply H.
  destruct (plt b (nextblock m)).  zify; xomega.
  eapply bs_valid in n; eauto. congruence.
  etransitivity. 2: apply NPeano.Nat.add_le_mono. rewrite plus_0_r. apply le_refl. apply le_refl. lia.
Qed.

Lemma in_bound_rep:
  forall m b o,
    in_bound_m o m b ->
    0 <= o < Int.max_unsigned.
Proof.
  intros m b o IB.
  apply in_bound_rep_aux in IB.
  simpl in IB; unfold __szmem, comp_size in IB;  NormaliseSpec.unfsize.
  generalize (two_power_nat_pos MA); lia.
Qed.

(** This is now provable and not needed as an invariant.  *)
Lemma mi_representable':
  forall sm m f m1 m2
         (MI: mem_inj sm m f m1 m2),
  forall b b' delta ofs
         (FB: f b = Some(b', delta))
         (PERM: in_bound_m (Int.unsigned ofs) m1 b \/ 
                in_bound_m (Int.unsigned ofs - 1) m1 b)
         (delta_pos: delta >= 0),
    0 <= Int.unsigned ofs + delta <= Int.max_unsigned.
Proof.
  intros.
  assert (PERM': in_bound_m (Int.unsigned ofs + delta) m2 b' \/ 
                 in_bound_m (Int.unsigned ofs - 1 + delta) m2 b').
  inv MI.
  destruct PERM as [PERM|PERM]; [left|right];
  eapply (mi_bounds0 _ _ _ _ FB) in PERM; eauto.
  destruct PERM' as [PERM'|PERM'];
  eapply in_bound_rep in PERM'; eauto; omega.
Qed.

Lemma mi_representable:
  forall sm m f m1 m2
         (MI: mem_inj sm m f m1 m2),
  forall b b' delta ofs
         (FB: f b = Some(b', delta))
         (PERM: perm m1 b (Int.unsigned ofs) Max Nonempty \/ 
                perm m1 b (Int.unsigned ofs - 1) Max Nonempty)
         (delta_pos: delta >= 0),
    0 <= Int.unsigned ofs + delta <= Int.max_unsigned.
Proof.
  intros.
  eapply mi_representable'; eauto.
  destruct PERM as [PERM|PERM]; [left|right];
  apply perm_bounds in PERM; auto.
Qed.


Lemma meminj_no_overlap_impl:
  forall f m,
    Mem.meminj_no_overlap' f m ->
    Mem.meminj_no_overlap f m.
Proof.
  intros f m MNO. 
  red in MNO; red.
  intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 diff FB1 FB2 P1 P2.
  apply Mem.perm_bounds in P1.
  apply Mem.perm_bounds in P2.
  specialize (MNO b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 diff FB1 FB2 P1 P2).
  auto.
Qed.

Definition is_dynamic_block m b :=
  (mem_blocktype m) # b = Some Dynamic.

Lemma is_block_dynamic_alloc:
  forall m lo hi m' b
    (AB: Mem.alloc m lo hi Normal = Some (m',b))
    b',
    Mem.is_dynamic_block m b' <-> Mem.is_dynamic_block m' b'.
Proof.
  Transparent Mem.alloc. intros.
  unfold Mem.alloc, Mem.low_alloc in AB; destr_in AB; inv AB.
  unfold Mem.is_dynamic_block. simpl. rewrite PMap.gsspec. destr. subst.
  rewrite Mem.blocktype_valid. destr. xomega.    
Qed.

Lemma is_block_dynamic_alloc':
  forall m lo hi m' b bt
    (AB: Mem.alloc m lo hi bt = Some (m',b))
    b' (diff: b <> b'),
    Mem.is_dynamic_block m b' <-> Mem.is_dynamic_block m' b'.
Proof.
  Transparent Mem.alloc. intros.
  unfold Mem.alloc, Mem.low_alloc in AB; destr_in AB; inv AB.
  unfold Mem.is_dynamic_block. simpl. rewrite PMap.gsspec. destr.     
Qed.

Lemma is_block_dynamic_storebytes:
  forall m b o l m'
    (AB: Mem.storebytes m b o l = Some m')
    b',
    Mem.is_dynamic_block m b' <-> Mem.is_dynamic_block m' b'.
Proof.
  unfold Mem.storebytes. intros.
  destr_in AB. inv AB. destr.
Qed.



Lemma is_block_dynamic_drop_perm:
  forall m b lo hi p m'
    (AB: Mem.drop_perm m b lo hi p = Some m')
    b',
    Mem.is_dynamic_block m b' <-> Mem.is_dynamic_block m' b'.
Proof.
  unfold Mem.drop_perm. intros.
  destr_in AB. inv AB. destr.
Qed.



Lemma is_block_dynamic_unchfree:
  forall m b lo hi b',
    Mem.is_dynamic_block (Mem.unchecked_free m b lo hi) b' <-> Mem.is_dynamic_block m b'.
Proof.
  unfold Mem.unchecked_free, Mem.is_dynamic_block; simpl; tauto.
Qed.



Lemma is_block_dynamic_free:
  forall m b lo hi b' m' (FREE: Mem.free m b lo hi = Some m'),
    Mem.is_dynamic_block m' b' <-> Mem.is_dynamic_block m b'.
Proof.
  unfold Mem.free; intros; repeat destr_in FREE; inv FREE; apply is_block_dynamic_unchfree.
Qed.


Lemma is_block_dynamic_freelist:
  forall l m b' m' (FL: Mem.free_list m l = Some m'),
    Mem.is_dynamic_block m' b' <-> Mem.is_dynamic_block m b'.
Proof.
  induction l; simpl; intros; eauto. inv FL. tauto.
  repeat destr_in FL. rewrite <- (is_block_dynamic_free _ _ _ _ _ _ Heqo). auto.  
Qed.

Lemma size_block_snd:
  forall m2 b0,
    snd (Mem.bounds_of_block m2 b0) = Mem.size_block m2 b0.
Proof.
  unfold Mem.bounds_of_block, Mem.size_block, Alloc.get_size.
  intros; repeat destr.
  eapply Mem.bounds_lo_inf0 in Heqo. destruct Heqo; subst; lia.
Qed.


Lemma size_block_unchecked_free:
  forall m b lo hi b',
    Mem.size_block (Mem.unchecked_free m b lo hi) b' =
    if eq_block b b'
    then let (lo',hi') := Mem.bounds_of_block m b in
         if zeq lo' lo && zeq hi' hi
         then 0
         else hi'
    else Mem.size_block m b'.
Proof.
  intros.
  rewrite <- ! size_block_snd, (Mem.unchecked_free_bounds'); repeat destr;
  try rewrite ! size_block_snd; eauto.
Qed.



Ltac rewbnd :=
  try rewrite <- ! size_block_snd;
  repeat
    match goal with
      H: Mem.storebytes ?m ?b ?o ?l = Some ?m' |-
      context [Mem.bounds_of_block ?m' ?b']  =>
      rewrite <- (Mem.bounds_of_block_storebytes _ _ _ _ _ H b')
    | H: Mem.drop_perm ?m ?b ?lo ?hi ?p = Some ?m' |-
      context [Mem.bounds_of_block ?m' ?b']  =>
      rewrite <- (Mem.drop_perm_bounds _ _ _ _ _ _ H b')
    | H: Mem.alloc ?m ?lo ?hi ?bt = Some (?m',?b) |-
      context [Mem.bounds_of_block ?m' ?b]  =>
      rewrite (Mem.bounds_of_block_alloc _ _ _ _ _ _ H)
    | H: Mem.alloc ?m ?lo ?hi ?bt = Some (?m',?b),
         H1: ?b <> ?b' |-
      context [Mem.bounds_of_block ?m' ?b']  =>
      rewrite <- (Mem.bounds_of_block_alloc_other _ _ _ _ _ _ H _ H1)
    | H: Mem.alloc ?m ?lo ?hi ?bt = Some (?m',?b),
         H1: ?b' <> ?b |-
      context [Mem.bounds_of_block ?m' ?b']  =>
      rewrite <- (Mem.bounds_of_block_alloc_other _ _ _ _ _ _ H _ (not_eq_sym H1))
    end;
  try rewrite ! size_block_snd.

Ltac rewmsk :=
  repeat
    match goal with
      H: Mem.storebytes ?m ?b ?o ?l = Some ?m' |-
      context [Mem.mask ?m' ?b']  =>
      rewrite <- (Mem.mask_storebytes _ _ _ _ _ H b')
    | H: Mem.drop_perm ?m ?b ?lo ?hi ?p = Some ?m' |-
      context [Mem.mask ?m' ?b']  =>
      rewrite <- (Mem.mask_drop_perm _ _ _ _ _ _ H b')
    | H: Mem.alloc ?m ?lo ?hi ?bt = Some (?m',?b) |-
      context [Mem.mask ?m' ?b]  =>
      rewrite (Mem.alloc_mask _ _ _ _ _ _ H)
    | H: Mem.alloc ?m ?lo ?hi ?bt = Some (?m',?b),
         H1: ?b <> ?b' |-
      context [Mem.mask ?m' ?b']  =>
      rewrite <- (Mem.mask_alloc_other _ _ _ _ _ _ H _ H1)
    | H: Mem.alloc ?m ?lo ?hi ?bt = Some (?m',?b),
         H1: ?b' <> ?b |-
      context [Mem.mask ?m' ?b']  =>
      rewrite <- (Mem.mask_alloc_other _ _ _ _ _ _ H _ (not_eq_sym H1))
    end.

Ltac rewvb :=
  repeat
    match goal with
      H: Mem.storebytes ?m ?b ?o ?l = Some ?m' |-
      Mem.valid_block ?m' ?b' =>
      apply (Mem.storebytes_valid_block_1 _ _ _ _ _ H b')
    | H: Mem.drop_perm ?m ?b ?lo ?hi ?p = Some ?m' |-
      Mem.valid_block ?m' ?b' =>
      apply (Mem.drop_perm_valid_block_1 _ _ _ _ _ _ H)
    | H: Mem.alloc ?m ?lo ?hi _ = Some (?m',?b) |-
      Mem.valid_block ?m' ?b =>
      apply (Mem.valid_new_block _ _ _ _ _ _ H)
    | H: Mem.alloc ?m ?lo ?hi _ = Some (?m',?b),
         H1: ?b <> ?b' |-
      Mem.valid_block ?m' ?b' =>
      apply (Mem.valid_block_alloc _ _ _ _ _ _ H)
    | H: Mem.alloc ?m ?lo ?hi _ = Some (?m',?b),
         H1: ?b' <> ?b |-
      Mem.valid_block ?m' ?b' =>
      apply (Mem.valid_block_alloc _ _ _ _ _ _ H)
    | H: Mem.alloc ?m ?lo ?hi _ = Some (?m',?b)
      |-
      Mem.valid_block ?m' ?b' =>
      let i := fresh in
      set (i := b' <> b); exfalso
    end.




Lemma Forall_impl':
  forall {A : Type} (P Q : A -> Prop),
  forall l : list A,
    (forall a : A, In a l -> P a -> Q a) ->
    Forall P l -> Forall Q l.
Proof.
  induction l; simpl; intros; eauto.
  inv H0; constructor; auto.
Qed.
Lemma size_block_free_list:
  forall l m b
    (F: Forall (fun x =>
                  let '(b,lo,hi) := x in
                  Mem.bounds_of_block m b = (lo,hi)) l)
    (lnr: list_norepet (map fst (map fst l)))
    m',
    Mem.free_list m l = Some m' ->
    Mem.size_block m' b =
    if in_dec peq b (map fst (map fst l))
    then 0
    else Mem.size_block m b.
Proof.
  induction l; simpl; intros; eauto.
  inv H; auto.
  repeat destr_in H.
  specialize (IHl m0 b).
  trim IHl.
  {
    clear IHl.
    inv F.
    revert H3; apply Forall_impl'.
    intros; des a. des p. rewrite <- H1.
    eapply Mem.bounds_free. eauto.
    inv lnr.
    rewrite map_map, in_map_iff in H5. intro; subst.
    elim H5; exists (b1,z2,z1); split; auto. 
  }
  trim IHl.
  {
    inv lnr; auto.
  }
  specialize (IHl _ H).
  rewrite IHl.
  destr. destr. destr.
  destr.
  inv lnr. des o.
  unfold Mem.free in Heqo; repeat destr_in Heqo; inv Heqo.
  rewrite size_block_unchecked_free. rewrite pred_dec_true; auto. inv F.
  rewrite H4.
  des (zeq z0 z0) ; des (zeq z z).
  unfold Mem.free in Heqo; repeat destr_in Heqo; inv Heqo.
  rewrite size_block_unchecked_free. rewrite pred_dec_false; auto.
Qed.


Lemma bounds_of_block_free_list:
  forall l m b
    (F: Forall (fun x =>
                  let '(b,lo,hi) := x in
                  Mem.bounds_of_block m b = (lo,hi)) l)
    (lnr: list_norepet (map fst (map fst l)))
    m',
    Mem.free_list m l = Some m' ->
    Mem.bounds_of_block m' b =
    if in_dec peq b (map fst (map fst l))
    then (0,0)
    else Mem.bounds_of_block m b.
Proof.
  induction l; simpl; intros; eauto.
  inv H; auto.
  repeat destr_in H.
  specialize (IHl m0 b).
  trim IHl.
  {
    clear IHl.
    inv F.
    revert H3; apply Forall_impl'.
    intros; des a. des p. rewrite <- H1.
    eapply Mem.bounds_free. eauto.
    inv lnr.
    rewrite map_map, in_map_iff in H5. intro; subst.
    elim H5; exists (b1,z2,z1); split; auto. 
  }
  trim IHl.
  {
    inv lnr; auto.
  }
  specialize (IHl _ H).
  rewrite IHl.
  destr. destr. destr.
  destr.
  inv lnr. des o.
  unfold Mem.free in Heqo; repeat destr_in Heqo; inv Heqo.
  rewrite Mem.unchecked_free_bounds'. rewrite pred_dec_true; auto. inv F.
  rewrite H4.
  des (zeq z0 z0) ; des (zeq z z).
  unfold Mem.free in Heqo; repeat destr_in Heqo; inv Heqo.
  rewrite Mem.unchecked_free_bounds'. rewrite pred_dec_false; auto. 
Qed.




Lemma freelist_in_bound_m:
  forall  l m m'
    (FL: Mem.free_list m l = Some m')
    o b
    (IB: Mem.in_bound_m o m' b),
    Mem.in_bound_m o m b.
Proof.
  induction l; simpl; intros; eauto.
  - inv FL; auto.
  - des a; des p.
    destr_in FL.
    specialize (IHl _ _ FL _ _ IB).
    unfold Mem.in_bound_m in *.
    destruct (Mem.free_bounds' _ _ _ _ _ b Heqo0).
    rewrite <- H; auto.
    rewrite H in IHl. red in IHl; destr; lia.
Qed.

Lemma freelist_perm:
  forall l m m'
    (FL: Mem.free_list m l = Some m')
    b o k p
    (NIN: ~ In b (map fst (map fst l)))
    (P: Mem.perm m b o k p),
    Mem.perm m' b o k p.
Proof.
  induction l; simpl; intros; eauto.
  inv FL; auto.
  repeat destr_in FL.
  eapply IHl in FL; eauto.
  eapply Mem.perm_free_1; eauto.
Qed.

Lemma free_list_not_in_bound:
  forall l m m' (FL: Mem.free_list m l = Some m')
    o b (NIB: ~ Mem.in_bound_m o m b),
    ~ Mem.in_bound_m o m' b.
Proof.
  intros; intro IB.
  exploit freelist_in_bound_m; eauto.
Qed.

Lemma freelist_in_bound_m':
  forall  l m m'
     (FL: Mem.free_list m l = Some m')
     (LNR: list_norepet (map fst (map fst l)))
     (* (F: Forall (fun x => Mem.bounds_of_block m (fst (fst x)) = (snd (fst x), snd x)) l) *)
    o b
    (IB: Mem.in_bound_m o m' b),
    (forall lo hi, In b (map fst (map fst l)) ->
              lo <= o < hi ->
              False).
Proof.
  induction l; simpl; intros; eauto.
  repeat destr_in FL. des H.
  revert IB.
  eapply free_list_not_in_bound; eauto.
  unfold Mem.in_bound_m.
  erewrite  Mem.free_bounds_exact; eauto.
  rewrite peq_true. unfold in_bound; simpl; lia.
  exploit IHl; eauto.
  inv LNR; auto.
Qed.

Lemma uf_load:
  forall chunk m b o b' lo hi ,
    b <> b' ->
    Mem.load chunk (Mem.unchecked_free m b' lo hi) b o =
    Mem.load chunk m b o.
Proof.
  Transparent Mem.load.
  unfold Mem.load, Mem.unchecked_free.
  simpl. intros.
  repeat destr. 
  - exfalso; apply n. clear n.
    unfold Mem.valid_access in *. 
    unfold Mem.range_perm, Mem.perm in *. simpl in *.
    des v. split.
    intros. apply p in H0. rewrite PMap.gsspec in H0. destr_in H0. auto.
  - exfalso; apply n. clear n.
    unfold Mem.valid_access in *. 
    unfold Mem.range_perm, Mem.perm in *. simpl in *.
    des v. split.
    intros. apply p in H0. rewrite PMap.gsspec. destr. auto.
Qed.

Lemma free_size:
  forall m b lo hi m'
    (FREE: Mem.free m b lo hi = Some m'),
  forall b',
    Mem.size_block m' b' <= Mem.size_block m b'.
Proof.
  clear. intros.
  generalize (Mem.free_bounds' _ _ _ _ _ b' FREE).
  destr.
  intros [A|A]; inv A; try lia.    
  rewrite <- ! size_block_snd, H0. lia.
  rewrite <- size_block_snd, H0. simpl; apply size_block_pos.
Qed.

Lemma lnr_remove:
  forall {A: Type} (eq: forall (a b: A), {a = b} + {a <> b}) (a: A) (l: list A),
    list_norepet l ->
    list_norepet (remove eq a l).
Proof.
  induction 1; simpl; intros; eauto.
  constructor.
  destr; constructor; auto.
  intro IN. apply Mem.remove_in_before in IN; destr.
Qed.

Lemma has_bounds_bounds:
  forall m b lo hi,
    Mem.has_bounds m b lo hi = true ->
    Mem.bounds_of_block m b = (lo,hi).
Proof.
  unfold Mem.has_bounds; simpl; intros.
  repeat destr_in H.
  des (zeq lo z); des (zeq hi z0).
Qed.

Lemma free_bounds_exact':
  forall m b lo hi m',
    Mem.free m b lo hi = Some m' ->
    Mem.bounds_of_block m b = (lo,hi).
Proof.
  intros m b lo hi m' FREE.
  unfold Mem.free in FREE; repeat destr_in FREE; inv FREE.
  eapply has_bounds_bounds; eauto.
Qed.


Section INJECT.

  Variable sm : bool.
  Variable ei: meminj -> expr_sym -> expr_sym -> Prop.
  Hypothesis wf: wf_inj ei.



  Record inject' (f: meminj) (m1 m2: mem) : Prop :=
    mk_inject {
        mi_inj:
          mem_inj sm ei f m1 m2;
        mi_freeblocks:
          forall b, ~(valid_block m1 b) -> f b = None;
        mi_mappedblocks:
          forall b b' delta, f b = Some(b', delta) -> valid_block m2 b';
        mi_no_overlap':
          meminj_no_overlap' f m1;
        mi_delta_pos:               (**r the [mi_representable] is derivable from [mi_delta_pos] and [mi_inj]  *)
          forall b b' delta,
            f b = Some(b', delta) ->
            delta >= 0;
        mi_inj_dynamic:
          forall b b' delta,
            f b = Some (b',delta) ->
            (is_dynamic_block m1 b <-> is_dynamic_block m2 b') /\
            (is_dynamic_block m1 b -> delta = 0 /\ bounds_of_block m1 b = bounds_of_block m2 b') /\
            (is_dynamic_block m2 b' -> forall b'' delta', f b'' = Some (b', delta') -> b'' = b)
      }.

Definition inject := inject'.

Local Hint Resolve mi_mappedblocks: mem.

Lemma inject_meminj_no_overlap:
  forall f m1 m2,
    inject f m1 m2 ->
    meminj_no_overlap f m1.
Proof.
  intros f m1 m2 INJ.
  apply meminj_no_overlap_impl.
  inv INJ; auto.
Qed.

(** Preservation of access validity and pointer validity *)

Theorem valid_block_inject_1:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m1 b1.
Proof.
  intros. inv H. destruct (plt b1 (nextblock m1)). auto. 
  assert (f b1 = None). eapply mi_freeblocks; eauto. congruence.
Qed.

Theorem valid_block_inject_2:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m2 b2.
Proof.
  intros. eapply mi_mappedblocks; eauto. 
Qed.

Local Hint Resolve valid_block_inject_1 valid_block_inject_2: mem.

Theorem perm_inject:
  forall f m1 m2 b1 b2 delta ofs k p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  perm m1 b1 ofs k p -> perm m2 b2 (ofs + delta) k p.
Proof.
  intros. inv H0. eapply perm_inj; eauto. 
Qed.

Theorem range_perm_inject:
  forall f m1 m2 b1 b2 delta lo hi k p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  range_perm m1 b1 lo hi k p -> range_perm m2 b2 (lo + delta) (hi + delta) k p.
Proof.
  intros. inv H0. eapply range_perm_inj; eauto.
Qed.

Theorem valid_access_inject:
  forall f m1 m2 chunk b1 ofs b2 delta p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_access m1 chunk b1 ofs p ->
  valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. eapply valid_access_inj; eauto. apply mi_inj; auto. 
Qed.

Theorem valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros. 
  rewrite valid_pointer_valid_access in H1.
  rewrite valid_pointer_valid_access.
  eapply valid_access_inject; eauto.
Qed.

Theorem weak_valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  weak_valid_pointer m1 b1 ofs = true ->
  weak_valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros until 2. unfold weak_valid_pointer. rewrite !orb_true_iff.
  replace (ofs + delta - 1) with ((ofs - 1) + delta) by omega.
  intros []; eauto using valid_pointer_inject.
Qed.

(** The following lemmas establish the absence of machine integer overflow
  during address computations. *)

Lemma address_inject:
  forall f m1 m2 b1 ofs1 b2 delta p,
  inject f m1 m2 ->
  perm m1 b1 (Int.unsigned ofs1) Cur p ->
  f b1 = Some (b2, delta) ->
  Int.unsigned (Int.add ofs1 (Int.repr delta)) = Int.unsigned ofs1 + delta.
Proof.
  intros.
  assert (perm m1 b1 (Int.unsigned ofs1) Max Nonempty) by eauto with mem.
  exploit mi_representable; eauto. inv H; eauto. inv H; eauto. intros [A B].
  inv H.
  specialize (mi_delta_pos0 _ _ _ H1).
  assert (0 <= delta <= Int.max_unsigned).
    generalize (Int.unsigned_range ofs1). intros. omega.
  unfold Int.add. repeat rewrite Int.unsigned_repr; omega.
Qed.

Lemma address_inject':
  forall f m1 m2 chunk b1 ofs1 b2 delta,
  inject f m1 m2 ->
  valid_access m1 chunk b1 (Int.unsigned ofs1) Nonempty ->
  f b1 = Some (b2, delta) ->
  Int.unsigned (Int.add ofs1 (Int.repr delta)) = Int.unsigned ofs1 + delta.
Proof.
  intros. destruct H0. eapply address_inject; eauto. 
  apply H0. generalize (size_chunk_pos chunk). omega. 
Qed.

Theorem weak_valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' delta,
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Int.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Int.unsigned ofs + Int.unsigned (Int.repr delta) <= Int.max_unsigned.
Proof.
  intros. rewrite weak_valid_pointer_spec in H0. 
  rewrite ! valid_pointer_nonempty_perm in H0.
  inv H. generalize (mi_delta_pos0 _ _ _ H1). intros.
  generalize (mi_representable _ _ _ _ _ mi_inj0 _ _ _ ofs H1); eauto. 
  intro C.
  trim C.
  destruct H0; eauto with mem.
  trim C; auto.
  pose proof (Int.unsigned_range ofs).
  rewrite Int.unsigned_repr; omega.
Qed.

Theorem valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' delta,
  inject f m1 m2 ->
  valid_pointer m1 b (Int.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Int.unsigned ofs + Int.unsigned (Int.repr delta) <= Int.max_unsigned.
Proof.
  eauto using weak_valid_pointer_inject_no_overflow, valid_pointer_implies.
Qed.

Theorem valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  valid_pointer m1 b (Int.unsigned ofs) = true ->
  ei f (Eval (Vptr b ofs)) (Eval (Vptr b' ofs')) ->
  valid_pointer m2 b' (Int.unsigned ofs') = true.
Proof.
  intros. 
  generalize (fun al => ei_ld_expr _ wf f al (fun _ _ => Byte.zero) _ _ H1); simpl.
  unfold Val.inj_alloc.
  des (f b). des p. intros.
  generalize (H2 (fun _ => Int.zero)); simpl.
  rewrite ! Int.add_zero_l. intro.
  apply lessdef_vint in H3. subst.
  replace (Int.unsigned (Int.add (Int.repr z) ofs)) with
  (Int.unsigned ofs + z).
  eapply valid_pointer_inject; eauto.
  rewrite Heqo; repeat f_equal; auto.
  generalize (H2 (fun bb => if peq bb b0 then Int.zero else Int.one)); clear; simpl.
  rewrite peq_true; simpl. intro A; apply lessdef_vint in A; revert A; destr. intro.
  revert A; sint.
  rewrite <- ! (Int.add_commut (Int.add _ _)).
  intro. apply int_add_eq_l in A. discriminate.
  erewrite <- address_inject; eauto. rewrite Int.add_commut; auto.
  rewrite valid_pointer_valid_access in H0. unfold valid_access in H0.
  simpl in H0. unfold range_perm in H0.  destruct H0. 
  specialize (H0 (Int.unsigned ofs)). exploit H0; eauto. omega. intros.
  generalize (H2 (fun bb => Int.one)) (H2 (fun bb => Int.zero)); clear; simpl.
  intros A B; apply lessdef_vint in A; apply lessdef_vint in B.
  rewrite ! Int.add_zero_l in B. subst.
  rewrite <- ! (Int.add_commut ofs') in A.
  apply int_add_eq_l in A; discriminate.
Qed.

Theorem weak_valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Int.unsigned ofs) = true ->
  ei f (Eval (Vptr b ofs)) (Eval (Vptr b' ofs')) ->
  weak_valid_pointer m2 b' (Int.unsigned ofs') = true.
Proof.
  intros.
  generalize (fun al => ei_ld_expr _ wf f al (fun _ _ => Byte.zero) _ _ H1); simpl.
  unfold Val.inj_alloc. des (f b). des p.
  exploit weak_valid_pointer_inject; eauto.
  rewrite weak_valid_pointer_spec in H0. 
  rewrite ! valid_pointer_nonempty_perm in H0.
  inv H. specialize (mi_delta_pos0 _ _ _ Heqo).
  exploit (mi_representable _ _ _ _ _ mi_inj0 _ _ _ ofs Heqo); eauto. destruct H0; eauto with mem. 
  intros.
  pose proof (Int.unsigned_range_2 ofs).
  intros. generalize (H3 (fun _ => Int.zero)); intro A; apply lessdef_vint in A.
  rewrite ! Int.add_zero_l in A. subst.
  unfold Int.add. repeat rewrite Int.unsigned_repr; auto; try omega.

  generalize (H3 (fun bb => if peq bb b0 then Int.zero else Int.one));
    intro A; apply lessdef_vint in A; simpl in A.
  rewrite peq_true in A. rewrite Z.add_comm.
  destruct (peq b' b0); subst; auto.
  exfalso; clear -A.
  revert A; sint. rewrite <- ! (Int.add_commut (Int.add _ _ )).
  intro A. apply int_add_eq_l in A. discriminate.
  intros.
  generalize (H2 (fun bb => Int.one)) (H2 (fun bb => Int.zero)); clear; simpl.
  intros A B; apply lessdef_vint in A; apply lessdef_vint in B.
  rewrite ! Int.add_zero_l in B. subst.
  rewrite <- ! (Int.add_commut ofs') in A.
  apply int_add_eq_l in A; discriminate.  
Qed.

Theorem inject_no_overlap:
  forall f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject f m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Max Nonempty ->
  perm m1 b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.
Proof.
  intros m f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2 INJ.
  eapply inject_meminj_no_overlap in INJ; eauto.
Qed.

Theorem different_pointers_inject:
  forall f m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  inject f m m' ->
  b1 <> b2 ->
  valid_pointer m b1 (Int.unsigned ofs1) = true ->
  valid_pointer m b2 (Int.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Int.unsigned (Int.add ofs1 (Int.repr delta1)) <>
  Int.unsigned (Int.add ofs2 (Int.repr delta2)).
Proof.
  intros. 
  rewrite valid_pointer_valid_access in H1. 
  rewrite valid_pointer_valid_access in H2. 
  rewrite (address_inject' _ _ _ _ _ _ _ _ H H1 H3). 
  rewrite (address_inject' _ _ _ _ _ _ _ _ H H2 H4). 
  inv H1. simpl in H5. inv H2. simpl in H1.
  eapply inject_meminj_no_overlap; eauto.
  apply perm_cur_max. apply (H5 (Int.unsigned ofs1)). omega.
  apply perm_cur_max. apply (H1 (Int.unsigned ofs2)). omega.
Qed.

Require Intv.

Theorem disjoint_or_equal_inject:
  forall f m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
  inject f m m' ->
  f b1 = Some(b1', delta1) ->
  f b2 = Some(b2', delta2) ->
  range_perm m b1 ofs1 (ofs1 + sz) Max Nonempty ->
  range_perm m b2 ofs2 (ofs2 + sz) Max Nonempty ->
  sz > 0 ->
  b1 <> b2 \/ ofs1 = ofs2 \/ ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1 ->
  b1' <> b2' \/ ofs1 + delta1 = ofs2 + delta2
             \/ ofs1 + delta1 + sz <= ofs2 + delta2 
             \/ ofs2 + delta2 + sz <= ofs1 + delta1.
Proof.
  intros. 
  destruct (eq_block b1 b2).
  assert (b1' = b2') by congruence. assert (delta1 = delta2) by congruence. subst.
  destruct H5. congruence. right. destruct H5. left; congruence. right. omega.
  destruct (eq_block b1' b2'); auto. subst. right. right. 
  set (i1 := (ofs1 + delta1, ofs1 + delta1 + sz)).
  set (i2 := (ofs2 + delta2, ofs2 + delta2 + sz)).
  change (snd i1 <= fst i2 \/ snd i2 <= fst i1).
  apply Intv.range_disjoint'; simpl; try omega.
  unfold Intv.disjoint, Intv.In; simpl; intros. red; intros. 
  exploit inject_meminj_no_overlap; eauto. 
  instantiate (1 := x - delta1). apply H2. omega.
  instantiate (1 := x - delta2). apply H3. omega.
  intuition. 
Qed.

Theorem aligned_area_inject:
  forall f m m' b ofs al sz b' delta,
  inject f m m' ->
  al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz > 0 ->
  (al | sz) ->
  range_perm m b ofs (ofs + sz) Cur Nonempty ->
  (al | ofs) ->
  f b = Some(b', delta) ->
  (al | ofs + delta).
Proof.
  intros. 
  assert (P: al > 0) by omega.
  assert (Q: Zabs al <= Zabs sz). apply Zdivide_bounds; auto. omega.
  rewrite Zabs_eq in Q; try omega. rewrite Zabs_eq in Q; try omega.
  assert (R: exists chunk, al = align_chunk chunk /\ al = size_chunk chunk).
    destruct H0. subst; exists Mint8unsigned; auto.
    destruct H0. subst; exists Mint16unsigned; auto.
    destruct H0. subst; exists Mint32; auto.
    subst; exists Mint64; auto.
  destruct R as [chunk [A B]].
  assert (valid_access m chunk b ofs Nonempty).
    split. red; intros; apply H3. omega. congruence.
  exploit valid_access_inject; eauto. intros [C D]. 
  congruence.
Qed.

(** Preservation of loads *)

Theorem load_inject:
  forall f m1 m2 chunk b1 ofs b2 delta v1,
  inject f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ ei f v1 v2.
Proof.
  intros. inv H. eapply load_inj; eauto. 
Qed.

Lemma alloc_0_inject: 
  forall tm1 tm2 sp f1 m2 bt,
    alloc tm1 0 0 bt = Some (tm2, sp) ->
    inject f1 m2 tm1 ->
    inject f1 m2 tm2.
Proof.
  intros.
  inv H0; constructor; eauto.
  - inv mi_inj0; constructor; intros; eauto.
    + eapply perm_alloc_1; eauto.
    + unfold in_bound_m. erewrite bounds_of_block_alloc_eq; eauto.
      generalize (mi_mappedblocks0 _ _ _ H0). intros.
      destruct (eq_block b2 sp). 
      * subst.
        generalize (alloc_result _ _ _ _ _ _ H). intro; subst. 
        unfold valid_block in H2; xomega.
      * destruct (plt b2 (nextblock tm2)).
        eapply mi_bounds0; eauto.
        erewrite nextblock_alloc in n0; eauto.
        unfold valid_block in H2; xomega. 
    + specialize (mi_align'0 _ _ _ H0); intuition try congruence.
      generalize (mi_mappedblocks0 _ _ _ H0). intros.
      destruct (eq_block b0 sp); subst.
      generalize (alloc_result _ _ _ _ _ _ H). intro; subst.
      unfold valid_block in H3; xomega.
      erewrite <- mask_alloc_other with (m2:=tm2); eauto.
    + generalize (mi_mappedblocks0 _ _ _ H0). intros.
      destruct (eq_block b2 sp); subst.
      generalize (alloc_result _ _ _ _ _ _ H). intro; subst. unfold valid_block in H2; xomega.
      erewrite (alloc_contents) with (m':=tm2); eauto.
    + rewrite (nb_boxes_alloc _ _ _ _ _ _ H). 
      rewrite Z.max_r by lia.
      replace (box_span 0) with O. intuition lia. unfold box_span.
      simpl. rewrite minus_1_div_eq. reflexivity. apply tpMA_pos.
  - intros.
    apply mi_mappedblocks0 in H0.
    unfold valid_block in *.
    erewrite nextblock_alloc; eauto. xomega.
  - intros b b' delta FB.
    generalize (mi_inj_dynamic0 _ _ _ FB).
    intros (DYNeq & DYNimpl & DYNimpl').
    repSplit.
    + split; intros IDB; first [rewrite DYNeq in IDB || rewrite <- DYNeq in IDB || rewrite DYNeq];
      unfold is_dynamic_block in IDB |- *.
      unfold alloc, low_alloc in H; destr_in H; inv H; simpl.
      rewrite PMap.gsspec; destr.
      eapply mi_mappedblocks0 in FB; eauto. subst. red in FB; xomega.
      unfold alloc, low_alloc in H; destr_in H; inv H; simpl in *.
      rewrite PMap.gsspec in IDB; destr_in IDB. inv IDB.
      eapply mi_mappedblocks0 in FB; eauto. red in FB; xomega.
    + intro IDB; specialize (DYNimpl IDB). des DYNimpl.
      rewrite e0.
      erewrite bounds_of_block_alloc_other. 2: eauto. auto. intro; subst.
      apply mi_mappedblocks0 in FB; eauto.
      apply fresh_block_alloc in H; eauto.
    + intro IDB.
      assert (b' = sp \/ is_dynamic_block tm1 b').
      {
        unfold is_dynamic_block in IDB;
        unfold alloc, low_alloc in H; destr_in H; inv H; simpl in *.
        rewrite PMap.gsspec in IDB; destr_in IDB. 
      }
      des H0. 
      apply mi_mappedblocks0 in FB; eauto.
      apply fresh_block_alloc in H; eauto. destr.
Qed.

Lemma compat_wider:
  forall m m'
         (bw : forall b o, in_bound_m o m b -> in_bound_m o m' b)
         (ms: forall b, nat_mask m b = nat_mask m' b)
         cm q
         (COMP: compat_m m' q cm),
    compat_m m q cm.
Proof.
  intros; inv COMP; constructor; simpl; intros.
  - apply addr_space.
    apply bw; auto.
  - apply overlap; auto.
    apply bw; auto.
    apply bw; auto.
  - rewrite ms. apply alignment.
Qed.



Lemma abi_in_bound:
  forall f m b o
         (ABI : all_blocks_injected f m)
         (IB : in_bound (Int.unsigned o) (bounds_of_block m b))
         (Fnone : f b = None),
    False.
Proof.
  intros.
  destruct (bounds_of_block m b) eqn:?.
  specialize (ABI b _ _ Heqp ).
  destruct (zeq (z0 - z) 0).
  unfold in_bound in IB. simpl in IB. omega. 
  apply ABI; auto.
Qed.


Lemma compat_inject:
  forall f m m'
         (ABI: all_blocks_injected f m)
         (INJ : inject f m m')
         cm q
         (COMP: compat_m m' q cm),
    compat_m m q (Val.inj_alloc cm f).
Proof.
  intros.
  constructor; simpl; intros; auto.
  - unfold Val.inj_alloc. 
    destruct (f b) eqn:?. 
    + destruct p.
      generalize (mi_bounds sm ei f _ _ (mi_inj _ _ _ INJ) _ _ _ _ Heqo0 H).
      intro A. 
      inv INJ.
      generalize (mi_representable' _ _ _ _ _ mi_inj0 _ _ _ (o) Heqo0 (or_introl H)).
      intro B.
      assert (z <= Int.max_unsigned). clear - B.
      generalize (Int.unsigned_range o).
      unfold Int.max_unsigned in *.
      {
        intro.
        destruct (zlt z 0). omega.
        apply B in g.
        omega.
      }
      generalize (addr_space _ _ _ _ COMP b0 (Int.add o (Int.repr z))).
      unfold Int.add.
      specialize (mi_delta_pos0 _ _ _ Heqo0).
      rewrite (Int.unsigned_repr z) by omega.
      intro C.
      rewrite Int.unsigned_repr in C by (intuition omega).
      specialize (C A).
      replace ( Int.unsigned
                  (Int.repr
                     (Int.unsigned
                        (Int.repr (Int.unsigned (cm b0) + z)) +
                      Int.unsigned o))) with
      (Int.unsigned (Int.repr (Int.unsigned (cm b0) + (Int.unsigned o + z)))).
      auto.
      rewrite <- (Int.unsigned_repr (Int.unsigned o + z)) by (intuition omega).
      rewrite ! int_add_rew.
      rewrite <- (Int.unsigned_repr z) by omega.
      rewrite ! int_add_rew.
      rewrite Int.add_assoc.
      rewrite (Int.add_commut o).
      auto.
    + exfalso.
      eapply abi_in_bound; eauto.
  - unfold Val.inj_alloc. 
    destruct (f b) eqn:?. destruct ( f b') eqn:?.
    + destruct p; destruct p0.
      generalize (mi_bounds _ ei f _ _ (mi_inj _ _ _ INJ) _ _ _ _ Heqo0 H0).
      generalize (mi_bounds _ ei f _ _ (mi_inj _ _ _ INJ) _ _ _ _ Heqo1 H1).
      intros A B.
      generalize (mi_no_overlap' f _ _ INJ b b0 z b' b1 z0 (Int.unsigned o) (Int.unsigned o') H Heqo0 Heqo1 H0 H1).
      intro C.
      destruct (eq_block b0 b1). subst.
      * destruct C; try congruence.
        inv INJ. generalize (mi_delta_pos0 _ _ _ Heqo1)
                            (mi_delta_pos0 _ _ _ Heqo0). intros.
        generalize (mi_representable' _ _ _ _ _ mi_inj0 _ _ _ o Heqo0 (or_introl H0)).
        generalize (mi_representable' _ _ _ _ _ mi_inj0 _ _ _ o' Heqo1 (or_introl H1)).
        revert H2 H3 H4.  clear.
        unfold Int.max_unsigned.
        intros.
        rewrite <- (Int.repr_unsigned (cm b1)).
        rewrite ! Val.int_add_repr. 
        unfold Int.add.
        generalize (cm b1).
        intros. rewrite ! Int.unsigned_repr_eq.
        {
          specialize (H H3). specialize (H0 H4).
          apply int_add_diff_range_plus; auto.
        }
      * inv COMP. clear C.
        inv INJ. generalize (mi_delta_pos0 _ _ _ Heqo1)
                            (mi_delta_pos0 _ _ _ Heqo0). intros.
        generalize (mi_representable' _ _ _ _ _ mi_inj0 _ _ _ o Heqo0 (or_introl H0)).
        generalize (mi_representable' _ _ _ _ _ mi_inj0 _ _ _ o' Heqo1 (or_introl H1)).
        intros. 
        rewrite <- (Int.unsigned_repr (Int.unsigned o' + z0)) in A by intuition omega.
        rewrite <- (Int.unsigned_repr (Int.unsigned o + z)) in B by intuition omega.
        generalize (addr_space _ _ A).
        generalize (addr_space _ _ B).
        assert (z <= Int.max_unsigned). clear - H3 H5.
        {
          generalize (Int.unsigned_range o).
          unfold Int.max_unsigned in *.
          intros.
          specialize (H5 H3).
          omega.
        }
        assert (z0 <= Int.max_unsigned). clear - H2 H4.
        {
          generalize (Int.unsigned_range o').
          unfold Int.max_unsigned in *.
          intros.
          specialize (H4 H2).
          omega.
        }
        rewrite <- (Int.unsigned_repr z) in B by omega.
        rewrite <- (Int.unsigned_repr z0) in A by omega.
        rewrite int_add_rew in A, B.
        generalize (overlap _ _ (Int.add o (Int.repr z)) (Int.add o' (Int.repr z0)) n B A).
        intros. clear - H8.
        rewrite ! Int.add_assoc. rewrite (Int.add_commut _ o).
        rewrite (Int.add_commut _ o'). auto.
    + exfalso.
      eapply abi_in_bound; eauto.
    + exfalso.
      eapply abi_in_bound with (b:=b); eauto.
  - inv COMP. 
    unfold Val.inj_alloc. des (f b). des p.
    clear addr_space overlap. 
    generalize (mi_align' _ _ _ _ _ (mi_inj _ _ _ INJ) _ _ _ Heqo). 
    specialize (alignment b0).
    intros  [A B].
    clear INJ.
    revert alignment.
    unfold nat_mask.  
    intros alignment.
    assert (fst (bounds_of_block m' b0) = 0).
    {
      unfold bounds_of_block.
      destr. des p.
      apply bounds_lo_inf0 in Heqo0. destr. 
    }
    eapply alignment_inj; eauto.
    + rewrite two_p_abs; auto.
    + Opaque two_power_nat.  unfold mask in *.
      destr.
      apply alignment_ok in Heqo0. subst.
      revert A; destr.
      * apply alignment_ok in Heqo1. destruct Heqo1 as [C D].
        red in B.
        destruct B; subst z. clear alignment.
        intros. rewrite <- (Int.not_involutive (Int.repr (x*two_p _))).
        rewrite <- Int.not_or_and_not.
        f_equal.
        solve_int. 
        rewrite ! Int.bits_not; auto.
        rewrite ! Int.testbit_repr; auto.
        rewrite two_power_nat_two_p.
        rewrite Int.Ztestbit_two_p_m1; auto; try omega.
        intros.
        destr'; try rewrite orb_false_r; auto.
        rewrite orb_true_r.
        generalize (Int.Ztestbit_mod_two_p (Z.of_nat n)
                                         (x*two_p (Z.of_nat n)) i).
        rewrite Heqs.
        clear A; intro A; rewrite <- A; try omega.
        rewrite Z_mod_mult.
        rewrite Int.Ztestbit_0. auto.
      * intros. assert (n = O) by omega.
        rewrite H0 in *.  
        change (two_power_nat 0 - 1) with 0.
        setoid_rewrite Int.not_zero.
        apply Int.and_mone.
      * change (two_power_nat 0 - 1) with 0.
        setoid_rewrite Int.not_zero.
        apply Int.and_mone.
Qed.

Lemma is_norm_m_is_norm:
  forall m e v,
    is_norm_m m e v ->
    IsNorm.t (bounds_of_block m) (nat_mask m) e v.
Proof.
  intros m e v [A]; constructor; auto.
Qed.

Lemma tpMA_not_null:
  Int.zero = Int.repr (two_power_nat MA) -> False.
Proof.
  intro EQ.
  apply f_equal with (f:=Int.unsigned) in EQ.
  rewrite Int.unsigned_zero in EQ.
  rewrite Int.unsigned_repr in EQ.
  generalize (two_power_nat_pos MA); lia.
  generalize (two_power_nat_pos MA); split. lia.
  unfold Int.max_unsigned.
  unfold Int.modulus.
  rewrite ! two_power_nat_two_p.
  generalize (two_p_monotone_strict (Z.of_nat MA) (Z.of_nat Int.wordsize)).
  intro A. trim A. clear A. split. lia.
  generalize (MA_bound). change (Int.wordsize) with (32%nat). lia.
  lia.
Qed.

Lemma inject_dep:
  forall f m e e' b
    (EI: expr_inj f e e')
    (DEP: depends Int.max_unsigned (bounds_of_block m) (nat_mask m) e b),
    f b <> None.
Proof.
  intros f m e e' b EI DEP.
  destruct (exists_two_cms m b) as (cm & cm' & COMP & COMP' & DIFF & SAME).
  specialize (DEP _ COMP _ COMP' DIFF dummy_em).
  clear COMP COMP'. revert e e' EI cm cm' DEP DIFF SAME.
  induction 1; simpl; intros; eauto.
  - inv VI; simpl in *; try congruence.
    destruct (peq b b1); subst; auto.
    congruence. rewrite SAME in DEP; auto.
  - apply (fun d => IHEI _ _ d DIFF SAME). intro EQ. rewrite EQ in DEP.  congruence.
  - unfold not in *. intro FB.
    specialize (fun d => IHEI1 _ _ d DIFF SAME FB).
    specialize (fun d => IHEI2 _ _ d DIFF SAME FB).
    apply Decidable.dec_not_not in IHEI1.
    apply Decidable.dec_not_not in IHEI2.
    congruence.
    destruct (Val.eq (eSexpr cm dummy_em f1) (eSexpr cm' dummy_em f1)); [left|right]; auto.
    destruct (Val.eq (eSexpr cm dummy_em e1) (eSexpr cm' dummy_em e1)); [left|right]; auto.
Qed.

Lemma not_injected_not_dep:
  forall f m m' e1 e1' b i (ABI : all_blocks_injected f m)
    (INJ : inject f m m') (EI : ei f e1 e1')
    (N : is_norm_m m e1 (Vptr b i)) (Fnone : f b = None), False.
Proof.
  intros.
  exploit is_norm_dep. apply is_norm_m_is_norm. eauto.
  intro GR.
  generalize (ei_ld'_expr ei wf f _ _ EI). intro A.
  (* destruct (exists_two_cms m b) as (cm & cm' & COMP & COMP' & DIFF & SAME). *)
  (* specialize (GR _ COMP _ COMP' DIFF dummy_em). *)
  (* specialize (fun cm0 cm'0 pf => A cm0 dummy_em cm'0 dummy_em pf (fun b0 b' delta FB i => eq_refl)). *)
  red in ABI;
    destruct (bounds_of_block m b) eqn:?.
  eapply ABI in Heqp; eauto.
  intro; subst.
  assert (z0 = z) by omega. subst.
  destruct (concrete_mem m') as [cm COMP].
  exploit compat_inject; eauto.  intro COMP'.
  assert (COMP'': compat_m m M32 (fun bb => if peq b bb
                                         then Int.add (Val.inj_alloc cm f b) (Int.repr (two_power_nat MA))
                                         else Val.inj_alloc cm f bb)).
  {
      inv COMP'.
      constructor; simpl; intros.
      destr_cond_match; subst; eauto.
      rewrite Heqp in H0; unfold in_bound in H0; destr; lia.
      repeat destr_cond_match; subst; eauto.
      rewrite Heqp in H1; unfold in_bound in H1; destr; lia.
      rewrite Heqp in H2; unfold in_bound in H2; destr; lia.
      destr_cond_match; subst; eauto.
      unfold Val.inj_alloc; rewrite Fnone. rewrite Int.add_zero_l.
      unfold nat_mask.
      cut (mask m b0 <= MA)%nat.
      generalize (mask m b0); clear. intros.
      solve_int.
      rewrite Int.bits_not; auto.
      rewrite ! Int.testbit_repr by auto.
      rewrite ! two_power_nat_two_p.
      rewrite Int.Ztestbit_two_p_m1; try lia.
      destr.
      2: apply andb_true_r.
      rewrite <- Int.testbit_repr; auto.
      replace (Int.repr (two_p (Z.of_nat MA))) with (Int.shl Int.one (Int.repr (Z.of_nat MA))).
      rewrite Int.bits_shl; auto.
      rewrite Int.unsigned_repr.
      rewrite Int.bits_one.
      apply Nat2Z.inj_le in H. destr. lia. generalize (MA_bound). intros [A B].
      assert (Z.of_nat 12 <= Int.max_unsigned) by (vm_compute; destr).
      apply Nat2Z.inj_le in B; lia.
      rewrite Int.shl_mul_two_p. rewrite Int.mul_commut, Int.mul_one.
      rewrite Int.unsigned_repr. auto.
      generalize (MA_bound). intros [A B].
      assert (Z.of_nat 12 <= Int.max_unsigned) by (vm_compute; destr). lia.
      unfold mask. destr. eapply alignment_ok; eauto. lia.
    }
    specialize (GR _ COMP' _ COMP'').
    trim GR. rewrite peq_true. rewrite <- Int.add_zero at 1.
    intro EQ; apply int_add_eq_l in EQ.
    apply tpMA_not_null; auto.
    set (em:= dummy_em).
    generalize (A cm em (Val.inj_alloc cm f) (Val.inj_em em f)).
    generalize (A cm em (fun bb => if peq b bb
                                then Int.add (Val.inj_alloc cm f b) (Int.repr (two_power_nat MA))
                                else (Val.inj_alloc cm f bb)) (Val.inj_em em f)).
    clear A; intros B C; trim B.
    { unfold Val.inj_alloc. red; intros. destr; try congruence.
      rewrite FB. auto. }
    trim B. apply em_inj_inj_em.
    trim C. apply cm_inj_inj_alloc.
    trim C. apply em_inj_inj_em.
    destruct N.
    rename eval_ok_m0 into N.
    generalize (N _ (Val.inj_em em f) COMP').
    generalize (N _ (Val.inj_em em f) COMP'').
    generalize (GR (Val.inj_em em f)).
    clear - B C. intros. simpl in *.
    inv H0.
    rewrite peq_true in H4. rewrite <- H4 in *.
    inv B. inv H1.
    rewrite <- H3, <- H5 in *.
    apply lessdef_vint in C.
    clear - C.
    rewrite ! (Int.add_commut _ i) in C.
    apply int_add_eq_l in C.
    rewrite <- Int.add_zero in C at 1.
    apply int_add_eq_l in C.     apply tpMA_not_null; auto. 
Qed.

Lemma norm_inject:
  forall f m m' e1 v1 e1'
         (ABI: all_blocks_injected f m)
         (INJ: inject f m m')
         (EI: ei f e1 e1')
         (NU: v1 <> Vundef),
  forall (MN:mem_norm m e1 = v1),
    mem_norm m' e1' <> Vundef /\    
    ei f (Eval v1) (Eval (mem_norm m' e1')).
Proof.  
  intros.
  assert (N:= norm_ld m e1 _ MN).
  assert (GR:= norm_gr m e1). rewrite MN in GR.
  clear MN.
  destruct (Val.apply_inj f (Eval v1)) eqn:?; try congruence.
  - destruct (inj_eval_eval _ _ _ Heqo). subst.
    cut (mem_norm m' e1' = x).
    intro MNV; subst.
    + split. 
      * unfold Val.apply_inj, Val.inj_ptr in Heqo. 
        intro H. rewrite H in Heqo.
        des v1. des (f b). des p.
      * inv wf.  apply vi_ei. auto. 
    + apply eq_norm.
      constructor.
      * intros alloc0 em COMPAT.
        setoid_rewrite <- (Val.apply_inj_eSexpr f alloc0 em _ _ Heqo); eauto.
        eapply Values.Val.lessdef_trans. apply N.
        eapply compat_inject with (q:=M32); eauto.
        eapply ei_ld_expr; eauto.
      * des v1.  unfold Val.inj_ptr in Heqo; des (f b); des p.
  - exfalso.
    des v1. 
    unfold Val.inj_ptr in Heqo;
      des (f b); try des p.
    eapply not_injected_not_dep in Heqo0; eauto.
    constructor; eauto.
Qed.

Lemma ei_vi_norm:
  forall f v1 v2 m m',
    all_blocks_injected f m ->
    inject f m m' ->
    ei f (Eval (mem_norm m v1)) (Eval v2) ->
    val_inject f (mem_norm m v1) v2.
Proof.
  intros f v1 v2 m m' ABI INJ EI.
  eapply ei_vi; eauto.  
  destr. 
  intro.
  generalize (norm_correct m v1); rewrite Heqv.
  intros.
  exploit not_injected_not_dep; eauto.
  constructor.
  red; intros; simpl; eauto.
Qed.

Lemma norm_inject_val':
  forall f m m' e1  e1'
         (ABI: all_blocks_injected f m)
         (INJ: inject f m m')
         (EI: ei f e1 e1'),
    val_inject f (mem_norm m e1) (mem_norm m' e1').
Proof.
  intros f m m' e1 e1' ABI INJ EI.
  assert (mem_norm m e1 = Vundef \/ mem_norm m e1 <> Vundef).
  {
    destruct (mem_norm m e1); tauto.
  }
  destruct H as [H|H].
  - rewrite H. constructor.
  - eapply norm_inject in H; eauto.
    destruct H as [H1 H2].
    eapply ei_vi_norm; eauto.
Qed.


Lemma sgn_lt:
  forall a, a > 0 -> Z.sgn a = 1.
Proof.
  des a; lia.
Qed.

Lemma sgn_le:
  forall a, a >= 0 -> Z.sgn a = 1 \/ Z.sgn a = 0.
Proof.
  des a; lia.
Qed.

Lemma propZ:
  forall (a b c d:Z),
    a = b -> c = d ->
    a = c ->
    b = d.
Proof.
  intros; subst; auto.
Qed.

Lemma align_ge2:
  forall al z,
    al > 0 ->
    align z al = z + (al - 1 - (z-1) mod al).
Proof.
  intros.
  destruct (align_ge1 z _ H) as [b [A [B C]]].
  rewrite B. f_equal.
  subst.
  generalize (Z_div_mod_eq (z-1) _ H).
  intros.
  assert (al *  ((z-1)/al) = z - 1 - (z-1) mod al) by lia.
  rewrite H1.  lia.
Qed.

Lemma sgn_gt x:
  Z.sgn x = 1 -> x > 0.
Proof. des x; lia. Qed.

Lemma filter_mbla_ext:
  forall sz n p p' (P: forall b, Ple b (Pos.of_nat n) -> p b = p' b),
    filter (fun x => p (fst x)) (mk_block_list_aux sz n) =
    filter (fun x => p' (fst x)) (mk_block_list_aux sz n).
Proof.
  induction n; simpl; intros; auto.
  trim (IHn p p').
  intros b PLT; apply P. ppsimpl; lia.
  rewrite P.
  destr; f_equal; auto.
  xomega.
Qed.

Theorem loadv_inject:
  forall f m1 m2 chunk a1 a2 v1
    (ABI: all_blocks_injected f m1)
    (MINJ: inject f m1 m2),
    loadv chunk m1 a1 = Some v1 ->
    ei f a1 a2 ->
    exists v2, loadv chunk m2 a2 = Some v2 /\ ei f v1 v2.
Proof.
  intros. 
  unfold loadv in H.
  destruct (mem_norm m1 a1) eqn:?; try discriminate.
  unfold loadv.
  exploit norm_inject; eauto.
  congruence.
  intros [A B].
  rewrite <- Heqv in B.
  eapply ei_vi_norm in B; eauto. rewrite Heqv in B. inv B.
  exploit load_inject; eauto. intros [v2 [LOAD INJ]].
  exists v2; split; auto. 
  replace (Int.unsigned (Int.add i (Int.repr delta)))
  with (Int.unsigned i + delta).
  auto. symmetry. eapply address_inject'; eauto with mem.
Qed.

Theorem loadbytes_inject:
  forall f m1 m2 b1 ofs len b2 delta bytes1,
  inject f m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject ei f) bytes1 bytes2.
Proof.
  intros. inv H. eapply loadbytes_inj; eauto. 
Qed.

(** Preservation of stores *)

Theorem store_mapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  ei f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ inject f n1 n2.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto. 
  eapply inject_meminj_no_overlap; eauto. 
  intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor; eauto; eauto with mem.
  - red; intros. eapply store_in_bound_m_2 in H6; eauto.
    eapply store_in_bound_m_2 in H7; eauto.
  -

    unfold is_dynamic_block, store, bounds_of_block in *;
    destr_in STORE; destr_in H0; inv STORE; inv H0; simpl in *. destr.
Qed.

Theorem storev_inject:
  forall f m1 m2 chunk a1 a2 b1 b2 v1
    (ABI: all_blocks_injected f m1),
    inject f m1 m2 ->
    storev chunk m1 a1 b1 = Some v1 ->
    ei f a1 a2 ->
    ei f b1 b2 ->
    exists v2, storev chunk m2 a2 b2 = Some v2 /\ inject f v1 v2.
Proof.
  intros. 
  unfold storev in H0.
  destruct (mem_norm m1 a1) eqn:?; try discriminate.
  unfold storev.
  
  exploit (norm_inject _ _ _ _ (Vptr b i) _ ABI H H1); eauto.
  congruence.
  intros [A B].
  rewrite <- Heqv in B. eapply ei_vi_norm in B; eauto.  rewrite Heqv in B; inv B.
  exploit store_mapped_inject; try eassumption; eauto.
  intros [v2 [STORE INJ]].
  exists v2; split; auto. 
  replace (Int.unsigned (Int.add i (Int.repr delta)))
  with (Int.unsigned i + delta).
  auto. symmetry. eapply address_inject'; eauto with mem.
Qed.

Theorem store_unmapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2,
    inject f m1 m2 ->
    store chunk m1 b1 ofs v1 = Some n1 ->
    f b1 = None ->
    inject f n1 m2.
Proof.
  intros. inversion H.
  constructor; eauto with mem.
  - (* inj *)
    eapply store_unmapped_inj; eauto.
  - (* no overlap *)
    red; intros. eapply store_in_bound_m_2 in H6; eauto.
    eapply store_in_bound_m_2 in H5; eauto.
  - unfold is_dynamic_block, store, bounds_of_block in *;
    destr_in H0; inv H0; simpl in *. destr. 
Qed.

Theorem store_outside_inject:
  forall f m1 m2 chunk b ofs v m2',
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v = Some m2' ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor; eauto with mem.
  eapply store_outside_inj; eauto.
  unfold is_dynamic_block, store, bounds_of_block in *;
    destr_in H1; inv H1; simpl in *. destr.
Qed.

Theorem storev_mapped_inject:
  forall f chunk m1 a1 v1 n1 m2 a2 v2
    (ABI: all_blocks_injected f m1),
  inject f m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  ei f a1 a2 ->
  ei f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ inject f n1 n2.
Proof.
  intros.
  unfold storev in *.
  revert H0; destr.
  generalize (norm_inject _ _ _ _ (Vptr b i) _  ABI H H1).
  intuition try congruence.
  rewrite <- Heqv in H5. eapply ei_vi_norm in H5; eauto.
  rewrite Heqv in H5; inv H5.
  replace (Int.unsigned (Int.add i (Int.repr delta)))
  with (Int.unsigned i + delta).
  eapply store_mapped_inject; try eassumption.
  destr.
  symmetry. eapply address_inject'; eauto with mem.
Qed.

Theorem storebytes_mapped_inject:
  forall f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject ei f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ inject f n1 n2.
Proof.
  intros. inversion H.
  exploit storebytes_mapped_inj; eauto. 
  eapply inject_meminj_no_overlap; eauto. intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor; eauto with mem.
  - intros. apply mi_freeblocks0. 
    red; intros; elim H3; eapply storebytes_valid_block_1; eauto.
  - intros. eapply storebytes_valid_block_1; eauto. 
  - red; intros. eapply storebytes_in_bound_m_2 in H6; eauto.
    eapply storebytes_in_bound_m_2 in H7; eauto.
  - unfold is_dynamic_block, storebytes, bounds_of_block in *;
    destr_in STORE; destr_in H0; inv STORE; inv H0; simpl in *. destr.
Qed.

Theorem storebytes_unmapped_inject:
  forall f m1 b1 ofs bytes1 n1 m2,
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  inject f n1 m2.
Proof.
  intros. inversion H.
  constructor; eauto with mem.
  - eapply storebytes_unmapped_inj; eauto.
  - intros. apply mi_freeblocks0. red; intros; elim H2; eapply storebytes_valid_block_1; eauto.
  - red; intros. eapply storebytes_in_bound_m_2 in H6; eauto.
    eapply storebytes_in_bound_m_2 in H5; eauto.
  - unfold is_dynamic_block, storebytes, bounds_of_block in *;
    destr_in H0; inv H0; simpl in *. destr.
Qed.

Theorem storebytes_outside_inject:
  forall f m1 m2 b ofs bytes2 m2',
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z_of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor; eauto.
  - eapply storebytes_outside_inj; eauto.
  - intros. eapply storebytes_valid_block_1; eauto.
  - unfold is_dynamic_block, storebytes, bounds_of_block in *;
    destr_in H1;inv H1; simpl in *. destr.
Qed.

Theorem storebytes_empty_inject:
  forall f m1 b1 ofs1 m1' m2 b2 ofs2 m2',
  inject f m1 m2 ->
  storebytes m1 b1 ofs1 nil = Some m1' ->
  storebytes m2 b2 ofs2 nil = Some m2' ->
  inject f m1' m2'.
Proof.
  intros. inversion H. constructor; intros; eauto.
  - eapply storebytes_empty_inj; eauto.
  - intros. apply mi_freeblocks0. red; intros; elim H2; eapply storebytes_valid_block_1; eauto.
  - intros. eapply storebytes_valid_block_1; eauto. 
  - red; intros. eapply storebytes_in_bound_m_2 in H6; eauto.
    eapply storebytes_in_bound_m_2 in H5; eauto.
  - unfold is_dynamic_block, storebytes, bounds_of_block in *;
    destr_in H1; destr_in H0; inv H1; inv H0; simpl in *.
    apply mi_inj_dynamic0. auto.
Qed.
(* Preservation of allocations *)

Theorem alloc_left_unmapped_inject:
  forall f m1 m2 lo hi m1' b1 bt,
  inject f m1 m2 ->
  alloc m1 lo hi bt = Some (m1', b1) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros. inversion H.
  set (f' := fun b => if eq_block b b1 then None else f b).
  assert (inject_incr f f').
  {
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  }
  assert (mem_inj sm ei f' m1 m2).
  {
    inversion mi_inj0; constructor; eauto with mem. 
    - unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    - unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    - unfold f'; intros. destruct (eq_block b b1).  congruence. eauto.
    - unfold f'; intros. destruct (eq_block b0 b1).  congruence.
      apply memval_inject_incr with f; auto.
  } 
  exists f'; split. constructor; eauto.
  - eapply alloc_left_unmapped_inj; eauto. unfold f'; apply dec_eq_true.
    unfold f'. intros; destr. eauto.
  - intros. unfold f'. destruct (eq_block b b1). auto. 
    apply mi_freeblocks0. red; intro; elim H3. eauto with mem. 
  - unfold f'; intros. destruct (eq_block b b1). congruence. eauto. 
  - unfold f'; red; intros.
    destruct (eq_block b0 b1); destruct (eq_block b2 b1); try congruence.
    eapply mi_no_overlap'0. eexact H3. eauto. eauto.
    unfold in_bound_m in *.
    erewrite <- bounds_of_block_alloc_other in H6; eauto.
    unfold in_bound_m in *.
    erewrite <- bounds_of_block_alloc_other in H7; eauto.
  - (* representable *)
    unfold f'; intros.
    destruct (eq_block b b1); try discriminate. eauto.
  - unfold f'. intros. destr_in H3.
    unfold is_dynamic_block, bounds_of_block in *;
      unfold alloc, low_alloc in H0; destr_in H0; inv H0; simpl in *.
    unfold f' in *. subst b1.
    rewrite ! PMap.gso by auto. move mi_inj_dynamic0 at bottom.
    specialize (mi_inj_dynamic0 _ _ _ H3).
    des mi_inj_dynamic0. des a.
    repSplit; eauto. intros A. intros. destr_in H0.
    apply e in H0; auto.
  - (* incr *)
    split; auto. 
    (* image *)
    split. unfold f'; apply dec_eq_true. 
    (* incr *)
    intros; unfold f'; apply dec_eq_false; auto.
Qed.

Lemma alloc_in_bound':
  forall m1 lo hi m2 b bt (ALLOC: alloc m1 lo hi bt = Some (m2, b)) b0 o,
    in_bound_m o m1 b0 ->
    in_bound_m o m2 b0.
Proof.
  intros m1 lo hi m2 b bt ALLOC b0 o IB.
  unfold in_bound_m in *.
  erewrite bounds_of_block_alloc_eq; eauto.
  destr_cond_match; subst; auto.
  + erewrite bounds_of_block_alloc_old in IB; eauto.
    unfold NormaliseSpec.in_bound in IB; simpl in IB; omega.
  + destr_cond_match; simpl; auto.
    destruct (bounds_of_block m1 b0) eqn:?; simpl in *.
    destruct IB; simpl in *.
    destruct (zeq z z0); subst. omega.
    apply Mem.bounds_of_block_valid in Heqp; auto.
    unfold Mem.valid_block in Heqp. clear Heqs0.
    erewrite nextblock_alloc in n0; eauto.
    xomega.
Qed.

Lemma alloc_in_bound_old:
  forall m1 lo hi m2 b bt (ALLOC: alloc m1 lo hi bt = Some (m2, b)) b0 o (diff: b <> b0),
    in_bound_m o m2 b0 ->
    in_bound_m o m1 b0.
Proof.
  intros m1 lo hi m2 b bt ALLOC b0 o diff IB.
  unfold in_bound_m in *.
  erewrite bounds_of_block_alloc_eq in IB; eauto.
  repeat destr_in IB.
  red in IB; destr; lia.
Qed.

Lemma ioa_div:
  forall sz delta,
    inj_offset_aligned delta sz ->
    (two_p (Z.of_nat (alignment_of_size sz)) | delta).
Proof.
  intros.
  rewrite <- two_power_nat_two_p. auto.
Qed. 
 
Definition align_distr := align_distr.

Opaque align.


Lemma alloc_less_ok:
  forall m z z0 bt,
    Mem.alloc m 0 z bt = None ->
    Mem.alloc m 0 z0 bt <> None ->
    0 <= z <= z0 ->
    False.
Proof.
  intros m z z0 bt ALLOC ALLOC' INF.
  unfold Mem.alloc, Mem.low_alloc in *.
  destr_in ALLOC. destr_in ALLOC'.
  clear ALLOC' ALLOC.
  generalize (box_span_le _ _ INF).
  rewrite Z.max_r in * by lia. lia.
Qed.

Lemma alloc_parallel_inj:
  forall f m1 m2 lo hi m1' b1 m b bt
         (INJ: inject f m1 m2)
         (ALLOC: alloc m1 lo hi bt = Some (m1', b1))
         (HIpos : hi >= 0)
         (ALLOC2 : alloc m2 lo hi bt = Some (m, b)),
    mem_inj sm ei (fun b0 : positive => if peq b0 b1 then Some (b, 0) else f b0) m1' m.
Proof.
  intros.
  inv INJ. inv mi_inj0.
  constructor; simpl; intros; eauto.
  - des (peq b0 b1).
    + inv H.
      apply perm_implies with (p1:=Freeable).
      apply (perm_alloc_2 _ _ _ _ _ _ ALLOC2); auto.
      apply perm_bounds in H0.
      unfold in_bound_m in *; rewrite (bounds_of_block_alloc _ _ _ _ _ _ ALLOC) in H0.
      unfold in_bound in H0; simpl in H0. rewrite Zmax_spec in H0; revert H0; destr; lia. 
      apply perm_F_any.
    + apply (perm_alloc_4 _ _ _ _ _ _ ALLOC) in H0; auto.
      generalize (mi_perm0 _ _ _ _ _ _ H H0).
      eapply perm_alloc_1; eauto.
  - des (peq b0 b1).
    + inv H.
      unfold in_bound_m in *; rewrite (bounds_of_block_alloc _ _ _ _ _ _ ALLOC2).
      rewrite (bounds_of_block_alloc _ _ _ _ _ _ ALLOC) in H0.
      unfold in_bound in *; simpl in *; omega.
    + unfold in_bound_m in *; rewrite <- (bounds_of_block_alloc_other _ _ _ _ _ _ ALLOC2); auto.
      rewrite <- (bounds_of_block_alloc_other _ _ _ _ _ _ ALLOC) in H0; auto.
      revert H0; apply mi_bounds0; auto.
      intro; subst.
      apply mi_mappedblocks0 in H.
      apply fresh_block_alloc in ALLOC2. auto.
  - destruct (peq b0 b1); subst; auto;  try inv H.
    rewrite (alloc_mask _ _ _ _ _ _ ALLOC).
    rewrite (alloc_mask _ _ _ _ _ _ ALLOC2).
    split. omega. apply Z.divide_0_r.
    rewrite <- (mask_alloc_other _ _ _ _ _ _ ALLOC); auto.
    rewrite <- (mask_alloc_other _ _ _ _ _ _ ALLOC2).
    apply mi_align'0. auto.
    apply mi_mappedblocks0 in H1.
    apply fresh_block_alloc in ALLOC2; auto.
    intro; subst; auto.
  - des (peq b0 b1).
    + inv H.
      generalize (mem_alloc_block_undefs _ _ _ _ _ _ ALLOC)
                 (mem_alloc_block_undefs _ _ _ _ _ _ ALLOC2).
      unfold block_undefs; intros B1 B2.
      rewrite <- (Z.add_0_r ofs) at 1.
      apply perm_bounds in H0.
      unfold in_bound_m in *;  rewrite (bounds_of_block_alloc _ _ _ _ _ _ ALLOC) in H0.
      unfold in_bound in H0; simpl in H0.
      auto.
      rewrite B1; auto.
      rewrite B2; auto.
      constructor. apply (vi_ei _ wf).
      simpl; unfold Val.inj_undef; simpl. auto. auto.
      rewrite Z.max_r in H0. auto. lia. lia.
    + rewrite (alloc_contents_old _ _ _ _ _ _ ALLOC2).
      rewrite (alloc_contents_old _ _ _ _ _ _ ALLOC); auto.
      apply (perm_alloc_4 _ _ _ _ _ _ ALLOC) in H0; auto.
      specialize (mi_memval0 _ _ _ _ H H0).
      inv mi_memval0. constructor.
      eapply (ei_inj_incr _ wf); eauto.
      red; intros.
      destr_cond_match. subst.
      rewrite mi_freeblocks0 in H1. congruence.
      eapply (fresh_block_alloc); eauto.
      apply mi_mappedblocks0 in H; auto.
      {
        des TYPorUNDEF. right.
        eapply same_eval_inj_incr; eauto.
        red; intros. destr.
        subst.
        rewrite mi_freeblocks0 in H1. congruence.
        eapply fresh_block_alloc; eauto. 
      }
      apply (fresh_block_alloc) in ALLOC2; auto.
      intro; subst. apply mi_mappedblocks0 in H. congruence.
  - rewrite (nb_boxes_alloc _ _ _ _ _ _ ALLOC), (nb_boxes_alloc _ _ _ _ _ _ ALLOC2). intuition lia.
Qed.

Lemma alloc_none_too_many_boxes:
  forall m lo hi bt (ALLOC: alloc m lo hi bt = None),
    Z.of_nat (nb_boxes_used_m m + box_span (Z.max 0 hi))%nat >= nb_boxes_max.
Proof.
  unfold alloc, low_alloc. intros. destr_in ALLOC.
Qed.

Lemma wfm_alloc: forall m, Z.of_nat (nb_boxes_used_m m) < nb_boxes_max.
Proof.
  unfold nb_boxes_used_m, mk_block_list. intros.
  eapply Z.le_lt_trans. 2: apply wfm_alloc_ok.
  apply Zle_refl.
Qed.

Theorem alloc_parallel_inject:
  forall f m1 m2 lo1 hi1 m1' b1 (ORD: lo1 <= hi1) bt
    (INJ: inject f m1 m2)
    (ALLOC: alloc m1 lo1 hi1 bt = Some (m1', b1))
    (HIpos: hi1 >= 0)
    (SM: sm = true),
  exists f', exists m2', exists b2,
        alloc m2 lo1 hi1 bt = Some (m2', b2)
        /\ inject f' m1' m2'
        /\ inject_incr f f'
        /\ f' b1 = Some(b2, 0)
        /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros. 
  destruct (alloc m2 lo1 hi1 bt) eqn:?.
  - destruct p.
    exists (fun b0 => if peq b0 b1 then Some (b,0) else f b0).
    exists m. exists b.
    intuition.
    + constructor; simpl; intros; eauto.
      * eapply alloc_parallel_inj; eauto.
      * destr. subst b0.
        contradict H. eapply valid_new_block; eauto.
        inv INJ; auto.
        apply mi_freeblocks0; auto.
        intro A. apply (valid_block_alloc _ _ _ _ _ _ ALLOC) in A. congruence.
      * inv INJ; eauto.
        destr_in H. 
        inv H.
        apply valid_new_block in Heqo; auto.
        apply mi_mappedblocks0 in H; auto.
        eapply valid_block_alloc in H; eauto.
      * inv INJ. red. intros b0 b1' delta1 b2 b2' delta2 ofs1 ofs2 diff F0 F2 i0 i2.
        {
          des (peq b0 b1).
          des (peq b2 b1).
          - left. inv F0.
            intro; subst.
            apply mi_mappedblocks0 in F2.
            apply (fresh_block_alloc _ _ _ _ _ _ Heqo) in F2; auto.
          - des (peq b2 b1). inv F2.
            + left. 
              intro; subst.
              apply mi_mappedblocks0 in F0.
              apply (fresh_block_alloc _ _ _ _ _ _ Heqo) in F0; auto.
            + red in mi_no_overlap'0. 
              apply (mi_no_overlap'0 _ _ _ _ _ _  _ _ diff); eauto.
              unfold in_bound_m in *;  rewrite <-  (bounds_of_block_alloc_other _ _ _ _ _ _ ALLOC) in i0; auto.
              unfold in_bound_m in *; rewrite <-(bounds_of_block_alloc_other _ _ _ _ _ _ ALLOC) in i2; auto.
        }
      * inv INJ.
        destruct (peq b0 b1); subst; auto.
        inv H. omega. eauto.
      * inv INJ. destr_in H.
        inv H.
        unfold is_dynamic_block, bounds_of_block in *;
          unfold alloc, low_alloc in ALLOC, Heqo; destr_in ALLOC; destr_in Heqo; inv ALLOC; inv Heqo;
          simpl in *.
        rewrite ! PMap.gss. repSplit; destr.
        intro A; inv A. intros. destr_in H. apply mi_mappedblocks0 in H. red in H; xomega.
        assert (b' <> b).
        intro; subst. apply mi_mappedblocks0 in H. apply alloc_result in Heqo.
        subst; red in H; xomega.
        unfold is_dynamic_block, bounds_of_block in *;
          unfold alloc, low_alloc in ALLOC, Heqo; destr_in ALLOC; destr_in Heqo; inv ALLOC; inv Heqo;
          simpl in *.
        rewrite ! PMap.gso by auto.                
        des (mi_inj_dynamic0 _ _ _ H). des a.
        repSplit; auto. intros. destr_in H2.
        eapply e; eauto.
    + unfold inject_incr.
      intros.
      des (peq b0 b1).    
      rewrite mi_freeblocks with (m1:=m1) (m2:=m2) in H; auto.
      congruence.
      eapply fresh_block_alloc; eauto. subst b0; eauto.
    + rewrite peq_true. auto.
    + rewrite peq_false; auto.
  - exfalso.  
    rewrite alloc_lo_0 in *.
    apply alloc_none_too_many_boxes in Heqo.
    apply nb_boxes_alloc in ALLOC.
    generalize (mi_size_mem _ _ _ _ _ (mi_inj _ _ _ INJ)). 
    generalize (wfm_alloc m1').
    intros.
    intuition lia. 
Qed.

(** Preservation of [free] operations *)

Lemma perm_free_list:
  forall l m m' b ofs k p,
  free_list m l = Some m' ->
  perm m' b ofs k p ->
  perm m b ofs k p /\ 
  (forall lo hi, In (b, lo, hi) l -> lo <= ofs < hi -> False).
Proof.
  induction l; simpl; intros.
  inv H. auto. 
  destruct a as [[b1 lo1] hi1].
  destruct (free m b1 lo1 hi1) as [m1|] eqn:E; try discriminate.
  exploit IHl; eauto. intros [A B].
  split. eauto with mem.
  intros. destruct H1. inv H1.
  elim (perm_free_2 _ _ _ _ _ E ofs k p). auto. auto.
  eauto.
Qed.

Lemma drop_outside_inject: 
  forall f m1 m2 b lo hi p m2',
    inject f m1 m2 -> 
    drop_perm m2 b lo hi p = Some m2' -> 
    (forall b' delta ofs k p,
       f b' = Some(b, delta) ->
       perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
    inject f m1 m2'.
Proof.
  intros. destruct H. constructor; eauto.
  eapply drop_outside_inj; eauto.
  intros. unfold valid_block in *. erewrite nextblock_drop; eauto.
  unfold is_dynamic_block, bounds_of_block in *;
    unfold drop_perm in H0; destr_in H0; inv H0; simpl in *. destr.          
Qed.

(** Injecting a memory into itself. *)

Definition flat_inj (thr: block) : meminj :=
  fun (b: block) => if plt b thr then Some(b, 0) else None.

Definition inject_neutral (thr: block) (m: mem) :=
  mem_inj sm ei (flat_inj thr) m m.

Remark flat_inj_no_overlap:
  forall thr m, meminj_no_overlap (flat_inj thr) m.
Proof.
  unfold flat_inj; intros; red; intros.
  destruct (plt b1 thr); inversion H0; subst.
  destruct (plt b2 thr); inversion H1; subst.
  auto.
Qed.

Theorem neutral_inject:
  forall m, inject_neutral (nextblock m) m -> 
            inject (flat_inj (nextblock m)) m m.
Proof.
  intros. constructor.
  - (* meminj *)
    auto.
  - (* freeblocks *)
    unfold flat_inj, valid_block; intros.
    apply pred_dec_false. auto. 
  - (* mappedblocks *)
    unfold flat_inj, valid_block; intros. 
    destruct (plt b (nextblock m)); inversion H0; subst. auto.
  - (* no overlap *)
    red; intros.
    unfold flat_inj in *.
    des (plt b1 (nextblock m));
      des (plt b2 (nextblock m)).
  - (* range *)
    unfold flat_inj; intros.  
    destruct (plt b (nextblock m)); inv H0. omega.
  - unfold flat_inj.
    intros. destr_in H0. inv H0. red in H.
    repSplit; auto. tauto.
    intros. destr_in H1.
Qed.

Theorem empty_inject_neutral:
  forall thr, inject_neutral thr empty.
Proof.
  intros thr; red; constructor; eauto.
-(* perm *)
  unfold flat_inj; intros. destruct (plt b1 thr); inv H.
  replace (ofs + 0) with ofs by omega; auto.

-(* perm *)
  unfold flat_inj; intros. destruct (plt b1 thr); inv H.
  replace (ofs + 0) with ofs by omega; auto.

-(* align *)
  unfold flat_inj; intros. destruct (plt b thr); inv H. 
  split; try omega.
  unfold mask; simpl.
  rewrite PMap.gi. simpl. apply Z.divide_1_l.
- (* mem_contents *)
  intros.
  apply perm_empty in H0. exfalso; auto.
Qed.

Theorem alloc_inject_neutral:
  forall thr m lo hi b m' bt
         (ALLOC: alloc m lo hi bt = Some (m', b))
         (LO: lo <= 0)
         (INJ: inject_neutral thr m)
         (LT: Plt (nextblock m) thr),
    inject_neutral thr m'.
Proof. 
  intros; inv INJ.
  constructor; simpl; intros; eauto.
  - unfold flat_inj  in H.
    des (plt b1 thr). inv H.
    rewrite Z.add_0_r; auto.
  - unfold flat_inj  in H.
    des (plt b1 thr). inv H.
    rewrite Z.add_0_r; auto.
  - unfold flat_inj  in H.
    des (plt b0 thr). inv H. split. omega.
    apply Z.divide_0_r.
  - unfold flat_inj  in H.
    des (plt b1 thr). inv H.
    rewrite Z.add_0_r; auto.
    destruct (peq b2 b); subst; auto.
    + apply perm_bounds in H0.
      unfold in_bound_m in *; rewrite (bounds_of_block_alloc _ _ _ _ _ _ ALLOC) in H0.
      unfold in_bound in H0; simpl in H0.
      apply mem_alloc_block_undefs in ALLOC.
      red in ALLOC.
      rewrite <- (Z.add_0_r ofs).
      rewrite ALLOC; auto.
      constructor.
      inv wf.  apply vi_ei. simpl.
      unfold Val.inj_undef; simpl.
      unfold flat_inj. destr; try xomega. repeat f_equal. (* rewrite Val.int_add_repr. f_equal; lia. *)
      auto.
      rewrite Zmax_spec in H0; revert H0; destr; lia. 
    + apply (perm_alloc_4 _ _ _ _ _ _ ALLOC) in H0; auto.
      rewrite (alloc_contents_old _ _ _ _ _ _ ALLOC); auto.
      rewrite <- (Z.add_0_r ofs) at 2.
      apply mi_memval0; auto.
      unfold flat_inj; destr.
Qed.

Theorem store_inject_neutral:
  forall chunk m b ofs v m' thr,
  store chunk m b ofs v = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  ei (flat_inj thr) v v ->
  inject_neutral thr m'.
Proof.
  intros; red.
  exploit store_mapped_inj; try eassumption. eauto. apply flat_inj_no_overlap. 
  unfold flat_inj. apply pred_dec_true; auto. eauto.
  replace (ofs + 0) with ofs by omega.  
  intros [m'' [A B]]. congruence.
Qed. 

Theorem drop_inject_neutral:
  forall m b lo hi p m' thr,
  drop_perm m b lo hi p = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  inject_neutral thr m'.
Proof.
  unfold inject_neutral; intros.
  exploit drop_mapped_inj; eauto. apply flat_inj_no_overlap. 
  unfold flat_inj. apply pred_dec_true; eauto. 
  repeat rewrite Zplus_0_r. intros [m'' [A B]]. congruence.
Qed.

End INJECT.

Definition one2oneinject (f: meminj) :=
  forall b b' delta, f b = Some (b', delta) -> delta = 0.
  
(* The following axiom states that:
 * for an injection f that is one-to-one (i.e. it maps one block to itself (modulo renaming))
 * for any memories m1 and m2 such that m1 injects into m2
 * for any concrete memory cm2 of m2
 * there exists a concrete memory of m1 that agrees with cm2 on all injected blocks.
 * This is true because existence of memory m1 implies the existence of a concrete memory cm,
 * that gives the maximum alignement to blocks in a 31-bit-memory. This gives us enough space 
 * to fit the blocks in twice as much memory with fewer alignment constraints.
 * This is left as an axiom for the time being.
 *)

(** * Invariance properties between two memory states *)

Section UNCHANGED_ON.

Variable P: block -> Z -> Prop.

Record unchanged_on (m_before m_after: mem) : Prop := mk_unchanged_on {
  unchanged_on_perm:
    forall b ofs k p,
    P b ofs -> valid_block m_before b ->
    (perm m_before b ofs k p <-> perm m_after b ofs k p);
  unchanged_on_contents:
    forall b ofs,
    P b ofs -> perm m_before b ofs Cur Readable ->
    ZMap.get ofs (PMap.get b m_after.(mem_contents)) =
    ZMap.get ofs (PMap.get b m_before.(mem_contents))
}.

Lemma unchanged_on_refl:
  forall m, unchanged_on m m.
Proof.
  intros; constructor; tauto.
Qed.

Lemma perm_unchanged_on:
  forall m m' b ofs k p,
  unchanged_on m m' -> P b ofs -> valid_block m b ->
  perm m b ofs k p -> perm m' b ofs k p.
Proof.
  intros. destruct H. apply unchanged_on_perm0; auto. 
Qed.

Lemma perm_unchanged_on_2:
  forall m m' b ofs k p,
  unchanged_on m m' -> P b ofs -> valid_block m b ->
  perm m' b ofs k p -> perm m b ofs k p.
Proof.
  intros. destruct H. apply unchanged_on_perm0; auto. 
Qed.

Lemma loadbytes_unchanged_on_1:
  forall m m' b ofs n,
  unchanged_on m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m' b ofs n = loadbytes m b ofs n.
Proof.
  intros. 
  destruct (zle n 0).
+ erewrite ! loadbytes_empty by assumption. auto.
+ unfold loadbytes. destruct H.
  destruct (range_perm_dec m b ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true. f_equal.
  apply getN_exten. intros. rewrite nat_of_Z_eq in H by omega.
  apply unchanged_on_contents0; auto.
  red; intros. apply unchanged_on_perm0; auto. 
  rewrite pred_dec_false. auto.
  red; intros; elim n0; red; intros. apply <- unchanged_on_perm0; auto.
Qed.

Lemma loadbytes_unchanged_on:
  forall m m' b ofs n bytes,
  unchanged_on m m' ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m b ofs n = Some bytes ->
  loadbytes m' b ofs n = Some bytes.
Proof.
  intros. 
  destruct (zle n 0).
+ erewrite loadbytes_empty in * by assumption. auto.
+ rewrite <- H1. apply loadbytes_unchanged_on_1; auto. 
  exploit loadbytes_range_perm; eauto. instantiate (1 := ofs). omega. 
  intros. eauto with mem.
Qed.

Lemma load_unchanged_on_1:
  forall m m' chunk b ofs,
  unchanged_on m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m' b ofs = load chunk m b ofs.
Proof.
  intros. unfold load. destruct (valid_access_dec m chunk b ofs Readable).
  destruct v. rewrite pred_dec_true. f_equal. f_equal. apply getN_exten. intros. 
  rewrite <- size_chunk_conv in H4. eapply unchanged_on_contents; eauto.
  split; auto. red; intros. eapply perm_unchanged_on; eauto.
  rewrite pred_dec_false. auto. 
  red; intros [A B]; elim n; split; auto. red; intros; eapply perm_unchanged_on_2; eauto. 
Qed.

Lemma load_unchanged_on:
  forall m m' chunk b ofs v,
  unchanged_on m m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m b ofs = Some v ->
  load chunk m' b ofs = Some v.
Proof.
  intros. rewrite <- H1. eapply load_unchanged_on_1; eauto with mem.
Qed.

Lemma store_unchanged_on:
  forall chunk m b ofs v m',
  store chunk m b ofs v = Some m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- split; intros; eauto with mem.
- erewrite store_mem_contents; eauto. rewrite PMap.gsspec. 
  destruct (peq b0 b); auto. subst b0. apply setN_outside. 
  erewrite encode_val_length; eauto. rewrite <- size_chunk_conv. 
  destruct (zlt ofs0 ofs); auto. 
  destruct (zlt ofs0 (ofs + size_chunk chunk)); auto.
  elim (H0 ofs0). omega. auto.
Qed.

Lemma storebytes_unchanged_on:
  forall m b ofs bytes m',
  storebytes m b ofs bytes = Some m' ->
  (forall i, ofs <= i < ofs + Z_of_nat (length bytes) -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- split; intros. eapply perm_storebytes_1; eauto. eapply perm_storebytes_2; eauto. 
- erewrite storebytes_mem_contents; eauto. rewrite PMap.gsspec. 
  destruct (peq b0 b); auto. subst b0. apply setN_outside. 
  destruct (zlt ofs0 ofs); auto. 
  destruct (zlt ofs0 (ofs + Z_of_nat (length bytes))); auto.
  elim (H0 ofs0). omega. auto.
Qed.

Lemma alloc_unchanged_on:
  forall m lo hi m' b bt, 
  alloc m lo hi bt = Some (m', b) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- split; intros.
  eapply perm_alloc_1; eauto.
  eapply perm_alloc_4; eauto. 
  eapply valid_not_valid_diff; eauto with mem.
- unfold alloc, low_alloc in H.
  destr_in H.
  injection H; intros A B. rewrite <- B; simpl.
  rewrite PMap.gso; auto. rewrite A.  eapply valid_not_valid_diff; eauto with mem.
  subst. clear. unfold valid_block; xomega.
Qed.

Lemma free_unchanged_on:
  forall m b lo hi m',
  free m b lo hi = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- split; intros. 
  eapply perm_free_1; eauto. 
  destruct (eq_block b0 b); auto. destruct (zlt ofs lo); auto. destruct (zle hi ofs); auto. 
  subst b0. elim (H0 ofs). omega. auto.
  eapply perm_free_3; eauto.
- unfold free in H. repeat destr_in H; inv H. 
  simpl. auto.
Qed.

End UNCHANGED_ON.



End Mem.

Notation mem := Mem.mem.



Global Opaque Mem.alloc Mem.free Mem.store Mem.load Mem.storebytes Mem.loadbytes.

Hint Resolve
  Mem.valid_not_valid_diff
  Mem.perm_implies
  Mem.perm_cur
  Mem.perm_max
  Mem.perm_valid_block
  Mem.range_perm_implies
  Mem.range_perm_cur
  Mem.range_perm_max
  Mem.valid_access_implies
  Mem.valid_access_valid_block
  Mem.valid_access_perm
  Mem.valid_access_load
  Mem.load_valid_access
  Mem.loadbytes_range_perm
  Mem.valid_access_store
  Mem.perm_store_1
  Mem.perm_store_2
  Mem.nextblock_store
  Mem.store_valid_block_1
  Mem.store_valid_block_2
  Mem.store_valid_access_1
  Mem.store_valid_access_2
  Mem.store_valid_access_3
  Mem.storebytes_range_perm
  Mem.perm_storebytes_1
  Mem.perm_storebytes_2
  Mem.storebytes_valid_access_1
  Mem.storebytes_valid_access_2
  Mem.nextblock_storebytes
  Mem.storebytes_valid_block_1
  Mem.storebytes_valid_block_2
  Mem.nextblock_alloc
  Mem.alloc_result
  Mem.valid_block_alloc
  Mem.fresh_block_alloc
  Mem.valid_new_block
  Mem.perm_alloc_1
  Mem.perm_alloc_2
  Mem.perm_alloc_3
  Mem.perm_alloc_4
  Mem.perm_alloc_inv
  Mem.valid_access_alloc_other
  Mem.valid_access_alloc_same
  Mem.valid_access_alloc_inv
  Mem.range_perm_free
  Mem.free_range_perm
  Mem.nextblock_free
  Mem.valid_block_free_1
  Mem.valid_block_free_2
  Mem.perm_free_1
  Mem.perm_free_2
  Mem.perm_free_3
  Mem.valid_access_free_1
  Mem.valid_access_free_2
  Mem.valid_access_free_inv_1
  Mem.valid_access_free_inv_2
  Mem.unchanged_on_refl
: mem.


