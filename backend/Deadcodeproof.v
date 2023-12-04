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

(** Elimination of unneeded computations over RTL: correctness proof. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import IntvSets.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import ExprEval Values_symbolictype Values_symbolic Normalise NormaliseSpec
        Memory.
Require Import MemRel.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Lattice.
Require Import Kildall.
Require Import ValueDomain.
Require Import ValueAnalysis.
Require Import NeedDomain.
Require Import NeedOp.
Require Import Deadcode.
Require Import Tactics.
(** * Relating the memory states *)

(** The [magree] predicate is a variant of [Mem.extends] where we
  allow the contents of the two memory states to differ arbitrarily
  on some locations.  The predicate [P] is true on the locations whose
  contents must be in the [lessdef] relation. *)

Definition locset := block -> Z -> Prop.

Record magree (m1 m2: mem) (P: locset) : Prop := mk_magree {
  ma_access:
    forall b, (Mem.mem_access m1) # b = (Mem.mem_access m2) # b;
  ma_bs:
    forall b,
      (Mem.mem_blocksize m1) # b = (Mem.mem_blocksize m2) # b;
  ma_bm:
    forall b,
      (Mem.mem_mask m1) # b = (Mem.mem_mask m2) # b;
  ma_bt:
    forall b,
      (Mem.mem_blocktype m1) # b = (Mem.mem_blocktype m2) # b;
 ma_memval:
    forall b ofs,
    Mem.perm m1 b ofs Cur Readable ->
    P b ofs ->
    memval_lessdef (ZMap.get ofs (PMap.get b (Mem.mem_contents m1)))
                   (ZMap.get ofs (PMap.get b (Mem.mem_contents m2)));
  ma_nextblock:
    Mem.nextblock m2 = Mem.nextblock m1;
  ma_nb_extra:
    Mem.nb_extra m2 = Mem.nb_extra m1
}.

Lemma ma_perm:
  forall m1 m2 P,
    magree m1 m2 P ->
    forall b ofs k p,
      Mem.perm m1 b ofs k p ->
      Mem.perm m2 b ofs k p.
Proof.
  unfold Mem.perm; intros.
  inv H. rewrite ma_access0 in H0; auto.
Qed.

Lemma magree_monotone:
  forall m1 m2 (P Q: locset),
  magree m1 m2 P ->
  (forall b ofs, Q b ofs -> P b ofs) ->
  magree m1 m2 Q.
Proof.
  intros. destruct H. constructor; auto.
Qed.

Lemma mextends_agree:
  forall m1 m2 P, mem_rel Val.lessdef m1 m2 -> magree m1 m2 P.
Proof.
  intros. inv H. constructor; intros; auto.
  apply mem_contents_eq.
  auto.
Qed.

Lemma magree_extends:
  forall m1 m2 (P: locset),
  (forall b ofs, P b ofs) ->
  magree m1 m2 P -> mem_rel Val.lessdef m1 m2.
Proof.
  intros. destruct H0. constructor; auto.
  - intros. apply ma_memval0; auto.
Qed.

Lemma magree_loadbytes:
  forall m1 m2 P b ofs n bytes,
  magree m1 m2 P ->
  Mem.loadbytes m1 b ofs n = Some bytes ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  exists bytes', Mem.loadbytes m2 b ofs n = Some bytes' /\ list_forall2 memval_lessdef bytes bytes'.
Proof.
  assert (GETN: forall c1 c2 n ofs,
    (forall i, ofs <= i < ofs + Z.of_nat n -> memval_lessdef (ZMap.get i c1) (ZMap.get i c2)) ->
    list_forall2 memval_lessdef (Mem.getN n ofs c1) (Mem.getN n ofs c2)).
  {
    induction n; intros; simpl. 
    constructor.
    rewrite inj_S in H. constructor.
    apply H. omega. 
    apply IHn. intros; apply H; omega.
  }
Local Transparent Mem.loadbytes.
  unfold Mem.loadbytes; intros. (* destruct H.  *)
  destruct (Mem.range_perm_dec m1 b ofs (ofs + n) Cur Readable); inv H0.
  rewrite pred_dec_true. econstructor; split; eauto.
  apply GETN. intros. rewrite nat_of_Z_max in H0.
  assert (ofs <= i < ofs + n) by xomega. 
  eapply ma_memval; eauto.
  eauto. red; intros; eauto. 
  eapply ma_perm; eauto.
Qed.

Lemma magree_load:
  forall m1 m2 P chunk b ofs v,
  magree m1 m2 P ->
  Mem.load chunk m1 b ofs = Some v ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  exists v', Mem.load chunk m2 b ofs = Some v' /\ Val.lessdef v v'.
Proof.
  intros. exploit Mem.load_valid_access; eauto. intros [A B]. 
  exploit Mem.load_loadbytes; eauto. intros [bytes [C D]].
  exploit magree_loadbytes; eauto. intros [bytes' [E F]].
  exists (decode_val chunk bytes'); split. 
  apply Mem.loadbytes_load; auto. 
  subst. apply decode_val_spec; auto.  apply wf_mr_ld.
Qed.

Lemma magree_storebytes_parallel:
  forall m1 m2 (P Q: locset) b ofs bytes1 m1' bytes2,
  magree m1 m2 P ->
  Mem.storebytes m1 b ofs bytes1 = Some m1' ->
  (forall b' i, Q b' i ->
                b' <> b \/ i < ofs \/ ofs + Z_of_nat (length bytes1) <= i ->
                P b' i) ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2', Mem.storebytes m2 b ofs bytes2 = Some m2' /\ magree m1' m2' Q.
Proof.
  assert (SETN: forall (access: Z -> Prop) bytes1 bytes2,
    list_forall2 memval_lessdef bytes1 bytes2 ->
    forall p c1 c2,
    (forall i, access i -> i < p \/ p + Z.of_nat (length bytes1) <= i -> memval_lessdef (ZMap.get i c1) (ZMap.get i c2)) ->
    forall q,  access q ->
    memval_lessdef (ZMap.get q (Mem.setN bytes1 p c1))
                   (ZMap.get q (Mem.setN bytes2 p c2))).
  {
    induction 1; intros; simpl.
  - apply H; auto. simpl. omega.
  - simpl length in H1; rewrite inj_S in H1. 
    apply IHlist_forall2; auto. 
    intros. rewrite ! ZMap.gsspec. destruct (ZIndexed.eq i p). auto. 
    apply H1; auto. unfold ZIndexed.t in *; omega. 
  }
  intros. 
  destruct (Mem.range_perm_storebytes m2 b ofs bytes2) as [m2' ST2].
  { erewrite <- list_forall2_length by eauto. red; intros.
    eapply ma_perm; eauto. 
    eapply Mem.storebytes_range_perm; eauto. }
  exists m2'; split; auto. 
  constructor; intros.
  - Transparent Mem.storebytes.
    unfold Mem.storebytes in H0, ST2.
    destr_in H0; inv H0. destr_in ST2; inv ST2. simpl. inv H; auto.
  - unfold Mem.storebytes in H0, ST2.
    destr_in H0; inv H0. destr_in ST2; inv ST2. simpl. inv H; auto.
  - unfold Mem.storebytes in H0, ST2.
    destr_in H0; inv H0. destr_in ST2; inv ST2. simpl. inv H; auto.
  - unfold Mem.storebytes in H0, ST2.
    destr_in H0; inv H0. destr_in ST2; inv ST2. simpl. inv H; auto.
  - rewrite (Mem.storebytes_mem_contents _ _ _ _ _ H0).
    rewrite (Mem.storebytes_mem_contents _ _ _ _ _ ST2).
    rewrite ! PMap.gsspec. destr.
    + subst. apply SETN with (access := fun ofs => Mem.perm m1 b ofs Cur Readable /\ Q b ofs); auto.
      intros. eapply ma_memval; eauto. apply H5.
      apply H1; auto. apply H5. split; auto.
      eapply Mem.perm_storebytes_2; eauto.
    + eapply ma_memval; eauto.
      eapply Mem.perm_storebytes_2; eauto.
      apply H1; auto.
  - rewrite (Mem.nextblock_storebytes _ _ _ _ _ H0).
    rewrite (Mem.nextblock_storebytes _ _ _ _ _ ST2).
    eapply ma_nextblock; eauto.
  - rewrite <- (Mem.nb_extra_storebytes _ _ _ _ _ H0).
    rewrite <- (Mem.nb_extra_storebytes _ _ _ _ _ ST2).
    eapply ma_nb_extra; eauto. 
Qed.

Lemma magree_store_parallel:
  forall m1 m2 (P Q: locset) chunk b ofs v1 m1' v2,
  magree m1 m2 P ->
  Mem.store chunk m1 b ofs v1 = Some m1' ->
  vagree v1 v2 (store_argument chunk) ->
  (forall b' i, Q b' i ->
                b' <> b \/ i < ofs \/ ofs + size_chunk chunk <= i ->
                P b' i) ->
  exists m2', Mem.store chunk m2 b ofs v2 = Some m2' /\ magree m1' m2' Q.
Proof.
  intros. 
  exploit Mem.store_valid_access_3; eauto. intros [A B]. 
  exploit Mem.store_storebytes; eauto. intros SB1.
  exploit magree_storebytes_parallel. eauto. eauto. 
  instantiate (1 := Q). intros. rewrite encode_val_length in H4.
  rewrite <- size_chunk_conv in H4. apply H2; auto. 
  eapply store_argument_sound; eauto. 
  intros [m2' [SB2 AG]]. 
  exists m2'; split; auto.
  apply Mem.storebytes_store; auto. 
Qed.

Lemma magree_storebytes_left:
  forall m1 m2 P b ofs bytes1 m1',
  magree m1 m2 P ->
  Mem.storebytes m1 b ofs bytes1 = Some m1' ->
  (forall i, ofs <= i < ofs + Z_of_nat (length bytes1) -> ~(P b i)) ->
  magree m1' m2 P.
Proof.
  intros. inv H; constructor; intros; auto;
            try solve [unfold Mem.storebytes in H0; destr_in H0; inv H0; simpl in *; auto].
- rewrite (Mem.storebytes_mem_contents _ _ _ _ _ H0).
  rewrite PMap.gsspec. destruct (peq b0 b).
+ subst b0. rewrite Mem.setN_outside. eapply ma_memval0; eauto. 
  eapply Mem.perm_storebytes_2; eauto.
  destruct (zlt ofs0 ofs); auto.
  destruct (zle (ofs + Z.of_nat (length bytes1)) ofs0); try omega.
  elim (H1 ofs0). omega. auto. 
+ apply ma_memval0; eauto.
  eapply Mem.perm_storebytes_2; eauto.
Qed.

Lemma magree_store_left:
  forall m1 m2 P chunk b ofs v1 m1',
  magree m1 m2 P ->
  Mem.store chunk m1 b ofs v1 = Some m1' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~(P b i)) ->
  magree m1' m2 P.
Proof.
  intros. eapply magree_storebytes_left; eauto.
  eapply Mem.store_storebytes; eauto. 
  intros. rewrite encode_val_length in H2.
  rewrite <- size_chunk_conv in H2. apply H1; auto. 
Qed.

Lemma magree_unchecked_free:
  forall m1 m2 (P : locset) m1' n,
    MemReserve.release_boxes m1 n = Some m1' ->
    magree m1 m2 P ->
    (* (forall b' i, Q b' i -> b <> b' \/ ~ (lo <= i < hi) -> P b' i) -> *)
    exists m2',
      MemReserve.release_boxes m2 n = Some m2' /\
      magree m1' m2' P.
Proof.
  intros m1 m2 P m1' n REL H.
  unfold MemReserve.release_boxes in *.  destr_in REL. inv REL. destr. eexists; split; eauto.
  inversion H.
  constructor; intros; simpl; auto.
  exfalso.
  erewrite ma_nb_extra in n0; eauto.
Qed.

Lemma magree_free:
  forall m1 m2 (P Q: locset) b lo hi m1',
  magree m1 m2 P ->
  Mem.free m1 b lo hi = Some m1' ->
  (forall b' i, Q b' i ->
                b' <> b \/ ~(lo <= i < hi) ->
                P b' i) ->
  (* (forall b' i, Q b' i -> b' <> b \/ ~(lo <= i < hi)) -> *)
  exists m2', Mem.free m2 b lo hi = Some m2' /\ magree m1' m2' Q.
Proof.
  intros. 
  destruct (Mem.range_perm_free m2 b lo hi) as [m2' FREE].
  red; intros. eapply ma_perm; eauto. eapply Mem.free_range_perm; eauto. 
  {
    Transparent Mem.free. unfold Mem.free in H0.
    repeat destr_in H0.
    revert Heqb0.
    unfold Mem.has_bounds. unfold Mem.bounds_of_block.
    erewrite ma_bs; eauto.
  }
  exists m2'; split; auto.
  constructor; intros.
- (* permissions *)
  unfold Mem.free in H0; repeat destr_in H0; inv H0.
  unfold Mem.free in FREE; repeat destr_in FREE; inv FREE.
  simpl.
  rewrite ! PMap.gsspec. inv H. destr; auto.
  apply Axioms.extensionality. intros.
  apply Axioms.extensionality. intros.
  destr.
  rewrite ma_access0. auto.
-
  unfold Mem.free in H0; repeat destr_in H0; inv H0.
  unfold Mem.free in FREE; repeat destr_in FREE; inv FREE.
  simpl.
  rewrite ! PMap.gsspec. inv H. destr; auto.
  rewrite ma_bs0. destr.
-
  unfold Mem.free in H0; repeat destr_in H0; inv H0.
  unfold Mem.free in FREE; repeat destr_in FREE; inv FREE.
  simpl. inv H; auto.
-
  unfold Mem.free in H0; repeat destr_in H0; inv H0.
  unfold Mem.free in FREE; repeat destr_in FREE; inv FREE.
  simpl. inv H; auto.

-  (* contents *)
  rewrite (Mem.free_result _ _ _ _ _ H0).
  rewrite (Mem.free_result _ _ _ _ _ FREE). 
  simpl. eapply ma_memval; eauto.
  eapply Mem.perm_free_3; eauto.
  apply H1.  auto.
  des (peq b0 b). right. intro.
  eapply Mem.perm_free_2 in H2; eauto.
- (* nextblock *)
  rewrite (Mem.free_result _ _ _ _ _ H0).
  rewrite (Mem.free_result _ _ _ _ _ FREE).
  simpl. eapply ma_nextblock; eauto.
- (* nextblock *)
  rewrite <- (Mem.nb_extra_free _ _ _ _ _ H0).
  rewrite <- (Mem.nb_extra_free _ _ _ _ _ FREE).
  simpl. eapply ma_nb_extra; eauto.
Qed.

(** * Properties of the need environment *)

Lemma add_need_all_eagree:
  forall e e' r ne,
  eagree e e' (add_need_all r ne) -> eagree e e' ne.
Proof.
  intros; red; intros. generalize (H r0). unfold add_need_all. 
  rewrite NE.gsspec. destruct (peq r0 r); auto with na. 
Qed.

Lemma add_need_all_lessdef:
  forall e e' r ne,
  eagree e e' (add_need_all r ne) -> Val.lessdef e#r e'#r.
Proof.
  intros. generalize (H r); unfold add_need_all. 
  rewrite NE.gsspec, peq_true. auto with na.
Qed.

Lemma add_need_eagree:
  forall e e' r nv ne,
  eagree e e' (add_need r nv ne) -> eagree e e' ne.
Proof.
  intros; red; intros. generalize (H r0); unfold add_need.
  rewrite NE.gsspec. destruct (peq r0 r); auto.
  subst r0. intros. eapply nge_agree; eauto. apply nge_lub_r.
Qed.

Lemma add_need_vagree:
  forall e e' r nv ne,
  eagree e e' (add_need r nv ne) -> vagree e#r e'#r nv.
Proof.
  intros. generalize (H r); unfold add_need.
  rewrite NE.gsspec, peq_true. intros. eapply nge_agree; eauto. apply nge_lub_l.
Qed.

Lemma add_needs_all_eagree:
  forall rl e e' ne,
  eagree e e' (add_needs_all rl ne) -> eagree e e' ne.
Proof.
  induction rl; simpl; intros.
  auto.
  apply IHrl. eapply add_need_all_eagree; eauto. 
Qed.

Lemma add_needs_all_lessdef:
  forall rl e e' ne,
  eagree e e' (add_needs_all rl ne) -> Val.lessdef_list e##rl e'##rl.
Proof.
  induction rl; simpl; intros. 
  constructor.
  constructor. eapply add_need_all_lessdef; eauto. 
  eapply IHrl. eapply add_need_all_eagree; eauto. 
Qed.

Lemma add_needs_eagree:
  forall rl nvl e e' ne,
  eagree e e' (add_needs rl nvl ne) -> eagree e e' ne.
Proof.
  induction rl; simpl; intros.
  auto.
  destruct nvl. apply add_needs_all_eagree with (a :: rl); auto.
  eapply IHrl. eapply add_need_eagree; eauto. 
Qed.

Lemma add_needs_vagree:
  forall rl nvl e e' ne,
  eagree e e' (add_needs rl nvl ne) -> vagree_list e##rl e'##rl nvl.
Proof.
  induction rl; simpl; intros.
  constructor.
  destruct nvl.
  apply vagree_lessdef_list. eapply add_needs_all_lessdef with (rl := a :: rl); eauto.
  constructor. eapply add_need_vagree; eauto. 
  eapply IHrl. eapply add_need_eagree; eauto. 
Qed.

Lemma add_ros_need_eagree:
  forall e e' ros ne, eagree e e' (add_ros_need_all ros ne) -> eagree e e' ne.
Proof.
  intros. destruct ros; simpl in *. eapply add_need_all_eagree; eauto. auto. 
Qed.

Hint Resolve add_need_all_eagree add_need_all_lessdef
             add_need_eagree add_need_vagree
             add_needs_all_eagree add_needs_all_lessdef
             add_needs_eagree add_needs_vagree
             add_ros_need_eagree: na.

Lemma eagree_init_regs:
  forall rl vl1 vl2 ne,
  Val.lessdef_list vl1 vl2 ->  
  eagree (init_regs vl1 rl) (init_regs vl2 rl) ne.
Proof.
  induction rl; intros until ne; intros LD; simpl.
- red; auto with na.
- inv LD. 
  + red; auto with na. 
  + apply eagree_update; auto with na.
Qed.

(** * Basic properties of the translation *)

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: transf_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Let rm := romem_for_program prog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intro. unfold ge, tge.
  apply Genv.find_symbol_transf_partial with (transf_fundef rm).
  exact TRANSF.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intro. unfold ge, tge.
  apply Genv.find_var_info_transf_partial with (transf_fundef rm).
  exact TRANSF.
Qed.

Lemma functions_translated:
  forall m (v: expr_sym) (f: RTL.fundef),
  Genv.find_funct m ge v = Some f ->
  exists tf,
  Genv.find_funct m tge v = Some tf /\ transf_fundef rm f = OK tf.
Proof (Genv.find_funct_transf_partial (transf_fundef rm) _ TRANSF).

Lemma function_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef rm f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial (transf_fundef rm) _ TRANSF).

Lemma sig_function_translated:
  forall f tf,
  transf_fundef rm f = OK tf ->
  funsig tf = funsig f.
Proof.
  intros; destruct f; monadInv H.
  unfold transf_function in EQ. 
  destruct (analyze (vanalyze rm f) f); inv EQ; auto. 
  auto.
Qed.

Lemma stacksize_translated:
  forall f tf,
  transf_function rm f = OK tf -> tf.(fn_stacksize) = f.(fn_stacksize).
Proof.
  unfold transf_function; intros. destruct (analyze (vanalyze rm f) f); inv H; auto.
Qed.

Lemma transf_function_at:
  forall f tf an pc instr,
  transf_function rm f = OK tf ->
  analyze (vanalyze rm f) f = Some an ->
  f.(fn_code)!pc = Some instr ->
  tf.(fn_code)!pc = Some(transf_instr (vanalyze rm f) an pc instr).
Proof.
  intros. unfold transf_function in H. rewrite H0 in H. inv H; simpl. 
  rewrite PTree.gmap. rewrite H1; auto. 
Qed.

Lemma is_dead_sound_1:
  forall nv, is_dead nv = true -> nv = Nothing.
Proof.
  destruct nv; simpl; congruence. 
Qed.

Lemma is_dead_sound_2:
  forall nv, is_dead nv = false -> nv <> Nothing.
Proof.
  intros; red; intros. subst nv; discriminate.
Qed.

Hint Resolve is_dead_sound_1 is_dead_sound_2: na.

Lemma is_int_zero_sound:
  forall nv, is_int_zero nv = true -> nv = I Int.zero.
Proof.
  unfold is_int_zero; destruct nv; try discriminate.
  predSpec Int.eq Int.eq_spec m Int.zero; congruence.
Qed.  

Lemma find_function_translated:
  forall m tm ros rs fd trs ne,
    find_function ge m ros rs = Some fd ->
    mem_lessdef m tm ->
  eagree rs trs (add_ros_need_all ros ne) ->
  exists tfd, find_function tge tm ros trs = Some tfd /\ transf_fundef rm fd = OK tfd.
Proof.
  intros. destruct ros as [r|id]; simpl in *.
- assert (LD: Val.lessdef rs#r trs#r) by eauto with na. 
  apply functions_translated; auto.
  eapply Genv.find_funct_lessdef; eauto.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try discriminate.
  apply function_ptr_translated; auto.
Qed.

(** * Semantic invariant *)

(* Definition extra_not_readable m l:= *)
(*   Forall (fun b => Mem.valid_block m b *)
(*                    /\ (forall ofs k, ~ Mem.perm m b ofs k Readable) *)
(*                    /\ ~ Mem.is_dynamic_block m b) l. *)

(* Lemma extra_not_readable_store: *)
(*   forall chunk m b ofs v m' l *)
(*          (ENR: extra_not_readable m l) *)
(*          (STORE: Mem.store chunk m b ofs v = Some m'), *)
(*     extra_not_readable m' l. *)
(* Proof. *)
(*   intros. revert ENR. *)
(*   unfold extra_not_readable. *)
(*   apply Forall_impl. *)
(*   intros a [VB [NP NDYN]]; repSplit. *)
(*   eapply Mem.store_valid_block_1; eauto. *)
(*   intros ofs0 k P. *)
(*   eapply NP. *)
(*   eapply Mem.perm_store_2; eauto. *)
(*   rewrite <- Genv.store_dyn; eauto. *)
(* Qed. *)

(* Lemma extra_not_readable_storev: *)
(*   forall chunk m addr v m' l *)
(*          (ENR: extra_not_readable m l) *)
(*          (STORE: Mem.storev chunk m addr v = Some m'), *)
(*     extra_not_readable m' l. *)
(* Proof. *)
(*   intros. *)
(*   unfold Mem.storev in STORE; destr_in STORE. *)
(*   eapply extra_not_readable_store; eauto. *)
(* Qed. *)

(* Lemma extra_not_readable_storebytes: *)
(*   forall m b ofs v m' l *)
(*          (ENR: extra_not_readable m l) *)
(*          (STORE: Mem.storebytes m b ofs v = Some m'), *)
(*     extra_not_readable m' l. *)
(* Proof. *)
(*   intros. revert ENR. *)
(*   unfold extra_not_readable. *)
(*   apply Forall_impl. *)
(*   intros a [VB [NP NDYN]]; repSplit. *)
(*   eapply Mem.storebytes_valid_block_1; eauto. *)
(*   intros ofs0 k P. *)
(*   eapply NP. *)
(*   eapply Mem.perm_storebytes_2; eauto. *)
(*   rewrite <- Mem.is_block_dynamic_storebytes; eauto. *)
(* Qed. *)

(* Lemma extra_not_readable_low_alloc: *)
(*   forall m lo hi al bt m' b *)
(*          (ALLOC: Mem.low_alloc m lo hi al bt = Some (m',b)) *)
(*          l *)
(*          (ENR: extra_not_readable m l), *)
(*     extra_not_readable m' l. *)
(* Proof. *)
(*   intros. *)
(*   revert ENR; apply Forall_impl. *)
(*   intros a [VB [NP NDYN]]; repSplit. *)
(*   unfold Mem.low_alloc in ALLOC. destr_in ALLOC. inv ALLOC. red; simpl. red in VB. xomega. *)
(*   intros ofs k P; eapply NP. *)
(*   rewrite Genv.low_alloc_perm. eauto. eauto. auto. *)
(*   unfold Mem.low_alloc, Mem.is_dynamic_block, Mem.valid_block in *. destr_in ALLOC. inv ALLOC. *)
(*   simpl in *. *)
(*   rewrite PMap.gsspec. destr. subst. xomega. *)
(* Qed. *)

(* Lemma extra_not_readable_alloc: *)
(*   forall m lo hi bt m' b *)
(*          (ALLOC: Mem.alloc m lo hi bt = Some (m',b)) *)
(*          l *)
(*          (ENR: extra_not_readable m l), *)
(*     extra_not_readable m' l. *)
(* Proof. *)
(*   intros. *)
(*   Transparent Mem.alloc. unfold Mem.alloc in ALLOC. *)
(*   eapply extra_not_readable_low_alloc; eauto. *)
(* Qed. *)

(* Lemma extra_not_readable_alloc_bytes: *)
(*   forall n m m' l' l *)
(*          (AB: Mem.alloc_bytes m n = Some (m',l')) *)
(*          (ENR: extra_not_readable m l), *)
(*     extra_not_readable m' l. *)
(* Proof. *)
(*   induction n; simpl; intros; eauto. inv AB; auto. *)
(*   repeat destr_in AB; inv AB. *)
(*   inv ENR. constructor. *)
(*   destruct H as [VB [NPERM NDYN]]. *)
(*   constructor. *)
(*   - repSplit. *)
(*     + eapply Mem.drop_perm_valid_block_1. eauto. *)
(*       eapply Mem.storebytes_valid_block_1. eauto. *)
(*       eapply Mem.valid_block_alloc. eauto. *)
(*       eapply Mem.alloc_bytes_nextblock_ple in Heqo. red in VB |- *. xomega. *)
(*     + intros ofs k P. *)
(*       rewrite Mem.perm_drop_perm in P; eauto. *)
(*       destr_in P. destr_in P. inv P. apply Mem.zle_zlt_false in Heqb. *)
(*       eapply Mem.perm_storebytes_2 in P; eauto. *)
(*       eapply Mem.perm_alloc_3 in P; eauto. Psatz.lia. *)
(*       eapply Mem.perm_storebytes_2 in P; eauto. *)
(*       eapply Mem.perm_alloc_4 in P; eauto. *)
(*       eapply Mem.alloc_bytes_perm in P; eauto. apply NPERM in P. auto. *)
(*     + rewrite <- (Mem.is_block_dynamic_drop_perm _ _ _ _ _ _ Heqo2). *)
(*       rewrite <- (Mem.is_block_dynamic_storebytes _ _ _ _ _ Heqo1). *)
(*       rewrite <- (Mem.is_block_dynamic_alloc _ _ _ _ _ Heqo0). *)
(*       rewrite <- (Mem.is_block_dynamic_alloc_bytes _ _ _ _ Heqo). auto. *)
(*   - revert H0; apply Forall_impl. *)
(*     clear x VB NPERM NDYN. *)
(*     intros x [VB [NPERM NDYN]]. *)
(*     repSplit. *)
(*     + eapply Mem.drop_perm_valid_block_1. eauto. *)
(*       eapply Mem.storebytes_valid_block_1. eauto. *)
(*       eapply Mem.valid_block_alloc. eauto. *)
(*       eapply Mem.alloc_bytes_nextblock_ple in Heqo. red in VB |- *. xomega. *)
(*     + intros ofs k P. *)
(*       rewrite Mem.perm_drop_perm in P; eauto. *)
(*       destr_in P. destr_in P. inv P. apply Mem.zle_zlt_false in Heqb. *)
(*       eapply Mem.perm_storebytes_2 in P; eauto. *)
(*       eapply Mem.perm_alloc_3 in P; eauto. Psatz.lia. *)
(*       eapply Mem.perm_storebytes_2 in P; eauto. *)
(*       eapply Mem.perm_alloc_4 in P; eauto. *)
(*       eapply Mem.alloc_bytes_perm in P; eauto. apply NPERM in P. auto. *)
(*     + rewrite <- (Mem.is_block_dynamic_drop_perm _ _ _ _ _ _ Heqo2). *)
(*       rewrite <- (Mem.is_block_dynamic_storebytes _ _ _ _ _ Heqo1). *)
(*       rewrite <- (Mem.is_block_dynamic_alloc _ _ _ _ _ Heqo0). *)
(*       rewrite <- (Mem.is_block_dynamic_alloc_bytes _ _ _ _ Heqo). auto. *)
(* Qed. *)

(* Lemma extra_not_readable_unchecked_free: *)
(*   forall m b lo hi l *)
(*          (ENR: extra_not_readable m l), *)
(*     extra_not_readable (Mem.unchecked_free m b lo hi) l. *)
(* Proof. *)
(*   red; intros. *)
(*   red in ENR. *)
(*   eapply Forall_impl; eauto. *)
(*   intros a [VB [NP ND]]; repSplit. *)
(*   unfold Mem.unchecked_free; simpl. red; simpl. eauto. *)
(*   intros. intro P. eapply perm_unchecked_free in P. apply NP in P. auto. eauto. *)
(*   unfold Mem.is_dynamic_block, Mem.unchecked_free; simpl. auto. *)
(* Qed. *)

(* Lemma extra_not_readable_release: *)
(*   forall m  l m' n *)
(*     (REL: MemReserve.release_boxes m n = Some m') *)
(*     (ENR: extra_not_readable m l), *)
(*     extra_not_readable m' l. *)
(* Proof. *)
(*   unfold MemReserve.release_boxes. intros. destr_in REL; inv REL. *)
(*   red. unfold Mem.valid_block, Mem.perm, Mem.is_dynamic_block.  simpl. eauto. *)
(* Qed. *)

(* Lemma extra_not_readable_reserve: *)
(*   forall m  l m' n *)
(*     (REL: MemReserve.reserve_boxes m n = Some m') *)
(*     (ENR: extra_not_readable m l), *)
(*     extra_not_readable m' l. *)
(* Proof. *)
(*   unfold MemReserve.reserve_boxes. intros. destr_in REL; inv REL. *)
(*   red. unfold Mem.valid_block, Mem.perm, Mem.is_dynamic_block.  simpl. eauto. *)
(* Qed. *)


(* Lemma extra_not_readable_free: *)
(*   forall m b lo hi m' l *)
(*          (FREE: Mem.free m b lo hi = Some m') *)
(*          (ENR: extra_not_readable m l), *)
(*     extra_not_readable m' l. *)
(* Proof. *)
(*   unfold Mem.free; intros. repeat destr_in FREE. inv FREE. *)
(*   eapply extra_not_readable_unchecked_free; eauto. *)
(* Qed. *)

(* Hint Resolve extra_not_readable_storebytes extra_not_readable_store *)
(*      extra_not_readable_storev *)
(*      extra_not_readable_low_alloc extra_not_readable_alloc *)
(*      extra_not_readable_alloc_bytes *)
(*      extra_not_readable_free *)
(*      extra_not_readable_unchecked_free *)
(*      extra_not_readable_reserve *)
(*      extra_not_readable_release *)
(* . *)

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  | match_stackframes_intro:
      forall res f sp pc e tf te an
        (FUN: transf_function rm f = OK tf)
        (ANL: analyze (vanalyze rm f) f = Some an)
        (RES: forall v tv,
              Val.lessdef v tv ->
              eagree (e#res <- v) (te#res<- tv)
                     (fst (transfer f (vanalyze rm f) pc an!!pc))),
      match_stackframes (Stackframe res f sp pc e)
                        (Stackframe res tf sp pc te).

Inductive match_states: state -> state -> Prop :=
  | match_regular_states:
      forall s f sp pc e m ts tf te tm an
        (STACKS: list_forall2 (match_stackframes) s ts)
        (FUN: transf_function rm f = OK tf)
        (ANL: analyze (vanalyze rm f) f = Some an)
        (ENV: eagree e te (fst (transfer f (vanalyze rm f) pc an!!pc)))
        (MEM: magree m tm (nlive ge sp (snd (transfer f (vanalyze rm f) pc an!!pc)))),
      match_states (State s f sp pc e m)
                   (State ts tf sp pc te tm)
  | match_call_states:
      forall s f args m ts tf targs tm
        (STACKS: list_forall2 (match_stackframes) s ts)
        (FUN: transf_fundef rm f = OK tf)
        (ARGS: Val.lessdef_list args targs)
        (MEM: mem_lessdef m tm),
      match_states (Callstate s f args m)
                   (Callstate ts tf targs tm)
  | match_return_states:
      forall s v m ts tv tm
        (STACKS: list_forall2 (match_stackframes) s ts)
        (RES: Val.lessdef v tv)
        (MEM: mem_lessdef m tm),
      match_states (Returnstate s v m)
                   (Returnstate ts tv tm).

(** [match_states] and CFG successors *)

Lemma analyze_successors:
  forall f an pc instr pc',
  analyze (vanalyze rm f) f = Some an ->
  f.(fn_code)!pc = Some instr ->
  In pc' (successors_instr instr) ->
  NA.ge an!!pc (transfer f (vanalyze rm f) pc' an!!pc').
Proof.
  intros. eapply DS.fixpoint_solution; eauto.
  intros. unfold transfer; rewrite H2. destruct a. apply DS.L.eq_refl.
Qed.

Lemma match_succ_states:
  forall s f sp pc e m ts tf te tm an pc' instr ne nm
    (STACKS: list_forall2 (match_stackframes) s ts)
    (FUN: transf_function rm f = OK tf)
    (ANL: analyze (vanalyze rm f) f = Some an)
    (INSTR: f.(fn_code)!pc = Some instr)
    (SUCC: In pc' (successors_instr instr))
    (ANPC: an!!pc = (ne, nm))
    (ENV: eagree e te ne)
    (MEM: magree m tm (nlive ge sp nm)),
  match_states (State s f sp pc' e m)
               (State ts tf sp pc' te tm).
Proof.
  intros. exploit analyze_successors; eauto. rewrite ANPC; simpl. intros [A B]. 
  econstructor; eauto. 
  eapply eagree_ge; eauto. 
  eapply magree_monotone; eauto. intros; apply B; auto.  
Qed.

(** Properties of volatile memory accesses *)

(*
Lemma transf_volatile_load:

  forall s f sp pc e m te r tm nm chunk t v m',

  volatile_load_sem chunk ge (addr :: nil) m t v m' ->
  Val.lessdef addr taddr ->
  genv_match bc ge ->
  bc sp = BCstack ->
  pmatch 

  sound_state prog (State s f (Vptr sp Int.zero) pc e m) ->
  Val.lessdef e#r te#r ->
  magree m tm
        (nlive ge sp
           (nmem_add nm (aaddr (vanalyze rm f) # pc r) (size_chunk chunk))) ->
  m' = m /\
  exists tv, volatile_load_sem chunk ge (te#r :: nil) tm t tv tm /\ Val.lessdef v tv.
Proof.
  intros. inv H2. split; auto. rewrite <- H3 in H0; inv H0. inv H4.
- (* volatile *)
  exists (Val.load_result chunk v0); split; auto. 
  constructor. constructor; auto. 
- (* not volatile *)
  exploit magree_load; eauto.
  exploit aaddr_sound; eauto. intros (bc & P & Q & R).
  intros. eapply nlive_add; eauto.
  intros (v' & P & Q).
  exists v'; split. constructor. econstructor; eauto. auto.
Qed.
*)

Lemma compat_magree:
  forall P m m'
    (MR: magree m m' P)
    cm,
    Mem.compat_m m Mem.M32 cm <-> Mem.compat_m m' Mem.M32 cm.
Proof.
  intros. apply Mem.same_compat_bounds_mask.
  unfold Mem.bounds_of_block; intros; inv MR; rewrite ma_bs0; eauto.
  unfold Mem.nat_mask, Mem.mask; intros; inv MR; rewrite ma_bm0; eauto.
Qed.


Lemma is_norm_m_rel:
  forall P m m' e v
    (MR: magree m m' P),
    Mem.is_norm_m m e v <->
    Mem.is_norm_m m' e v.
Proof.
  intros.
  apply Mem.is_norm_m_same_compat.
  apply (compat_magree _ _ _ MR).
Qed.

Lemma magree_norm':
  forall P m m' e,
    magree m m' P ->
    Mem.mem_norm m e = Mem.mem_norm m' e.
Proof.
  intros P m m' e ME.
  generalize (Mem.norm_correct m e) (Mem.norm_correct m' e).
  intros A B.
  apply lessdef_antisym; apply Mem.norm_complete.
  rewrite <- is_norm_m_rel; eauto.
  rewrite is_norm_m_rel; eauto.
Qed.

Lemma magree_norm:
  forall P m m' e e',
    magree m m' P ->
    Val.lessdef e e' ->
    Values.Val.lessdef (Mem.mem_norm m e) (Mem.mem_norm m' e').
Proof.
  intros.
  rewrite (magree_norm' _ _ _ _ H).
  generalize (wf_mr_norm_ld m' _ _ H0).
  intros; rewrite <- lessdef_val; auto.
Qed.

Lemma magree_in_bound:
  forall P m m',
    magree m m' P ->
    forall b ofs,
      Mem.in_bound_m ofs m b <-> Mem.in_bound_m ofs m' b.
Proof.
  intros.
  unfold Mem.in_bound_m, Mem.bounds_of_block.
  inv H. rewrite ma_bs0. tauto.
Qed.

Lemma transf_volatile_store:
  forall v1 v2 v1' v2' m tm chunk sp nm t v m',
  volatile_store_sem chunk ge (v1::v2::nil) m t v m' ->
  Val.lessdef v1 v1' ->
  vagree v2 v2' (store_argument chunk) ->
  magree m tm (nlive ge sp nm) ->
  v = Eval Vundef /\
  exists tm', volatile_store_sem chunk ge (v1'::v2'::nil) tm t (Eval Vundef) tm'
           /\ magree m' tm' (nlive ge sp nm).
Proof.
  intros. inv H. split; auto.
  inv VOLSTORE.
  - (* volatile *)
    exists tm; split; auto. econstructor. econstructor; eauto.
    exploit magree_norm; eauto. rewrite MN; intro A; inv A. auto.
    rewrite <- magree_in_bound; eauto.

    eapply eventval_match_lessdef; eauto.
    eapply magree_norm. eauto.
    apply store_argument_load_result; auto.

  - (* not volatile *)
    exploit magree_store_parallel. eauto. eauto. eauto.
    instantiate (1 := nlive ge sp nm). auto. 
    intros (tm' & P & Q).
    exists tm'; split. econstructor. econstructor; eauto. 2: auto.
    exploit magree_norm. apply H2. apply H0. rewrite MN; intro A; inv A. auto.
Qed.

Lemma vagree_vundef:
  forall x nv,
    vagree (Eval Vundef) x nv.
Proof.
  des nv; ldt.
Qed.

Lemma eagree_set_undef:
  forall e1 e2 ne r, eagree e1 e2 ne -> eagree (e1#r <- (Eval Vundef)) e2 ne.
Proof.
  intros; red; intros. rewrite PMap.gsspec. destruct (peq r0 r); auto with na.
  apply vagree_vundef.
Qed.

(** * The simulation diagram *)

Variable ns : ident -> nat.

Lemma aaddressing_sound:
  forall prog s f sp pc e m addr args b ofs sv,
  sound_state prog (State s f sp pc e m) ->
  eval_addressing (Genv.globalenv prog) (Eval (Vptr sp Int.zero)) addr e##args = Some sv ->
  Mem.mem_norm m sv = Vptr b ofs ->
  exists bc,
     pmatch bc b ofs (aaddressing (ValueAnalysis.analyze (romem_for_program prog) f)!!pc addr args)
  /\ genv_match bc (Genv.globalenv prog)
  /\ bc sp = BCstack.
Proof.
  intros. inv H. exists bc; split; auto. 
  unfold aaddressing. rewrite AN. eapply match_aptr_of_aval. 
  eapply ValueAOp.eval_static_addressing_sound; eauto with va.
  econstructor; eauto. red. reflexivity.
  eauto.
Qed.

Theorem step_simulation:
  forall S1 t S2, step ge ns S1 t S2 ->
  forall S1', match_states S1 S1' -> sound_state prog S1 ->
  exists S2', step tge ns S1' t S2' /\ match_states S2 S2'.
Proof.

Ltac TransfInstr :=
  match goal with
  | [INSTR: (fn_code _)!_ = Some _,
     FUN: transf_function _ _ = OK _,
     ANL: analyze _ _ = Some _ |- _ ] =>
       generalize (transf_function_at _ _ _ _ _ FUN ANL INSTR);
       intro TI;
       unfold transf_instr in TI
  end.

Ltac UseTransfer :=
  match goal with
  | [INSTR: (fn_code _)!?pc = Some _,
     ANL: analyze _ _ = Some ?an |- _ ] =>
       destruct (an!!pc) as [ne nm] eqn:ANPC;
       unfold transfer in *;
       rewrite INSTR in *;
       simpl in *
  end.

  induction 1; intros S1' MS SS; inv MS.

- (* nop *)
  TransfInstr; UseTransfer.
  econstructor; split.
  eapply exec_Inop; eauto. 
  eapply match_succ_states; eauto. simpl; auto.

- (* op *)
  TransfInstr; UseTransfer.
  destruct (is_dead (nreg ne res)) eqn:DEAD;
  [idtac|destruct (is_int_zero (nreg ne res)) eqn:INTZERO;
  [idtac|destruct (operation_is_redundant op (nreg ne res)) eqn:REDUNDANT]].
+ (* dead instruction, turned into a nop *)
  econstructor; split.
  eapply exec_Inop; eauto. 
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update_dead; auto with na. 
+ (* instruction with needs = [I Int.zero], turned into a load immediate of zero. *)
  econstructor; split.
  eapply exec_Iop with (v := Eval (Vint Int.zero)); eauto. 
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; auto. 
  rewrite is_int_zero_sound by auto.
  simpl. ldt.
  rewrite ! Int.and_zero. auto.
+ (* redundant operation *)
  destruct args.
  * (* kept as is because no arguments -- should never happen *)
  simpl in *. 
  exploit needs_of_operation_sound. (* eapply ma_perm; eauto.  *)
  eauto. instantiate (1 := nreg ne res). eauto with na. eauto with na. intros [tv [A B]].
  econstructor; split. 
  eapply exec_Iop with (v := tv); eauto.
  rewrite <- A. apply eval_operation_preserved. exact symbols_preserved.
  eapply match_succ_states; eauto. simpl; auto. 
  apply eagree_update; auto.
  * (* turned into a move *)
  unfold fst in ENV. unfold snd in MEM. simpl in H0.
  assert (VA: vagree v te#r (nreg ne res)).
  { eapply operation_is_redundant_sound with (arg1' := te#r) (args' := te##args).
    eauto. eauto. exploit add_needs_vagree; eauto. }
  econstructor; split.
  eapply exec_Iop; eauto. simpl; reflexivity. 
  eapply match_succ_states; eauto. simpl; auto. 
  eapply eagree_update; eauto 2 with na. 
+ (* preserved operation *)
  simpl in *.
  exploit needs_of_operation_sound. (* eapply ma_perm; eauto.  *)
  eauto. eauto 2 with na. eauto with na.
  intros [tv [A B]].
  econstructor; split. 
  eapply exec_Iop with (v := tv); eauto.
  rewrite <- A. apply eval_operation_preserved. exact symbols_preserved.
  eapply match_succ_states; eauto. simpl; auto. 
  apply eagree_update; eauto 2 with na.

- (* load *)
  TransfInstr; UseTransfer.
  destruct (is_dead (nreg ne dst)) eqn:DEAD;
  [idtac|destruct (is_int_zero (nreg ne dst)) eqn:INTZERO];
  simpl in *.
+ (* dead instruction, turned into a nop *)
  econstructor; split.
  eapply exec_Inop; eauto. 
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update_dead; auto with na. 
+ (* instruction with needs = [I Int.zero], turned into a load immediate of zero. *)
  econstructor; split.
  eapply exec_Iop with (v := Eval (Vint Int.zero)); eauto. 
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; auto. 
  rewrite is_int_zero_sound by auto.
  simpl; ldt. rewrite ! Int.and_zero; auto.
+ (* preserved *)
  exploit eval_addressing_rel. apply wf_mr_ld.
  apply Val.lessdef_list_inv.
  eapply add_needs_all_lessdef; eauto. eauto.
  intros (ta & U & V).
  (* destruct ta; simpl in H1; try discriminate. *)
  unfold Mem.loadv in H1; destr_in H1; inv H1.
  exploit magree_load; eauto. 
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. eapply nlive_add. eauto. assumption. eauto. auto.
  intros (tv & P & Q).
  econstructor; split.
  eapply exec_Iload with (a := ta). eauto. 
  rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved.
  unfold Mem.loadv.
  exploit magree_norm. apply MEM. apply V. rewrite Heqv0. intro A; inv A. eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 2 with na. 
  eapply magree_monotone; eauto. intros. apply incl_nmem_add; auto. 

- (* store *)
  TransfInstr; UseTransfer.
  destruct (nmem_contains nm (aaddressing (vanalyze rm f) # pc addr args)
             (size_chunk chunk)) eqn:CONTAINS.
+ (* preserved *)
  simpl in *. 
  exploit eval_addressing_rel. apply wf_mr_ld.
  apply Val.lessdef_list_inv. eapply add_needs_all_lessdef; eauto. eauto. 
  intros (ta & U & V).
  unfold Mem.storev in H1. destr_in H1. inv H1.
  exploit magree_store_parallel. eauto. eauto. instantiate (1 := te#src). eauto with na.
  instantiate (1 := nlive ge sp nm). 
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. apply nlive_remove with bc b i; assumption. 
  intros (tm' & P & Q).
  econstructor; split.
  eapply exec_Istore with (a := ta). eauto. 
  rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved.
  unfold Mem.storev. exploit magree_norm. apply MEM. apply V.
  rewrite Heqv; intro A; inv A. eauto.
  eapply match_succ_states; eauto. simpl; auto. 
  eauto 3 with na. 
+ (* dead instruction, turned into a nop *)
  econstructor; split.
  eapply exec_Inop; eauto. 
  eapply match_succ_states; eauto.  simpl; auto.
  unfold Mem.storev in H1; destr_in H1; inv H1.
  eapply magree_store_left; eauto.
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. eapply nlive_contains; eauto. 

- (* call *)
  TransfInstr; UseTransfer.
  exploit find_function_translated; eauto 2 with na.
  eapply magree_extends; eauto.
  apply nlive_all.
  intros (tfd & A & B).
  econstructor; split.
  eapply exec_Icall; eauto. apply sig_function_translated; auto. 
  constructor. 
  constructor; auto. econstructor; eauto. 
  intros.
  edestruct analyze_successors; eauto. simpl; eauto. 
  eapply eagree_ge; eauto. rewrite ANPC. simpl. 
  apply eagree_update; eauto with na.
  auto. eauto 2 with na. eapply magree_extends; eauto. apply nlive_all. 

- (* tailcall *)
  TransfInstr; UseTransfer.
  exploit magree_free. eauto. eauto. instantiate (1 := nlive ge stk nmem_all). 
  intros; eapply nlive_dead_stack; eauto.
  intros (tm' & C & D).
  exploit magree_unchecked_free. 2: apply D. eauto. intros (m2' & E & F).
  exploit find_function_translated; eauto 2 with na.
  eapply magree_extends; eauto.
  apply nlive_all.
  intros (tfd & A & B).
  econstructor; split.
  eapply exec_Itailcall; eauto. apply sig_function_translated; auto. 
  erewrite stacksize_translated by eauto. eexact C.
  unfold transf_function in FUN; destr_in FUN; inv FUN. simpl; eauto.
  constructor; eauto 2 with na.
  eapply magree_extends; eauto. apply nlive_all.

- (* builtin *)
  TransfInstr; UseTransfer. revert ENV MEM TI. 
  functional induction (transfer_builtin (vanalyze rm f)#pc ef args res ne nm);
  simpl in *; intros.
+ (* volatile load *)
  assert (LD: Val.lessdef rs#a1 te#a1) by eauto 2 with na.
  inv H0. (* rewrite <- H1 in LD; inv LD. *)
  assert (X: exists tv, volatile_load ge chunk tm te#a1 t tv /\ Val.lessdef v tv).
  {
    inv VOLLOAD. 
    * exists (Val.load_result chunk (Eval v0)); split; auto. econstructor; eauto.
      exploit magree_norm. apply MEM.
      eapply add_need_all_lessdef. apply ENV. rewrite MN. intro A; inv A. auto.
      rewrite <- magree_in_bound; eauto.
    * exploit magree_load; eauto. 
    +

Lemma aaddr_sound:
  forall prog s f sp pc e m r b ofs,
  sound_state prog (State s f sp pc e m) ->
  Mem.mem_norm m e#r = Vptr b ofs ->
  exists bc,
     pmatch bc b ofs (aaddr (ValueAnalysis.analyze (romem_for_program prog) f)!!pc r)
  /\ genv_match bc (Genv.globalenv prog)
  /\ bc sp = BCstack.
Proof.
  intros. inv H. exists bc; split; auto.
  unfold aaddr; rewrite AN. eapply match_aptr_of_aval. apply EM.
  rewrite <- H0. eauto. 
Qed. 

exploit aaddr_sound; eauto. intros (bc & A & B & C).
    intros. eapply nlive_add; eassumption. 
    + intros (tv & P & Q). 
      exists tv; split; auto. econstructor; eauto.
      exploit magree_norm. apply MEM.
      eapply add_need_all_lessdef. apply ENV. rewrite MN. intro A; inv A. auto.
  }
  destruct X as (tv & A & B).
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved.
  simpl. constructor. eauto.   
  exact symbols_preserved. exact varinfo_preserved.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 2 with na.
  eapply magree_monotone; eauto. intros. apply incl_nmem_add; auto. 
+ (* volatile global load *)
  inv H0. 
  assert (X: exists tv, volatile_load ge chunk tm (Eval (Vptr b ofs)) t tv /\ Val.lessdef v tv).
  {
    inv VOLLOAD. 
    * exists (Val.load_result chunk (Eval v0)); split; auto. econstructor; eauto.
      rewrite Mem.norm_val in *; auto.
      rewrite <- magree_in_bound; eauto.
    * exploit magree_load; eauto.
      inv SS. intros. eapply nlive_add; eauto. rewrite Mem.norm_val in MN; inv MN.
      constructor. apply GE. auto.
      intros (tv & P & Q). 
      exists tv; split; auto. econstructor; eauto.
      rewrite Mem.norm_val in *; auto.
  }
  destruct X as (tv & A & B).
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved.
  simpl. econstructor; eauto.   
  exact symbols_preserved. exact varinfo_preserved.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 2 with na.
  eapply magree_monotone; eauto. intros. apply incl_nmem_add; auto. 
+ (* volatile store *)
  exploit transf_volatile_store. eauto. 
  instantiate (1 := te#a1). eauto 3 with na.
  instantiate (1 := te#a2). eauto 3 with na. 
  eauto.
  intros (EQ & tm' & A & B). subst v. 
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved. simpl; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
  eapply match_succ_states; eauto. simpl; auto. 
  apply eagree_update; eauto 3 with na.
+ (* volatile global store *)
  rewrite volatile_store_global_charact in H0. destruct H0 as (b & P & Q).
  exploit transf_volatile_store. eauto. eauto. 
  instantiate (1 := te#a1). eauto 2 with na. 
  eauto.
  intros (EQ & tm' & A & B). subst v. 
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved. simpl. 
  rewrite volatile_store_global_charact. exists b; split; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
  eapply match_succ_states; eauto. 
  intros. simpl; auto. 
  apply eagree_update; eauto 2 with na.
+ (* memcpy *)
  rewrite e1 in TI.
  inv H0. 
  set (adst := aaddr (vanalyze rm f) # pc dst) in *.
  set (asrc := aaddr (vanalyze rm f) # pc src) in *.
  exploit magree_loadbytes. eauto. eauto. 
  exploit aaddr_sound. eauto. apply MNv.
  intros (bc & A & B & C).
  intros. eapply nlive_add; eassumption. 
  intros (tbytes & P & Q).
  exploit magree_storebytes_parallel.
  eapply magree_monotone. eexact MEM. 
  instantiate (1 := nlive ge sp (nmem_remove nm adst sz)).
  intros. apply incl_nmem_add; auto.
  eauto. 
  instantiate (1 := nlive ge sp nm). 
  exploit aaddr_sound. eauto. apply MNv'.
  intros (bc & A & B & C).
  intros. eapply nlive_remove; eauto.
  erewrite Mem.loadbytes_length in H1 by eauto. 
  rewrite nat_of_Z_eq in H1 by omega. auto.
  eauto. 
  intros (tm' & A & B).
  assert (LD1: Val.lessdef rs#src te#src) by eauto 3 with na.
  assert (LD2: Val.lessdef rs#dst te#dst) by eauto 3 with na. 
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved. simpl.
  econstructor.
  7: eauto. 7: eauto. auto. auto. auto. auto.
  auto. auto.
  exploit magree_norm. apply MEM. apply LD2. rewrite MNv'. intro X; inv X; auto.
  exploit magree_norm. apply MEM. apply LD1. rewrite MNv. intro X; inv X; auto.
  exact symbols_preserved. exact varinfo_preserved.
  eapply match_succ_states; eauto.
  simpl; auto.
  apply eagree_update; eauto 3 with na.
  {
    eexists; split; eauto.
    eapply exec_Ibuiltin; eauto.
    eapply external_call_symbols_preserved.  simpl. econstructor 2. auto.
    exact symbols_preserved. exact varinfo_preserved.
    eapply match_succ_states; eauto.
    simpl; auto.
    eapply eagree_update; eauto. apply vagree_same.
    eapply add_need_all_eagree; eauto.
    eapply add_need_all_eagree; eauto.
    eapply magree_monotone; eauto.
    intros.
    apply incl_nmem_add.
    inv H0. simpl.  destr; try constructor; auto. clear MEM.
    intros. destr_in H1. rewrite PTree.gsspec in H1. destr_in H1. inv H1.
    rewrite ISet.In_add. intros [A|A]. Psatz.lia. eapply GL in A; eauto.
    eapply GL; eauto.
    rewrite PTree.gsspec in H1. destr_in H1. inv H1.
    rewrite ISet.In_interval. Psatz.lia. eapply GL; eauto.
    intro; subst.
    rewrite ISet.In_add. intros [A|A]. Psatz.lia. apply STK in A; auto.
  }
+ (* memcpy eliminated *)
  rewrite e1 in TI. inv H0.
  set (adst := aaddr (vanalyze rm f) # pc dst) in *.
  set (asrc := aaddr (vanalyze rm f) # pc src) in *.
  econstructor; split.
  eapply exec_Inop; eauto. 
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_undef; auto.
  eapply magree_storebytes_left; eauto.
  exploit aaddr_sound. eauto. apply MNv'.
  intros (bc & A & B & C).
  intros. eapply nlive_contains; eauto.
  erewrite Mem.loadbytes_length in H0 by eauto. 
  rewrite nat_of_Z_eq in H0 by omega. auto.
  eexists; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_undef; auto.
 + (* annot *)
  inv H0. 
  econstructor; split. 
  eapply exec_Ibuiltin; eauto. 
  eapply external_call_symbols_preserved. simpl; constructor. 
  eapply eventval_list_match_lessdef; eauto 2 with na.

  Lemma ld_list_lf2:
    forall vl1 vl2,
      Values.Val.lessdef_list vl1 vl2 <-> list_forall2 Values.Val.lessdef vl1 vl2.
  Proof.
    red; split; induction 1; constructor; auto.
  Qed.
  
  rewrite ld_list_lf2.
  revert ENV. clear - MEM.
  induction _x; simpl; intros; eauto. constructor.
  constructor; auto.
  exploit magree_norm. eauto. 2: eauto. eapply add_need_all_lessdef; eauto.
  apply IH_x.
  eapply add_need_all_eagree; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 2 with na.
+ (* annot val *)  
  inv H0. destruct _x; inv H1. destruct _x; inv H4.
  econstructor; split. 
  eapply exec_Ibuiltin; eauto. 
  eapply external_call_symbols_preserved. simpl; constructor. 
  eapply eventval_match_lessdef; eauto 2 with na.
  eapply magree_norm; eauto. eapply add_need_all_lessdef. eauto.
  exact symbols_preserved. exact varinfo_preserved.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 3 with na.
+ (* all other builtins *)
  assert ((fn_code tf)!pc = Some(Ibuiltin _x _x0 res pc')).
  {
    destruct _x; auto. destruct _x0; auto. destruct _x0; auto. destruct _x0; auto. contradiction. 
  }
  clear y TI. 
  exploit external_call_mem_rel; eauto 2 with na.
  apply wf_mr_ld. apply wf_mr_norm_ld.
  eapply magree_extends; eauto. intros. apply nlive_all. 
  instantiate (1:= te ## _x0). revert ENV. clear - MEM.
  induction _x0; simpl; intros; eauto. constructor.
  constructor; auto.
  eapply add_need_all_lessdef; eauto.
  apply IH_x0. eapply add_need_all_eagree; eauto.
  intros (v' & tm' & A & B & C & D).
  econstructor; split.
  eapply exec_Ibuiltin; eauto. 
  eapply external_call_symbols_preserved. eauto.
  exact symbols_preserved. exact varinfo_preserved.
  eapply match_succ_states; eauto.
  simpl; auto.
  apply eagree_update; eauto 3 with na.
  eapply mextends_agree; eauto.
  
- (* conditional *)
  TransfInstr; UseTransfer.
  exploit needs_of_condition_sound; eauto. eapply add_needs_vagree; eauto.
  intros [b' [EC LD]].
  econstructor; split.
  eapply exec_Icond; eauto. 
  exploit magree_norm; eauto. rewrite H1; intro A; inv A; auto.
  eapply match_succ_states; eauto 2 with na. 
  destr; auto. 

- (* jumptable *)
  TransfInstr; UseTransfer.
  assert (LD: Val.lessdef rs#arg te#arg) by eauto 2 with na. 
  econstructor; split.
  eapply exec_Ijumptable; eauto. 
  exploit magree_norm; eauto. rewrite H0; intro A; inv A; auto.
  eapply match_succ_states; eauto 2 with na. 
  simpl. eapply list_nth_z_in; eauto. 

- (* return *)
  TransfInstr; UseTransfer.
  exploit magree_free. eauto. eauto. instantiate (1 := nlive ge stk nmem_all). 
  intros; eapply nlive_dead_stack; eauto. 
  intros (tm' & A & B).
  exploit magree_unchecked_free. 2: apply B. eauto. intros (m2' & REL & MAG).
  (* instantiate (1:= map (fun b => (b,0,8)) l). *)
  (* rewrite Forall_forall. intros x IN. *)
  (* rewrite in_map_iff in IN. dex; des IN. *)
  (* red in NREAD. rewrite Forall_forall in NREAD. apply NREAD in i. *)
  (* des i. des a. intros k o NP. *)
  (* eapply Mem.perm_free_3 in NP; eauto. apply n in NP; auto. *)
  (* intro MU. *)
  econstructor; split.
  eapply exec_Ireturn; eauto. 
  erewrite stacksize_translated by eauto. eexact A. unfold transf_function in FUN; destr_in FUN; inv FUN; eauto.
  constructor; auto.
  destruct or; simpl; eauto 2 with na.
  eapply magree_extends; eauto. apply nlive_all.

- (* internal function *)
  monadInv FUN. generalize EQ. unfold transf_function. intros EQ'.
  destruct (analyze (vanalyze rm f) f) as [an|] eqn:AN; inv EQ'.
  exploit alloc_mem_rel; eauto. apply wf_mr_ld.
  intros (tm' & A & B). 
  exploit MemReserve.reserve_boxes_rel; eauto.
  intros (tm'' & C & D).
  econstructor; split.
  econstructor; simpl; eauto. 
  simpl.
  econstructor; auto. eauto.
  apply eagree_init_regs; auto. 
  apply mextends_agree; auto. 

- (* external function *)
  (* exploit external_call_mem_extends; eauto. *)
  (* intros (res' & tm' & A & B & C & D & E).  *)
  (* simpl in FUN. inv FUN. *)
  (* econstructor; split. *)
  (* econstructor; eauto. *)
  (* eapply external_call_symbols_preserved; eauto.  *)
  (* exact symbols_preserved. exact varinfo_preserved. *)
  (* econstructor; eauto.  *)
  exploit external_call_mem_rel; eauto 2 with na.
  apply wf_mr_ld. apply wf_mr_norm_ld.
  (* eapply magree_extends; eauto. intros. apply nlive_all.  *)
  apply Val.lessdef_list_inv. eauto.
  intros (v' & tm' & A & B & C & D).
  econstructor; split.
  simpl in FUN. inv FUN. econstructor; eauto.
  eapply external_call_symbols_preserved. eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.

- (* return *)
  inv STACKS. inv H1. 
  econstructor; split.
  constructor. 
  econstructor; eauto. apply mextends_agree; auto. 
Qed.

Variable sg : ident -> Z.
Lemma transf_initial_states:
  forall st1, initial_state prog sg st1 ->
  exists st2, initial_state tprog sg st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intros (tf & A & B).
  exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
  eapply Genv.init_mem_transf_partial; eauto.
  intros. des a. unfold bind in H5. destr_in H5. inv H5. simpl.
  unfold transf_function in Heqr. destr_in Heqr. inv Heqr. reflexivity.
  inv H5. reflexivity.
  rewrite (transform_partial_program_main _ _ TRANSF).
  rewrite symbols_preserved. eauto.
  rewrite <- H3. apply sig_function_translated; auto.
  constructor. constructor. auto. constructor. apply mem_lessdef_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. constructor. 
  exploit magree_norm; eauto. eapply mextends_agree with (P := fun b ofs => True). eauto.
  rewrite H1; intro A; inv A; auto.
Qed.

(** * Semantic preservation *)

Hypothesis sg_pos:
  forall i, sg i > 0.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog ns sg) (RTL.semantics tprog ns sg).
Proof.
  intros.
  apply forward_simulation_step with
     (match_states := fun s1 s2 => sound_state prog s1 /\ match_states s1 s2).
- exact symbols_preserved.
- simpl; intros. exploit transf_initial_states; eauto. intros [st2 [A B]].
  exists st2; intuition. eapply sound_initial; eauto. 
- simpl; intros. destruct H. eapply transf_final_states; eauto.
- simpl; intros. destruct H0.
  assert (sound_state prog s1') by (eapply sound_step; eauto).
  fold ge; fold tge. exploit step_simulation; eauto. intros [st2' [A B]].
  exists st2'; auto. 
Qed.

End PRESERVATION.


