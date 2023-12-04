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

(** Correctness proof for the translation from Linear to Mach. *)

(** This file proves semantic preservation for the [Stacking] pass. *)

Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Op.
Require Import NormaliseSpec.
Require Import ExprEval.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Import LTL.
Require Import Linear.
Require Import Lineartyping.
Require Import Mach.
Require Import Bounds.
Require Import Conventions.
Require Import Stacklayout.
Require Import Stacking MemReserve.

Require Import Psatz.
Require Import PP.PpsimplZ.


Require Import Values_symbolictype.
Require Import Values_symbolic.
(* Require Import StackingInject. *)

(** * Properties of frame offsets *)

(* Simplifies the proof in a first step. *)
Axiom ma_3: MA = 3%nat.

Lemma typesize_typesize:
  forall ty, AST.typesize ty = 4 * Locations.typesize ty.
Proof.
  destruct ty; auto.
Qed.

Remark size_type_chunk:
  forall ty, size_chunk (chunk_of_type ty) = AST.typesize ty.
Proof.
  destruct ty; reflexivity.
Qed.

Section PRESERVATION.

Variable return_address_offset: Mach.function -> Mach.code -> int -> Prop.

Hypothesis return_address_offset_exists:
  forall f sg ros c,
  is_tail (Mcall sg ros :: c) (fn_code f) ->
  exists ofs, return_address_offset f c ofs.

Let step := Mach.step return_address_offset.

Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: transf_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Variable needed_stackspace : ident -> nat. 


Section FRAME_PROPERTIES.

Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable tf: Mach.function.
Hypothesis TRANSF_F: transf_function f = OK tf.

Hypothesis stackspace_ok:
  (Mem.box_span (Linear.fn_stacksize f) + needed_stackspace (Linear.fn_id f) =
   Mem.box_span (fe_size fe))%nat.

Lemma unfold_transf_function:
  tf = Mach.mkfunction
         f.(Linear.fn_id)
         f.(Linear.fn_sig)
         (transl_body f fe)
         (align (fe.(fe_size)) 8)
         (Int.repr fe.(fe_ofs_link))
         (Int.repr fe.(fe_ofs_retaddr))
         (Zle_trans _ _ _ (size_pos f) (align_le _ _ epos))
         (Z.to_nat (align (fe_size fe) 8 - Linear.fn_stacksize f)).
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb.
  destruct (zlt Int.max_unsigned (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros.
  unfold fe, b. congruence.
  discriminate.
Qed.

Lemma transf_function_well_typed:
  wt_function f = true.
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb. auto. intros; discriminate.
Qed.

Lemma size_no_overflow: fe.(fe_size) <= Int.max_unsigned.
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb.
  destruct (zlt Int.max_unsigned (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe. unfold b. omega.
  intros; discriminate.
Qed.

Remark bound_stack_data_stacksize:
  f.(Linear.fn_stacksize) <= b.(bound_stack_data).
Proof.
  unfold b, function_bounds, bound_stack_data. apply Zmax1.
Qed.  

(** A frame index is valid if it lies within the resource bounds
  of the current function. *)

Definition index_valid (idx: frame_index) :=
  match idx with
  | FI_link => True
  | FI_retaddr => True
  | FI_local x ty => ty <> AST.Tlong /\ 0 <= x /\ x + typesize ty <= b.(bound_local)
  | FI_arg x ty => ty <> AST.Tlong /\ 0 <= x /\ x + typesize ty <= b.(bound_outgoing)
  | FI_saved_int x => 0 <= x < b.(bound_int_callee_save)
  | FI_saved_float x => 0 <= x < b.(bound_float_callee_save)
  end.

Definition type_of_index (idx: frame_index) : typ :=
  match idx with
  | FI_link => AST.Tint
  | FI_retaddr => AST.Tint
  | FI_local x ty => ty
  | FI_arg x ty => ty
  | FI_saved_int x => Tany32
  | FI_saved_float x => Tany64
  end.

(** Non-overlap between the memory areas corresponding to two
  frame indices. *)

Definition index_diff (idx1 idx2: frame_index) : Prop :=
  match idx1, idx2 with
  | FI_link, FI_link => False
  | FI_retaddr, FI_retaddr => False
  | FI_local x1 ty1, FI_local x2 ty2 =>
      x1 + typesize ty1 <= x2 \/ x2 + typesize ty2 <= x1
  | FI_arg x1 ty1, FI_arg x2 ty2 =>
      x1 + typesize ty1 <= x2 \/ x2 + typesize ty2 <= x1
  | FI_saved_int x1, FI_saved_int x2 => x1 <> x2
  | FI_saved_float x1, FI_saved_float x2 => x1 <> x2
  | _, _ => True
  end.

Lemma index_diff_sym:
  forall idx1 idx2, index_diff idx1 idx2 -> index_diff idx2 idx1.
Proof.
  unfold index_diff; intros. 
  destruct idx1; destruct idx2; intuition.
Qed.

Ltac AddPosProps :=
  generalize (bound_local_pos b); intro;
  generalize (bound_int_callee_save_pos b); intro;
  generalize (bound_float_callee_save_pos b); intro;
  generalize (bound_outgoing_pos b); intro;
  generalize (bound_stack_data_pos b); intro.

Lemma size_pos: 0 <= fe.(fe_size).
Proof.
  generalize (frame_env_separated b). intuition.
  AddPosProps.
  unfold fe. omega.
Qed.

Opaque function_bounds.

Ltac InvIndexValid :=
  match goal with
  | [ H: ?ty <> AST.Tlong /\ _ |- _ ] =>
       destruct H; generalize (typesize_pos ty) (typesize_typesize ty); intros
  end.

Lemma offset_of_index_disj:
  forall idx1 idx2,
  index_valid idx1 -> index_valid idx2 ->
  index_diff idx1 idx2 ->
  offset_of_index fe idx1 + AST.typesize (type_of_index idx1) <= offset_of_index fe idx2 \/
  offset_of_index fe idx2 + AST.typesize (type_of_index idx2) <= offset_of_index fe idx1.
Proof.
  intros idx1 idx2 V1 V2 DIFF.
  generalize (frame_env_separated b). intuition. fold fe in H.
  AddPosProps. 
  destruct idx1; destruct idx2;
  simpl in V1; simpl in V2; repeat InvIndexValid; simpl in DIFF;
  unfold offset_of_index, type_of_index;
  change (AST.typesize Tany32) with 4; change (AST.typesize Tany64) with 8;
  change (AST.typesize AST.Tint) with 4;
  omega.
Qed.

Lemma offset_of_index_disj_stack_data_1:
  forall idx,
  index_valid idx ->
  offset_of_index fe idx + AST.typesize (type_of_index idx) <= fe.(fe_stack_data)
  \/ fe.(fe_stack_data) + b.(bound_stack_data) <= offset_of_index fe idx.
Proof.
  intros idx V.
  generalize (frame_env_separated b). intuition. fold fe in H.
  AddPosProps.
  destruct idx;
  simpl in V; repeat InvIndexValid;
  unfold offset_of_index, type_of_index;
  change (AST.typesize Tany32) with 4; change (AST.typesize Tany64) with 8;
  change (AST.typesize AST.Tint) with 4;
  omega.
Qed.

Lemma offset_of_index_disj_stack_data_2:
  forall idx,
  index_valid idx ->
  offset_of_index fe idx + AST.typesize (type_of_index idx) <= fe.(fe_stack_data)
  \/ fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= offset_of_index fe idx.
Proof.
  intros. 
  exploit offset_of_index_disj_stack_data_1; eauto.
  generalize bound_stack_data_stacksize. 
  omega.
Qed.

(** Alignment properties *)

Remark aligned_4_4x: forall x, (4 | 4 * x).
Proof. intro. exists x; ring. Qed.

Remark aligned_4_8x: forall x, (4 | 8 * x).
Proof. intro. exists (x * 2); ring. Qed.

Remark aligned_8_4:
  forall x, (8 | x) -> (4 | x).
Proof. intros. apply Zdivides_trans with 8; auto. exists 2; auto. Qed.

Hint Resolve Zdivide_0 Zdivide_refl Zdivide_plus_r 
             aligned_4_4x aligned_4_8x aligned_8_4: align_4.
Hint Extern 4 (?X | ?Y) => (exists (Y/X); reflexivity) : align_4.

Lemma offset_of_index_aligned:
  forall idx, (4 | offset_of_index fe idx).
Proof.
  intros.
  generalize (frame_env_aligned b). intuition. fold fe in H. intuition.
  destruct idx; try (destruct t);
  unfold offset_of_index, type_of_index, AST.typesize;
  auto with align_4.
Qed.

Lemma offset_of_index_aligned_2:
  forall idx, index_valid idx ->
  (align_chunk (chunk_of_type (type_of_index idx)) | offset_of_index fe idx).
Proof.
  intros. replace (align_chunk (chunk_of_type (type_of_index idx))) with 4.
  apply offset_of_index_aligned.
  assert (type_of_index idx <> AST.Tlong) by
    (destruct idx; simpl; simpl in H; intuition congruence).
  destruct (type_of_index idx); auto; congruence.
Qed.

Lemma fe_stack_data_aligned:
  (8 | fe_stack_data fe).
Proof.
  intros.
  generalize (frame_env_aligned b). intuition. fold fe in H. intuition.
Qed.

(** The following lemmas give sufficient conditions for indices
  of various kinds to be valid. *)

Lemma index_local_valid:
  forall ofs ty,
  slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
  index_valid (FI_local ofs ty).
Proof.
  unfold slot_within_bounds, slot_valid, index_valid; intros. 
  InvBooleans. 
  split. destruct ty; auto || discriminate. auto.
Qed.

Lemma index_arg_valid:
  forall ofs ty,
  slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
  index_valid (FI_arg ofs ty).
Proof.
  unfold slot_within_bounds, slot_valid, index_valid; intros. 
  InvBooleans. 
  split. destruct ty; auto || discriminate. auto. 
Qed.

Lemma index_saved_int_valid:
  forall r,
  In r int_callee_save_regs ->
  index_int_callee_save r < b.(bound_int_callee_save) ->
  index_valid (FI_saved_int (index_int_callee_save r)).
Proof.
  intros. red. split. 
  apply Zge_le. apply index_int_callee_save_pos; auto. 
  auto.
Qed.

Lemma index_saved_float_valid:
  forall r,
  In r float_callee_save_regs ->
  index_float_callee_save r < b.(bound_float_callee_save) ->
  index_valid (FI_saved_float (index_float_callee_save r)).
Proof.
  intros. red. split. 
  apply Zge_le. apply index_float_callee_save_pos; auto. 
  auto.
Qed.

Hint Resolve index_local_valid index_arg_valid
             index_saved_int_valid index_saved_float_valid: stacking.

(** The offset of a valid index lies within the bounds of the frame. *)

Lemma offset_of_index_valid:
  forall idx,
  index_valid idx ->
  0 <= offset_of_index fe idx /\
  offset_of_index fe idx + AST.typesize (type_of_index idx) <= fe.(fe_size).
Proof.
  intros idx V.
  generalize (frame_env_separated b). intros [A B]. fold fe in A. fold fe in B.
  AddPosProps.
  destruct idx; simpl in V; repeat InvIndexValid;
  unfold offset_of_index, type_of_index;
  change (AST.typesize Tany32) with 4; change (AST.typesize Tany64) with 8;
  change (AST.typesize AST.Tint) with 4;
  omega.
Qed.

(** The image of the Linear stack data block lies within the bounds of the frame. *)

Lemma stack_data_offset_valid:
  0 <= fe.(fe_stack_data) /\ fe.(fe_stack_data) + b.(bound_stack_data) <= fe.(fe_size).
Proof.
  generalize (frame_env_separated b). intros [A B]. fold fe in A. fold fe in B.
  AddPosProps.
  omega.
Qed.

(** Offsets for valid index are representable as signed machine integers
  without loss of precision. *)

Lemma offset_of_index_no_overflow:
  forall idx,
  index_valid idx ->
  Int.unsigned (Int.repr (offset_of_index fe idx)) = offset_of_index fe idx.
Proof.
  intros.
  generalize (offset_of_index_valid idx H). intros [A B].
  apply Int.unsigned_repr.
  generalize (AST.typesize_pos (type_of_index idx)).
  generalize size_no_overflow. 
  omega.
Qed.

(** Likewise, for offsets within the Linear stack slot, after shifting. *)

Lemma shifted_stack_offset_no_overflow:
  forall ofs,
  0 <= Int.unsigned ofs < Linear.fn_stacksize f ->
  Int.unsigned (Int.add ofs (Int.repr fe.(fe_stack_data))) 
  = Int.unsigned ofs + fe.(fe_stack_data).
Proof.
  intros. unfold Int.add.
  generalize size_no_overflow stack_data_offset_valid bound_stack_data_stacksize; intros.
  AddPosProps.
  replace (Int.unsigned (Int.repr (fe_stack_data fe))) with (fe_stack_data fe).
  apply Int.unsigned_repr. omega. 
  symmetry. apply Int.unsigned_repr. omega.
Qed.

(** * Contents of frame slots *)

Inductive index_contains (m: mem) (sp: block) (idx: frame_index) (v: expr_sym) : Prop :=
| index_contains_intro:
    forall v',
      index_valid idx ->
      Mem.load (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) = Some v' ->
      same_eval v' v ->
      index_contains m sp idx v.

Lemma depends_ptr:
  forall m b i,
    depends Int.max_unsigned (Mem.bounds_of_block m) (Mem.nat_mask m)
            (Eval (Vptr b i)) b.
Proof.
  clear; intros.
  red; intros; simpl.
  intro EQ.
  apply inj_vint in EQ.
  rewrite ! (Int.add_commut _ i) in EQ.
  apply int_add_eq_l in EQ; congruence.
Qed.

Lemma index_contains_load_stack:
  forall m sp idx v,
    index_contains m sp idx v ->
    exists v',
      load_stack m (Eval (Vptr sp Int.zero)) (type_of_index idx)
                 (Int.repr (offset_of_index fe idx)) = Some v' /\
      same_eval v' v.
Proof.
  intros. inv H. 
  unfold load_stack, Mem.loadv, Val.add.
  replace (Mem.mem_norm _ _ ) with (Vptr sp (Int.repr (offset_of_index fe idx))).
  - rewrite offset_of_index_no_overflow; auto.  rewrite H1.
    eexists; split; eauto. (* reflexivity. *)
  - symmetry. apply Mem.eq_norm; try constructor; red; simpl; try discriminate; intros.
    + rewrite Int.add_zero. auto.
Qed.

(** Good variable properties for [index_contains] *)

Lemma gss_index_contains_base:
  forall idx m m' sp v,
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  exists v',
     index_contains m' sp idx v'
  /\ decode_encode_expr_sym v (chunk_of_type (type_of_index idx)) (chunk_of_type (type_of_index idx)) v'.
Proof.
  intros. 
  exploit Mem.load_store_similar. eauto. reflexivity. omega. 
  intros [v' [A B]].
  exists v'; split; auto. econstructor; eauto.
  reflexivity.
Qed.



Lemma gss_index_contains_base_type:
  forall idx m m' sp v,
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  exists v',
     index_contains m' sp idx v'
     /\ decode_encode_expr_sym v (chunk_of_type (type_of_index idx)) (chunk_of_type (type_of_index idx)) v'. 
Proof.
  intros. 
  exploit Mem.load_store_similar. eauto. reflexivity. omega. 
  intros [v' [A B]].
  exists v'; split; auto. econstructor; eauto. reflexivity.
Qed.

Lemma gss_index_contains:
  forall idx m m' sp v,
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  index_contains m' sp idx (decode_encode (chunk_of_type (type_of_index idx)) v).
Proof.
  intros. exploit gss_index_contains_base; eauto. intros [v' [A B]].
  inv A.
  econstructor; eauto.
  rewrite (Mem.load_result _ _ _ _ _ H2).
  erewrite Mem.store_mem_contents; eauto.
  rewrite Maps.PMap.gss.
  replace (size_chunk_nat (chunk_of_type (type_of_index idx)))
          with (length (encode_val (chunk_of_type (type_of_index idx)) v)).
  rewrite Mem.getN_setN_same; auto. reflexivity.
  rewrite encode_val_length; auto.
Qed.


Lemma load_result_eSexpr_typ:
  forall v t,
    wt v t ->
    same_eval (Val.load_result (chunk_of_type t) v) v.
Proof.
  clear. red; intros.
  destruct H; dex; destr_and.
  - generalize (expr_type _ _ H0 alloc em); des t; des t'; seval;
    repeat match goal with
      H : context [if wt_expr_dec ?v ?t then _ else _] |- _ => revert H; destr
    end.
    rewrite Int.sign_ext_above; auto; vm_compute; destr.
    rewrite Int64.sign_ext_above; auto; vm_compute; destr.
  - generalize (nwt_expr_undef alloc em _ H).
    des t; rewrite H0; repeat destr.
Qed.


Lemma gss_index_contains':
  forall idx m m' sp v,
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  wt v (type_of_index idx) ->
  index_contains m' sp idx v.
Proof.
  intros. exploit gss_index_contains; eauto. intro A; inv A.
  econstructor; eauto.
  rewrite H4. 
  rewrite decode_encode_eSexpr.
  apply load_result_eSexpr_typ; auto.
Qed.

Lemma gso_index_contains:
  forall idx m m' sp v idx' v',
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  index_contains m sp idx' v' ->
  index_diff idx idx' ->
  index_contains m' sp idx' v'.
Proof.
  intros. inv H1. econstructor; eauto. 
  rewrite <- H4. eapply Mem.load_store_other; eauto.
  right. repeat rewrite size_type_chunk. 
  apply offset_of_index_disj; auto. apply index_diff_sym; auto.
Qed.

Lemma store_other_index_contains:
  forall chunk m blk ofs v' m' sp idx v,
  Mem.store chunk m blk ofs v' = Some m' ->
  blk <> sp \/
    (fe.(fe_stack_data) <= ofs /\ ofs + size_chunk chunk <= fe.(fe_stack_data) + f.(Linear.fn_stacksize)) ->
  index_contains m sp idx v ->
  index_contains m' sp idx v.
Proof.
  intros. inv H1. econstructor; eauto. rewrite <- H3. 
  eapply Mem.load_store_other; eauto. 
  destruct H0. auto. right. 
  exploit offset_of_index_disj_stack_data_2; eauto. intros.
  rewrite size_type_chunk.
  omega.
Qed.

Definition frame_perm_freeable (m: mem) (sp: block): Prop :=
  forall ofs,
  0 <= ofs < align (fe.(fe_size)) 8 ->
  ofs < fe.(fe_stack_data) \/ fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= ofs ->
  Mem.perm m sp ofs Cur Freeable.

Lemma offset_of_index_perm:
  forall m sp idx,
  index_valid idx ->
  frame_perm_freeable m sp ->
  Mem.range_perm m sp (offset_of_index fe idx) (offset_of_index fe idx + AST.typesize (type_of_index idx)) Cur Freeable.
Proof.
  intros.
  exploit offset_of_index_valid; eauto. intros [A B].
  exploit offset_of_index_disj_stack_data_2; eauto. intros.
  red; intros. apply H0.
  generalize B (align_le (fe_size fe) 8).
  generalize (fe_size fe).
  intros; lia. lia. 
Qed.

Lemma store_index_succeeds:
  forall m sp idx v,
  index_valid idx ->
  frame_perm_freeable m sp ->
  exists m',
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m'.
Proof.
  intros.
  destruct (Mem.valid_access_store m (chunk_of_type (type_of_index idx)) sp (offset_of_index fe idx) v) as [m' ST].
  constructor.
  rewrite size_type_chunk. 
  apply Mem.range_perm_implies with Freeable; auto with mem.
  apply offset_of_index_perm; auto.
  apply offset_of_index_aligned_2; auto.
  exists m'; auto.
Qed.

Lemma store_stack_succeeds:
  forall m sp idx v m',
  index_valid idx ->
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  store_stack m (Eval (Vptr sp Int.zero)) (type_of_index idx) (Int.repr (offset_of_index fe idx)) v = Some m'.
Proof.
  intros. unfold store_stack, Mem.storev, Val.add.
  replace (Mem.mem_norm _ _ ) with (Vptr sp (Int.repr (offset_of_index fe idx))).
  rewrite offset_of_index_no_overflow; auto.
  apply Mem.store_valid_access_3 in H0.
  apply Mem.valid_access_perm with (k:=Cur) in H0.
  eapply Mem.perm_bounds in H0.
  generalize (Mem.norm_complete
                m
                (Ebinop OpAdd Tint Tint (Eval (Vptr sp Int.zero))
                        (Eval (Vint (Int.repr (offset_of_index fe idx)))))
                (Vptr sp (Int.repr (offset_of_index fe idx)))).
  intro A; trim A.  
  - clear A. constructor; try red; simpl; intros; auto.
    + rewrite Int.add_zero. auto.
  - inv A; auto.
Qed.

(** A variant of [index_contains], up to a memory injection. *)

Definition index_contains_inj (j: meminj) (m: mem) (sp: block) (idx: frame_index) (v: expr_sym) : Prop :=
  exists v', index_contains m sp idx v' /\ expr_inj_se j v v'.

Lemma decode_encode_inj:
  forall f a b
    (EI: expr_inj_se f a b)
    chunk,
    expr_inj_se f (decode_encode chunk a) (decode_encode chunk b).
Proof.
  clear. intros.
  destruct wf_inj_expr_inj_se.
  destruct (expr_inj_se_get_type _ _ _ EI) as [A|A].
  apply wf_inj_undef.
  red; intros. rewrite decode_encode_eSexpr.
  des chunk; repeat destr; try erewrite A; eauto.
  erewrite A in Heqv; eauto. destr.
  des chunk; 
    repeat (apply ei_unop || apply ei_binop || eauto);
    rewrite  ! tolm_eq;
    rewrite (wt_gt _ _ A);
    destr;
    repeat (apply ei_unop || apply ei_binop || apply expr_inj_se_to_bits || eauto);
    apply wt_gt; auto.
Qed.


Lemma gss_index_contains_inj:
  forall j idx m m' sp v v'
    (STORE: Mem.store (chunk_of_type (type_of_index idx))
                      m sp (offset_of_index fe idx) v' = Some m')
    (IVLD: index_valid idx)
    (EI: expr_inj_se j v v'),
    index_contains_inj j m' sp idx (decode_encode (chunk_of_type (type_of_index idx)) v).
Proof.
  intros. exploit gss_index_contains_base_type; eauto. intros [v'' [A B ]].
  eexists; split; eauto.
  inv A.
  eapply expr_inj_se_se; eauto.
  rewrite (Mem.load_result _ _ _ _ _ H0).
  erewrite Mem.store_mem_contents; eauto.
  rewrite Maps.PMap.gss.
  replace (size_chunk_nat (chunk_of_type (type_of_index idx)))
  with (length (encode_val (chunk_of_type (type_of_index idx)) v'))
    by (rewrite encode_val_length; auto).
  rewrite Mem.getN_setN_same; auto.
  apply decode_encode_inj; eauto.
Qed.

Lemma index_contains_inj_se:
  forall j m sp idx v v',
    same_eval v v' ->
    index_contains_inj j m sp idx v ->
    index_contains_inj j m sp idx v'.
Proof.
  intros.
  destruct H0; repeat destr_and.
  exists x; split; auto.
  eapply expr_inj_se_l; eauto.
Qed.

Lemma gss_index_contains_inj':
  forall j idx m m' sp v v',
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v' = Some m' ->
  index_valid idx ->
  expr_inj_se j v v' ->
  index_contains_inj j m' sp idx (Val.load_result (chunk_of_type (type_of_index idx)) v).
Proof.
  intros.
  exploit gss_index_contains_inj; eauto.
  eapply index_contains_inj_se; eauto.
  apply decode_encode_eSexpr. 
Qed.

Lemma gso_index_contains_inj:
  forall j idx m m' sp v idx' v',
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  index_contains_inj j m sp idx' v' ->
  index_diff idx idx' ->
  index_contains_inj j m' sp idx' v'.
Proof.
  intros. destruct H1 as [v1 [A B]].
  red.
  exists v1; repSplit; auto.
  eapply gso_index_contains; eauto.
Qed.

Lemma store_other_index_contains_inj:
  forall j chunk m b ofs v' m' sp idx v,
  Mem.store chunk m b ofs v' = Some m' ->
  b <> sp \/
    (fe.(fe_stack_data) <= ofs /\ ofs + size_chunk chunk <= fe.(fe_stack_data) + f.(Linear.fn_stacksize)) ->
  index_contains_inj j m sp idx v ->
  index_contains_inj j m' sp idx v.
Proof.
  intros. destruct H1 as [v1 [A B]]. exists v1; repSplit; auto.
  eapply store_other_index_contains; eauto.
Qed.

Lemma index_contains_inj_incr:
  forall j m sp idx v j',
  index_contains_inj j m sp idx v ->
  inject_incr j j' ->
  index_contains_inj j' m sp idx v.
Proof.
  intros. destruct H as [v1 [A B]]. exists v1; repSplit; auto.
  eapply ei_inj_incr; eauto.
Qed.

Lemma index_contains_inj_undef:
  forall j m sp idx,
  index_valid idx ->
  frame_perm_freeable m sp ->
  index_contains_inj j m sp idx (Eval Vundef).
Proof.
  intros.
  exploit (Mem.valid_access_load m (chunk_of_type (type_of_index idx)) sp (offset_of_index fe idx)).
  constructor.
  rewrite size_type_chunk.
  apply Mem.range_perm_implies with Freeable; auto with mem.
  apply offset_of_index_perm; auto.
  apply offset_of_index_aligned_2; auto.
  intros [v C].
  red.
  exists v; repSplit; auto.
  econstructor; eauto. reflexivity.
  repeat eexists. constructor.
Qed.

Hint Resolve store_other_index_contains_inj index_contains_inj_incr: stacking.

(** * Agreement between location sets and Mach states *)

(** Agreement with Mach register states *)

Definition agree_regs (j: meminj) (ls: locset) (rs: regset) : Prop :=
  forall r, expr_inj_se j (ls (R r)) (rs r).

(** Agreement over data stored in memory *)

Definition in_frame_undefs m l :=
  (forall x,
      In x l ->
      forall ofs, 0 <= ofs < 8 ->
      exists n,
        Maps.ZMap.get ofs (Maps.PMap.get x (Mem.mem_contents m)) = Symbolic (Eval Vundef) None n).

Record agree_frame (j: meminj) (ls ls0: locset)
                   (m: mem) (sp: block)
                   (m': mem) (sp': block)
                   (parent retaddr: expr_sym) : Prop :=
  mk_agree_frame {

    (** Unused registers have the same value as in the caller *)
    agree_unused_reg:
       forall r, ~(mreg_within_bounds b r) -> ls (R r) = ls0 (R r);

    (** Local and outgoing stack slots (on the Linear side) have
        the same values as the one loaded from the current Mach frame 
        at the corresponding offsets. *)
    agree_locals:
      forall ofs ty, 
      slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
      index_contains_inj j m' sp' (FI_local ofs ty) (ls (S Local ofs ty));
    agree_outgoing:
      forall ofs ty, 
      slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
      index_contains_inj j m' sp' (FI_arg ofs ty) (ls (S Outgoing ofs ty));

    (** Incoming stack slots have the same value as the
        corresponding Outgoing stack slots in the caller *)
    agree_incoming:
       forall ofs ty, 
       In (S Incoming ofs ty) (loc_parameters f.(Linear.fn_sig)) ->
       ls (S Incoming ofs ty) = ls0 (S Outgoing ofs ty);

    (** The back link and return address slots of the Mach frame contain
        the [parent] and [retaddr] values, respectively. *)
    agree_link:
      index_contains m' sp' FI_link parent;
    agree_retaddr:
      index_contains m' sp' FI_retaddr retaddr;

    (** The areas of the frame reserved for saving used callee-save
        registers always contain the values that those registers had
        in the caller. *)
    agree_saved_int:
      forall r,
      In r int_callee_save_regs ->
      index_int_callee_save r < b.(bound_int_callee_save) ->
      index_contains_inj j m' sp' (FI_saved_int (index_int_callee_save r)) (ls0 (R r));
    agree_saved_float:
      forall r,
      In r float_callee_save_regs ->
      index_float_callee_save r < b.(bound_float_callee_save) ->
      index_contains_inj j m' sp' (FI_saved_float (index_float_callee_save r)) (ls0 (R r));

    (** Mapping between the Linear stack pointer and the Mach stack pointer *)
    agree_inj:
      j sp = Some(sp', fe.(fe_stack_data));
    agree_inj_cases: forall b delta, j b = Some (sp', delta) -> b = sp;
    (* agree_inj_in_undef: forall b delta, *)
    (*     j b = Some (sp', delta) -> *)
    (*     delta < fe_stack_data fe \/ fe_stack_data fe + Linear.fn_stacksize f <= delta -> *)

    (*     False *)
    (* ; *)
    
    (* agree_inj_data: forall b delta, j b = Some (sp', delta) -> *)
    (*                       fe_stack_data fe <= delta < *)
    (*                       fe_stack_data fe + Linear.fn_stacksize f -> *)
    (*                       b = sp; *)
    agree_sp_bounds: Mem.bounds_of_block m sp = (0, Linear.fn_stacksize f);
    agree_sp'_bounds: Mem.bounds_of_block m' sp' = (0, fn_stacksize tf);
    (** The Linear and Mach stack pointers are valid *)
    agree_valid_linear:
      Mem.valid_block m sp;
    agree_valid_mach:
      Mem.valid_block m' sp';
    agree_ndyn_sp: ~ Mem.is_dynamic_block m sp;
    agree_ndyn_sp': ~ Mem.is_dynamic_block m' sp';
    (* agree_extra_ndyn: Forall (fun b => ~ Mem.is_dynamic_block m b) l; *)
    (* agree_size_mem: *)
    (*   Mem.size_mem m - 8 * Z.of_nat (length l) - *)
    (*   align (Z.max 0 (Linear.fn_stacksize f)) 8 >= *)
    (*   Mem.size_mem m' - align (Z.max 0 (fn_stacksize tf)) 8; *)
    (** Bounds of the Linear stack data block *)
    agree_bounds:
      forall ofs p, Mem.perm m sp ofs Max p -> 0 <= ofs < f.(Linear.fn_stacksize);

    (** Permissions on the frame part of the Mach stack block *)
    agree_perm:
      frame_perm_freeable m' sp'
  }.

Lemma agree_inj_in_undef:
  forall j ls ls0 m sp m' sp' parent retaddr 
    (AGFR: agree_frame j ls ls0 m sp m' sp' parent retaddr)
    b delta
    (FB: j b = Some (sp', delta))
    (RNG: delta < fe_stack_data fe \/ fe_stack_data fe + Linear.fn_stacksize f <= delta)
    o k p
    (PERM: Mem.perm m b o k p),
    False.
Proof.
  intros. inv AGFR.
  exploit agree_inj_cases0. apply FB. intro; subst.
  Opaque fe_stack_data.
  rewrite agree_inj0 in FB. inv FB.
  destruct RNG. lia.
  eapply Mem.perm_max in PERM.
  apply agree_bounds0 in PERM. lia.
Qed.


Hint Resolve agree_unused_reg agree_locals agree_outgoing agree_incoming
             agree_link agree_retaddr agree_saved_int agree_saved_float
             agree_valid_linear agree_valid_mach agree_perm: stacking.

(** Auxiliary predicate used at call points *)

Definition agree_callee_save (ls ls0: locset) : Prop :=
  forall l,
  match l with
  | R r => ~In r destroyed_at_call
  | S _ _ _ => True
  end ->
  ls l = ls0 l.

(** ** Properties of [agree_regs]. *)

(** Values of registers *)


Lemma agree_reg:
  forall j ls rs r,
    agree_regs j ls rs ->
    expr_inj_se j (ls (R r)) (rs r).
Proof.
  intros. auto. 
Qed.


Lemma agree_reglist:
  forall j ls rs rl,
    agree_regs j ls rs ->
    expr_list_inject j (reglist ls rl) (rs##rl).
Proof.
  induction rl; simpl; intros.
  - constructor. 
  - specialize (IHrl H).
    eapply agree_reg in H.
    constructor; auto. eexact H.
Qed.

Hint Resolve agree_reg agree_reglist: stacking.

(** Preservation under assignments of machine registers. *)

Lemma agree_regs_set_reg:
  forall j ls rs r v v',
  agree_regs j ls rs ->
  expr_inj_se j v v' ->
  agree_regs j (Locmap.set (R r) v ls) (Regmap.set r v' rs).
Proof.
  intros; red; intros. 
  unfold Regmap.set. destruct (RegEq.eq r0 r). subst r0. 
  rewrite Locmap.gss; auto. 
  rewrite Locmap.gso; auto. red. auto.
Qed.

Lemma agree_regs_set_regs:
  forall j rl vl vl' ls rs,
  agree_regs j ls rs ->
  expr_list_inject j vl vl' ->
  agree_regs j (Locmap.setlist (map R rl) vl ls) (set_regs rl vl' rs).
Proof.
  induction rl; simpl; intros. 
  auto.
  inv H0. auto.
  apply IHrl; auto. apply agree_regs_set_reg; auto. 
Qed.

Lemma agree_regs_exten:
  forall j ls rs ls' rs',
  agree_regs j ls rs ->
  (forall r, ls' (R r) = Eval Vundef \/ ls' (R r) = ls (R r) /\ rs' r = rs r) ->
  agree_regs j ls' rs'.
Proof.
  intros; red; intros.
  destruct (H0 r) as [A|[ A B]]; rewrite A.
  apply expr_inj_se_vundef.
  rewrite B; auto.
Qed.

Lemma agree_regs_undef_regs:
  forall j rl ls rs,
  agree_regs j ls rs ->
  agree_regs j (LTL.undef_regs rl ls) (Mach.undef_regs rl rs).
Proof.
  induction rl; simpl; intros.
  auto. 
  apply agree_regs_set_reg; auto.
  apply expr_inj_se_vundef.
Qed.

(** Preservation under assignment of stack slot *)

Lemma agree_regs_set_slot:
  forall j ls rs sl ofs ty v,
  agree_regs j ls rs ->
  agree_regs j (Locmap.set (S sl ofs ty) v ls) rs.
Proof.
  intros; red; intros. rewrite Locmap.gso; auto. red. auto.
Qed.

(** Preservation by increasing memory injections *)

Lemma agree_regs_inject_incr:
  forall j ls rs j',
  agree_regs j ls rs -> inject_incr j j' -> agree_regs j' ls rs.
Proof.
  intros; red; intros.
  red in H.
  eapply ei_inj_incr; eauto.
Qed.

(** Preservation at function entry. *)

Lemma agree_regs_call_regs:
  forall j ls rs,
  agree_regs j ls rs ->
  agree_regs j (call_regs ls) rs.
Proof.
  intros.
  unfold call_regs; intros; red; intros; auto.
Qed.

(** ** Properties of [agree_frame] *)

(** Preservation under assignment of machine register. *)

Lemma agree_frame_set_reg:
  forall j ls ls0 m sp m' sp' parent ra r v,
  agree_frame j ls ls0 m sp m' sp' parent ra ->
  mreg_within_bounds b r ->
  agree_frame j (Locmap.set (R r) v ls) ls0 m sp m' sp' parent ra.
Proof.
  intros. inv H; constructor; auto; intros.
  rewrite Locmap.gso. auto. red. intuition congruence.
Qed.

Lemma agree_frame_set_regs:
  forall j ls0 m sp m' sp' parent ra rl vl ls,
  agree_frame j ls ls0 m sp m' sp' parent ra ->
  (forall r, In r rl -> mreg_within_bounds b r) ->
  agree_frame j (Locmap.setlist (map R rl) vl ls) ls0 m sp m' sp' parent ra.
Proof.
  induction rl; destruct vl; simpl; intros; intuition.
  apply IHrl; auto. 
  eapply agree_frame_set_reg; eauto. 
Qed.

Lemma agree_frame_undef_regs:
  forall j ls0 m sp m' sp' parent ra regs ls,
  agree_frame j ls ls0 m sp m' sp' parent ra ->
  (forall r, In r regs -> mreg_within_bounds b r) ->
  agree_frame j (LTL.undef_regs regs ls) ls0 m sp m' sp' parent ra.
Proof.
  induction regs; simpl; intros.
  auto.
  apply agree_frame_set_reg; auto.
Qed.

Lemma caller_save_reg_within_bounds:
  forall r,
  In r destroyed_at_call -> mreg_within_bounds b r.
Proof.
  intros. red.
  destruct (zlt (index_int_callee_save r) 0).
  destruct (zlt (index_float_callee_save r) 0).
  generalize (bound_int_callee_save_pos b) (bound_float_callee_save_pos b); omega.
  exfalso. eapply float_callee_save_not_destroyed; eauto. eapply index_float_callee_save_pos2; eauto.
  exfalso. eapply int_callee_save_not_destroyed; eauto. eapply index_int_callee_save_pos2; eauto.
Qed.

Lemma agree_frame_undef_locs:
  forall j ls0 m sp m' sp' parent ra regs ls,
  agree_frame j ls ls0 m sp m' sp' parent ra ->
  incl regs destroyed_at_call ->
  agree_frame j (LTL.undef_regs regs ls) ls0 m sp m' sp' parent ra.
Proof.
  intros. eapply agree_frame_undef_regs; eauto. 
  intros. apply caller_save_reg_within_bounds. auto. 
Qed.

(** Preservation by assignment to local slot *)

Lemma agree_frame_set_local:
  forall j ls ls0 m sp m' sp' parent retaddr ofs ty v v' m'',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
  expr_inj_se j v v' ->
  Mem.store (chunk_of_type ty) m' sp' (offset_of_index fe (FI_local ofs ty)) v' = Some m'' ->
  agree_frame j (Locmap.set (S Local ofs ty) v ls) ls0 m sp m'' sp' parent retaddr.
Proof.
  intros. inv H.
  change (chunk_of_type ty) with (chunk_of_type (type_of_index (FI_local ofs ty))) in H3.
  constructor; auto; intros.
  - (* local *) 
    unfold Locmap.set.
    destruct (Loc.eq (S Local ofs ty) (S Local ofs0 ty0)).
    + inv e. eapply gss_index_contains_inj'; eauto with stacking.
    + destruct (Loc.diff_dec (S Local ofs ty) (S Local ofs0 ty0)).
      * eapply gso_index_contains_inj. eauto. eauto with stacking. eauto.
        simpl. simpl in d. intuition.
      * apply index_contains_inj_undef. auto with stacking.
        red; intros. eapply Mem.perm_store_1; eauto.
  - (* outgoing *)
    rewrite Locmap.gso. eapply gso_index_contains_inj; eauto with stacking.
    red; auto. red; left; congruence.
  - (* parent *)
    eapply gso_index_contains; eauto with stacking. red; auto.
  - (* retaddr *)
    eapply gso_index_contains; eauto with stacking. red; auto.
  - (* int callee save *)
    eapply gso_index_contains_inj; eauto with stacking. simpl; auto.
  - (* float callee save *)
    eapply gso_index_contains_inj; eauto with stacking. simpl; auto.
  - erewrite <- Mem.bounds_of_block_store; eauto.
  - (* valid *)
    eauto with mem.
  - rewrite <- Genv.store_dyn; eauto.
  - (* perm *)
    red; intros. eapply Mem.perm_store_1; eauto.
Qed.

(** Preservation by assignment to outgoing slot *)

Lemma agree_frame_set_outgoing:
  forall j ls ls0 m sp m' sp' parent retaddr ofs ty v v' m'',
    agree_frame j ls ls0 m sp m' sp' parent retaddr ->
    slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
    expr_inj_se j v v' ->
    Mem.store (chunk_of_type ty) m' sp' (offset_of_index fe (FI_arg ofs ty)) v' = Some m'' ->
    agree_frame j (Locmap.set (S Outgoing ofs ty) v ls) ls0 m sp m'' sp' parent retaddr.
Proof.
  intros. inv H.
  change (chunk_of_type ty) with (chunk_of_type (type_of_index (FI_arg ofs ty))) in H3.
  constructor; auto; intros.
  - (* local *)
    rewrite Locmap.gso. eapply gso_index_contains_inj; eauto with stacking. red; auto.
    red; left; congruence.
  - (* outgoing *)
    unfold Locmap.set. destruct (Loc.eq (S Outgoing ofs ty) (S Outgoing ofs0 ty0)).
    inv e. eapply gss_index_contains_inj'; eauto with stacking.
    destruct (Loc.diff_dec (S Outgoing ofs ty) (S Outgoing ofs0 ty0)).
    eapply gso_index_contains_inj; eauto with stacking.
    red. red in d. intuition.
    apply index_contains_inj_undef. auto with stacking.
    red; intros. eapply Mem.perm_store_1; eauto.
  - (* parent *)
    eapply gso_index_contains; eauto with stacking. red; auto.
  - (* retaddr *)
    eapply gso_index_contains; eauto with stacking. red; auto.
  - (* int callee save *)
    eapply gso_index_contains_inj; eauto with stacking. simpl; auto.
  - (* float callee save *)
    eapply gso_index_contains_inj; eauto with stacking. simpl; auto.
  - erewrite <- Mem.bounds_of_block_store; eauto.
  - (* valid *)
    eauto with mem stacking.
  - rewrite <- Genv.store_dyn; eauto.
  - (* perm *)
    red; intros. eapply Mem.perm_store_1; eauto.
Qed.

(** General invariance property with respect to memory changes. *)

Require Import Tactics.

Lemma agree_frame_invariant:
  forall j ls ls0 m sp m' sp' parent retaddr m1 m1'
    (AGFR: agree_frame j ls ls0 m sp m' sp' parent retaddr)
    (Jvalid: forall b b' delta, j b = Some (b',delta) -> Mem.valid_block m b /\ Mem.valid_block m' b'
                                                   /\ (Mem.is_dynamic_block m b <->
                                                      Mem.is_dynamic_block m' b'))
    (PERM: forall b ofs k p, Mem.valid_block m b ->
                        ~ Mem.is_dynamic_block m b ->
                        (Mem.perm m1 b ofs k p <-> Mem.perm m b ofs k p))
    (BND: forall b, Mem.valid_block m b ->
               ~ Mem.is_dynamic_block m b ->
               Mem.bounds_of_block m1 b = Mem.bounds_of_block m b)
    (BND': forall b, Mem.valid_block m' b ->
               ~ Mem.is_dynamic_block m' b ->
               Mem.bounds_of_block m1' b = Mem.bounds_of_block m' b)
    (Nb: Ple (Mem.nextblock m) (Mem.nextblock m1))
    (Nb': Ple (Mem.nextblock m') (Mem.nextblock m1'))
    (LOAD: forall chunk ofs v,
        ofs + size_chunk chunk <= fe.(fe_stack_data) \/
        fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= ofs ->
        Mem.load chunk m' sp' ofs = Some v ->
        Mem.load chunk m1' sp' ofs = Some v)
    (PERM': forall ofs k p,
        ofs < fe.(fe_stack_data) \/ fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= ofs ->
        Mem.perm m' sp' ofs k p -> Mem.perm m1' sp' ofs k p)
    (DYN: forall b, Mem.valid_block m b -> (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m1 b))
    (DYN': forall b, Mem.valid_block m' b -> (Mem.is_dynamic_block m' b <-> Mem.is_dynamic_block m1' b))
  ,
  agree_frame j ls ls0 m1 sp m1' sp' parent retaddr.
Proof.
  intros.
  assert (IC: forall idx v,
              index_contains m' sp' idx v -> index_contains m1' sp' idx v).
  {
    intros idx v IC. inv IC.
    exploit offset_of_index_disj_stack_data_2; eauto. intros.
    econstructor; eauto. apply LOAD;auto. rewrite size_type_chunk. auto.
  }
  assert (ICI: forall idx v,
              index_contains_inj j m' sp' idx v -> index_contains_inj j m1' sp' idx v).
  {
    intros idx v ICC. destruct ICC as [v' [A B]]. exists v'; split; auto.
  }
  inv AGFR; constructor; auto; intros.
  (* - exfalso. eapply agree_inj_in_undef0. eauto. auto. *)
  (*   dex; exists o. unfold Mem.in_bound_m in *. rewrite <- BND. auto. *)
  (*   eapply Jvalid; eauto. *)
  (*   apply Jvalid in H. destruct H as [A [B C]]. rewrite C. auto.  *)
  (* - unfold Mem.valid_block in *. *)
  (*   revert agree_extra_valid0. apply Forall_impl. *)
  (*   intros; xomega. *)
  (* - red; intros. rewrite Forall_forall in same_contents_l. *)
  (*   specialize (same_contents_l _ H). *)
  (*   rewrite <- same_contents_l. *)
  (*   eauto. *)
  (* - revert agree_inj_bounds_extra0. apply Mem.Forall_impl'. *)
  (*   intros a IN. *)
  (*   rewrite BND. auto. *)
  (*   rewrite Forall_forall in agree_extra_valid0; eauto. *)
  (*   rewrite Forall_forall in agree_extra_ndyn0; eauto. *)
  (* - apply Forall_forall; intros. intro; dex. rewrite PERM in H0. *)
  (*   rewrite Forall_forall in agree_inj_extra_not_writable0. *)
  (*   apply agree_inj_extra_not_writable0 in H. apply H; exists o, k; auto. *)
  (*   rewrite Forall_forall in agree_extra_valid0; eauto. *)
  (*   rewrite Forall_forall in agree_extra_ndyn0; eauto. *)
  - rewrite <- agree_sp_bounds0. apply BND. auto. auto.
  - rewrite BND'; auto.
  - unfold Mem.valid_block in *. xomega. 
  - unfold Mem.valid_block in *. xomega.
  - rewrite <- DYN; auto.
  - rewrite <- DYN'; auto.
  (* - revert agree_extra_ndyn0. apply Mem.Forall_impl'. *)
  (*   intros. *)
  (*   rewrite <- DYN; auto. *)
  (*   rewrite Forall_forall in agree_extra_valid0; eauto. *)
  - rewrite  PERM in H; eauto.
  - red; intros; apply PERM'; auto.
Qed.

Opaque fe_stack_data.

Lemma agree_frame_store_inject:
  forall j ls ls0 m sp m' sp' parent retaddr
    (AGFR : agree_frame j ls ls0 m sp m' sp' parent retaddr)
    (ABI : Mem.all_blocks_injected j m)
    (MINJ : Mem.inject true expr_inj_se j m m')
    a e
    (EI : expr_inj_se j a e)
    b1 ofs1
    (MN : Mem.mem_norm m a = Vptr b1 ofs1)
    b0 ofs0
    (MN' : Mem.mem_norm m' e = Vptr b0 ofs0)
    chunk0 v1 v0 m1 m1'
    (STORE : Mem.store chunk0 m b1 (Int.unsigned ofs1) v1 = Some m1)
    (STORE' : Mem.store chunk0 m' b0 (Int.unsigned ofs0) v0 = Some m1')
    ofs chunk
    (DELTA : ofs + size_chunk chunk <= fe_stack_data fe \/
             fe_stack_data fe + Linear.fn_stacksize f <= ofs),
    Mem.load chunk m' sp' ofs = Mem.load chunk m1' sp' ofs.
Proof.
  intros.
  symmetry. eapply Mem.load_store_other; eauto.
  destruct (eq_block sp' b0); subst; auto.
  right.
  cut (fe_stack_data fe <= Int.unsigned ofs0 <= fe_stack_data fe - size_chunk chunk0 + Linear.fn_stacksize f). lia.
  generalize (Mem.norm_inject_val' _ _ wf_inj_expr_inj_se _ _ _ _ _ ABI MINJ EI).
  rewrite MN, MN'; intro A; inv A.
  eapply Mem.store_valid_access_3 in STORE. destruct STORE.
  exploit agree_inj_cases. eauto. eauto. intro; subst.
  erewrite agree_inj in FB; eauto. inv FB.
  generalize (size_chunk_pos chunk0); intro.
  apply Mem.range_perm_bounds' in H; [|lia].
  erewrite agree_sp_bounds in H; eauto.
  rewrite shifted_stack_offset_no_overflow; lia.
Qed.

Opaque fe_size.

Lemma agree_frame_storebytes_inject:
  forall j ls ls0 m sp m' sp' parent retaddr
    (AGFR : agree_frame j ls ls0 m sp m' sp' parent retaddr)
    (ABI : Mem.all_blocks_injected j m)
    (MINJ : Mem.inject true expr_inj_se j m m')
    a e
    (EI : expr_inj_se j a e)
    b1 ofs1
    (MN : Mem.mem_norm m a = Vptr b1 ofs1)
    b0 ofs0
    (MN' : Mem.mem_norm m' e = Vptr b0 ofs0)
    v1 v0 m1 m1'
    (LN: length v1 = length v0)
    (STORE : Mem.storebytes m b1 (Int.unsigned ofs1) v1 = Some m1)
    (STORE' : Mem.storebytes m' b0 (Int.unsigned ofs0) v0 = Some m1')
    ofs chunk
    (DELTA : ofs + size_chunk chunk <= fe_stack_data fe \/
             fe_stack_data fe + Linear.fn_stacksize f <= ofs),
    Mem.load chunk m' sp' ofs = Mem.load chunk m1' sp' ofs.
Proof.
  intros.
  destruct (zeq 0 (Z.of_nat (length v1))).
  {
    (* stupid 0 case *)
    destruct v1; simpl in *; try congruence.
    destruct v0; simpl in *; try congruence.
    Transparent Mem.storebytes Mem.load.
    unfold Mem.storebytes in STORE'. revert STORE'; destr_cond_match; try congruence.
    intro A; inv A.
    apply Mem.load_contents_access; simpl; intros; auto.
    rewrite Maps.PMap.gsspec.
    destr.
  }
  symmetry. eapply Mem.load_storebytes_other; eauto.
  destruct (eq_block sp' b0); subst; auto.
  right.
  cut (fe_stack_data fe <= Int.unsigned ofs0 <= fe_stack_data fe - Z.of_nat (length v0) + Linear.fn_stacksize f). lia.
  generalize (Mem.norm_inject_val' _ _ wf_inj_expr_inj_se _ _ _ _ _ 
                                   ABI MINJ EI).
  rewrite MN, MN'; intro A; inv A.
  eapply Mem.storebytes_range_perm in STORE.
  exploit agree_inj_cases. eauto. eauto. intro; subst.
  erewrite agree_inj in FB; eauto. inv FB.
  generalize (size_chunk_pos chunk); intro.
  apply Mem.range_perm_bounds' in STORE; [|lia].
  erewrite agree_sp_bounds in STORE; eauto.
  rewrite shifted_stack_offset_no_overflow; lia.
Qed.

(** Preservation by parallel stores in the Linear and Mach codes *)

Lemma agree_frame_parallel_stores:
  forall j ls ls0 m sp m' sp' parent retaddr chunk addr addr' v v' m1 m1',
    Mem.all_blocks_injected j m ->
    agree_frame j ls ls0 m sp m' sp' parent retaddr ->
    Mem.inject true expr_inj_se j m m' ->
    expr_inj_se j addr addr' ->
    Mem.storev chunk m addr v = Some m1 ->
    Mem.storev chunk m' addr' v' = Some m1' ->
    agree_frame j ls ls0 m1 sp m1' sp' parent retaddr.
Proof.
  Opaque Int.add.
  intros until m1'. intros ABI AG MINJ VINJ STORE1 STORE2.
  eapply agree_frame_invariant; eauto.
  - intros.
    exploit (Mem.mi_mappedblocks); eauto.
    destruct (Mem.valid_block_dec m b0); auto.
    exploit Mem.mi_inj_dynamic; eauto. destr.
    erewrite Mem.mi_freeblocks in H; eauto; destr.
  - intros. unfold Mem.storev in STORE1; destr_in STORE1.
    split; intros.
    eapply Mem.perm_store_2; eauto. eauto with mem.
  - intros.
    symmetry; eapply Mem.storev_bounds; eauto.
  - intros.
    symmetry; eapply Mem.storev_bounds; eauto.
  - erewrite  <- Mem.nextblock_storev; eauto. xomega.
  - erewrite  <- Mem.nextblock_storev; eauto. xomega.
  - intros. rewrite <- H0.
    unfold Mem.storev in STORE2; revert STORE2; destr_cond_match; try discriminate.
    unfold Mem.storev in STORE1; revert STORE1; destr_cond_match; try discriminate.
    generalize (Mem.norm_inject_val' _ _ wf_inj_expr_inj_se _ _ _ _ _ ABI MINJ VINJ).
    rewrite Heqv0, Heqv1. intro A; inv A. 
    intros.
    symmetry; eapply agree_frame_store_inject; eauto.
  - intros. unfold Mem.storev in STORE2; revert STORE2; destr_cond_match; try discriminate.
    eauto with mem.
  - unfold Mem.storev in STORE1; destr_in STORE1.
    intros; rewrite Genv.store_dyn; eauto. tauto.
  - unfold Mem.storev in STORE2; destr_in STORE2.
    intros; rewrite Genv.store_dyn; eauto. tauto.
Qed.

(** Preservation by increasing memory injections (allocations and external calls) *)

Lemma agree_frame_inject_incr:
  forall j ls ls0 m sp m' sp' parent retaddr m1 m1' j'
    (AGFR: agree_frame j ls ls0 m sp m' sp' parent retaddr)
    (INCR: inject_incr j j') (SEP: inject_separated j j' m1 m1')
    (VB: Mem.valid_block m1' sp')
    (P: forall b b' delta, j b = None -> j' b = Some (b',delta) -> b' <> sp'),
    agree_frame j' ls ls0 m sp m' sp' parent retaddr.
Proof.
  intros. inv AGFR. constructor; auto; intros; eauto with stacking.
  - eapply agree_inj_cases0.
    destruct (j b0) eqn:?. destruct p. eapply INCR in Heqo. rewrite H in Heqo; inv Heqo; eauto.
    eapply P in Heqo; eauto. congruence.
Qed.

Remark inject_alloc_separated:
  forall j m1 m2 j' b1 b2 delta,
  inject_incr j j' ->
  j' b1 = Some(b2, delta) ->
  (forall b, b <> b1 -> j' b = j b) ->
  ~Mem.valid_block m1 b1 -> ~Mem.valid_block m2 b2 ->
  inject_separated j j' m1 m2.
Proof.
  intros. red. intros.
  destruct (eq_block b0 b1). subst b0. rewrite H0 in H5; inv H5. tauto.
  rewrite H1 in H5. congruence. auto.
Qed.

(** Preservation at return points (when [ls] is changed but not [ls0]). *)

Lemma agree_frame_return:
  forall j ls ls0 m sp m' sp' parent retaddr ls',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  agree_callee_save ls' ls ->
  agree_frame j ls' ls0 m sp m' sp' parent retaddr.
Proof.
  intros. red in H0. inv H; constructor; auto; intros.
  rewrite H0; auto. red; intros; elim H. apply caller_save_reg_within_bounds; auto. 
  rewrite H0; auto.
  rewrite H0; auto.
  rewrite H0; auto.
Qed.

(** Preservation at tailcalls (when [ls0] is changed but not [ls]). *)

Lemma agree_frame_tailcall:
  forall j ls ls0 m sp m' sp' parent retaddr ls0',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  agree_callee_save ls0 ls0' ->
  agree_frame j ls ls0' m sp m' sp' parent retaddr.
Proof.
  intros. red in H0. inv H; constructor; auto; intros.
  rewrite <- H0; auto. red; intros; elim H. apply caller_save_reg_within_bounds; auto. 
  rewrite <- H0; auto.
  rewrite <- H0. auto. red; intros. eapply int_callee_save_not_destroyed; eauto. 
  rewrite <- H0. auto. red; intros. eapply float_callee_save_not_destroyed; eauto. 
Qed.

(** Properties of [agree_callee_save]. *)

Lemma agree_callee_save_return_regs:
  forall ls1 ls2,
  agree_callee_save (return_regs ls1 ls2) ls1.
Proof.
  intros; red; intros.
  unfold return_regs. destruct l; auto.
  rewrite pred_dec_false; auto. 
Qed.

Lemma agree_callee_save_set_result:
  forall sg vl ls1 ls2,
  agree_callee_save ls1 ls2 ->
  agree_callee_save (Locmap.setlist (map R (loc_result sg)) vl ls1) ls2.
Proof.
  intros sg. generalize (loc_result_caller_save sg).
  generalize (loc_result sg).
Opaque destroyed_at_call.
  induction l; simpl; intros.
  auto.
  destruct vl; auto. 
  apply IHl; auto.
  red; intros. rewrite Locmap.gso. apply H0; auto. 
  destruct l0; simpl; auto. 
Qed.

(** Properties of destroyed registers. *)

Lemma check_mreg_list_incl:
  forall l1 l2,
  forallb (fun r => In_dec mreg_eq r l2) l1 = true ->
  incl l1 l2.
Proof.
  intros; red; intros. 
  rewrite forallb_forall in H. eapply proj_sumbool_true. eauto. 
Qed.

Remark destroyed_by_op_caller_save:
  forall op, incl (destroyed_by_op op) destroyed_at_call.
Proof.
  destruct op; apply check_mreg_list_incl; compute; auto.
Qed.

Remark destroyed_by_load_caller_save:
  forall chunk addr, incl (destroyed_by_load chunk addr) destroyed_at_call.
Proof.
  intros. destruct chunk; apply check_mreg_list_incl; compute; auto.
Qed.

Remark destroyed_by_store_caller_save:
  forall chunk addr, incl (destroyed_by_store chunk addr) destroyed_at_call.
Proof.
  intros. destruct chunk; apply check_mreg_list_incl; compute; auto.
Qed.

Remark destroyed_by_cond_caller_save:
  forall cond, incl (destroyed_by_cond cond) destroyed_at_call.
Proof.
  destruct cond; apply check_mreg_list_incl; compute; auto.
Qed.

Remark destroyed_by_jumptable_caller_save:
  incl destroyed_by_jumptable destroyed_at_call.
Proof.
  apply check_mreg_list_incl; compute; auto.
Qed.

Remark destroyed_by_setstack_caller_save:
  forall ty, incl (destroyed_by_setstack ty) destroyed_at_call.
Proof.
  destruct ty; apply check_mreg_list_incl; compute; auto.
Qed.

Remark destroyed_at_function_entry_caller_save:
  incl destroyed_at_function_entry destroyed_at_call.
Proof.
  apply check_mreg_list_incl; compute; auto.
Qed.

Remark temp_for_parent_frame_caller_save:
  In temp_for_parent_frame destroyed_at_call.
Proof.
  Transparent temp_for_parent_frame.
  Transparent destroyed_at_call.
  unfold temp_for_parent_frame; simpl; tauto.
Qed.

Hint Resolve destroyed_by_op_caller_save destroyed_by_load_caller_save
    destroyed_by_store_caller_save
    destroyed_by_cond_caller_save destroyed_by_jumptable_caller_save
    destroyed_at_function_entry_caller_save: stacking.

Remark destroyed_by_setstack_function_entry:
  forall ty, incl (destroyed_by_setstack ty) destroyed_at_function_entry.
Proof.
  destruct ty; apply check_mreg_list_incl; compute; auto. 
Qed.

Remark transl_destroyed_by_op:
  forall op e, destroyed_by_op (transl_op e op) = destroyed_by_op op.
Proof.
  intros; destruct op; reflexivity.
Qed.

Remark transl_destroyed_by_load:
  forall chunk addr e, destroyed_by_load chunk (transl_addr e addr) = destroyed_by_load chunk addr.
Proof.
  intros; destruct chunk; reflexivity.
Qed.

Remark transl_destroyed_by_store:
  forall chunk addr e, destroyed_by_store chunk (transl_addr e addr) = destroyed_by_store chunk addr.
Proof.
  intros; destruct chunk; reflexivity.
Qed.

(** * Correctness of saving and restoring of callee-save registers *)

(** The following lemmas show the correctness of the register saving
  code generated by [save_callee_save]: after this code has executed,
  the register save areas of the current frame do contain the
  values of the callee-save registers used by the function. *)

Ltac rtrim H tac :=
  trim H; [try tac|try rtrim H tac].


Section SAVE_CALLEE_SAVE.

Variable bound: frame_env -> Z.
Variable number: mreg -> Z.
Variable mkindex: Z -> frame_index.
Variable ty: typ.
Variable j: meminj.
Variable cs: list stackframe.
Variable fb: block.
Variable sp: block.
Variable csregs: list mreg.
Variable ls: locset.

Inductive stores_in_frame: mem -> mem -> Prop :=
  | stores_in_frame_refl: forall m,
      stores_in_frame m m
  | stores_in_frame_step: forall m1 chunk ofs v m2 m3,
       ofs + size_chunk chunk <= fe.(fe_stack_data)
       \/ fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= ofs ->
       Mem.store chunk m1 sp ofs v = Some m2 ->
       stores_in_frame m2 m3 ->
       stores_in_frame m1 m3.


Remark stores_in_frame_trans:
  forall m1 m2, stores_in_frame m1 m2 ->
  forall m3, stores_in_frame m2 m3 -> stores_in_frame m1 m3.
Proof.
  induction 1; intros. auto. econstructor; eauto.
Qed.

Hypothesis number_inj: 
  forall r1 r2, In r1 csregs -> In r2 csregs -> r1 <> r2 -> number r1 <> number r2.
Hypothesis mkindex_valid:
  forall r, In r csregs -> number r < bound fe -> index_valid (mkindex (number r)).
Hypothesis mkindex_typ:
  forall z, type_of_index (mkindex z) = ty.
Hypothesis mkindex_inj:
  forall z1 z2, z1 <> z2 -> mkindex z1 <> mkindex z2.
Hypothesis mkindex_diff:
  forall r idx,
  idx <> mkindex (number r) -> index_diff (mkindex (number r)) idx.
Hypothesis csregs_typ:
  forall r, In r csregs -> mreg_type r = ty.

Hypothesis ls_temp_undef:
  forall r, In r (destroyed_by_setstack ty) -> ls (R r) = Eval Vundef.

Hypothesis wt_ls: forall r, wt (ls (R r)) ((mreg_type r)).

Lemma save_callee_save_regs_correct:
  forall l k rs m,
  incl l csregs ->
  list_norepet l ->
  frame_perm_freeable m sp ->
  agree_regs j ls rs ->
  exists rs', exists m',
    star step tge 
       (State cs fb (Eval (Vptr sp Int.zero))
         (save_callee_save_regs bound number mkindex ty fe l k) rs m)
    E0 (State cs fb (Eval (Vptr sp Int.zero)) k rs' m')
  /\ (forall r,
       In r l -> number r < bound fe ->
       index_contains_inj j m' sp (mkindex (number r)) (ls (R r)))
  /\ (forall idx v,
       index_valid idx ->
       (forall r,
         In r l -> number r < bound fe -> idx <> mkindex (number r)) ->
       index_contains m sp idx v ->
       index_contains m' sp idx v)
  /\ stores_in_frame m m'
  /\ frame_perm_freeable m' sp
  /\ agree_regs j ls rs'
  /\ (forall b, Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b).
Proof.
  induction l; intros; simpl save_callee_save_regs.
  - (* base case *)
    (exists rs; exists m). split. apply star_refl. 
    split. intros. elim H3.
    split. auto.
    split. constructor.
    repSplit; auto. tauto.
  - (* inductive case *)
    assert (R1: incl l csregs). eauto with coqlib.
    assert (R2: list_norepet l). inversion H0; auto.
    unfold save_callee_save_reg.
    destruct (zlt (number a) (bound fe)).
    + (* a store takes place *)
      exploit store_index_succeeds. apply (mkindex_valid a); auto with coqlib. 
      eauto. instantiate (1 := rs a). intros [m1 ST].
      exploit (IHl k (undef_regs (destroyed_by_setstack ty) rs) m1).  auto with coqlib. auto. 
      red; eauto with mem.
      apply agree_regs_exten with ls rs. auto.
      intros.
      destruct (In_dec mreg_eq r (destroyed_by_setstack ty)).
      left.  apply ls_temp_undef; auto. 
      right; split. auto. apply undef_regs_other; auto.
      intros [rs' [m' [A [B [C [D [E [F G]]]]]]]].
      exists rs'; exists m'. 
      {
        repSplit; auto.
        - eapply star_left; eauto.
          + econstructor. 
            rewrite <- (mkindex_typ (number a)). 
            apply store_stack_succeeds; auto with coqlib.
            auto.
          + traceEq.
        - intros.
          simpl in H3.
          destruct (mreg_eq a r).
          + subst r.
            assert (index_contains_inj j m1 sp (mkindex (number a))
                                       (Val.load_result
                                          (chunk_of_type (type_of_index (mkindex (number a))))
                                          (ls (R a)))).
            { generalize (H2 a). 
              intro.
              red.
              generalize (Mem.load_store_same _ _ _ _ _ _ ST).
              intros. dex. repeat destr_and.
              eexists; repSplit.
              econstructor. auto.
              apply H7. eauto.
              apply load_result_ei; auto. 
            }
            destruct H5 as [v' [P Q]].
            exists v'; split; auto. apply C; auto. 
            intros. apply mkindex_inj. apply number_inj; auto with coqlib. 
            inv H0. congruence.
            eapply expr_inj_se_l. eauto.
            apply load_result_eSexpr_typ.
            generalize (wt_ls a). 
            rewrite mkindex_typ. rewrite csregs_typ. auto. auto.
          + apply B; auto with coqlib. 
            intuition congruence.
        - intros.
          apply C; auto with coqlib.
          eapply gso_index_contains; eauto with coqlib. 
        - econstructor; eauto.
          rewrite size_type_chunk. apply offset_of_index_disj_stack_data_2; eauto with coqlib.
        - intros; rewrite <- G.
          eapply Genv.store_dyn; eauto.
      } 
    + (* no store takes place *)
      exploit (IHl k rs m); auto with coqlib. 
      intros [rs' [m' [A [B [C [D [E [F G]]]]]]]].
      exists rs'; exists m'; intuition. 
      simpl in H3. destruct H3. subst r. omegaContradiction. apply B; auto.
      apply C; auto with coqlib.
      intros. eapply H4; eauto. auto with coqlib.
Qed.

End SAVE_CALLEE_SAVE.

Remark LTL_undef_regs_same:
  forall r rl ls, In r rl -> LTL.undef_regs rl ls (R r) = Eval Vundef.
Proof.
  induction rl; simpl; intros. contradiction. 
  unfold Locmap.set. destruct (Loc.eq (R a) (R r)). auto. 
  destruct (Loc.diff_dec (R a) (R r)); auto. 
  apply IHrl. intuition congruence.
Qed.

Remark LTL_undef_regs_others:
  forall r rl ls, ~In r rl -> LTL.undef_regs rl ls (R r) = ls (R r).
Proof.
  induction rl; simpl; intros. auto.
  rewrite Locmap.gso. apply IHrl. intuition. red. intuition. 
Qed.

Remark LTL_undef_regs_slot:
  forall sl ofs ty rl ls, LTL.undef_regs rl ls (S sl ofs ty) = ls (S sl ofs ty).
Proof.
  induction rl; simpl; intros. auto.
  rewrite Locmap.gso. apply IHrl. red; auto. 
Qed.

Lemma save_callee_save_correct:
  forall j ls0 rs sp cs fb k m,
  let ls := LTL.undef_regs destroyed_at_function_entry ls0 in
  agree_regs j ls rs ->
  (forall r, wt (ls (R r)) (mreg_type r)) ->
  frame_perm_freeable m sp ->
  exists rs', exists m',
    star step tge 
       (State cs fb (Eval (Vptr sp Int.zero)) (save_callee_save fe k) rs m)
    E0 (State cs fb (Eval (Vptr sp Int.zero)) k rs' m')
  /\ (forall r,
       In r int_callee_save_regs -> index_int_callee_save r < b.(bound_int_callee_save) ->
       index_contains_inj j m' sp (FI_saved_int (index_int_callee_save r))
                          (ls (R r)))
  /\ (forall r,
       In r float_callee_save_regs -> index_float_callee_save r < b.(bound_float_callee_save) ->
       index_contains_inj j m' sp (FI_saved_float (index_float_callee_save r))
                          (ls (R r)))
  /\ (forall idx v,
       index_valid idx ->
       match idx with FI_saved_int _ => False | FI_saved_float _ => False | _ => True end ->
       index_contains m sp idx v ->
       index_contains m' sp idx v)
  /\ stores_in_frame sp m m'
  /\ frame_perm_freeable m' sp
  /\ agree_regs j ls rs'
  /\ (forall b, Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b).
Proof.
  intros.
  assert (UNDEF: forall r ty, In r (destroyed_by_setstack ty) -> ls (R r) = Eval Vundef).
  {
    intros. unfold ls. apply LTL_undef_regs_same. eapply destroyed_by_setstack_function_entry; eauto.
  }
  exploit (save_callee_save_regs_correct 
             fe_num_int_callee_save
             index_int_callee_save
             FI_saved_int Tany32
             j cs fb sp int_callee_save_regs ls).
  - intros. apply index_int_callee_save_inj; auto. 
  - intros. simpl. split. apply Zge_le. apply index_int_callee_save_pos; auto. assumption.
  - auto.
  - intros; congruence.
  - intros; simpl. destruct idx; auto. congruence.
  - intros. apply int_callee_save_type. auto.
  - eauto.
  - red; eauto.
  - apply incl_refl. 
  - apply int_callee_save_norepet.
  - eauto.
  - eauto.
  - intros [rs1 [m1 [A [B [C [D [E [F G]]]]]]]].
    exploit (save_callee_save_regs_correct 
               fe_num_float_callee_save
               index_float_callee_save
               FI_saved_float Tany64
               j cs fb sp float_callee_save_regs ls).
    + intros. apply index_float_callee_save_inj; auto. 
    + intros. simpl. split. apply Zge_le. apply index_float_callee_save_pos; auto. assumption.
    + simpl; auto.
    + intros; congruence.
    + intros; simpl. destruct idx; auto. congruence.
    + intros. apply float_callee_save_type. auto.
    + eauto.
    + red; eauto.
    + apply incl_refl. 
    + apply float_callee_save_norepet.
    + eexact E.
    + eexact F.
    + intros [rs2 [m2 [P [Q [R [S [T [U V]]]]]]]].
      exists rs2; exists m2.
      repSplit.
      * unfold save_callee_save, save_callee_save_int, save_callee_save_float.
        eapply star_trans; eauto. 
      * intros.
        destruct (B r H2 H3) as [v [X Y]]. exists v; split; auto. apply R.
        apply index_saved_int_valid; auto. 
        intros. congruence.
        auto.
      * simpl. intuition. 
      * intros. apply R. auto.
        intros; destruct idx; contradiction||congruence.
        apply C. auto. 
        intros. destruct idx; contradiction||congruence.
        auto.
      * eapply stores_in_frame_trans; eauto.
      * auto.
      * auto.
      * intros; rewrite G, V. tauto.
Qed.

(** Properties of sequences of stores in the frame. *)

Lemma stores_in_frame_inject:
  forall j sp sp' m,
  (forall b delta, j b = Some(sp', delta) -> b = sp /\ delta = fe.(fe_stack_data)) ->
  (forall ofs k p, Mem.perm m sp ofs k p -> 0 <= ofs < f.(Linear.fn_stacksize)) ->
  forall m1 m2,
    stores_in_frame sp' m1 m2 ->
    Mem.inject true expr_inj_se j m m1 ->
    Mem.inject true expr_inj_se j m m2.
Proof.
  induction 3; intros.
  auto.
  apply IHstores_in_frame.
  intros. eapply Mem.store_outside_inject; eauto.
  intros. exploit H; eauto. intros [A B]; subst.
  exploit H0; eauto. omega. 
Qed.

Lemma stores_in_frame_valid:
  forall b sp m m', stores_in_frame sp m m' -> Mem.valid_block m b -> Mem.valid_block m' b.
Proof.
  induction 1; intros. auto. apply IHstores_in_frame. eauto with mem.
Qed.

Lemma stores_in_frame_perm:
  forall b ofs k p sp m m', stores_in_frame sp m m' -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p.
Proof.
  induction 1; intros. auto. apply IHstores_in_frame. eauto with mem.
Qed.

Lemma stores_in_frame_contents:
  forall chunk b ofs sp, Plt b sp ->
  forall m m', stores_in_frame sp m m' -> 
  Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  induction 2. auto. 
  rewrite IHstores_in_frame. eapply Mem.load_store_other; eauto.
  left. apply Plt_ne; auto.
Qed.

Lemma undef_regs_type:
  forall ty l rl ls,
    wt (ls l) ty -> wt (LTL.undef_regs rl ls l) ty.
Proof.
  induction rl; simpl; intros.
- auto.
- unfold Locmap.set. destruct (Loc.eq (R a) l).
  red; left; eexists; split; try apply subtype_refl; destr. 
  destruct (Loc.diff_dec (R a) l); auto.
  red; left; eexists; split; try apply subtype_refl; destr. 
Qed.

Lemma inj_store_ifu:
  forall j m1 m1'
    (MINJ : Mem.inject true expr_inj_se j m1 m1')
    ofs chunk
    (OFS : ofs + size_chunk chunk <= fe_stack_data fe \/
           fe_stack_data fe + Linear.fn_stacksize f <= ofs)
    v sp m2'
    (STORE : Mem.store chunk m1' sp ofs v = Some m2')
   
    (H: forall b delta o k p,
        j b = Some (sp, delta) ->
        delta < fe_stack_data fe \/ fe_stack_data fe + Linear.fn_stacksize f <= delta ->
        Mem.perm m1 b o k p ->
        False
    )
    (inj_data: forall b delta, j b = Some (sp, delta) ->
                          fe_stack_data fe <= delta <
                          fe_stack_data fe + Linear.fn_stacksize f ->
                          delta = fe_stack_data fe /\ Mem.bounds_of_block m1 b = (0, Linear.fn_stacksize f)
    ),
    Mem.inject true expr_inj_se j m1 m2'.
Proof.
  intros.
  inversion MINJ; constructor; intros; eauto with mem.
  inversion mi_inj; constructor; intros; eauto with mem.
  eapply Mem.store_in_bound_m_1; eauto.
  erewrite <- Mem.mask_store; eauto.
  erewrite (Mem.store_mem_contents _ _ _ _ _ _ STORE).
  rewrite Maps.PMap.gsspec.
  destr_cond_match; auto. subst.
  assert (ITVdec: Decidable.decidable (delta < fe_stack_data fe \/ fe_stack_data fe + Linear.fn_stacksize f <= delta)) by (red; lia).
  destruct ITVdec.
  - specialize (H _ _ _ _ _ H0 H2 H1). easy.
 - rewrite Mem.setN_other. auto. intro r.
    rewrite encode_val_length. rewrite <- size_chunk_conv.
    intros. intro.
    subst.
    eapply inj_data in H0; eauto. repeat destr_and.
    apply Mem.perm_bounds in H1. unfold Mem.in_bound_m in H1.
    rewrite H6 in H1; unfold in_bound in H1; simpl in *.
    lia. lia.
  - unfold Mem.nb_boxes_used_m.
    rewrite (Mem.store_mk_block_list _ _ _ _ _ _ STORE).
    rewrite <- (Mem.nb_extra_store _ _ _ _ _ _ STORE). intuition lia.
  - specialize (mi_inj_dynamic _ _ _ H0). des mi_inj_dynamic. des a.
    rewrite <- (Genv.store_dyn _ _ _ _ _ STORE).
    erewrite <- (Mem.bounds_of_block_store _ _ _ _ _ _ STORE); eauto.
Qed.

Lemma inj_sif_ifu:
  forall sp m1' m2'
    (SIF : stores_in_frame sp m1' m2')
    j m1 
    (MINJ: Mem.inject true expr_inj_se j m1 m1')
    
    (H: forall b delta o k p, 
        j b = Some (sp, delta) ->
        delta < fe_stack_data fe \/ fe_stack_data fe + Linear.fn_stacksize f <= delta ->
        Mem.perm m1 b o k p ->
        False
    )
    (inj_data: forall b delta, j b = Some (sp, delta) ->
                          fe_stack_data fe <= delta <
                          fe_stack_data fe + Linear.fn_stacksize f ->
                          delta = fe_stack_data fe /\ Mem.bounds_of_block m1 b = (0, Linear.fn_stacksize f)
    ),
    Mem.inject true expr_inj_se j m1 m2'.
Proof.
  induction 1; intros; auto.
  apply IHSIF; clear IHSIF; auto.
  eapply inj_store_ifu; eauto.
Qed.

(** As a corollary of the previous lemmas, we obtain the following
  correctness theorem for the execution of a function prologue
  (allocation of the frame + saving of the link and return address +
  saving of the used callee-save registers). *)

Lemma stores_in_frame_bounds:
  forall sp m1 m2
    (SIF: stores_in_frame sp m1 m2)
    b,
    Mem.bounds_of_block m1 b = Mem.bounds_of_block m2 b.
Proof.
  induction 1; simpl; intros; eauto.
  rewrite (Mem.bounds_of_block_store _ _ _ _ _ _ H0); auto.
Qed.


Lemma stores_in_frame_nextblock:
  forall sp m1 m2
    (SIF: stores_in_frame sp m1 m2),
    Mem.nextblock m1 = Mem.nextblock m2.    
Proof.
  induction 1; simpl; intros; eauto.
  rewrite <- (Mem.nextblock_store _ _ _ _ _ _ H0); auto.
Qed.

Opaque fe_stack_data.
Opaque Z.add Z.sub Z.mul.


Lemma box_span_ma_3:
  forall z, z >= 0 ->
    8 * Z.of_nat (Mem.box_span z) = align z 8.
Proof.
  intros.
  replace 8 with (two_power_nat MA).
  apply Mem.box_span_align; auto.
  rewrite ma_3; reflexivity.
Qed.

Lemma box_span_mul_plus:
  forall z y, z >= 0 -> y >= 0 ->
    Mem.box_span (8 * z + y) = (Z.to_nat z + Mem.box_span y)%nat.
Proof.
  intros.
  replace 8 with (two_power_nat MA) by (rewrite ma_3; reflexivity).
  unfold Mem.box_span.
  replace ((two_power_nat MA * z + y - 1) / two_power_nat MA)
    with (z + (y - 1) / two_power_nat MA).
  rewrite <- Z.add_assoc. rewrite (Z2Nat.inj_add z). auto.
  lia.
  destruct (zlt 0 y). apply Z.add_nonneg_nonneg. apply Z.div_pos. lia. apply Z.gt_lt, Mem.tpMA_pos.
  lia.
  replace y with 0 by lia. rewrite ma_3. vm_compute. destr.
  rewrite Z.mul_comm.
  replace (z * two_power_nat MA + y - 1) with (z * two_power_nat MA + (y - 1)) by lia.
  rewrite Z_div_plus_full_l. lia. generalize (Mem.tpMA_pos); lia.
Qed.


Lemma box_span_mul:
  forall z, z >= 0 ->
    Mem.box_span (8 * z) = (Z.to_nat z)%nat.
Proof.
  intros.
  replace (8 * z) with (8 * z + 0) by lia.
  rewrite box_span_mul_plus. rewrite <- box_span_0. lia. lia. lia.
Qed.


Lemma function_prologue_correct:
  forall j m1 (ABI: Mem.all_blocks_injected j m1) ls ls0 ls1 rs rs1 m1' m2 sp parent ra cs fb m11 k
    (AGREGS:agree_regs j ls rs)
    (AGCS: agree_callee_save ls ls0)
    (WTREGS: forall r, wt (ls (R r)) (mreg_type r))
    (LS1: ls1 = LTL.undef_regs destroyed_at_function_entry (LTL.call_regs ls))
    (RS1: rs1 = undef_regs destroyed_at_function_entry rs)
    (INJ1: Mem.inject true expr_inj_se j m1 m1')
    (Aligned: Linear.fn_stacksize f = 8 * Z.of_nat (Mem.box_span (Linear.fn_stacksize f)))
    (ALLOC: Mem.alloc m1 0 f.(Linear.fn_stacksize) Normal = Some (m11, sp))
    (AB: MemReserve.reserve_boxes m11 (needed_stackspace f.(Linear.fn_id)) = Some m2)
    (TYPAR: wt parent AST.Tint) (TYRA: wt ra AST.Tint)
    (SSpos: 0 <= Linear.fn_stacksize f),
  exists j' rs' m2' sp' m3' m4' m5', 
    Mem.alloc m1' 0 (align tf.(fn_stacksize) (two_power_nat MA)) Normal = Some (m2', sp')
  /\ store_stack m2' (Eval (Vptr sp' Int.zero)) AST.Tint tf.(fn_link_ofs) parent = Some m3'
  /\ store_stack m3' (Eval (Vptr sp' Int.zero)) AST.Tint tf.(fn_retaddr_ofs) ra = Some m4'
  /\ star step tge 
         (State cs fb (Eval (Vptr sp' Int.zero)) (save_callee_save fe k) rs1 m4')
      E0 (State cs fb (Eval (Vptr sp' Int.zero)) k rs' m5')
  /\ agree_regs j' ls1 rs'
  /\ agree_frame j' ls1 ls0 m2 sp m5' sp' parent ra
  /\ inject_incr j j'
  /\ inject_separated j j' m1 m1'
  /\ Mem.inject true expr_inj_se j' m2 m5'
  /\ stores_in_frame sp' m2' m5'
  /\ (Mem.all_blocks_injected j m1 -> Mem.all_blocks_injected j' m2).
Proof.
  intros.
  rewrite unfold_transf_function.
  unfold fn_stacksize, fn_link_ofs, fn_retaddr_ofs.

  assert (sizes: fn_stacksize tf = 8 * Z.of_nat (Mem.box_span (fe_size fe))).
  {
    rewrite unfold_transf_function. unfold fn_stacksize.
    rewrite box_span_ma_3; auto. apply Zle_ge, size_pos.
  }
  assert (FSD:  0 <= fe_stack_data fe <= 8 * Z.of_nat (Mem.box_span (fn_stacksize tf)) - 8 * Z.of_nat (Mem.box_span (Linear.fn_stacksize f))).
  {
    generalize stack_data_offset_valid (bound_stack_data_pos b) size_no_overflow.
    rewrite sizes, <- stackspace_ok. split. lia.
    rewrite box_span_mul by lia.
    rewrite Z2Nat.id by lia.
    cut (fe_stack_data fe <= 8 * Z.of_nat (needed_stackspace (Linear.fn_id f))). lia.
    eapply Z.le_trans with (align (fe_size fe) 8 - bound_stack_data b). generalize (align_le (fe_size fe) 8). lia.
    generalize bound_stack_data_stacksize.
    rewrite <- ! box_span_ma_3.
    rewrite <- stackspace_ok.
    intros.
    rewrite Nat2Z.inj_add.
    rewrite Z.mul_add_distr_l.
    cut (8 * Z.of_nat (Mem.box_span (Linear.fn_stacksize f)) <= bound_stack_data b ). lia.    
    rewrite <- Aligned. lia. apply Zle_ge, size_pos.
  }
  assert (IOA: Mem.inj_offset_aligned
                 (fe_stack_data fe)
                 (Linear.fn_stacksize f + 8 * Z.of_nat (needed_stackspace (Linear.fn_id f)))).
  {
    red. intros. 
    eapply Zdivide_trans.
    2: apply fe_stack_data_aligned.
    destruct (align_divides (Linear.fn_stacksize f) 8) as [X' X'eq]. lia.    
    rewrite <- box_span_ma_3 in X'eq. rewrite <- Aligned in X'eq. rewrite X'eq.
    cut (let x := X' * 8 + 8* Z.of_nat (needed_stackspace (Linear.fn_id f)) in
         x = 0 \/ x >= 8).
    Require Import Tactics.
    destr.
    intros [A|A]. rewrite A. change (alignment_of_size 0) with O.
    change (two_power_nat O) with 1. apply Z.divide_1_l.
    unfold alignment_of_size.
    repeat destr; try lia.
    change (two_power_nat 3) with 8; exists 1; lia.
    destr. lia.
    lia.
  }
  
  destruct (fe_stack_data_aligned) as [X Xeq].
  destruct (align_divides (Linear.fn_stacksize f) 8) as [X' X'eq]. lia.
  destruct (align_divides (fe_size fe) 8) as [Y Yeq]. lia.
  

  assert (EQY: (Z.to_nat Y - Z.to_nat (X + X') + Z.to_nat X)%nat =
          (needed_stackspace (Linear.fn_id f))%nat).
  {
    apply Nat2Z.inj. 
    apply (Z.mul_reg_l _ _ 8). lia.
    transitivity (align (fe_size fe) 8 - Linear.fn_stacksize f). 
    rewrite <- Z2Nat.inj_sub. 
    rewrite <- ! Z2Nat.inj_add.
    rewrite Z2Nat.id. 
    rewrite Yeq. rewrite Aligned. rewrite box_span_ma_3. rewrite X'eq. lia. lia. 
    apply Zmult_le_reg_r with (p:=8). lia.
    rewrite Z.mul_add_distr_r.
    rewrite Z.mul_sub_distr_r.
    rewrite Z.mul_add_distr_r.
    rewrite <- X'eq, <- Xeq, <- Yeq. rewrite <- ! box_span_ma_3. lia. lia.
    apply Zle_ge, size_pos.

    apply Zmult_le_reg_r with (p:=8). lia.
    rewrite Z.mul_sub_distr_r.
    rewrite Z.mul_add_distr_r.
    rewrite <- X'eq, <- Xeq, <- Yeq.
    rewrite <- (box_span_ma_3 (Linear.fn_stacksize _)).
    rewrite <- box_span_ma_3. rewrite <- sizes.
    replace (fn_stacksize tf) with (8 * Z.of_nat (Mem.box_span (fn_stacksize tf))). lia.
    rewrite sizes. rewrite box_span_mul. rewrite Z2Nat.id. auto. lia. lia. apply Zle_ge, size_pos.
    lia.
    lia.
    apply Zmult_le_reg_r with (p:=8). lia.
    rewrite Z.mul_add_distr_r. 
    rewrite <- X'eq, <- Xeq.
    rewrite <- (box_span_ma_3 (Linear.fn_stacksize _)). lia. lia.
    rewrite <- box_span_ma_3. rewrite <- stackspace_ok. lia.
    apply Zle_ge, size_pos.
  }

Lemma alloc_alloc_bytes_bigger_alloc_succeeds:
  forall m1 m1' (MINJ: (Mem.nb_boxes_used_m m1' <= Mem.nb_boxes_used_m m1)%nat)
    m2 b sz  (SZpos: 0 <= sz)  (ALLOC: Mem.alloc m1 0 sz Normal = Some (m2,b))
    m3 n (AB: MemReserve.reserve_boxes m2 n = Some m3)
    sz' (RNG: sz <= sz' <= sz + 8*Z.of_nat n),
  exists m2' b',
    Mem.alloc m1' 0 sz' Normal = Some (m2',b'). 
Proof.
  clear; intros.
  destruct (Mem.alloc m1' 0 sz' Normal) as [[m2' b']|] eqn:?.
  - exists m2', b'. eauto.
  - exfalso.
    apply Mem.alloc_none_too_many_boxes in Heqo.
    cut (Z.of_nat (Mem.nb_boxes_used_m m1 + Mem.box_span (Z.max 0 sz) + n) < Mem.nb_boxes_max).
    cut (Mem.box_span (Z.max 0 sz) + n >= Mem.box_span (Z.max 0 sz'))%nat. lia.
    clear - RNG SZpos.
    unfold Peano.ge.
    exploit Mem.box_span_le. split. 2: apply RNG. lia. intro LE.
    rewrite ! Z.max_r by lia. rewrite Z.add_comm in LE. rewrite box_span_mul_plus in LE.
    rewrite Nat2Z.id in LE. lia. lia. lia.
    clear - ALLOC AB.
    eapply Z.le_lt_trans. 2: apply (Mem.wfm_alloc m3).
    replace (Mem.nb_boxes_used_m m3) with (Mem.nb_boxes_used_m m2 + n)%nat.
    rewrite <- (Mem.nb_boxes_alloc _ _ _ _ _ _ ALLOC). lia.
    unfold MemReserve.reserve_boxes in AB. destr_in AB. inv AB. unfold Mem.nb_boxes_used_m.
    unfold Mem.mk_block_list, Mem.size_block. simpl. lia.
Qed.

Lemma alloc_alloc_bytes_inject:
  forall j m1 (ABI: Mem.all_blocks_injected j m1)
    m1' (MINJ: Mem.inject true expr_inj_se j m1 m1')
    m2 sp sz (ALLOC: Mem.alloc m1 0 sz Normal = Some (m2,sp))
    (x x' y: nat)
    m3  (AB: MemReserve.reserve_boxes m2 (y-x'+x) = Some m3)
    (SZpos: 0 <= sz)
    (Aligned: sz = align sz 8)
    (EQ: align sz 8 + 8 * Z.of_nat x = 8 * Z.of_nat x')
    (ORD: (x <= x' <= y)%nat)
,
  exists m2' sp',
    Mem.alloc m1' 0 (8*Z.of_nat y) Normal = Some (m2',sp') /\
    exists j',
      j'= (fun b => if peq b sp then Some (sp', 8 * Z.of_nat x) else j b) /\
      j' sp = Some (sp',8*Z.of_nat x) /\
      Mem.inject true expr_inj_se j' m3 m2' /\
      inject_incr j j'.
Proof.
  intros.
  destruct (fun pf => alloc_alloc_bytes_bigger_alloc_succeeds
                     m1 m1' pf m2 sp sz SZpos ALLOC m3 _
                     AB (8*Z.of_nat y))
    as [m2' [sp' ALLOC' ]].
  apply (Mem.mi_size_mem _ _ _ _ _ (Mem.mi_inj _ _ _ _ _ MINJ)).
  split. generalize (align_le sz 8); lia.
  exists m2', sp'. repSplit; auto.
  exists (fun b => if peq b sp then Some (sp', 8 * Z.of_nat x) else j b).
  repSplit.
  - auto.
  - rewrite peq_true. eauto.
  - {
      constructor.
      - constructor.
        + Opaque Z.add Z.sub.
          intros.
          cut (Mem.perm m2 b1 ofs k p). clear H0; intro H0.
          eapply Mem.perm_alloc_inv in H0; eauto.
          destr_in H.
          * destr_in H0. subst b1. inv H. subst b2 delta.
            eapply Mem.perm_implies. eapply Mem.perm_alloc_2; eauto.
            split. lia.
            apply Z.lt_le_trans with (m:=8*Z.of_nat x').
            2: ppsimpl; lia.
            2: constructor.
            rewrite <- EQ.
            generalize (align_le sz 8); lia.
          * destr_in H0. assert (Plt b1 sp).
            apply Mem.alloc_result in ALLOC. subst sp.
            eapply Mem.perm_valid_block; eauto.
            generalize  (Mem.mi_perm _ _ _ _ _ (Mem.mi_inj _ _ _ _ _ MINJ) _ _ _ _ _ _ H H0).
            eapply Mem.perm_alloc_1; eauto.
          * rewrite (MemReserve.reserve_perm _ _ _ _ _ _ _ AB). auto.

        + intros.
          unfold Mem.in_bound_m in H0.
          rewrite <- (MemReserve.reserve_bounds_of_block _ _ _ _ AB) in H0.
          destr_in H.
          * subst b1. inv H. subst b2 delta.
            red.
            erewrite Mem.bounds_of_block_alloc; eauto.
            red; simpl. rewrite Zmax_r by lia.
            erewrite Mem.bounds_of_block_alloc in H0. red in H0; simpl in H0. 2: eauto.
            split. lia.
            apply Z.lt_le_trans with (m:=8*Z.of_nat x').
            2: ppsimpl; lia.
            rewrite <- EQ.
            generalize (align_le sz 8); lia.

          * eapply Mem.alloc_in_bound'; eauto.
            eapply Mem.alloc_in_bound_old in H0; eauto.
            apply  (Mem.mi_bounds _ _ _ _ _ (Mem.mi_inj _ _ _ _ _ MINJ) _ _ _ _ H H0).
            
        + intros.
          rewrite <- (MemReserve.reserve_mask _ _ _ _ AB).
          rewrite (Mem.a_mask _ _ _ _ _ ALLOC').
          rewrite (Mem.a_mask _ _ _ _ _ ALLOC).
          destr_in H.
          * inv H. revert Aligned; subst; intro.
            destr. xomega. clear n. rewrite peq_true. destr. xomega. clear n.
            split. apply Mem.alignment_of_size_inj.
            rewrite  ! Zmax_r by lia.
            apply Zle_ge. etransitivity.
            apply (align_le sz 8); try lia.
            transitivity (8*Z.of_nat x'). lia. lia.
            eapply Z.divide_trans.
            apply IntFacts.two_p_inj_div. instantiate (1:=3).
            unfold Alloc.alignment_of_size; repeat destr; lia.
            exists (Z.of_nat x). change (two_p 3) with 8; lia.
          * destr. destr. eapply Mem.mi_align'. eapply Mem.mi_inj. eauto. eauto.
            split. lia. exists z; lia.
            destr. subst b1.
            eapply Mem.valid_block_inject_2 in H; eauto.
            eapply Mem.fresh_block_alloc in H; eauto. easy.
            destr.
            eapply Mem.valid_block_inject_2 in H; eauto. exfalso; apply n0.
            red in H. exploit Mem.alloc_result. apply ALLOC'. intro; subst sp'. auto.
            split. lia. exists z; lia.
        + intros.
          replace (Mem.mem_contents m3) with (Mem.mem_contents m2).
          rewrite (Mem.a_mem_contents' _ _ _ _ _ ALLOC').
          rewrite (Mem.a_mem_contents' _ _ _ _ _ ALLOC).
          rewrite ! Maps.PMap.gsspec.
          cut (Mem.perm m2 b1 ofs Cur Readable). clear H0; intro H0.
          destr_in H.
          * inv H. subst b1 b2 delta.
            rewrite peq_true.
            rewrite ! Mem.get_init_block.
            constructor.
            apply wf_inj_undef. auto.
            red; intros. rewrite gnp_rew; simpl; auto.
            right.
            red; intros. rewrite gnp_rew; simpl; auto.
          * cut (b2 <> sp'). intro DIFF.
            rewrite peq_false; auto. eapply memval_inject_incr. auto.
            eapply Mem.mi_memval; eauto. eapply Mem.mi_inj; eauto.
            eauto with mem. 
            red; intros. destr. subst b0.
            eapply Mem.valid_block_inject_1 in H1. 2: eauto.
            eapply Mem.fresh_block_alloc in H1; eauto. destruct H1.
            intro; subst b2.
            eapply Mem.valid_block_inject_2 in H. 2: eauto.
            eapply Mem.fresh_block_alloc in H; eauto.
          * unfold MemReserve.reserve_boxes in AB; destr_in AB; inv AB. unfold Mem.perm in *; simpl in *; subst m3. eauto.
          * unfold MemReserve.reserve_boxes in AB; destr_in AB; inv AB; reflexivity.
        +
          replace (Mem.nb_boxes_used_m m3) with (Mem.nb_boxes_used_m m2 + (y - x' + x))%nat.
          Focus 2.
          unfold MemReserve.reserve_boxes in AB. destr_in AB. inv AB. unfold Mem.nb_boxes_used_m.
          unfold Mem.mk_block_list, Mem.size_block. simpl. clear. lia. 
          rewrite (Mem.nb_boxes_alloc _ _ _ _ _ _ ALLOC).
          rewrite (Mem.nb_boxes_alloc _ _ _ _ _ _ ALLOC'). intros _.
          exploit Mem.mi_size_mem. apply Mem.mi_inj; eauto. auto.
          cut (Mem.box_span (Z.max 0 sz) + (y - x' + x) >= Mem.box_span (Z.max 0 (8 * Z.of_nat y)))%nat. lia.
          unfold Peano.ge. rewrite Z.max_r. 2: lia.
          rewrite box_span_mul by lia. rewrite Nat2Z.id. rewrite Z.max_r by lia.
          rewrite Aligned.
          replace (align sz 8) with (8 * (Z.of_nat x' - Z.of_nat x)) by lia.
          rewrite box_span_mul. rewrite Z2Nat.inj_sub by lia.
          rewrite ! Nat2Z.id. lia. lia.

      - intros. unfold Mem.valid_block in H.
        destr; eauto. subst b0. 
        exfalso; apply H.
        rewrite <- (MemReserve.reserve_nextblock _ _ _ AB).
        eapply Mem.valid_new_block; eauto.
        eapply Mem.mi_freeblocks. eauto. unfold Mem.valid_block.
        rewrite <- (MemReserve.reserve_nextblock _ _ _ AB) in H. 
        intros PLT. eapply Mem.valid_block_alloc in PLT; eauto.
        
      - intros.
        unfold Mem.valid_block.
        destr_in H. inv H.
        + subst b0 b' delta.
          eapply Mem.valid_new_block; eauto.
        + generalize (Mem.mi_mappedblocks _ _ _ _ _ MINJ _ _ _ H).
          eapply Mem.valid_block_alloc; eauto.
          
      - red; intros.
        clear Aligned.
        destr_in H0.
        + inv H0.
          destr_in H1.
          left.  intro; subst.
          eapply Mem.valid_block_inject_2 in H1; eauto.
          eapply Mem.fresh_block_alloc in ALLOC'. destr.
        + destr_in H1. inv H1. 
          left.  intro; subst.
          eapply Mem.valid_block_inject_2 in H0; eauto.
          eapply Mem.fresh_block_alloc in ALLOC'. destr.
          eapply Mem.mi_no_overlap'. eauto. 2: eauto. 2: eauto. eauto.

          eapply Mem.alloc_in_bound_old. eauto. eauto.
          red; rewrite (MemReserve.reserve_bounds_of_block _ _ _ _ AB); eauto.
          eapply Mem.alloc_in_bound_old. eauto. eauto.
          red; rewrite (MemReserve.reserve_bounds_of_block _ _ _ _ AB); eauto.

      - clear Aligned. intros.
        destr_in H. inv H. lia.
        eapply Mem.mi_delta_pos; eauto.

      - intros. clear Aligned.
        rewrite <- ! (MemReserve.reserve_is_dynamic_block _ _ _ _ AB).
        rewrite <- Mem.is_block_dynamic_alloc; eauto.
        rewrite <- Mem.is_block_dynamic_alloc with (m':=m2'); eauto.
        rewrite <- (MemReserve.reserve_bounds_of_block _ _ _ _ AB).
        rewrite (Mem.bounds_of_block_alloc_eq _ _ _ _ _ _ ALLOC),
        (Mem.bounds_of_block_alloc_eq _ _ _ _ _ _ ALLOC').
        destr_in H. inv H. rewrite ! peq_true.
        + unfold Mem.is_dynamic_block.
          exploit Mem.alloc_result. eexact ALLOC. intro; subst.
          exploit Mem.alloc_result. eexact ALLOC'. intro; subst.
          rewrite ! Mem.blocktype_valid by xomega.
          repSplit; destr.
        + rewrite peq_false by auto.
          exploit Mem.mi_inj_dynamic; eauto.
          assert (b' <> sp').
          {
            intro; subst.
            eapply Mem.valid_block_inject_2 in H; eauto. eapply Mem.fresh_block_alloc in H; eauto.
          }
          intros [B [C D]]; repSplit; destr.
          * intro DYN; trim C; auto. split; destr.
            destr; eauto.
            eapply Mem.valid_block_inject_2 in H; eauto.
            red in H.
            exploit Mem.nextblock_alloc. apply ALLOC'. intro A; rewrite A in n1.
            clear - n1 H. xomega.
          * intro A. trim C. auto. des C. split; auto. rewrite peq_false by auto.
            destr. eapply Mem.valid_block_inject_1 in H; eauto.
            exploit Mem.nextblock_alloc. apply ALLOC. intro X; rewrite X in n0.
            clear - n0 H. red in H. xomega.
          * intro DYN; trim D; auto. intros.
            destr_in H1. eapply D in H; eauto.
    }
  - red; intros.
    rewrite H. destr.
    subst b0. eapply Mem.valid_block_inject_1 in H; eauto.
    eapply Mem.fresh_block_alloc in H; eauto. des H.
Qed.


  destruct (alloc_alloc_bytes_inject
              _ _ ABI _ INJ1 _ _ _
              ALLOC (Z.to_nat X) (Z.to_nat (X+X')) (Z.to_nat Y) m2)
    as (m2' & sp' & ALLOC' & j' & j'SPEC & j'SUBSPEC & INJ2 & INCR); auto.
  { 
    rewrite <- AB. f_equal. auto.
  }
  {
    rewrite <- box_span_ma_3. auto. lia.
  }
  {
    rewrite X'eq. rewrite ! Z2Nat.id. lia.
    apply Zmult_le_reg_r with (p:=8). lia.
    rewrite Z.mul_add_distr_r. rewrite <- Xeq, <- X'eq.
    generalize (align_le (Linear.fn_stacksize f) 8). lia.
    apply Zmult_le_reg_r with (p:=8). lia. rewrite <- Xeq; lia.
  }
  {
    split; apply Z2Nat.inj_le; try lia.
    - apply Zmult_le_reg_r with (p:=8). lia. 
      rewrite Z.mul_add_distr_r. rewrite <- Xeq, <- X'eq.
      rewrite sizes in FSD.
      generalize (align_le (Linear.fn_stacksize f) 8). lia.
    - cut (0 <= X'). lia.
      apply Zmult_le_reg_r with (p:=8). lia.
      generalize (align_le (Linear.fn_stacksize f) 8). lia.
    - apply Zmult_le_reg_r with (p:=8). lia. 
      rewrite Z.mul_add_distr_r. rewrite <- Xeq, <- X'eq.
      rewrite sizes in FSD.
      generalize (align_le (Linear.fn_stacksize f) 8). lia.
    - apply Zmult_le_reg_r with (p:=8). lia.
      rewrite <- Yeq.
      rewrite <- box_span_ma_3. lia.
      apply Zle_ge, size_pos.
    - apply Zmult_le_reg_r with (p:=8). lia. 
      rewrite Z.mul_add_distr_r. rewrite <- Xeq, <- X'eq, <- Yeq.
      rewrite <- ! box_span_ma_3.
      rewrite sizes in FSD.
      rewrite box_span_mul in FSD.
      rewrite Z2Nat.id in FSD. 2: lia. 2: lia. lia.
      apply Zle_ge, size_pos. lia.
  }
  assert (PERM: frame_perm_freeable m2' sp').
  {
    red; intros.
    eapply Mem.perm_alloc_2; eauto.
    rewrite Z2Nat.id by lia. rewrite Z.mul_comm.
    rewrite <- Yeq. generalize (align_le (fe_size fe) 8); lia.  
  }
  (* Store of parent *)
  exploit (store_index_succeeds m2' sp' FI_link parent). red; auto. auto. 
  intros [m3' STORE2].
  (* Store of retaddr *)
  exploit (store_index_succeeds m3' sp' FI_retaddr ra). red; auto. red; eauto with mem.
  intros [m4' STORE3].
  (* Saving callee-save registers *)
  assert (PERM4: frame_perm_freeable m4' sp').
    red; intros. eauto with mem. 
  exploit save_callee_save_correct. 
    instantiate (1 := rs1). instantiate (1 := call_regs ls). instantiate (1 := j').
    subst rs1. apply agree_regs_undef_regs. 
    apply agree_regs_call_regs. eapply agree_regs_inject_incr; eauto.
    intros. apply undef_regs_type. simpl. apply WTREGS.
    eexact PERM4.
  rewrite <- LS1.
  intros [rs' [m5' [STEPS [ICS [FCS [OTHERS [STORES [PERM5 [AGREGS' SDYN]]]]]]]]].
  (* stores in frames *)
  assert (SIF: stores_in_frame sp' m2' m5').
    econstructor; eauto. 
    rewrite size_type_chunk. apply offset_of_index_disj_stack_data_2; auto. red; auto.
    econstructor; eauto.
    rewrite size_type_chunk. apply offset_of_index_disj_stack_data_2; auto. red; auto.
  (* Conclusions *)
    rewrite unfold_transf_function in *.
    unfold fn_stacksize in *.

    exists j', rs', m2', sp', m3', m4', m5'.
    rewrite Z2Nat.id in ALLOC'.
    rewrite Z.mul_comm in ALLOC'.
    rewrite <- Yeq in ALLOC'.
    rewrite ma_3. change (two_power_nat 3) with 8.
    rewrite Align.align_align by lia.
    rewrite ALLOC'. 
    repSplit; auto.
  - (* store parent *)
    change AST.Tint with (type_of_index FI_link). 
    change (fe_ofs_link fe) with (offset_of_index fe FI_link).
    apply store_stack_succeeds; auto. red; auto.
  - (* store retaddr *)
    change AST.Tint with (type_of_index FI_retaddr). 
    change (fe_ofs_retaddr fe) with (offset_of_index fe FI_retaddr).
    apply store_stack_succeeds; auto. red; auto.
  - (* saving of registers *)
    eexact STEPS.
  - (* agree frame *)
    constructor; intros.
    + (* unused regs *)
    assert (~In r destroyed_at_call). 
      red; intros; elim H; apply caller_save_reg_within_bounds; auto.
      rewrite LS1. rewrite LTL_undef_regs_others. unfold call_regs. 
      apply AGCS; auto. red; intros; elim H0. 
      apply destroyed_at_function_entry_caller_save; auto.
    + (* locals *)
      rewrite LS1. rewrite LTL_undef_regs_slot. unfold call_regs. 
      apply index_contains_inj_undef; auto with stacking.
    + (* outgoing *)
      rewrite LS1. rewrite LTL_undef_regs_slot. unfold call_regs. 
      apply index_contains_inj_undef; auto with stacking.
    + (* incoming *)
      rewrite LS1. rewrite LTL_undef_regs_slot. unfold call_regs.
      apply AGCS; auto. 
    + (* parent *)
      apply OTHERS; auto. red; auto.
      eapply gso_index_contains; eauto. red; auto.
      eapply gss_index_contains'; eauto. red; auto.
      red; auto.
    + (* retaddr *)
      apply OTHERS; auto. red; auto.
      eapply gss_index_contains'; eauto. red; auto.
    + (* int callee save *) 
      assert (~In r destroyed_at_call).
      {
        red; intros. eapply int_callee_save_not_destroyed; eauto.
      }
      exploit ICS; eauto. rewrite LS1. rewrite LTL_undef_regs_others. unfold call_regs.
      rewrite AGCS; auto. 
      red; intros; elim H1. apply destroyed_at_function_entry_caller_save; auto.
    + (* float callee save *)
      assert (~In r destroyed_at_call). 
      red; intros. eapply float_callee_save_not_destroyed; eauto.
      exploit FCS; eauto. rewrite LS1. rewrite LTL_undef_regs_others. unfold call_regs.
      rewrite AGCS; auto. 
      red; intros; elim H1. apply destroyed_at_function_entry_caller_save; auto.
    + (* inj *)
      rewrite j'SUBSPEC. f_equal. rewrite Z2Nat.id by lia. rewrite Xeq. f_equal. lia. 
    + subst. destr_in H.
      eapply Mem.valid_block_inject_2 in H; eauto.
      eapply Mem.fresh_block_alloc in H; eauto. des H.
      
    + rewrite <- (MemReserve.reserve_bounds_of_block _ _ _ _ AB).
      erewrite Mem.bounds_of_block_alloc; eauto. rewrite Z.max_r; auto.
    +
      rewrite <- (stores_in_frame_bounds _ _ _ SIF).
      erewrite Mem.bounds_of_block_alloc; eauto. rewrite Z.max_r; auto.
      f_equal.
      rewrite unfold_transf_function. reflexivity.
      etransitivity. 2: apply align_le. apply size_pos. lia.
    + red. rewrite <- (MemReserve.reserve_nextblock _ _ _ AB).
      eapply Mem.valid_new_block; eauto.
    + (* valid sp' *)
      eapply stores_in_frame_valid with (m := m2'); eauto with mem.

    + erewrite <- MemReserve.reserve_is_dynamic_block. 2: eauto.
      rewrite <- Mem.is_block_dynamic_alloc. 2: eauto.
      unfold Mem.is_dynamic_block; rewrite Mem.blocktype_valid. destr.
      eapply Mem.fresh_block_alloc; eauto. 
    + rewrite <- SDYN. rewrite <- Genv.store_dyn. 2: eauto.
      rewrite <- Genv.store_dyn. 2: eauto. 
      rewrite <- Mem.is_block_dynamic_alloc. 2: eauto.
      unfold Mem.is_dynamic_block; rewrite Mem.blocktype_valid. destr.
      eapply Mem.fresh_block_alloc; eauto.
    + (* bounds *)
      assert (Mem.perm m11 sp ofs Max p).
      unfold MemReserve.reserve_boxes in AB; destr_in AB; inv AB. unfold Mem.perm in *; simpl in *. eauto.
      exploit Mem.perm_alloc_inv.
      eexact ALLOC. eauto. rewrite dec_eq_true. auto.
    + (* perms *)
      auto.
  - (* separated *)
    subst. red; intros.
    destr_in H0. inv H0.
    split. eapply Mem.fresh_block_alloc; eauto.
    eapply Mem.fresh_block_alloc; eauto.
  - (* inject *)
    
    eapply inj_sif_ifu; eauto. 
    + subst.
      intros b0 delta o k0 p INJ DELTA EXPERM.
      destr_in INJ. inv INJ.
      rewrite Z2Nat.id in DELTA by lia.
      rewrite Z.mul_comm in DELTA. rewrite <- Xeq in DELTA.
      destruct DELTA. lia.
      cut (Mem.perm m11 sp o k0 p). clear EXPERM; intro EXPERM.
      apply Mem.perm_bounds in EXPERM.
      unfold Mem.in_bound_m in EXPERM.
      rewrite (Mem.bounds_of_block_alloc _ _ _ _ _ _ ALLOC) in EXPERM. 
      destruct EXPERM. simpl in *. lia. 
      unfold MemReserve.reserve_boxes in AB; destr_in AB; inv AB. unfold Mem.perm in *; simpl in *. eauto.
      eapply Mem.valid_block_inject_2 in INJ; eauto.
      eapply Mem.fresh_block_alloc in INJ; eauto.
    + subst.
      intros b0 delta INJ DELTA.
      destr_in INJ. inv INJ.
      rewrite Z2Nat.id by lia.
      rewrite Z.mul_comm, <- Xeq. split; auto.
      rewrite <- (MemReserve.reserve_bounds_of_block _ _ _ _ AB).
      rewrite (Mem.bounds_of_block_alloc _ _ _ _ _ _ ALLOC). f_equal. apply Z.max_r. lia.
      eapply Mem.valid_block_inject_2 in INJ; eauto.
      eapply Mem.fresh_block_alloc in INJ; eauto.
      destr.
  - unfold Mem.all_blocks_injected.
    intros ? b0 lo hi Bnd Nn.
    destruct (j b0) eqn:?. destruct p. apply INCR in Heqo. congruence.
    rewrite <- (MemReserve.reserve_bounds_of_block _ _ _ _ AB) in Bnd.
    rewrite (Mem.bounds_of_block_alloc_eq _ _ _ _ _ _ ALLOC) in Bnd.
    destr_in Bnd. destr.
    destr_in Bnd. 2: inv Bnd; lia.
    eapply H. eauto. eauto.
  - lia.
Qed.

(** The following lemmas show the correctness of the register reloading
  code generated by [reload_callee_save]: after this code has executed,
  all callee-save registers contain the same values they had at
  function entry. *)

Section RESTORE_CALLEE_SAVE.

Variable bound: frame_env -> Z.
Variable number: mreg -> Z.
Variable mkindex: Z -> frame_index.
Variable ty: typ.
Variable csregs: list mreg.
Variable j: meminj.
Variable cs: list stackframe.
Variable fb: block.
Variable sp: block.
Variable ls0: locset.
Variable m: mem.

Hypothesis mkindex_valid:
  forall r, In r csregs -> number r < bound fe -> index_valid (mkindex (number r)).
Hypothesis mkindex_typ:
  forall z, type_of_index (mkindex z) = ty.
Hypothesis number_within_bounds:
  forall r, In r csregs ->
  (number r < bound fe <-> mreg_within_bounds b r).
Hypothesis mkindex_val:
  forall r,
  In r csregs -> number r < bound fe ->
  index_contains_inj j m sp (mkindex (number r)) (ls0 (R r)).

Definition agree_unused (ls0: locset) (rs: regset) : Prop :=
  forall r, ~(mreg_within_bounds b r) -> expr_inj_se j (ls0 (R r)) (rs r).

Lemma restore_callee_save_regs_correct:
  forall l rs k,
  incl l csregs ->
  list_norepet l -> 
  agree_unused ls0 rs ->
  exists rs',
    star step tge
      (State cs fb (Eval (Vptr sp Int.zero))
        (restore_callee_save_regs bound number mkindex ty fe l k) rs m)
   E0 (State cs fb (Eval (Vptr sp Int.zero)) k rs' m)
  /\ (forall r, In r l -> expr_inj_se j (ls0 (R r)) (rs' r))
  /\ (forall r, ~(In r l) -> same_eval (rs' r) (rs r))
  /\ agree_unused ls0 rs'.
Proof.
  induction l; intros; simpl restore_callee_save_regs.
  - (* base case *)
    (exists rs). intuition. apply star_refl.
  - (* inductive case *)
    assert (R0: In a csregs) by (apply H; auto with coqlib).
    assert (R1: incl l csregs) by eauto with coqlib.
    assert (R2: list_norepet l) by (inversion H0; auto).
    unfold restore_callee_save_reg.
    destruct (zlt (number a) (bound fe)).
    + exploit (mkindex_val a); auto. intros [v [X Y]]. 
      exploit index_contains_load_stack. eexact X. intros (v'0 & LD & LS).
      set (rs1 := Regmap.set a v'0 rs).
      exploit (IHl rs1 k); eauto.
      * red; intros. unfold rs1. unfold Regmap.set. destruct (RegEq.eq r a).
        subst r. eapply expr_inj_se_se. apply Y. congruence. auto. 
      * intros [rs' [A [B [C D ]]]].
        eexists.
        { repSplit.
          -
            eapply star_left. 
            constructor. rewrite <- (mkindex_typ (number a)). eauto.
            eexact A.
            traceEq.
          - intros. destruct H2.
            + subst r.
              apply (expr_inj_se_se j _ v); auto.
              rewrite C.  unfold rs1. rewrite Regmap.gss. congruence. 
              inv H0; auto.
            + eapply expr_inj_se_se.
              apply B. auto. reflexivity. 
          - intros. simpl in H2.
            apply Classical_Prop.not_or_and in H2. destr_and.
            specialize (C _ H4).
            rewrite C. unfold rs1.
            rewrite Regmap.gso. reflexivity. auto.
          - red; intros. eapply expr_inj_se_se. apply D; auto. reflexivity. 
        }
    + (* no load takes place *)
      exploit (IHl rs k); auto.
      intros [rs' [A [B [C D]]]].
      exists rs'. repSplit.
      * assumption.
      * intros. destruct H2. subst r. apply D. 
        rewrite <- number_within_bounds. auto. auto. auto.
      * intros. simpl in H2. apply C. tauto.
      * auto.
Qed.

End RESTORE_CALLEE_SAVE.


Lemma index_contains_mem_equiv:
  forall m m' (ME: MemRel.mem_equiv m m') sp i v
    (IC: index_contains m sp i v),
    index_contains m' sp i v.
Proof.
  intros.
  inv IC.
  destruct  (MemRel.mem_rel_load _ wf_mr_se _ _ _ _ _ _ ME H0) as [vv [A B]].
  econstructor; auto. rewrite A. eauto. congruence.
Qed.

Lemma index_contains_inj_mem_equiv:
  forall m m' (ME: MemRel.mem_equiv m m') j sp i v
    (ICI: index_contains_inj j m sp i v),
    index_contains_inj j m' sp i v.
Proof.
  intros.
  inv ICI. destr_and.
  econstructor. split.
  eapply index_contains_mem_equiv; eauto.
  auto.
Qed.



Lemma frame_perm_freeable_rel:
  forall m m' mr (ME: MemRel.mem_rel mr m m') b
    (VB: frame_perm_freeable m b),
    frame_perm_freeable m' b.
Proof.
  red; intros.
  erewrite <- MemRel.perm_rel; eauto.
Qed.


Lemma rel_bt:
  forall m m' mr (ME: MemRel.mem_rel mr m m') b,
    Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b.
Proof.
  unfold Mem.is_dynamic_block.
  intros; inv ME. rewrite mem_blocktype_eq; tauto.
Qed.

Lemma agree_frame_mem_equiv:
  forall m m' (ME: MemRel.mem_equiv m m')
    j ls ls0 m1 sp sp' parent retaddr
    (AGF: agree_frame j ls  ls0 m1 sp m sp' parent retaddr),
    agree_frame j ls  ls0 m1 sp m' sp' parent retaddr.
Proof.
  intros.
  inv AGF.
  econstructor; intros; eauto;
  try solve [eapply index_contains_inj_mem_equiv; eauto];
  try solve [eapply index_contains_mem_equiv; eauto].
  rewrite <- agree_sp'_bounds0.
  unfold Mem.bounds_of_block.
  inv ME. rewrite mem_blocksize_eq. auto.
  eapply MemRel.valid_block_rel; eauto.
  rewrite <- rel_bt; eauto.
  eapply frame_perm_freeable_rel; eauto.
Qed.

Lemma restore_callee_save_correct:
  forall j ls ls0 m sp m' sp' pa ra cs fb rs k,
  agree_frame j ls ls0 m sp m' sp' pa ra ->
  agree_unused j ls0 rs ->
  exists rs',
    star step tge
       (State cs fb (Eval (Vptr sp' Int.zero)) (restore_callee_save fe k) rs m')
    E0 (State cs fb (Eval (Vptr sp' Int.zero)) k rs' m')
  /\ (forall r, 
        In r int_callee_save_regs \/ In r float_callee_save_regs -> 
        expr_inj_se j (ls0 (R r)) (rs' r))
  /\ (forall r, 
        ~(In r int_callee_save_regs) ->
        ~(In r float_callee_save_regs) ->
        same_eval (rs' r) (rs r)).
Proof.
  intros. 
  exploit (restore_callee_save_regs_correct 
             fe_num_int_callee_save
             index_int_callee_save
             FI_saved_int
             Tany32
             int_callee_save_regs
             j cs fb sp' ls0 m'); auto.
  - intros. unfold mreg_within_bounds. split; intros.
    + split; auto. destruct (zlt (index_float_callee_save r) 0).
      * generalize (bound_float_callee_save_pos b). omega. 
      * eelim int_float_callee_save_disjoint. eauto. 
        eapply index_float_callee_save_pos2. eauto. auto.
    + destruct H2; auto. 
  - eapply agree_saved_int; eauto. 
  - apply incl_refl.
  - apply int_callee_save_norepet.
  - eauto.
  - intros [rs1 [A [B [C D]]]].
    exploit (restore_callee_save_regs_correct 
               fe_num_float_callee_save
               index_float_callee_save
               FI_saved_float
               Tany64
               float_callee_save_regs
               j cs fb sp' ls0 m'); auto.
    + intros. unfold mreg_within_bounds. split; intros.
      * split; auto. destruct (zlt (index_int_callee_save r) 0).
        generalize (bound_int_callee_save_pos b). omega. 
        eelim int_float_callee_save_disjoint. 
        eapply index_int_callee_save_pos2. eauto. eauto. auto.
      * destruct H2; auto. 
    + eapply agree_saved_float; eauto.
    + apply incl_refl.
    + apply float_callee_save_norepet.
    + eexact D.
    + intros [rs2 [P [Q [R S]]]].
      exists rs2.
      repSplit.
      * unfold restore_callee_save. eapply star_trans. eauto.
        simpl in P. eexact P.  auto.
      * intros. destruct H1.
        eapply expr_inj_se_se. apply B; auto. rewrite R; auto. reflexivity.
        apply Q; auto.
      * intros.
        rewrite R; auto.
Qed.

(** As a corollary, we obtain the following correctness result for
  the execution of a function epilogue (reloading of used callee-save
  registers + reloading of the link and return address + freeing
  of the frame). *)


Lemma agree_frame_inj_sp:
  forall j ls ls0 m sp m' sp' pa ra
    (AGFR: agree_frame j ls ls0 m sp m' sp' pa ra)
    b delta
    (INJ: j b = Some (sp', delta)),
    b = sp.
Proof.
  intros.
  inv AGFR. eauto.
Qed.

Lemma function_epilogue_correct:
  forall j ls ls0 m sp m' sp' pa ra cs fb rs k m11 m1
    (ABI: Mem.all_blocks_injected j m)
    (AGREGS: agree_regs j ls rs)
    (AGFR: agree_frame j ls ls0 m sp m' sp' pa ra)
    (MINJ: Mem.inject true expr_inj_se j m m')
    (FR: Mem.free m sp 0 f.(Linear.fn_stacksize) = Some m11)
    (FL: MemReserve.release_boxes m11 (needed_stackspace (Linear.fn_id f)) = Some m1)
    (mi_size_mem: (Mem.nb_boxes_used_m m - needed_stackspace (Linear.fn_id f) -
                   Mem.box_span (align (Z.max 0 (Linear.fn_stacksize f)) 8) >=
                   Mem.nb_boxes_used_m m' - Mem.box_span (align (Z.max 0 (fn_stacksize tf)) 8))%nat),
  exists rs1 m1', 
    (exists pa',
       load_stack m' (Eval (Vptr sp' Int.zero)) AST.Tint tf.(fn_link_ofs) = Some pa' /\
       same_eval pa pa')
    /\ (exists ra',
          load_stack m' (Eval (Vptr sp' Int.zero)) AST.Tint tf.(fn_retaddr_ofs) = Some ra' /\
          same_eval ra ra')
    /\ Mem.free m' sp' 0 tf.(fn_stacksize) = Some m1'
    /\ star step tge
            (State cs fb (Eval (Vptr sp' Int.zero)) (restore_callee_save fe k) rs m')
            E0 (State cs fb (Eval (Vptr sp' Int.zero)) k rs1 m')
    /\ agree_regs j (return_regs ls0 ls) rs1
    /\ agree_callee_save (return_regs ls0 ls) ls0
    /\ Mem.inject true expr_inj_se j m1 m1'.
Proof.
  intros.
  (* can free *)
  destruct (Mem.range_perm_free m' sp' 0 ((fn_stacksize tf))) as [m1' FREE].
  {
    rewrite unfold_transf_function; unfold fn_stacksize. red; intros.
    assert (EITHER: fe_stack_data fe <= ofs < fe_stack_data fe + Linear.fn_stacksize f
                    \/ (ofs < fe_stack_data fe \/ fe_stack_data fe + Linear.fn_stacksize f <= ofs))
      by lia.
    destruct EITHER.
    + replace ofs with ((ofs - fe_stack_data fe) + fe_stack_data fe) by lia.
      eapply Mem.perm_inject with (f := j). eapply agree_inj; eauto. eauto. 
      eapply Mem.free_range_perm; eauto. lia. 
    + eapply agree_perm; eauto.
  } 
  {
    unfold Mem.has_bounds; inv AGFR. rewrite agree_sp'_bounds0.
    rewrite andb_if. repeat destruct zeq; try lia. reflexivity.
  }
  - (* inject after free *)
    assert (INJ1: Mem.inject true expr_inj_se j m1 m1').
    {
      inversion MINJ; constructor; eauto with mem.
      - inversion mi_inj; constructor; eauto.
        + intros b1 b2 delta ofs k0 p INJ PERM.
          rewrite <- release_perm in PERM. 2: eauto.
          eapply perm_free_eq in PERM; eauto.
          destruct PERM as [PERM NB1].
          generalize (mi_perm _ _ _ _ _ _ INJ PERM).
          eapply Mem.perm_free_1; eauto.
          destruct (eq_block b2 sp'); auto.
          subst. right.
          exploit (agree_frame_inj_sp). eauto. eauto. destr.
        + intros b1 b2 delta ofs INJ IB.
          red in IB. rewrite <- (MemReserve.release_bounds_of_block _ _ _ _ FL) in IB.
          unfold Mem.in_bound_m in *.
          erewrite Mem.free_bounds_exact in IB; eauto.
          erewrite Mem.free_bounds_exact; eauto.
          destruct (eq_block sp b1).
          unfold in_bound in IB; simpl in IB; lia.
          generalize IB; intro IB'. eapply mi_bounds in IB; eauto.
          destr. subst.
          eapply agree_frame_inj_sp in INJ; eauto.
          destr. 
        + intros b0 b1 z INJ.
          rewrite <- (Mem.mask_free _ _ _ _ _ FREE).
          rewrite <- (MemReserve.release_mask _ _ _ _ FL).
          rewrite <- (Mem.mask_free _ _ _ _ _ FR).
          eauto.
        + intros b1 ofs b2 delta INJ PERM.
          rewrite (Mem.free_contents _ _ _ _ _ FREE).
          subst.
          replace (Mem.mem_contents m1) with (Mem.mem_contents m11).
          rewrite (Mem.free_contents _ _ _ _ _ FR).
          eapply mi_memval; eauto.
          rewrite <- release_perm in PERM by eauto.
          eapply perm_free_eq in PERM. 2: eauto.
          destr_and. eauto. 
          * unfold MemReserve.release_boxes in FL; destr_in FL; inv FL; reflexivity.
        +
          intros. trim mi_size_mem0. auto.
          replace (Mem.nb_boxes_used_m m1) with (Mem.nb_boxes_used_m m11 - needed_stackspace (Linear.fn_id f))%nat.

revert mi_size_mem.
rewrite <- (free_nb_boxes_used' _ _ _ _ _ FR).
rewrite <- (free_nb_boxes_used' _ _ _ _ _ FREE).
rewrite ! Z.sub_0_r.
rewrite <- box_span_ma_3.
rewrite box_span_mul.
rewrite Nat2Z.id.
rewrite <- box_span_ma_3.
rewrite box_span_mul.
rewrite Nat2Z.id.
rewrite ! Z.max_r. lia.
des tf; auto.
clear. des f; auto.
lia.
apply Z.le_ge. apply Z.le_max_l. lia.
apply Z.le_ge. apply Z.le_max_l.
rewrite (release_nb_boxes_used _ _ _ FL). lia.
      - intros; eapply mi_freeblocks; eauto with mem.
        intro.
        eapply Mem.valid_block_free_1 in H0; try eassumption.
        red in H0.
        rewrite (MemReserve.release_nextblock _ _ _ FL) in H0. apply H; auto.
      - red; intros.
        red in H2, H3.
        rewrite <- (MemReserve.release_bounds_of_block _ _ _ _ FL) in H2.
        rewrite <- (MemReserve.release_bounds_of_block _ _ _ _ FL) in H3.
        destruct (Mem.free_bounds' _ _ _ _ _ b1 FR).
        destruct (Mem.free_bounds' _ _ _ _ _ b2 FR).
        rewrite H4, H5 in *.
        eapply mi_no_overlap'; eauto.
        rewrite H5 in *; unfold in_bound in *; simpl in *; lia.
        rewrite H4 in *; unfold in_bound in *; simpl in *; lia.
      - subst. intros.
        erewrite <- (MemReserve.release_is_dynamic_block _ _ _ _ FL).
        erewrite <- (MemReserve.release_bounds_of_block _ _ _ _ FL).
        rewrite (Mem.is_block_dynamic_free _ _ _ _ _ _ FREE).
        rewrite (Mem.is_block_dynamic_free _ _ _ _ _ _ FR).
        specialize (mi_inj_dynamic _ _ _ H); repSplit; destr.
        intros. des mi_inj_dynamic. des a. trim a0. auto. des a0. split; auto.
        rewrite (Mem.free_bounds_exact _ _ _ _ _ FR),
        (Mem.free_bounds_exact _ _ _ _ _ FREE). rewrite e1.
        destr. destr. subst.
        inv AGFR; destr. destr. subst.
        inv AGFR; destr.
    }
  (* can execute epilogue *)
  exploit restore_callee_save_correct; eauto.
    instantiate (1 := rs). red; intros. 
    rewrite <- (agree_unused_reg _ _ _ _ _ _ _ _ _ AGFR). auto. auto. 
  intros [rs1 [A [B C]]]. 
  (* conclusions *)
  exists rs1; exists m1'.
  repSplit.
    + rewrite unfold_transf_function; unfold fn_link_ofs.
      generalize  (index_contains_load_stack _ _ _ _  (agree_link _ _ _ _ _ _ _ _ _ AGFR)).
      simpl. auto. intros [v' [E F]]; rewrite E; eexists; split; eauto.
      congruence.
    + rewrite unfold_transf_function; unfold fn_link_ofs.
      generalize  (index_contains_load_stack _ _ _ _  (agree_retaddr _ _ _ _ _ _ _ _ _ AGFR)).
      simpl; intros [v' [E F]]; rewrite E; eexists; split; eauto.
      congruence.
    + auto.
    + eexact A. 
    + red; intros. unfold return_regs.
      generalize (register_classification r) (int_callee_save_not_destroyed r) (float_callee_save_not_destroyed r); intros.
      destruct (in_dec mreg_eq r destroyed_at_call). 
      * eapply expr_inj_se_se. apply AGREGS. rewrite C. congruence. intuition. intuition.
      * apply B. intuition. 
    + apply agree_callee_save_return_regs.
    + auto.
Qed.

End FRAME_PROPERTIES.

(** * Call stack invariant *)

Inductive match_globalenvs (j: meminj) (bound: block) : Prop :=
  | match_globalenvs_intro
      (DOMAIN: forall b, Plt b bound -> j b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, j b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).
 
Inductive match_stacks (j: meminj) (m m': mem): 
       list Linear.stackframe -> list stackframe -> signature -> block -> block -> Prop :=
  | match_stacks_empty: forall sg hi bound bound',
      Ple hi bound -> Ple hi bound' -> match_globalenvs j hi ->
      tailcall_possible sg ->
      match_stacks j m m' nil nil sg bound bound'
  | match_stacks_cons: forall f sp ls c cs fb sp' ra c' cs' sg bound bound' trf
        (TAIL: is_tail c (Linear.fn_code f))
        (FINDF: Genv.find_funct_ptr tge fb = Some (Internal trf))
        (TRF: transf_function f = OK trf)
        (TRC: transl_code (make_env (function_bounds f)) c = c')
        (TY_RA: wt ra AST.Tint)
        (FRM: agree_frame f trf j ls (parent_locset cs) m sp m' sp' (parent_sp cs') (parent_ra cs'))
        (ARGS: forall ofs ty,
           In (S Outgoing ofs ty) (loc_arguments sg) ->
           slot_within_bounds (function_bounds f) Outgoing ofs ty)
        (STK: match_stacks j m m' cs cs' (Linear.fn_sig f) sp sp')
        (BELOW: Plt sp bound)
        (BELOW': Plt sp' bound'),
      match_stacks j m m'
                   (Linear.Stackframe f (Eval (Vptr sp Int.zero)) ls c :: cs)
                   (Stackframe fb (Eval (Vptr sp' Int.zero)) ra c' :: cs')
                   sg bound bound'.

(** Invariance with respect to change of bounds. *)

Lemma match_stacks_change_bounds:
  forall j m1 m' cs cs' sg bound bound',
  match_stacks j m1 m' cs cs' sg bound bound' ->
  forall xbound xbound',
  Ple bound xbound -> Ple bound' xbound' ->
  match_stacks j m1 m' cs cs' sg xbound xbound'.
Proof.
  induction 1; intros. 
  apply match_stacks_empty with hi; auto. apply Ple_trans with bound; eauto. apply Ple_trans with bound'; eauto. 
  econstructor; eauto.
  eapply Plt_le_trans; eauto.
  eapply Plt_le_trans; eauto. 
Qed.

(** Invariance with respect to change of [m]. *)

(** A variant of the latter, for use with external calls *)

Hypothesis stackspace_ok:
  forall f tf (TF: transf_function f = OK tf)
    b (GFF: Genv.find_funct_ptr tge b = Some (Internal tf)) ,
  (Mem.box_span (Linear.fn_stacksize f) + needed_stackspace (Linear.fn_id f) =
   Mem.box_span (fe_size (make_env (function_bounds f))))%nat.

Lemma stackspace_ok':
  forall f tf (TF: transf_function f = OK tf)
    b (GFF: Genv.find_funct_ptr tge b = Some (Internal tf)) ,
    align (Linear.fn_stacksize f) 8 + 8*Z.of_nat (needed_stackspace (Linear.fn_id f))
    = fn_stacksize tf.
Proof.
  intros.
  erewrite (unfold_transf_function f tf); eauto.
  Opaque fe_size make_env Z.mul.
  simpl.
  rewrite <- ! box_span_ma_3. exploit stackspace_ok; eauto. lia.
  clear. set (b:=function_bounds f).
  generalize (frame_env_separated (function_bounds f)). intuition.
  generalize (bound_local_pos b); intro;
  generalize (bound_int_callee_save_pos b); intro;
  generalize (bound_float_callee_save_pos b); intro;
  generalize (bound_outgoing_pos b); intro;
  generalize (bound_stack_data_pos b); intro.
  repeat destr_and. unfold b in *.
  lia. des f; lia. 
Qed.

Lemma stackspace:
  forall f tf (TF: transf_function f = OK tf)
    b (GFF: Genv.find_funct_ptr tge b = Some (Internal tf)) ,
   align (Linear.fn_stacksize f) 8 + 8*Z.of_nat (needed_stackspace (Linear.fn_id f)) =
   align (fe_size (make_env (function_bounds f))) 8.
Proof.
  intros.
  erewrite stackspace_ok'; eauto.
  erewrite (unfold_transf_function f tf); eauto.
Qed.

Lemma match_stacks_change_meminj:
  forall j j' m m' m1 m1',
  inject_incr j j' ->
  inject_separated j j' m1 m1' ->
  forall cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  Ple bound' (Mem.nextblock m1') ->
  match_stacks j' m m' cs cs' sg bound bound'.
Proof.
  induction 3; intros.
  apply match_stacks_empty with hi; auto.
  inv H3. constructor; auto.
  intros. red in H0. case_eq (j b1).
  intros [b' delta'] EQ. rewrite (H _ _ _ EQ) in H3. inv H3. eauto.
  intros EQ. exploit H0; eauto. intros [A B]. elim B. red.
  apply Plt_le_trans with hi. auto. apply Ple_trans with bound'; auto.
  econstructor; eauto. 
  eapply agree_frame_inject_incr; eauto. red. eapply Plt_le_trans; eauto. 
  intros; intro; subst. generalize (H0 _ _ _ H3 H4).
  intros [A B]. apply B.
  red; destruct FRM. xomega.
  apply IHmatch_stacks. apply Ple_trans with bound'; auto. apply Plt_Ple; auto.
Qed.

Lemma match_stacks_change_mem_extcall:
  forall j m1 m2 m1' m2' cs cs' sg bound bound'
    (ms: match_stacks j m1 m1' cs cs' sg bound bound')
    (inj_glob: meminj_preserves_globals ge j)
    j' (INCR: inject_incr j j')
    (SEP: inject_separated j j' m1 m1')
    (UNCH1: forall b o, Mem.valid_block m1 b -> loc_not_writable m1 b o ->
       Maps.ZMap.get o (Maps.PMap.get b (Mem.mem_contents m1)) =
       Maps.ZMap.get o (Maps.PMap.get b (Mem.mem_contents m2)))
    (UNCH: Mem.unchanged_on (loc_out_of_reach j m1) m1' m2')
    (ABI: Mem.all_blocks_injected j m1)
    (MINJ: Mem.inject true expr_inj_se j m1 m1')
    (PERM: forall b, Mem.valid_block m1 b -> ~ Mem.is_dynamic_block m1 b ->
                forall k p ofs, (Mem.perm m1 b ofs k p <-> Mem.perm m2 b ofs k p))
    (PERM': forall b, Mem.valid_block m1' b -> ~ Mem.is_dynamic_block m1' b ->
                forall k p ofs, (Mem.perm m1' b ofs k p <-> Mem.perm m2' b ofs k p))
    (BND: forall b, Mem.valid_block m1 b -> ~ Mem.is_dynamic_block m1 b ->
               Mem.bounds_of_block m1 b = Mem.bounds_of_block m2 b)
    (BND': forall b, Mem.valid_block m1' b -> ~ Mem.is_dynamic_block m1' b ->
                Mem.bounds_of_block m1' b = Mem.bounds_of_block m2' b)
    (DYN: forall b : block,
        Mem.valid_block m1 b ->
        (Mem.is_dynamic_block m1 b <-> Mem.is_dynamic_block m2 b))
    (DYN': forall b : block,
        Mem.valid_block m1' b ->
        (Mem.is_dynamic_block m1' b <-> Mem.is_dynamic_block m2' b))     
  ,
    Ple bound (Mem.nextblock m1) ->
    Ple bound' (Mem.nextblock m1') ->
    Ple (Mem.nextblock m1) (Mem.nextblock m2) ->
    Ple (Mem.nextblock m1') (Mem.nextblock m2') ->
    match_stacks j' m2 m2' cs cs' sg bound bound'.
Proof.
  induction 1; simpl; intros; eauto.
  - econstructor; eauto.
    inv H1. constructor.
    + intros; eapply INCR; eauto.
    + intros.
      des (j b1).
      * des p. erewrite INCR in H1; eauto. inv H1.   
        eapply IMAGE in Heqo. auto. auto.
      * generalize (SEP _ _ _ Heqo H1).
        intros [A B]. exfalso; apply B. red. xomega.
    + eauto.
    + eauto.
    + eauto.
  - econstructor; eauto.
    2: apply IHms; auto; try xomega.
    clear IHms.
    eapply agree_frame_inject_incr; eauto.
    2: inv FRM; auto.
    2: intros; intro; subst; generalize (SEP _ _ _ H3 H4);
    intros [A B]; exfalso; apply B; inv FRM; auto.
    eapply agree_frame_invariant; eauto.
    + intros.
      exploit (Mem.valid_block_inject_1); eauto. exploit Mem.mi_mappedblocks; eauto. intros.
      exploit (Mem.mi_inj_dynamic); eauto. destr.
    + intros.
      rewrite PERM; tauto.
    + intros.
      rewrite BND; tauto.
    + intros.
      rewrite BND'; tauto.
    + intros. erewrite Mem.load_unchanged_on_1; eauto.
      inv FRM; auto. intros.
      red. intros.
      exploit (agree_inj_cases); eauto.
      destruct (peq b0 sp). subst.
      erewrite agree_inj in H6; eauto. Opaque fe_stack_data.  inversion H6.
      intros _ P; eapply Mem.perm_bounds in P.
      red in P.
      erewrite agree_sp_bounds in P; eauto. red in P. simpl in P. lia.
      destr. 
    + intros.
      rewrite <- PERM'; eauto. eapply Mem.perm_valid_block; eauto.
      inv FRM; auto.
Qed.

Lemma match_stacks_change_mem_extcall':
  forall j m1 m2 m1' m2' cs cs' sg bound bound'
    (ms: match_stacks j m1 m1' cs cs' sg bound bound')
    (inj_glob: meminj_preserves_globals ge j)
    j' (INCR: inject_incr j j')
    (SEP: inject_separated j j' m1 m1')
    ef ef' F V (ge: Genv.t F V) vargs vargs' t t' vres vres'
    (EC1: external_call' ef ge vargs m1 t vres m2)
    (EC2: external_call' ef' ge vargs' m1' t' vres' m2')
    (UNCH: Mem.unchanged_on (loc_out_of_reach j m1) m1' m2')
    (ABI: Mem.all_blocks_injected j m1)
    (MINJ: Mem.inject true expr_inj_se j m1 m1'),
    Ple bound (Mem.nextblock m1) ->
    Ple bound' (Mem.nextblock m1') ->
    match_stacks j' m2 m2' cs cs' sg bound bound'.
Proof.
  intros.
  eapply match_stacks_change_mem_extcall; eauto.
  - inv EC1; eapply external_call_readonly'; eauto.
  - intros; inv EC1; eapply external_call_perm; eauto.
  - intros; inv EC2; eapply external_call_perm; eauto.
  - intros; inv EC1; eapply external_call_bounds_mask; eauto.
  - intros; inv EC2; eapply external_call_bounds_mask; eauto.
  - intros; inv EC1; eapply external_call_dyn; eauto.
  - intros; inv EC2; eapply external_call_dyn; eauto.
  - eapply external_call_nextblock'; eauto.
  - eapply external_call_nextblock'; eauto.
Qed.

(** Invariance with respect to change of [j]. *)

(** Preservation by parallel stores in Linear and Mach. *)


Lemma match_stacks_parallel_stores:
  forall j m m' chunk addr addr' v v' m1 m1',
    Mem.all_blocks_injected j m ->
  Mem.inject true expr_inj_se j m m' ->
  expr_inj_se j addr addr' ->
  Mem.storev chunk m addr v = Some m1 ->
  Mem.storev chunk m' addr' v' = Some m1' ->
  forall cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  match_stacks j m1 m1' cs cs' sg bound bound'.
Proof.
  intros until m1'. intros ABI MINJ VINJ STORE1 STORE2.
  induction 1.
  econstructor; eauto.
  econstructor; eauto.
  eapply agree_frame_parallel_stores; eauto.
Qed.

(** Invariance by external calls. *)

(** Invariance with respect to change of signature *)

Lemma match_stacks_change_sig:
  forall sg1 j m m' cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  tailcall_possible sg1 ->
  match_stacks j m m' cs cs' sg1 bound bound'.
Proof.
  induction 1; intros.
  econstructor; eauto. 
  econstructor; eauto. intros. elim (H0 _ H1).
Qed.

(** [match_stacks] implies [match_globalenvs], which implies [meminj_preserves_globals]. *)

Lemma match_stacks_globalenvs:
  forall j m m' cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  exists hi, match_globalenvs j hi.
Proof.
  induction 1. exists hi; auto. auto.
Qed.

Lemma match_stacks_preserves_globals:
  forall j m m' cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  meminj_preserves_globals ge j.
Proof.
  intros. exploit match_stacks_globalenvs; eauto. intros [hi MG]. inv MG.
  split. eauto. split. eauto. intros. symmetry. eauto. 
Qed.

(** Typing properties of [match_stacks]. *)

Lemma match_stacks_type_sp:
  forall j m m' cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  wt (parent_sp cs') AST.Tint.
Proof.
  induction 1; simpl;
  left; exists AST.Tint; destr.
Qed.

Lemma match_stacks_type_retaddr:
  forall j m m' cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  wt (parent_ra cs') AST.Tint.
Proof.
  induction 1; simpl.
  left; exists AST.Tint; destr. auto.
Qed.

(** * Syntactic properties of the translation *)

(** Preservation of code labels through the translation. *)

Section LABELS.

Remark find_label_fold_right:
  forall (A: Type) (fn: A -> Mach.code -> Mach.code) lbl,
  (forall x k, Mach.find_label lbl (fn x k) = Mach.find_label lbl k) ->  forall (args: list A) k,
  Mach.find_label lbl (List.fold_right fn k args) = Mach.find_label lbl k.
Proof.
  induction args; simpl. auto. 
  intros. rewrite H. auto.
Qed.

Remark find_label_save_callee_save:
  forall fe lbl k,
  Mach.find_label lbl (save_callee_save fe k) = Mach.find_label lbl k.
Proof.
  intros. unfold save_callee_save, save_callee_save_int, save_callee_save_float, save_callee_save_regs.
  repeat rewrite find_label_fold_right. reflexivity.
  intros. unfold save_callee_save_reg. 
  case (zlt (index_float_callee_save x) (fe_num_float_callee_save fe));
  intro; reflexivity.
  intros. unfold save_callee_save_reg.  
  case (zlt (index_int_callee_save x) (fe_num_int_callee_save fe));
  intro; reflexivity.
Qed.

Remark find_label_restore_callee_save:
  forall fe lbl k,
  Mach.find_label lbl (restore_callee_save fe k) = Mach.find_label lbl k.
Proof.
  intros. unfold restore_callee_save, restore_callee_save_int, restore_callee_save_float, restore_callee_save_regs.
  repeat rewrite find_label_fold_right. reflexivity.
  intros. unfold restore_callee_save_reg. 
  case (zlt (index_float_callee_save x) (fe_num_float_callee_save fe));
  intro; reflexivity.
  intros. unfold restore_callee_save_reg. 
  case (zlt (index_int_callee_save x) (fe_num_int_callee_save fe));
  intro; reflexivity.
Qed.

Lemma transl_code_eq:
  forall fe i c, transl_code fe (i :: c) = transl_instr fe i (transl_code fe c).
Proof.
  unfold transl_code; intros. rewrite list_fold_right_eq. auto.
Qed.

Lemma find_label_transl_code:
  forall fe lbl c,
  Mach.find_label lbl (transl_code fe c) =
    option_map (transl_code fe) (Linear.find_label lbl c).
Proof.
  induction c; simpl; intros.
  auto.
  rewrite transl_code_eq. 
  destruct a; unfold transl_instr; auto.
  destruct s; simpl; auto.
  destruct s; simpl; auto.
  rewrite find_label_restore_callee_save. auto.
  simpl. case (peq lbl l); intro. reflexivity. auto.
  rewrite find_label_restore_callee_save. auto.
Qed.

Lemma transl_find_label:
  forall f tf lbl c,
  transf_function f = OK tf ->
  Linear.find_label lbl f.(Linear.fn_code) = Some c ->
  Mach.find_label lbl tf.(Mach.fn_code) = 
    Some (transl_code (make_env (function_bounds f)) c).
Proof.
  intros. rewrite (unfold_transf_function _ _ H).  simpl. 
  unfold transl_body. rewrite find_label_save_callee_save.
  rewrite find_label_transl_code. rewrite H0. reflexivity.
Qed.

End LABELS.

(** Code tail property for Linear executions. *)

Lemma find_label_tail:
  forall lbl c c', 
  Linear.find_label lbl c = Some c' -> is_tail c' c.
Proof.
  induction c; simpl.
  intros; discriminate.
  intro c'. case (Linear.is_label lbl a); intros.
  injection H; intro; subst c'. auto with coqlib.
  auto with coqlib.
Qed.

(** Code tail property for translations *)

Lemma is_tail_save_callee_save_regs:
  forall bound number mkindex ty fe csl k,
  is_tail k (save_callee_save_regs bound number mkindex ty fe csl k).
Proof.
  induction csl; intros; simpl. auto with coqlib.
  unfold save_callee_save_reg. destruct (zlt (number a) (bound fe)). 
  constructor; auto. auto.
Qed.

Lemma is_tail_save_callee_save:
  forall fe k,
  is_tail k (save_callee_save fe k).
Proof.
  intros. unfold save_callee_save, save_callee_save_int, save_callee_save_float.
  eapply is_tail_trans; apply is_tail_save_callee_save_regs.
Qed.

Lemma is_tail_restore_callee_save_regs:
  forall bound number mkindex ty fe csl k,
  is_tail k (restore_callee_save_regs bound number mkindex ty fe csl k).
Proof.
  induction csl; intros; simpl. auto with coqlib.
  unfold restore_callee_save_reg. destruct (zlt (number a) (bound fe)). 
  constructor; auto. auto.
Qed.

Lemma is_tail_restore_callee_save:
  forall fe k,
  is_tail k (restore_callee_save fe k).
Proof.
  intros. unfold restore_callee_save, restore_callee_save_int, restore_callee_save_float.
  eapply is_tail_trans; apply is_tail_restore_callee_save_regs.
Qed.

Lemma is_tail_transl_instr:
  forall fe i k,
  is_tail k (transl_instr fe i k).
Proof.
  intros. destruct i; unfold transl_instr; auto with coqlib.
  destruct s; auto with coqlib.
  destruct s; auto with coqlib.
  eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
  eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
Qed.

Lemma is_tail_transl_code:
  forall fe c1 c2, is_tail c1 c2 -> is_tail (transl_code fe c1) (transl_code fe c2).
Proof.
  induction 1; simpl. auto with coqlib.
  rewrite transl_code_eq. 
  eapply is_tail_trans. eauto. apply is_tail_transl_instr.
Qed.

Lemma is_tail_transf_function:
  forall f tf c,
  transf_function f = OK tf ->
  is_tail c (Linear.fn_code f) ->
  is_tail (transl_code (make_env (function_bounds f)) c) (fn_code tf).
Proof.
  intros. rewrite (unfold_transf_function _ _ H). simpl. 
  unfold transl_body. eapply is_tail_trans. 2: apply is_tail_save_callee_save.
  apply is_tail_transl_code; auto.
Qed.

(** * Semantic preservation *)

(** Preservation / translation of global symbols and functions. *)

Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_symbol_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_var_info_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma functions_translated:
  forall m v f,
  Genv.find_funct m ge v = Some f ->
  exists tf,
  Genv.find_funct m tge v = Some tf /\ transf_fundef f = OK tf.
Proof
  (Genv.find_funct_transf_partial transf_fundef _ TRANSF).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  exists tf,
  Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial transf_fundef _ TRANSF).

Lemma sig_preserved:
  forall f tf, transf_fundef f = OK tf -> Mach.funsig tf = Linear.funsig f.
Proof.
  intros until tf; unfold transf_fundef, transf_partial_fundef.
  destruct f; intros; monadInv H.
  rewrite (unfold_transf_function _ _ EQ). auto. 
  auto.
Qed.

Lemma expr_inj_se_norm:
  forall j m m' (ABI: Mem.all_blocks_injected j m)
         (MINJ: Mem.inject true expr_inj_se j m m')
         v1 v2
         (VINJ: expr_inj_se j v1 v2),
    val_inject j (Mem.mem_norm m v1) (Mem.mem_norm m' v2).
Proof.
  intros j m m' ABI MINJ v1 v2 VINJ.
  generalize (Mem.norm_inject_val' _ _ wf_inj_expr_inj_se _ _ _ _ _ ABI MINJ VINJ).
  auto.
Qed.

Lemma find_function_translated:
  forall j ls rs m m' cs cs' sg bound bound' ros f,
    Mem.all_blocks_injected j m ->
    agree_regs j ls rs ->
    match_stacks j m m' cs cs' sg bound bound' ->
    Linear.find_function ge m ros ls = Some f ->
    Mem.inject true expr_inj_se j m m' ->
    exists bf, exists tf,
                 find_function_ptr m' tge ros rs = Some bf
                 /\ Genv.find_funct_ptr tge bf = Some tf
                 /\ transf_fundef f = OK tf.
Proof.
  intros until f; intros ABI AG MS FF MINJ.
  exploit match_stacks_globalenvs; eauto. intros [hi MG]. 
  destruct ros; simpl in FF.
  exploit Genv.find_funct_inv; eauto. intros [b EQ]. unfold Genv.find_funct in FF. rewrite EQ in FF.
  rewrite pred_dec_true in FF; auto.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl.
  generalize (AG m0). intro VINJ.
  generalize (expr_inj_se_norm _ _ _ ABI MINJ _ _ VINJ).
  rewrite EQ. intro INJ. inv INJ.
  inv MG. rewrite DOMAIN in FB. inv FB. simpl. auto. eapply FUNCTIONS; eauto. 
  destruct (Genv.find_symbol ge i) as [b|] eqn:?; try discriminate. 
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl. 
  rewrite symbols_preserved. auto.
Qed.

(** Preservation of the arguments to an external call. *)

Section EXTERNAL_ARGUMENTS.

Variable j: meminj.
Variables m m': mem.
Variable cs: list Linear.stackframe.
Variable cs': list stackframe.
Variable sg: signature.
Variables bound bound': block.
Hypothesis MS: match_stacks j m m' cs cs' sg bound bound'.
Variable ls: locset.
Variable rs: regset.
Hypothesis AGR: agree_regs j ls rs.
Hypothesis AGCS: agree_callee_save ls (parent_locset cs).

Lemma transl_external_argument:
  forall l,
  In l (loc_arguments sg) ->
  exists v, extcall_arg rs m' (parent_sp cs') l v /\ expr_inj_se j (ls l) v.
Proof.
  intros.
  assert (loc_argument_acceptable l). apply loc_arguments_acceptable with sg; auto.
  destruct l; red in H0.
  exists (rs r); split. constructor. reflexivity. auto. 
  destruct sl; try contradiction.
  inv MS.
  elim (H4 _ H).
  unfold parent_sp.
  assert (slot_valid f Outgoing pos ty = true).
    exploit loc_arguments_acceptable; eauto. intros [A B]. 
    unfold slot_valid. unfold proj_sumbool. rewrite zle_true by omega.
    destruct ty; auto; congruence.
  assert (slot_within_bounds (function_bounds f) Outgoing pos ty).
    eauto.
  exploit agree_outgoing; eauto. intros [v [A B]].
  exploit index_contains_load_stack.  eauto.
  eapply stackspace_ok; eauto. eexact A.
  intros [v' [C D]].
  eexists; split.
  econstructor.  eauto. apply D. auto.
  red in AGCS. rewrite AGCS; auto.
Qed.

Lemma transl_external_arguments_rec:
  forall locs,
  incl locs (loc_arguments sg) ->
  exists vl,
  list_forall2 (extcall_arg rs m' (parent_sp cs')) locs vl /\ expr_list_inject j ls##locs vl.
Proof.
  induction locs; simpl; intros.
  exists (@nil expr_sym); split. constructor. constructor.
  exploit transl_external_argument; eauto with coqlib. intros [v [A B]].
  exploit IHlocs; eauto with coqlib. intros [vl [C D]].
  exists (v :: vl); split; constructor; auto.
Qed.

Lemma transl_external_arguments:
  exists vl,
  extcall_arguments rs m' (parent_sp cs') sg vl /\
  expr_list_inject j (ls ## (loc_arguments sg)) vl.
Proof.
  unfold extcall_arguments. 
  apply transl_external_arguments_rec.
  auto with coqlib.
Qed.

End EXTERNAL_ARGUMENTS.

Inductive size_mem_preserved : list mem -> list mem -> list Linear.stackframe -> list stackframe -> Prop :=
| smp_nil : forall m1 m2
              (smp_size_mem: (Mem.nb_boxes_used_m m1 >= Mem.nb_boxes_used_m m2)%nat),
    size_mem_preserved (m1::nil) (m2::nil) nil nil
| smp_cons_same: forall m1 m2 cs cs' lm1 lm2
                   (smp_rec: size_mem_preserved (m1::lm1) (m2::lm2) cs cs')
                   C C' m1' m2'
                   (sz1: (nb_boxes_dynamic m1' + C' = nb_boxes_dynamic m1 + C)%nat)
                   (sz2: (nb_boxes_dynamic m2' + C' = nb_boxes_dynamic m2 + C)%nat)
                   (st1: (nb_boxes_static m1' = nb_boxes_static m1)%nat)
                   (st2: (nb_boxes_static m2' = nb_boxes_static m2)%nat)
                   (ext1: (Mem.nb_extra m1' = Mem.nb_extra m1)%nat)
                   (ext2: (Mem.nb_extra m2' = Mem.nb_extra m2)%nat),
    size_mem_preserved (m1'::m1::lm1) (m2'::m2::lm2) cs cs'
| smp_cons:
    forall m1 m2 lm1 lm2 cs cs' f sp ls c  fb sp' ra c' tf m1' m2'
      (smp_tf: transf_function f = OK tf)
      (stm1: (nb_boxes_static m1 = nb_boxes_static m1' + Mem.box_span (Z.max 0 (Linear.fn_stacksize f)))%nat)
      (stm2: (nb_boxes_static m2 = nb_boxes_static m2' + Mem.box_span (Z.max 0 (fn_stacksize tf)))%nat)
      (dm1: nb_boxes_dynamic m1 = nb_boxes_dynamic m1')
      (dm2: nb_boxes_dynamic m2 = nb_boxes_dynamic m2')
      (extm1: (Mem.nb_extra m1 = Mem.nb_extra m1' + needed_stackspace (Linear.fn_id f))%nat)
      (extm2: Mem.nb_extra m2 = Mem.nb_extra m2')
      (smp_size_mem: (Mem.nb_boxes_used_m m1 >= Mem.nb_boxes_used_m m2)%nat)
      (smp_rec: size_mem_preserved (m1'::lm1) (m2'::lm2) cs cs'),
      size_mem_preserved (m1::m1'::lm1) (m2::m2'::lm2)
                         (Linear.Stackframe f (Eval (Vptr sp Int.zero)) ls c ::cs) 
                         (Stackframe fb (Eval (Vptr sp' Int.zero)) ra c' ::cs').

Lemma smp_same_size:
  forall lm1 m1 lm2 m2 cs cs' (SMP: size_mem_preserved (m1::lm1) (m2::lm2) cs cs')
    m1' m2'
    (sz1: (nb_boxes_dynamic m1' = nb_boxes_dynamic m1)%nat)
    (sz2: (nb_boxes_dynamic m2' = nb_boxes_dynamic m2)%nat)
    (st1: (nb_boxes_static m1' = nb_boxes_static m1)%nat)
    (st2: (nb_boxes_static m2' = nb_boxes_static m2)%nat)
    (ext1: (Mem.nb_extra m1' = Mem.nb_extra m1)%nat)
    (ext2: (Mem.nb_extra m2' = Mem.nb_extra m2)%nat),
size_mem_preserved (m1'::lm1) (m2'::lm2) cs cs'.
Proof.
  intros. inv SMP. constructor.
  rewrite ! nb_boxes_sep in *. lia.
  eapply smp_cons_same with (C:=C) (C':=C'); eauto. lia. lia. lia. lia. lia. lia.
  eapply smp_cons; eauto.
  rewrite ! nb_boxes_sep in *. lia.
  rewrite ! nb_boxes_sep in *. lia.
  rewrite ! nb_boxes_sep in *. lia.
  rewrite ! nb_boxes_sep in *. lia.
  rewrite ! nb_boxes_sep in *. lia.
  rewrite ! nb_boxes_sep in *. lia.
  rewrite ! nb_boxes_sep in *. lia.
Qed.

Lemma size_mem_preserved_inf:
  forall lm1 lm2 m1 m2 cs cs',
    size_mem_preserved (m1::lm1) (m2::lm2) cs cs' ->
    (Mem.nb_boxes_used_m m2 <= Mem.nb_boxes_used_m m1)%nat.
Proof.
  induction lm1; simpl; intros; eauto.
  - inv H. lia.
  - inv H.
    + apply IHlm1 in smp_rec. rewrite ! nb_boxes_sep in *. lia.
    + apply IHlm1 in smp_rec; lia.
Qed.

Lemma smp_regs:
  forall lm1 m m'0 lm2 f stk ls c s fb sp' ra c' cs'
    (SMP: size_mem_preserved
            (m::lm1) (m'0::lm2)
            (Linear.Stackframe f (Eval (Vptr stk Int.zero)) ls c :: s)
            (Stackframe fb (Eval (Vptr sp' Int.zero)) ra c' :: cs'))
  stk sp' fb ls c ra c',
    size_mem_preserved
      (m::lm1) (m'0::lm2)
      (Linear.Stackframe f (Eval (Vptr stk Int.zero)) ls c :: s)
      (Stackframe fb (Eval (Vptr sp' Int.zero)) ra c' :: cs').
Proof.
  induction lm1; simpl; intros; eauto.
  - inv SMP.
  - inv SMP.
    + eapply smp_cons_same; eauto.
    + eapply smp_cons; eauto. 
Qed.

Lemma smp_nb_extra_enough:
  forall lm lm' m m'0 f stk rs b' b s fb sp' cs' tf
    (TRANSL: transf_function f = OK tf),
    size_mem_preserved (m :: lm) (m'0 :: lm')
                       (Linear.Stackframe f (Eval (Vptr stk Int.zero)) rs b :: s)
                       (Stackframe fb (Eval (Vptr sp' Int.zero)) (parent_ra cs') b' :: cs') ->
    (Mem.nb_extra m >= needed_stackspace (Linear.fn_id f))%nat.
Proof.
  induction lm; simpl; intros; eauto.
  - inv H.
  - inv H.
    + eapply IHlm with (tf:=tf) in smp_rec. lia. eauto.
    + lia. 
Qed.

Lemma smp_nb_static_enough:
  forall lm lm' m m'0 f stk rs b' b s fb sp' cs' tf
    (TRANSL: transf_function f = OK tf),
    size_mem_preserved (m :: lm) (m'0 :: lm')
                       (Linear.Stackframe f (Eval (Vptr stk Int.zero)) rs b :: s)
                       (Stackframe fb (Eval (Vptr sp' Int.zero)) (parent_ra cs') b' :: cs') ->
    (nb_boxes_static m >= Mem.box_span (Z.max 0 (Linear.fn_stacksize f)))%nat.
Proof.
  induction lm; simpl; intros; eauto.
  - inv H.
  - inv H.
    + eapply IHlm with (tf:=tf) in smp_rec. lia. eauto.
    + lia. 
Qed.

Lemma smp_nb_static_enough':
  forall lm lm' m m'0 f stk rs b' b s fb sp' cs' tf
    (TRANSL: transf_function f = OK tf),
    size_mem_preserved (m :: lm) (m'0 :: lm')
                       (Linear.Stackframe f (Eval (Vptr stk Int.zero)) rs b :: s)
                       (Stackframe fb (Eval (Vptr sp' Int.zero)) (parent_ra cs') b' :: cs') ->
    (nb_boxes_static m'0  >= Mem.box_span (Z.max 0 (fn_stacksize tf)))%nat.
Proof.
  induction lm; simpl; intros; eauto.
  - inv H.
  - inv H.
    + eapply IHlm with (tf:=tf) in smp_rec. lia. eauto.
    + replace tf0 with tf in *.  lia. congruence.
Qed.

Lemma smp_size':
  forall lm lm' m m'0 f stk rs b' b s fb sp' cs' tf
    (TRANSL: transf_function f = OK tf),
    size_mem_preserved (m :: lm) (m'0 :: lm')
                       (Linear.Stackframe f (Eval (Vptr stk Int.zero)) rs b :: s)
                       (Stackframe fb (Eval (Vptr sp' Int.zero)) (parent_ra cs') b' :: cs') ->
    (Mem.nb_boxes_used_m m - needed_stackspace (Linear.fn_id f) -
     Mem.box_span (Z.max 0 (Linear.fn_stacksize f)) >=
     Mem.nb_boxes_used_m m'0 - Mem.box_span (Z.max 0 (fn_stacksize tf)))%nat.
Proof.
  induction lm; simpl; intros; eauto.
  - inv H.
  - inv H.
    + exploit smp_nb_extra_enough; eauto.
      exploit smp_nb_static_enough; eauto.
      exploit smp_nb_static_enough; eauto.
      intros.
      eapply IHlm with (tf:=tf) in smp_rec.
      rewrite ! nb_boxes_sep in *. lia. eauto.
    + 
      rewrite TRANSL in smp_tf; inv smp_tf.
      rewrite ! nb_boxes_sep in *. rewrite stm1, stm2, dm1, dm2, extm1, extm2 in *.
      eapply size_mem_preserved_inf in smp_rec; eauto. rewrite ! nb_boxes_sep in *. lia.
Qed.

Lemma smp_inv:
  forall lm m cs tm tlm cs' f stk rs t fb sp' t'
    (SMP: size_mem_preserved
            (m::lm) (tm::tlm)
            (Linear.Stackframe f (Eval (Vptr stk Int.zero)) rs t :: cs)
            (Stackframe fb (Eval (Vptr sp' Int.zero)) (parent_ra cs') t' :: cs'))
    tf
    (TRANSF: transf_function f = OK tf),
  exists m' tm' lm' tlm' C C',
    (Mem.nb_boxes_used_m m' + C' = C + Mem.nb_boxes_used_m m - needed_stackspace (Linear.fn_id f)
                                       - Mem.box_span (Linear.fn_stacksize f) /\
     Mem.nb_boxes_used_m tm' + C' = C + Mem.nb_boxes_used_m tm 
                                        - Mem.box_span (Mach.fn_stacksize tf))%nat /\
    size_mem_preserved (m'::lm') (tm'::tlm') cs cs'.
Proof.
  induction lm; simpl; intros; eauto.
  - inv SMP.
  - inv SMP.
    + specialize (IHlm _ _ _ _ _ _ _ _ _ _ _ _ smp_rec _ TRANSF0).
      destruct IHlm as (m' & tm' & lm' & tlm' & C'0 & C'1 & (EQ1 & EQ2) & SMP).
      exists m', tm', lm', tlm'.
      rewrite ! nb_boxes_sep in *.
      rewrite st1, st2, ext1, ext2 in *.
      exists (C'0 + C')%nat, (C'1 + C)%nat. repSplit.
      exploit smp_nb_static_enough; eauto. exploit smp_nb_extra_enough; eauto.
      rewrite Z.max_r.
      intros.
      lia. des f.
      exploit smp_nb_static_enough; eauto.
      exploit smp_nb_static_enough'; eauto.
      exploit smp_nb_extra_enough; eauto.
      rewrite ! Z.max_r.
      intros.
      lia. des f. des tf. eauto.
    + rewrite Z.max_r in * by des f.
      rewrite TRANSF0 in smp_tf; inv smp_tf.
      rewrite Z.max_r in * by (des tf0).
      rewrite ! nb_boxes_sep in *.
      exists a, m2', lm, lm2, O, O;       rewrite ! nb_boxes_sep in *; repSplit. lia. lia. auto.
Qed.

Lemma smp_inv':
  forall lm m cs tm tlm cs' f stk rs t fb sp' t'
    (SMP: size_mem_preserved
            (m::lm) (tm::tlm)
            (Linear.Stackframe f (Eval (Vptr stk Int.zero)) rs t :: cs)
            (Stackframe fb (Eval (Vptr sp' Int.zero)) (parent_ra cs') t' :: cs'))
    tf
    (TRANSF: transf_function f = OK tf),
  exists m' tm' lm' tlm' C C',
    (nb_boxes_dynamic m' + C' = C + nb_boxes_dynamic m /\
     Mem.nb_extra m' = Mem.nb_extra m - needed_stackspace (Linear.fn_id f) /\
     nb_boxes_static m' = nb_boxes_static m - Mem.box_span (Linear.fn_stacksize f) /\
     nb_boxes_dynamic tm' + C' = C + nb_boxes_dynamic tm /\
     Mem.nb_extra tm' = Mem.nb_extra tm /\
     nb_boxes_static tm' = nb_boxes_static tm - Mem.box_span (fn_stacksize tf))%nat /\
    size_mem_preserved (m'::lm') (tm'::tlm') cs cs'.
Proof.
  induction lm; simpl; intros; eauto.
  - inv SMP.
  - inv SMP.
    + specialize (IHlm _ _ _ _ _ _ _ _ _ _ _ _ smp_rec _ TRANSF0).
      destruct IHlm as (m' & tm' & lm' & tlm' & C'0 & C'1 & (EQ1 & EQ2 & EQ3 & EQ4 & EQ5 & EQ6) & SMP).
      exists m', tm', lm', tlm'.
      rewrite st1, st2, ext1, ext2 in *.
      exists (C'0 + C')%nat, (C'1 + C)%nat. repSplit.
      lia. lia. lia. lia. lia. lia. auto. 
    +
      rewrite Z.max_r in * by des f.
      rewrite TRANSF0 in smp_tf; inv smp_tf.
      rewrite Z.max_r in * by (des tf0).
      exists a, m2', lm, lm2, O, O; repSplit; auto. lia. lia.
      lia. lia. lia.
Qed.


Lemma transf_function_stacksize_pos:
  forall f tf
    (TRANSL : transf_function f = OK tf),
    fn_stacksize tf > 0.
Proof.
  intros.
  exploit unfold_transf_function; eauto.
  clear; intros; subst.
  unfold fn_stacksize.
  generalize (frame_env_separated (function_bounds f)); eauto.
  intros.
  destruct (make_env (function_bounds f)).
  simpl. Opaque Z.mul. simpl in H.
  repeat destr_and.
  Transparent Stacklayout.fe_stack_data Stacklayout.fe_size.
  unfold Stacklayout.fe_stack_data in *. simpl in *.
  cut (fe_size > 0). generalize (align_le fe_size 8); lia.
  cut (fe_ofs_retaddr >= 0). omega.
  cut (fe_stack_data >= 0). generalize (Z.le_max_r (Linear.fn_stacksize f) 0).  intros; omega.
  cut (fe_ofs_local >= 0). generalize (max_over_slots_of_funct_pos f local_slot). omega.
  cut (fe_ofs_float_callee_save >= 0). generalize (max_over_regs_of_funct_pos f float_callee_save). omega.
  cut (fe_ofs_int_callee_save >= 0). generalize (max_over_regs_of_funct_pos f int_callee_save). omega.
  cut (fe_ofs_link >= 0).  omega.
  generalize (function_bounds_obligation_1 f).  omega.
Qed.

Lemma alloc_abi:
  forall m lo hi m' stk 
    (ALLOC : Mem.alloc m lo hi Normal = Some (m', stk))
    j
    (ABI : Mem.all_blocks_injected j m)
    j'
    (INCR: inject_incr j j')
    ls ls0 m1 sp sp' ra f tf
    (AGFRM : agree_frame f tf j' ls ls0 m' stk m1 sp' sp ra),
    Mem.all_blocks_injected j' m'.
Proof.
  intros.
  red; red; intros.
  destruct (peq stk b); subst; auto.
  apply agree_inj in AGFRM. congruence.
  rewrite <- (Mem.bounds_of_block_alloc_other _ _ _ _ _ _ ALLOC _ n) in H.
  generalize (ABI _ _ _ H H0).
  des (j b). des p.  apply INCR in Heqo. congruence.
Qed.

Lemma stores_in_frame_norm:
  forall f b m1 m2
    (SIF: stores_in_frame f b m1 m2)
    e,
    Mem.mem_norm m1 e = Mem.mem_norm m2 e.
Proof.
  induction 1; simpl; intros; auto.
  rewrite <- IHSIF.
  eapply Mem.store_norm; eauto.
Qed.

Lemma agree_regs_list_ei:
  forall j rs rs0
    (AGREGS : agree_regs j rs rs0) args,
    list_ei expr_inj_se j (fun r : mreg => rs (R r)) ## args rs0 ## args.
Proof.
  induction args; simpl; intros; eauto.
  constructor.
  constructor; auto.
Qed.

Lemma Forall_impl:
  forall T (P Q: T -> Prop) (l: list T),
    (forall x, In x l -> P x -> Q x) ->
    Forall P l ->
    Forall Q l.
Proof.
  intros.
  rewrite Forall_forall in *.
  intros x IN.
  apply H. auto. apply H0; auto.
Qed.

Lemma size_mem_stores_in_frame:
  forall f b m1 m2 (SIF: stores_in_frame f b m1 m2),
    Mem.nb_boxes_used_m m1 = Mem.nb_boxes_used_m m2.
Proof.
  induction 1; simpl; intros; auto.
  rewrite <- IHSIF; clear IHSIF.
  eapply Mem.nb_boxes_used_same.
  symmetry; eapply Mem.store_mk_block_list; eauto.
  eapply Mem.nb_extra_store; eauto.
Qed.

Lemma align_plus:
  forall z s,
    s >= 0 -> z >= 0 ->
    align s 8 + 8 * z >= align (s+z) 8.
Proof.
  unfold align; intros. IntFacts.elim_div.
  ppsimpl; lia.
Qed.
Lemma sif_dyn:
  forall f sp m1 m2 (SIF: stores_in_frame f sp m1 m2),
  forall b, Mem.is_dynamic_block m1 b <-> Mem.is_dynamic_block m2 b.
Proof.
  induction 1; simpl; intros. tauto.
  rewrite Genv.store_dyn. eauto. eauto.
Qed.

Lemma alloc_match_stacks:
  forall m m1 m'0 tfn m2' f m' m5' sp' sp
    (TFN: transf_function f = OK tfn)
    (SSpos: Linear.fn_stacksize f >= 0),
   Mem.alloc m'0 0 (fn_stacksize tfn) Normal = Some (m2', sp') ->
   MemReserve.reserve_boxes m1 (needed_stackspace (Linear.fn_id f)) = Some m' ->
   Mem.alloc m 0 (Linear.fn_stacksize f) Normal = Some (m1, sp) ->
   stores_in_frame f sp' m2' m5' ->
   forall j s cs' bound bound',
     Ple bound sp ->
     Ple bound' sp' ->
   match_stacks j m m'0 s cs' (Linear.fn_sig f) bound bound' ->
   match_stacks j m' m5' s cs' (Linear.fn_sig f) bound bound'.
Proof.
  intros until j; induction 3; simpl; intros.
  econstructor; eauto.
  econstructor; eauto.
  -
    assert (IC: forall idx v,
               index_contains f0 m'0 sp'0 idx v -> index_contains f0 m5' sp'0 idx v).
    {
      intros idx v IC. inv IC.
      exploit offset_of_index_disj_stack_data_2; eauto. intros.
      econstructor; eauto.
      apply (Mem.load_alloc_other _ _ _ _ _ _ H) in H7; auto.
      rewrite (fun p => stores_in_frame_contents _ _ _ _ _ p _ _ H2). auto.
      xomega.
    }
    assert (ICI: forall idx v,
               index_contains_inj f0 j m'0 sp'0 idx v -> index_contains_inj f0 j m5' sp'0 idx v).
    {
      intros idx v ICC. destruct ICC as [v' [A B]]. exists v'; split; auto.
    }

    inversion FRM; constructor; auto.
    + rewrite <- (MemReserve.reserve_bounds_of_block _ _ _ _ H0).
      rewrite <- (Mem.bounds_of_block_alloc_other _ _ _ _ _ _ H1). eauto. intro; subst.
      eapply Mem.fresh_block_alloc in H1. eauto.
    + erewrite <- stores_in_frame_bounds; [|eauto].
      erewrite <- Mem.bounds_of_block_alloc_other; eauto.
      clear - H4 BELOW'. intro; subst; xomega.
    + clear - agree_valid_linear0 H1 H0. unfold Mem.valid_block in *.
      rewrite <- (MemReserve.reserve_nextblock _ _ _ H0).
      exploit Mem.nextblock_alloc. apply H1. intro A; rewrite A. xomega.
    + eapply stores_in_frame_valid; [eauto|].
      clear - agree_valid_mach0 H.
      unfold Mem.valid_block in *.
      exploit Mem.nextblock_alloc. apply H. intro A; rewrite A. xomega.
    + erewrite <- MemReserve.reserve_is_dynamic_block. 2: eauto.
      rewrite <- Mem.is_block_dynamic_alloc; eauto.
    +

      rewrite <- sif_dyn. 2: eauto.
      rewrite <- Mem.is_block_dynamic_alloc; eauto.
    + intros ofs p PERM.
      eapply agree_bounds0; eauto.
      rewrite <- MemReserve.reserve_perm in PERM. 2: eauto.
      eapply Mem.perm_alloc_4.  eauto. eauto.
      intro; subst.
      eapply Mem.fresh_block_alloc in agree_valid_linear0. auto. eauto.
    + red. intros ofs ENC ENC'.
      eapply stores_in_frame_perm; [eauto|].
      eapply Mem.perm_alloc_1; eauto.
  - apply IHmatch_stacks.
    xomega. xomega.
Qed.

Lemma free_free_list_stacks:
  forall m'0 m1' m m' sp' stk tf f j s cs'
    (TF: transf_function f = OK tf)
    (agree_size_mem0 : (Mem.nb_boxes_used_m m - needed_stackspace (Linear.fn_id f) -
                        Mem.box_span (Z.max 0 (Linear.fn_stacksize f)) >=
                        Mem.nb_boxes_used_m m'0 - Mem.box_span (Z.max 0 (fn_stacksize tf)))%nat)
    (FREE': Mem.free m'0 sp' 0 (fn_stacksize tf) = Some m1')
    (FREE: Mem.free m stk 0 (Linear.fn_stacksize f) = Some m')
    m''
    (REL: MemReserve.release_boxes m' (needed_stackspace (Linear.fn_id f)) = Some m'')
    bound bound'
    (spb: Ple bound stk)
    (spb: Ple bound' sp')
    (MS: match_stacks j m m'0 s cs' (Linear.fn_sig f) bound bound'),
    match_stacks j m'' m1' s cs' (Linear.fn_sig f) bound bound'.
Proof.
  intros until bound'; induction 3.
  - econstructor; eauto.
  - econstructor; eauto.
    + clear IHMS.
      assert (IC: forall idx v,
                 index_contains f0 m'0 sp'0 idx v -> index_contains f0 m1' sp'0 idx v).
      {
        intros idx v IC. inv IC.
        exploit offset_of_index_disj_stack_data_2; eauto. intros.
        econstructor; eauto. rewrite (Mem.load_free _ _ _ _ _ FREE'); auto.
        left. intro; subst. clear - BELOW' spb0. xomega.
      }
      assert (ICI: forall idx v,
                 index_contains_inj f0 j m'0 sp'0 idx v -> index_contains_inj f0 j m1' sp'0 idx v).
      {
        intros idx v ICC. destruct ICC as [v' [A B]]. exists v'; split; auto.
      }
      inversion FRM; constructor; eauto.
      * erewrite <- MemReserve.release_bounds_of_block. 2: eauto.
        erewrite Mem.bounds_free; eauto.
        clear - spb BELOW; intro; subst; xomega.
      * rewrite <- agree_sp'_bounds0.
        eapply Mem.bounds_free; eauto.
        clear - BELOW' spb0. intro; subst; xomega.
      * red. erewrite <- MemReserve.release_nextblock. 2: eauto.
        erewrite Mem.nextblock_free. 2: eauto. eauto.
      * eauto with mem.
      * erewrite <- MemReserve.release_is_dynamic_block. 2: eauto. 
        rewrite Mem.is_block_dynamic_free. eauto. eauto.
      * rewrite Mem.is_block_dynamic_free. 2: eauto. eauto.
      * intros ofs p PERM.
        eapply agree_bounds0.
        eapply release_perm in PERM. 2: eauto.
        eapply Mem.perm_free_3 in PERM; eauto.
      * red. intros ofs ENC ENC'.
        generalize (agree_perm0 _ ENC ENC').
        eapply Mem.perm_free_1; eauto.
        left; intro; subst.
        ppsimpl; lia. 
    + apply IHMS; auto;         ppsimpl; lia. 
Qed.

Lemma eq_ge:
 forall x y, x = y -> x >= y.
Proof. intros; lia. Qed.

Lemma ineq_stacks:
  forall f tf (TF: transf_function f = OK tf)
    b (GFF: Genv.find_funct_ptr tge b = Some (Internal tf)),
    (Mem.box_span (Z.max 0 (Linear.fn_stacksize f)) + (needed_stackspace (Linear.fn_id f)) >=
     Mem.box_span (Z.max 0 (fn_stacksize tf)))%nat.
Proof.
  intros.
  rewrite Z.max_r.
  erewrite  stackspace_ok; eauto.
  rewrite Z.max_r.
  rewrite (unfold_transf_function _ _ TF).
  Opaque fe_size.
  simpl.
  rewrite <- ! box_span_ma_3.
  erewrite box_span_mul; eauto.
  rewrite Nat2Z.id. lia. lia.
  apply Zle_ge, size_pos; eauto.
  destruct tf. simpl; auto.
  destruct f. simpl; auto.
Qed.

Lemma static_stores_in_frame:
  forall f b m1 m2 (SIF: stores_in_frame f b m1 m2),
    nb_boxes_static m1 = nb_boxes_static m2.
Proof.
  induction 1; simpl; intros; auto.
  rewrite <- IHSIF; clear IHSIF.
  unfold nb_boxes_static. 
  erewrite <- Mem.store_mk_block_list; eauto.
  erewrite ForgetNorm.filter_ext. reflexivity.
  unfold is_static_block_b.
  Transparent Mem.store.
  unfold Mem.store in H0. destr_in H0; inv H0. simpl. auto.
Qed.

Lemma dynamic_stores_in_frame:
  forall f b m1 m2 (SIF: stores_in_frame f b m1 m2),
    nb_boxes_dynamic m1 = nb_boxes_dynamic m2.
Proof.
  induction 1; simpl; intros; auto.
  rewrite <- IHSIF; clear IHSIF.
  unfold nb_boxes_dynamic. 
  erewrite <- Mem.store_mk_block_list; eauto.
  erewrite Mem.filter_ext. reflexivity.
  unfold is_dynamic_block_b.
  Transparent Mem.store.
  unfold Mem.store in H0. destr_in H0; inv H0. simpl. auto.
Qed.

Lemma extra_stores_in_frame:
  forall f b m1 m2 (SIF: stores_in_frame f b m1 m2),
    Mem.nb_extra m1 = Mem.nb_extra m2.
Proof.
  induction 1; simpl; intros; auto.
  rewrite <- IHSIF; clear IHSIF.
  eapply Mem.nb_extra_store; eauto.
Qed.


Opaque Z.mul.
Lemma alloc_smp:
  forall m m1 m'0 tfn m2' f m' m5' sp' sp
    (TFN: transf_function f = OK tfn)
    (SSpos: Linear.fn_stacksize f >= 0)
    (ALLOC': Mem.alloc m'0 0 (fn_stacksize tfn) Normal = Some (m2', sp'))
    (ALLOC: Mem.alloc m 0 (Linear.fn_stacksize f) Normal  = Some (m1, sp))
    (AB: MemReserve.reserve_boxes m1 (needed_stackspace (Linear.fn_id f)) = Some m')
    (SIF: stores_in_frame f sp' m2' m5') fb
    (FIND: Genv.find_funct_ptr tge fb = Some (Internal tfn))
    c' ra c ls     s cs' lm1 lm2 
    (SMP: size_mem_preserved (m::lm1) (m'0::lm2) s cs'),
    size_mem_preserved (m'::m::lm1) (m5'::m'0::lm2) (Linear.Stackframe f (Eval (Vptr sp Int.zero)) ls c :: s)
        (Stackframe fb (Eval (Vptr sp' Int.zero)) ra c' :: cs').
Proof.
  intros.
  eapply smp_cons; eauto.
  - rewrite <- (reserve_boxes_nb_static _ _ _ AB).
    erewrite <- (alloc_static_nb_static _ _ _ _ _ ALLOC). auto. 
  - rewrite <- (static_stores_in_frame _ _ _ _ SIF).
    rewrite <- (alloc_static_nb_static _ _ _ _ _ ALLOC'). auto.
  - rewrite <- (reserve_boxes_nb_dynamic _ _ _ AB).
    erewrite <- (alloc_static_nb_dynamic _ _ _ _ _ ALLOC). auto. 
  - rewrite <- (dynamic_stores_in_frame _ _ _ _ SIF).
    rewrite <- (alloc_static_nb_dynamic _ _ _ _ _ ALLOC'). auto.
  - rewrite <- (reserve_boxes_nb_extra _ _ _ AB).
    rewrite (Mem.nb_extra_alloc _ _ _ _ _ _ ALLOC). lia.
  - rewrite <- (extra_stores_in_frame _ _ _ _ SIF).
    rewrite (Mem.nb_extra_alloc _ _ _ _ _ _ ALLOC'). lia.
  - rewrite <- (size_mem_stores_in_frame _ _ _ _ SIF).
    rewrite (Mem.nb_boxes_alloc _ _ _ _ _ _ ALLOC'). 
    rewrite <- (reserve_boxes_nb_boxes_used _ _ _ AB).
    rewrite (Mem.nb_boxes_alloc _ _ _ _ _ _ ALLOC).
    generalize (ineq_stacks _ _ TFN _ FIND).
    generalize (size_mem_preserved_inf _ _ _ _ _ _ SMP).
    lia.
Qed.

Definition is_func_ptr (b: block) : Prop :=
  exists f, Genv.find_funct_ptr tge b = Some f.

Variable size_glob : ident -> Z.

Definition is_stack_ptr (b: block) : Prop :=
  (forall im,
      Genv.init_mem fid size_glob tprog = Some im ->
      ~ Mem.valid_block im b) /\
  Genv.find_funct_ptr tge b = None.

Inductive valid_ra : mem -> block -> list stackframe -> Prop :=
| valid_ra_nil: forall m p, Ple p (Mem.nextblock m) -> valid_ra m p nil
| valid_ra_cons: forall m fb ora c cs bsp osp
                   (VRA: valid_ra m bsp cs)
                   (FP_RA: is_func_ptr fb)
                   (SP_SP: is_stack_ptr bsp)
                   (DYN: ~ Mem.is_dynamic_block m bsp)
                   (IB: Mem.in_bound_m (Int.unsigned ora) m fb)
                   (IBsp: Mem.in_bound_m (Int.unsigned osp) m bsp)
                   p (PLT: Plt bsp p)
                   (valid_bra: Ple fb bsp),
    valid_ra m p (Stackframe fb (Eval (Vptr bsp osp)) (Eval (Vptr fb ora)) c :: cs).

Lemma valid_ra_ext:
  forall m cs fb sp ra c c' p,
    valid_ra m p (Stackframe fb sp ra c :: cs) ->
    valid_ra m p (Stackframe fb sp ra c' :: cs).
Proof.
  inversion 1; subst.
  econstructor; eauto.
Qed.

Lemma valid_ra_bnd:
  forall m m' cs
    (ndynglob: forall b, is_func_ptr b -> ~ Mem.is_dynamic_block m b)
    (Bnd: forall b o, Mem.valid_block m b ->
                 ~ Mem.is_dynamic_block m b ->
                 (Mem.in_bound_m o m b <-> Mem.in_bound_m o m' b)) p
    (DYN: forall b, Mem.valid_block m b -> (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b))
    (PLE: Ple (Mem.nextblock m) (Mem.nextblock m')),
    valid_ra m p cs ->
    valid_ra m' p cs.
Proof.
  induction 5; simpl; intros; eauto.
  constructor;  xomega.
  econstructor; eauto.
  rewrite <- DYN; auto.
  eapply Mem.in_bound_valid; eauto.
  apply Bnd; auto.   eapply Mem.in_bound_valid; eauto.
  apply Bnd; auto.   eapply Mem.in_bound_valid; eauto.
Qed.

Lemma valid_ra_bnd_weak:
  forall m m' cs p
    (Bnd: forall b o, Plt b p -> (Mem.in_bound_m o m b <-> Mem.in_bound_m o m' b))
    (PLE: Ple (Mem.nextblock m) (Mem.nextblock m'))
    (DYN: forall b, Mem.valid_block m b -> (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b)),
    valid_ra m p cs ->
    valid_ra m' p cs.
Proof.
  induction 4; simpl; intros; eauto.
  constructor;  xomega.
  econstructor; eauto.
  apply IHvalid_ra; auto. intros; apply Bnd. xomega.
  rewrite <- DYN; auto. eapply Mem.in_bound_valid; eauto.
  apply Bnd; auto. xomega.
  apply Bnd; auto.
Qed.

Lemma valid_ra_bound:
  forall m cs p,
    valid_ra m p cs ->
    forall p' (Valid: Ple p' (Mem.nextblock m))
    (LE: Ple p p'),
      valid_ra m p' cs.
Proof.
  induction 1; simpl; intros.
  constructor. xomega. 
  econstructor; eauto.
  xomega.
Qed.

(** The proof of semantic preservation relies on simulation diagrams
  of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                  +|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  Matching between source and target states is defined by [match_states]
  below.  It implies:
- Agreement between, on the Linear side, the location sets [ls]
  and [parent_locset s] of the current function and its caller,
  and on the Mach side the register set [rs] and the contents of
  the memory area corresponding to the stack frame.
- The Linear code [c] is a suffix of the code of the
  function [f] being executed.
- Memory injection between the Linear and the Mach memory states.
- Well-typedness of [f].
*)

Definition in_bound_init_preserved m:=
  forall im (INIT: Genv.init_mem fid size_glob tprog = Some im)
    o b (IB: Mem.in_bound_m o im b)
    (IFP: is_func_ptr b),
    Mem.in_bound_m o m b.

Definition nextblock_init_preserved m:=
  forall im (INIT: Genv.init_mem fid size_glob tprog = Some im),
    Ple (Mem.nextblock im) (Mem.nextblock m).

Inductive match_states: Linear.state -> Mach.state -> Prop :=
  | match_states_intro:
      forall cs f sp c ls m cs' fb sp' rs m' j tf
        (FUNC_NDYN: forall b, is_func_ptr b -> ~ Mem.is_dynamic_block m b)
        (ABI: Mem.all_blocks_injected j m)
        (MINJ: Mem.inject true expr_inj_se j m m')
        (STACKS: match_stacks j m m' cs cs' f.(Linear.fn_sig) sp sp')
        (TRANSL: transf_function f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some (Internal tf))
        (AGREGS: agree_regs j ls rs)
        (AGFRAME: agree_frame f tf j ls (parent_locset cs) m sp m' sp' (parent_sp cs') (parent_ra cs'))
        lm lm'
        (SMP: size_mem_preserved (m::lm) (m'::lm')
                                 (Linear.Stackframe f (Eval (Vptr sp Int.zero)) ls c :: cs)
                                 (Stackframe fb (Eval (Vptr sp' Int.zero)) (parent_ra cs') (transl_code (make_env (function_bounds f)) c)::cs'))
        (VRA: valid_ra m' sp' cs') 
(SP_SP: is_stack_ptr sp')
(FP_lt_SP: forall b b' (ISP: is_stack_ptr b') (IFP: is_func_ptr b), Plt b b')
(NV_SP: forall b, ~ Mem.valid_block m' b -> is_stack_ptr b)
(IBIP: in_bound_init_preserved m')
(NIP: nextblock_init_preserved m')
(NIP': nextblock_init_preserved m)
im (INIT_MEM: Genv.init_mem fid size_glob tprog = Some im)
        (TAIL: is_tail c (Linear.fn_code f)),
      match_states (Linear.State cs f (Eval (Vptr sp Int.zero)) c ls m)
                  (Mach.State cs' fb (Eval (Vptr sp' Int.zero)) (transl_code (make_env (function_bounds f)) c) rs m')
  | match_states_call:
      forall cs f ls m cs' fb rs m' j tf
        (ABI: Mem.all_blocks_injected j m)
        (FUNC_NDYN: forall b, is_func_ptr b -> ~ Mem.is_dynamic_block m b)
        (MINJ: Mem.inject true expr_inj_se j m m')
        (STACKS: match_stacks j m m' cs cs' (Linear.funsig f) (Mem.nextblock m) (Mem.nextblock m'))
        (TRANSL: transf_fundef f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some tf)
        lm lm'
        (SMP: size_mem_preserved (m::lm) (m'::lm') (cs) (cs'))
(VRA: valid_ra m' (Mem.nextblock m') cs')
(FP_lt_SP: forall b b' (ISP: is_stack_ptr b') (IFP: is_func_ptr b), Plt b b')
(NV_SP: forall b, ~ Mem.valid_block m' b -> is_stack_ptr b)
(IBIP: in_bound_init_preserved m')
(NIP: nextblock_init_preserved m')
(NIP': nextblock_init_preserved m)
im (INIT_MEM: Genv.init_mem fid size_glob tprog = Some im)
        (AGREGS: agree_regs j ls rs)
        (AGLOCS: agree_callee_save ls (parent_locset cs)),
      match_states (Linear.Callstate cs f ls m)
                  (Mach.Callstate cs' fb rs m')
  | match_states_return:
      forall cs ls m cs' rs m' j sg 
        (ABI: Mem.all_blocks_injected j m)
        (FUNC_NDYN: forall b, is_func_ptr b -> ~ Mem.is_dynamic_block m b)
        (MINJ: Mem.inject true expr_inj_se j m m')
        (STACKS: match_stacks j m m' cs cs' sg (Mem.nextblock m) (Mem.nextblock m'))
        (AGREGS: agree_regs j ls rs)
        (AGLOCS: agree_callee_save ls (parent_locset cs))
        lm lm'
        (SMP: size_mem_preserved (m::lm) (m'::lm') cs cs')
(VRA: valid_ra m' (Mem.nextblock m') cs')
(NV_SP: forall b, ~ Mem.valid_block m' b -> is_stack_ptr b)
(IBIP: in_bound_init_preserved m')
(NIP: nextblock_init_preserved m')
(NIP': nextblock_init_preserved m)
im (INIT_MEM: Genv.init_mem fid size_glob tprog = Some im)
(FP_lt_SP: forall b b' (ISP: is_stack_ptr b') (IFP: is_func_ptr b), Plt b b'),
      match_states (Linear.Returnstate cs ls m)
                  (Mach.Returnstate cs' rs m').

Lemma smp_store_1: forall (lm1 : list mem) (m1 : mem) (lm2 : list mem) 
                   (m2 : mem) (cs : list Linear.stackframe) (cs' : list stackframe),
    size_mem_preserved (m1 :: lm1) (m2 :: lm2) cs cs' ->
    forall m2' chunk b' o' v',
      Mem.store chunk m2 b' o' v' = Some m2' ->
      size_mem_preserved (m1 :: lm1) (m2' :: lm2) cs cs'.
Proof.
  intros. 
  cut (nb_boxes_dynamic m2' = nb_boxes_dynamic m2 /\
       nb_boxes_static m2' = nb_boxes_static m2 /\
       Mem.nb_extra m2' = Mem.nb_extra m2). intuition.
  eapply smp_same_size; eauto.
  rewrite ! (store_nb_static _ _ _ _ _ _ H0).
  rewrite ! (Mem.nb_extra_store _ _ _ _ _ _ H0).
  rewrite ! (store_nb_dynamic _ _ _ _ _ _ H0).
  intuition. 
Qed.

Lemma smp_store_2: forall (lm1 : list mem) (m1 : mem) (lm2 : list mem) 
                   (m2 : mem) (cs : list Linear.stackframe) (cs' : list stackframe),
    size_mem_preserved (m1 :: lm1) (m2 :: lm2) cs cs' ->
    forall m1' chunk b o v,
      Mem.store chunk m1 b o v = Some m1' ->
      size_mem_preserved (m1' :: lm1) (m2 :: lm2) cs cs'.
Proof.
  intros. 
  cut (nb_boxes_dynamic m1' = nb_boxes_dynamic m1 /\
       nb_boxes_static m1' = nb_boxes_static m1 /\
       Mem.nb_extra m1' = Mem.nb_extra m1). intuition.
  eapply smp_same_size; eauto.
  rewrite ! (store_nb_static _ _ _ _ _ _ H0).
  rewrite ! (Mem.nb_extra_store _ _ _ _ _ _ H0).
  rewrite ! (store_nb_dynamic _ _ _ _ _ _ H0).
  intuition. 
Qed.

Lemma smp_store: forall (lm1 : list mem) (m1 : mem) (lm2 : list mem) 
                   (m2 : mem) (cs : list Linear.stackframe) (cs' : list stackframe),
    size_mem_preserved (m1 :: lm1) (m2 :: lm2) cs cs' ->
    forall m1' m2' chunk b b' o o' v v',
      Mem.store chunk m1 b o v = Some m1' ->
      Mem.store chunk m2 b' o' v' = Some m2' ->
      size_mem_preserved (m1' :: lm1) (m2' :: lm2) cs cs'.
Proof.
  intros.
  eapply smp_store_1. eapply smp_store_2. eauto. eauto. eauto.
Qed.


Hypothesis return_address_offset_correct:
  forall f tf c ofs sig ros,
    transf_function f = OK tf ->
    is_tail (Mcall sig ros :: transl_code (make_env (function_bounds f)) c)
            (fn_code tf) ->
    return_address_offset tf (transl_code (make_env (function_bounds f)) c) ofs ->
    forall fb, Genv.find_funct_ptr tge fb = Some (Internal tf) ->
          forall im, Genv.init_mem fid size_glob tprog = Some im ->
    Mem.in_bound_m (Int.unsigned ofs) im fb.

Theorem transf_step_correct:
  forall s1 t s2, Linear.step ge needed_stackspace s1 t s2 ->
  forall (WTS: wt_state s1) s1' (MS: match_states s1 s1'),
  exists s2', plus step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros;
  try inv MS;
  try rewrite transl_code_eq;
  try (generalize (function_is_within_bounds f _ (is_tail_in TAIL));
       intro BOUND; simpl in BOUND);
  unfold transl_instr.

  - (* Lgetstack *)
    destruct BOUND.
    exploit wt_state_getstack; eauto. intros SV.
    unfold destroyed_by_getstack; destruct sl.
    + (* Lgetstack, local *)
      exploit agree_locals; eauto. intros [v [A B]].
      exploit index_contains_load_stack; eauto. intros [v' [C D]].
      econstructor; split.
      apply plus_one. apply exec_Mgetstack. 
      simpl type_of_index in C. rewrite C. eauto.
      econstructor; eauto with coqlib.
      apply agree_regs_set_reg; auto.
      eapply expr_inj_se_se; eauto. congruence.
      apply agree_frame_set_reg; auto.
      eapply smp_regs; eauto.
    + (* Lgetstack, incoming *)
      unfold slot_valid in SV. InvBooleans.
      exploit incoming_slot_in_parameters; eauto. intros IN_ARGS.
      inversion STACKS; clear STACKS.
      elim (H6 _ IN_ARGS).
      subst bound bound' s cs'.
      exploit agree_outgoing. eexact FRM. eapply ARGS; eauto.
      exploit loc_arguments_acceptable; eauto. intros [A B].
      unfold slot_valid, proj_sumbool. rewrite zle_true. 
      destruct ty; reflexivity || congruence. omega.
      intros [v [A B]].
      simpl in AGFRAME.
      edestruct (index_contains_load_stack _ _ TRANSL) as [v' [C D]].
      eauto. eapply agree_link. eauto.
      edestruct (index_contains_load_stack _ _ TRF) as [v'' [E F]].
      eauto. apply A. 
      econstructor; split. 
      * apply plus_one. eapply exec_Mgetparam. eauto. 
        rewrite (unfold_transf_function _ _ TRANSL). unfold fn_link_ofs. 
        simpl type_of_index in C. eauto.
        simpl. auto.
        simpl parent_sp.
        change (offset_of_index (make_env (function_bounds f)) (FI_arg ofs ty))
        with (offset_of_index (make_env (function_bounds f0)) (FI_arg ofs ty)).
        simpl type_of_index in E. rewrite E. eauto. eauto. eauto.
      * exploit agree_incoming; eauto. intros EQ; simpl in EQ.
        econstructor; eauto with coqlib. econstructor; eauto.
        apply agree_regs_set_reg. apply agree_regs_set_reg. auto. apply expr_inj_se_vundef.
        congruence. 
        eapply agree_frame_set_reg; eauto. eapply agree_frame_set_reg; eauto. 
        apply caller_save_reg_within_bounds. eauto. 
        apply temp_for_parent_frame_caller_save.
        eapply smp_regs; eauto.

    + (* Lgetstack, outgoing *)
      exploit agree_outgoing; eauto. intros [v [A B]].
      edestruct (index_contains_load_stack _ _ TRANSL) as [v' [C D]].
      eauto. apply A.
      econstructor; split.
      apply plus_one. apply exec_Mgetstack. 
      simpl in *. rewrite C. eauto. 
      econstructor; eauto with coqlib.
      apply agree_regs_set_reg; auto. eapply expr_inj_se_se; eauto. congruence.
      apply agree_frame_set_reg; auto.
      eapply smp_regs; eauto.
      
  - (* Lsetstack *)
    exploit wt_state_setstack; eauto. intros (SV & SW). 
    set (idx := match sl with
                | Local => FI_local ofs ty
                | Incoming => FI_link (*dummy*)
                | Outgoing => FI_arg ofs ty
                end).
    assert (index_valid f idx).
    { unfold idx; destruct sl.
      apply index_local_valid; auto.
      red; auto.
      apply index_arg_valid; auto. }
    exploit store_index_succeeds; eauto. eauto.
    eapply agree_perm; eauto. 
    instantiate (1 := rs0 src). intros [m1' STORE].
    econstructor; split.
    apply plus_one. destruct sl; simpl in SW.
    econstructor. eapply store_stack_succeeds with (idx := idx); eauto.
    eauto.
    discriminate.
    econstructor. eapply store_stack_succeeds with (idx := idx); eauto.
    reflexivity.
    econstructor.
    + eauto.
    + eauto.
    + exploit offset_of_index_disj_stack_data_2; eauto. intros DISJ.
      rewrite <- size_type_chunk in DISJ.
      inversion AGFRAME; auto.
      eapply inj_store_ifu; eauto.
      * intros. eapply agree_inj_in_undef; eauto.
      * intros.
        exploit agree_inj_cases0. apply H0. intro; subst.
        Opaque fe_stack_data.
        rewrite agree_inj0 in H0; inv H0. split; auto.
    +
      Lemma match_stacks_change_mach_mem:
        forall j m m1' m2' cs cs' sg bound bound'
          (MS: match_stacks j m m1' cs cs' sg bound bound')
          (BND': forall b, Mem.bounds_of_block m2' b = Mem.bounds_of_block m1' b)
          (Nb': Mem.nextblock m1' = Mem.nextblock m2')
          (LOAD: forall chunk ofs v sp',
              Plt sp' bound' ->
              Mem.load chunk m1' sp' ofs = Some v ->
              Mem.load chunk m2' sp' ofs = Some v)
          (PERM': forall ofs k p sp',
              Plt sp' bound' ->
              Mem.perm m1' sp' ofs k p -> Mem.perm m2' sp' ofs k p)
          (INJ: forall (b b' : block) (delta : Z),
              j b = Some (b', delta) ->
              Mem.valid_block m b /\
              Mem.valid_block m1' b' /\
              (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m1' b'))
          (DYN: forall b : block,
              Mem.valid_block m1' b ->
              (Mem.is_dynamic_block m1' b <-> Mem.is_dynamic_block m2' b))
        ,
          match_stacks j m m2' cs cs' sg bound bound'.
      Proof.
        induction 1; intros.
        - econstructor; eauto.
        - trim IHMS. auto.
          trim IHMS; auto.
          trim IHMS; auto.
          intros; apply LOAD. xomega. auto.
          trim IHMS; auto.
          intros; apply PERM'. xomega. auto.
          econstructor; eauto.
          eapply agree_frame_invariant; eauto. 
          tauto.
          apply Ple_refl.
          rewrite Nb'; apply Ple_refl.
          tauto.
      Qed.
      apply match_stacks_change_mach_mem with m'; auto.
      intros. symmetry; eapply Mem.bounds_of_block_store; eauto.
      symmetry; eapply Mem.nextblock_store; eauto.
      intros chunk ofs0 v sp'0 Order Load .
      erewrite Mem.load_store_other; eauto.
      left. intro; subst; xomega.
      intros.
      eapply Mem.perm_store_1; eauto.
      intros.
      repSplit.
      eapply Mem.valid_block_inject_1;eauto.
      eapply Mem.valid_block_inject_2;eauto.
      eapply Mem.mi_inj_dynamic in H0; eauto. apply H0.
      intros; eapply Genv.store_dyn; eauto.
    + eauto.
    + eauto. 
    + apply agree_regs_set_slot. apply agree_regs_undef_regs; auto. 
    + destruct sl.
      *  eapply agree_frame_set_local. eauto.
         eapply agree_frame_undef_locs; eauto.
         eauto.
         apply destroyed_by_setstack_caller_save. auto. auto. auto.
         assumption. 
      * simpl in SW; discriminate.
      * eapply agree_frame_set_outgoing.
        eauto.
        eapply agree_frame_undef_locs; eauto.
        eauto.
        apply destroyed_by_setstack_caller_save. auto. auto. auto.
        assumption.
    + eapply smp_regs; eauto.
      eapply smp_store_1; eauto.
    +
      eapply valid_ra_bnd. 5: eauto.
      * intros. intro. 
        exploit FUNC_NDYN; eauto.
        red in H0. dex.
        exploit match_stacks_globalenvs; eauto. intros (hi & A). inv A.
        exploit Genv.find_funct_ptr_rev_transf_partial; eauto. intros [f1 [FFP TF]].
        apply FUNCTIONS in FFP. apply DOMAIN in FFP.
        eapply Mem.mi_inj_dynamic in FFP; eauto. destr.
      * split; intros.
        apply (Mem.store_in_bound_m_1 _ _ _ _ _ _ STORE); auto.
        apply (Mem.store_in_bound_m_2 _ _ _ _ _ _ STORE); auto.
      * intros. eapply Genv.store_dyn; eauto.
      * rewrite (Mem.nextblock_store _ _ _ _ _ _ STORE). apply Ple_refl.
    + auto.
    + intros b0 b' ISP IFP; apply FP_lt_SP; auto.
    + intros. apply NV_SP; auto. eauto with mem.
    + red; intros.
      eapply IBIP in IB; eauto.
      eapply Mem.store_in_bound_m_1; eauto.
    + red; intros.
      eapply NIP in INIT. erewrite <- Mem.nextblock_store with (m1:=m') in INIT; eauto.
    + eauto.
    + eauto.  
    + eauto with coqlib.

  - (* Lop *)
    assert (exists v',
               eval_operation ge (Eval (Vptr sp' Int.zero)) (transl_op (make_env (function_bounds f)) op) rs0##args = Some v'
               /\ expr_inj_se j v v').
    eapply eval_operation_inject'; eauto.
    eapply match_stacks_preserves_globals; eauto.
    eapply agree_inj; eauto. eapply agree_reglist; eauto.
    destruct H as [v' [A B]].
    econstructor; split. 
    apply plus_one. econstructor. 
    instantiate (1 := v'). rewrite <- A. apply eval_operation_preserved. 
    exact symbols_preserved. eauto.
    econstructor; eauto with coqlib.
    apply agree_regs_set_reg; auto.
    rewrite transl_destroyed_by_op.  apply agree_regs_undef_regs; auto. 
    apply agree_frame_set_reg; auto. apply agree_frame_undef_locs; auto.
    eauto.
    apply destroyed_by_op_caller_save.
    eapply smp_regs; eauto.

  - (* Lload *)
    assert (exists a',
               eval_addressing ge (Eval (Vptr sp' Int.zero)) (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a'
               /\ expr_inj_se j a a').
    eapply eval_addressing_inject'; eauto. 
    eapply match_stacks_preserves_globals; eauto.
    eapply agree_inj; eauto. eapply agree_reglist; eauto.
    destruct H as [a' [A B]].
    exploit Mem.loadv_inject; eauto. intros [v' [C D]].
    econstructor; split. 
    apply plus_one. econstructor. 
    instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.
    eexact C. eauto.
    econstructor; eauto with coqlib.
    apply agree_regs_set_reg. rewrite transl_destroyed_by_load. apply agree_regs_undef_regs; auto. auto. 
    apply agree_frame_set_reg. apply agree_frame_undef_locs; auto.
    eauto.
    apply destroyed_by_load_caller_save. auto.
    eapply smp_regs; eauto.
    
  - (* Lstore *)
    assert (exists a',
               eval_addressing ge (Eval (Vptr sp' Int.zero)) (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a'
               /\ expr_inj_se j a a').
    eapply eval_addressing_inject'; eauto. 
    eapply match_stacks_preserves_globals; eauto.
    eapply agree_inj; eauto. eapply agree_reglist; eauto.
    destruct H as [a' [A B]].
    exploit Mem.storev_mapped_inject; eauto. apply AGREGS. intros [m1' [C D]].
    econstructor; split. 
    + apply plus_one. econstructor. 
      instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.
      eexact C. eauto.
    + econstructor.
      * unfold Mem.storev in H2; destr_in H2. intros; rewrite <- Genv.store_dyn; eauto.
      * eapply Mem.storev_abi; eauto.
      * eauto.
      * eapply match_stacks_parallel_stores. eauto. eexact MINJ. eexact B. eauto. eauto. auto. 
      * eauto.
      * eauto. 
      * rewrite transl_destroyed_by_store. 
        apply agree_regs_undef_regs; auto. 
      * apply agree_frame_undef_locs; auto.
        eauto.
        eapply agree_frame_parallel_stores; eauto.
        eauto.
        apply destroyed_by_store_caller_save.
      * eapply smp_regs; eauto.
        unfold Mem.storev in C; destr_in C.
        unfold Mem.storev in H2; destr_in H2.
        eapply smp_store; eauto.


      * eapply valid_ra_bnd.
        5: eauto.
        {
          intros. intro. 
          exploit FUNC_NDYN; eauto.
          red in H. dex.
          exploit match_stacks_globalenvs; eauto. intros (hi & AA). inv AA.
          exploit Genv.find_funct_ptr_rev_transf_partial; eauto. intros [f1 [FFP TF]].
          apply FUNCTIONS in FFP. apply DOMAIN in FFP.
          eapply Mem.mi_inj_dynamic in FFP. 2: eexact MINJ. destr.
        }
        {
          unfold Mem.storev in C; destr_in C.
          split; intros.
          apply (Mem.store_in_bound_m_1 _ _ _ _ _ _ C); auto.
          apply (Mem.store_in_bound_m_2 _ _ _ _ _ _ C); auto.
        }
        unfold Mem.storev in C; destr_in C.        intros. eapply Genv.store_dyn; eauto.
        rewrite (Mem.nextblock_storev _ _ _ _ _ C). apply Ple_refl.
      * auto.
      * intros b0 b' ISP IFP; apply FP_lt_SP; auto.
      * unfold Mem.valid_block in *.
        erewrite Mem.nextblock_storev; eauto.
      * red; intros.
        eapply IBIP in IB; eauto.
        erewrite <- storev_in_bound_m; eauto.
      * red; intros.
        eapply NIP in INIT. erewrite <- Mem.nextblock_storev with (m:=m'0) in INIT; eauto.
      * red; intros.
        eapply NIP' in INIT. erewrite <- Mem.nextblock_storev with (m:=m) in INIT; eauto.
      * eauto.
      * eauto with coqlib.

  - (* Lcall *) 
    exploit find_function_translated; eauto. intros [bf [tf' [A [B C]]]].
    exploit is_tail_transf_function; eauto. intros IST.
    rewrite transl_code_eq in IST. simpl in IST.
    exploit return_address_offset_exists. eexact IST.
    intros [ra' D].
    econstructor; split.
    apply plus_one. econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto with coqlib.
    left; exists AST.Tint; destr.
    intros; red.
    apply Zle_trans with (size_arguments (Linear.funsig f')); auto.
    apply loc_arguments_bounded; auto.
    eapply agree_valid_linear; eauto.
    eapply agree_valid_mach; eauto.
    eapply smp_regs; eauto.
    {
      constructor; auto.
      - red; eexists; eauto.
      - inv AGFRAME; auto.
      - eapply IBIP. eauto.
        eapply return_address_offset_correct; eauto.
        red; eexists; eauto. 
      - red. erewrite (agree_sp'_bounds); eauto.
        generalize (transf_function_stacksize_pos _ _ TRANSL).
        red. simpl. change (Int.unsigned Int.zero) with 0. lia.
      - eapply agree_valid_mach; eauto.
      - apply Plt_Ple.
        apply FP_lt_SP; auto. red; eexists; eauto.
    }
    simpl; red; auto.

  - (* Ltailcall *) 
    generalize (smp_size' _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRANSL SMP). intro.
    exploit function_epilogue_correct; eauto.
    rewrite <- ! box_span_ma_3.
    erewrite ! box_span_mul; eauto; try lia.
    rewrite ! Nat2Z.id . lia. lia. lia.
    intros [rs1 [m1' [P [Q [R [S [T [U V]]]]]]]].
    assert (MS' : match_stacks j m'' m1' s cs' (Linear.funsig f') (Mem.nextblock m'')
                               (Mem.nextblock m1')).
    {
      apply match_stacks_change_sig with (Linear.fn_sig f); auto.
      2: apply zero_size_arguments_tailcall_possible;eapply wt_state_tailcall; eauto.
      apply match_stacks_change_bounds with stk sp'.
      inv AGFRAME; auto.
      eapply free_free_list_stacks; eauto; try (ppsimpl; lia).
      * apply Plt_Ple. change (Mem.valid_block m'' stk).
        assert (Mem.valid_block m' stk).
        eapply Mem.valid_block_free_1; eauto.
        eapply agree_valid_linear; eauto.
        red; erewrite <- MemReserve.release_nextblock. 2: eauto. auto.
      * apply Plt_Ple. change (Mem.valid_block m1' sp'). eapply Mem.valid_block_free_1; eauto.
        eapply agree_valid_mach; eauto. 
    }
    generalize (find_function_translated _ _ _ _ _ _ _ _ _ _ _ _
                                         (release_abi _ _ (Mem.free_abi _ _ _ _ _ H2 _ ABI) _ _ H3)
                                         T MS' H0 V).
    intros [bf [tf' [A [B C]]]].
    dex. repeat destr_and.

    econstructor; split.
    + eapply plus_right.
      * eexact S.
      * econstructor; eauto; try congruence.
        apply Mem.norm_val. 
      * traceEq.
    +
      edestruct (smp_inv' _ _ _ _ _ _ _ _ _ _ _ _ _ SMP )
        as (mm' & tmm' & lm'' & tlm' & C' & C'' & (eq1 & eq2 & eq3 & eq4 & eq5 & eq6) & smp). eauto.
      econstructor; eauto.
      eapply release_abi. 2: eauto. 
      eapply Mem.free_abi; eauto.
      intros; erewrite <- MemReserve.release_is_dynamic_block. 2: eauto. 
      rewrite Mem.is_block_dynamic_free. eauto. eauto.
      eapply smp_cons_same. apply smp.
      *
        exploit release_nb_dynamic. eauto. eauto.
        exploit free_static_nb_dynamic. apply H2. inv AGFRAME; auto.
        intros. rewrite <- H8, <- H7.
        instantiate (1 := C''). instantiate (1:=C'). lia.
      * 
        rewrite eq4.
        exploit free_static_nb_dynamic. apply R. inv AGFRAME; auto. lia.
      * exploit release_nb_static. eauto. eauto.
        exploit free_static_nb_static. 2: apply H2. inv AGFRAME; auto.
        intros. rewrite <- H8. rewrite eq3. rewrite H7. rewrite Z.sub_0_r. lia.
      * exploit free_static_nb_static. 2: apply R. inv AGFRAME; auto.
        rewrite Z.sub_0_r. lia.
      *

        exploit nb_extra_release. eauto. rewrite eq2.
        exploit Mem.nb_extra_free. apply H2. lia.
      * rewrite eq5.
        exploit Mem.nb_extra_free. apply R. lia.
      * eapply valid_ra_bound with (p:=sp'); try (ppsimpl; lia).
        apply valid_ra_bnd_weak with (m:=m'0); eauto.
        intros.
        unfold Mem.in_bound_m.
        erewrite <- Mem.bounds_free; eauto. tauto. intro; subst; ppsimpl; lia.
        rewrite (Mem.nextblock_free _ _ _ _ _ R). apply Ple_refl. 
        intros; symmetry; eapply Mem.is_block_dynamic_free; eauto.
        apply Plt_Ple.         rewrite (Mem.nextblock_free _ _ _ _ _ R).
        eapply agree_valid_mach; eauto.
      * eauto with mem.
      * red; intros.
        red.
        erewrite Mem.bounds_free; [|eauto|].
        eapply IBIP; eauto.
        clear - SP_SP IFP.
        intro; subst. red in IFP, SP_SP. destr_and. rewrite H0 in IFP.
        dex; congruence.
      * red; intros. rewrite (Mem.nextblock_free _ _ _ _ _ R). eapply NIP; eauto.
      * red; intros.
        eapply NIP' in INIT.
        erewrite <- (MemReserve.release_nextblock _ _ _ H3).
        erewrite Mem.nextblock_free with( m2:=m'). 2: eauto.   auto.
        
  - (* Lbuiltin *)
    assert (exists (f' : meminj) (vres' : list expr_sym) (m2' : mem),
      external_call' ef ge (rs0 ## args) m'0 t vres' m2' /\
      Mem.all_blocks_injected f' m' /\
      list_ei expr_inj_se f' vl vres' /\
      Mem.inject true expr_inj_se f' m' m2' /\
      Mem.unchanged_on (loc_unmapped j) m m' /\
      Mem.unchanged_on (loc_out_of_reach j m) m'0 m2' /\
      inject_incr j f' /\
      inject_separated j f' m m'0 /\
      exists C C',
        (nb_boxes_dynamic m' + C = nb_boxes_dynamic m + C' /\
        nb_boxes_dynamic m2' + C = nb_boxes_dynamic m'0 + C' /\
        nb_boxes_static m' = nb_boxes_static m /\
        nb_boxes_static m2' = nb_boxes_static m'0 /\
        Mem.nb_extra m' = Mem.nb_extra m /\
        Mem.nb_extra m2' = Mem.nb_extra m'0)%nat).
    { 
      inv H0.
      exploit external_call_mem_inject; eauto. 
      eapply match_stacks_preserves_globals; eauto.
      eapply decode_longs_inject; eauto.
      eapply expr_list_inject_list_ei.
      eapply agree_reglist; eauto.
      intros [f' [res' [m1' [A [ABI' [B [C [D [E [INCR [SEP [SZ EXT]]]]]]]]]]]].
      exists f', (encode_long (sig_res (ef_sig ef)) res'), m1'; repSplit; auto.
      econstructor; eauto.
      apply encode_long_inject; eauto.
      dex. exists C0, C'; lia.
    }
    destruct H as [f' [res' [m1' [A [ABI' [B [C [D [E [INCR [SEP SZ]]]]]]]]]]].
    econstructor; split.
    + apply plus_one. econstructor; eauto.
      eapply external_call_symbols_preserved'; eauto.
      exact symbols_preserved. exact varinfo_preserved. 
    + econstructor; eauto with coqlib.
      * inv H0; intros; rewrite <- external_call_dyn; eauto.
        red in H; dex.
        exploit Genv.find_funct_ptr_not_fresh. eauto. apply H.
        unfold Mem.valid_block.
        generalize (NIP' _ INIT_MEM). xomega.
      * eapply match_stacks_change_mem_extcall'; eauto.
        eapply match_stacks_preserves_globals; eauto.
        apply Plt_Ple. change (Mem.valid_block m sp0). eapply agree_valid_linear; eauto.
        apply Plt_Ple. change (Mem.valid_block m'0 sp'). eapply agree_valid_mach; eauto.
      * apply agree_regs_set_regs; auto. apply agree_regs_undef_regs; auto.
        eapply agree_regs_inject_incr; eauto.
        apply list_ei_expr_list_inject. auto.
      * apply agree_frame_set_regs; auto. apply agree_frame_undef_regs; auto.
        eapply agree_frame_inject_incr; eauto.
        2: inv AGFRAME; auto.
        2: intros; intro; subst; generalize (SEP _ _ _ H H1);
        intros [AA AB]; exfalso; apply AB; inv AGFRAME; auto.
        {
          eapply agree_frame_invariant; eauto.
          + intros. repSplit.
            exploit (Mem.valid_block_inject_1); eauto.
            exploit Mem.mi_mappedblocks. 2: apply H. eauto. eauto. 
            exploit (Mem.mi_inj_dynamic). 2: apply H. eauto. destr.
          + intros.
            inv H0; symmetry; eapply external_call_perm; eauto.
          + inv H0; intros. symmetry; eapply external_call_bounds_mask; eauto.
          + inv A; intros. symmetry; eapply external_call_bounds_mask; eauto.
          + inv H0; eapply external_call_nextblock; eauto.
          + inv A; eapply external_call_nextblock; eauto.
          + intros. erewrite Mem.load_unchanged_on_1; eauto.
            inv AGFRAME; auto. intros.
            red. intros.
            exploit (agree_inj_cases); eauto.
            destruct (peq b0 sp0). subst.
            erewrite agree_inj in H3; eauto. Opaque fe_stack_data.  inversion H3.
            intros _ P; eapply Mem.perm_bounds in P.
            red in P.
            erewrite agree_sp_bounds in P; eauto. red in P. simpl in P. lia.
            destr. 
          + intros.
            inv A; erewrite <- external_call_perm; eauto.
            inv AGFRAME; auto.
            inv AGFRAME; auto.
          + intros. inv H0; eapply external_call_dyn; eauto.
          + intros. inv A; eapply external_call_dyn; eauto.
        }

      * dex; des SZ. des a. des a0. des a. des a0.
        eapply smp_cons_same.
        eapply smp_regs; eauto. apply e. apply e0. auto. auto. auto. auto.

      * eapply valid_ra_bnd. 5:eauto.
        {
          intros. intro. 
          exploit FUNC_NDYN; eauto.
          red in H. dex.
          exploit match_stacks_globalenvs; eauto. intros (hi & AA). inv AA.
          exploit Genv.find_funct_ptr_rev_transf_partial; eauto. intros [f1 [FFP TF]].
          apply FUNCTIONS in FFP. apply DOMAIN in FFP.
          eapply Mem.mi_inj_dynamic in FFP. 2: eexact MINJ. destr.
        }
        {
          inv A. unfold Mem.in_bound_m; intros.
          erewrite <- extcall_bounds; eauto. tauto.
        }
        {
          inv A. intros.
          eapply external_call_dyn; eauto.
        }
        {
          eapply external_call_nextblock'; eauto.
        }
      * intros. apply NV_SP. unfold Mem.valid_block in H |- *.
        eapply external_call_nextblock' in A. xomega.
      * red; intros.
        generalize (IBIP _ INIT _ _ IB IFP).
        unfold Mem.in_bound_m.
        inv A. erewrite <- extcall_bounds; eauto.
        red in IFP; dex.
        exploit Genv.find_funct_ptr_not_fresh. eauto. apply IFP.
        unfold Mem.valid_block.
        generalize (NIP _ INIT). xomega.
        {
          intros. intro. 
          exploit FUNC_NDYN; eauto. 
          red in IFP. dex.
          exploit match_stacks_globalenvs; eauto. intros (hi & AA). inv AA.
          exploit Genv.find_funct_ptr_rev_transf_partial; eauto. intros [f1 [FFP TF]].
          apply FUNCTIONS in FFP. apply DOMAIN in FFP.
          eapply Mem.mi_inj_dynamic in FFP.  2: eexact MINJ. destr. 
        }
      * red; intros.
        generalize (NIP _ INIT).
        eapply external_call_nextblock' in A; xomega.
      * red; intros.
        generalize (NIP' _ INIT).
        eapply external_call_nextblock' in H0; xomega.
        
  - (* Llabel *)
    econstructor; split.
    apply plus_one; apply exec_Mlabel.
    econstructor; eauto with coqlib.
    eapply smp_regs; eauto.

  - (* Lgoto *)
    econstructor; split.
    apply plus_one; eapply exec_Mgoto; eauto.
    apply transl_find_label; eauto.
    econstructor; eauto. 
    eapply smp_regs; eauto.
    eapply find_label_tail; eauto.
    
  - (* Lcond, true *)
    exploit eval_condition_inj; eauto.
    apply expr_list_inject_list_ei.
    apply agree_reglist. exact AGREGS.
    intros [b1 [A B]].
    econstructor; split.
    apply plus_one. eapply exec_Mcond_true; eauto.
    generalize (Mem.norm_inject_val' _ _ wf_inj_expr_inj_se _ _ _ _ _ ABI MINJ B).
    rewrite H1. unfold Vtrue.
    intro C; inv C. eauto.
    simpl; auto.
    eapply transl_find_label; eauto.
    econstructor; eauto.
    eapply smp_regs; eauto.
    eapply find_label_tail; eauto. 

  - (* Lcond, false *)
        exploit eval_condition_inj; eauto.
    apply expr_list_inject_list_ei.
    apply agree_reglist. exact AGREGS.
    intros [b1 [A B]].
    econstructor; split.
    apply plus_one. eapply exec_Mcond_false; eauto.
    generalize (Mem.norm_inject_val' _ _ wf_inj_expr_inj_se _ _ _ _ _ ABI MINJ B).
    rewrite H1. unfold Vfalse.
    intro C; inv C. eauto.
    econstructor; eauto. 
    eapply smp_regs; eauto.
    eauto with coqlib.

  - (* Ljumptable *)
    econstructor; split.
    apply plus_one; eapply exec_Mjumptable; eauto.
    generalize (Mem.norm_inject_val' _ _ wf_inj_expr_inj_se _ _ _ _ _ ABI MINJ (AGREGS arg)).
    rewrite H0; intro A; inv A. auto.
    apply transl_find_label; eauto.
    econstructor; eauto. 
    eapply smp_regs; eauto.        
    eapply find_label_tail; eauto.

  - (* Lreturn *)
    assert (size_mem_cond:   (Mem.nb_boxes_used_m m - needed_stackspace (Linear.fn_id f) -
               Mem.box_span (Z.max 0 (Linear.fn_stacksize f)) >=
               Mem.nb_boxes_used_m m'0 - Mem.box_span (Z.max 0 (fn_stacksize tf)))%nat).
    {
      eapply smp_size' in SMP. eauto. eauto.
    }
    exploit function_epilogue_correct; eauto.
    rewrite <- ! box_span_ma_3.
    erewrite ! box_span_mul; eauto; try lia.
    rewrite ! Nat2Z.id . lia. lia. lia.
    intros [rs1 [m1' [P [Q [R [S [T [U V]]]]]]]].
    dex; repeat destr_and.
    econstructor; split.
    eapply plus_right. eexact S. econstructor; eauto.
    apply Mem.norm_val.
    congruence. congruence.
    traceEq.
    edestruct (smp_inv' _ _ _ _ _ _ _ _ _ _ _ _ _ SMP )
      as (mm' & tmm' & lm'' & tlm' & C' & C'0 & (eq1 & eq2 & eq3 & eq4 & eq5 & eq6) & smp). eauto.
    econstructor; eauto.
    + eapply release_abi. 2: eauto.
      eapply Mem.free_abi; eauto.
    + intros. erewrite <- MemReserve.release_is_dynamic_block. 2: eauto.
      rewrite Mem.is_block_dynamic_free. eauto. eauto.
    + erewrite <- MemReserve.release_nextblock. 2: eauto. 
      apply match_stacks_change_bounds with stk sp'.
      Focus 2.
      apply Plt_Ple. change (Mem.valid_block m' stk).
      destruct (Mem.valid_block_dec m' stk); auto.
      exploit agree_valid_linear; eauto.  intro A.
      eapply Mem.valid_block_free_1 in A. exfalso; apply n; eauto. eauto. 
      Focus 2.
      apply Plt_Ple. change (Mem.valid_block m1' sp').
      eapply Mem.valid_block_free_1; eauto. eapply agree_valid_mach; eauto. 
      {
        inv AGFRAME.
        (* rewrite TRANSL in smp_tf; inv smp_tf; auto. *)
        eapply free_free_list_stacks; eauto; try (ppsimpl; lia).
      }
    + eapply smp_cons_same. apply smp.
      * exploit release_nb_dynamic. eauto. eauto.
        exploit free_static_nb_dynamic. apply H. inv AGFRAME; auto.
        intros.
        instantiate (1 := C'0). instantiate (1:=C'). lia.
      * 
        rewrite eq4.
        exploit free_static_nb_dynamic. apply R. inv AGFRAME; auto. lia.
      * exploit release_nb_static. eauto. eauto.
        exploit free_static_nb_static. 2: apply H. inv AGFRAME; auto.
        rewrite Z.sub_0_r. lia.
      * exploit free_static_nb_static. 2: apply R. inv AGFRAME; auto.
        rewrite Z.sub_0_r. lia.
      *
        exploit nb_extra_release. eauto. rewrite eq2.
        exploit Mem.nb_extra_free. apply H. lia.
      * rewrite eq5.
        exploit Mem.nb_extra_free. apply R. lia.
      + eapply valid_ra_bound with (p:=sp').
        apply valid_ra_bnd_weak with (m:=m'0); eauto.
        intros.
        unfold Mem.in_bound_m.
        erewrite <- Mem.bounds_free; eauto. tauto. clear - H5. intro; subst; xomega. 
        rewrite (Mem.nextblock_free _ _ _ _ _ R). apply Ple_refl. 
        intros; symmetry; eapply Mem.is_block_dynamic_free; eauto.
        apply Ple_refl. apply Plt_Ple.         rewrite (Mem.nextblock_free _ _ _ _ _ R).
        eapply agree_valid_mach; eauto.
      + eauto with mem.
      +  red; intros.
        red.
        erewrite Mem.bounds_free; [|eauto|].
        eapply IBIP; eauto.
        clear - SP_SP IFP.
        intro; subst. red in IFP, SP_SP. destr_and. rewrite H0 in IFP.
        dex; congruence.
      + red; intros. rewrite (Mem.nextblock_free _ _ _ _ _ R). eapply NIP; eauto.
      + red; intros.
        eapply NIP' in INIT.
        erewrite <- (MemReserve.release_nextblock _ _ _ H0).
        erewrite Mem.nextblock_free with( m2:=m'). 2: eauto.   auto.
      
  - (* internal function *)
    revert TRANSL. unfold transf_fundef, transf_partial_fundef.
    caseEq (transf_function f); simpl; try congruence.
    intros tfn TRANSL EQ. inversion EQ; clear EQ; subst tf.
    destruct (zlt (Linear.fn_stacksize f) 0).
    {
      contradict l; clear. destruct f; simpl. lia.
    }
    exploit function_prologue_correct; eauto.
    eapply wt_callstate_wt_regs; eauto.
    rewrite box_span_ma_3.
    destruct f; auto. auto.
    eapply match_stacks_type_sp; eauto. 
    eapply match_stacks_type_retaddr; eauto.
    omega.
    intros [j' [rs' [m2' [sp' [m3' [m4' [m5' [A [B [C [D [E [F [G [J [K [L M]]]]]]]]]]]]]]]]].
    econstructor; split.
    + eapply plus_left.
      * econstructor; eauto.
        rewrite <- A; f_equal.
        rewrite (unfold_transf_function _ _ TRANSL). simpl. symmetry.
        rewrite ma_3. apply Align.align_align; lia.
      * rewrite (unfold_transf_function _ _ TRANSL). unfold fn_code. unfold transl_body. 
        eexact D.
      * traceEq.
    + generalize (Mem.alloc_result _ _ _ _ _ _ H). intro SP_EQ. 
      generalize (Mem.alloc_result _ _ _ _ _ _ A). intro SP'_EQ.
      econstructor; eauto.
      * intros.
        erewrite <- MemReserve.reserve_is_dynamic_block. 2: eauto.
        rewrite <- Mem.is_block_dynamic_alloc; [|eauto]. eauto.
      * eapply match_stacks_change_meminj. eauto. eauto. 2: subst;  apply Ple_refl.
        unfold Linear.funsig.
        eapply alloc_match_stacks; eauto.
        rewrite <- A; f_equal.
        rewrite ma_3.
        rewrite (unfold_transf_function _ _ TRANSL). symmetry; simpl; apply Align.align_align; lia.
        apply Ple_refl. apply Ple_refl.
        subst. auto.
      * eapply alloc_smp; eauto.
        rewrite <- A; f_equal.
        rewrite (unfold_transf_function _ _ TRANSL). rewrite ma_3. symmetry; simpl; apply Align.align_align; lia.
      * subst.
        apply valid_ra_bnd_weak with (m:=m'0); auto.
        intros; unfold Mem.in_bound_m.
        rewrite <- (stores_in_frame_bounds _ _ _ _ L).
        rewrite <- (Mem.bounds_of_block_alloc_other _ _ _ _ _ _ A). tauto.
        intro; subst; xomega.
        rewrite <- (stores_in_frame_nextblock _ _ _ _ L).
        rewrite (Mem.nextblock_alloc _ _ _ _ _ _ A); eauto.
        xomega.
        intros.
        rewrite <- (sif_dyn _ _ _ _ L).
        rewrite Mem.is_block_dynamic_alloc; [|eauto]. tauto.
      * apply NV_SP. red. unfold Mem.valid_block; subst; clear. xomega.
      * unfold Mem.valid_block. erewrite <- stores_in_frame_nextblock; [|eauto].
        erewrite Mem.nextblock_alloc; eauto.
        intros b VB; apply NV_SP.
        unfold Mem.valid_block; clear - VB; xomega.
      * red; intros.
        red. erewrite <- stores_in_frame_bounds; [|eauto].
        erewrite <- Mem.bounds_of_block_alloc_other; [idtac|eauto|].
        eapply IBIP; eauto.
        cut (Plt b sp'). clear; unfold block; ppsimpl; lia.
        apply FP_lt_SP; auto.
        apply NV_SP.
        subst. clear; intro A; red in A; xomega.
      * red; intros. eapply Ple_trans.
        eapply NIP; eauto.
        rewrite <- (stores_in_frame_nextblock _ _ _ _ L).
        rewrite (Mem.nextblock_alloc _ _ _ _ _ _ A). xomega.
      * red; intros. eapply Ple_trans.
        eapply NIP'; eauto.
        rewrite <- (MemReserve.reserve_nextblock _ _ _ H0).
        rewrite (Mem.nextblock_alloc _ _ _ _ _ _ H); xomega.
      * eauto with coqlib.
        
  - (* external function *)
    simpl in TRANSL. inversion TRANSL; subst tf.
    exploit transl_external_arguments; eauto. intros [vl [ARGS VINJ]].
    assert (exists (f' : meminj) (vres' : list expr_sym) (m2' : mem),
               external_call' ef ge vl m'0 t vres' m2' /\
               Mem.all_blocks_injected f' m' /\
               list_ei expr_inj_se f' res vres' /\
               Mem.inject true expr_inj_se f' m' m2' /\
               Mem.unchanged_on (loc_unmapped j) m m' /\
               Mem.unchanged_on (loc_out_of_reach j m) m'0 m2' /\
               inject_incr j f' /\
               inject_separated j f' m m'0 /\
               (exists C C',
                   (nb_boxes_dynamic m' + C = nb_boxes_dynamic m + C' /\
                    nb_boxes_dynamic m2' + C = nb_boxes_dynamic m'0 + C' /\
                    nb_boxes_static m' = nb_boxes_static m /\
                    nb_boxes_static m2' = nb_boxes_static m'0 /\
                    Mem.nb_extra m' = Mem.nb_extra m /\
                    Mem.nb_extra m2' = Mem.nb_extra m'0)%nat)).
    { 
      inv H0.
      exploit external_call_mem_inject; eauto. 
      eapply match_stacks_preserves_globals; eauto.
      eapply decode_longs_inject; eauto.
      eapply expr_list_inject_list_ei.
      apply VINJ.
      intros [f' [res' [m1' [A [ABI' [B [C [D [E [INCR [SEP [SZ EXT]]]]]]]]]]]].
      exists f', (encode_long (sig_res (ef_sig ef)) res'), m1'; repSplit; auto.
      econstructor; eauto.
      apply encode_long_inject; eauto.
      dex. exists C0, C'; lia.
    }
    destruct H as [f' [res' [m1' [A [ABI' [B [C [D [E [INCR [SEP SZ]]]]]]]]]]].
    econstructor; split.
    + apply plus_one. eapply exec_function_external; eauto.
      eapply external_call_symbols_preserved'; eauto.
      exact symbols_preserved. exact varinfo_preserved.
    + econstructor; eauto with coqlib.
      * inv H0; intros; rewrite <- external_call_dyn; eauto.
        red in H; dex.
        exploit Genv.find_funct_ptr_not_fresh. eauto. apply H.
        unfold Mem.valid_block.
        generalize (NIP' _ INIT_MEM). xomega.
      *
        eapply match_stacks_change_bounds. 
        eapply match_stacks_change_mem_extcall'; eauto.
        eapply match_stacks_preserves_globals; eauto. apply Ple_refl. apply Ple_refl. 
        eapply external_call_nextblock'; eauto.
        eapply external_call_nextblock'; eauto.
      * apply agree_regs_set_regs; auto. 
        eapply agree_regs_inject_incr; eauto.
        apply list_ei_expr_list_inject. auto.
      * apply agree_callee_save_set_result; auto. 
      * dex; des SZ. repeat destr_and. eapply smp_cons_same. eauto.
        eauto. eauto. assumption. assumption. assumption. assumption.
      * eapply valid_ra_bound. eapply valid_ra_bnd. 5: eauto. 
        {
          intros. intro. 
          exploit FUNC_NDYN; eauto.
          red in H. dex.
          exploit match_stacks_globalenvs; eauto. intros (hi & AA). inv AA.
          exploit Genv.find_funct_ptr_rev_transf_partial; eauto. intros [f1 [FFP TF]].
          apply FUNCTIONS in FFP. apply DOMAIN in FFP.
          eapply Mem.mi_inj_dynamic in FFP. 2: eexact MINJ. destr.
        }
        {
          inv A. unfold Mem.in_bound_m; intros.
          erewrite <- extcall_bounds; eauto. tauto.
        }
        {
          inv A. intros.
          eapply external_call_dyn; eauto.
        }
        eapply external_call_nextblock'; eauto.
        apply Ple_refl.
        eapply external_call_nextblock'; eauto.
      * intros; apply NV_SP.
        eapply external_call_nextblock' in A; unfold Mem.valid_block in *; xomega.
      * red; intros.
        generalize (IBIP _ INIT _ _ IB IFP).
        unfold Mem.in_bound_m.
        inv A. erewrite <- extcall_bounds; eauto.
        red in IFP; dex.
        exploit Genv.find_funct_ptr_not_fresh. eauto. apply IFP.
        unfold Mem.valid_block.
        generalize (NIP _ INIT). xomega.
        {
          intros. intro. 
          exploit FUNC_NDYN; eauto. 
          red in IFP. dex.
          exploit match_stacks_globalenvs; eauto. intros (hi & AA). inv AA.
          exploit Genv.find_funct_ptr_rev_transf_partial; eauto. intros [f1 [FFP TF]].
          apply FUNCTIONS in FFP. apply DOMAIN in FFP.
          eapply Mem.mi_inj_dynamic in FFP.  2: eexact MINJ. destr. 
        }
      * red; intros.
        generalize (NIP _ INIT).
        eapply external_call_nextblock' in A; xomega.
      * red; intros.
        generalize (NIP' _ INIT).
        eapply external_call_nextblock' in H0; xomega.
        
  - (* return *)
    inv STACKS. simpl in AGLOCS.  
    econstructor; split.
    apply plus_one. apply exec_return. 
    econstructor; eauto.
    apply agree_frame_return with rs0; auto. eauto.
    eapply smp_regs; eauto.
    inv VRA. auto.
    inv VRA. auto.
Qed.

Lemma abi_flat_inj:
  forall m,
    Mem.all_blocks_injected (Mem.flat_inj (Mem.nextblock m)) m.
Proof.
  red; red; intros.
  unfold Mem.flat_inj in H1.
  revert H1; destr.
  exploit Mem.bounds_of_block_valid; eauto. lia. 
Qed.

Lemma fid_eq:
  forall (a : Linear.fundef) (b0 : AST.fundef function),
    transf_fundef a = OK b0 -> Linear.fid a = fid b0.
Proof.
  intros a b0 TR'; des a; des b0; monadInv TR'.
  unfold transf_function in EQ.
  repeat destr_in EQ.  inv EQ. auto. 
Qed.

Hypothesis sgpos: forall i, size_glob i > 0.

Lemma transf_initial_states:
  forall st1, Linear.initial_state prog size_glob  st1 ->
         exists st2, Mach.initial_state tprog size_glob st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  econstructor; split.
  - econstructor. 
    + eapply Genv.init_mem_transf_partial; eauto.
      apply fid_eq.
    + rewrite (transform_partial_program_main _ _ TRANSF). 
      rewrite symbols_preserved. eauto.
  - generalize (Genv.init_mem_transf_partial _ _ TRANSF size_glob
                                             Linear.fid fid fid_eq H0). intro INIT.      
    econstructor; eauto.
    + eapply abi_flat_inj.
    + intros. red in H. dex. exploit Genv.init_mem_characterization_2; eauto.
      apply H. destr.
    + eapply Genv.initmem_inject; eauto.
    + clear INIT. apply match_stacks_empty with (Mem.nextblock m0). apply Ple_refl. apply Ple_refl. 
      * {
          constructor.
          - intros. unfold Mem.flat_inj. apply pred_dec_true; auto.
          - unfold Mem.flat_inj; intros. destruct (plt b1 (Mem.nextblock m0)); congruence.
          - intros. change (Mem.valid_block m0 b0). eapply Genv.find_symbol_not_fresh; eauto.
          - intros. change (Mem.valid_block m0 b0). eapply Genv.find_funct_ptr_not_fresh; eauto.
          - intros. change (Mem.valid_block m0 b0). eapply Genv.find_var_info_not_fresh; eauto.
        }
      * rewrite H3. red; intros. rewrite loc_arguments_main in H. contradiction.
    + econstructor. lia.
    + constructor. xomega.
    + unfold is_stack_ptr, is_func_ptr. intros. destruct ISP as [ISP1 ISP2].
      dex.
      eapply Genv.find_funct_ptr_not_fresh in IFP; eauto.
      specialize (ISP1 _ INIT).
      clear - ISP1 IFP.
      unfold Mem.valid_block in *. xomega.
    + red; intros.
      destruct (Genv.find_funct_ptr tge b0) eqn:?; try (split; [|now auto]).
      eapply Genv.find_funct_ptr_not_fresh in Heqo; eauto. congruence.
      setoid_rewrite INIT.
      intros im EQ; inv EQ.
      auto. 
    + red; intros. fold fundef in INIT0. congruence.
    + red; intros. fold fundef in INIT0. replace m0 with im by congruence. xomega.
    + red; intros. clear - INIT INIT0. unfold fundef in *. rewrite INIT in INIT0.
      inv INIT0. apply Ple_refl.
    + unfold Locmap.init. red; intros; auto. apply expr_inj_se_vundef.
    + unfold parent_locset. red; auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
    match_states st1 st2 -> Linear.final_state st1 r -> Mach.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS.
  generalize (AGREGS r0).
  econstructor; eauto.
  generalize (Mem.norm_inject_val' _ _ wf_inj_expr_inj_se _ _ _ _ _ ABI MINJ H5).
  rewrite H3. intro A; inv A. auto.
Qed.

Lemma wt_prog:
  forall i fd, In (i, Gfun fd) prog.(prog_defs) -> wt_fundef fd.
Proof.
  intros. exploit transform_partial_program_succeeds; eauto. 
  intros [tfd TF]. destruct fd; simpl in *. 
  - monadInv TF. unfold transf_function in EQ.
    destruct (wt_function f). auto. discriminate.  
  - auto.
Qed.

Theorem transf_program_correct:
  forward_simulation (Linear.semantics prog needed_stackspace size_glob)
                     (Mach.semantics return_address_offset tprog size_glob).
Proof.
  set (ms := fun s s' => wt_state s /\ match_states s s').
  eapply forward_simulation_plus with (match_states := ms). 
  - exact symbols_preserved.
  - intros. exploit transf_initial_states; eauto. intros [st2 [A B]].
    exists st2; split; auto. split; auto.
    eapply wt_initial_state with (prog := prog); eauto. exact wt_prog.
    unfold Linear.semantics in *; simpl in *. eauto.
  - intros. destruct H. eapply transf_final_states; eauto. 
  - intros. destruct H0. 
    unfold Linear.semantics in *; simpl in *. 
    exploit transf_step_correct; eauto. intros [s2' [A B]].
    exists s2'; split. exact A. split.
    eapply step_type_preservation; eauto. eexact wt_prog. eexact B. 
Qed.

End PRESERVATION.
