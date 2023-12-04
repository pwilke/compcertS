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

(** Semantic preservation for the SimplLocals pass. *)

Require Import FSets.
Require FSetAVL.
Require Import Coqlib.
Require Import Errors.
Require Import Ordered.
Require Import AST.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Clight.
Require Import Values_symbolictype.
Require Import Values_symbolic.
Require Import Normalise.
Require Import NormaliseSpec.
Require Import SimplLocals.
Require Import ExprEval.
Require Import Memory.
Require Import VarSort.
Require Import PP.PpsimplZ.
Require Import Psatz.
Require Import ClightRel.
Require Import MemRel Align Tactics ForgetNorm MemReserve.

Opaque Mem.nb_boxes_max.

Module VSF := FSetFacts.Facts(VSet).
Module VSP := FSetProperties.Properties(VSet).

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: transf_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  exact (Genv.find_symbol_transf_partial _ _ TRANSF).
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  exact (Genv.find_var_info_transf_partial _ _ TRANSF).
Qed.

Lemma functions_translated:
  forall m (v: expr_sym) (f: fundef),
  Genv.find_funct m ge v = Some f ->
  exists tf, Genv.find_funct m tge v = Some tf /\ transf_fundef f = OK tf.
Proof.
  exact (Genv.find_funct_transf_partial _ _ TRANSF).
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof.  
  exact (Genv.find_funct_ptr_transf_partial _ _ TRANSF).
Qed.

Lemma type_of_fundef_preserved:
  forall fd tfd,
  transf_fundef fd = OK tfd -> type_of_fundef tfd = type_of_fundef fd.
Proof.
  intros. destruct fd; monadInv H; auto.
  monadInv EQ. simpl; unfold type_of_function; simpl. auto.  
Qed.


(** Matching between environments before and after *)

Inductive match_var (f: meminj) (cenv: compilenv) (e: env) (m: mem) (te: env) (tle: temp_env) (id: ident) : Prop :=
  | match_var_lifted: forall b ty chunk v tv
      (ENV: e!id = Some(b, ty))
      (TENV: te!id = None)
      (LIFTED: VSet.mem id cenv = true)
      (MAPPED: f b = None)
      (MODE: access_mode ty = By_value chunk)
      (LOAD: Mem.load chunk m b 0 = Some v)
      (TLENV: tle!(id) = Some tv)
      (VINJ: expr_inj_se f v tv),
      match_var f cenv e m te tle id
  | match_var_not_lifted: forall b ty b'
      (ENV: e!id = Some(b, ty))
      (TENV: te!id = Some(b', ty))
      (LIFTED: VSet.mem id cenv = false)
      (MAPPED: f b = Some (b',0)),
      match_var f cenv e m te tle id
  | match_var_not_local: forall
      (ENV: e!id = None)
      (TENV: te!id = None)
      (LIFTED: VSet.mem id cenv = false),
      match_var f cenv e m te tle id.

(* Definition free_blocks (m1 m2: mem) (n: nat) := *)
(*   (Mem.nb_boxes_used_m m2 + n <= Mem.nb_boxes_used_m m1)%nat. *)

(* Require Import CompatForgetInj. *)

Record match_envs (f: meminj) (cenv: compilenv)
                  (e: env) (le: temp_env) (m tm: mem) (lo hi: block)
                  (te: env) (tle: temp_env) (tlo thi : block) : Prop :=
  mk_match_envs {
    me_vars:
      forall id, match_var f cenv e m te tle id;
    me_temps:
      forall id v,
      le!id = Some v ->
      (exists tv, tle!id = Some tv /\ expr_inj_se f v tv)
      /\ (VSet.mem id cenv = true -> v = Eval Vundef);
    me_bounds:
      forall id b ty, e!id = Some (b,ty) -> Mem.bounds_of_block m b = (0, sizeof ty);
    me_bounds_same:
      forall id b ty b' delta, e!id = Some (b,ty) -> f b = Some (b',delta) -> Mem.bounds_of_block m b = Mem.bounds_of_block tm b';
    me_inj:
      forall id1 b1 ty1 id2 b2 ty2, e!id1 = Some(b1, ty1) -> e!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2;
    me_range:
      forall id b ty, e!id = Some(b, ty) -> Ple lo b /\ Plt b hi;
    me_trange:
      forall id b ty, te!id = Some(b, ty) -> Ple tlo b /\ Plt b thi;
    me_mapped:
      forall id b' ty,
      te!id = Some(b', ty) -> exists b, f b = Some(b', 0) /\ e!id = Some(b, ty);
    me_flat:
      forall id b' ty b delta,
      te!id = Some(b', ty) -> f b = Some(b', delta) -> e!id = Some(b, ty) /\ delta = 0;
    me_incr:
      Ple lo hi;
    me_tincr:
      Ple tlo thi;
    me_not_dynamic_e: Forall (fun b => ~ Mem.is_dynamic_block m b) (map fst (map fst (blocks_of_env e)));
    me_not_dynamic_te: Forall (fun b => ~ Mem.is_dynamic_block tm b) (map fst (map fst (blocks_of_env te)))
    }.

(** Invariance by change of memory and injection *)

Lemma assign_loc_bounds:
  forall ty m e1 e2 m'
    (AL: assign_loc ty m e1 e2 m')
    b,
    Mem.bounds_of_block m b = Mem.bounds_of_block m' b.
Proof.
  intros.
  inv AL; auto.
  eapply Mem.storev_bounds; eauto.
  eapply Mem.bounds_of_block_storebytes; eauto.
Qed.

Lemma assign_loc_mask:
  forall ty m e1 e2 m'
    (AL: assign_loc ty m e1 e2 m')
    b,
    Mem.mask m b = Mem.mask m' b.
Proof.
  intros.
  inv AL; auto.
  unfold Mem.storev in STOREV; destr_in STOREV.
  symmetry; erewrite Mem.store_mask; eauto.
  rewrite (Mem.mask_storebytes _ _ _ _ _ SB); auto.
Qed.

Lemma assign_loc_nextblock:
  forall ty m bofs v m',
  assign_loc ty m bofs v m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  destruct 1; auto.
  eapply Mem.nextblock_storev; eauto.
  eapply Mem.nextblock_storebytes; eauto.
Qed.

Lemma assign_loc_mk_block_list:
  forall m m' ty a b
    (AL: assign_loc ty m a b m'),
    Mem.mk_block_list m = Mem.mk_block_list m'.
Proof.
  intros.
  inv AL; auto.
  unfold Mem.storev in STOREV; destr_in STOREV. symmetry; eapply Mem.store_mk_block_list; eauto.
  symmetry; eapply Mem.storebytes_mk_block_list; eauto.
Qed.


Lemma assign_loc_nb_extra:
  forall m m' ty a b
    (AL: assign_loc ty m a b m'),
    Mem.nb_extra m = Mem.nb_extra m'.
Proof.
  intros.
  inv AL; auto.
  unfold Mem.storev in STOREV; destr_in STOREV. eapply Mem.nb_extra_store; eauto.
  eapply Mem.nb_extra_storebytes; eauto.
Qed.

Lemma assign_loc_size_mem:
  forall m m' ty a b
    (AL: assign_loc ty m a b m'),
    Mem.nb_boxes_used_m m = Mem.nb_boxes_used_m m'.
Proof.
  intros.
  eapply Mem.nb_boxes_used_same.
  eapply assign_loc_mk_block_list; eauto.
  eapply assign_loc_nb_extra; eauto.
Qed.

Lemma in_blocks_of_env:
  forall x e, In x (blocks_of_env e) ->
         exists i t, sizeof t = snd x /\
                snd (fst x) = 0 /\
                e ! i = Some (fst (fst x), t).
Proof.
  intros.
  unfold blocks_of_env, block_of_binding in H.
  rewrite in_map_iff in H.
  dex; destr. des x0.
  des p.
  exists i, t.
  des x. des p. des H. inv e0.
  repSplit; auto. apply PTree.elements_complete in i0; auto.
Qed.

Lemma in_blocks_of_env':
  forall e i b t
    (EI: e ! i = Some (b,t)),
    In b (map fst (map fst (blocks_of_env e))).
Proof.
  intros.
  unfold blocks_of_env, block_of_binding.
  rewrite ! map_map; simpl.
  rewrite in_map_iff.
  exists (i,(b,t)); simpl; split; auto.
  apply PTree.elements_correct; auto.
Qed.


Lemma in_blocks_of_env_forall:
  forall e i b t
    (EI: e ! i = Some (b,t))
    P (F: Forall P (map fst (map fst (blocks_of_env e)))),
    P b.
Proof.
  intros.
  apply in_blocks_of_env' in EI.
  rewrite Forall_forall in F; apply F in EI; auto.
Qed.

Lemma in_forall:
  forall {A: Type} (b: A) l P,
    Forall P l ->
    In b l ->
    P b.
Proof.
  intros.
  rewrite Forall_forall in H; apply H in H0; auto.
Qed.

Lemma match_envs_invariant:
  forall f cenv e le m tm lo hi te tle tlo thi f' m' tm'
    (ME: match_envs f cenv e le m tm lo hi te tle tlo thi)
    (LD: forall b chunk v,
        f b = None ->
        Ple lo b /\ Plt b hi ->
        Mem.load chunk m b 0 = Some v -> Mem.load chunk m' b 0 = Some v)
    (BOUNDS: forall b, Plt b hi -> ~ Mem.is_dynamic_block m b ->
                  Mem.bounds_of_block m b = Mem.bounds_of_block m' b)
    (BOUNDS': forall b, Plt b thi -> ~ Mem.is_dynamic_block tm b ->
                   Mem.bounds_of_block tm b = Mem.bounds_of_block tm' b)
    (INCR: inject_incr f f')
    (INV1: forall b, Ple lo b /\ Plt b hi -> f' b = f b)
    (INV2: forall b b' delta, f' b = Some(b', delta) -> Ple tlo b' /\ Plt b' thi -> f' b = f b)
    (DYNinject: forall b b' delta,
        f b = Some (b',delta) ->
        (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block tm b'))
    (DYNsame: forall b, Plt b hi ->
                   (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b))
    (DYNsame': forall b, Plt b thi ->
                    (Mem.is_dynamic_block tm b <-> Mem.is_dynamic_block tm' b)),
    match_envs f' cenv e le m' tm' lo hi te tle tlo thi.
Proof.
  intros.
  destruct ME; constructor; eauto. 
  - (* vars *)
    intros. generalize (me_vars0 id); intros MV; inv MV.
    + eapply match_var_lifted; eauto.
      rewrite <- MAPPED; eauto. 
      eapply ei_inj_incr; eauto.
    + eapply match_var_not_lifted; eauto.
    + eapply match_var_not_local; eauto.
  - (* temps *)
    intros. exploit me_temps0; eauto. intros [[v' [A B]] C]. split; auto. exists v'; split; eauto.
    eapply ei_inj_incr; eauto.
  - intros.
    exploit me_bounds0; eauto.
    exploit me_range0; eauto. intros.
    rewrite <- BOUNDS; auto. xomega.
    generalize (in_blocks_of_env_forall _ _ _ _ H _ me_not_dynamic_e0). auto. 
  - intros id b ty b' delta EI FB.
    exploit me_range0; eauto.
    intros [PLE PLT]. 
    exploit me_bounds_same0; eauto.
    rewrite <- INV1; eauto. 
    rewrite <- BOUNDS; try xomega.
    rewrite <- BOUNDS'. auto.
    destruct (me_vars0 id); rewrite EI in ENV; inv ENV.
    rewrite INV1 in FB. congruence. xomega.
    exploit  me_trange0; eauto.
    rewrite INV1 in FB. rewrite FB in MAPPED; inv MAPPED; xomega.
    xomega.
    rewrite INV1 in FB.
    rewrite <- DYNinject.   2: eauto. 
    generalize (in_blocks_of_env_forall _ _ _ _ EI _ me_not_dynamic_e0). auto.
    xomega.
    generalize (in_blocks_of_env_forall _ _ _ _ EI _ me_not_dynamic_e0). auto.
  - (* mapped *)
    intros. exploit me_mapped0; eauto. intros [b [A B]]. exists b; split; auto.  
  - (* flat *)
    intros. eapply me_flat0; eauto. rewrite <- H0. symmetry. eapply INV2; eauto.
  - revert me_not_dynamic_e0.
    apply Mem.Forall_impl'.
    intros; rewrite <- DYNsame; auto.

    Lemma blocks_of_env_impl:
      forall b e (P: block -> Prop),
        In b (map fst (map fst (blocks_of_env e))) ->
        (forall i b t, e ! i = Some (b,t) -> P b) ->
        P b.
    Proof.
      intros.
      rewrite map_map, in_map_iff in H. dex; destr_and. subst. des x. des p.
      apply in_blocks_of_env in H1.
      dex; destr_and. simpl in *. subst. apply H0 in H2. auto.
    Qed.
    generalize (blocks_of_env_impl _ _ _ H me_range0). xomega.
  - revert me_not_dynamic_te0.
    apply Mem.Forall_impl'.
    intros; rewrite <- DYNsame'; auto.
    generalize (blocks_of_env_impl _ _ _ H me_trange0). xomega.
Qed.

Lemma match_envs_extcall:
  forall f cenv e le m lo hi te tle tlo thi tm f' m' tm'
    (ME: match_envs f cenv e le m tm lo hi te tle tlo thi)
    (UNCH: Mem.unchanged_on (loc_unmapped f) m m')
    (Bnds: forall b, Plt b hi -> ~ Mem.is_dynamic_block m b ->
                Mem.bounds_of_block m b = Mem.bounds_of_block m' b)
    (Bnds':forall b, Plt b thi -> ~ Mem.is_dynamic_block tm b ->
                Mem.bounds_of_block tm b = Mem.bounds_of_block tm' b)
    (INCR: inject_incr f f')
    (SEP: inject_separated f f' m tm)
    (PLE1: Ple hi (Mem.nextblock m)) (PLE2: Ple thi (Mem.nextblock tm))
      (DYNinject: forall b b' delta,
        f b = Some (b',delta) ->
        (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block tm b'))
    (DYNsame: forall b, Plt b hi ->
                   (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b))
    (DYNsame': forall b, Plt b thi ->
                    (Mem.is_dynamic_block tm b <-> Mem.is_dynamic_block tm' b)),
    match_envs f' cenv e le m' tm' lo hi te tle tlo thi.
Proof.
  intros. eapply match_envs_invariant; eauto.
  - intros. eapply Mem.load_unchanged_on; eauto.
  - red in SEP. intros. destruct (f b) as [[b' delta]|] eqn:?.
    eapply INCR; eauto.
    destruct (f' b) as [[b' delta]|] eqn:?; auto.
    exploit SEP; eauto. unfold Mem.valid_block. intros [A B].
    xomega.
  - intros. destruct (f b) as [[b'' delta']|] eqn:?. eauto.
    exploit SEP; eauto. unfold Mem.valid_block. intros [A B].
    xomegaContradiction.
Qed.


(** Invariance by external call *)


(** Properties of values obtained by casting to a given type. *)

(** Correctness of [make_cast] *)

Lemma make_cast_correct:
  forall e le m a v1 tto v2,
  eval_expr tge e le m a v1 ->
  sem_cast_expr v1 (typeof a) tto = Some v2 ->
  eval_expr tge e le m (make_cast a tto) v2.
Proof.
  intros.
  econstructor; eauto.
Qed.

Definition expr_casted (e: expr_sym) (ty: type) :=
  exists e', sem_cast_expr e ty ty = Some e' /\ same_eval e e'.

Lemma expr_casted_load_result:
  forall v ty chunk,
    expr_casted v ty -> access_mode ty = By_value chunk ->
    same_eval (Val.load_result chunk v) v.
Proof.
  intros. destruct H as [v' [A B]].
  unfold sem_cast_expr in A.
  pose (ct := classify_cast ty ty).
  pose (n:=ty).
  des ty.
  - replace (match i with I8 => cast_case_i2i i s |
                     I16 => cast_case_i2i i s| I32 => cast_case_i2i I32 s
                     | IBool => cast_case_i2i i s end)
    with (cast_case_i2i i s) in * by des i.
    inv A.
    red; intros.
    des i; des s; inv H0; simpl; intros; auto; rewrite B; simpl; seval;
    try (rewrite Int.sign_ext_above with (n:=32%Z); auto; unfsize; try Psatz.lia);
    try (rewrite Int.zero_ext_above with (n:=32%Z); auto; unfsize; try Psatz.lia);
    try (des (Int.eq i Int.zero));
    try (rewrite Int.zero_ext_narrow; auto; omega);
    try (rewrite Int.sign_ext_narrow; auto; omega).
  - inv A; inv H0; destr. red; intros; rewrite B.
    simpl. seval; auto. unfold convert_t.
    rewrite Int64.sign_ext_above with (n:=64%Z); auto; unfsize; Psatz.lia.
  - unfold expr_cast_gen in *.
    red; intros.
    specialize (B cm em).
    des f; inv A; inv H0; simpl; auto. 
  - inv A. inv H0.
    simpl. symmetry; auto. 
Qed.

(** Preservation by assignment to lifted variable. *)

Lemma sem_cast_expr_casted:
  forall e ty e'
    (SCE: sem_cast_expr e ty ty = Some e'),
    expr_casted e' ty.
Proof.
  intros.
  exploit Equivalences.sem_cast_expr_idem; eauto.
Qed.

Lemma match_envs_assign_lifted:
  forall f cenv e le m tm lo hi te tle tlo thi b ty v m' id tv 
    (MENV: match_envs f cenv e le m tm lo hi te tle tlo thi)
    (EID: e!id = Some(b, ty))
    (SCE: expr_casted  v ty)
    (EI: expr_inj_se f v tv)
    (AL: assign_loc ty m (Eval (Vptr b Int.zero)) v m')
    (VMEM: VSet.mem id cenv = true),
  match_envs f cenv e le m' tm lo hi te (PTree.set id tv tle) tlo thi.
Proof.
  intros. destruct MENV. generalize (me_vars0 id); intros MV; inv MV; try congruence.
  rewrite ENV in EID; inv EID. inv AL; try congruence.
  unfold Mem.storev in STOREV.
  revert STOREV; destr.
  exploit Mem.norm_ptr_same; eauto. intro A; inv A. rewrite Int.unsigned_zero.
  constructor; eauto; intros.
  - (* vars *)
    destruct (peq id0 id). subst id0.
    exploit Mem.load_store_same; eauto. intros [v1 [A B]]. 
    eapply match_var_lifted with (v := v1); eauto.
    apply PTree.gss.
    rewrite (expr_casted_load_result) in B; eauto.
    symmetry in B; revert B; apply expr_inj_se_l; auto.
    generalize (me_vars0 id0); intros MV; inv MV.
    eapply match_var_lifted; eauto.
    rewrite <- LOAD0. eapply Mem.load_store_other; eauto. 
    rewrite PTree.gso; auto.
    eapply match_var_not_lifted; eauto. 
    eapply match_var_not_local; eauto.
  - (* temps *)
    exploit me_temps0; eauto. intros [[tv1 [A B]] C]. split; auto.
    rewrite PTree.gsspec. destruct (peq id0 id). 
    subst id0. exists tv; split; auto. rewrite C; auto.
    apply expr_inj_se_vundef.
    exists tv1; auto.
  - erewrite <- Mem.bounds_of_block_store; eauto.
  - erewrite <- Mem.bounds_of_block_store; eauto.
  - revert me_not_dynamic_e0.
    apply Forall_impl.
    Transparent Mem.store.
    unfold Mem.store in STOREV; destr_in STOREV; inv STOREV.
    unfold Mem.is_dynamic_block; destr.    
Qed.

(** Preservation by assignment to a temporary *)

Lemma match_envs_set_temp:
  forall f cenv e le m lo hi te tle tlo thi id v tv x tm ,
  match_envs f cenv e le m tm lo hi te tle tlo thi ->
  expr_inj_se f v tv ->
  check_temp cenv id = OK x ->
  match_envs f cenv e (PTree.set id v le) m tm lo hi te (PTree.set id tv tle) tlo thi.
Proof.
  intros. unfold check_temp in H1. 
  destruct (VSet.mem id cenv) eqn:?; monadInv H1.
  destruct H. constructor; eauto; intros.
(* vars *)
  generalize (me_vars0 id0); intros MV; inv MV.
  eapply match_var_lifted; eauto. rewrite PTree.gso. eauto. congruence.
  eapply match_var_not_lifted; eauto. 
  eapply match_var_not_local; eauto. 
(* temps *)
  rewrite PTree.gsspec in *. destruct (peq id0 id). 
  inv H. split. exists tv; auto. intros; congruence.
  eapply me_temps0; eauto. 
Qed.

Lemma match_envs_set_opttemp:
  forall f cenv e le m tm lo hi te tle tlo thi optid v tv x,
  match_envs f cenv e le m tm lo hi te tle tlo thi ->
  expr_inj_se f v tv ->
  check_opttemp cenv optid = OK x ->
  match_envs f cenv e (set_opttemp optid v le) m tm lo hi 
             te (set_opttemp optid tv tle) tlo thi.
Proof.
  intros. unfold set_opttemp. destruct optid; simpl in H1.
  eapply match_envs_set_temp; eauto.
  auto.
Qed.

(** Extensionality with respect to temporaries *)

Lemma match_envs_temps_exten:
  forall f cenv e le m tm lo hi te tle tlo thi tle',
  match_envs f cenv e le m tm lo hi te tle tlo thi ->
  (forall id, tle'!id = tle!id) ->
  match_envs f cenv e le m tm lo hi te tle' tlo thi.
Proof.
  intros. destruct H. constructor; auto; intros.
  (* vars *)
  generalize (me_vars0 id); intros MV; inv MV.
  eapply match_var_lifted; eauto. rewrite H0; auto.
  eapply match_var_not_lifted; eauto.
  eapply match_var_not_local; eauto.
  (* temps *)
  rewrite H0. eauto.
Qed.

(** Invariance by assignment to an irrelevant temporary *)

Lemma match_envs_change_temp:
  forall f cenv e le m tm lo hi te tle tlo thi id v,
  match_envs f cenv e le m tm lo hi te tle tlo thi ->
  le!id = None -> VSet.mem id cenv = false ->
  match_envs f cenv e le m tm lo hi te (PTree.set id v tle) tlo thi.
Proof.
  intros. destruct H. constructor; auto; intros.
  (* vars *)
  generalize (me_vars0 id0); intros MV; inv MV.
  eapply match_var_lifted; eauto. rewrite PTree.gso; auto. congruence. 
  eapply match_var_not_lifted; eauto.
  eapply match_var_not_local; eauto.
  (* temps *)
  rewrite PTree.gso. eauto. congruence.
Qed.

(** Properties of [cenv_for]. *)

Definition cenv_for_gen (atk: VSet.t) (vars: list (ident * type)) : compilenv :=
  List.fold_right (add_local_variable atk) VSet.empty vars.

Remark add_local_variable_charact:
  forall id ty atk cenv id1,
  VSet.In id1 (add_local_variable atk (id, ty) cenv) <->
  VSet.In id1 cenv \/ exists chunk, access_mode ty = By_value chunk /\ id = id1 /\ VSet.mem id atk = false.
Proof.
  intros. unfold add_local_variable. split; intros. 
  destruct (access_mode ty) eqn:?; auto.
  destruct (VSet.mem id atk) eqn:?; auto.
  rewrite VSF.add_iff in H. destruct H; auto. right; exists m; auto.
  destruct H as [A | [chunk [A [B C]]]].
  destruct (access_mode ty); auto. destruct (VSet.mem id atk); auto. rewrite VSF.add_iff; auto.
  rewrite A. rewrite <- B. rewrite C. apply VSet.add_1; auto.
Qed.

Lemma cenv_for_gen_domain:
 forall atk id vars, VSet.In id (cenv_for_gen atk vars) -> In id (var_names vars).
Proof.
  induction vars; simpl; intros.
  rewrite VSF.empty_iff in H. auto.
  destruct a as [id1 ty1]. rewrite add_local_variable_charact in H. 
  destruct H as [A | [chunk [A [B C]]]]; auto.
Qed.

Lemma cenv_for_gen_by_value:
  forall atk id ty vars,
  In (id, ty) vars ->
  list_norepet (var_names vars) ->
  VSet.In id (cenv_for_gen atk vars) ->
  exists chunk, access_mode ty = By_value chunk.
Proof.
  induction vars; simpl; intros.
  contradiction.
  destruct a as [id1 ty1]. simpl in H0. inv H0. 
  rewrite add_local_variable_charact in H1.
  destruct H; destruct H1 as [A | [chunk [A [B C]]]].
  inv H. elim H4. eapply cenv_for_gen_domain; eauto. 
  inv H. exists chunk; auto.
  eauto.
  subst id1. elim H4. change id with (fst (id, ty)). apply in_map; auto. 
Qed.

Lemma cenv_for_gen_compat:
  forall atk id vars,
  VSet.In id (cenv_for_gen atk vars) -> VSet.mem id atk = false.
Proof.
  induction vars; simpl; intros.
  rewrite VSF.empty_iff in H. contradiction.
  destruct a as [id1 ty1]. rewrite add_local_variable_charact in H.
  destruct H as [A | [chunk [A [B C]]]].
  auto.
  congruence.
Qed.

(** Compatibility between a compilation environment and an address-taken set. *)

Definition compat_cenv (atk: VSet.t) (cenv: compilenv) : Prop :=
  forall id, VSet.In id atk -> VSet.In id cenv -> False.

Lemma compat_cenv_for:
  forall f, compat_cenv (addr_taken_stmt f.(fn_body)) (cenv_for f).
Proof.
  intros; red; intros. 
  assert (VSet.mem id (addr_taken_stmt (fn_body f)) = false).
    eapply cenv_for_gen_compat. eexact H0. 
  rewrite VSF.mem_iff in H. congruence.
Qed.

Lemma compat_cenv_union_l:
  forall atk1 atk2 cenv,
  compat_cenv (VSet.union atk1 atk2) cenv -> compat_cenv atk1 cenv.
Proof.
  intros; red; intros. eapply H; eauto. apply VSet.union_2; auto. 
Qed.

Lemma compat_cenv_union_r:
  forall atk1 atk2 cenv,
  compat_cenv (VSet.union atk1 atk2) cenv -> compat_cenv atk2 cenv.
Proof.
  intros; red; intros. eapply H; eauto. apply VSet.union_3; auto. 
Qed.

Lemma compat_cenv_empty:
  forall cenv, compat_cenv VSet.empty cenv.
Proof.
  intros; red; intros. eapply VSet.empty_1; eauto. 
Qed.

Hint Resolve compat_cenv_union_l compat_cenv_union_r compat_cenv_empty: compat.

(** Allocation and initialization of parameters *)

Lemma alloc_variables_nextblock:
  forall e m vars e' m',
  alloc_variables e m vars e' m' -> Ple (Mem.nextblock m) (Mem.nextblock m').
Proof.
  induction 1.
  apply Ple_refl.
  eapply Ple_trans; eauto. exploit Mem.nextblock_alloc; eauto. intros EQ; rewrite EQ. apply Ple_succ. 
Qed.

Lemma alloc_variables_range:
  forall id b ty e m vars e' m',
  alloc_variables e m vars e' m' ->
  e'!id = Some(b, ty) -> e!id = Some(b, ty) \/ Ple (Mem.nextblock m) b /\ Plt b (Mem.nextblock m').
Proof.
  induction 1; intros.
  auto.
  exploit IHalloc_variables; eauto. rewrite PTree.gsspec. intros [A|A].
  destruct (peq id id0). inv A. 
  right. exploit Mem.alloc_result; eauto. exploit Mem.nextblock_alloc; eauto.
  generalize (alloc_variables_nextblock _ _ _ _ _ H0). intros A B C. 
  subst b. split. apply Ple_refl. eapply Plt_le_trans; eauto. rewrite B. apply Plt_succ. 
  auto.
  right. exploit Mem.nextblock_alloc; eauto. intros B. rewrite B in A. xomega. 
Qed.

Lemma alloc_variables_injective:
  forall id1 b1 ty1 id2 b2 ty2 e m vars e' m',
  alloc_variables e m vars e' m' ->
  (e!id1 = Some(b1, ty1) -> e!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2) ->
  (forall id b ty, e!id = Some(b, ty) -> Plt b (Mem.nextblock m)) ->
  (e'!id1 = Some(b1, ty1) -> e'!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2).
Proof.
  induction 1; intros. 
  eauto.
  eapply IHalloc_variables; eauto. 
  repeat rewrite PTree.gsspec; intros.
  destruct (peq id1 id); destruct (peq id2 id).
  congruence.
  inv H6. exploit Mem.alloc_result; eauto. exploit H2; eauto. unfold block; xomega.
  inv H7. exploit Mem.alloc_result; eauto. exploit H2; eauto. unfold block; xomega.
  eauto.
  intros. rewrite PTree.gsspec in H6. destruct (peq id0 id). inv H6.
  exploit Mem.alloc_result; eauto. exploit Mem.nextblock_alloc; eauto. unfold block; xomega.
  exploit H2; eauto. exploit Mem.nextblock_alloc; eauto. unfold block; xomega.
Qed.



(* Record wf_forget_inj (f: meminj) (m1 m2: mem) := *)
(*   { *)
(*     wfi_inj: inj_injective f; *)
(*     wf_o2o: Mem.one2oneinject f; *)
(*     wf_fb: forget_bound f m1; *)
(*     wf_fm: forget_mask f m1; *)
(*     wf_ssi: same_size_inj f m1 m2; *)
(*     wf_smi: same_mask_inj f m1 m2 *)
(*   }. *)



Inductive cenv_bound (cenv: compilenv) : list (ident*type) -> Prop :=
| cb_nil: cenv_bound cenv nil
| cb_cons: forall l i ty, cenv_bound cenv l ->
                     (0 < sizeof ty <= 8 \/ VSet.mem i cenv = false) ->
                     cenv_bound cenv ((i,ty)::l).






Lemma alloc_variables_load:
  forall e m vars e' m',
  alloc_variables e m vars e' m' ->
  forall chunk b ofs v,
  Mem.load chunk m b ofs = Some v ->
  Mem.load chunk m' b ofs = Some v.
Proof.
  induction 1; intros.
  auto.
  apply IHalloc_variables. eapply Mem.load_alloc_other; eauto.
Qed.

Lemma sizeof_by_value:
  forall ty chunk,
  access_mode ty = By_value chunk -> size_chunk chunk <= sizeof ty.
Proof.
  unfold access_mode; intros.
  assert (size_chunk chunk = sizeof ty).
  {
    destruct ty; try destruct i; try destruct s; try destruct f; inv H; auto.
  }
  omega.
Qed.

Definition env_initial_value (e: env) (m: mem) :=
  forall id b ty chunk,
    e!id = Some(b, ty) -> access_mode ty = By_value chunk ->
    exists v, Mem.load chunk m b 0 = Some v /\ same_eval v (Eval Vundef).


Lemma alloc_load:
  forall m hi m' b bt
    (ALLOC: Mem.alloc m 0 hi bt = Some (m', b))
    chunk o (OFS: 0 <= o < hi) (OFS': o + size_chunk chunk <= hi),
    (align_chunk chunk | o) ->
    exists v, Mem.load chunk m' b o = Some v /\ same_eval v (Eval Vundef).
Proof.
  Transparent Mem.load.
  unfold Mem.load.
  intros; repeat destr.
  eexists; split; eauto.
  erewrite Mem.a_mem_contents; eauto.
  apply in_decode_undef' with (x:=Symbolic (Eval Vundef) None 0); simpl.
  des (size_chunk_nat chunk). unfold size_chunk_nat in Heqn. des chunk; Psatz.lia.
  unfold Mem.init_block. rewrite ZMap.gi. auto.
  red; destr.
  exploit Mem.valid_access_alloc_same; eauto; try easy.
  intros; exfalso; apply n ; auto.
  eapply Mem.valid_access_implies; eauto.
  constructor.
Qed.

Lemma alloc_variables_initial_value:
  forall e m vars e' m',
  alloc_variables e m vars e' m' ->
  env_initial_value e m ->
  env_initial_value e' m'.
Proof.
  induction 1; intros.
  auto.
  apply IHalloc_variables. red; intros. rewrite PTree.gsspec in H2.
  destruct (peq id0 id). inv H2.
  eapply alloc_load; eauto. 
  split. omega. eapply Z.lt_le_trans. 2: eapply sizeof_by_value; eauto.
  des chunk; Psatz.lia.
  rewrite Zplus_0_l. eapply sizeof_by_value; eauto. 
  apply Zdivide_0. 
  exploit H1; eauto.
  intros. dex; destr_and.   erewrite Mem.load_alloc_other; eauto. 
Qed.

Lemma create_undef_temps_charact:
  forall id ty vars, In (id, ty) vars -> (create_undef_temps vars)!id = Some (Eval Vundef).
Proof.
  induction vars; simpl; intros.
  contradiction.
  destruct H. subst a. apply PTree.gss. 
  destruct a as [id1 ty1]. rewrite PTree.gsspec. destruct (peq id id1); auto. 
Qed.

Lemma create_undef_temps_inv:
  forall vars id v, (create_undef_temps vars)!id = Some v -> v = (Eval Vundef) /\ In id (var_names vars).
Proof.
  induction vars; simpl; intros. 
  rewrite PTree.gempty in H; congruence.
  destruct a as [id1 ty1]. rewrite PTree.gsspec in H. destruct (peq id id1).
  inv H. auto.
  exploit IHvars; eauto. tauto.
Qed.

Lemma create_undef_temps_exten:
  forall id l1 l2,
  (In id (var_names l1) <-> In id (var_names l2)) ->
  (create_undef_temps l1)!id = (create_undef_temps l2)!id.
Proof.
  assert (forall id l1 l2,
          (In id (var_names l1) -> In id (var_names l2)) ->
          (create_undef_temps l1)!id = None \/ (create_undef_temps l1)!id = (create_undef_temps l2)!id).
    intros. destruct ((create_undef_temps l1)!id) as [v1|] eqn:?; auto.
    exploit create_undef_temps_inv; eauto. intros [A B]. subst v1.
    exploit list_in_map_inv. unfold var_names in H. apply H. eexact B.
    intros [[id1 ty1] [P Q]]. simpl in P; subst id1.
    right; symmetry; eapply create_undef_temps_charact; eauto.
  intros. 
  exploit (H id l1 l2). tauto. 
  exploit (H id l2 l1). tauto. 
  intuition congruence.
Qed.

Remark var_names_app:
  forall vars1 vars2, var_names (vars1 ++ vars2) = var_names vars1 ++ var_names vars2.
Proof.
  intros. apply map_app. 
Qed.

Remark filter_app:
  forall (A: Type) (f: A -> bool) l1 l2,
  List.filter f (l1 ++ l2) = List.filter f l1 ++ List.filter f l2.
Proof.
  induction l1; simpl; intros.
  auto.
  destruct (f a). simpl. decEq; auto. auto.
Qed.

Remark filter_norepet:
  forall (A: Type) (f: A -> bool) l,
  list_norepet l -> list_norepet (List.filter f l).
Proof.
  induction 1; simpl. constructor. 
  destruct (f hd); auto. constructor; auto. rewrite filter_In. tauto.
Qed.

Remark filter_map:
  forall (A B: Type) (f: A -> B) (pa: A -> bool) (pb: B -> bool),
  (forall a, pb (f a) = pa a) ->
  forall l, List.map f (List.filter pa l) = List.filter pb (List.map f l).
Proof.
  induction l; simpl.
  auto.
  rewrite H. destruct (pa a); simpl; congruence.
Qed.

Lemma create_undef_temps_lifted:
  forall id f,
  ~ In id (var_names (fn_params f)) ->
  (create_undef_temps (add_lifted (cenv_for f) (fn_vars f) (fn_temps f))) ! id =
  (create_undef_temps (add_lifted (cenv_for f) (fn_params f ++ fn_vars f) (fn_temps f))) ! id.
Proof.
  intros. apply create_undef_temps_exten. 
  unfold add_lifted. rewrite filter_app. 
  unfold var_names in *. 
  repeat rewrite map_app. repeat rewrite in_app. intuition. 
  exploit list_in_map_inv; eauto. intros [[id1 ty1] [P Q]]. simpl in P. subst id. 
  rewrite filter_In in Q. destruct Q. 
  elim H. change id1 with (fst (id1, ty1)). apply List.in_map. auto.
Qed.

Lemma vars_and_temps_properties:
  forall cenv params vars temps,
  list_norepet (var_names params ++ var_names vars) ->
  list_disjoint (var_names params) (var_names temps) ->
  list_norepet (var_names params)
  /\ list_norepet (var_names (remove_lifted cenv (params ++ vars)))
  /\ list_disjoint (var_names params) (var_names (add_lifted cenv vars temps)).
Proof.
  intros. rewrite list_norepet_app in H. destruct H as [A [B C]].
  split. auto.
  split. unfold remove_lifted. unfold var_names. erewrite filter_map. 
  instantiate (1 := fun a => negb (VSet.mem a cenv)). 2: auto.
  apply filter_norepet. rewrite map_app. apply list_norepet_append; assumption.
  unfold add_lifted. rewrite var_names_app. 
  unfold var_names at 2. erewrite filter_map. 
  instantiate (1 := fun a => VSet.mem a cenv). 2: auto.
  change (map fst vars) with (var_names vars).
  red; intros.
  rewrite in_app in H1. destruct H1.
  rewrite filter_In in H1. destruct H1. apply C; auto.
  apply H0; auto.
Qed.

Lemma alloc_variables_in_not_in_vars:
  forall e m1 vars e2 m2
    (AV: alloc_variables e m1 vars e2 m2)
    id0 (N: ~ In id0 (var_names vars)),
    e2 ! id0 = e ! id0.
Proof.
  induction 1; simpl; intros; auto.
  rewrite IHAV; auto.
  rewrite PTree.gso; auto.
Qed.

Lemma alloc_variables_bounds_other:
  forall e m1 vars e2 m2
    (AV : alloc_variables e m1 vars e2 m2)
    (Valid: forall id b ty, e!id = Some (b,ty) -> Mem.valid_block m1 b)
    id0 b ty0 (E : e2 ! id0 = Some (b, ty0))
    (n : In id0 (var_names vars) -> False),
    Mem.bounds_of_block m2 b = Mem.bounds_of_block m1 b.
Proof.
  induction 1; simpl; intros; auto.
  erewrite IHAV; eauto.
  symmetry; eapply Mem.bounds_of_block_alloc_other; eauto.
  intro; subst.
  exploit (alloc_variables_in_not_in_vars _ _ _ _ _ AV id0); eauto.
  rewrite PTree.gso; auto. rewrite E.
  intro A; symmetry in A.
  exploit Valid; eauto.
  eapply Mem.fresh_block_alloc; eauto.
  intros id1 b0 ty1.
  rewrite PTree.gsspec.
  destr. subst. intro A; inv A. 
  eapply Mem.valid_new_block; eauto.
  intros; eapply Mem.valid_block_alloc; eauto.
Qed.

Lemma alloc_variables_bounds:
  forall e m vars m' e' 
    (AV: alloc_variables e m vars e' m')
    (Valid: forall id b ty, e!id = Some (b,ty) -> Mem.valid_block m b)
    id b ty
    (I: In id (var_names vars))
    (E: e' ! id = Some (b,ty)),
    Mem.bounds_of_block m' b = (0, sizeof ty).
Proof.
  induction 1; simpl; intros; auto. easy.
  destruct (in_dec peq id0 (var_names vars)).
  - eapply IHAV; eauto.
    intros id1 b0 ty1.
    rewrite PTree.gsspec. clear I.  destr; subst.
    intro A; inv A. 
    eapply Mem.valid_new_block; eauto.
    intros; eapply Mem.valid_block_alloc; eauto.
  - intuition subst.
    erewrite alloc_variables_bounds_other; eauto.
    exploit alloc_variables_in_not_in_vars; eauto.
    rewrite PTree.gss. 
    rewrite E; intro A; inv A.
    erewrite Mem.bounds_of_block_alloc; eauto. f_equal.
    apply Zmax_r. apply Zge_le, sizeof_pos.
    intros id b0 ty1. rewrite PTree.gsspec.
    destr. intro A; inv A. eapply Mem.valid_new_block; eauto.
    intros; eapply Mem.valid_block_alloc; eauto.
Qed.

Definition free_blocks (m1 m2: mem) (n: nat) :=
  (Mem.nb_boxes_used_m m2 + n <= Mem.nb_boxes_used_m m1)%nat.

Lemma free_blocks_more:
  forall m tm n n' (LE: (n' <= n)%nat)
    (FB: free_blocks m tm n),
    free_blocks m tm n'.
Proof.
  unfold free_blocks; intros.
  generalize (two_power_nat_pos MA); nia.
Qed.

Lemma Sle_le:
  forall (a b: nat),
    (S a <= b)%nat -> (a <= b)%nat.
Proof. intros; lia. Qed.

Lemma box_span_small:
  forall x : Z, 0 < x <= two_power_nat MA ->
           Mem.box_span x = S O.
Proof.
  unfold Mem.box_span.
  intros.
  rewrite Zdiv_small. reflexivity. lia.
Qed.

Lemma free_blocks_alloc:
  forall m tm k bt,
    free_blocks m tm (S k) ->
    exists tm' b,
      Mem.alloc tm 0 8 bt = Some (tm',b) /\
      free_blocks m tm' k.
Proof.
  intros m tm k bt FrB.
  destruct (Mem.alloc tm 0 8 bt) as [[tm1 b1]|] eqn:ALLOC.
  - intros.  exists tm1,b1; split; auto.
    red; intros.
    rewrite (Mem.nb_boxes_alloc _ _ _ _ _ _ ALLOC).
    red in FrB.
    rewrite Zmax_r by lia. rewrite box_span_small. lia.
    split. lia. change 8 with (two_power_nat 3).
    rewrite ! two_power_nat_two_p. apply two_p_monotone. generalize (MA_bound); lia. 
  - exfalso.
    generalize (Mem.alloc_none_too_many_boxes _ _ _ _ ALLOC).
    rewrite Zmax_r by lia. rewrite box_span_small. red in FrB.
    generalize (Mem.wfm_alloc m). lia.
    split. lia. change 8 with (two_power_nat 3).
    rewrite ! two_power_nat_two_p. apply two_p_monotone. generalize (MA_bound); lia.
Qed.


Lemma free_blocks_reserve_boxes:
  forall k k' m tm,
    free_blocks m tm k ->
    (k' <= k)%nat ->
    exists tm',
      MemReserve.reserve_boxes tm k' = Some tm' /\
      free_blocks m tm' (k - k').
Proof.
  Opaque minus.
  unfold MemReserve.reserve_boxes.
  intros. destr. eexists; split; eauto.
  red.
  red in H.
  revert H.
  unfold Mem.nb_boxes_used_m, Mem.mk_block_list, Mem.size_block; simpl.
  lia.
  contradict g.
  red in H.
  generalize (Mem.wfm_alloc m). lia.
Qed.

Lemma free_blocks_alloc_bytes_1:
  forall k k' m tm m'
    (FrB: free_blocks m tm k)
    (AB: MemReserve.reserve_boxes m k' = Some m'),
    free_blocks m' tm (k + k').
Proof.
  Opaque Peano.plus.
  unfold MemReserve.reserve_boxes, free_blocks; simpl; intros.
  destr_in AB; inv AB.
  revert FrB.
  unfold Mem.nb_boxes_used_m, Mem.mk_block_list, Mem.size_block; simpl. lia.
Qed.

Ltac genAlloc := Mem.genAlloc.

Lemma alloc_bytes_load:
  forall m n m'
    (AB: MemReserve.reserve_boxes m n = Some m')
    b (PLT: Plt b (Mem.nextblock m))
    chunk o,
    Mem.load chunk m' b o = Mem.load chunk m b o.
Proof.
  unfold MemReserve.reserve_boxes, Mem.load.
  intros. destr_in AB; inv AB.
  repeat destr.
Qed.

Lemma load_valid_block:
  forall m chunk b ofs v,
    Mem.load chunk m b ofs = Some v ->
    Mem.valid_block m b.
Proof.
  intros.
  eapply Mem.load_valid_access in H.
  inv H.
  eapply Mem.perm_valid_block with (ofs:=ofs).
  apply H0. des chunk; lia.
Qed.

Lemma cenv_bound_add:
  forall l e i,
    cenv_bound e l ->
    (forall t, In (i,t) l -> 0 < sizeof t <= 8) ->
    cenv_bound (VSet.add i e) l.
Proof.
  induction l; simpl; intros.
  constructor.
  inv H. constructor; auto.
  destruct H4.
  auto.
  rewrite VSP.FM.add_b.
  rewrite H.
  destruct (VSP.FM.eqb i i0) eqn:?; simpl; auto.
  unfold VSP.FM.eqb in Heqb.
  revert Heqb; destr. subst.
  specialize (H0 _ (or_introl eq_refl)). auto.
Qed.

Lemma access_mode_value_s8:
  forall t m,
    access_mode t = By_value m ->
    0 < sizeof t <= 8.
Proof.
  intros. des t; 
  destr; lia.
Qed.

Lemma not_int_mem_false:
  forall b vars i 
    (NIN: ~ In i (map fst vars) ),
    VSet.mem i (cenv_for_gen b vars) = false.
Proof.
  induction vars; simpl; intros; eauto.
  des a.
  repeat destr; eauto.
  rewrite VSF.add_b. rewrite IHvars; auto. unfold VSF.eqb; destr.
Qed.

Lemma cenv_bound_for_gen:
  forall vars  (lnr: list_norepet (map fst vars)) b,
    cenv_bound (cenv_for_gen (addr_taken_stmt b) vars) vars.
Proof.
  induction vars; simpl; intros; eauto. constructor.
  des a.
  constructor.
  - inv lnr. specialize (IHvars H2).
    destr; destr; try apply IHvars; auto.
    apply cenv_bound_add; auto.
    intros.
    rewrite in_map_iff in H1.
    exfalso; apply H1.
    exists (i, t0); simpl; auto.
  - inv lnr.
    destr.
    right.
    destr; apply not_int_mem_false; auto.
    destr; try (right; apply not_int_mem_false; auto).
    apply access_mode_value_s8 in Heqm; auto.
Qed.


Lemma alloc_bytes_in_bound_m:
  forall m 
    n m'
    (AB: MemReserve.reserve_boxes m n = Some m')
    b i,
    Mem.in_bound_m i m b <->
    Mem.in_bound_m i m' b.
Proof.
  unfold MemReserve.reserve_boxes, Mem.in_bound_m, in_bound, Mem.bounds_of_block; simpl.
  intros. destr_in AB; inv AB. simpl. tauto.
Qed.

Lemma size_block_alloc_bytes:
  forall m n m'  b
    (AB: MemReserve.reserve_boxes m n = Some m'),
    Mem.size_block m b =
    Mem.size_block m' b.
Proof.
  unfold MemReserve.reserve_boxes, Mem.size_block; simpl.
  intros. destr_in AB; inv AB. reflexivity.
Qed.

Definition forb :=
  (fun a: block * Z * Z => (snd (fst a), snd a)).

Require Import Permutation.

Lemma blocks_set_elements_permut:
  forall e id b1 ty
    (nex: e ! id = None)
    (nex': ~ exists id t, e ! id = Some (b1,t))
    (injective: forall id1 id2 b1 b2 ty1 ty2,
        (e ! id1 = Some (b1, ty1) ->
         e ! id2 = Some (b2, ty2) -> id1 <> id2 -> b1 <> b2)),
    Permutation (blocks_of_env (PTree.set id (b1, ty) e))
                ((b1,0,sizeof ty) :: blocks_of_env e ).
Proof.
  intros.
  generalize (PTree.elements_correct e)
             (PTree.elements_complete e).
  generalize (PTree.elements_correct (PTree.set id (b1, ty) e))
             (PTree.elements_complete (PTree.set id (b1, ty) e)).
  generalize (PTree.elements_keys_norepet e).
  generalize (PTree.elements_keys_norepet (PTree.set id (b1, ty) e)).
  unfold blocks_of_env.
  generalize (PTree.elements e).
  generalize (PTree.elements (PTree.set id (b1, ty) e)).
  clear - nex nex' injective. intros l l0 lnr lnr0 A B C D.
  eapply NoDup_Permutation; try rewrite list_norepet_NoDup.
  - eapply list_map_norepet. eapply PTree_Properties.list_norepet_map; eauto.
    intros x y IN IN' DIFF. des x; des y. des p; des p0.
    intro H; inv H.
    des (peq i i0).
    apply B in IN.
    apply B in IN'.
    rewrite PTree.gsspec in IN, IN'.
    des (peq i0 id). 
    generalize (B _ _ IN) (B _ _ IN'). 
    rewrite ! PTree.gsspec.
    des (peq i0 id). des (peq i id).
    intros H H0; inv H0.
    apply nex'; exists i, t; auto.
    des (peq i id).
    intros H H0; inv H.
    apply nex'; exists i0, t0; auto.
    intros H H0.
    exploit injective. eexact H. eexact H0. auto. auto. auto.
  - constructor.
    + intro IN.
      apply in_map_iff in IN. dex; destr.
      des x. des p. des IN. inv e0.
      generalize (D _ _ i0).
      intro. apply nex'; exists i, t; auto.
    + eapply list_map_norepet. eapply PTree_Properties.list_norepet_map; eauto.
      intros x y IN IN' DIFF. des x; des y. des p; des p0.
      intro H; inv H.
      des (peq i i0).
      apply D in IN.
      apply D in IN'.
      congruence.
      generalize (D _ _ IN) (D _ _ IN'). intros.
      exploit injective. eexact H. eexact H0. auto. auto. auto.
  - split; intros IN.
    + rewrite in_map_iff in IN. dex; destr. des x0. des p.
      des IN. apply B in i0. rewrite PTree.gsspec in i0.
      des (peq i id).
      right.
      apply C in i0.
      apply in_map_iff. exists (i, (b,t)); auto.
    + destruct IN.
      * subst.
        apply in_map_iff. exists (id, (b1,ty)); split; auto.
        apply (A _ _ (PTree.gss _ _ _)).
      * apply in_map_iff in H.
        apply in_map_iff.
        dex; destr.
        exists x0; split; destr.
        des x0. des p. des H.
        apply D in i0.
        apply A.
        rewrite PTree.gso; auto.
        congruence.
Qed.

Lemma fr_is_map:
  forall {A B} (f: A -> B) l z,
    (fold_right (fun elt acc => f elt :: acc) z l) =
    map f l ++ z.
Proof.
  induction l; simpl; intros; eauto.
  f_equal. auto.
Qed.
                            

Lemma blocks_of_env_charact:
  forall vars e' m' e m
    (AV: alloc_variables e m vars e' m')
    (lnr: list_norepet (map fst vars))
    (range: forall id b t, e!id = Some (b,t) -> Plt b (Mem.nextblock m))
    (inj0: forall id1 id2 b1 b2 ty1 ty2, e ! id1 = Some (b1,ty1) -> e!id2 = Some (b2,ty2) ->
                                    id1<>id2 -> b1 <> b2)
    (eid: forall id, ~ In id (map fst vars) -> e ! id = e' ! id)
    (eid': forall id, In id (map fst vars) -> e ! id = None)
  ,
    Permutation (map forb (blocks_of_env e'))
                (fold_right (fun elt acc => (0,sizeof (snd elt))::acc)
                            (map forb (blocks_of_env e)) vars).
Proof.
  induction vars; simpl; intros; eauto.
  - inv AV. reflexivity.
  - inv lnr. inv AV.
    rewrite IHvars; eauto; clear IHvars.
    + rewrite fr_is_map. rewrite  fr_is_map.
      rewrite (Permutation_cons_app _ _ _ (Permutation_refl _)).
      apply Permutation_app_head.
      rewrite Permutation_map.
      2: apply blocks_set_elements_permut; auto.
      * simpl. unfold forb at 1; simpl. reflexivity.
      * simpl in *. intro; dex.
        destruct (peq id0 id). subst.
        rewrite eid' in H; auto; congruence.
        destruct (in_dec peq id0 (map fst vars)).
        rewrite eid' in H; auto; congruence.
        eapply range in H; eauto.
        exploit Mem.alloc_result; eauto. intro. subst. xomega.
    + intros id0 b t.
      rewrite PTree.gsspec.
      destr_cond_match. subst. intro A; inv A.
      eapply Mem.valid_new_block; eauto.
      intro EI.
      exploit range; eauto.
      exploit Mem.nextblock_alloc; eauto. intro A; rewrite A.
      ppsimpl; lia.
    + intros id1 id2 b0 b2 ty1 ty2 EI1 EI2 DIFF.
      rewrite PTree.gsspec in EI1, EI2.
      destruct (peq id1 id); subst; inv EI1;
      destruct (peq id2 id); subst; inv EI2.
      * congruence.  
      * exploit range. eexact H0. exploit Mem.alloc_result; eauto.
        intros; intro; repeat subst. ppsimpl; lia.
      * exploit range. eexact H0. exploit Mem.alloc_result; eauto.
        intros; intro; repeat subst. ppsimpl; lia.
      * eapply inj0; eauto.
    + simpl in *; intros.
      rewrite PTree.gsspec.
      destr.
      subst.
      erewrite alloc_variables_in_not_in_vars; eauto.
      rewrite PTree.gss; auto.
      eapply eid; eauto. destr.
    +
      simpl in *; intros.
      rewrite PTree.gsspec; destr.
      eapply eid'; eauto.
Qed.
      
Lemma filter_rev:
  forall {A} (f: A -> bool) l,
    filter f (rev l) = rev (filter f l).
Proof.
  induction l; simpl; intros; eauto.
  destr. rewrite filter_app. simpl. destr.
  rewrite filter_app. simpl. destr.
  rewrite app_nil_r; auto.
Qed.

Lemma align_mul:
  forall x y,
    y > 0 ->
    align (y*x) y = y*x.
Proof.
  intros.
  rewrite Z.mul_comm.
  apply Mem.align_mul; auto.
Qed.

Lemma align_eq_8:
  forall z, 0 < z <= 8 ->
       align z (two_power_nat MA) = two_power_nat MA.
Proof.
  intros.
  apply Mem.align_small.
  auto.
  split; auto. lia.
  transitivity 8; auto. lia.
  change 8 with (two_power_nat 3).
  rewrite ! two_power_nat_two_p. apply two_p_monotone. generalize (MA_bound); lia. 
Qed.

Lemma cenv_bound_app:
  forall c l,
    cenv_bound c l <-> Forall (fun x => 0 < sizeof (snd x) <= 8 \/ VSet.mem (fst x) c = false) l.
Proof.
  induction l; simpl; intros; eauto.
  - split; intros; constructor.
  - split; intros.
    + constructor.
      inv H. auto.
      inv H. rewrite IHl in H2. auto.
    + inv H. destruct a; constructor.
      rewrite IHl; auto.
      auto.
Qed.

Lemma Forall_app:
  forall {A} (P: A -> Prop) l1 l2,
    Forall P l1 -> Forall P l2 ->
    Forall P (l1 ++ l2).
Proof.
  intros A P l1 l2 F1 F2.
  rewrite Forall_forall in *.
  intros x IN.
  apply in_app_or in IN.
  destruct IN as [IN|IN]; eauto.
Qed.

Lemma cenv_bound_rev:
  forall c l
    (CB : cenv_bound c l),
    cenv_bound c (rev l).
Proof.
  induction l; simpl; intros; eauto.
  rewrite cenv_bound_app.
  apply Forall_app.
  rewrite <- cenv_bound_app.
  apply IHl. inv CB; auto.
  inv CB.
  constructor; [auto|constructor].
Qed.

Opaque align.
Opaque Z.mul Z.add.
Opaque Z.mul Z.of_nat.


Lemma free_blocks_0:
  forall m tm (FrB: free_blocks m tm 0),
    (Mem.nb_boxes_used_m tm <= Mem.nb_boxes_used_m m)%nat.
Proof.
  intros; red in FrB. rewrite plus_0_r in FrB. apply FrB. 
Qed.

Lemma free_blocks_0':
  forall m tm,
    (Mem.nb_boxes_used_m tm <= Mem.nb_boxes_used_m m)%nat ->
    free_blocks m tm 0.
Proof.
  red; intros. rewrite plus_0_r. auto.
Qed.

(* Oracles used for the semantics of Clight.
 * [ns1] is used for the semantics before SimplLocals
 * [ns2] is used after the transformation.
 * This enables to recycle blocks that are not injected by Clight into extra space
 *
 * Example: (b1,b2,b3) and 4 extra spaces before SL
 *          (b1)       and 6 extra spaces after SL
 *)

Variable ns1 ns2: ident -> nat.
Hypothesis ns1_spec:
  forall f,
    In (Gfun (Internal f)) (map snd (prog_defs prog)) ->
    (ns1 (fn_id f) <=
     ns2 (fn_id f)
     <= ns1 (fn_id f) + 
       length
         (filter
            (fun it : VSet.elt * type =>
               VSet.mem (fst it)
                        (cenv_for_gen (addr_taken_stmt (fn_body f))
                                      (varsort (fn_params f ++ fn_vars f))))
            (varsort (fn_params f ++ fn_vars f)))) % nat.


Lemma contra:
  forall A (P Q: A -> Prop),
    (forall x, P x -> Q x) -> (forall x, ~ Q x -> ~ P x).
Proof.
  intros.
  intro. apply H0; apply H; auto.
Qed.

Lemma assign_loc_inject:
  forall sm ei (wf: wf_inj ei) f ty m locofs v m' tm loc'ofs' v'
    (IWB: inj_well_behaved f m tm)
    (AL: assign_loc ty m locofs v m')
    (EIaddr: ei f (locofs) (loc'ofs'))
    (SI: sep_inj m f locofs)
    (EIval: ei f v v')
    (SI': sep_inj m f v)
    (INJ: Mem.inject sm ei f m tm),
  exists tm',
    assign_loc ty tm loc'ofs' v' tm'
    /\ Mem.inject sm ei f m' tm'
    /\ (forall b chunk v,
          f b = None -> Mem.load chunk m b 0 = Some v -> Mem.load chunk m' b 0 = Some v).
Proof.
  intros. inv AL.
- (* by value *)
  exploit storev_inject; eauto.
  intros [tm' [A B]].
  exists tm'; split. eapply assign_loc_value; eauto. 
  split. auto.
  intros b chunk0 v0 Fnone LOAD. rewrite <- LOAD.
  unfold Mem.storev in STOREV; revert STOREV; destr.
  intros; eapply Mem.load_store_other; eauto.
  left.
  generalize (forget_norm _ _ wf _ _ _ INJ IWB _ _ EIaddr SI).
  rewrite Heqv1; intro C; inv C. congruence.

- (* by copy *)
  rename b' into bsrc. rename ofs' into osrc. 
  rename b into bdst. rename ofs into odst.
  generalize (forget_norm _ _ wf _ _ _ INJ IWB _ _ EIaddr SI).
  generalize (forget_norm _ _ wf _ _ _ INJ IWB _ _ EIval SI').
  rewrite MNv, MNaddr.
  intros A B; inv A; inv B.
  exploit Mem.loadbytes_length; eauto. intros LEN.
  assert (SZPOS: sizeof ty > 0).
  { generalize (sizeof_pos ty); omega. }
  assert (RPSRC: Mem.range_perm m bsrc (Int.unsigned osrc) (Int.unsigned osrc + sizeof ty) Cur Nonempty).
  eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
  assert (RPDST: Mem.range_perm m bdst (Int.unsigned odst) (Int.unsigned odst + sizeof ty) Cur Nonempty).
  replace (sizeof ty) with (Z_of_nat (length bytes)).
  eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
  rewrite LEN. apply nat_of_Z_eq. omega.
  assert (PSRC: Mem.perm m bsrc (Int.unsigned osrc) Cur Nonempty).
  apply RPSRC. omega.
  assert (PDST: Mem.perm m bdst (Int.unsigned odst) Cur Nonempty).
  apply RPDST. omega.
  exploit Mem.address_inject.  eauto. eexact PSRC. eauto. intros EQ1.
  exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
  exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_mapped_inject; eauto. intros [tm' [C D]].
  exists tm'. 
  split.
  eapply assign_loc_copy; 
    try (now (rewrite <- EQ1 in A; apply A));
    try (now (rewrite <- EQ2 in C; apply C)); eauto.
  rewrite EQ1.
  intros; eapply Mem.aligned_area_inject with (m := m); eauto.
  apply alignof_blockcopy_1248.
  apply sizeof_alignof_blockcopy_compat.
  rewrite EQ2.
  intros; eapply Mem.aligned_area_inject with (m := m); eauto.
  apply alignof_blockcopy_1248.
  apply sizeof_alignof_blockcopy_compat.
  rewrite EQ1, EQ2.
  eapply Mem.disjoint_or_equal_inject with (m := m); eauto.
  apply Mem.range_perm_max with Cur; auto.
  apply Mem.range_perm_max with Cur; auto.
  split. auto.
  intros b chunk v0 Fnone LOAD. rewrite <- LOAD. eapply Mem.load_storebytes_other; eauto. 
  left. congruence.
- eexists; repSplit; eauto.
  econstructor 3; auto.
Qed.

Remark bind_parameter_temps_inv:
  forall id params args le le',
  bind_parameter_temps params args le = Some le' ->
  ~In id (var_names params) ->
  le'!id = le!id.
Proof.
  induction params; simpl; intros. 
  destruct args; inv H. auto.
  destruct a as [id1 ty1]. destruct args; try discriminate. 
  transitivity ((PTree.set id1 e le)!id). 
  eapply IHparams; eauto. apply PTree.gso. intuition. 
Qed.

Lemma sem_cast_expr_typ: forall e e' ty,
    sem_cast_expr e' ty ty <> None ->
    sem_cast_expr e ty ty <> None.
Proof.
  intros e e' ty. 
  unfold sem_cast_expr; des ty;
  try revert H; repeat destr; try des i.
Qed.

Lemma memval_rel_inject:
  forall f a b c
    (MR: memval_rel same_eval a b)
    (MI: memval_inject expr_inj_se f a c),
    memval_inject expr_inj_se f b c.
Proof.
  intros.
  inv MI. inv MR.
  destruct b. constructor.
  simpl in *.
  eapply expr_inj_se_l; eauto.
  simpl in *. des H0. des TYPorUNDEF. rewrite <- s. 
  right. red; intros; rewrite H. reflexivity.
Qed.

Lemma dep_store:
  forall chunk m b o  e2 m'
    (AL: Mem.store chunk m b o e2 = Some m')
    e b,
    depends_m m e b <-> depends_m m' e b.
Proof.
  intros.
  red.
  unfold Mem.bounds_of_block.
  Transparent Mem.store. simp AL.
Qed.

Lemma dep_storev:
  forall chunk m e1 e2 m'
    (AL: Mem.storev chunk m e1 e2 = Some m')
    e b,
    depends_m m e b <-> depends_m m' e b.
Proof.
  intros.
  unfold Mem.storev in AL; revert AL; destr_cond_match; try easy. intro; 
  eapply dep_store; eauto.
Qed.

Lemma dep_storebytes:
  forall m b o  e2 m'
    (AL: Mem.storebytes m b o e2 = Some m')
    e b,
    depends_m m e b <-> depends_m m' e b.
Proof.
  intros.
  red.
  unfold Mem.bounds_of_block.
  Transparent Mem.storebytes. simp AL.
Qed.

Lemma dep_assign_loc:
  forall ty m e1 e2 m'
    (AL: assign_loc ty m e1 e2 m')
    e b,
    depends_m m e b <->
    depends_m m' e b.
Proof.
  intros.
  inv AL.
  - eapply dep_storev; eauto.
  - eapply dep_storebytes; eauto.
  - tauto.
Qed.

Lemma depends_ptr: 
       forall m (b b' : block) (i : int),
         depends_m m (Eval (Vptr b i)) b' -> b = b'.
Proof.
  intros.
  eapply depends_ptr; eauto.
  intros b2; destruct (Mem.exists_two_cms m b2) as [cm [cm' [AA [B [C D]]]]].
  exists cm, cm'; eauto.
Qed.    

Lemma assign_loc_is_dynamic_block:
  forall t m e f m'
    (AL: assign_loc t m e f m'),
  forall b, Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b.
Proof.
  intros; inv AL; auto.
  -  unfold Mem.storev, Mem.store in STOREV; repeat destr_in STOREV; inv STOREV.
     unfold Mem.is_dynamic_block; destr.
  - unfold Mem.storebytes in SB; repeat destr_in SB; inv SB.
    unfold Mem.is_dynamic_block; destr.
  - tauto.
Qed.

Theorem store_params_correct:
  forall sm NS j f k cenv le lo hi te tlo thi e m params args m' 
    (BP: bind_parameters e m params args m')
    s tm tle1 tle2 targs
    (NOREPET : list_norepet (var_names params))
    (CASTED: list_forall2 expr_casted args (map snd params))
    (VINJ: list_ei expr_inj_se j args targs)
    (SEP: Forall (fun x => sep_inj m j x) args)
    (MENV: match_envs j cenv e le m tm lo hi te tle1 tlo thi)
    (MINJ: Mem.inject sm expr_inj_se j m tm)
    (IWB: inj_well_behaved j m tm)
    (TLE: forall id, ~In id (var_names params) -> tle2!id = tle1!id)
    (LE: forall id, In id (var_names params) -> le!id = None),
  exists tle tm',
    star (fun ge => step2 ge NS) tge (State f (store_params cenv params s) k te tle tm)
         E0 (State f s k te tle tm')
    /\ bind_parameter_temps params targs tle2 = Some tle
    /\ Mem.inject sm expr_inj_se j m' tm'
    /\ match_envs j cenv e le m' tm' lo hi te tle tlo thi
    /\ Mem.nextblock tm' = Mem.nextblock tm
    /\ (forall b, Mem.bounds_of_block tm' b = Mem.bounds_of_block tm b)
    /\ (forall b, Mem.mask tm' b = Mem.mask tm b)
    /\ (forall b, Mem.is_dynamic_block tm b <-> Mem.is_dynamic_block tm' b) /\
    Mem.nb_extra tm' = Mem.nb_extra tm.
Proof.
  induction 1; simpl; intros. 
  - (* base case *)
    inv VINJ. exists tle2; exists tm; repSplit; auto. apply star_refl. 
    apply match_envs_temps_exten with tle1; auto. tauto. 
  - (* inductive case *)
    inv NOREPET. inv CASTED. inv VINJ. inv SEP.
    exploit me_vars; eauto. instantiate (1 := id); intros MV.
    destruct (VSet.mem id cenv) eqn:?.
    + (* lifted to temp *) 
      eapply IHBP with (tle1 := PTree.set id b0 tle1); eauto.
      * revert H7; apply Forall_impl.
        unfold sep_inj.
        intros a SI b1 JB1 DEP.
        erewrite <- dep_assign_loc in DEP; eauto.
        eapply SI; eauto.
      * eapply match_envs_assign_lifted; eauto. 
      * inv MV; try congruence.
        inv H0; try congruence.
        unfold Mem.storev in STOREV. destr_in STOREV. 
        eapply Mem.store_unmapped_inject; eauto.
        rewrite ENV in H; inv H.
        exploit Mem.norm_ptr_same; eauto. intro A; inv A. auto.
      * eapply iwb_inv. eauto.
        now eapply assign_loc_bounds; eauto.
        now auto.
        now eapply assign_loc_mask; eauto.
        now auto.
        intros; xomega.
      * intros. repeat rewrite PTree.gsspec. destruct (peq id0 id). auto.
        apply TLE. intuition.
    + (* still in memory *)
      inv MV; try congruence. rewrite ENV in H; inv H.
      destruct H6 as [v1' [SCE SE]].
      destruct (sem_cast_expr_inject _ _ wf_inj_expr_inj_se _ _ _ _ _ SCE EI)
        as [tv [SCE' SE']].
      assert (EEI: expr_inj_se j v1 tv) by (eapply expr_inj_se_l; eauto; symmetry; auto).
      generalize (fun (pf1: expr_inj_se j (Eval (Vptr b Int.zero)) (Eval (Vptr b' Int.zero))) pf2
                  =>
                    assign_loc_inject
                      _ _ wf_inj_expr_inj_se
                      _ _ _ _ _ _ tm _ _ IWB H0 pf1 pf2 EEI H5 MINJ).
      intro A; trim A.
      apply vi_ei; auto. simpl. unfold Val.inj_ptr; rewrite MAPPED. rewrite Int.add_zero; auto.
      trim A.
      red; simpl; intros.
      
      intro DEP; apply depends_ptr in DEP. congruence.
      destruct A as [tm1 [A [B C]]].
      exploit IHBP. eauto. eauto. eauto.
      { revert H7; apply Forall_impl.
        unfold sep_inj.
        intros a SI b2 JB1 DEP'.
        erewrite <- dep_assign_loc in DEP'; eauto.
        eapply SI; eauto.
      }
      apply match_envs_change_temp.   
      eapply match_envs_invariant with (tm':=tm1); eauto.
      {
        intros bb PLT NDYN.
        eapply assign_loc_bounds; eauto.
      }
      {
        intros bb PLT NDYN.
        eapply assign_loc_bounds; eauto.
      }
      intros; eapply Mem.mi_inj_dynamic in MINJ; eauto. destr.
      intros; eapply assign_loc_is_dynamic_block; eauto.
      intros; eapply assign_loc_is_dynamic_block; eauto.
      apply LE; auto. auto.
      eauto.
      eapply iwb_inv. eauto.
      eapply assign_loc_bounds; eauto.
      eapply assign_loc_bounds; eauto.
      eapply assign_loc_mask; eauto.
      eapply assign_loc_mask; eauto.
      rewrite (assign_loc_nextblock _ _ _ _ _ A). intros; xomega.
      instantiate (2 := PTree.set id b0 tle2). 
      intros. repeat rewrite PTree.gsspec. destruct (peq id0 id). auto.
      apply TLE. intuition.
      intros. apply LE. auto.
      instantiate (1 := s). 
      intros [tle [tm' [U [V [X [Y [AA [AB [AC [AD NBE]]]]]]]]]].
      exists tle; exists tm'; repSplit; auto.
      * 
        eapply star_trans.
        eapply star_left. econstructor.
        eapply star_left. econstructor.  
        eapply eval_Evar_local. eauto. 
        eapply eval_Etempvar. erewrite bind_parameter_temps_inv; eauto.
        apply PTree.gss. 
        simpl. eauto. 
        simpl. eexact A. 
        apply star_one. constructor.
        reflexivity. reflexivity. 
        eexact U. 
        traceEq.
      * rewrite <- (assign_loc_nextblock _ _ _ _ _ A). auto.
      * intros. rewrite AB. symmetry; eapply assign_loc_bounds; eauto.
      * intros. rewrite AC. symmetry; eapply assign_loc_mask; eauto.
      * intros; rewrite <- AD. eapply assign_loc_is_dynamic_block; eauto.
      * rewrite NBE. symmetry; eapply assign_loc_nb_extra; eauto.
Qed.

Lemma bind_parameters_nextblock:
  forall e m params args m',
  bind_parameters e m params args m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction 1.
  auto.
  rewrite IHbind_parameters. eapply assign_loc_nextblock; eauto. 
Qed.

Lemma bind_parameters_load:
  forall e chunk b ofs,
  (forall id b' ty, e!id = Some(b', ty) -> b <> b') ->
  forall m params args m',
  bind_parameters e m params args m' ->
  Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  induction 2.
  auto.
  rewrite IHbind_parameters.
  assert (b <> b0) by eauto.
  inv H1. 
  - 
    unfold Mem.storev in STOREV; revert STOREV; destr.
    eapply Mem.norm_ptr_same in Heqv; inv Heqv. intro; 
    eapply Mem.load_store_other; eauto.
  - eapply Mem.norm_ptr_same in MNaddr; inv MNaddr.
    eapply Mem.load_storebytes_other; eauto.
  - auto.
Qed.

(** Freeing of local variables *)

Lemma free_blocks_of_env_perm_1:
  forall m e m' id b ty ofs k p,
  Mem.free_list m (blocks_of_env e) = Some m' ->
  e!id = Some(b, ty) ->
  Mem.perm m' b ofs k p ->
  0 <= ofs < sizeof ty ->
  False.
Proof.
  intros. exploit Mem.perm_free_list; eauto. intros [A B].
  apply B with 0 (sizeof ty); auto.
  unfold blocks_of_env. change (b, 0, sizeof ty) with (block_of_binding (id, (b, ty))).
  apply in_map. apply PTree.elements_correct. auto.
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

Lemma free_blocks_of_env_perm_2:
  forall m e m' id b ty,
  Mem.free_list m (blocks_of_env e) = Some m' ->
  e!id = Some(b, ty) ->
  Mem.range_perm m b 0 (sizeof ty) Cur Freeable.
Proof.
  intros. eapply free_list_perm'; eauto. 
  unfold blocks_of_env. change (b, 0, sizeof ty) with (block_of_binding (id, (b, ty))).
  apply in_map. apply PTree.elements_correct. auto.
Qed.

Fixpoint freelist_no_overlap (l: list (block * Z * Z)) : Prop :=
  match l with
  | nil => True
  | (b, lo, hi) :: l' =>
      freelist_no_overlap l' /\
      (forall b' lo' hi', In (b', lo', hi') l' ->
       b' <> b \/ hi' <= lo \/ hi <= lo')
  end.

Lemma can_free_list:
  forall l m,
    (forall b lo hi, In (b, lo, hi) l -> Mem.range_perm m b lo hi Cur Freeable
                                   /\ Mem.bounds_of_block m b = (lo, hi)) ->
  freelist_no_overlap l ->
  exists m', Mem.free_list m l = Some m'.
Proof.
  induction l; simpl; intros.
- exists m; auto.
- destruct a as [[b lo] hi]. destruct H0.
  destruct (Mem.range_perm_free m b lo hi) as [m1 A]; auto. 
  + apply H; auto.
  + unfold Mem.has_bounds. destruct (H _ _ _ (or_introl eq_refl)).
    rewrite H3. des (zeq lo lo); des (zeq hi hi).
  + rewrite A. apply IHl; auto.
    intros. split.
    * red; intros. eapply Mem.perm_free_1; eauto. 
      exploit H1; eauto. intros [B|B]. auto. right; omega.   
      eapply H; eauto.
    * generalize (H _ _ _ (or_intror H2)). intros [B C].
      generalize (H1 _ _ _ H2). intro D.
      generalize (H _ _ _ (or_introl eq_refl)). intros [E F]. 
      rewrite <- C.
      des (peq b0 b).
      assert (lo = lo0 /\ hi = hi0) by destr. des H3.
      generalize (Mem.size_block_snd m b). rewrite C. simpl. intro; subst.
      generalize (Mem.bounds_lo_0 m b); rewrite C; simpl; intro. subst.
      assert (Mem.size_block m b = 0). generalize (Mem.size_block_pos m b); des D; lia.
      rewrite H3 in *.
      erewrite Mem.free_bounds_exact; eauto. rewrite peq_true. auto.
      eapply Mem.bounds_free; eauto. 
Qed.

Lemma blocks_of_env_no_overlap:
  forall sm j cenv e le m lo hi te tle tlo thi tm
    (ME: match_envs j cenv e le m tm lo hi te tle tlo thi )
    (MINJ: Mem.inject sm expr_inj_se j m tm)
    (PERMS: forall id b ty, 
        e!id = Some(b, ty) -> Mem.range_perm m b 0 (sizeof ty) Cur Freeable)
    l
    (lnr: list_norepet (List.map fst l))
    (TEID: forall id bty, In (id, bty) l -> te!id = Some bty),
    freelist_no_overlap (List.map block_of_binding l).
Proof.
  induction l; simpl; intros.
  - auto.
  - destruct a as [id [b ty]]. simpl in *. inv lnr. split.
    + apply IHl; auto.
    + intros. exploit list_in_map_inv; eauto. intros [[id' [b'' ty']] [A B]].
      simpl in A. inv A. rename b'' into b'. 
      assert (TE: te!id = Some(b, ty)) by eauto. 
      assert (TE': te!id' = Some(b', ty')) by eauto. 
      exploit me_mapped. eauto. eexact TE. intros [b0 [INJ E]]. 
      exploit me_mapped. eauto. eexact TE'. intros [b0' [INJ' E']]. 
      destruct (zle (sizeof ty) 0); auto. 
      destruct (zle (sizeof ty') 0); auto. 
      assert (b0 <> b0').
      { eapply me_inj; eauto. red; intros; subst; elim H1.
        change id' with (fst (id', (b', ty'))). apply List.in_map; auto. }
      assert (Mem.perm m b0 0 Max Nonempty). 
      { apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable.
        eapply PERMS; eauto. omega. auto with mem. }
      assert (Mem.perm m b0' 0 Max Nonempty). 
      { apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable.
        eapply PERMS; eauto. omega. auto with mem. }
      exploit Mem.inject_no_overlap; eauto. intros [A|A]. auto. omegaContradiction.
Qed.

Lemma free_list_permut:
  forall l
    (LNR: list_norepet (map fst (map fst l)))
    l' (P: Permutation.Permutation l l')
    m m'
    (* (BndsExact: Forall (fun x => Mem.bounds_of_block m (fst (fst x)) = (snd (fst x), snd x)) l) *)
    (FL: Mem.free_list m l = Some m')
    tm (ME: mem_equiv m tm),
  exists tm', Mem.free_list tm l' = Some tm' /\ mem_equiv m' tm'.
Proof.
  induction 2; simpl in *; intros; auto.
  - inv FL; eexists; split; eauto. 
  - repeat destr_in FL.
    exploit free_mem_rel; eauto. intros [m2 [A B]].
    intros; rewrite A.
    eapply IHP; eauto. inv LNR; auto.
  - repeat destr_in FL. 
    inv LNR. inv H2. simpl in *.
    assert (b <> b0) by intuition.
    Transparent Mem.free.
    unfold Mem.free in *.
    repeat destr_in Heqo; repeat destr_in Heqo0.
    inv Heqo. inv Heqo0.
    assert (Mem.range_perm tm b0 z2 z1 Cur Freeable).
    {
      eapply range_perm_mem_rel; eauto.
      red; intros. unfold Mem.range_perm in r0.
      apply r0 in H0. erewrite Mem.perm_unchecked_free in H0; eauto. intuition.
      unfold Mem.has_bounds in Heqb1; destr_in Heqb1.
      des (zeq z0 z3); des (zeq z z4).
    }
    destr.
    unfold Mem.has_bounds at 1.
    unfold Mem.has_bounds in Heqb0.
    destr_in Heqb0.
    rewrite Mem.unchecked_free_bounds' in Heqp. destr_in Heqp.
    erewrite mem_lessdef_bounds in Heqp; eauto.
    rewrite Heqp. rewrite Heqb0.
    assert (Mem.range_perm (Mem.unchecked_free tm b0 z2 z1) b z0 z Cur Freeable).
    {
      red; intros.
      des (zeq z2 z3); des (zeq z1 z4).
      rewrite (Mem.perm_unchecked_free _ _ _ _ Heqp _ eq_refl); eauto.
      split; auto.
      eapply range_perm_mem_rel; eauto.
    }
    destr.
    unfold Mem.has_bounds at 1.
    unfold Mem.has_bounds in Heqb1.
    destr_in Heqb1.
    rewrite Mem.unchecked_free_bounds'.
    des (eq_block b b0). 
    erewrite mem_lessdef_bounds in Heqp0; eauto.
    rewrite Heqp0. rewrite Heqb1.
    exploit free_list_mem_equiv.
    2: eexact FL.
    Focus 2. 
    intros [m2' [A B]].
    rewrite A. eexists; split; eauto.
    inv ME.
    unfold Mem.unchecked_free.
    simpl.  
    constructor; simpl; auto. 
    + simpl. unfold Mem.perm; simpl; intros.
      eapply mem_contents_eq.
      rewrite ! PMap.gsspec in H5.
      repeat destr_in H5.
    + simpl. intros. rewrite mem_access_eq. intros.
      repeat rewrite ! PMap.gsspec.
      repeat destr; auto. 
      rewrite mem_access_eq; auto. 
    + intros; rewrite ! PMap.gsspec.
      rewrite ! mem_blocksize_eq.
      repeat destr.
  - specialize (IHP1 LNR _ _ FL _ ME).
    trim IHP2.
    eapply permutation_norepet.
    apply Permutation.Permutation_map.
    apply Permutation.Permutation_map. eauto. auto.
    destruct IHP1 as [tm' [A B]].
    specialize (IHP2 tm tm').
    specialize (IHP2 A _ (mem_rel_refl _ wf_mr_se _)).
    destruct IHP2 as [tm'0 [C D]]; exists tm'0; split; eauto.
    rewrite B, D. reflexivity.
Qed.


Opaque minus.

Lemma filter_Forall:
  forall A f (l: list A)
    (F: Forall (fun x => f x = true) l),
    filter f l = l.
Proof.
  induction l; simpl; intros; eauto.
  inv F. rewrite H1. f_equal; auto.
Qed.

Definition inj (j:meminj) :=
  (fun (elt : block) (acc : list block) =>
                  match j elt with
                  | Some (b', _) => b' :: acc
                  | None => acc
                  end).

(** Matching global environments *)

Inductive match_globalenvs (f: meminj) (bound: block): Prop :=
  | mk_match_globalenvs
      (DOMAIN: forall b, Plt b bound -> f b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, f b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).

Lemma match_globalenvs_preserves_globals:
  forall f,
  (exists bound, match_globalenvs f bound) ->
  meminj_preserves_globals ge f.
Proof.
  intros. destruct H as [bound MG]. inv MG.
  split; intros. eauto. split; intros. eauto. symmetry. eapply IMAGE; eauto.
Qed. 

(** Evaluation of expressions *)

Section EVAL_EXPR.

Variables e te: env.
Variables le tle: temp_env.
Variables m tm: mem.
Variable f: meminj.
Hypothesis IWB: inj_well_behaved f m tm.

Variable cenv: compilenv.
Variables lo hi tlo thi: block.
Hypothesis MATCH: match_envs f cenv e le m tm lo hi te tle tlo thi.
Variable sm: bool.
Hypothesis MEMINJ: Mem.inject sm expr_inj_se f m tm.
Hypothesis GLOB: exists bound, match_globalenvs f bound.

Lemma typeof_simpl_expr:
  forall a, typeof (simpl_expr cenv a) = typeof a.
Proof.
  destruct a; simpl; auto. destruct (VSet.mem i cenv); auto.
Qed.

Lemma deref_loc_inject:
  forall ty locofs v loc'ofs',
    deref_loc ty m locofs v ->
    sep_inj m f locofs ->
    expr_inj_se f (locofs) (loc'ofs') ->
    exists tv, deref_loc ty tm loc'ofs' tv /\ expr_inj_se f v tv.
Proof.
  intros. inv H. 
  - (* by value *)
    exploit loadv_inject; eauto. intros [tv [A B]]. 
    exists tv; split; auto. eapply deref_loc_value; eauto.
  - (* by reference *)
    exists (loc'ofs'); split; auto. eapply deref_loc_reference; eauto.
  - (* by copy *)
    exists (loc'ofs'); split; auto. eapply deref_loc_copy; eauto.
Qed.

Lemma eval_simpl_expr:
  forall a v,
  eval_expr ge e le m a v ->
  compat_cenv (addr_taken_expr a) cenv ->
  exists tv, eval_expr tge te tle tm (simpl_expr cenv a) tv /\ expr_inj_se f v tv

with eval_simpl_lvalue:
  forall a bofs,
  eval_lvalue ge e le m a bofs ->
  compat_cenv (addr_taken_expr a) cenv ->
  match a with Evar id ty => VSet.mem id cenv = false | _ => True end ->
  exists b'ofs', eval_lvalue tge te tle tm (simpl_expr cenv a) b'ofs' /\ expr_inj_se f (bofs) (b'ofs').
Proof.
  destruct 1; simpl; intros.
  - (* const *)
    exists (Eval (Vint i)); split; auto. constructor. apply vi_ei; auto.
  - exists (Eval (Vfloat f0)); split; auto. constructor. apply vi_ei; auto.
  - exists (Eval (Vsingle f0)); split; auto. constructor. apply vi_ei; auto.
  - exists (Eval (Vlong i)); split; auto. constructor. apply vi_ei; auto.
  - (* tempvar *)
    exploit me_temps; eauto. intros [[tv [A B]] C].
    exists tv; split; auto. constructor; auto.
  - (* addrof *)
    exploit eval_simpl_lvalue; eauto.
    destruct a; auto with compat.
    destruct a; auto. destruct (VSet.mem i cenv) eqn:?; auto.
    elim (H0 i). apply VSet.singleton_2. auto. apply VSet.mem_2. auto.
    intros [b'ofs' [A B]].
    exists (b'ofs'); split; auto. constructor; auto.
  - (* unop *)
    exploit eval_simpl_expr; eauto. intros [tv1 [A B]].
    exploit sem_unary_operation_expr_inject; eauto. intros [tv [C D]].
    exists tv; split; auto. econstructor; eauto. rewrite typeof_simpl_expr; auto.
  - (* binop *)
    exploit eval_simpl_expr. eexact H. eauto with compat. intros [tv1 [A B]].
    exploit eval_simpl_expr. eexact H0. eauto with compat. intros [tv2 [C D]].
    exploit sem_binary_operation_expr_inject; eauto. intros [tv [E F]].
    exists tv; split; auto. econstructor; eauto. repeat rewrite typeof_simpl_expr; auto.
  - (* cast *)
    exploit eval_simpl_expr; eauto. intros [tv1 [A B]].
    exploit sem_cast_expr_inject; eauto. intros [tv2 [C D]].
    exists tv2; split; auto. econstructor. eauto. rewrite typeof_simpl_expr; auto.
  - (* rval *)
    assert (EITHER: (exists id, exists ty, a = Evar id ty /\ VSet.mem id cenv = true)
                    \/ (match a with Evar id _ => VSet.mem id cenv = false | _ => True end)).
    { destruct a; auto. destruct (VSet.mem i cenv) eqn:?; auto. left; exists i; exists t; auto.   }
    destruct EITHER as [ [id [ty [EQ OPT]]] | NONOPT ].
    + (* a variable pulled out of memory *)
      subst a. simpl. rewrite OPT.
      exploit me_vars; eauto. instantiate (1 := id). intros MV.
      inv H; inv MV; try congruence.
      rewrite ENV in H5; inv H5.
      inv H0; try congruence.
      assert (chunk0 = chunk). simpl in H. congruence. subst chunk0.
      assert (v0 = v). unfold Mem.loadv in H2. revert H2; destr.
      apply Mem.norm_ptr_same in Heqv1; inv Heqv1.
      rewrite Int.unsigned_zero. congruence. subst v0.
      exists tv; split; auto. constructor; auto.
      simpl in H; congruence.
      simpl in H; congruence.
    + (* any other l-value *)
      exploit eval_simpl_lvalue; eauto. intros [loc'ofs' [A B]].
      exploit deref_loc_inject; eauto.
      Focus 2.
      intros [tv [C D]].
      exists tv; split; auto. econstructor. eexact A. rewrite typeof_simpl_expr; auto.
      eapply expr_inj_se_not_dep; eauto.

  - (* lvalues *)
    destruct 1; simpl; intros.
    + (* local var *)
      rewrite H1.
      exploit me_vars; eauto. instantiate (1 := id). intros MV. inv MV; try congruence.
      rewrite ENV in H; inv H.
      exists (Eval (Vptr b' Int.zero)); split.
      apply eval_Evar_local; auto.
      apply vi_ei; auto. simpl; unfold Val.inj_ptr; rewrite MAPPED; auto.
    + (* global var *)
      rewrite H2.
      exploit me_vars; eauto. instantiate (1 := id). intros MV. inv MV; try congruence.
      exists (Eval (Vptr l Int.zero)); split.
      apply eval_Evar_global. auto. rewrite <- H0. apply symbols_preserved.
      apply vi_ei; auto. simpl; unfold Val.inj_ptr. destruct GLOB as [bound GLOB1]. inv GLOB1.
      rewrite DOMAIN; eauto.
    + (* deref *)
      exploit eval_simpl_expr; eauto. intros [tv [A B]].
      eexists; split; eauto.
      econstructor; eauto.
    + (* field struct *)
      exploit eval_simpl_expr; eauto. intros [tv [A B]].
      eexists; split; eauto.
      eapply eval_Efield_struct; eauto. rewrite typeof_simpl_expr; eauto.
      unfold Val.add. eapply ei_binop; auto.
      apply vi_ei; simpl; auto.
    + (* field union *)
      exploit eval_simpl_expr; eauto. intros [tv [A B]].
      econstructor; split.
      eapply eval_Efield_union; eauto. rewrite typeof_simpl_expr; eauto. auto.
Qed.

Inductive expr_list_casted : list expr_sym -> typelist -> Prop :=
  expr_list_casted_nil: expr_list_casted nil Tnil
| expr_list_casted_cons:
    forall e el t tl (EC: expr_casted e t)
      (ELC: expr_list_casted el tl),
      expr_list_casted (e::el) (Tcons t tl).
      
Lemma eval_simpl_exprlist:
  forall al tyl vl,
  eval_exprlist ge e le m al tyl vl ->
  compat_cenv (addr_taken_exprlist al) cenv ->
  expr_list_casted vl tyl /\
  exists tvl,
     eval_exprlist tge te tle tm (simpl_exprlist cenv al) tyl tvl
  /\ list_ei expr_inj_se f vl tvl.
Proof.
  induction 1; simpl; intros.
  - split. constructor. econstructor; split. constructor. constructor. 
  - exploit eval_simpl_expr; eauto with compat. intros [tv1 [A B]].
    exploit sem_cast_expr_inject; eauto. intros [tv2 [C D]].
    exploit IHeval_exprlist; eauto with compat. intros [E [tvl [F G]]].
    split. constructor; auto. eapply Equivalences.sem_cast_expr_idem; eauto. 
    exists (tv2 :: tvl); split. econstructor; eauto.
    rewrite typeof_simpl_expr; auto.
    econstructor; eauto.
Qed.

End EVAL_EXPR.


Definition size_env e :=
  size_list (blocks_of_env e).


Lemma match_cont_sm:
  forall e m m' m'' N,
  Mem.free_list m (blocks_of_env e) = Some m' ->
  release_boxes m' N = Some m'' ->
  (Mem.nb_boxes_used_m m'' =
   Mem.nb_boxes_used_m m - size_env e - N)%nat.
Proof.
  intros e m m' m'' N FL REL.
  generalize (release_nb_boxes_used _ _ _ REL).
  generalize (free_list_nb_boxes_used _ _ _ FL). unfold size_env. lia.
Qed.


(** Matching continuations *)

Inductive match_cont (f: meminj): compilenv -> cont -> cont -> mem -> mem -> block -> block -> Prop :=
  | match_Kstop: forall cenv m tm bound tbound hi ,
      match_globalenvs f hi -> Ple hi bound -> Ple hi tbound ->
      match_cont f cenv Kstop Kstop m tm bound tbound 
  | match_Kseq: forall cenv s k ts tk m tm bound tbound,
      simpl_stmt cenv s = OK ts ->
      match_cont f cenv k tk m tm bound tbound  ->
      compat_cenv (addr_taken_stmt s) cenv ->
      match_cont f cenv (Kseq s k) (Kseq ts tk) m tm bound tbound
  | match_Kloop1: forall cenv s1 s2 k ts1 ts2 tk m tm bound tbound ,
      simpl_stmt cenv s1 = OK ts1 ->
      simpl_stmt cenv s2 = OK ts2 ->
      match_cont f cenv k tk m tm bound tbound  ->
      compat_cenv (VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)) cenv ->
      match_cont f cenv (Kloop1 s1 s2 k) (Kloop1 ts1 ts2 tk) m tm bound tbound 
  | match_Kloop2: forall cenv s1 s2 k ts1 ts2 tk m tm bound tbound ,
      simpl_stmt cenv s1 = OK ts1 ->
      simpl_stmt cenv s2 = OK ts2 ->
      match_cont f cenv k tk m tm bound tbound  ->
      compat_cenv (VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)) cenv ->
      match_cont f cenv (Kloop2 s1 s2 k) (Kloop2 ts1 ts2 tk) m tm bound tbound
  | match_Kswitch: forall cenv k tk m tm bound tbound ,
      match_cont f cenv k tk m tm bound tbound  ->
      match_cont f cenv (Kswitch k) (Kswitch tk) m tm bound tbound 
  | match_Kcall: forall cenv optid fn e le k tfn te tle tk m tm hi thi lo tlo bound tbound x ,
      transf_function fn = OK tfn ->
      match_envs f (cenv_for fn) e le m tm lo hi te tle tlo thi ->
      match_cont f (cenv_for fn) k tk m tm lo tlo  ->
      check_opttemp (cenv_for fn) optid = OK x ->
      Ple hi bound -> Ple thi tbound ->
      (ns1 (fn_id fn) + size_env e >= ns2 (fn_id tfn) + size_env te)%nat ->
      In (Gfun (Internal fn)) (map snd (prog_defs prog)) ->
      match_cont f cenv (Kcall optid fn e le k)
                        (Kcall optid tfn te tle tk) m tm bound tbound .

(** Invariance property by change of memory and injection *)

Lemma match_cont_invariant:
  forall f' m' f cenv k tk m tm tm' bound tbound
    (MC: match_cont f cenv k tk m tm bound tbound)
    (LOAD: forall b chunk v,
        f b = None -> Plt b bound -> Mem.load chunk m b 0 = Some v -> Mem.load chunk m' b 0 = Some v)
    (B: forall b, Plt b bound -> ~ Mem.is_dynamic_block m b ->
             Mem.bounds_of_block m b = Mem.bounds_of_block m' b)
    (B': forall b, Plt b tbound -> ~ Mem.is_dynamic_block tm b ->
              Mem.bounds_of_block tm b = Mem.bounds_of_block tm' b)
    (INCR: inject_incr f f')
    (INJ1: forall b, Plt b bound -> f' b = f b)
    (INJ2: forall b b' delta, f' b = Some(b', delta) -> Plt b' tbound -> f' b = f b)
    (DYNinject: forall b b' delta,
        f b = Some (b',delta) ->
        (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block tm b'))
    (DYNsame: forall b, Plt b bound ->
                   (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b))
    (DYNsame': forall b, Plt b tbound ->
                    (Mem.is_dynamic_block tm b <-> Mem.is_dynamic_block tm' b)),
    match_cont f' cenv k tk m' tm' bound tbound .
Proof.
  induction 1; intros; econstructor; eauto.
  - (* globalenvs *)
    inv H. constructor; intros; eauto.
    assert (f b1 = Some (b2, delta)). rewrite <- H; symmetry; eapply INJ2; eauto. xomega.
    eapply IMAGE; eauto.
  - (* call *)
    eapply match_envs_invariant; eauto. 
    intros. apply LOAD; auto. inv H0. xomega.
    intros. apply B; auto. inv H0; xomega.
    intros. apply B'; auto. inv H0; xomega.
    intros. apply INJ1; auto; xomega.
    intros. eapply INJ2; eauto; xomega.
    intros. apply DYNsame. xomega.
    intros. apply DYNsame'. xomega.
  - eapply IHMC; eauto.
    intros; apply LOAD; auto. inv H0; xomega.
    intros. apply B; auto. inv H0; xomega.
    intros. apply B'; auto. inv H0; xomega.
    intros; apply INJ1. inv H0; xomega.
    intros; eapply INJ2; eauto. inv H0; xomega.
    intros. apply DYNsame. inv H0; xomega.
    intros. apply DYNsame'. inv H0; xomega.
Qed.

(** Invariance by assignment to location "above" *)

Lemma match_cont_assign_loc:
  forall f cenv k tk m bound tbound ty locofs v m' tm tm'
    (MC: match_cont f cenv k tk m tm bound tbound)
    (AL: assign_loc ty m locofs v m')
    (MNaddr: forall b o, Mem.mem_norm m locofs = Vptr b o -> Ple bound b)
    (Bnds: forall b, Mem.bounds_of_block tm b = Mem.bounds_of_block tm' b)
    (EQ: Mem.nextblock tm = Mem.nextblock tm')
    (DYNinject: forall b b' delta,
        f b = Some (b',delta) ->
        (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block tm b'))
    (DYNsame': forall b, Plt b tbound ->
                    (Mem.is_dynamic_block tm b <-> Mem.is_dynamic_block tm' b)),
    match_cont f cenv k tk m' tm' bound tbound.
Proof.
  intros.
  eapply match_cont_invariant; eauto.
  - intros b chunk v0 Fnone PLT LOAD. rewrite <- LOAD. inv AL; auto.
    + (* scalar *)
      unfold Mem.storev in STOREV; destr_in STOREV.
      eapply Mem.load_store_other; eauto. left.
      specialize (MNaddr _ _ eq_refl). unfold block; xomega. 
    +  (* block copy *)
      eapply Mem.load_storebytes_other; eauto. left.
      specialize (MNaddr _ _ MNaddr0). unfold block; xomega.
  - intros b PLT DYN. inv AL; auto.
    eapply Mem.storev_bounds; eauto.
    eapply Mem.bounds_of_block_storebytes; eauto.
  - intros; eapply assign_loc_is_dynamic_block; eauto.
Qed.

(** Invariance by external calls *)

Lemma match_cont_extcall:
  forall f cenv k tk m bound tbound tm f' m' tm'
    (MC: match_cont f cenv k tk m tm bound tbound)
    (UNCH: Mem.unchanged_on (loc_unmapped f) m m')
    (Bn: forall b : positive,
        Plt b bound -> ~ Mem.is_dynamic_block m b ->
        Mem.bounds_of_block m b = Mem.bounds_of_block m' b)
    (B': forall b : positive,
        Plt b tbound -> ~ Mem.is_dynamic_block tm b ->
        Mem.bounds_of_block tm b = Mem.bounds_of_block tm' b)
    (INCR: inject_incr f f')
    (SEP: inject_separated f f' m tm)
    (PLE1: Ple bound (Mem.nextblock m)) (PLE2: Ple tbound (Mem.nextblock tm))
    (DYNinject: forall b b' delta,
        f b = Some (b',delta) ->
        (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block tm b'))
    (DYNsame: forall b, Plt b bound ->
                   (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b))
    (DYNsame': forall b, Plt b tbound ->
                    (Mem.is_dynamic_block tm b <-> Mem.is_dynamic_block tm' b)),
  match_cont f' cenv k tk m' tm' bound tbound.
Proof.
  intros. eapply match_cont_invariant; eauto. 
  - intros. eapply Mem.load_unchanged_on; eauto.
  - red in SEP. intros. destruct (f b) as [[b' delta] | ] eqn:?. auto. 
    destruct (f' b) as [[b' delta] | ] eqn:?; auto. 
    exploit SEP; eauto. unfold Mem.valid_block. intros [A B]. xomegaContradiction.
  - red in SEP. intros. destruct (f b) as [[b'' delta''] | ] eqn:?. auto. 
    exploit SEP; eauto. unfold Mem.valid_block. intros [A B]. xomegaContradiction.
Qed.

(** Invariance by change of bounds *)

Lemma match_cont_incr_bounds:
  forall f cenv k tk m tm bound tbound,
  match_cont f cenv k tk m tm bound tbound ->
  forall bound' tbound',
    Ple bound bound' -> Ple tbound tbound' ->
  match_cont f cenv k tk m tm bound' tbound'.
Proof.
  induction 1; intros; try solve [econstructor; eauto; xomega].
Qed.

(** [match_cont] and call continuations. *)

Lemma match_cont_change_cenv:
  forall f cenv k tk m tm bound tbound cenv',
  match_cont f cenv k tk m tm bound tbound ->
  is_call_cont k ->
  match_cont f cenv' k tk m tm bound tbound.
Proof.
  intros. inv H; simpl in H0; try contradiction; econstructor; eauto.
Qed.

Lemma match_cont_is_call_cont:
  forall f cenv k tk m tm bound tbound,
  match_cont f cenv k tk m tm bound tbound ->
  is_call_cont k ->
  is_call_cont tk.
Proof.
  intros. inv H; auto. 
Qed.

Lemma match_cont_call_cont:
  forall f cenv k tk m tm bound tbound,
  match_cont f cenv k tk m tm bound tbound ->
  forall cenv',
  match_cont f cenv' (call_cont k) (call_cont tk) m tm bound tbound.
Proof.
  induction 1; simpl; auto; intros; econstructor; eauto.
Qed.


(** [match_cont] and freeing of environment blocks *)

Lemma match_cont_free_env':
  forall sm f cenv e le m lo hi te tle tm tlo thi k tk m' tm' 
    (IWB: inj_well_behaved f m tm)
    fn
    (* (DIFF:   (two_power_nat MA) * Z.of_nat (ns1 (fn_id fn)) + *)
    (*          align (Mem.size_mem_blocks (blocks_of_env e) 0) (two_power_nat MA) >= *)
    (*          (two_power_nat MA) * Z.of_nat (ns2 (fn_id fn)) + *)
    (*          align (Mem.size_mem_blocks (blocks_of_env te) 0) (two_power_nat MA)) *)
  (MENV: match_envs f cenv e le m tm lo hi te tle tlo thi)
  (MC: match_cont f cenv k tk m tm lo tlo)
  (PLE1: Ple hi (Mem.nextblock m))
  (PLE2: Ple thi (Mem.nextblock tm))
  (FL1: Mem.free_list m (blocks_of_env e) = Some m')
  (FL2: Mem.free_list tm (blocks_of_env te) = Some tm')
  ei (MINJ: Mem.inject sm ei f m tm)
  m2' (MR: MemReserve.release_boxes m' (ns1 (fn_id fn)) = Some m2')
  tm2' (MR': MemReserve.release_boxes tm' (ns2 (fn_id fn)) = Some tm2'),
    match_cont f cenv k tk m2' tm2' (Mem.nextblock m2') (Mem.nextblock tm2').
Proof.
  intros. apply match_cont_incr_bounds with lo tlo.
  - eapply match_cont_invariant; eauto. 
    + intros. rewrite <- H1.  erewrite <- (Mem.free_list_load _ _ _ _ _ FL1); eauto. 
      symmetry; eapply MemReserve.release_load; eauto.
      unfold blocks_of_env; intros. exploit list_in_map_inv; eauto. 
      intros [[id [b1 ty]] [P Q]]. simpl in P. inv P. 
      exploit me_range; eauto. eapply PTree.elements_complete; eauto. xomega.
    + intros.
      rewrite <- (MemReserve.release_bounds_of_block _ _ _ _ MR).
      symmetry; eapply Mem.bounds_freelist; eauto.
      unfold blocks_of_env.
      rewrite map_map.
      rewrite in_map_iff.
      intros [[i [bb ty]] [A B]]. simpl in *. subst.
      apply PTree.elements_complete in B.
      exploit me_range; eauto. xomega.
      
    + intros.
      rewrite <- (MemReserve.release_bounds_of_block _ _ _ _ MR').
      symmetry; eapply Mem.bounds_freelist; eauto.
      unfold blocks_of_env.
      rewrite map_map.
      rewrite in_map_iff.
      intros [[i [bb ty]] [A B]]. simpl in *. subst.
      apply PTree.elements_complete in B.
      exploit me_trange; eauto. xomega.
    + intros.
      eapply Mem.mi_inj_dynamic; eauto.
    + intros. rewrite <- (MemReserve.release_is_dynamic_block _ _ _ _ MR).
      symmetry; eapply Mem.is_block_dynamic_freelist; eauto.
    + intros. rewrite <- (MemReserve.release_is_dynamic_block _ _ _ _ MR').
      symmetry; eapply Mem.is_block_dynamic_freelist; eauto.
  - rewrite <- (MemReserve.release_nextblock _ _ _ MR). rewrite (Mem.free_list_nextblock _ _ _ FL1).
     inv MENV; xomega.
  - rewrite <- (MemReserve.release_nextblock _ _ _ MR'). rewrite (Mem.free_list_nextblock _ _ _ FL2).
     inv MENV; xomega.
Qed.

(** Matching of global environments *)

Lemma match_cont_globalenv:
  forall f cenv k tk m tm bound tbound,
  match_cont f cenv k tk m tm bound tbound ->
  exists bound, match_globalenvs f bound.
Proof.
  induction 1; auto. exists hi; auto. 
Qed.

Hint Resolve match_cont_globalenv: compat.

Lemma match_cont_find_funct:
  forall sm f cenv k tk m bound tbound vf fd tvf tm
    (IWB: inj_well_behaved f m tm)
    (MC: match_cont f cenv k tk m tm bound tbound)
    (FF: Genv.find_funct m ge vf = Some fd)
    (EI: expr_inj_se f vf tvf)
    (SI: sep_inj m f vf)
    (MINJ: Mem.inject sm expr_inj_se f m tm),
  exists tfd, Genv.find_funct tm tge tvf = Some tfd /\ transf_fundef fd = OK tfd.
Proof.
  intros. exploit match_cont_globalenv; eauto. intros [bound1 MG]. destruct MG.
  generalize (forget_norm _ _ wf_inj_expr_inj_se _ _ _ MINJ IWB _ _ EI SI).
  intro A. unfold Genv.find_funct in FF. repeat destr_in FF.
  subst. inv A.
  assert (f b = Some(b, 0)). 
  { apply DOMAIN. eapply FUNCTIONS; eauto. }
  rewrite FB in H0; inv H0.
  unfold Genv.find_funct. rewrite <- H. 
  rewrite Int.add_zero. rewrite dec_eq_true. apply function_ptr_translated; auto.
Qed.

(** The simulation diagrams *)

Remark is_liftable_var_charact:
  forall cenv a,
  match is_liftable_var cenv a with
  | Some id => exists ty, a = Evar id ty /\ VSet.mem id cenv = true
  | None => match a with Evar id ty => VSet.mem id cenv = false | _ => True end
  end.
Proof.
  intros. destruct a; simpl; auto.
  destruct (VSet.mem i cenv) eqn:?; simpl.
  exists t; auto. 
  auto.
Qed.

Remark simpl_select_switch:
  forall cenv n ls tls,
  simpl_lblstmt cenv ls = OK tls ->
  simpl_lblstmt cenv (select_switch n ls) = OK (select_switch n tls).
Proof.
  intros cenv n.
  assert (DFL:
    forall ls tls, 
    simpl_lblstmt cenv ls = OK tls ->
    simpl_lblstmt cenv (select_switch_default ls) = OK (select_switch_default tls)).
  {
    induction ls; simpl; intros; monadInv H. 
    auto.
    simpl. destruct o. eauto. simpl; rewrite EQ, EQ1. auto.  
  }
  assert (CASE:
    forall ls tls,
    simpl_lblstmt cenv ls = OK tls ->
    match select_switch_case n ls with
    | None => select_switch_case n tls = None
    | Some ls' =>
        exists tls', select_switch_case n tls = Some tls' /\ simpl_lblstmt cenv ls' = OK tls'
    end).
  {
    induction ls; simpl; intros; monadInv H; simpl.
    auto.
    destruct o. 
    destruct (zeq z n).
    econstructor; split; eauto. simpl; rewrite EQ, EQ1; auto.
    apply IHls. auto. 
    apply IHls. auto.
  }
  intros; unfold select_switch. 
  specialize (CASE _ _ H). destruct (select_switch_case n ls) as [ls'|]. 
  destruct CASE as [tls' [P Q]]. rewrite P, Q. auto.
  rewrite CASE. apply DFL; auto.
Qed.

Remark simpl_seq_of_labeled_statement:
  forall cenv ls tls,
  simpl_lblstmt cenv ls = OK tls ->
  simpl_stmt cenv (seq_of_labeled_statement ls) = OK (seq_of_labeled_statement tls).
Proof.
  induction ls; simpl; intros; monadInv H; simpl.
  auto.
  rewrite EQ; simpl. erewrite IHls; eauto. simpl. auto.
Qed.

Remark compat_cenv_select_switch:
  forall cenv n ls,
  compat_cenv (addr_taken_lblstmt ls) cenv ->
  compat_cenv (addr_taken_lblstmt (select_switch n ls)) cenv.
Proof.
  intros cenv n.
  assert (DFL: forall ls,
    compat_cenv (addr_taken_lblstmt ls) cenv ->
    compat_cenv (addr_taken_lblstmt (select_switch_default ls)) cenv).
  {
    induction ls; simpl; intros. 
    eauto with compat.
    destruct o; simpl; eauto with compat.
  }
  assert (CASE: forall ls ls',
    compat_cenv (addr_taken_lblstmt ls) cenv ->
    select_switch_case n ls = Some ls' ->
    compat_cenv (addr_taken_lblstmt ls') cenv).
  {
    induction ls; simpl; intros.
    discriminate.
    destruct o. destruct (zeq z n). inv H0. auto. eauto with compat. 
    eauto with compat.
  }
  intros. specialize (CASE ls). unfold select_switch. 
  destruct (select_switch_case n ls) as [ls'|]; eauto. 
Qed.

Remark addr_taken_seq_of_labeled_statement:
  forall ls, addr_taken_stmt (seq_of_labeled_statement ls) = addr_taken_lblstmt ls.
Proof.
  induction ls; simpl; congruence.
Qed.

Section FIND_LABEL.

Variable f: meminj.
Variable cenv: compilenv.
Variables m tm: mem.
Variables bound tbound: block.
Variable lbl: ident.

Lemma simpl_find_label:
  forall s k ts tk,
  simpl_stmt cenv s = OK ts ->
  match_cont f cenv k tk m tm bound tbound ->
  compat_cenv (addr_taken_stmt s) cenv ->
  match find_label lbl s k with
  | None =>
      find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk', 
         find_label lbl ts tk = Some(ts', tk')
      /\ compat_cenv (addr_taken_stmt s') cenv
      /\ simpl_stmt cenv s' = OK ts'
      /\ match_cont f cenv k' tk' m tm bound tbound 
  end

with simpl_find_label_ls:
  forall ls k tls tk,
  simpl_lblstmt cenv ls = OK tls ->
  match_cont f cenv k tk m tm bound tbound  ->
  compat_cenv (addr_taken_lblstmt ls) cenv ->
  match find_label_ls lbl ls k with
  | None =>
      find_label_ls lbl tls tk = None
  | Some(s', k') =>
      exists ts', exists tk', 
         find_label_ls lbl tls tk = Some(ts', tk')
      /\ compat_cenv (addr_taken_stmt s') cenv
      /\ simpl_stmt cenv s' = OK ts'
      /\ match_cont f cenv k' tk' m tm bound tbound 
  end.

Proof.
  induction s; simpl; intros until tk; intros TS MC COMPAT; auto.
  (* skip *)
  monadInv TS; auto.
  (* var *)
  destruct (is_liftable_var cenv e); monadInv TS; auto. 
  (* set *)
  monadInv TS; auto.
  (* call *)
  monadInv TS; auto.
  (* builtin *)
  monadInv TS; auto.
  (* seq *)
  monadInv TS.
  exploit (IHs1 (Kseq s2 k) x (Kseq x0 tk)); eauto with compat. 
    constructor; eauto with compat.
  destruct (find_label lbl s1 (Kseq s2 k)) as [[s' k']|]. 
  intros [ts' [tk' [P [Q [R S]]]]]. exists ts'; exists tk'. simpl. rewrite P. auto.
  intros E. simpl. rewrite E. eapply IHs2; eauto with compat.
  (* ifthenelse *)
  monadInv TS.
  exploit (IHs1 k x tk); eauto with compat. 
  destruct (find_label lbl s1 k) as [[s' k']|]. 
  intros [ts' [tk' [P [Q [R S]]]]]. exists ts'; exists tk'. simpl. rewrite P. auto. 
  intros E. simpl. rewrite E. eapply IHs2; eauto with compat.
  (* loop *)
  monadInv TS.
  exploit (IHs1 (Kloop1 s1 s2 k) x (Kloop1 x x0 tk)); eauto with compat.
    constructor; eauto with compat.
  destruct (find_label lbl s1 (Kloop1 s1 s2 k)) as [[s' k']|]. 
  intros [ts' [tk' [P [Q [R S]]]]]. exists ts'; exists tk'. simpl; rewrite P. auto. 
  intros E. simpl; rewrite E. eapply IHs2; eauto with compat. econstructor; eauto with compat.
  (* break *)
  monadInv TS; auto.
  (* continue *)
  monadInv TS; auto.
  (* return *)
  monadInv TS; auto.
  (* switch *)
  monadInv TS. simpl.
  eapply simpl_find_label_ls; eauto with compat. constructor; auto.
  (* label *)
  monadInv TS. simpl.
  destruct (ident_eq lbl l).
  exists x; exists tk; auto.
  eapply IHs; eauto.
  (* goto *)
  monadInv TS; auto.

  induction ls; simpl; intros.
  (* nil *)
  monadInv H. auto.
  (* cons *)
  monadInv H.
  exploit (simpl_find_label s (Kseq (seq_of_labeled_statement ls) k)).
    eauto. constructor. eapply simpl_seq_of_labeled_statement; eauto. eauto.
    rewrite addr_taken_seq_of_labeled_statement. eauto with compat.
    eauto with compat. 
  destruct (find_label lbl s (Kseq (seq_of_labeled_statement ls) k)) as [[s' k']|].
  intros [ts' [tk' [P [Q [R S]]]]]. exists ts'; exists tk'; split. simpl; rewrite P. auto. auto.
  intros E. simpl; rewrite E. eapply IHls; eauto with compat.
Qed.

Lemma find_label_store_params:
  forall lbl s k params, find_label lbl (store_params cenv params s) k = find_label lbl s k.
Proof.
  induction params; simpl. auto. 
  destruct a as [id ty]. destruct (VSet.mem id cenv); auto. 
Qed.

End FIND_LABEL.  

Lemma bool_expr_inj:
  forall ei (wf: wf_inj ei) f b b' ty
    (EI: ei f b b'),
    ei f (bool_expr b ty) (bool_expr b' ty).
Proof.
  intros.
  inv wf.
  unfold bool_expr.
  destr; eauto.
Qed.

Lemma sep_inj_bool_expr:
  forall m f v ty
    (SI: sep_inj m f v),
    sep_inj m f (bool_expr v ty).
Proof.
  unfold sep_inj. intros m f v ty SI b SEP DEP.
  eapply SI; eauto.
  red; red; intros.
  specialize (DEP _ COMP _ COMP' SameB em).
  intro EQ; apply DEP.
  unfold bool_expr.
  destr; eauto.
Qed.

Lemma expr_casted_list_params:
  forall params vl,
    expr_list_casted vl (type_of_params params) ->
    list_forall2 expr_casted vl (map snd params).
Proof.
  induction params; simpl; intros.
  inv H. constructor.
  destruct a as [id ty]. inv H. constructor; auto.
Qed.

Lemma expr_list_inject_incr:
  forall ei (wf: wf_inj ei) f a b
    (ELI: list_ei ei f a b)
    f' (INCR: inject_incr f f'),
    list_ei ei f' a b.
Proof.
  induction 2; simpl; intros; eauto; constructor.
  eapply ei_inj_incr; eauto.
  apply IHELI; auto.
Qed.


Lemma filter_permut:
  forall A (f: A -> bool) l l'
    (P: Permutation.Permutation l l'),
    Permutation.Permutation (filter f l) (filter f l').
Proof.
  induction 1; simpl; intros; auto.
  - destr. constructor; auto.
  - repeat destr; try (now constructor). apply Permutation.Permutation_refl.
  - eapply Permutation.Permutation_trans; eauto.
Qed.

Lemma add_lifted_permut:
  forall x Y Y' z z', Permutation.Permutation Y Y' ->
                 Permutation.Permutation z z' ->
                 Permutation.Permutation (add_lifted x Y z) (add_lifted x Y' z').
Proof.
  unfold add_lifted.
  intros.
  apply Permutation.Permutation_app; auto.
  apply filter_permut; auto.
Qed.

Lemma create_undef_temps_permut:
  forall l1 l2 (P: Permutation.Permutation l1 l2) id,
    (create_undef_temps l1)! id = (create_undef_temps l2)! id.
Proof.
  intros.
  apply create_undef_temps_exten.
  apply Alloc.perm_in.
  apply Permutation.Permutation_map; auto.
Qed.


Lemma  add_lifted_set_eq:
  forall s s' (EQ: VSet.Equal s s') l1 l2,
    (add_lifted s l1 l2) = (add_lifted s' l1 l2).
Proof.
  intros.
  induction l1; simpl; auto.
  unfold add_lifted; simpl.
  generalize (VSF.mem_m (eq_refl (fst a)) EQ).
  intro A. unfold VSet.elt, ident in *.  rewrite A.
  destr. f_equal.
  auto.
Qed.

Lemma cenv_for_gen_set_eq:
  forall s l l' (P: Permutation.Permutation l l'),
    VSet.Equal (cenv_for_gen s l) (cenv_for_gen s l').
Proof.
  induction 1; simpl;intros; auto.
  - apply VSP.equal_refl.
  - unfold add_local_variable. destr. des (access_mode t).
    destr.
    apply VSF.add_m; auto.
  - unfold add_local_variable.
    generalize (VSP.equal_refl).
    repeat destr; eauto.
    intros; apply  VSP.add_add.
  - etransitivity;eauto.
Qed.


Lemma sort_remove_lifted:
  forall c l,
    varsort (remove_lifted c l) =
    remove_lifted c (varsort l).
Proof.
  clear. intros. setoid_rewrite varsort_filter; auto.
Qed.

Lemma remove_lifted_eq:
  forall c c' (EQ: VSet.Equal c c') l,
    remove_lifted c l = remove_lifted c' l.
Proof.
  induction l; simpl; intros; auto.
  rewrite (VSF.mem_m); eauto. destr.
Qed.


Lemma perm_add_loc_aux:
  forall t l t0 t1 (EQ: (VSet.Equal t0 t1)),
    VSet.Equal (fold_right (add_local_variable t) t0 l)
               (fold_right (add_local_variable t) t1 l).
Proof.
  induction l; simpl; intros; auto.
  unfold add_local_variable at 1 3.
  repeat destr; eauto.
  apply VSF.add_m; auto.
Qed.

Lemma perm_add_loc:
  forall t l l' (P: Permutation.Permutation l l')
    t0 t1 (EQ: VSet.Equal t0 t1),
    VSet.Equal (fold_right (add_local_variable t) t0 l)
               (fold_right (add_local_variable t) t1 l').
Proof.
  induction 1; simpl; intros; eauto.
  - unfold add_local_variable at 1.
    repeat destr; eauto.
    apply VSF.add_m; auto.
  - unfold add_local_variable at 1 2 4 5.
    generalize (VSP.equal_refl).
    generalize (perm_add_loc_aux t l t0 t1 EQ).
    repeat destr; intros; eauto;
    try (apply VSF.add_m ;auto; fail).
    intros; erewrite  VSP.add_add.
    apply VSF.add_m ;auto.
    apply VSF.add_m ;auto.
  - etransitivity;eauto.
    etransitivity; eauto.
    apply perm_add_loc_aux; auto. symmetry; auto.
Qed.



Lemma cenv_for_cenv_for_gen_eq:
  forall f,
    VSet.Equal (cenv_for f)
               (cenv_for_gen (addr_taken_stmt (fn_body f))
                             (varsort (fn_params f ++ fn_vars f))).
Proof.
  unfold cenv_for, cenv_for_gen; simpl; intros.
  apply perm_add_loc.
  apply varsort_permut.
  apply VSP.equal_refl.
Qed.

Lemma remove_lifted_app:
  forall f l1 l2,
    remove_lifted f (l1 ++ l2) = remove_lifted f l1 ++ remove_lifted f l2.
Proof.
  induction l1; simpl; intros; eauto.
  destr.
Qed.


Lemma store_params_ext:
  forall cenv cenv' l s (EQ: VSet.Equal cenv cenv'),
    store_params cenv l s = store_params cenv' l s.
Proof.
  induction l; simpl; intros; auto.
  destr.
  rewrite (VSF.mem_m); eauto. destr; eauto.
  rewrite IHl; auto.
Qed.

Lemma match_envs_cenv_ext:
  forall  cenv cenv' f  e le m tm lo hi te tle tlo thi
     (EQ: VSet.Equal cenv cenv')
     (ME: match_envs f cenv e le m tm lo hi te tle tlo thi),
    match_envs f cenv' e le m tm lo hi te tle tlo thi.
Proof.
  intros.
  inv ME; constructor; auto.
  - intros. destruct (me_vars0 id);
      rewrite (VSF.mem_m) in *; eauto.
    eapply match_var_lifted; eauto.
    eapply match_var_not_lifted; eauto.
    eapply match_var_not_local; eauto.
  - intros; rewrite <- (VSF.mem_m) in *; eauto.
Qed.

Lemma av_bounds:
  forall e m vars e' m1
    (AV: alloc_variables e m vars e' m1)
    b (PLT: Plt b (Mem.nextblock m)),
    Mem.bounds_of_block m b = Mem.bounds_of_block m1 b.
Proof.
  induction 1; simpl; intros; eauto.
  erewrite (Mem.bounds_of_block_alloc_other _ _ _ _ _ _ H); eauto.
  apply IHAV.
  genAlloc. xomega.
  genAlloc. intro; subst; xomega.
Qed.

Lemma bp_bounds:
  forall m e v vl m1
    (BP: bind_parameters e m v vl m1) b,
    Mem.bounds_of_block m b = Mem.bounds_of_block m1 b.
Proof.
  induction 1; simpl; intros; eauto.
  erewrite assign_loc_bounds; eauto.
Qed.

Lemma free_blocks_alloc_bytes':
  forall k m tm,
    free_blocks m tm k ->
    exists tm',
      MemReserve.reserve_boxes tm k = Some tm' /\
      free_blocks m tm' 0.
Proof.
  intros. exploit free_blocks_reserve_boxes; eauto.
  rewrite minus_diag. auto.
Qed.


Lemma fl_rew:
  forall vars z,
    (fold_left
       (fun (acc : nat) (it : ident * type) => acc + Mem.box_span (sizeof (snd it)))
       vars z =
     fold_left
       (fun (acc : nat) (it : ident * type) => acc + Mem.box_span (sizeof (snd it)))
       vars 0 + z)%nat.
Proof.
  induction vars; simpl; intros; eauto.
  rewrite ! (IHvars (Peano.plus _ _)). rewrite <- ! plus_assoc. f_equal. simpl.
  rewrite plus_comm. rewrite plus_0_l. reflexivity. 
Qed.

Lemma alloc_variables_size_mem:
  forall vars m e m' e'
    (AV: alloc_variables e m vars e' m'),
    (Mem.nb_boxes_used_m m' = Mem.nb_boxes_used_m m + (fold_left (fun acc it => acc + Mem.box_span (sizeof (snd it))) vars 0))%nat.
Proof.
  induction vars; simpl; intros.
  - inv AV. rewrite plus_0_r. reflexivity. 
  - inv AV.
    specialize (IHvars _ _ _ _ H6).
    rewrite IHvars.
    rewrite (Mem.nb_boxes_alloc _ _ _ _ _ _ H3).
    simpl.
    rewrite (fl_rew _ (Peano.plus _ _)). rewrite Zmax_r. rewrite plus_0_l.
    rewrite <- ! plus_assoc. f_equal. apply plus_comm. apply Z.ge_le, (sizeof_pos ty).
Qed.

Lemma blocks_of_env_norepet:
  forall e
    (Einj: forall i1 b1 t1 i2 b2 t2
             (ei1: e ! i1 = Some (b1, t1))
             (ei2: e ! i2 = Some (b2, t2))
             (idiff: i1 <> i2), b1 <> b2),
    list_norepet (map fst (map fst (blocks_of_env e))).
Proof.
  intros.
  unfold blocks_of_env, block_of_binding.
  rewrite ! map_map.
  generalize (PTree.elements_complete e) (* (PTree.elements_correct e) *)
             (PTree.elements_keys_norepet e).
  intros Comp (* Corr  *)NR; revert Comp (* Corr *) NR Einj.
  generalize (PTree.elements e).
  clear.
  induction l; simpl; intros; eauto.
  constructor.
  - clear IHl.
    des a . des p0.
    rewrite  in_map_iff.
    intros [x [EQ IN]]. des x. des p0.
    generalize (Comp _ _ (or_introl eq_refl)).
    generalize (Comp _ _ (or_intror IN)).
    intros EI1 EI2.
    assert (i = p).
    destruct (peq i p); subst; auto.
    specialize (Einj _ _ _ _ _ _ EI1 EI2 n). destr.
    subst.
    inv NR.
    apply H1; apply in_map_iff. exists (p,(b,t0)); simpl; auto.
  - inv NR.
    eapply IHl; intros; eauto.
Qed.

Lemma match_alloc_variables:
  forall cenv e m vars e' m'
    (AV:alloc_variables e m vars e' m')
    j tm te n
    (FrB: free_blocks m tm n)
    (CB: cenv_bound cenv vars)
    (LNR: list_norepet (var_names vars))
    (MINJ: Mem.inject true expr_inj_se j m tm)
    (IWB: inj_well_behaved j m tm)
    (EVB: forall i b t, e ! i = Some (b,t) -> Mem.valid_block m b)
    (TE: forall i b t, te ! i = Some (b,t) -> ~ In i (var_names vars))
    (INJenv: forall b' i t, te ! i = Some (b',t) -> exists b delta, e ! i = Some (b,t) /\ j b = Some (b',delta)),
  exists j' te' tm',
    alloc_variables te tm (remove_lifted cenv vars) te' tm'
    /\ free_blocks m' tm' (n + length (filter (fun it => VSet.mem (fst it) cenv) vars))
    /\ Mem.inject true expr_inj_se j' m' tm'
    /\ inject_incr j j'
    /\ (forall b, Mem.valid_block m b -> j' b = j b)
    /\ (forall b b' delta, j' b = Some(b', delta) -> Mem.valid_block tm b' -> j' b = j b)
    /\ (forall b b' delta, j' b = Some(b', delta) -> ~Mem.valid_block tm b' -> 
                     exists id, exists ty, e'!id = Some(b, ty) /\ te'!id = Some(b', ty) /\ delta = 0)
    /\ (forall id ty, In (id, ty) vars ->
                exists b, 
                  e'!id = Some(b, ty)
                  /\ if VSet.mem id cenv
                    then te'!id = te!id /\ j' b = None
                    else exists tb, te'!id = Some(tb, ty) /\ j' b = Some(tb, 0))
    /\ (forall id, ~In id (var_names vars) -> e'!id = e!id /\ te'!id = te!id)
    /\ (forall id b ty, ~In id (var_names vars) -> e'!id = Some (b,ty) -> j' b = j b)
    /\ inj_well_behaved j' m' tm'
    (* /\ (exists l1, l' = l1 ++ l /\ length l1 = length (filter (fun it => VSet.mem (fst it) cenv) vars)) *)
    (* /\ (length l' = length l + length (filter (fun it => VSet.mem (fst it) cenv) vars))%nat *)
    (* /\ (Mem.one2oneinject j -> Mem.one2oneinject j') *)
    (* /\ (inj_injective j -> inj_injective j') *)
    (* /\ (forall b b' z, j' b = Some (b',z) -> g' b = Some b') *)
    /\ (forall b' i t, te' ! i = Some (b',t) -> exists b delta, e' ! i = Some (b,t) /\ j' b = Some (b', delta))
    (* /\ (forall b, In b l' -> In b l \/ In b (map fst (map fst (blocks_of_env e')))) *)
    (* /\ (forall b b', g b = Some b' -> g' b = Some b') *)
    (* /\ (forall b b', g b = None -> g' b = Some b' -> In b (map fst (map fst (blocks_of_env e')))) *)
.
Proof.
  induction 1; intros.
  - (* base case *)
    exists j, te, tm.  simpl.
    repSplit; auto.
    + constructor.
    + rewrite plus_0_r; auto.
    + intros. elim H0. eapply Mem.mi_mappedblocks; eauto.
    + tauto.
  - (* inductive case *)
    simpl in AV. inv LNR. simpl.
    destruct (VSet.mem id cenv) eqn:?. simpl.
    + (* variable is lifted out of memory *)
      exploit Mem.alloc_left_unmapped_inject; eauto.
      intros [j' [A [B [C D]]]].
      exploit IHAV.
      * instantiate (1:=S n). instantiate (1:=tm).
        red; intros. inv CB.
        rewrite (Mem.nb_boxes_alloc _ _ _ _ _ _ H ).
        red in FrB; revert FrB. destruct H6; try congruence. clear - H0.
        rewrite Zmax_r by (lia).
        rewrite box_span_small.
        Transparent Z.of_nat. lia.
        split. lia. etransitivity. apply H0.
        change 8 with (two_power_nat 3).
        rewrite ! two_power_nat_two_p.
        apply two_p_monotone. generalize MA_bound; lia.
      * inv CB; auto.
      * auto.
      * eauto.
      * {
          inv IWB; constructor; simpl; intros; eauto.
          - red; intros.
            des (peq b b1). rewrite D in H0; eauto.
          - red; intros.
            des (peq b b1). inv CB.
            rewrite <- Mem.size_block_snd. erewrite Mem.bounds_of_block_alloc. 2: eauto.
            simpl. 
            rewrite Heqb in H7. des H7.
            rewrite Z.max_r by lia. split ; try lia.
            erewrite Mem.alloc_mask. apply Genv.aos_3. eauto.
            rewrite <- Mem.size_block_snd. 
            erewrite <- Mem.bounds_of_block_alloc_other.
            2: eauto.
            rewrite Mem.size_block_snd.
            erewrite <- Mem.mask_alloc_other.
            apply iwb_wb. rewrite <- D. auto. auto. eauto.
            apply not_eq_sym; auto.
            apply not_eq_sym; auto.
          - intros.
            rewrite <- (Mem.size_block_snd m1 b).
            erewrite <- Mem.bounds_of_block_alloc_other.
            rewrite Mem.size_block_snd.
            eapply iwb_bounds; auto. rewrite D in H0. eauto. intro; subst b1. destr. eauto.
            destr.
          - intros.
            erewrite <- Mem.mask_alloc_other.
            eapply iwb_mask; eauto. rewrite D in H0. eauto. destr. eauto. destr.
          - edestruct iwb_no_oota as (b & delta & FB). eauto.
            eapply B in FB.
            eauto.
          - rewrite D in H0 by destr.
            rewrite D in H1 by destr. eauto.
        }
      * intros i b t EQ.
        rewrite PTree.gsspec in EQ; destr_in EQ.
        inv EQ. eapply Mem.valid_new_block; eauto.
        eapply EVB in EQ.
        eapply Mem.valid_block_alloc; eauto.
      * instantiate (1:=te). intros. apply TE in H0. destr. 
      * intros. rewrite PTree.gsspec. destr.
        subst. apply TE in H0. destr.
        apply INJenv in H0. dex; destr_and. rewrite H0.
        eexists; eexists; split; eauto.
      * 
        intros [j'' [te' [tm' [J [JJ [K [L [M [N [Q [O [P [P' [R S]]]]]]]]]]]]]].
        exists j'', te', tm'.
        {
          repSplit; auto.
          - rewrite <- plus_n_Sm.
            rewrite plus_Sn_m in JJ. auto.
          - eapply inject_incr_trans; eauto. 
          - intros. transitivity (j' b). apply M. eapply Mem.valid_block_alloc; eauto. 
            apply D. apply Mem.valid_not_valid_diff with m; auto. eapply Mem.fresh_block_alloc; eauto. 
          - intros. transitivity (j' b). eapply N; eauto.
            destruct (eq_block b b1); auto. subst. 
            assert (j'' b1 = j' b1). apply M. eapply Mem.valid_new_block; eauto. 
            congruence.
          - intros. destruct (ident_eq id0 id).
            {
              (* same var *)
              subst id0.
              assert (ty0 = ty).
              destruct H0. congruence.
              elim H2.
              unfold var_names.  change id with (fst (id, ty0)).
              apply in_map_iff. eexists; split; eauto.
              subst ty0. exploit (P id); eauto. intros [X Y'].
              exists b1. rewrite Heqb. rewrite X,Y'. rewrite PTree.gss.
              repSplit; auto.
              rewrite M. auto. eapply Mem.valid_new_block; eauto.
            }
            {
              (* other vars *)
              eapply O; eauto. destruct H0. congruence. auto.
            }
          - intros. exploit (P id0). tauto. intros [X Y'].
            rewrite X, Y'. split; auto.
            apply PTree.gso. intuition.
          - intros.
            apply Classical_Prop.not_or_and in  H0.
            des H0.
            rewrite (P' _ _ _ n1 H1). apply D.
            exploit P. apply n1. rewrite PTree.gso.
            intros (EQ & _). rewrite EQ in H1.
            apply EVB in H1.
            intro; subst.
            exploit Mem.fresh_block_alloc. eauto. auto. auto. auto.
        }              

    + (* variable is not lifted out of memory *)
      exploit (Mem.alloc_parallel_inject true _ wf_inj_expr_inj_se j m tm 0 (sizeof ty) m1 b1); eauto.
      apply Zge_le; apply sizeof_pos. apply sizeof_pos.
      intros [j1 [tm1 [tb1 [A [B [C [D E]]]]]]].
      {
        exploit IHAV. 
        - instantiate (1:=n). instantiate (1:=tm1).
          red; intros. 
          rewrite (Mem.nb_boxes_alloc _ _ _ _ _ _ H ).
          rewrite (Mem.nb_boxes_alloc _ _ _ _ _ _ A ).
          red in FrB; revert FrB. lia. 
        - now inv CB.
        - auto.
        - eauto.
        - clear IHAV.


          apply iwb_ext with (j:= fun b => if peq b b1 then Some (tb1,0) else j b).

          inv IWB; constructor; destr.
          + red in iwb_o2o |- *. intros. destr_in H0. eauto.
          + red in iwb_wb |- *. intros. destr_in H0; eauto.
            inv CB.
            rewrite <- Mem.size_block_snd. 
            erewrite <- Mem.bounds_of_block_alloc_other.
            2: eauto.
            rewrite Mem.size_block_snd.
            erewrite <- Mem.mask_alloc_other.
            apply iwb_wb. auto. eauto. 
            apply not_eq_sym; auto.
            apply not_eq_sym; auto.
          + intros. destr_in H0. inv H0.
            rewrite <- ! (Mem.size_block_snd).
            rewrite (Mem.bounds_of_block_alloc _ _ _ _ _ _ A).
            rewrite (Mem.bounds_of_block_alloc _ _ _ _ _ _ H). auto.
            rewrite <- ! (Mem.size_block_snd).
            erewrite <- (Mem.bounds_of_block_alloc_other _ _ _ _ _ _ H).
            erewrite <- (Mem.bounds_of_block_alloc_other _ _ _ _ _ _ A).
            rewrite ! Mem.size_block_snd. eauto.
            eapply Mem.valid_block_inject_2 in H0. 2: eauto.
            exploit Mem.alloc_result. apply A. intro; subst. intro; subst.
            red in H0; xomega. auto.
          + intros. destr_in H0. inv H0.
            rewrite (Mem.alloc_mask _ _ _ _ _ _ A).
            rewrite (Mem.alloc_mask _ _ _ _ _ _ H). auto.
            rewrite <- (Mem.mask_alloc_other _ _ _ _ _ _ A).
            rewrite <- (Mem.mask_alloc_other _ _ _ _ _ _ H). eauto.
            auto.
            eapply Mem.valid_block_inject_2 in H0. 2: eauto.
            exploit Mem.alloc_result. apply A. intro; subst. intro; subst.
            red in H0; xomega.
          + intros. destr; eauto.
            destruct (Mem.valid_block_alloc_inv _ _ _ _ _ _ A b'). auto.
            * subst. eexists b1, 0. rewrite peq_true. auto.
            * exploit iwb_no_oota. eauto. intros; dex.
              exists b, delta. rewrite peq_false. auto.
              intro; subst. exploit Mem.fresh_block_alloc. apply H.
              eapply Mem.valid_block_inject_1; eauto. auto.
          + intros. destr_in H0; destr_in H1.
            inv H0.
            exploit Mem.fresh_block_alloc. apply A. eapply Mem.valid_block_inject_2. apply H1. eauto. destr.
            inv H1.
            exploit Mem.fresh_block_alloc. apply A. eapply Mem.valid_block_inject_2. apply H0. eauto. destr.
            exploit iwb_inj. apply H0. apply H1. auto.
          + intros; destr. symmetry; apply E. auto.
            
        - intros i b t EQ. rewrite PTree.gsspec in EQ; destr_in EQ.
          inv EQ. eapply Mem.valid_new_block; eauto.
          apply EVB in EQ. eapply Mem.valid_block_alloc; eauto.
        - instantiate (1:= PTree.set id (tb1, ty) te).
          intros i b t; rewrite PTree.gsspec.
          destr; eauto.
          intro X; inv X. auto.
          intro TEI. apply TE in TEI. destr.
        - intros b' i t EQ. rewrite PTree.gsspec in EQ; destr_in EQ.
          inv EQ. rewrite PTree.gss. eexists; eexists; split; eauto.
          rewrite PTree.gso; auto. apply INJenv in EQ. destruct EQ as [b [ delta [EQ GB]]].
          exists b, delta ; split; auto.
        - intros [j' [te' [tm' [J [JJ [K [L [M [N [Q [O [P [P' [R S]]]]]]]]]]]]]].
          exists j', te', tm'.
          repSplit; auto.
          + simpl. econstructor; eauto.
          + eapply inject_incr_trans; eauto. 
          + intros. transitivity (j1 b). apply M. eapply Mem.valid_block_alloc; eauto. 
            apply E. apply Mem.valid_not_valid_diff with m; auto. eapply Mem.fresh_block_alloc; eauto.
          + intros. transitivity (j1 b). eapply N; eauto. eapply Mem.valid_block_alloc; eauto. 
            destruct (eq_block b b1); auto. subst. 
            assert (j' b1 = j1 b1). apply M. eapply Mem.valid_new_block; eauto.
            rewrite H4 in H0. rewrite D in H0. inv H0. eelim Mem.fresh_block_alloc; eauto.
          + intros. destruct (eq_block b' tb1). 
            {
              subst b'. rewrite (N _ _ _ H0) in H0.
              - destruct (eq_block b b1).
                + subst b. rewrite D in H0; inv H0.  
                  exploit (P id); auto. intros [X Y].
                  exists id; exists ty. rewrite X, Y.
                  rewrite  ! PTree.gss. repSplit; auto. 
                + 
                  rewrite E in H0; auto. elim H1. eapply Mem.mi_mappedblocks; eauto.
              - 
                eapply Mem.valid_new_block; eauto.
            }
            eapply Q; eauto. unfold Mem.valid_block in *.
            exploit Mem.nextblock_alloc. eexact A. exploit Mem.alloc_result. eexact A.
            unfold block; xomega. 
          + intros. destruct (ident_eq id0 id).
            * (* same var *)
              subst id0.
              assert (ty0 = ty).
              destruct H0. congruence. elim H2. unfold var_names.
              apply in_map_iff; econstructor; split; eauto. auto.
              subst ty0. 
              exploit P; eauto. intros [X Y]. rewrite Heqb, X, Y.
              rewrite ! PTree.gss.
              exists b1. split; auto. 
              exists tb1; split; auto.
            * (* other vars *)
              exploit (O id0 ty0). destruct H0. congruence. auto. 
              rewrite ! PTree.gso; auto. 
          +  intros. exploit (P id0). tauto. intros [X Y]. rewrite X, Y.
             split; apply PTree.gso; intuition.
          + intros.
            apply Classical_Prop.not_or_and in  H0. des H0.
            rewrite (P' _ _ _ n1 H1).
            apply E.
            destruct (P _ n1) as [EI TEI].
            rewrite PTree.gso in EI, TEI by auto.
            rewrite H1 in EI. symmetry in EI. apply EVB in EI.
            contradict EI.
            subst. eapply Mem.fresh_block_alloc; eauto.
      }
Qed.


Theorem match_envs_alloc_variables:
  forall cenv m vars e m' temps j tm
    (CB: cenv_bound cenv vars)
    (IWB: inj_well_behaved j m tm)
    n (FrB: free_blocks m tm n)
    (AV: alloc_variables empty_env m vars e m')
    nbytes m''
    needed (ORD: (nbytes <= needed)%nat)
    (ORD': (needed <= nbytes +
                     length
                       (filter (fun it : VSet.elt * type => VSet.mem (fst it) cenv)
                               vars))%nat)
    (AB: MemReserve.reserve_boxes m' nbytes = Some m'')
    (LNR: list_norepet (var_names vars))
    (MINJ: Mem.inject true expr_inj_se j m tm)
    (AM: forall id ty, In (id, ty) vars -> VSet.mem id cenv = true ->
                  exists chunk, access_mode ty = By_value chunk)
    (VARIN: forall id, VSet.mem id cenv = true -> In id (var_names vars)),
  exists j' te tm' tm'',
    alloc_variables empty_env tm (remove_lifted cenv vars) te tm'
    /\ MemReserve.reserve_boxes tm' needed = Some tm''
    /\ free_blocks m'' tm'' n
    /\ match_envs j' cenv e (create_undef_temps temps) m'' tm''
                 (Mem.nextblock m) (Mem.nextblock m'')
                 te (create_undef_temps (add_lifted cenv vars temps))
                 (Mem.nextblock tm) (Mem.nextblock tm'')
    /\ Mem.inject true expr_inj_se j' m'' tm''
    /\ inject_incr j j'
    /\ (forall b, Mem.valid_block m b -> j' b = j b)
    /\ (forall b b' delta, j' b = Some(b', delta) -> Mem.valid_block tm b' -> j' b = j b)
    /\ inj_well_behaved j' m'' tm''.
Proof.
  intros.  
  exploit (match_alloc_variables cenv); eauto.
  intros i b t; rewrite PTree.gempty; destr.
  instantiate (1 := empty_env).
  intros i b t; rewrite PTree.gempty; destr.
  intros b' i t; rewrite PTree.gempty; destr.
  intros [j' [te [tm' [A [FrB' [B [C [D [E [K [F [G [H [I J]]]]]]]]]]]]]].
  generalize (free_blocks_alloc_bytes_1 _ _ _ _ _ FrB' AB). intro FrB''. 
  destruct (free_blocks_reserve_boxes
              _
              needed
              _ _ FrB'') as [tm'' [AB' FrB''']]. lia.
  exists j', te, tm', tm''.
  assert (E_VB:
            forall id b ty (EID: e!id = Some (b,ty)),
              Mem.valid_block m' b).
  {
    intros.
    destruct (in_dec peq id (var_names vars)); auto.
    - generalize (alloc_variables_range id b ty empty_env _ _ _ _ AV EID).
      rewrite PTree.gempty. destr.
    - exploit G; eauto.
      rewrite PTree.gempty. destr.
  }
  assert (TE_VB:
            forall id b ty (EID: te!id = Some (b,ty)),
              Mem.valid_block tm' b).
  {
    intros.
    destruct (in_dec peq id (var_names vars)); auto.
    - generalize (alloc_variables_range id b ty empty_env _ _ _ _ A EID).
      rewrite PTree.gempty. destr.
    - exploit G; eauto.
      rewrite PTree.gempty. destr.
  }
  replace (needed) with (nbytes + (needed - nbytes))%nat in AB' by lia.
  assert (MENV':
            match_envs j' cenv e (create_undef_temps temps) m'' tm''
                       (Mem.nextblock m) (Mem.nextblock m'') te
                       (create_undef_temps (add_lifted cenv vars temps)) 
                       (Mem.nextblock tm) (Mem.nextblock tm'')
         ).
  {
    constructor; intros; try easy.
    {
      destruct (In_dec ident_eq id (var_names vars)).
      - unfold var_names in i. exploit list_in_map_inv; eauto.
        intros [[id' ty] [EQ IN]]; simpl in EQ; subst id'.
        exploit F; eauto. intros [b [P R]]. 
        destruct (VSet.mem id cenv) eqn:?.
        + (* local var, lifted *)
          edestruct R as [U V]. exploit AM; eauto. intros [chunk X].
          generalize (alloc_variables_initial_value _ _ _ _ _ AV).
          intro L; trim L.
          red. intros id0 b0 ty0 chunk0 EE AMc.
          rewrite PTree.gempty in EE. congruence.
          exploit L; eauto. intros [v [M N]].
          eapply match_var_lifted with (v:=v) (tv:= Eval Vundef) ; eauto.
          rewrite U; apply PTree.gempty.
          rewrite <- M. eapply alloc_bytes_load; eauto.
          eapply load_valid_block; eauto.
          apply create_undef_temps_charact with ty.
          unfold add_lifted; apply in_or_app; left; rewrite filter_In; auto.
          eapply expr_inj_se_l. apply expr_inj_se_vundef. symmetry; auto.
        +  (* local var, not lifted *)
          destruct R as [tb [U V]].
          eapply match_var_not_lifted; eauto. 
      -  (* non-local var *)
        exploit G; eauto. unfold empty_env. rewrite PTree.gempty. intros [U V].
        eapply match_var_not_local; eauto. 
        destruct (VSet.mem id cenv) eqn:?; auto.
        elim n0; eauto.
    }
    {
      (* temps *)
      exploit create_undef_temps_inv; eauto. intros [P Q]. subst v.
      unfold var_names in Q. exploit list_in_map_inv; eauto. 
      intros [[id1 ty] [EQ IN]]; simpl in EQ; subst id1. 
      split; auto. exists (Eval Vundef); split; auto. 
      apply create_undef_temps_charact with ty. unfold add_lifted. 
      apply in_or_app; auto.
      apply expr_inj_se_vundef.
    }
    {
      destruct (in_dec peq id (var_names vars)).
      - erewrite <- (MemReserve.reserve_bounds_of_block _ _ _ _ AB).
        eapply alloc_variables_bounds; eauto. intro; rewrite PTree.gempty; destr.
      - exploit G; eauto.
        rewrite PTree.gempty. destr.
    }
    {
      destruct (in_dec peq id (var_names vars)); [|exploit G; eauto; rewrite PTree.gempty; destr].
      exploit (alloc_variables_bounds empty_env m); eauto. intro; rewrite PTree.gempty; destr.
      unfold var_names in i. apply in_map_iff in i.
      dex; destr; subst. des x.
      destruct (F _ _ (proj2 i)) as [bb [EI VST]].
      rewrite (proj1 i) in EI; inv EI.
      revert VST; destr.
      intros [tb [TEI J'BB]] Bnds. 
      des i.
      rewrite H0 in H3; inv H3.
      exploit (alloc_variables_bounds empty_env tm); eauto.
      intro; rewrite PTree.gempty; destr.
      eapply in_map_iff. exists (id,t); split; auto.
      unfold remove_lifted. rewrite filter_In. simpl; rewrite Heqb0. split; auto.
      rewrite <- (MemReserve.reserve_bounds_of_block _ _ _ _ AB).
      rewrite <- (MemReserve.reserve_bounds_of_block _ _ _ _ AB').
      congruence.
    }
    {
      (* injective *)
      eapply alloc_variables_injective. eexact AV. 
      rewrite PTree.gempty. congruence.
      intros id b ty EE. rewrite PTree.gempty in EE. congruence.
      eauto. eauto. auto.
    }
    {
      (* range *)
      exploit alloc_variables_range. eexact AV. eauto. 
      rewrite PTree.gempty. intuition try congruence.
      erewrite <- MemReserve.reserve_nextblock. apply H3. eauto.
    }
    {
      (* trange *)
      exploit alloc_variables_range. eexact A. eauto. 
      rewrite PTree.gempty. intuition try congruence.
      erewrite <- MemReserve.reserve_nextblock. apply H3. eauto.
    }
    {
      (* mapped *)
      destruct (In_dec ident_eq id (var_names vars)).
      - unfold var_names in i. exploit list_in_map_inv; eauto. 
        intros [[id' ty'] [EQ IN]]; simpl in EQ; subst id'.
        exploit F; eauto. intros [b [P Q]].
        destruct (VSet.mem id cenv). 
        + rewrite PTree.gempty in Q. destruct Q; congruence.
        + destruct Q as [tb [U V]]. exists b; split; congruence.
      - exploit G; eauto. rewrite PTree.gempty. intuition congruence.
    }
    {
      (* flat *)
      exploit alloc_variables_range. eexact A. eauto. 
      rewrite PTree.gempty. intros [P|P]. congruence. 
      exploit K; eauto. unfold Mem.valid_block. xomega. 
      intros [id0 [ty0 [U [V W]]]]. split; auto. 
      destruct (ident_eq id id0). congruence.
      assert (b' <> b').
      {
        eapply alloc_variables_injective with (e' := te) (id1 := id) (id2 := id0); eauto.
        rewrite PTree.gempty; congruence. 
        intros until ty1; rewrite PTree.gempty; congruence.
      }
      congruence.
    }
    {
      eapply Ple_trans. eapply alloc_variables_nextblock; eauto.
      rewrite (MemReserve.reserve_nextblock _ _ _ AB). reflexivity.
    }
    {
      eapply Ple_trans. eapply alloc_variables_nextblock; eauto.
      rewrite (MemReserve.reserve_nextblock _ _ _ AB'). reflexivity. 
    }
      Lemma alloc_variables_in:
        forall l e1 e2 m1 m2
          (AV: alloc_variables e1 m1 l e2 m2),
        forall i p,
          e2 ! i = Some p ->
          e1 ! i = Some p \/ In i (map fst l).
      Proof.
        induction 1; simpl; intros; eauto.
        specialize (IHAV _ _ H0).
        rewrite PTree.gsspec in IHAV. destr_in IHAV.
      Qed.


    Lemma alloc_variables_not_dynamic:
      forall v e m e' m'
        (AV: alloc_variables e m v e' m')
        (INIT: forall i b t,
            e ! i = Some (b,t) ->
            ~ Mem.is_dynamic_block m b),
      forall i b t,
        e' ! i = Some (b,t) ->
        ~ Mem.is_dynamic_block m' b.
    Proof.
      induction 1; simpl; intros; eauto.
      trim IHAV.
      - intros. rewrite PTree.gsspec in H1. destr_in H1. inv H1.
        erewrite <- Mem.is_block_dynamic_alloc. 2: eauto.
        unfold Mem.is_dynamic_block. rewrite Mem.blocktype_valid. congruence.
        eapply Mem.fresh_block_alloc; eauto.
        apply INIT in H1.
        erewrite <- Mem.is_block_dynamic_alloc. 2: eauto. auto.
      - eauto.
    Qed.
    Lemma alloc_variables_not_dynamic_forall:
      forall v m e m'
        (AV: alloc_variables empty_env m v e m'),
        Forall (fun b => ~ Mem.is_dynamic_block m' b) (map fst (map fst (blocks_of_env e))).
    Proof.
      intros.
      trim (alloc_variables_not_dynamic _ _ _ _ _ AV).
      intros i b t; rewrite PTree.gempty. destr.
      intros.
      apply Forall_forall.
      intros.
      rewrite map_map, in_map_iff in H0.
      destruct H0 as [[[b lo] hi] [EQ IN]]. simpl in *. subst.
      apply in_blocks_of_env in IN.
      destruct IN as [i [t [SZ [LO0 TEI]]]]. simpl in *; subst.
      apply H in TEI. auto.
    Qed.
    eapply alloc_variables_not_dynamic_forall in AV; eauto.
    revert AV. apply Forall_impl.
    intro a. rewrite (MemReserve.reserve_is_dynamic_block _ _ _ _ AB). auto.
    eapply alloc_variables_not_dynamic_forall in A; eauto.
    revert A. apply Forall_impl.
    intro a. rewrite (MemReserve.reserve_is_dynamic_block _ _ _ _ AB'). auto.
  }
  repSplit; auto.
  - replace (needed) with (nbytes + (needed - nbytes))%nat by lia. auto.
  - eapply free_blocks_more.
    2: eauto. lia.
  - inv B. constructor; simpl; intros; eauto.
    + 
      {
        inv mi_inj; constructor; simpl; intros; eauto.
        -
         erewrite <- reserve_perm in H1; eauto.
          erewrite <- reserve_perm; eauto.
        - red in H1 |- *.
          erewrite <- MemReserve.reserve_bounds_of_block in H1 |- * ; eauto. eapply mi_bounds; eauto.
        - rewrite <- (MemReserve.reserve_mask _ _ _ _ AB), <- (MemReserve.reserve_mask _ _ _ _ AB'). eauto.
        - rewrite <- reserve_perm in H1; eauto.

         rewrite <- (reserve_mem_contents _ _ _ AB), <- (reserve_mem_contents _ _ _ AB'). eauto.
        - 
         eapply free_blocks_0.
          eapply free_blocks_more. 2: eauto. lia.
      }
    + eapply mi_freeblocks; eauto.
      unfold Mem.valid_block in H |-*.
      rewrite (MemReserve.reserve_nextblock _ _ _ AB). auto.
    + eapply mi_mappedblocks in H0.
      unfold Mem.valid_block in H0 |-*.
      rewrite <- (MemReserve.reserve_nextblock _ _ _ AB'). auto.
    + red. intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 DIFF INJ1 INJ2 IB1 IB2.
      red in IB1, IB2.
      rewrite <- (MemReserve.reserve_bounds_of_block _ _ _ _ AB) in IB1.
      rewrite <- (MemReserve.reserve_bounds_of_block _ _ _ _ AB) in IB2. eauto.
    + specialize (mi_inj_dynamic _ _ _ H0). des mi_inj_dynamic. des a.
      rewrite <- (MemReserve.reserve_is_dynamic_block _ _ _ _ AB').
      rewrite <- (MemReserve.reserve_is_dynamic_block _ _ _ _ AB).
      repSplit; auto.
      intros. trim a0; auto. split; destr.
      specialize (mi_mappedblocks _ _ _ H0).
      rewrite <- (MemReserve.reserve_bounds_of_block _ _ _ _ AB').
      rewrite <- (MemReserve.reserve_bounds_of_block _ _ _ _ AB).
      destr.
  - eapply iwb_inv. eauto.
    intros. eapply MemReserve.reserve_bounds_of_block; eauto.
    intros. eapply MemReserve.reserve_bounds_of_block; eauto.
    intros. eapply MemReserve.reserve_mask; eauto.
    intros. eapply MemReserve.reserve_mask; eauto.
    intro b'; rewrite (MemReserve.reserve_nextblock _ _ _ AB'). xomega.
Qed.

Lemma release_inj:
  forall sm j m tm
    ei (INJ: Mem.inject sm ei j m tm)
    n n' (LEextra: (n <= n' <= Mem.nb_extra tm)%nat)
    m' (MR: MemReserve.release_boxes m n = Some m'),
  exists tm',
    MemReserve.release_boxes tm n' = Some tm' /\
    Mem.inject sm ei j m' tm'.
Proof.
  intros.
  unfold MemReserve.release_boxes in *. destr_in MR; inv MR.
  destr.
  eexists; split; eauto.
  - inv INJ; constructor; simpl; intros; eauto.
    + inv mi_inj; constructor; simpl; intros; eauto.
      * unfold Mem.perm in *; simpl in *; eauto.
      * unfold Mem.in_bound_m, Mem.bounds_of_block in *; simpl in *; eauto.
      * unfold Mem.nb_boxes_used_m, Mem.mk_block_list, Mem.size_block in *; simpl in *; eauto.
        intuition lia.
    + red; simpl. eapply mi_mappedblocks; eauto.
Qed.

Lemma free_list_preserves:
  forall m m' tm e te (FL: Mem.free_list m (blocks_of_env e) = Some m')
    j
    (IWB: inj_well_behaved j m tm)
    (INJ: Mem.inject true expr_inj_se j m tm)
    cenv le lo hi tle tlo thi 
    (MENV : match_envs j cenv e le m tm lo hi te tle tlo thi)
    fn
    (INPROG: In (Gfun (Internal fn)) (map snd (prog_defs prog)))
    (NbExtra2: (ns2 (fn_id fn) <= Mem.nb_extra tm)%nat)
    (NbExtra1: (ns1 (fn_id fn) <= Mem.nb_extra m)%nat)
    m'' (REL: MemReserve.release_boxes m' (ns1 (fn_id fn)) = Some m''),
  exists tm' tm'',
    Mem.free_list tm (blocks_of_env te) = Some tm' /\
    MemReserve.release_boxes tm' (ns2 (fn_id fn)) = Some tm'' /\
    ( forall     (FreeOrd:  (Mem.nb_boxes_used_m tm - size_env te - ns2 (fn_id fn) <=
                        Mem.nb_boxes_used_m m - size_env e - ns1 (fn_id fn))%nat),
        Mem.inject true expr_inj_se j m'' tm'') /\
    inj_well_behaved j m'' tm''.
Proof.
  intros.
  assert (X: exists tm', Mem.free_list tm (blocks_of_env te) = Some tm').
  {
    apply can_free_list. 
    - (* permissions *)
      intros. unfold blocks_of_env in H.
      exploit list_in_map_inv; eauto. intros [[id [b' ty]] [EQ IN]].
      simpl in EQ; inv EQ.
      exploit me_mapped; eauto. eapply PTree.elements_complete; eauto.
      intros [b [A B]].
      split. 
      + change 0 with (0 + 0). replace (sizeof ty) with (sizeof ty + 0) by omega.
        eapply Mem.range_perm_inject; eauto.
        eapply free_blocks_of_env_perm_2; eauto.
      + exploit me_bounds_same. eauto. apply B. eauto.
        exploit me_bounds. eauto. apply B. congruence.
    - (* no overlap *)
      unfold blocks_of_env; eapply blocks_of_env_no_overlap; eauto.
      intros. eapply free_blocks_of_env_perm_2; eauto.
      apply PTree.elements_keys_norepet.
      intros. apply PTree.elements_complete; auto.
  }
  dex; destr. exists tm'; rewrite X.
  rewrite (Mem.nb_extra_free_list _ _ _ FL) in NbExtra1.
  rewrite (Mem.nb_extra_free_list _ _ _ X) in NbExtra2.
  exploit (release_inj false j m' tm' expr_inj_se).
  2: split. 3: apply NbExtra2. 2: apply ns1_spec; eauto.
  2: eauto.
  inv INJ; constructor; intros; eauto.
  - {
      inv mi_inj; constructor; intros; eauto.
      -
        Lemma release_perm:
          forall m n m' (MR: MemReserve.release_boxes m n = Some m') b o k p,
            Mem.perm m b o k p <-> Mem.perm m' b o k p.
        Proof.
          unfold MemReserve.release_boxes; intros; destr_in MR; inv MR.
          unfold Mem.perm; simpl; tauto.
        Qed.
        eapply Mem.perm_free_list in H0; eauto.
        destruct H0 as (B & Pfree).
        generalize B; intro C.
        eapply mi_perm in B; eauto. 
        eapply Mem.freelist_perm in B; eauto. (* split. intros [x [EQ IN]]. subst. *)
        (* exploit me_extra_tinj; eauto. auto. *)
        intro IN.
        assert (exists i t, te!i = Some (b2,t)).
        {
          clear - IN.
          unfold blocks_of_env, block_of_binding in IN.
          rewrite ! map_map in IN.
          rewrite in_map_iff in IN.
          dex; destr.
          des x. des p. des IN.
          exists i, t. apply PTree.elements_complete; auto.
        }
        destruct H0 as [i [t TE]].
        exploit me_mapped; eauto.
        intro; dex. des H0.
        assert (b1 = b). eapply iwb_inj. eauto. eauto. eauto. subst.
        eapply (Pfree 0 (sizeof t)).
        unfold blocks_of_env, block_of_binding.
        apply in_map_iff. exists (i,(b,t)); split; auto.
        eapply PTree.elements_correct; eauto. 
        exploit me_bounds; eauto. 
        eapply Mem.perm_bounds in C. red in C.
        intro D; rewrite D in C.
        simpl in C; auto.
      - exploit Mem.freelist_in_bound_m. 2: eauto. eauto. intro IB.
        generalize (fun pf => Mem.freelist_in_bound_m' _ _ _ FL (blocks_of_env_norepet _ pf) _ _ H0). intro Pfree.
        red. erewrite Mem.bounds_freelist. 2: eassumption. eapply mi_bounds; eauto.
        + intro IN.
          assert (exists i t, te!i = Some (b2,t)).
          {
            clear - IN.
            unfold blocks_of_env, block_of_binding in IN.
            rewrite ! map_map in IN.
            rewrite in_map_iff in IN.
            dex; destr.
            des x. des p. des IN.
            exists i, t. apply PTree.elements_complete; auto.
          }
          destruct H1 as [i [t TE]].
          exploit me_mapped; eauto.
          intro; dex. des H1.
          assert (b1 = b). eapply iwb_inj. eauto. eauto. eauto. subst.
          eapply Pfree. eapply me_inj. eauto.
          unfold blocks_of_env, block_of_binding.
          rewrite !map_map. apply in_map_iff. exists (i,(b,t)); split; auto.
          eapply PTree.elements_correct; eauto. 
          instantiate (1:=ofs + 1). instantiate (1:=ofs); lia.
      - rewrite (Mem.freelist_mask _ _ _ _ FL).
        rewrite (Mem.freelist_mask _ _ _ _ X). eauto.
      - rewrite <- (Mem.contents_freelist _ _ _ _ FL).
        rewrite <- (Mem.contents_freelist _ _ _ _ X).
        eapply mi_memval; eauto.
        eapply Mem.perm_free_list in H0; eauto. destr.
      - destr. 
    }
  - apply mi_freeblocks. eapply Mem.freelist_valid. eauto. eauto.
  - destruct (Mem.valid_block_dec tm' b'). auto.
    eapply Mem.freelist_valid in n; eauto.
    red in n. exploit mi_mappedblocks; eauto. destr.
  - red. intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 .
    intros. 
    apply (Mem.freelist_in_bound_m _ _ _ FL) in H2.
    apply (Mem.freelist_in_bound_m _ _ _ FL) in H3. eauto.
  -
    specialize (mi_inj_dynamic _ _ _ H). des mi_inj_dynamic. des a.
    rewrite (Mem.is_block_dynamic_freelist _ _ _ _ X).
    rewrite (Mem.is_block_dynamic_freelist _ _ _ _ FL).
    repSplit; eauto. intros. exploit a0. apply H0. intros (A & B). subst. split; auto. 
    trim e0. destr.

  assert (SBeq: forall b, Mem.bounds_of_block m' b =
                     if in_dec peq b (map fst (map fst (blocks_of_env e)))
                     then (0,0)
                     else Mem.bounds_of_block m b).
      {
        intros. erewrite Mem.bounds_of_block_free_list. 4: eauto. rewrite map_map; auto.
        rewrite Forall_forall; intros x I. apply in_blocks_of_env in I.
        destruct I as [i0 [t [SZ [LO EQ]]]].
        des x. des p. subst.  
        eapply me_bounds in EQ; eauto. 

        eapply blocks_of_env_norepet. inv MENV; auto.
      }

      assert (SBeq': forall b', Mem.bounds_of_block tm' b'
                           = if in_dec peq b' (map fst (map fst (blocks_of_env te)))
                             then (0,0)
                             else Mem.bounds_of_block tm b').
      {
        intros; erewrite Mem.bounds_of_block_free_list. 4: eauto. rewrite map_map; auto.

        rewrite Forall_forall; intros x I. apply in_blocks_of_env in I.
        destruct I as [i0 [t [SZ [LO EQ]]]].
        des x. des p. subst.
        eapply me_mapped in EQ; eauto. destruct EQ as [b1 [JB1 EQ]].
        exploit me_bounds_same; eauto. intro a; rewrite <- a.
        eapply me_bounds in EQ; eauto. 
      
        eapply blocks_of_env_norepet.
        intros.
        eapply me_mapped in ei1; eauto.
        eapply me_mapped in ei2; eauto.
        destruct ei1 as [b11 [JB11 ei1]].
        destruct ei2 as [b22 [JB22 ei2]].
        assert (b11 <> b22). intro; subst.
        exploit me_inj. eauto. apply ei1. apply ei2. auto. auto. auto.
        intro; subst. exploit iwb_inj. eauto. apply JB11. apply JB22. auto. 
      }
      rewrite SBeq, SBeq', B.

      exploit me_not_dynamic_e. eauto.
      exploit me_not_dynamic_te. eauto.
      rewrite ! Forall_forall. intros Y Z.
      repeat destr.
      apply Z in i0. destr.
      apply Y in i0. destr.
  - intros (tm'' & REL' & INJ').
    rewrite REL'.
    eexists; repSplit; eauto.
    {
      inv INJ'; constructor; simpl; intros; eauto.
      inv mi_inj; constructor; simpl;intros; eauto.

      exploit free_list_nb_boxes_used. apply FL.
      exploit free_list_nb_boxes_used. apply X.

    exploit nb_boxes_release. apply REL. 
    exploit nb_boxes_release. apply REL'. exploit Mem.mi_size_mem. eapply Mem.mi_inj. apply INJ. auto.
    intros.
    unfold size_env in FreeOrd. lia. 
    }
    inv IWB. constructor; simpl; intros; eauto.
    + red in iwb_wb |- *.
      intros.
      rewrite <- Mem.size_block_snd.
      rewrite <- (MemReserve.release_bounds_of_block _ _ _ _ REL).
      rewrite Mem.size_block_snd.
      erewrite Mem.size_block_free_list. 4: eauto.
      erewrite <- MemReserve.release_mask. 2: eauto.
      erewrite Mem.freelist_mask. 2: eauto. apply iwb_wb in H. des H. destr; split; eauto. lia.

      rewrite Forall_forall.
      intros x IN.
      apply in_blocks_of_env in IN. dex. des IN. des a. des x. des p.
      subst. eapply me_bounds; eauto.
      eapply blocks_of_env_norepet; eauto. eapply me_inj; eauto.
    + rewrite <- ! Mem.size_block_snd.
      rewrite <- (MemReserve.release_bounds_of_block _ _ _ _ REL).
      rewrite <- (MemReserve.release_bounds_of_block _ _ _ _ REL').
      rewrite ! Mem.size_block_snd.
      erewrite Mem.size_block_free_list. 4: eauto.
      erewrite Mem.size_block_free_list with (m':=tm'). 4: eauto.
      repeat destr.

      * rewrite map_map, in_map_iff in i. dex. des i.
        eapply in_blocks_of_env in i0. dex. des i0. des a. des x. des p. subst.
        generalize (me_vars _ _ _ _ _ _ _ _ _ _ _ _ MENV i). intro A; inv A.
        destr.
        rewrite e2 in ENV. inv ENV.
        apply in_blocks_of_env' in TENV. assert (b' = b'0) by congruence. subst. destr.
        destr.
      * rewrite map_map, in_map_iff in i. dex. des i.
        eapply in_blocks_of_env in i0. dex. des i0. des a. des x. des p. subst.
        generalize (me_vars _ _ _ _ _ _ _ _ _ _ _ _ MENV i). intro A; inv A.
        destr.
        rewrite e2 in TENV. inv TENV.
        apply in_blocks_of_env' in ENV. assert (b = b1).
        eapply iwb_inj. eauto. eauto. subst. destr.
        destr. 
      * eauto.
      * rewrite Forall_forall.  
        intros x IN.
        apply in_blocks_of_env in IN. dex. des IN. des a. des x. des p.
        assert (exists b1, e ! i = Some (b1, t) /\ j b1 = Some (b0, 0)).
        generalize (me_vars _ _ _ _ _ _ _ _ _ _ _ _ MENV i). intro A; inv A.
        destr.
        rewrite e2 in TENV. inv TENV.
        rewrite ENV, <- MAPPED. eauto. destr.
        dex. des H0.
        subst. erewrite <- me_bounds_same. eapply me_bounds; eauto. eauto. eauto. eauto.
      * eapply blocks_of_env_norepet; eauto.
        intros.
        eapply me_mapped in ei1; eauto.
        eapply me_mapped in ei2; eauto.
        destruct ei1 as [b11 [JB11 ei1]].
        destruct ei2 as [b22 [JB22 ei2]].
        assert (b11 <> b22). intro; subst.
        exploit me_inj. eauto. apply ei1. apply ei2. auto. auto. auto.
        intro; subst. exploit iwb_inj. apply JB11. apply JB22. auto. 
      * rewrite Forall_forall.  
        intros x IN.
        apply in_blocks_of_env in IN. dex. des IN. des a. des x. des p.
        subst. eapply me_bounds; eauto.
      * eapply blocks_of_env_norepet; eauto.
        eapply me_inj; eauto.
    + rewrite <- (MemReserve.release_mask _ _ _ _ REL), <- (MemReserve.release_mask _ _ _ _ REL').
      rewrite (Mem.freelist_mask _ _ _ _ FL), (Mem.freelist_mask _ _ _ _ X). eauto.
    + apply iwb_no_oota.
      red in H.
      erewrite <- MemReserve.release_nextblock in H. 2: eauto.
      red. erewrite <- (Mem.nextblock_freelist _ _ _ X). auto.
Qed.

Fixpoint match_size_mem (k tk: cont) (m tm: mem) :=
  (Mem.nb_boxes_used_m tm <= Mem.nb_boxes_used_m m)%nat /\
 match k, tk with
   Kcall roi f e le k',
   Kcall troi tf te tle tk' =>
   (
     size_env te <= nb_boxes_static tm /\ ns2 (fn_id tf) <= Mem.nb_extra tm /\
     size_env e <= nb_boxes_static m /\ ns1 (fn_id f) <= Mem.nb_extra m /\
     forall m' tm',
       nb_boxes_static m' = nb_boxes_static m - size_env e ->
       nb_boxes_static tm' = nb_boxes_static tm - size_env te ->
       Mem.nb_extra m' = Mem.nb_extra m - ns1 (fn_id f) ->
       Mem.nb_extra tm' = Mem.nb_extra tm - ns2 (fn_id tf) ->
       forall C C', 
       nb_boxes_dynamic m' + C = nb_boxes_dynamic m + C' ->
       nb_boxes_dynamic tm' + C = nb_boxes_dynamic tm + C' ->
       match_size_mem k' tk' m' tm')%nat
 | Kstop, Kstop => True
 | Kseq s1 k', Kseq s2 tk' => match_size_mem k' tk' m tm
 | Kloop1 s1 s2 k', Kloop1 s1' s2' tk' => match_size_mem k' tk' m tm
 | Kloop2 s1 s2 k', Kloop2 s1' s2' tk' => match_size_mem k' tk' m tm
 | Kswitch k', Kswitch tk' => match_size_mem k' tk' m tm
 | _, _ => False
 end.

Lemma match_size_mem_rew (k tk: cont) (m tm: mem) :
  match_size_mem k tk m tm <->
  ((Mem.nb_boxes_used_m tm <= Mem.nb_boxes_used_m m)%nat /\
  match k, tk with
    Kcall roi f e le k',
    Kcall troi tf te tle tk' =>
    (
      size_env te <= nb_boxes_static tm /\ ns2 (fn_id tf) <= Mem.nb_extra tm /\
      size_env e <= nb_boxes_static m /\ ns1 (fn_id f) <= Mem.nb_extra m /\
      forall m' tm',
        nb_boxes_static m' = nb_boxes_static m - size_env e ->
        nb_boxes_static tm' = nb_boxes_static tm - size_env te ->
        Mem.nb_extra m' = Mem.nb_extra m - ns1 (fn_id f) ->
        Mem.nb_extra tm' = Mem.nb_extra tm - ns2 (fn_id tf) ->
        forall C C', 
          nb_boxes_dynamic m' + C = nb_boxes_dynamic m + C' ->
          nb_boxes_dynamic tm' + C = nb_boxes_dynamic tm + C' ->
          match_size_mem k' tk' m' tm')%nat
  | Kstop, Kstop => True
  | Kseq s1 k', Kseq s2 tk' => match_size_mem k' tk' m tm
  | Kloop1 s1 s2 k', Kloop1 s1' s2' tk' => match_size_mem k' tk' m tm
  | Kloop2 s1 s2 k', Kloop2 s1' s2' tk' => match_size_mem k' tk' m tm
  | Kswitch k', Kswitch tk' => match_size_mem k' tk' m tm
  | _, _ => False
  end).
Proof.
  induction k; simpl in *; intros; eauto; des tk.
Qed.

Lemma msm_le:
  forall k tk m tm,
    match_size_mem k tk m tm ->
    (Mem.nb_boxes_used_m tm <= Mem.nb_boxes_used_m m)%nat.
Proof.
  induction k; simpl in *; intros; eauto; des tk.
Qed.

Inductive match_states: state -> state -> Prop :=
| match_regular_states:
    forall f s k e le m tf ts tk te tle tm j lo hi tlo thi
      (IWB: inj_well_behaved j m tm)
      (TRF: transf_function f = OK tf)
      (TRS: simpl_stmt (cenv_for f) s = OK ts)
      (MENV: match_envs j (cenv_for f) e le m tm lo hi te tle tlo thi)
      (DIFF: (ns1 (fn_id f) + size_env e >=
              ns2 (fn_id tf) + size_env te)%nat)
      (MCONT: match_cont j (cenv_for f) k tk m tm lo tlo)
      (MSM: match_size_mem (Kcall None f e le k) (Kcall None tf te tle tk) m tm)
      (MINJ: Mem.inject true expr_inj_se j m tm)
      (COMPAT: compat_cenv (addr_taken_stmt s) (cenv_for f))
      (BOUND: Ple hi (Mem.nextblock m))
      (TBOUND: Ple thi (Mem.nextblock tm))
      (Pdefs: In (Gfun (Internal f)) (map snd (prog_defs prog))),
      match_states (State f s k e le m)
                   (State tf ts tk te tle tm)
  | match_call_state:
      forall fd vargs k m tfd tvargs tk tm j targs tres cconv
        (IWB: inj_well_behaved j m tm)
        (TRFD: transf_fundef fd = OK tfd)
        (MCONT: forall cenv, match_cont j cenv k tk m tm (Mem.nextblock m) (Mem.nextblock tm))
        (MSM: match_size_mem k tk m tm)
        (MINJ: Mem.inject true expr_inj_se j m tm)
        (AINJ: list_ei expr_inj_se j vargs tvargs)
        (FUNTY: type_of_fundef fd = Tfunction targs tres cconv)
        (ANORM: expr_list_casted vargs targs)
        (Pdefs: In (Gfun (fd)) (map snd (prog_defs prog))),
      match_states (Callstate fd vargs k m)
                   (Callstate tfd tvargs tk tm)
  | match_return_state:
      forall v k m tv tk tm j
        (IWB: inj_well_behaved j m tm)
        (MCONT: forall cenv, match_cont j cenv k tk m tm (Mem.nextblock m) (Mem.nextblock tm))
        (MSM: match_size_mem k tk m tm)
        (MINJ: Mem.inject true expr_inj_se j m tm)
        (RINJ: expr_inj_se j v tv)
      ,
      match_states (Returnstate v k m)
                   (Returnstate tv tk tm).

Lemma msm_call_cont:
  forall k k' m m' (MSM: match_size_mem k k' m m'),
    match_size_mem (call_cont k) (call_cont k') m m'.
Proof.
  induction k; simpl; intros; eauto.
  - des k'.
  - des k'. apply IHk; simpl; auto. destr.
  - des k'. apply IHk; simpl; auto. destr.
  - des k'. apply IHk; simpl; auto. destr.
  - des k'. apply IHk; simpl; auto. destr.
  - des k'.
Qed.

Section GotoMsm.
  
Variable f: meminj.
Variable cenv: compilenv.
Variables m tm: mem.
Variables bound tbound: block.
Variable lbl: ident.

Lemma simpl_find_label_msm:
  forall s k ts tk sm stm,
  simpl_stmt cenv s = OK ts ->
  match_size_mem k tk sm stm ->
  match find_label lbl s k with
  | None =>
      find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk', 
         find_label lbl ts tk = Some(ts', tk')
      /\ simpl_stmt cenv s' = OK ts'
      /\ match_size_mem k' tk' sm stm
  end

with simpl_find_label_msm_ls:
  forall ls k tls tk sm stm,
  simpl_lblstmt cenv ls = OK tls ->
  match_size_mem k tk sm stm ->
  match find_label_ls lbl ls k with
  | None =>
      find_label_ls lbl tls tk = None
  | Some(s', k') =>
      exists ts', exists tk', 
         find_label_ls lbl tls tk = Some(ts', tk')
      /\ simpl_stmt cenv s' = OK ts'
      /\ match_size_mem k' tk' sm stm
  end.

Proof.
  induction s; simpl; intros until stm; intros TS MC; auto.
  - (* skip *)
    monadInv TS; auto.
  - (* var *)
    destruct (is_liftable_var cenv e); monadInv TS; auto. 
  - (* set *)
    monadInv TS; auto.
  - (* call *)
    monadInv TS; auto.
  - (* builtin *)
    monadInv TS; auto.
  - (* seq *)
    monadInv TS.
    exploit (IHs1 (Kseq s2 k) x (Kseq x0 tk)); eauto with compat.
    simpl; split. eapply msm_le; eauto. eauto.
    destruct (find_label lbl s1 (Kseq s2 k)) as [[s' k']|]. 
    intros [ts' [tk' [P [Q R]]]]. exists ts'; exists tk'. simpl. rewrite P. auto.
    intros E. simpl. rewrite E. eapply IHs2; eauto with compat.
  - (* ifthenelse *)
    monadInv TS.
    exploit (IHs1 k x tk); eauto with compat. 
    destruct (find_label lbl s1 k) as [[s' k']|]. 
    intros [ts' [tk' [P [Q R ]]]]. exists ts'; exists tk'. simpl. rewrite P. auto. 
    intros E. simpl. rewrite E. eapply IHs2; eauto with compat.
  - (* loop *)
    monadInv TS.
    exploit (IHs1 (Kloop1 s1 s2 k) x (Kloop1 x x0 tk)); eauto with compat.
    simpl; split. eapply msm_le; eauto. eauto.
    destruct (find_label lbl s1 (Kloop1 s1 s2 k)) as [[s' k']|]. 
    intros [ts' [tk' [P [Q R]]]]. exists ts'; exists tk'. simpl; rewrite P. auto. 
    intros E. simpl; rewrite E. eapply IHs2; eauto with compat. econstructor; eauto with compat.
    eapply msm_le; eauto.
  - (* break *)
    monadInv TS; auto.
  - (* continue *)
    monadInv TS; auto.
  - (* return *)
    monadInv TS; auto.
  - (* switch *)
    monadInv TS. simpl.
    eapply simpl_find_label_msm_ls; eauto with compat. constructor; auto.
    eapply msm_le; eauto.
  - (* label *)
    monadInv TS. simpl.
    destruct (ident_eq lbl l).
    exists x; exists tk; auto.
    eapply IHs; eauto.
  - (* goto *)
    monadInv TS; auto.

  - induction ls; simpl; intros.
    + monadInv H. auto.
    + monadInv H.
      
      exploit (simpl_find_label_msm s (Kseq (seq_of_labeled_statement ls) k)
                                    x
                                    (Kseq (seq_of_labeled_statement x0) tk)).
      eauto. simpl. split.
      eapply msm_le; eauto. auto.
      destruct (find_label lbl s (Kseq (seq_of_labeled_statement ls) k)) as [[s' k']|].
      intros [ts' [tk' [P [Q R]]]]. exists ts'; exists tk'; split. simpl; rewrite P. auto. auto.
      intros E. simpl; rewrite E. eapply IHls; eauto with compat.
Qed.
 
End GotoMsm.

Lemma assign_loc_static_size:
  forall m m' ty a b
    (AL: assign_loc ty m a b m'),
    nb_boxes_static m = nb_boxes_static m'.
Proof.
  intros.
  unfold nb_boxes_static.
  erewrite assign_loc_mk_block_list; eauto.
  erewrite filter_ext. reflexivity.
  intros; des x. unfold is_static_block_b.
  inv AL; auto. unfold Mem.storev, Mem.store in STOREV; repeat destr_in STOREV; inv STOREV. reflexivity.
  unfold Mem.storebytes in SB; repeat destr_in SB; inv SB. reflexivity. 
Qed.

Lemma assign_loc_dynamic_size:
  forall m m' ty a b
    (AL: assign_loc ty m a b m'),
    nb_boxes_dynamic m = nb_boxes_dynamic m'.
Proof.
  intros.
  unfold nb_boxes_dynamic.
  erewrite assign_loc_mk_block_list; eauto.
  erewrite filter_ext. reflexivity.
  intros; des x. unfold is_dynamic_block_b.
  inv AL; auto. unfold Mem.storev, Mem.store in STOREV; repeat destr_in STOREV; inv STOREV. reflexivity.
  unfold Mem.storebytes in SB; repeat destr_in SB; inv SB. reflexivity. 
Qed.

Opaque match_size_mem.

Lemma alloc_variables_size_mem':
  forall vars m e m' e'
    (AV: alloc_variables e m vars e' m')
    (LNR: list_norepet (map fst vars))
    (IN: forall id, In id (map fst vars) -> e ! id = None)
    (VB: forall id b ty, e ! id = Some (b, ty) -> Mem.valid_block m b)
    (INJ:    forall (id1 id2 : positive) (b0 b2 : block) (ty1 ty2 : type),
      e ! id1 = Some (b0, ty1) -> e ! id2 = Some (b2, ty2) -> id1 <> id2 -> b0 <> b2),
    (nb_boxes_static m' = nb_boxes_static m + size_env e' - size_env e)%nat.
Proof.
  induction vars; simpl; intros.
  - inv AV. lia.
  - inv AV.
    specialize (IHvars _ _ _ _ H6).
    trim IHvars. inv LNR; auto.
    inv LNR.
    trim IHvars. intros. rewrite PTree.gsspec. destr. eauto.
    trim IHvars. intros. rewrite PTree.gsspec in H. destr_in H. inv H. eapply Mem.valid_new_block; eauto.
    eapply Mem.valid_block_alloc; eauto.
    trim IHvars.
    intros.
    rewrite PTree.gsspec in H, H0. destr_in H; destr_in H0. inv H.
    intro; subst. eapply VB in H0. eapply Mem.fresh_block_alloc in H0; eauto.
    intro; subst. inv H0. eapply VB in H. eapply Mem.fresh_block_alloc in H; eauto.
    eauto.
    rewrite IHvars.
    exploit alloc_static_nb_static. eauto. rewrite Zmax_r.
    intro B; rewrite <- B.
    generalize (blocks_set_elements_permut e id b1 ty). intro A.
    trim A.
    apply IN. auto.
    trim A. intro; dex.
    eapply VB in H. eapply Mem.fresh_block_alloc in H; eauto.
    trim A. auto.
    unfold size_env. rewrite (size_list_permut _ _ A).
    rewrite size_list_cons. rewrite Z.sub_0_r. lia.
    apply Zge_le, sizeof_pos.
Qed.

Lemma alloc_variables_size_env:
  forall vars m m' e'
    (AV: alloc_variables empty_env m vars e' m')
    (LNR: list_norepet (map fst vars)),
    (nb_boxes_static m' = nb_boxes_static m + size_env e')%nat.
Proof.
  intros. exploit alloc_variables_size_mem'. eauto. eauto.
  intros; apply PTree.gempty.
  intros. rewrite PTree.gempty in H; destr.
  intros. rewrite PTree.gempty in H; destr.
  replace (size_env empty_env) with O. lia.
  reflexivity.
Qed.

Lemma bind_parameters_mask:
  forall e m params args m' b,
    bind_parameters e m params args m' -> Mem.mask m' b = Mem.mask m b.
Proof.
  induction 1.
  auto.
  rewrite IHbind_parameters. symmetry; eapply assign_loc_mask; eauto. 
Qed.

Lemma blocks_of_env_charact':
  forall vars e' m' e m
    (AV: alloc_variables e m vars e' m')
    (lnr: list_norepet (map fst vars))
    (range: forall id b t, e!id = Some (b,t) -> Plt b (Mem.nextblock m))
    (inj0: forall id1 id2 b1 b2 ty1 ty2, e ! id1 = Some (b1,ty1) -> e!id2 = Some (b2,ty2) ->
                                    id1<>id2 -> b1 <> b2)
    (eid: forall id, ~ In id (map fst vars) -> e ! id = e' ! id)
    (eid': forall id, In id (map fst vars) -> e ! id = None)
  ,
    Permutation (map size_of_block (blocks_of_env e'))
                (fold_right (fun elt acc => sizeof (snd elt)::acc)
                            (map size_of_block (blocks_of_env e)) vars).
Proof.
  induction vars; simpl; intros; eauto.
  - inv AV. reflexivity.
  - inv lnr. inv AV.
    rewrite IHvars; eauto; clear IHvars.
    + rewrite fr_is_map. rewrite  fr_is_map.
      rewrite (Permutation_cons_app _ _ _ (Permutation_refl _)).
      apply Permutation_app_head.
      rewrite Permutation_map.
      2: apply blocks_set_elements_permut; auto.
      * simpl. rewrite Z.sub_0_r. reflexivity.
      * simpl in *. intro; dex.
        destruct (peq id0 id). subst.
        rewrite eid' in H; auto; congruence.
        destruct (in_dec peq id0 (map fst vars)).
        rewrite eid' in H; auto; congruence.
        eapply range in H; eauto.
        exploit Mem.alloc_result; eauto. intro. subst. xomega.
    + intros id0 b t.
      rewrite PTree.gsspec.
      destr_cond_match. subst. intro A; inv A.
      eapply Mem.valid_new_block; eauto.
      intro EI.
      exploit range; eauto.
      exploit Mem.nextblock_alloc; eauto. intro A; rewrite A.
      ppsimpl; lia.
    + intros id1 id2 b0 b2 ty1 ty2 EI1 EI2 DIFF.
      rewrite PTree.gsspec in EI1, EI2.
      destruct (peq id1 id); subst; inv EI1;
      destruct (peq id2 id); subst; inv EI2.
      * congruence.  
      * exploit range. eexact H0. exploit Mem.alloc_result; eauto.
        intros; intro; repeat subst. ppsimpl; lia.
      * exploit range. eexact H0. exploit Mem.alloc_result; eauto.
        intros; intro; repeat subst. ppsimpl; lia.
      * eapply inj0; eauto.
    + simpl in *; intros.
      rewrite PTree.gsspec.
      destr.
      subst.
      erewrite alloc_variables_in_not_in_vars; eauto.
      rewrite PTree.gss; auto.
      eapply eid; eauto. destr.
    +
      simpl in *; intros.
      rewrite PTree.gsspec; destr.
      eapply eid'; eauto.
Qed.


Lemma alloc_variables_lengths':
  forall c l m e m0 tm te tm0
    (CB : cenv_bound c l)
    (AV : alloc_variables empty_env m l e m0)
    (AV' : alloc_variables empty_env tm (remove_lifted c l) te tm0)
    (LNR : list_norepet (map fst l)),
    size_env e  =
    ((length (filter (fun it : VSet.elt * type => VSet.mem (fst it) c) l)) + size_env te)%nat.
Proof.
  intros.
  unfold size_env.
  unfold size_list, size_list_blocks.
  rewrite ! fold_left_map.
  setoid_rewrite  <- (fold_left_map (fun acc elt => (acc + elt)%nat)
                                   (fun elt => Mem.box_span (size_of_block elt))).
  erewrite Mem.fold_left_plus_permut.
  2: rewrite <- map_map. 2: apply Permutation_map. 2: eapply blocks_of_env_charact'; eauto.
  erewrite (Mem.fold_left_plus_permut (map _ (blocks_of_env te))).
  2: rewrite <- map_map. 2: apply Permutation_map. 
  2: eapply (blocks_of_env_charact' _ te); eauto.
  rewrite ! fr_is_map.
  replace (blocks_of_env empty_env) with (@nil (block*Z*Z)).
  simpl. rewrite ! app_nil_r.
  {
    clear - CB.
    rewrite <- ! fold_left_rev_right.
    rewrite <- ! map_rev.
    unfold remove_lifted.
    cut (cenv_bound c (rev l)).
    rewrite <- rev_length.
    rewrite <- ! filter_rev.
    unfold ident, VSet.elt in *.
    generalize (rev l). clear.
    set ( f := fun y x => (x+y)%nat).
    set ( g := fun (it: positive*type) => VSet.mem (fst it) c).
    set ( h := fun (it: positive*type) => negb (VSet.mem (fst it) c)).
    set ( to := fun elt : positive*type => sizeof (snd elt)).
    
    induction l; simpl; intros. lia. 
    inv H.
    rewrite IHl; auto; clear IHl.
    - destruct (g (i,ty)) eqn:?.
      assert (h (i,ty) = false).
      { unfold g, h in *; destr. rewrite Heqb; auto. }
      rewrite H.
      assert (0 < sizeof ty <= 8).
      {
        unfold g in Heqb.  destr.
      }
      + simpl. generalize (length (filter g l)).
        unfold f, to. simpl. intros.
        replace (Mem.box_span (sizeof ty)) with 1%nat. lia.
        rewrite box_span_small. auto.
        generalize (two_p_monotone 3 (Z.of_nat MA)). intro A. trim A.
        generalize MA_bound. lia.
        rewrite two_power_nat_two_p.
        change (two_p 3) with 8 in A. lia.
      + replace (h (i,ty)) with true.
        clear H3.
        simpl. generalize (length (filter g l)).
        unfold f, to.
        simpl.  
        intros. lia.
        unfold g, h in *; rewrite Heqb; destr.
    -  apply cenv_bound_rev; auto.
  }
  {
    unfold blocks_of_env.
    auto.
  }
  {
    unfold remove_lifted.
    rewrite filter_map with (pb:=fun id => negb (VSet.mem id c)).
    eapply filter_norepet; eauto.
    auto.
  }
  {
    intros id b t. rewrite PTree.gempty; congruence.
  }
  {
    intros id1 id2 b1 b2 ty1 ty2; rewrite PTree.gempty; congruence.
  }
  intros. symmetry; eapply alloc_variables_in_not_in_vars; eauto.
  intros; apply PTree.gempty.
  {
    intros id b t. rewrite PTree.gempty; congruence.
  }
  {
    intros id1 id2 b1 b2 ty1 ty2; rewrite PTree.gempty; congruence.
  }
  intros. symmetry; eapply alloc_variables_in_not_in_vars; eauto.
  intros; apply PTree.gempty.
Qed.

Lemma bind_parameters_dynamic:
  forall e m v lsv m' (BP:bind_parameters e m v lsv m') b,
    Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b.
Proof.
  induction 1; simpl; intros; eauto. tauto.
  rewrite (assign_loc_is_dynamic_block _ _ _ _ _ H0). eauto.
Qed.

Lemma alloc_variables_dynamic:
  forall e m v e' m'
    (AV: alloc_variables e m v e' m')
    b,
    Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b.
Proof.
  induction 1; simpl; intros; eauto. tauto.
  rewrite Mem.is_block_dynamic_alloc. 2: eauto. eauto.
Qed.

Lemma filter_app_permut:
  forall {A} (f: A -> bool) l,
    Permutation
      (filter f l ++ filter (fun x => negb (f x)) l)
      l.
Proof.
  intros.
  des (partition f l).
  exploit (partition_app_perm (A:= A)). eauto.
  intro P. etransitivity. 2: symmetry; apply P. apply Permutation_app.
  eapply partition_filter in Heqp. subst; reflexivity.
  eapply partition_filter_r in Heqp. subst. reflexivity.
Qed.

Lemma fold_left_plus_length:
  forall l (F: Forall (fun x => x = 1%nat) l),
    fold_left Peano.plus l O = length l.
Proof.
  induction l; simpl; intros; eauto. rewrite Mem.fold_left_plus_rew. rewrite IHl.  inv F. lia.
  inv F; auto.
Qed.

Lemma bind_parameters_nb_extra:
  forall e m v lsv m' (BP:bind_parameters e m v lsv m'),
    Mem.nb_extra m = Mem.nb_extra m'.
Proof.
  induction 1; simpl; intros; eauto.
  exploit assign_loc_nb_extra; eauto. lia.
Qed.


Lemma alloc_variables_nb_dynamic:
  forall e m vars e2 m2 (AV: alloc_variables e m vars e2 m2),
    nb_boxes_dynamic m = nb_boxes_dynamic m2.
Proof.
  induction 1; simpl; intros; eauto. rewrite <- IHAV.
  unfold nb_boxes_dynamic.
  eapply Mem.nb_used_permut.
  apply Permutation_intro.
  intros; repeat decide equality.
  apply filter_norepet. apply mbla_norepet'.
  apply filter_norepet. apply mbla_norepet'.
  intros. rewrite ! filter_In.
  unfold Mem.mk_block_list.
  Transparent Mem.alloc.
  unfold Mem.alloc, Mem.low_alloc in H; destr_in H; inv H. simpl.
  unfold is_dynamic_block_b, Mem.size_block. simpl.
  erewrite mk_block_list_aux_eq. simpl.
  rewrite PMap.gsspec. split; repeat destr.
  erewrite Mem.blocktype_valid in Heqo. destr. rewrite e0. clear. xomega.
  intros [[A|A] B]. subst. destr. split; auto. apply MA_bound.
Qed.

  Lemma bp_boxes_static:
    forall e m vars le m',
      bind_parameters e m vars le m' ->
      nb_boxes_static m = nb_boxes_static m'.
  Proof.
    unfold nb_boxes_static.
    intros. f_equal.
    unfold Mem.mk_block_list.
    rewrite (bind_parameters_nextblock _ _ _ _ _ H). erewrite filter_ext.
    erewrite mk_block_list_aux_ext. reflexivity.
    intros; rewrite <- ! Mem.size_block_snd. erewrite bp_bounds. reflexivity.
    eauto.
    intros.
    generalize (bind_parameters_dynamic _ _ _ _ _ H (fst x)).
    unfold is_static_block_b, Mem.is_dynamic_block.
    repeat destr.
  Qed.

  Lemma bp_boxes_dynamic:
    forall e m vars le m',
      bind_parameters e m vars le m' ->
      nb_boxes_dynamic m = nb_boxes_dynamic m'.
  Proof.
    unfold nb_boxes_dynamic.
    intros. f_equal.
    unfold Mem.mk_block_list.
    rewrite (bind_parameters_nextblock _ _ _ _ _ H). erewrite filter_ext.
    erewrite mk_block_list_aux_ext. reflexivity.
    intros; rewrite <- ! Mem.size_block_snd. erewrite bp_bounds. reflexivity.
    eauto.
    intros.
    generalize (bind_parameters_dynamic _ _ _ _ _ H (fst x)).
    unfold is_dynamic_block_b, Mem.is_dynamic_block.
    repeat destr.
  Qed.

    Lemma match_size_mem_same_size:
    forall k tk m tm (MSM: match_size_mem k tk m tm)
      m' tm'
      (stEq: nb_boxes_static m = nb_boxes_static m')
      (stEqt: nb_boxes_static tm = nb_boxes_static tm')
      C C'
      (dynEq: (nb_boxes_dynamic m + C = nb_boxes_dynamic m' + C')%nat)
      (dynEqt: (nb_boxes_dynamic tm + C = nb_boxes_dynamic tm' + C')%nat)
      (exEq: Mem.nb_extra m = Mem.nb_extra m')
      (exEqt: Mem.nb_extra tm = Mem.nb_extra tm'),
      match_size_mem k tk m' tm'.
  Proof.
    Transparent match_size_mem.
    induction k; simpl; intros; des tk.
    - rewrite ! nb_boxes_sep in *. split. des MSM. lia. auto.
    - rewrite ! nb_boxes_sep in *. split; des MSM. lia. eapply IHk; eauto.
    - rewrite ! nb_boxes_sep in *. split; des MSM. lia. eapply IHk; eauto.
    - rewrite ! nb_boxes_sep in *. split; des MSM. lia. eapply IHk; eauto.
    - rewrite ! nb_boxes_sep in *. split; des MSM. lia. eapply IHk; eauto.
    - rewrite ! nb_boxes_sep in *.
      destruct MSM as (A&B&G&D&E&F). repSplit; eauto. lia. lia. lia. lia. lia.
      intros. eapply IHk. eapply F.
      rewrite stEq; eauto.
      rewrite stEqt; eauto.
      rewrite exEq; eauto.
      rewrite exEqt; eauto.
      instantiate (1 := (C'0 + C)%nat).
      instantiate (1 := (C0 + C')%nat). lia. lia. 
      auto. auto. instantiate (1:=O); instantiate (1 := O); lia. lia. auto. auto.
    Opaque match_size_mem.
  Qed.

  Lemma alloc_variables_nb_extra:
  forall e m vars e2 m2 (AV: alloc_variables e m vars e2 m2),
    Mem.nb_extra m = Mem.nb_extra m2.
Proof.
  induction 1; simpl; intros; eauto. rewrite <- IHAV.
  unfold Mem.alloc, Mem.low_alloc in H; destr_in H; inv H. reflexivity.
Qed.


Lemma step_simulation:
  forall S1 t S2,
    step1 ge ns1 S1 t S2 ->
    forall S1' (MS: match_states S1 S1'),
    exists S2', plus (fun ge => step2 ge ns2) tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; simpl; intros; inv MS; simpl in *; try (monadInv TRS).

  - (* assign *)
    generalize (is_liftable_var_charact (cenv_for f) a1); destruct (is_liftable_var (cenv_for f) a1) as [id|]; monadInv TRS.
    + (* liftable *)
      intros [ty [P Q]]; subst a1; simpl in *.
      exploit eval_simpl_expr; eauto with compat. intros [tv2 [A B]].
      exploit sem_cast_expr_inject; eauto. intros [tv [C D]].
      exploit me_vars; eauto. instantiate (1 := id). intros MV. 
      inv H.
      * (* local variable *)
        econstructor; split. 
        apply plus_one. econstructor. eapply make_cast_correct. eexact A. rewrite typeof_simpl_expr. eexact C.
        {
          econstructor; eauto with compat.
          - eapply iwb_inv. eauto.
            eapply assign_loc_bounds; eauto.
            auto.
            eapply assign_loc_mask; eauto.
            auto.
            intros; xomega.
          - eapply match_envs_assign_lifted; eauto. eapply Equivalences.sem_cast_expr_idem; eauto.
          - eapply match_cont_assign_loc; eauto.
            exploit me_range; eauto. intros.
            apply Mem.norm_ptr_same in H3; inv H3; xomega.
            destr.
            eapply Mem.mi_inj_dynamic; eauto.
            tauto.
          - rewrite match_size_mem_rew in MSM.
            destruct MSM as (E&F&G&H&I&J).
            rewrite match_size_mem_rew. rewrite <- (assign_loc_size_mem _ _ _ _ _ H2); auto.
            rewrite <- (assign_loc_static_size _ _ _ _ _ H2), <- (assign_loc_nb_extra _ _ _ _ _ H2).
            repSplit; auto.
            intros.
            eapply J; eauto.
            erewrite (assign_loc_dynamic_size _ _ _ _ _ H2); eauto.
          - inv MV; try congruence. inv H2; try congruence. unfold Mem.storev in STOREV.
            destr_in STOREV. apply Mem.norm_ptr_same in Heqv1. inv Heqv1.
            eapply Mem.store_unmapped_inject; eauto. congruence. 
          - erewrite assign_loc_nextblock; eauto.
        } 
      * (* global variable *)
        inv MV; congruence.
    + (* not liftable *)
      intros P. 
      exploit eval_simpl_lvalue; eauto with compat. intros [tbtofs [E F]]. 
      exploit eval_simpl_expr; eauto with compat. intros [tv2 [A B]].
      exploit sem_cast_expr_inject; eauto. intros [tv [C D]].
      exploit assign_loc_inject; eauto.
      eapply expr_inj_se_not_dep; eauto.
      eapply expr_inj_se_not_dep; eauto.
      intros [tm' [X [Y Z]]]. 
      econstructor; split.
      * apply plus_one. econstructor. eexact E. eexact A. repeat rewrite typeof_simpl_expr. eexact C. 
        rewrite typeof_simpl_expr; auto. eexact X.
      * {
          econstructor; eauto with compat.
          - eapply iwb_inv. eauto.
            eapply assign_loc_bounds; eauto.
            eapply assign_loc_bounds; eauto.
            eapply assign_loc_mask; eauto.
            eapply assign_loc_mask; eauto.
            intros b'. erewrite <- assign_loc_nextblock.  2: eauto. xomega.
          - eapply match_envs_invariant; eauto.
            intros. eapply assign_loc_bounds; eauto.
            intros. eapply assign_loc_bounds; eauto.
            destr.
            eapply Mem.mi_inj_dynamic; eauto.
            intros; eapply assign_loc_is_dynamic_block; eauto.
            intros; eapply assign_loc_is_dynamic_block; eauto.
          - eapply match_cont_invariant; eauto.
            intros. eapply assign_loc_bounds; eauto.
            intros. eapply assign_loc_bounds; eauto.
            destr.
            eapply Mem.mi_inj_dynamic; eauto.
            intros; eapply assign_loc_is_dynamic_block; eauto.
            intros; eapply assign_loc_is_dynamic_block; eauto.
          - rewrite match_size_mem_rew in MSM.
            destruct MSM as (E'&F'&G&H'&I&J).
            rewrite match_size_mem_rew.
            rewrite <- (assign_loc_size_mem _ _ _ _ _ H2); auto.
            rewrite <- (assign_loc_static_size _ _ _ _ _ H2), <- (assign_loc_nb_extra _ _ _ _ _ H2).
            rewrite <- (assign_loc_size_mem _ _ _ _ _ X); auto.
            rewrite <- (assign_loc_static_size _ _ _ _ _ X), <- (assign_loc_nb_extra _ _ _ _ _ X).
            erewrite <- (assign_loc_dynamic_size _ _ _ _ _ H2), <- (assign_loc_dynamic_size _ _ _ _ _ X); eauto.
            repSplit; auto.
          - erewrite assign_loc_nextblock; eauto.
          - erewrite assign_loc_nextblock; eauto.
        }
  - (* set temporary *)
    exploit eval_simpl_expr; eauto with compat. intros [tv [A B]].
    econstructor; split.
    apply plus_one. econstructor. eauto. 
    econstructor; eauto with compat. 
    eapply match_envs_set_temp; eauto. 

  - (* call *)
    exploit eval_simpl_expr; eauto with compat. intros [tvf [A B]].
    exploit eval_simpl_exprlist; eauto with compat. intros [CASTED [tvargs [C D]]].
    exploit match_cont_find_funct; eauto.
    eapply expr_inj_se_not_dep; eauto.
    intros [tfd [P Q]].
    econstructor; split.
    apply plus_one. eapply step_call with (fd := tfd).
    rewrite typeof_simpl_expr. eauto.
    eauto. eauto. eauto.  
    erewrite type_of_fundef_preserved; eauto.
    econstructor; eauto. 
    intros. econstructor; eauto.
    simpl; auto.
    
    exploit (Genv.find_funct_inversion m prog); eauto.
    intro; dex; destr. 
    rewrite in_map_iff; eexists; split; simpl; eauto. reflexivity.

  - (* builtin *)
    exploit eval_simpl_exprlist; eauto with compat. intros [CASTED [tvargs [C D]]].
    exploit external_call_mem_inject_forget; eauto.
    apply match_globalenvs_preserves_globals; eauto with compat.
    eapply list_expr_inj_se_not_dep; eauto.
    intros [f' [tvres [tm' [EC' [IWB' [EI [MINJ' [UNCH1 [UNCH2 [INCR [SEP [SZ [ST [ST' [EXT EXT']]]]]]]]]]]]]]].
    econstructor; split.
    + apply plus_one. econstructor; eauto. eapply external_call_symbols_preserved; eauto. 
      exact symbols_preserved. exact varinfo_preserved.
    + eapply match_regular_states with (j:=f') ; eauto with compat.
      * eapply match_envs_set_opttemp; eauto.
        move MENV at bottom.
        eapply match_envs_extcall; eauto.
        intros. symmetry; eapply extcall_bounds; eauto. red; xomega.
        intros. symmetry; eapply extcall_bounds; eauto. red; xomega.
        intros. 
        eapply Mem.mi_inj_dynamic; eauto.
        intros; eapply external_call_dyn; eauto. red; xomega.
        intros; eapply external_call_dyn; eauto. red; xomega.

      * eapply match_cont_extcall; eauto.
        intros. symmetry; eapply extcall_bounds; eauto. inv MENV; red; xomega.
        intros. symmetry; eapply extcall_bounds; eauto. inv MENV; red; xomega.
        inv MENV; xomega.
        inv MENV; xomega. 
        eapply Mem.mi_inj_dynamic; eauto.
        intros; eapply external_call_dyn; eauto. inv MENV; red; xomega.
        intros; eapply external_call_dyn; eauto. inv MENV; red; xomega.

      * rewrite match_size_mem_rew in MSM.
        destruct MSM as (MSM1 & MSM2 & MSM3 & MSM4 & MSM5 & MSM6).
        simpl.
        rewrite match_size_mem_rew. rewrite <- ST, <- ST', <- EXT, <- EXT'.
        dex. des SZ.
        repSplit.
        lia. assumption. assumption. assumption. assumption. intros.
        cut (nb_boxes_dynamic m' + C0 = nb_boxes_dynamic m + C' /\
             nb_boxes_dynamic tm' + C0 = nb_boxes_dynamic tm + C')%nat.
        intros (DYN & tDYN).
        eapply MSM6; eauto.
        instantiate (2 := (C1 + C0)%nat).
        instantiate (1 := (C' + C'0)%nat).
        lia. lia.
        revert e0 e1. rewrite ! nb_boxes_sep.
        rewrite ST, ST', EXT, EXT'. lia.
      * eapply Ple_trans; eauto. eapply external_call_nextblock; eauto.
      * eapply Ple_trans; eauto. eapply external_call_nextblock; eauto.

  - (* sequence *)
    econstructor; split. apply plus_one. econstructor.
    econstructor; eauto with compat. econstructor; eauto with compat.
    rewrite match_size_mem_rew in MSM.
    rewrite match_size_mem_rew. destruct MSM as (A & B& C&D&E&F). repSplit; auto.
    intros; simpl.
    exploit F; eauto. intro MSM.
    rewrite match_size_mem_rew. split. eapply msm_le; eauto. auto.

  - (* skip sequence *)
    inv MCONT. econstructor; split. apply plus_one. econstructor. econstructor; eauto. 
    rewrite match_size_mem_rew in MSM.
    rewrite match_size_mem_rew. destruct MSM as (A & B& C&D&E&F). repSplit; auto.
    intros; simpl.
    exploit F; eauto. intro MSM.
    rewrite match_size_mem_rew in MSM. destr.
    
  - (* continue sequence *)
    inv MCONT. econstructor; split. apply plus_one. econstructor. econstructor; eauto.
    rewrite match_size_mem_rew in MSM.
    rewrite match_size_mem_rew. destruct MSM as (A & B& C&D&E&F). repSplit; auto.
    intros; simpl.
    exploit F; eauto. intro MSM.
    rewrite match_size_mem_rew in MSM. destr.

  - (* break sequence *)
    inv MCONT. econstructor; split. apply plus_one. econstructor. econstructor; eauto.
    rewrite match_size_mem_rew in MSM.
    rewrite match_size_mem_rew. destruct MSM as (A & B& C&D&E&F). repSplit; auto.
    intros; simpl.
    exploit F; eauto. intro MSM.
    rewrite match_size_mem_rew in MSM. destr.

  - (* ifthenelse *)
    exploit eval_simpl_expr; eauto with compat. intros [tv [A B]].
    econstructor; split.
    apply plus_one. apply step_ifthenelse with (v1 := tv) (b := b). auto.
    rewrite typeof_simpl_expr.
    assert (EI:= bool_expr_inj _ wf_inj_expr_inj_se _ _ _ (typeof a) B).
    generalize (forget_norm _ _ wf_inj_expr_inj_se _ _ _ MINJ IWB _ _ EI); intro VI.
    rewrite H0 in VI. trim VI.
    eapply sep_inj_bool_expr.
    eapply expr_inj_se_not_dep; eauto.
    inv VI; auto.
    destruct (Int.eq b Int.zero); econstructor; eauto with compat.

  - (* loop *)
    econstructor; split. apply plus_one. econstructor. econstructor; eauto with compat.
    econstructor; eauto with compat.
    rewrite match_size_mem_rew in MSM.
    rewrite match_size_mem_rew. destruct MSM as (A & B& C&D&E&F). repSplit; auto.
    intros; simpl.
    exploit F; eauto. intro MSM.
    rewrite match_size_mem_rew. split. eapply msm_le; eauto. assumption.
    
  - (* skip-or-continue loop *)
    inv MCONT. econstructor; split.
    apply plus_one. econstructor. destruct H; subst x; simpl in *; intuition congruence. 
    econstructor; eauto with compat. econstructor; eauto with compat.

  - (* break loop1 *)
    inv MCONT. econstructor; split. apply plus_one. eapply step_break_loop1.
    econstructor; eauto.
    rewrite match_size_mem_rew in MSM.
    rewrite match_size_mem_rew. destruct MSM as (A & B& C&D&E&F). repSplit; auto.
    intros; simpl.
    exploit F; eauto. intro MSM.
    rewrite match_size_mem_rew in MSM. destr.
    
  - (* skip loop2 *)
    inv MCONT. econstructor; split. apply plus_one. eapply step_skip_loop2. 
    econstructor; eauto with compat. simpl; rewrite H2; rewrite H4; auto.
    rewrite match_size_mem_rew in MSM.
    rewrite match_size_mem_rew. destruct MSM as (A & B& C&D&E&F). repSplit; auto.
    intros; simpl.
    exploit F; eauto. intro MSM.
    rewrite match_size_mem_rew in MSM. destr.

  - (* break loop2 *)
    inv MCONT. econstructor; split. apply plus_one. eapply step_break_loop2. 
    econstructor; eauto.
    rewrite match_size_mem_rew in MSM.
    rewrite match_size_mem_rew. destruct MSM as (A & B& C&D&E&F). repSplit; auto.
    intros; simpl.
    exploit F; eauto. intro MSM.
    rewrite match_size_mem_rew in MSM. destr.
    
  - (* return none *) 
    rewrite match_size_mem_rew in MSM.
    destruct MSM as (A&B&C&D&E&F). replace (fn_id tf) with (fn_id f) in *. 

    edestruct (free_list_preserves _ _ _ _ te H _ IWB MINJ) as [tm' [tm'' [FL' [REL' [INJ IWB']]]]]; eauto.
    trim (F m'' tm'').
    rewrite <- (release_boxes_nb_static _ _ _ H0).
    exploit free_list_nb_static'. apply H.
    eapply me_not_dynamic_e; eauto. unfold size_env. lia.
    trim F.
    rewrite <- (release_boxes_nb_static _ _ _ REL').
    exploit free_list_nb_static'. apply FL'.
    eapply me_not_dynamic_te; eauto. unfold size_env. clear. lia.
    trim F.
    rewrite (Mem.nb_extra_free_list _ _ _ H).
    rewrite (nb_extra_release _ _ _ H0). clear. lia.
    trim F.
    rewrite (Mem.nb_extra_free_list _ _ _ FL').
    rewrite (nb_extra_release _ _ _ REL').
    clear. lia.
    trim (F O O).

    
    rewrite <- (release_nb_dynamic _ _ _ H0).
    rewrite (free_list_static_nb_dynamic _ _ _ H). lia.
    eapply me_not_dynamic_e; eauto.
    trim F.
    rewrite <- (release_nb_dynamic _ _ _ REL').
    rewrite (free_list_static_nb_dynamic _ _ _ FL'). lia.
    eapply me_not_dynamic_te; eauto.

    trim INJ. exploit msm_le. eapply F.
    exploit match_cont_sm. apply H. eauto.
    exploit match_cont_sm. apply FL'. eauto. clear. lia.

    econstructor; split.
    apply plus_one.
    econstructor; eauto. 
    replace (fn_id tf) with (fn_id f). eauto.
    unfold transf_function in TRF; monadInv TRF. reflexivity.

    econstructor; eauto. 
    + intros. eapply match_cont_call_cont.
      eapply match_cont_free_env'. 2: eauto. eauto. eauto. eauto.
      eauto. eauto. eauto. eauto. eauto. eauto.
    + eapply msm_call_cont; eauto.
    + apply expr_inj_se_vundef.
    + unfold transf_function in TRF; monadInv TRF. reflexivity.

  - (* return some *)
    exploit eval_simpl_expr; eauto with compat. intros [tv [A B]].
    exploit sem_cast_expr_inject; eauto. intros [tv' [C D]].

    rewrite match_size_mem_rew in MSM.
    destruct MSM as (A'&B'&C'&D'&E&F). replace (fn_id tf) with (fn_id f) in *. 

    edestruct (free_list_preserves _ _ _ _ te H1 _ IWB MINJ) as [tm' [tm'' [FL' [REL' [INJ IWB']]]]]; eauto.
    trim (F m'' tm'').
    rewrite <- (release_boxes_nb_static _ _ _ H2).
    exploit free_list_nb_static'. apply H1.
    eapply me_not_dynamic_e; eauto. unfold size_env. lia.
    trim F.
    rewrite <- (release_boxes_nb_static _ _ _ REL').
    exploit free_list_nb_static'. apply FL'.
    eapply me_not_dynamic_te; eauto. unfold size_env. clear. lia.
    trim F.
    rewrite (Mem.nb_extra_free_list _ _ _ H1).
    rewrite (nb_extra_release _ _ _ H2). clear. lia.
    trim F.
    rewrite (Mem.nb_extra_free_list _ _ _ FL').
    rewrite (nb_extra_release _ _ _ REL').
    clear. lia. 

    trim (F O O).
    rewrite <- (release_nb_dynamic _ _ _ H2).
    rewrite (free_list_static_nb_dynamic _ _ _ H1). lia.
    eapply me_not_dynamic_e; eauto.
    trim F.
    rewrite <- (release_nb_dynamic _ _ _ REL').
    rewrite (free_list_static_nb_dynamic _ _ _ FL'). lia.
    eapply me_not_dynamic_te; eauto.

    trim INJ. exploit msm_le. apply F.
    exploit match_cont_sm. apply H1. eauto.
    exploit match_cont_sm. apply FL'. eauto. clear. lia.

    econstructor; split.
    apply plus_one.
    econstructor; eauto. rewrite typeof_simpl_expr. monadInv TRF; simpl; eauto.
    monadInv TRF; simpl; eauto.
    econstructor; eauto.
    intros. eapply match_cont_call_cont. eapply match_cont_free_env'. 2: eauto.
    eauto. eauto. eauto. eauto. eauto. eauto.
    eauto. eauto. eauto. 
    eapply msm_call_cont; eauto. monadInv TRF; reflexivity.
    
  - (* skip call *)
    rewrite match_size_mem_rew in MSM.
    destruct MSM as (A&B&C&D&E&F). replace (fn_id tf) with (fn_id f) in *. 

    edestruct (free_list_preserves _ _ _ _ te H0 _ IWB MINJ) as [tm' [tm'' [FL' [REL' [INJ IWB']]]]]; eauto.
    trim (F m'' tm'').
    rewrite <- (release_boxes_nb_static _ _ _ H1).
    exploit free_list_nb_static'. apply H0.
    eapply me_not_dynamic_e; eauto. unfold size_env. lia.
    trim F.
    rewrite <- (release_boxes_nb_static _ _ _ REL').
    exploit free_list_nb_static'. apply FL'.
    eapply me_not_dynamic_te; eauto. unfold size_env. clear. lia.
    trim F.
    rewrite (Mem.nb_extra_free_list _ _ _ H0).
    rewrite (nb_extra_release _ _ _ H1). clear. lia.
    trim F.
    rewrite (Mem.nb_extra_free_list _ _ _ FL').
    rewrite (nb_extra_release _ _ _ REL').
    clear. lia. 
    trim (F O O).
    rewrite <- (release_nb_dynamic _ _ _ H1).
    rewrite (free_list_static_nb_dynamic _ _ _ H0). lia.
    eapply me_not_dynamic_e; eauto.
    trim F.
    rewrite <- (release_nb_dynamic _ _ _ REL').
    rewrite (free_list_static_nb_dynamic _ _ _ FL'). lia.
    eapply me_not_dynamic_te; eauto.
    trim INJ. exploit msm_le. apply F.
    exploit match_cont_sm. apply H0. eauto.
    exploit match_cont_sm. apply FL'. eauto. clear. lia.
    econstructor; split. apply plus_one. econstructor; eauto.
    eapply match_cont_is_call_cont; eauto.
    monadInv TRF; simpl; eauto.
    econstructor; eauto.
    intros. apply match_cont_change_cenv with (cenv_for f); auto. eapply match_cont_free_env'. 2: eauto.
    eauto. eauto. eauto. eauto. eauto. eauto.
    eauto. eauto. eauto. 
    apply expr_inj_se_vundef.
    monadInv TRF; reflexivity.

  - (* switch *)
    exploit eval_simpl_expr; eauto with compat. intros [tv [A B]].
    econstructor; split. apply plus_one. econstructor; eauto.
    rewrite typeof_simpl_expr. instantiate (1 := n).
    assert (SI:sep_inj m j v) by (eapply expr_inj_se_not_dep; eauto).
    generalize (forget_norm _ _ wf_inj_expr_inj_se _ _ _ MINJ IWB _ _ B SI); intro VI.
    generalize (forget_norm _ _ wf_inj_expr_inj_se _ _ _ MINJ IWB _ _ B SI); intro VL.
    unfold sem_switch_arg_expr in *; (destr; revert H0; destr); [inv VI|inv VL]; auto.
    econstructor; eauto. 
    erewrite simpl_seq_of_labeled_statement. reflexivity.
    eapply simpl_select_switch; eauto. 
    econstructor; eauto.
    rewrite match_size_mem_rew in MSM.
    rewrite match_size_mem_rew. destruct MSM as (A' & B'& C&D&E&F). repSplit; auto.
    intros; simpl.
    exploit F; eauto. intro MSM.
    rewrite match_size_mem_rew. split. eapply msm_le. eauto. auto.

    rewrite addr_taken_seq_of_labeled_statement. 
    apply compat_cenv_select_switch. eauto with compat.

  - (* skip-break switch *)
    inv MCONT. econstructor; split. 
    apply plus_one. eapply step_skip_break_switch. destruct H; subst x; simpl in *; intuition congruence. 
    econstructor; eauto with compat.
    rewrite match_size_mem_rew in MSM.
    rewrite match_size_mem_rew. destruct MSM as (A' & B'& C&D&E&F). repSplit; auto.
    intros; simpl.
    exploit F; eauto. intro MSM.
    rewrite match_size_mem_rew in MSM. destr.
    
  - (* continue switch *)
    inv MCONT. econstructor; split. 
    apply plus_one. eapply step_continue_switch.
    econstructor; eauto with compat.
    rewrite match_size_mem_rew in MSM.
    rewrite match_size_mem_rew. destruct MSM as (A' & B'& C&D&E&F). repSplit; auto.
    intros; simpl.
    exploit F; eauto. intro MSM.
    rewrite match_size_mem_rew in MSM. destr.
    
  - (* label *)
    econstructor; split. apply plus_one. econstructor. econstructor; eauto.

  - (* goto *)
    generalize TRF; intros TRF'. monadInv TRF'. 
    exploit (simpl_find_label j (cenv_for f) m tm lo tlo lbl (fn_body f) (call_cont k) x (call_cont tk)).
    eauto. eapply match_cont_call_cont. eauto.  
    apply compat_cenv_for.
    rewrite H. intros [ts' [tk' [A [B [C D]]]]]. 
    econstructor; split.
    apply plus_one. econstructor; eauto. simpl. rewrite find_label_store_params. eexact A.
    econstructor; eauto.


    rewrite match_size_mem_rew in MSM |- *.
    destruct MSM as (A' & B'& C'&D'&E&F). repSplit; auto. simpl.
    intros.

    exploit simpl_find_label_msm. eexact EQ.
    eapply msm_call_cont. 
    eapply F; eauto.
    instantiate (1:=lbl). rewrite H.
    intros [ts'0 [tk'0 [FL [SS MSM]]]].
    rewrite A in FL; inv FL.
    rewrite SS in C; inv C. auto.
    
  - (* internal function *)
    monadInv TRFD. inv H. 
    generalize EQ; intro EQ'; monadInv EQ'.
    assert (LNR : list_norepet (var_names (varsort (fn_params f ++ fn_vars f)))).
    { unfold var_names.
      unfold var_names in H0. rewrite <- map_app in H0.
      eapply permutation_norepet. 2: eexact H0.
      apply Permutation.Permutation_map.
      apply varsort_permut. }
    exploit (fun t lnr FB => match_envs_alloc_variables
               (cenv_for_gen (addr_taken_stmt f.(fn_body))
                             (varsort (fn_params f ++ fn_vars f)))
               m
               _ e m0 t j
               tm  (cenv_bound_for_gen _ lnr _)
               IWB
               O FB H1 (ns1 (fn_id f)) m2 (ns2 (fn_id f))
            ); eauto.
      
    + red; intros.
      generalize (Mem.mi_size_mem _ _ _ _ _ (Mem.mi_inj _ _ _ _ _ MINJ)).
      intuition lia.
    + exploit ns1_spec; eauto. lia.
    + exploit ns1_spec; eauto. lia.
    + intros. eapply cenv_for_gen_by_value; eauto. rewrite VSF.mem_iff. eexact H2.
    + intros. eapply cenv_for_gen_domain. rewrite VSF.mem_iff. eexact H.
    + intros [j' [te [tm0 [m3' [A [B [FrB [C [D [E [F [G IWB']]]]]]]]]]]].
      (* exploit sinj_simpl. 2: apply SINJ'. lia. *)
      (* intros [f' [l' [SINJ'' [INCR [sublist [INCRspec [[l1 [EQl1 EQlen1]] PropFirst]]]]]]]. *)
      (* cut (match_envs l l2' j' *)
      (*                 (cenv_for_gen (addr_taken_stmt (fn_body f)) *)
      (*                               (varsort (fn_params f ++ fn_vars f))) e *)
      (*                 (create_undef_temps (fn_temps f)) m2 m3' (Mem.nextblock m) *)
      (*                 (Mem.nextblock m0) (Mem.nextblock m2) te *)
      (*                 (create_undef_temps *)
      (*                    (add_lifted *)
      (*                       (cenv_for_gen (addr_taken_stmt (fn_body f)) *)
      (*                                     (varsort (fn_params f ++ fn_vars f))) *)
      (*                       (varsort (fn_params f ++ fn_vars f))  *)
      (*                       (fn_temps f))) (Mem.nextblock tm) (Mem.nextblock tm0) *)
      (*                 (Mem.nextblock m3') f'). *)
      (* clear C; intro C. *)
      exploit (store_params_correct true ns2 j').
      * eauto.
      * eapply list_norepet_append_left; eauto.
      * apply expr_casted_list_params. unfold type_of_function in FUNTY. congruence.
      * apply expr_list_inject_incr with j; eauto.
      * eapply list_expr_inj_se_not_dep; eauto.
        apply expr_list_inject_incr with j; eauto.
      * eexact C.
      * eexact D.
      * exact IWB'. 
      * intros.
        etransitivity.
        Focus 2.
        apply (create_undef_temps_permut _ _ (add_lifted_permut _ _ _ _ _
                                                                (varsort_permut _)
                                                                (Permutation.Permutation_refl _))).
        erewrite add_lifted_set_eq.
        apply (create_undef_temps_lifted _ _ H).
        rewrite cenv_for_cenv_for_gen_eq. red. tauto.

      * (* intros. trim H. *)
        intros; destruct (create_undef_temps (fn_temps f))!id as [v|] eqn:?; auto.
        exploit create_undef_temps_inv; eauto. intros [P Q]. elim (l id id); auto. 
      * intros [tel [tm1 [P [Q [R [S [T [U [V [W W']]]]]]]]]]. 
        change (cenv_for_gen (addr_taken_stmt (fn_body f)) (fn_params f ++ fn_vars f))
          with (cenv_for f) in *.
        generalize (vars_and_temps_properties (cenv_for f) (fn_params f) (fn_vars f) (fn_temps f)).
        intros [X [Y Z]]. auto. auto.
        econstructor; split. 
        {
          eapply plus_left.
          eapply step_internal_function. 
          econstructor . exact Y. exact X. exact Z.
          - simpl. rewrite sort_remove_lifted.
            erewrite remove_lifted_eq.
            eexact A.
            apply cenv_for_cenv_for_gen_eq.
          - simpl. eexact Q.
          - simpl. eauto. 
          - simpl. erewrite store_params_ext. repeat rewrite app_nil_r in *.
            eexact P.
            apply cenv_for_cenv_for_gen_eq.
          - traceEq.
        }
        {
          econstructor. eauto.
          - eapply iwb_inv. eauto.
            intros; eapply bp_bounds; eauto.
            intros; symmetry; eapply U.

            intros; symmetry; eapply bind_parameters_mask; eauto.
            intros; symmetry; apply V.
            rewrite T; intros; xomega.
          - rewrite EQ. f_equal. f_equal. apply store_params_ext. apply cenv_for_cenv_for_gen_eq.
          - eauto.
          - eapply match_envs_cenv_ext.
            symmetry; apply cenv_for_cenv_for_gen_eq.
            eauto.
          - simpl.





            rewrite  (alloc_variables_lengths'
                        _ _ _ _ _ _ _ _ (cenv_bound_for_gen _  LNR _ )
                        H1 A LNR).  
            exploit ns1_spec; eauto. lia.
            
          -
            eapply match_cont_invariant; eauto. 
            + intros b chunk v JB PLT LOAD.
              transitivity (Mem.load chunk m2 b 0).
              eapply bind_parameters_load; eauto.
              * intros. 
                exploit alloc_variables_range. eexact H1. eauto. 
                unfold empty_env. rewrite PTree.gempty. intros [?|?]. congruence. 
              red; intros; subst b'. xomega. 
            * transitivity (Mem.load chunk m0 b 0).
              eapply alloc_bytes_load; eauto.
              generalize ( alloc_variables_nextblock _ _ _ _ _ H1).
              clear - PLT. xomega.
              eapply alloc_variables_load; eauto.
          +
            intros.
            erewrite (av_bounds _ _ _ _ _ H1); eauto.
            erewrite (MemReserve.reserve_bounds_of_block _ _ _ _ H3).
            eapply bp_bounds; eauto.
          + intros. rewrite U.
            erewrite (av_bounds _ _ _ _ _ A); eauto.
            erewrite (MemReserve.reserve_bounds_of_block _ _ _ _ B). auto.
          + eapply Mem.mi_inj_dynamic; eauto.
          + intros.
            rewrite (alloc_variables_dynamic _ _ _ _ _ H1).
            rewrite (MemReserve.reserve_is_dynamic_block _ _ _ _ H3).
            rewrite (bind_parameters_dynamic _ _ _ _ _ H4). tauto.
          + intros.
            rewrite (alloc_variables_dynamic _ _ _ _ _ A).
            rewrite (MemReserve.reserve_is_dynamic_block _ _ _ _ B).
            apply W. 
        -
          rewrite match_size_mem_rew. simpl.
          repSplit.
          +
            rewrite (Mem.nb_boxes_used_same tm1 m3').
            rewrite (Mem.nb_boxes_used_same m1 m2).
            rewrite <- (reserve_nb_boxes_used_m _ _ _ B).
            rewrite <- (reserve_nb_boxes_used_m _ _ _ H3).

            rewrite (alloc_variables_size_mem _ _ _ _ _ H1).
            rewrite (alloc_variables_size_mem _ _ _ _ _ A).
            cut (
                fold_left (fun (acc : nat) (it : ident * type) => acc + Mem.box_span (sizeof (snd it)))
                          (remove_lifted (cenv_for_gen (addr_taken_stmt (fn_body f)) (varsort (fn_params f ++ fn_vars f)))
                                         (varsort (fn_params f ++ fn_vars f))) 0 + 
                ns2 (fn_id f) <=
                fold_left (fun (acc : nat) (it : ident * type) => acc + Mem.box_span (sizeof (snd it))) (varsort (fn_params f ++ fn_vars f)) 0 +
                ns1 (fn_id f))%nat.
            generalize (Mem.mi_size_mem _ _ _ _ _ (Mem.mi_inj _ _ _ _ _ MINJ)). clear. intuition lia.
            setoid_rewrite  <- (fold_left_map (fun acc elt => (acc + elt)%nat)
                                             (fun elt => Mem.box_span (sizeof (snd elt)))).
            erewrite (Mem.fold_left_plus_permut (map _ (varsort _))).
            2: apply Permutation_map.


2: symmetry; apply filter_app_permut.
unfold remove_lifted.
instantiate (1:= fun idty => (VSet.mem (fst idty) (cenv_for_gen (addr_taken_stmt (fn_body f)) (varsort (fn_params f ++ fn_vars f))))).
rewrite map_app.

rewrite fold_left_app.
rewrite (Mem.fold_left_plus_rew _ (fold_left _ _ _)).

cut    (    ns2 (fn_id f) <=
    fold_left Peano.plus
      (map (fun elt : ident * type => Mem.box_span (sizeof (snd elt)))
         (filter
            (fun idty : ident * type =>
             VSet.mem (fst idty) (cenv_for_gen (addr_taken_stmt (fn_body f)) (varsort (fn_params f ++ fn_vars f))))
            (varsort (fn_params f ++ fn_vars f)))) 0 + 
    ns1 (fn_id f))%nat.
rewrite ! (fold_left_ext Peano.plus (fun acc elt => acc + elt)%nat).

assert (forall a b c n m, n = m ->
                     a <= b + c ->
                     n + a <= m + b + c)%nat.
{
  clear. intros. subst. lia.
}
apply H. apply fold_left_ext. auto. auto.
exploit ns1_spec. eauto.

rewrite fold_left_plus_length. rewrite list_length_map. unfold VSet.elt. unfold ident. lia. 

rewrite Forall_forall.
intros x IN.
rewrite in_map_iff in IN. dex; des IN.
rewrite filter_In in i. des i.
des x1. exploit cenv_for_gen_by_value. apply i0. 2: apply VSet.mem_2; apply e0.
eapply permutation_norepet. 2: apply H0.
unfold var_names. rewrite <- map_app. apply Permutation_map. apply sort_permut.
intro; dex. apply box_span_small. clear - H.
generalize (two_p_monotone 3 (Z.of_nat MA)). intro A. trim A.
generalize MA_bound. lia.
rewrite two_power_nat_two_p.
cut (0 < sizeof t <= two_p 3). lia. change (two_p 3) with 8.
eapply access_mode_value_s8. eauto.

clear - H4. unfold Mem.mk_block_list.
rewrite (bind_parameters_nextblock _ _ _ _ _ H4).
apply mk_block_list_aux_ext. intros; rewrite <- ! Mem.size_block_snd; symmetry; erewrite bp_bounds; eauto.

symmetry; eapply bind_parameters_nb_extra; eauto.


unfold Mem.mk_block_list.
rewrite T. apply mk_block_list_aux_ext. intros; rewrite <- ! Mem.size_block_snd. rewrite U. reflexivity.
apply W'.

+



replace (nb_boxes_static tm1) with (nb_boxes_static m3').



rewrite <- (reserve_boxes_nb_static _ _ _ B).
erewrite alloc_variables_size_env. 2: eauto. lia.

unfold remove_lifted. erewrite filter_map. 
apply filter_norepet.
eapply permutation_norepet.
apply Permutation_map.
apply sort_permut.
unfold var_names in H0. rewrite map_app. apply H0.

instantiate (1 := fun a => negb (VSet.mem a ((cenv_for_gen (addr_taken_stmt (fn_body f)) (varsort (fn_params f ++ fn_vars f)))))).
simpl. reflexivity.

unfold nb_boxes_static.
f_equal.

unfold Mem.mk_block_list.
rewrite T. erewrite filter_ext.
erewrite mk_block_list_aux_ext. reflexivity.
intros; rewrite <- ! Mem.size_block_snd. rewrite U. reflexivity.

intros.
generalize (W (fst x)). unfold is_static_block_b, Mem.is_dynamic_block.
repeat destr.

+ 
  rewrite W'.

erewrite <- reserve_boxes_nb_extra; eauto. lia.

+
  
  rewrite <- (bp_boxes_static _ _ _ _ _ H4).
  rewrite <- (reserve_boxes_nb_static _ _ _ H3).
  erewrite alloc_variables_size_env. 2: eauto. lia.
  eapply permutation_norepet.
  apply Permutation_map.
  apply sort_permut.
  unfold var_names in H0. rewrite map_app. apply H0.
+ rewrite <- (bind_parameters_nb_extra _ _ _ _ _ H4).
  erewrite <- reserve_boxes_nb_extra; eauto. lia.
+ intros.

  eapply match_size_mem_same_size. apply MSM.

  rewrite H. rewrite <- (bp_boxes_static _ _ _ _ _ H4).
  rewrite <- (reserve_boxes_nb_static _ _ _ H3).
  erewrite (alloc_variables_size_env _ _ _ _ H1). lia.
  eapply permutation_norepet.
  apply Permutation_map.
  apply sort_permut.
  unfold var_names in H0. rewrite map_app. apply H0.


  rewrite H2. replace (nb_boxes_static tm1) with (nb_boxes_static m3').
  rewrite <- (reserve_boxes_nb_static _ _ _ B).
  erewrite (alloc_variables_size_env _ _ _ _ A). lia.

  unfold remove_lifted. erewrite filter_map. 
apply filter_norepet.
eapply permutation_norepet.
apply Permutation_map.
apply sort_permut.
unfold var_names in H0. rewrite map_app. apply H0.

instantiate (1 := fun a => negb (VSet.mem a ((cenv_for_gen (addr_taken_stmt (fn_body f)) (varsort (fn_params f ++ fn_vars f)))))).
simpl. reflexivity.

unfold nb_boxes_static.
f_equal.

unfold Mem.mk_block_list.
rewrite T. erewrite filter_ext.
erewrite mk_block_list_aux_ext. reflexivity.
intros; rewrite <- ! Mem.size_block_snd. rewrite U. reflexivity.

intros.
generalize (W (fst x)). unfold is_static_block_b, Mem.is_dynamic_block.
repeat destr.

instantiate (1 := C0). instantiate (1 := C'). rewrite H7.



rewrite (alloc_variables_nb_dynamic _ _ _ _ _ H1).
rewrite (reserve_boxes_nb_dynamic _ _ _ H3).
rewrite (bp_boxes_dynamic _ _ _ _ _ H4). lia.

rewrite H8. rewrite (alloc_variables_nb_dynamic _ _ _ _ _ A).
rewrite (reserve_boxes_nb_dynamic _ _ _ B).
unfold nb_boxes_dynamic.
f_equal.
f_equal.

unfold Mem.mk_block_list.
rewrite T. erewrite filter_ext.
erewrite mk_block_list_aux_ext. reflexivity.
intros; rewrite <- ! Mem.size_block_snd. rewrite U. reflexivity.

intros.
generalize (W (fst x)). unfold is_dynamic_block_b, Mem.is_dynamic_block.
repeat destr.



rewrite H5.
rewrite <- (bind_parameters_nb_extra _ _ _ _ _ H4).
erewrite <- (reserve_boxes_nb_extra _ _ _ H3); eauto.
rewrite (alloc_variables_nb_extra _ _ _ _ _ H1). lia.

rewrite H6. rewrite W'.
erewrite <- (reserve_boxes_nb_extra _ _ _ B); eauto.
rewrite (alloc_variables_nb_extra _ _ _ _ _ A). lia.

        - eauto.
               
        - apply compat_cenv_for. 
        - rewrite (bind_parameters_nextblock _ _ _ _ _ H4). xomega.
        - rewrite T; xomega.
        - eauto.
      }
      
  - (* external function *)
    monadInv TRFD. inv FUNTY. 
    exploit external_call_mem_inject_forget; eauto. apply match_globalenvs_preserves_globals. 
    eapply match_cont_globalenv. eexact (MCONT VSet.empty). 
    eapply list_expr_inj_se_not_dep; eauto.
    intros [f' [tvres [tm' [EC' [IWB' [EI [MINJ' [UNCH1 [UNCH2 [INCR [SEP [SZmem
      [ST [ST' [EXT EXT']]]]]]]]]]]]]]].
    econstructor; split.
    + apply plus_one. econstructor; eauto. eapply external_call_symbols_preserved; eauto. 
      exact symbols_preserved. exact varinfo_preserved.
    + econstructor; eauto.
      intros. apply match_cont_incr_bounds with (Mem.nextblock m) (Mem.nextblock tm).
      * eapply match_cont_extcall; eauto.
        intros. symmetry; eapply extcall_bounds; eauto. 
        intros. symmetry; eapply extcall_bounds; eauto. xomega. xomega.
        intros. 
        eapply Mem.mi_inj_dynamic; eauto.
        intros; eapply external_call_dyn; eauto. 
        intros; eapply external_call_dyn; eauto.
      * eapply external_call_nextblock; eauto.
      * eapply external_call_nextblock; eauto.
      *
        dex. des SZmem.
        cut (nb_boxes_dynamic m' + C = nb_boxes_dynamic m + C' /\
             nb_boxes_dynamic tm' + C = nb_boxes_dynamic tm + C')%nat.
        intros (DYN & tDYN).
        eapply match_size_mem_same_size. eauto. auto. auto.
        eauto. eauto. auto. auto.
        revert e0 e. rewrite ! nb_boxes_sep.
        rewrite ST, ST', EXT, EXT'. lia.

  - (* return *) 
    specialize (MCONT (cenv_for f)).  inv MCONT. 
    econstructor; split.
    apply plus_one. econstructor. 
    econstructor; eauto with compat.
    eapply match_envs_set_opttemp; eauto.
Qed.

Lemma iwb_flat:
  forall m,
    inj_well_behaved (Mem.flat_inj (Mem.nextblock m)) m m.
Proof.
  unfold Mem.flat_inj.
  intros.
  constructor.
  - red; intros. destr_in H; inv H; auto.
  - red. intros. destr_in H; inv H; auto.
    unfold Mem.size_block, get_size.
    exploit Mem.msk_valid. apply n. intro.
    erewrite Mem.bounds_mask_consistency; auto. unfold Mem.mask. rewrite H.  lia.
  - intros b b' delta H. destr_in H.
  - intros b b' delta H. destr_in H.
  - intros b' H. exists b', 0. destr.
  - intros b1 b2 b' delta1 delta2 H H0.
    destr_in H; destr_in H0.
Qed.

Lemma initial_states_simulation:
  forall sg S, initial_state prog sg S ->
  exists R, initial_state tprog sg R /\ match_states S R.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros [tf [A B]]. 
  econstructor; split.
  econstructor. eauto.
  eapply Genv.init_mem_transf_partial; eauto.
  intros a b0 TR'; inv TR'.
  unfold fid.
  des a; monadInv H4; auto.
  unfold transf_function in EQ. monadInv EQ.
  simpl. auto.
  
  rewrite (transform_partial_program_main _ _ TRANSF).
  instantiate (1 := b). rewrite <- H1. apply symbols_preserved.
  eauto.
  rewrite <- H3; apply type_of_fundef_preserved; auto.
  econstructor; eauto.
  eapply iwb_flat.
  intros. 
  econstructor. instantiate (1 := Mem.nextblock m0). 
  constructor; intros. 
  unfold Mem.flat_inj. apply pred_dec_true; auto. 
  unfold Mem.flat_inj in H. destruct (plt b1 (Mem.nextblock m0)); inv H. auto.
  eapply Genv.find_symbol_not_fresh; eauto.
  eapply Genv.find_funct_ptr_not_fresh; eauto.
  eapply Genv.find_var_info_not_fresh; eauto.
  xomega. xomega.
  simpl. split; auto. 
  eapply Genv.initmem_inject; eauto.
  constructor.
  constructor.
  exploit (Genv.find_funct_ptr_inversion prog); eauto.
  intro; dex; destr. 
  rewrite in_map_iff; eexists; split; simpl; eauto. reflexivity.
Qed.

Lemma final_states_simulation:
  forall S R r,
  match_states S R -> final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H.
  specialize (MCONT VSet.empty). inv MCONT. 
  constructor.
  generalize (forget_norm _ _ wf_inj_expr_inj_se _ _ _ MINJ IWB
                          _ _ RINJ).
  intro A; trim A.
  eapply expr_inj_se_not_dep; eauto.
  rewrite H1 in A. inv A; auto.
Qed.

Theorem transf_program_correct:
  forall sg, forward_simulation (semantics1 prog ns1 sg) (semantics2 tprog ns2 sg).
Proof.
  intros.
  eapply forward_simulation_plus.
  eexact symbols_preserved.
  intros. eapply initial_states_simulation; eauto.
  eexact final_states_simulation.
  intros. exploit step_simulation; eauto.
  destr.
Qed.

End PRESERVATION.
