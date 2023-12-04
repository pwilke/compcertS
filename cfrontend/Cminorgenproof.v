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

(** Correctness proof for Cminor generation. *)
Require Import Coq.Program.Equality.
Require Import FSets.
Require Import Permutation.
Require Import Coqlib.
Require Intv.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import NormaliseSpec.
Require Import ExprEval.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Switch.
Require Import Csharpminor.
Require Import Cminor.
Require Import Cminorgen.
Require Import Values_symbolictype.
Require Import Values_symbolic.
Require Import Normalise.
Require Import IntFacts.
Require Import Psatz.
Require Import VarSort Align MemReserve.
Open Local Scope error_monad_scope.

Section TRANSLATION.

Variable prog: Csharpminor.program.
Variable tprog: program.
Hypothesis TRANSL: transl_program prog = OK tprog.
Let ge : Csharpminor.genv := Genv.globalenv prog.
Let tge: genv := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf_partial transl_fundef _ TRANSL).

Lemma function_ptr_translated:
  forall (b: block) (f: Csharpminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial transl_fundef _ TRANSL).

Lemma functions_translated:
  forall m (v: expr_sym) (f: Csharpminor.fundef),
  Genv.find_funct m ge v = Some f ->
  exists tf,
  Genv.find_funct m tge v = Some tf /\ transl_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial transl_fundef _ TRANSL).

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof (Genv.find_var_info_transf_partial transl_fundef _ TRANSL).

Lemma sig_preserved_body:
  forall f tf cenv size spos,
  transl_funbody cenv size spos f = OK tf -> 
  tf.(fn_sig) = Csharpminor.fn_sig f.
Proof.
  intros. unfold transl_funbody in H. monadInv H; reflexivity.
Qed.

Lemma sig_preserved:
  forall f tf,
  transl_fundef f = OK tf -> 
  Cminor.funsig tf = Csharpminor.funsig f.
Proof.
  intros until tf; destruct f; simpl.
  unfold transl_function. (* destruct (build_compilenv f). *)
  destr; simpl bind; try congruence.
  intros. monadInv H. simpl. eapply sig_preserved_body; eauto. 
  intro. inv H. reflexivity.
Qed.

(** * Derived properties of memory operations *)

(** * Correspondence between C#minor's and Cminor's environments and memory states *)

(** In C#minor, every variable is stored in a separate memory block.
  In the corresponding Cminor code, these variables become sub-blocks
  of the stack data block.  We capture these changes in memory via a
  memory injection [f]: 
  [f b = Some(b', ofs)] means that C#minor block [b] corresponds
  to a sub-block of Cminor block [b] at offset [ofs].

  A memory injection [f] defines a relation [val_inject f] between
  values and a relation [Mem.inject f] between memory states.  These
  relations will be used intensively in our proof of simulation
  between C#minor and Cminor executions. *)

(** ** Matching between Cshaprminor's temporaries and Cminor's variables *)

Definition match_temps (f: meminj) (le: Csharpminor.temp_env) (te: env) : Prop :=
  forall id v, le!id = Some v -> exists v', te!(id) = Some v' /\ expr_inj_se f v v'.

Lemma match_temps_invariant:
  forall f f' le te,
  match_temps f le te ->
  inject_incr f f' ->
  match_temps f' le te.
Proof.
  intros; red; intros. destruct (H _ _ H1) as [v' [A B]]. exists v'; split; eauto.
  destruct (wf_inj_expr_inj_se). eauto.
Qed.

Lemma match_temps_assign:
  forall f le te id v tv,
  match_temps f le te ->
  expr_inj_se f v tv ->
  match_temps f (PTree.set id v le) (PTree.set id tv te).
Proof.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
  inv H1. exists tv; auto. 
  auto.
Qed.

(** ** Matching between C#minor's variable environment and Cminor's stack pointer *)

Inductive match_var (f: meminj) (sp: block): option (block * Z) -> option Z -> Prop :=
  | match_var_local: forall b sz ofs,
      expr_inj_se f (Eval (Vptr b Int.zero)) (Eval (Vptr sp (Int.repr ofs))) ->
      match_var f sp (Some(b, sz)) (Some ofs)
  | match_var_global:
      match_var f sp None None.

(** Matching between a C#minor environment [e] and a Cminor
  stack pointer [sp]. The [lo] and [hi] parameters delimit the range
  of addresses for the blocks referenced from [te]. *)

Record match_env (f: meminj) (cenv: compilenv)
                 (e: Csharpminor.env) (sp: block)
                 (lo hi: block) : Prop :=
  mk_match_env {

(** C#minor local variables match sub-blocks of the Cminor stack data block. *)
    me_vars:
      forall id, match_var f sp (e!id) (cenv!id);

(** [lo, hi] is a proper interval. *)
    me_low_high:
      Ple lo hi;

(** Every block appearing in the C#minor environment [e] must be
  in the range [lo, hi]. *)
    me_bounded:
      forall id b sz, PTree.get id e = Some(b, sz) -> Ple lo b /\ Plt b hi;

(** All blocks mapped to sub-blocks of the Cminor stack data must be
    images of variables from the C#minor environment [e] *)
    me_inv:
      forall b delta,
      f b = Some(sp, delta) ->
      exists id, exists sz, PTree.get id e = Some(b, sz);

(** All C#minor blocks below [lo] (i.e. allocated before the blocks
  referenced from [e]) must map to blocks that are below [sp]
  (i.e. allocated before the stack data for the current Cminor function). *)
    me_incr:
      forall b tb delta,
      f b = Some(tb, delta) -> Plt b lo -> Plt tb sp
  }.

Ltac geninv x := 
  let H := fresh in (generalize x; intro H; inv H).

Lemma match_env_invariant:
  forall f1 cenv e sp lo hi f2,
  match_env f1 cenv e sp lo hi ->
  inject_incr f1 f2 ->
  (forall b delta, f2 b = Some(sp, delta) -> f1 b = Some(sp, delta)) ->
  (forall b, Plt b lo -> f2 b = f1 b) ->
  match_env f2 cenv e sp lo hi.
Proof.
  intros. destruct H. constructor; auto.
  - (* vars *)
    intros. geninv (me_vars0 id); econstructor; eauto.
    destruct (wf_inj_expr_inj_se). eauto.
  - (* bounded *)
    intros. eauto. 
  - (* below *)
    intros. rewrite H2 in H; eauto.
Qed.

(** [match_env] and external calls *)

Remark inject_incr_separated_same:
  forall f1 f2 m1 m1',
  inject_incr f1 f2 -> inject_separated f1 f2 m1 m1' ->
  forall b, Mem.valid_block m1 b -> f2 b = f1 b.
Proof.
  intros. case_eq (f1 b).
  intros [b' delta] EQ. apply H; auto. 
  intros EQ. case_eq (f2 b).
  intros [b'1 delta1] EQ1. exploit H0; eauto. intros [C D]. contradiction.
  auto.
Qed.

Remark inject_incr_separated_same':
  forall f1 f2 m1 m1',
  inject_incr f1 f2 -> inject_separated f1 f2 m1 m1' ->
  forall b b' delta,
  f2 b = Some(b', delta) -> Mem.valid_block m1' b' -> f1 b = Some(b', delta).
Proof.
  intros. case_eq (f1 b).
  intros [b'1 delta1] EQ. exploit H; eauto. congruence.
  intros. exploit H0; eauto. intros [C D]. contradiction.
Qed.

Lemma match_env_external_call:
  forall f1 cenv e sp lo hi f2 m1 m1',
  match_env f1 cenv e sp lo hi ->
  inject_incr f1 f2 ->
  inject_separated f1 f2 m1 m1' ->
  Ple hi (Mem.nextblock m1) -> Plt sp (Mem.nextblock m1') ->
  match_env f2 cenv e sp lo hi.
Proof.
  intros. apply match_env_invariant with f1; auto.
  intros. eapply inject_incr_separated_same'; eauto.
  intros. eapply inject_incr_separated_same; eauto. red. destruct H. xomega. 
Qed.

(** [match_env] and allocations *)

(** The sizes of blocks appearing in [e] are respected. *)

Definition match_bounds (e: Csharpminor.env) (m: mem) : Prop :=
  forall id b sz ofs p,
  PTree.get id e = Some(b, sz) -> Mem.perm m b ofs Max p -> 0 <= ofs < sz.

Definition match_bounds' (e: Csharpminor.env) (m: mem) : Prop :=
  forall id b sz,
  PTree.get id e = Some(b, sz) -> 
  Mem.bounds_of_block m b = (0,sz).

Lemma match_bounds_invariant:
  forall e m1 m2,
  match_bounds e m1 ->
  (forall id b sz ofs p,
   PTree.get id e = Some(b, sz) -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  match_bounds e m2.
Proof.
  intros; red; intros. eapply H; eauto. 
Qed.

Lemma match_bounds'_invariant:
  forall e m1 m2,
  match_bounds' e m1 ->
  (forall id b sz,
   PTree.get id e = Some(b, sz) -> Mem.bounds_of_block m1 b = Mem.bounds_of_block m2 b) ->
  match_bounds' e m2.
Proof.
  intros; red; intros. erewrite <- H0; eauto. 
Qed.


(** ** Permissions on the Cminor stack block *)

(** The parts of the Cminor stack data block that are not images of
    C#minor local variable blocks remain freeable at all times. *)

Inductive is_reachable_from_env (f: meminj) (e: Csharpminor.env) (sp: block) (ofs: Z) : Prop :=
  | is_reachable_intro: forall id b sz delta,
      e!id = Some(b, sz) ->
      f b = Some(sp, delta) ->
      delta <= ofs < delta + sz ->
      is_reachable_from_env f e sp ofs.

Definition padding_freeable (f: meminj) (e: Csharpminor.env) (tm: mem) (sp: block) (sz: Z) : Prop :=
  forall ofs, 
  0 <= ofs < sz -> Mem.perm tm sp ofs Cur Freeable \/ is_reachable_from_env f e sp ofs.

Lemma padding_freeable_invariant:
  forall f1 e tm1 sp sz cenv lo hi f2 tm2,
  padding_freeable f1 e tm1 sp sz ->
  match_env f1 cenv e sp lo hi ->
  (forall ofs, Mem.perm tm1 sp ofs Cur Freeable -> Mem.perm tm2 sp ofs Cur Freeable) ->
  (forall b, Plt b hi -> f2 b = f1 b) ->
  padding_freeable f2 e tm2 sp sz.
Proof.
  intros; red; intros.
  exploit H; eauto. intros [A | A].
  left; auto.
  right. inv A. exploit me_bounded; eauto. intros [D E].
  econstructor; eauto. rewrite H2; auto. 
Qed.

(** Decidability of the [is_reachable_from_env] predicate. *)

Lemma is_reachable_from_env_dec:
  forall f e sp ofs, is_reachable_from_env f e sp ofs \/ ~is_reachable_from_env f e sp ofs.
Proof.
  intros. 
  set (pred := fun id_b_sz : ident * (block * Z) =>
                 match id_b_sz with
                 | (id, (b, sz)) =>
                      match f b with
                           | None => false
                           | Some(sp', delta) =>
                               if eq_block sp sp'
                               then zle delta ofs && zlt ofs (delta + sz)
                               else false
                      end
                 end).
  destruct (List.existsb pred (PTree.elements e)) eqn:?.
  (* yes *)
  rewrite List.existsb_exists in Heqb. 
  destruct Heqb as [[id [b sz]] [A B]].
  simpl in B. destruct (f b) as [[sp' delta] |] eqn:?; try discriminate.
  destruct (eq_block sp sp'); try discriminate.
  destruct (andb_prop _ _ B).
  left. apply is_reachable_intro with id b sz delta.
  apply PTree.elements_complete; auto. 
  congruence.
  split; eapply proj_sumbool_true; eauto.
  (* no *)
  right; red; intro NE; inv NE. 
  assert (existsb pred (PTree.elements e) = true).
  rewrite List.existsb_exists. exists (id, (b, sz)); split.
  apply PTree.elements_correct; auto. 
  simpl. rewrite H0. rewrite dec_eq_true.
  unfold proj_sumbool. destruct H1. rewrite zle_true; auto. rewrite zlt_true; auto. 
  congruence.
Qed.

(** * Correspondence between global environments *)

(** Global environments match if the memory injection [f] leaves unchanged
  the references to global symbols and functions. *)

Inductive match_globalenvs (f: meminj) (bound: block): Prop :=
  | mk_match_globalenvs
      (DOMAIN: forall b, Plt b bound -> f b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, f b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).

Remark inj_preserves_globals:
  forall f hi,
  match_globalenvs f hi ->
  meminj_preserves_globals ge f.
Proof.
  intros. inv H.
  split. intros. apply DOMAIN. eapply SYMBOLS. eauto.
  split. intros. apply DOMAIN. eapply VARINFOS. eauto. 
  intros. symmetry. eapply IMAGE; eauto. 
Qed.

(** * Invariant on abstract call stacks  *)

(** Call stacks represent abstractly the execution state of the current
  C#minor and Cminor functions, as well as the states of the
  calling functions.  A call stack is a list of frames, each frame
  collecting information on the current execution state of a C#minor
  function and its Cminor translation. *)

Inductive frame : Type :=
  Frame(cenv: compilenv)
       (tf: Cminor.function)
       (e: Csharpminor.env)
       (le: Csharpminor.temp_env)
       (te: Cminor.env)
       (sp: block)
       (lo hi: block).

Definition callstack : Type := list frame.

(** Matching of call stacks imply:
- matching of environments for each of the frames
- matching of the global environments
- separation conditions over the memory blocks allocated for C#minor local variables;
- separation conditions over the memory blocks allocated for Cminor stack data;
- freeable permissions on the parts of the Cminor stack data blocks
  that are not images of C#minor local variable blocks.
*)



Definition norepet_env e :=
  list_norepet (map fst (map fst (blocks_of_env e))).

Definition small_var_space (vars: list (ident*Z)) start :=
  fold_right (fun y x =>
                align x (block_alignment (snd y)) + Z.max 0 (snd y))
             start vars.



Lemma align_plus:
  forall z sz,
    align (align z (block_alignment sz)) (two_power_nat MA) = align z (two_power_nat MA).
Proof.
  intros.
  eapply align_le_two_p.
  apply Genv.aos_ma.
Qed.


Lemma fr_align_pos:
  forall vars z,
    z >= 0 ->
    small_var_space vars z >= z.
Proof.
  induction vars; simpl; intros.
  omega.
  apply Zle_ge.
  transitivity (small_var_space vars z); auto.
  specialize (IHvars _ H). omega.
  refine (Zle_trans _ _ _ (align_le _ _ (block_alignment_pos (snd a))) _).
  generalize (Zmax_bound_l 0 0 (snd a)). omega.
Qed.

Definition big_var_space (vars: list (ident*Z)) start :=
  fold_right (fun y x =>
                align x (two_power_nat MA) + Z.max 0 (snd y))
             start vars.

Lemma fr_align_pos8:
  forall vars z,
    z >= 0 ->
    big_var_space vars z >= z.
Proof.
  induction vars; simpl; intros.
  omega.
  specialize (IHvars _ H).
  generalize (align_le (big_var_space vars z) (two_power_nat MA))
             (Zmax_bound_l 0 0 (snd a)).
  generalize (two_power_nat_pos MA); lia. 
Qed.

Lemma sp_le_vars_right:
  forall vars ,
    small_var_space vars 0 <=
    big_var_space vars 0.
Proof.
  induction vars; simpl; intros. omega.
  apply Z.add_le_mono_r.
  transitivity (align (small_var_space vars 0) (two_power_nat MA)).
  rewrite <- align_plus with (sz:=snd a).
  apply align_le; auto. 
  apply align_add; auto.  
  generalize (fr_align_pos vars 0). lia. 
Qed.

Definition big_vars_block_space (vars: list (block*Z*Z)) start :=
  fold_right
    (fun (y : block * Z * Z) (x : Z) =>
       align x (two_power_nat MA) + Z.max 0 (snd y - snd (fst y))) start vars.

Definition small_vars_block_space (vars: list (block*Z*Z)) start :=
  fold_right
    (fun (y : block * Z * Z) (x : Z) =>
       align x (block_alignment (snd y - snd (fst y))) + Z.max 0 (snd y - snd (fst y))) start vars.

Lemma bvbs_rew:
  forall vars start,
    big_vars_block_space vars start =
    big_var_space (map (fun a => (fst (fst a), snd a - snd (fst a))) vars)
                 start.
Proof.
  induction vars; simpl; intros; 
  congruence.  
Qed.

Lemma svbs_rew:
  forall vars start,
    small_vars_block_space vars start =
    small_var_space (map (fun a => (fst (fst a), snd a - snd (fst a))) vars)
                 start.
Proof.
  induction vars; simpl; intros; 
  congruence.  
Qed.


Lemma fr_permut:
  forall l l' z,
    Permutation l l' ->
    align (big_vars_block_space l  z) (two_power_nat MA) =
    align (big_vars_block_space l' z) (two_power_nat MA).
Proof.
  induction 1; simpl; intros.
  - auto.
  - rewrite IHPermutation. auto.
  - rewrite <- ! Mem.align_distr; auto. omega.
  - congruence.
Qed.

Lemma fr_permut':
  forall (l l': list (ident*Z)) z,
    Permutation l l' ->
    align (big_var_space l  z) (two_power_nat MA) =
    align (big_var_space l' z) (two_power_nat MA).
Proof.
  induction 1; simpl; intros.
  - auto.
  - rewrite IHPermutation. auto.
  - rewrite <- ! Mem.align_distr; auto. lia. 
  - congruence.
Qed.

Lemma big_vars_block_space_left:
  forall vars z,
    align (fold_left
             (fun (x : Z) (y : block * Z * Z) =>
                align x (two_power_nat MA) + Z.max 0 (snd y - snd (fst y))) 
             vars z) (two_power_nat MA)
    = align (big_vars_block_space vars z) (two_power_nat MA) .
Proof.
  intros.
  rewrite <- fold_left_rev_right.
  rewrite (fr_permut _ _ _ (Permutation_rev _)).
  auto.
Qed.

Open Scope nat_scope.

Variable needed_stackspace: ident -> nat.

Inductive size_mem_preserved : list mem -> list mem -> callstack -> Prop :=
| smp_nil : forall m1 m2
              (smp_size_mem: Mem.nb_boxes_used_m m1 >= Mem.nb_boxes_used_m m2),
    size_mem_preserved (m1::nil) (m2::nil) nil
| smp_cons_same:
    forall m1 m2 lm1 lm2 cs
      (smp: size_mem_preserved (m1::lm1) (m2::lm2) cs)
      C C' m1' m2'
      (szineq: Mem.nb_boxes_used_m m2 <= Mem.nb_boxes_used_m m1)
      (szm1: Mem.nb_boxes_used_m m1' + C' = Mem.nb_boxes_used_m m1 + C)
      (szm2: Mem.nb_boxes_used_m m2' + C' = Mem.nb_boxes_used_m m2 + C)
      (smp_nb_extra1: Mem.nb_extra m1' = Mem.nb_extra m1)
      (smp_nb_extra2: Mem.nb_extra m2' = Mem.nb_extra m2),
      size_mem_preserved (m1'::m1::lm1) (m2'::m2::lm2) cs
| smp_cons:
    forall m1 m2 lm1 lm2 cs cenv tf e le te sp lo hi m1' m2'
      (smp_size_mem1: Mem.nb_boxes_used_m m1 = needed_stackspace (fn_id tf) +
                                               size_list_blocks (map size_of_block (blocks_of_env e)) +
                                               Mem.nb_boxes_used_m m1')
      (smp_size_mem2: Mem.nb_boxes_used_m m2 = needed_stackspace (fn_id tf) +
                                               Mem.box_span (fn_stackspace tf) +
                                               Mem.nb_boxes_used_m m2')
      (smp_size_mem: Mem.nb_boxes_used_m m1 >= Mem.nb_boxes_used_m m2)
      (smp_nb_extra1: Mem.nb_extra m1 = Mem.nb_extra m1' + needed_stackspace (fn_id tf))
      (smp_nb_extra2: Mem.nb_extra m2 = Mem.nb_extra m2' + needed_stackspace (fn_id tf))
      (smp_rec: size_mem_preserved (m1'::lm1) (m2'::lm2) cs),
      size_mem_preserved (m1::m1'::lm1) (m2::m2'::lm2)
                         (Frame cenv tf e le te sp lo hi::cs).

Open Scope Z_scope.


Inductive match_callstack (f: meminj) (m: mem) (tm: mem):
                          callstack -> block -> block -> Prop :=
  | mcs_nil:
      forall hi bound tbound,
      match_globalenvs f hi ->
      Mem.all_blocks_injected f m -> 
      Ple hi bound -> Ple hi tbound ->
      match_callstack f m tm nil bound tbound 
  | mcs_cons:
      forall cenv tf e le te sp lo hi cs bound tbound
        (BOUND: Ple hi bound)
        (TBOUND: Plt sp tbound)
        (MTMP: match_temps f le te)
        (MENV: match_env f cenv e sp lo hi)
        (BOUND: match_bounds e m)
        (BOUND': match_bounds' e m)
        (NRP: norepet_env e)
        (hi_pos: Forall (fun bnds : ident * Z * Z => snd bnds >= 0) (blocks_of_env e))
        (sz_stack: (Mem.box_span (fn_stackspace tf) <= size_list_blocks (map size_of_block (blocks_of_env e)))%nat)
        (ss_pos: fn_stackspace tf >= 0)
        (PERM: padding_freeable f e tm sp (fn_stackspace tf))
        (bnd_sp: Mem.bounds_of_block tm sp = (0, fn_stackspace tf))
        (ndyn_e: Forall (fun b => ~ Mem.is_dynamic_block m b) (map fst (map fst (blocks_of_env e))))
        (ndyn_sp: ~ Mem.is_dynamic_block tm sp)
        (MCS: match_callstack f m tm cs lo sp)
      ,
      match_callstack f m tm (Frame cenv tf e le te sp lo hi:: cs) bound tbound.

(** [match_callstack] implies [match_globalenvs]. *)

Lemma match_callstack_match_globalenvs:
  forall f m tm cs bound tbound,
  match_callstack f m tm cs bound tbound ->
  exists hi, match_globalenvs f hi.
Proof.
  induction 1; eauto.
Qed.
      
Lemma match_callstack_all_blocks_injected:
  forall f m tm cs mm sp,
    match_callstack f m tm cs mm sp ->
    Mem.all_blocks_injected f m.
Proof.
  induction 1; auto. 
Qed.


(** Invariance properties for [match_callstack]. *)

Lemma in_blocks_of_env:
  forall e id b sz,
  e!id = Some(b, sz) -> In (b, 0, sz) (blocks_of_env e).
Proof.
  unfold blocks_of_env; intros. 
  change (b, 0, sz) with (block_of_binding (id, (b, sz))).
  apply List.in_map. apply PTree.elements_correct. auto.
Qed.


Lemma in_blocks_of_env_map:
  forall e id b sz,
  e!id = Some(b, sz) -> In b (map fst (map fst (blocks_of_env e))).
Proof.
  intros.
  exploit in_blocks_of_env; eauto.
  rewrite map_map, in_map_iff; eexists; split; eauto. destr.
Qed.


Lemma in_blocks_of_env_inv:
  forall b lo hi e,
  In (b, lo, hi) (blocks_of_env e) ->
  exists id, e!id = Some(b, hi) /\ lo = 0.
Proof.
  unfold blocks_of_env; intros. 
  exploit list_in_map_inv; eauto. intros [[id [b' sz]] [A B]].
  unfold block_of_binding in A. inv A. 
  exists id; intuition. apply PTree.elements_complete. auto.
Qed.


Lemma match_callstack_invariant:
  forall f1 m1 tm1 f2 m2 tm2 cs bound tbound
         (MCS: match_callstack f1 m1 tm1 cs bound tbound)
         (INCR: inject_incr f1 f2)
         (PRM:forall b ofs p, Plt b bound -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) 
         (BND: forall b, Plt b bound -> ~Mem.is_dynamic_block m1 b ->
                    Mem.bounds_of_block m2 b = Mem.bounds_of_block m1 b) 
         (BND':forall b, Plt b tbound -> ~Mem.is_dynamic_block tm1 b ->
                    Mem.bounds_of_block tm2 b = Mem.bounds_of_block tm1 b) 
         (PRM':forall sp ofs, Plt sp tbound ->
                         ~Mem.is_dynamic_block tm1 sp ->
                         Mem.perm tm1 sp ofs Cur Freeable -> Mem.perm tm2 sp ofs Cur Freeable)
         (DYN: forall b, Plt b bound -> (Mem.is_dynamic_block m1 b <-> Mem.is_dynamic_block m2 b))
         (DYN': forall b, Plt b tbound -> (Mem.is_dynamic_block tm1 b <-> Mem.is_dynamic_block tm2 b))
         (Fsame:forall b, Plt b bound -> f2 b = f1 b) 
         (Fsame':forall b b' delta, f2 b = Some(b', delta) -> Plt b' tbound -> f1 b = Some(b', delta))
         (ABI: Mem.all_blocks_injected f2 m2),
  match_callstack f2 m2 tm2 cs bound tbound.
Proof.
  induction 1; intros.
  - (* base case *)
    apply (mcs_nil _ _ _ hi bound tbound); auto.
    + inv H.  constructor; intros; eauto.
      eapply IMAGE; eauto. eapply Fsame'; eauto. xomega.
  - (* inductive case *)
    assert (Ple lo hi) by (eapply me_low_high; eauto).
    econstructor; eauto.
    + eapply match_temps_invariant; eauto.
    + eapply match_env_invariant; eauto. 
      intros. apply Fsame. xomega.
    + eapply match_bounds_invariant; eauto.
      intros. eapply PRM; eauto.  
      exploit me_bounded; eauto. xomega. 
    + eapply match_bounds'_invariant; eauto.
      intros. erewrite <- BND; eauto.
      exploit me_bounded; eauto. xomega.
      rewrite Forall_forall in ndyn_e. apply ndyn_e.
      apply in_blocks_of_env_map in H0; auto.      
    + eapply padding_freeable_invariant; eauto. 
      intros. apply Fsame. xomega.
    + rewrite <- bnd_sp.
      apply BND'. xomega. destr.
    + revert ndyn_e. apply Mem.Forall_impl'.
      intros; rewrite <- DYN; eauto.
      Lemma in_blocks_of_env_inv':
        forall b e,
          In b (map fst (map fst (blocks_of_env e))) ->
          exists i t,
            e ! i = Some (b,t).
      Proof.
        intros b e IN.
        unfold blocks_of_env, block_of_binding in IN. rewrite ! map_map, in_map_iff in IN. dex; destr_and. des x.
        des p.
        exists i, z. apply PTree.elements_complete; auto.
      Qed.
      eapply in_blocks_of_env_inv' in H0; dex.
      exploit me_bounded; eauto. xomega.
    + rewrite  <-DYN'; eauto.
    + eapply IHMCS; eauto. 
      * intros. eapply PRM; eauto. xomega. 
      * intros. eapply BND; eauto. xomega. 
      * intros. eapply BND'; eauto. xomega.
      * intros. eapply PRM'; eauto. xomega.
      * intros; eapply DYN; eauto. xomega.
      * intros; eapply DYN'; eauto. xomega.
      * intros. eapply Fsame; eauto. xomega.
      * intros. eapply Fsame'; eauto. xomega.
Qed.

Lemma match_callstack_incr_bound:
  forall f m tm cs bound tbound bound' tbound',
  match_callstack f m tm cs bound tbound ->
  Ple bound bound' -> Ple tbound tbound' ->
  match_callstack f m tm cs bound' tbound'.
Proof.
  intros. inv H.
  econstructor; eauto. xomega. xomega.
  econstructor; auto. xomega. xomega.
Qed.

(** Assigning a temporary variable. *)

Lemma match_callstack_set_temp:
  forall f cenv e le te sp lo hi cs bound tbound m tm tf id v tv,
  expr_inj_se  f v tv ->
  match_callstack f m tm (Frame cenv tf e le te sp lo hi  :: cs) bound tbound ->
  match_callstack f m tm (Frame cenv tf e (PTree.set id v le) (PTree.set id tv te) sp lo hi :: cs) bound tbound.
Proof.
  intros. inv H0. econstructor; auto.
  eapply match_temps_assign; eauto. 
Qed.

(** Preservation of [match_callstack] by freeing all blocks allocated
  for local variables at function entry (on the C#minor side)
  and simultaneously freeing the Cminor stack data block. *)


Lemma assign_variable_cenv_indep:
  forall cenv cenv' z a c z0 c0 z1
    (AV1 : assign_variable (cenv, z) a = (c, z0))
    (AV2 : assign_variable (cenv', z) a = (c0, z1)),
    z0 = z1.
Proof.
  intros.
  destruct a; simpl in *. inv AV1; inv AV2. auto.
Qed.

Lemma assign_variables_cenv_indep:
  forall l cenv cenv' z,
    snd (assign_variables (cenv, z) l) =
    snd (assign_variables (cenv', z) l).
Proof.
  induction l; simpl; intros; eauto.
  destruct (assign_variable (cenv, z) a) eqn:?.
  destruct (assign_variable (cenv', z) a) eqn:?. 
  erewrite IHl. f_equal. f_equal. f_equal.
  eapply assign_variable_cenv_indep; eauto.
Qed.

Lemma alloc_variables_alloc_sp:
  forall fn tf,
    transl_function fn = OK tf ->
    fn_stackspace tf = small_var_space (rev (varsort' (Csharpminor.fn_vars fn))) 0.
Proof. 
  intros fn tf H0.
  unfold transl_function in H0.
  unfold build_compilenv in H0.
  revert H0; destr; try discriminate.
  unfold transl_funbody in H0. 
  destruct (transl_stmt _ nil (Csharpminor.fn_body fn));
  simpl in H0; try discriminate.
  inv H0. simpl.
  unfold small_var_space. rewrite fold_left_rev_right.
  generalize 0 at 1 3.
  generalize (varsort' (Csharpminor.fn_vars fn)).
  clear.
  induction l; simpl; auto.
  intros. rewrite <- IHl.
  destruct a. simpl; auto.
  apply assign_variables_cenv_indep.
Qed.


Lemma size_mem_blocks_big_vars:
  forall vars z,
    Mem.size_mem_blocks vars z = big_vars_block_space (rev vars) z.
Proof.
  unfold Mem.size_mem_blocks, big_vars_block_space. 
  intros. rewrite fold_left_rev_right. reflexivity.
Qed.

Lemma size_mem_preserved_inf:
  forall cs m1 tm1 m2 tm2,
    size_mem_preserved (m1::tm1) (m2::tm2) cs ->
    (Mem.nb_boxes_used_m m2 <= Mem.nb_boxes_used_m m1)%nat.
Proof.
  induction cs; simpl; intros; eauto.
  - inv H; lia.
  - inv H; lia. 
Qed.

Lemma smp_length:
  forall lm tlm cs,
    size_mem_preserved lm tlm cs ->
    length lm = length tlm.
Proof.
  induction 1; simpl; intros; eauto.
Qed.

Lemma smp_inf:
  forall lm m cs tm tlm cenv tf e le te lo hi sp 
    (SMP: size_mem_preserved (m::lm) (tm::tlm) (Frame cenv tf e le te lo hi sp  :: cs)),
    (Mem.nb_boxes_used_m tm + size_list_blocks (map size_of_block (blocks_of_env e)) <=
     Mem.nb_boxes_used_m m + Mem.box_span (fn_stackspace tf))%nat.
Proof.
  induction lm; simpl; intros; eauto.
  - inv SMP.
  - inv SMP.
    + specialize (IHlm _ _ _ _ _ _ _ _ _ _ _ _ smp). lia.
    + apply size_mem_preserved_inf in smp_rec. lia.
Qed.

Require Import Tactics.

Lemma freelist_free_size_mem:
  forall m m' tm tm' sp e tf
         (vars_norepet: list_norepet (map fst (map fst (blocks_of_env e))))       
         (exact_bounds: Forall
                          (fun bbnds : ident * Z * Z =>
                             Mem.bounds_of_block m (fst (fst bbnds)) =
                             (snd (fst bbnds), snd bbnds)) (blocks_of_env e))
         (FREELIST : Mem.free_list m (blocks_of_env e) = Some m')
         (SP_bnds : Mem.bounds_of_block tm sp = (0, (fn_stackspace tf) ))
         (FREE : Mem.free tm sp 0 ((fn_stackspace tf)) = Some tm')
         (ss_pos: fn_stackspace tf >= 0)
         (hi_pos: Forall (fun bnds: ident * Z * Z =>
                            snd bnds >= 0) (blocks_of_env e))
         lm tlm
         cenv le te lo hi sp cs
         (smp: size_mem_preserved (m::lm) (tm::tlm) (Frame cenv tf e le te lo hi sp :: cs)),
    (Mem.nb_boxes_used_m tm' <= Mem.nb_boxes_used_m  m')%nat.
Proof.
  intros. 
  generalize (free_nb_boxes_used _ _ _ _ _ FREE).
  generalize (free_list_nb_boxes_used _ _ _ FREELIST).
  apply smp_inf in smp. unfold size_list. lia.
Qed.

Require Import PP.PpsimplZ.

Lemma free_list_bounds_exact:
  forall bl m m' (FL: Mem.free_list m bl = Some m'),
    list_norepet (map fst (map fst bl)) ->
    Forall 
      (fun bbnds => Mem.bounds_of_block m (fst (fst bbnds)) =
                 (snd (fst bbnds), snd bbnds)) bl.
Proof.
  induction bl; simpl; intros; eauto.
  repeat destr_in FL.
  specialize (IHbl _ _ FL).
  inv H.
  trim IHbl; auto.
  constructor; auto.
  - simpl.
    eapply Mem.free_bounds_exact'; eauto.
  - revert IHbl; apply Mem.Forall_impl'. intros. des a. des p.
    rewrite <- H0.
    symmetry; eapply Mem.bounds_free; eauto.
    intro; subst; apply H2; rewrite map_map, in_map_iff; eexists; split; eauto. destr.    
Qed.

Lemma freelist_inject:
  forall f m tm e m' sp tf tm'
    (ABI: Mem.all_blocks_injected f m)
         (MI: Mem.inject true expr_inj_se f m tm)
         (nr: list_norepet (map fst (map fst (blocks_of_env e))))
         (* (exact_bounds: Forall *)
         (*                  (fun bbnds : ident * Z * Z => *)
         (*                     Mem.bounds_of_block m (fst (fst bbnds)) = (snd (fst bbnds), snd bbnds)) *)
         (*                  (blocks_of_env e)) *)
         (* (ss_eq:  (fn_stackspace tf) <= *)
         (*          align (big_vars_block_space (rev (blocks_of_env e)) 0) (two_power_nat MA) ) *)
         (ss_pos: fn_stackspace tf >= 0)
         (hi_pos: Forall (fun bnds : ident * Z * Z => snd bnds >= 0) (blocks_of_env e))
         (INJ_not_in_sp: forall b b' delta,
                           ~ In b (map (fun a => fst (fst a)) (blocks_of_env e)) ->
                           f b = Some (b',delta) ->
                           b' <> sp)
         (NOPERM: forall b, 
                    In b (map (fun a => fst (fst a)) (blocks_of_env e)) ->
                    forall k p ofs,
                      ~ Mem.perm m' b ofs k p) 
         (NOBOUND: forall b, 
                     In b (map (fun a => fst (fst a)) (blocks_of_env e)) ->
                     Mem.bounds_of_block m' b = (0,0))
         (FREELIST: Mem.free_list m (blocks_of_env e) = Some m')
         (NDYN: ~ Mem.is_dynamic_block tm sp)
         (NDYN': Forall (fun b => ~ Mem.is_dynamic_block m b) (map fst (map fst (blocks_of_env e))))
         (* (SP_bnds: Mem.bounds_of_block tm sp = (0,(fn_stackspace tf))) *)
         (FREE: Mem.free tm sp 0 ((fn_stackspace tf)) = Some tm')
         cenv le te lo hi sp cs lm tlm
         (smp: size_mem_preserved (m::lm) (tm::tlm) (Frame cenv tf e le te sp lo hi :: cs)),
    Mem.inject true expr_inj_se f m' tm'.
Proof.
  intros.
  inv MI.
  econstructor; eauto.
  - inv mi_inj.
    econstructor; eauto.
    + intros.
      destruct (in_dec peq b1 (map (fun a => fst (fst a)) (blocks_of_env e))).
      generalize (NOPERM _ i k p ofs). congruence.
      eapply Mem.perm_freelist in H0; eauto.
      eapply mi_perm in H0; eauto.
      generalize (INJ_not_in_sp _ _ _ n H).
      intro. eapply Mem.perm_free_1; eauto.
    + intros.
      destruct (in_dec peq b1 (map (fun a => fst (fst a)) (blocks_of_env e))).
      generalize (NOBOUND _ i). unfold Mem.in_bound_m in *.
      intro A; rewrite A in H0; unfold Mem.in_bound_m, in_bound in H0; simpl in H0; omega.
      unfold Mem.in_bound_m in *.
      erewrite Mem.bounds_freelist in H0; eauto.
      eapply mi_bounds in H0; eauto.
      generalize (INJ_not_in_sp _ _ _ n H).
      intro. erewrite Mem.bounds_free; eauto.
    + intros.
      erewrite <- (Mem.mask_free _ _ _ _ _ FREE); eauto.
      erewrite (Mem.freelist_mask _ _ _ _ FREELIST); eauto.
    + intros.
      destruct (in_dec peq b1 (map (fun a => fst (fst a)) (blocks_of_env e))).
      generalize (NOPERM _ i Cur Readable ofs). congruence.      
      generalize (INJ_not_in_sp _ _ _ n H). intro.
      erewrite <- Mem.contents_freelist with (m':=m'); eauto.
      erewrite <- Mem.contents_free with (m':=tm'); eauto.
      eapply Mem.perm_freelist in H0; eauto.
    + intros. eapply freelist_free_size_mem; eauto.
      eapply free_list_bounds_exact; eauto.
      eapply Mem.free_bounds_exact'; eauto.
  - intros.
    eapply Mem.freelist_valid in H; eauto.
  - intros.
    eapply Mem.valid_block_free_1; eauto.
  - red; intros.
    unfold Mem.in_bound_m in *.
    destruct (in_dec peq b1 (map (fun a => fst (fst a)) (blocks_of_env e))).
    + generalize (NOBOUND _ i). intro A; rewrite A in H2; unfold in_bound in H2; simpl in H2; omega.
    + destruct (in_dec peq b2 (map (fun a => fst (fst a)) (blocks_of_env e))).
      generalize (NOBOUND _ i). intro A; rewrite A in H3; unfold in_bound in H3; simpl in H3; omega.
      erewrite Mem.bounds_freelist in H2; eauto.
      erewrite Mem.bounds_freelist in H3; eauto.
  - intros.
    specialize (mi_inj_dynamic _ _ _ H).
    rewrite (Mem.is_block_dynamic_free _ _ _ _ _ _ FREE),
    (Mem.is_block_dynamic_freelist _ _ _ _ FREELIST). Coqlib.destr. 
    rewrite (Mem.bounds_free _ _ _ _ _ _ FREE). 2: destr.
    rewrite (Mem.bounds_freelist _ _ _ _ FREELIST). auto.
    intro IN. 
    rewrite map_map, Forall_forall in NDYN'; apply NDYN' in IN; destr.
Qed.

Lemma match_callstack_freelist_aux:
  forall f cenv tf e le te sp lo hi cs m m' tm
         (NOBOUND: forall b, 
                     In b (map (fun a => fst (fst a)) (blocks_of_env e)) ->
                     Mem.bounds_of_block m' b = (0,0))
         (NOPERM: forall b, 
                    In b (map (fun a => fst (fst a)) (blocks_of_env e)) ->
                    forall k p ofs,
                      ~ Mem.perm m' b ofs k p) ,
    Mem.inject true expr_inj_se  f m tm ->
    Mem.free_list m (blocks_of_env e) = Some m' ->
    Mem.bounds_of_block tm sp = (0, fn_stackspace tf) ->
    match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
    forall lm tlm (smp: size_mem_preserved (m::lm) (tm::tlm) (Frame cenv tf e le te sp lo hi :: cs)),
    
    exists tm',
      Mem.free tm sp 0 ((tf.(fn_stackspace))) = Some tm'
      /\ match_callstack f m' tm' cs (Mem.nextblock m') (Mem.nextblock tm')
      /\ Mem.inject true expr_inj_se f m' tm'.
Proof.
  intros until tm; intros NOBOUND NOPERM INJ FREELIST Bnds MCS. inv MCS. inv MENV.
  assert ({tm' | Mem.free tm sp 0 ((fn_stackspace tf)) = Some tm'}).
  {
    apply Mem.range_perm_free.
    red; intros.
    exploit PERM; eauto. intros [A | A].
    auto.
    inv A. assert (Mem.range_perm m b 0 sz Cur Freeable).
    eapply Mem.free_list_freeable; eauto. eapply in_blocks_of_env; eauto.
    replace ofs with ((ofs - delta) + delta) by omega.
    eapply Mem.perm_inject; eauto. apply H3. omega.
    unfold Mem.has_bounds; rewrite Bnds; auto. rewrite andb_if.
    repeat destruct zeq; destr.    
  }
  destruct X as  [tm' FREE].
  exploit Mem.nextblock_freelist; eauto. intro NEXT.
  exploit Mem.nextblock_free; eauto. intro NEXT'.
  exists tm'. split. auto. split.
  - rewrite NEXT; rewrite NEXT'.
    apply match_callstack_incr_bound with lo sp; try omega.
    eapply match_callstack_invariant with f m tm; eauto.
    + intros. eapply Mem.perm_freelist; eauto.
    + intros. erewrite Mem.bounds_freelist; eauto. 
      intro.
      apply in_map_iff in H1.
      destruct H1 as [[[b' lo'] hi'] [A B]]. simpl in *. subst.
      apply in_blocks_of_env_inv in B.
      destruct B as [id [C A]].
      subst.
      generalize (me_bounded0 _ _ _ C). xomega.
    + intros.
      eapply Mem.bounds_free; eauto. intro; subst. xomega.
    + intros. eapply Mem.perm_free_1; eauto. left; unfold block; xomega.
    + intros.
      rewrite <- Mem.is_block_dynamic_freelist. 2: eauto. tauto.
    + intros.
      rewrite <- Mem.is_block_dynamic_free. 2: eauto. tauto.
    + red; intros.
      destruct (in_dec peq b (map (fun a => fst (fst a)) (blocks_of_env e))).
      rewrite NOBOUND in H; auto. inv H. omega.
      erewrite Mem.bounds_freelist in H; eauto.
      apply (match_callstack_all_blocks_injected) in MCS0.
      eapply MCS0; eauto.
    + xomega. 
    + xomega.
  - eapply freelist_inject ; eauto.
    + eapply match_callstack_all_blocks_injected; eauto. 
    + intros. intro; subst.
      destruct (me_inv0 _ _ H0) as [id [sz Heid]].
      apply in_blocks_of_env in Heid.
      apply in_map with (f:=fun a => fst (fst a)) in Heid. simpl in Heid; congruence.
Qed.

Lemma mcs_norepet_env:
  forall f m tm cenv tf le te sp lo hi cs e
         (MCS: match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm)),
         list_norepet (map (fun a => fst (fst a)) (blocks_of_env e)).
Proof.
  intros.
  inv MCS. unfold norepet_env in NRP.
  rewrite map_map in NRP. auto.
Qed.

Lemma match_callstack_freelist:
  forall f cenv tf e le te sp lo hi cs m m' tm
  (BOUNDS: forall b lo hi, 
              In (b,lo,hi) (blocks_of_env e) ->
              Mem.bounds_of_block m b = (lo,hi))
  (BOUNDSsp: Mem.bounds_of_block tm sp = (0, (fn_stackspace tf))),
  Mem.inject true expr_inj_se f m tm ->
  Mem.free_list m (blocks_of_env e) = Some m' ->
  match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  forall lm tlm (smp: size_mem_preserved (m::lm) (tm::tlm) (Frame cenv tf e le te sp lo hi :: cs)),
  exists tm',
  Mem.free tm sp 0 ((tf.(fn_stackspace))) = Some tm'
  /\ match_callstack f m' tm' cs (Mem.nextblock m') (Mem.nextblock tm')
  /\ Mem.inject true expr_inj_se f m' tm'.
Proof.
  intros.
  assert (list_norepet (map (fun a => fst (fst a)) (blocks_of_env e))).
  {
    eapply mcs_norepet_env; eauto.
  }
  generalize (Mem.exact_bounds_free_list _ _ _ H2 H0).
  intros.
  eapply match_callstack_freelist_aux; eauto; intros; eauto.
  apply H3 in H4. destruct H4; auto.
  apply H3 in H4. destruct H4; auto.
Qed.


(** * Correctness of stack allocation of local variables *)

(** This section shows the correctness of the translation of
  Csharpminor local variables as sub-blocks of the Cminor stack data.
  This is the most difficult part of the proof. *)

Definition cenv_compat (cenv: compilenv) (vars: list (ident * Z)) (tsz: Z) : Prop :=
  forall id sz,
  In (id, sz) vars ->
  exists ofs, 
      PTree.get id cenv = Some ofs 
   /\ Mem.inj_offset_aligned ofs sz
   /\ 0 <= ofs
   /\ ofs + Zmax 0 sz <= tsz.

Definition cenv_separated (cenv: compilenv) (vars: list (ident * Z)) : Prop :=
  forall id1 sz1 ofs1 id2 sz2 ofs2,
  In (id1, sz1) vars -> In (id2, sz2) vars ->
  PTree.get id1 cenv = Some ofs1 -> PTree.get id2 cenv = Some ofs2 ->
  id1 <> id2 ->
  ofs1 + sz1 <= ofs2 \/ ofs2 + sz2 <= ofs1.

Definition cenv_mem_separated (cenv: compilenv) (vars: list (ident * Z)) (f: meminj) (sp: block) (m: mem) : Prop :=
  forall id sz ofs b delta ofs' k p,
  In (id, sz) vars -> PTree.get id cenv = Some ofs ->
  f b = Some (sp, delta) -> 
  Mem.perm m b ofs' k p ->
  ofs <= ofs' + delta < sz + ofs -> False.

Inductive alloc_variables_right : Csharpminor.env -> mem -> list (ident * Z)
                             -> Csharpminor.env -> mem -> Prop :=
  alloc_variables_right_nil : forall (e : Csharpminor.env) (m : mem),
                           alloc_variables_right e m nil e m
| alloc_variables_right_cons : forall (e : PTree.t (block * Z)) 
                                 (m : mem) (id : positive) 
                                 (sz : Z) (vars : list (ident * Z)) 
                                 (m1 : mem) (b1 : block) 
                                 (m2 : mem) (e2 : Csharpminor.env),
                            Mem.alloc m1 0 (Z.max 0 sz) Normal = Some (m2, b1) ->
                            alloc_variables_right (PTree.set id (b1, (Z.max 0 sz)) e) m vars
                                            e2 m1 ->
                            alloc_variables_right e m ((id, sz) :: vars) e2 m2.



Lemma alloc_variables_nextblock:
  forall vars e1 m1 e m2,
    alloc_variables_right e1 m1 vars e m2 ->
    Ple (Mem.nextblock m1) (Mem.nextblock m2).
Proof.
  induction vars; simpl; intros e1 m1 e m2 AVR.
  inv AVR; xomega.
  inv AVR.
  apply IHvars in H6.
  apply Mem.nextblock_alloc in H3.
  rewrite H3. xomega.
Qed.

Lemma alloc_in_vars'':
  forall vars e1 e m1 m2
         (AVR:alloc_variables_right e1 m1 vars  e m2),
    forall id p,
      e1!id = Some p ->
      e!id <> None.
Proof.
  induction vars; simpl; intros; inv AVR.
  - congruence.
  - specialize (IHvars _ _ _ _ H7 id).
    revert IHvars.
    rewrite PTree.gsspec.
    destruct (peq id id0); subst; auto.
    intro A; apply (A _ eq_refl).
    intro A; apply (A _ H).
Qed.

Lemma alloc_in_vars':
  forall vars e1 e m1 m2
         (AVR:alloc_variables_right e1 m1 vars  e m2)
         (LNR: list_norepet (map fst vars))
         (He1: forall id, In id (map fst vars) -> e1 ! id = None),
    forall id p,
      e1!id = Some p ->
      e!id = Some p.
Proof.
  induction vars; simpl; intros; inv AVR.
  - congruence.
  - eapply IHvars;eauto. 
    inv LNR; auto. 
    intros.
    specialize (He1 id1 (or_intror H0)).
    inv LNR.
    rewrite PTree.gso; auto. congruence.
    inv LNR.
    rewrite PTree.gsspec.
    destruct (peq id id0); subst; auto.
    specialize (He1 id0 (or_introl eq_refl)).
    congruence.
Qed.

Lemma alloc_in_vars_domain:
  forall vars e1 e m1 m2
         (AVR:alloc_variables_right e1 m1 vars  e m2)
         (LNT: list_norepet (map fst vars))
         (He1: forall id, In id (map fst vars) -> e1 ! id = None),
    forall id b z,
      e1!id = None ->
      e!id = Some (b,z) ->
      exists z',
        Z.max 0 z' = z /\
        In (id,z') vars.
Proof.
  induction vars; simpl; intros; inv AVR.
  - congruence.
  - inv LNT.
    assert ( forall id1 : ident,
               In id1 (map fst vars) -> (PTree.set id0 (b1,Z.max 0 sz) e1) ! id1 = None).
    intros; rewrite PTree.gso by congruence; auto.
    specialize (IHvars _ _ _ _ H8 H4 H1 id b z ). 
    rewrite PTree.gsspec in IHvars.
    destruct (peq id id0); simpl; subst; auto. 
    apply (alloc_in_vars') with (id:=id0) (p:=(b1,Z.max 0 sz)) in H8; auto.
    rewrite H8 in H0; inv H0; auto.
    exists sz. split; auto.
    apply PTree.gss.
    destruct IHvars as [z' [A B]]; auto.
    exists z'; auto.
Qed.

Record inject_incr_cs (f1 f2: meminj) (sp: block) (m1: mem) (e: Csharpminor.env) (cenv:compilenv) : Prop :=
{
  inj_incr: inject_incr f1 f2;
  inj_same_thr: forall b : positive, Plt b (Mem.nextblock m1) -> f2 b = f1 b;
  inj_above_thr_tm: forall (b b' : block) (delta : Z),
                      f2 b = Some (b', delta) ->
                      Plt b' sp -> f1 b = Some (b', delta);
  inj_env: forall id b z ofs,
             e!id = Some (b,z) ->
             cenv!id = Some ofs ->
             f2 b = Some (sp,ofs);
  inj_env_ex: forall (b : block) (delta : Z),
               f2 b = Some (sp, delta) ->
               exists (id : positive) (sz : Z), e ! id = Some (b, sz)
}.

Definition nodbl (e:Csharpminor.env) :=
  forall id b sz,
    e ! id = Some (b,sz) ->
    ~ (exists id' p, id' <> id /\ e!id' = Some p /\ fst p = b).

Lemma assign_variables_not_in:
  forall l t z id0,
    ~ In id0 (map fst l) ->
    (fst (assign_variables (t, z) l)) ! id0 = t ! id0.
Proof.
  induction l; simpl; intros; auto.
  generalize (IHl (fst (assign_variable (t,z) a)) (snd (assign_variable (t,z) a))).
  rewrite <- surjective_pairing.
  intro A; rewrite A.
  unfold assign_variable.
  destruct a.
  simpl. rewrite PTree.gso by (simpl in *; intuition congruence).
  auto.
  auto.
Qed.

Lemma assign_variables_fold_left:
  forall l t z id0 sz,
    (fst (assign_variables (t, z) (l ++ (id0, sz) :: nil))) ! id0 = 
    Some (
        align
          (small_var_space (rev l) z)
          (block_alignment sz)).
Proof.
  induction l; simpl; intros.
  rewrite PTree.gss; auto.
  destruct a. simpl.
  rewrite IHl.
  unfold small_var_space.
  replace (rev l ++ (p,z0)::nil) with (rev ((p,z0)::l)); auto.
  rewrite ! fold_left_rev_right.
  simpl. auto.
Qed.

Lemma alloc_variables_right_bounds:
  forall vars e1 e m1 m2 id b sz
         (AVR:alloc_variables_right e1 m1 vars  e m2)
         (Iv: In id (map fst vars))
         (Heid: e ! id = Some (b, sz))
         (LNR: list_norepet (map fst vars))
         (Hnodbl:
         forall id id0 b b' sz sz',
           In id (map fst vars) ->
           In id0 (map fst vars) ->
         id <> id0 -> e!id = Some (b,sz) -> e!id0 = Some (b',sz') -> b <> b')
         (He1: forall id,
                 In id (map fst vars) ->
                 e1 ! id = None
         ),
    Mem.bounds_of_block m2 b = (0,sz).
Proof.
  induction vars; simpl; intros; try 
  intuition congruence.
  inv AVR.
  destruct (peq id0 id); subst.
  - generalize H6; intros.
    inv LNR. 
    apply alloc_in_vars' with (id:=id) (p:=(b1,Z.max 0 sz0)) in H6; auto.
    + rewrite Heid in H6; inv H6.
      replace (Z.max 0 sz0) with (Z.max 0 (Z.max 0 sz0)).
      erewrite Mem.bounds_of_block_alloc; eauto.
      rewrite Zmax_r; auto. apply Z.le_max_l.
    + intros.
      rewrite PTree.gso by congruence.
      apply He1; auto.
    + rewrite PTree.gss; auto.
  - destruct Iv; subst; simpl in *;  try congruence.
    destruct (peq b b1). 
    + subst.
      generalize (He1 id0 (or_introl eq_refl)).
      generalize (He1 id (or_intror H)). 
      intros e1id e1id0. 
      inv LNR.
      generalize Heid.
      assert (forall id1 : ident,
                In id1 (map fst vars) -> 
                (PTree.set id0 (b1, Z.max 0 sz0) e1) ! id1 = None).
      {
        intros. rewrite PTree.gso. apply He1; auto. congruence.
      }
      generalize (alloc_in_vars' _ _ _ _ _ H6 H4 H0) (* with (p:=(b1,sz0)) in Heid. *).
      intro AIV. intros.
      generalize (AIV id0 (b1,Z.max 0 sz0)). 
      rewrite PTree.gss.
      destruct (e!id0) eqn:?; intuition try congruence.
      inv H7.
      specialize (Hnodbl id0 id _ _ _ _ (or_introl eq_refl) (or_intror H) n
                         Heqo Heid0).
      congruence.
    + erewrite <- Mem.bounds_of_block_alloc_other; eauto.
      eapply IHvars in H6; eauto.
      inv LNR; auto.
      intros.
      rewrite PTree.gso; auto.
      inv LNR. congruence.
Qed.

Lemma alloc_variables_right_nodbl:
  forall vars e1 e m1 m2
         (AVR:alloc_variables_right e1 m1 vars  e m2)
         (LNR: list_norepet (map fst vars))
         (INe1:forall id : ident, In id (map fst vars) -> e1 ! id = None)
         (NDBL: nodbl e1)
         (VB: forall id b z, e1!id = Some (b,z) -> ~ Mem.valid_block m2 b),
    nodbl e.
Proof.
  induction vars; simpl; intros; inv AVR; auto.
  inv LNR.  
  specialize (IHvars _ _ _ _ H6 H2).
  apply IHvars.
  - intros.
    rewrite PTree.gso by congruence.
    apply INe1; auto.
  - red; intros.
    intros  [id' [[i j] [A [B C]]]]; simpl in *. subst.
    red in NDBL.
    revert H B.
    rewrite ! PTree.gsspec.
    repeat destruct peq; subst; intuition try congruence.
    + inv H.
      generalize (Mem.valid_new_block _ _ _ _ _ _ H3). intro.
      apply VB in B; auto.
    + inv B.
      generalize (Mem.valid_new_block _ _ _ _ _ _ H3). intro.
      apply VB in H; auto.
    + apply (NDBL _ _ _ H).
      exists id' ; exists (b, j); repeat split; auto.
  - intros.
    rewrite PTree.gsspec in H.
    destruct (peq id0 id); subst; auto.
    inv H.
    eapply Mem.fresh_block_alloc; eauto.
    intro.
    generalize (Mem.valid_block_alloc _ _ _ _ _ _ H3).
    intro.
    apply H4 in H0.
    eapply VB; eauto.
Qed.

Lemma assign_variables_in:
  forall vars t o id,
    In id (map fst vars) ->
    list_norepet (map fst vars) ->
    (fst (assign_variables (t,o) vars)) ! id = None ->
    False.
Proof.
  induction vars; simpl; intros.
  auto.
  unfold assign_variable in H0.
  destruct a. simpl in *.
  destruct H.
  subst.
  rewrite assign_variables_not_in in H1.
  rewrite PTree.gss in H1; congruence.
  inv H0; auto.
  apply IHvars in H1; auto.
  inv H0; auto.
Qed.

Lemma fl_align_add:
  forall l z1,
    0 <= z1 ->
    z1 <=
    fold_left
      (fun (x : Z) (y : positive * Z) =>
         align x (block_alignment (snd y)) + Z.max 0 (snd y)) l
      z1.
Proof.
  induction l; simpl; intros; try omega.
  generalize (Zmax_bound_l 0 0 (snd a)).
  generalize (align_le z1 _ (block_alignment_pos (snd a))).
  intros.
  refine (Zle_trans _ _ _ _ (IHl _ _)); omega.
Qed.



Lemma alloc_in_vars_same:
  forall vars e1 e m1 m2
         (AVR:alloc_variables_right e1 m1 vars  e m2)
         id
         (LNR: ~ In id (map fst vars)),
      e1!id = e ! id.
Proof.
  induction vars; simpl; intros; inv AVR; auto.
  eapply IHvars in H6;eauto. 
  revert H6. rewrite PTree.gso; auto. 
Qed.

Lemma avr_valid_before:
  forall vars e1 m1 e m0 
         (AVR: alloc_variables_right e1 m1 vars e m0)
         b
         (LNR: list_norepet (map fst vars))
         (VB:Mem.valid_block m0 b),
    Mem.valid_block m1 b \/ 
    (exists i z, e ! i = Some (b,z) /\ In i (map fst vars)).
Proof.
  induction 1; simpl; intros; auto.
  generalize H; intro ALLOC.
  apply Mem.valid_block_alloc_inv with (b':=b) in ALLOC; auto.
  destruct ALLOC; subst.
  - right; exists id; exists (Z.max 0 sz); split; auto.
    inv LNR.
    generalize (alloc_in_vars_same _ _ _ _ _ AVR _ H2).
    rewrite PTree.gss; auto.
  - inv LNR. 
    destruct (IHAVR _ H4 H0); auto.
    destruct H1 as [i [z [A B]]].
    right; exists i; exists z; split; auto.
Qed.


Lemma box_span_small_align':
  forall z m, 0 <= z ->
       (m <= MA)%nat -> 
       Mem.box_span (align z (two_power_nat m)) = Mem.box_span z.
Proof.
  intros.
  apply Nat2Z.inj.
  cut (two_power_nat MA *    Z.of_nat (Mem.box_span (align z (two_power_nat m))) = two_power_nat MA * Z.of_nat (Mem.box_span z)). generalize Mem.tpMA_pos. nia.
  rewrite ! Mem.box_span_align; auto.
  apply align_le_two_p; auto. lia.
  apply Z.le_ge. etransitivity; [|apply align_le]. lia.
  apply two_power_nat_pos.
Qed.

Lemma box_span_small_alig:
  forall z s,
    z >= 0 ->
    Mem.box_span (align z (block_alignment s)) = Mem.box_span z.
Proof.
  intros.
  apply box_span_small_align'. lia.
  apply Genv.aos_ma.
Qed.

Lemma alloc_one_more:
  forall ei
    (wf: wf_inj ei)
    (tm1 tm2 tm2' m0 m2 : mem) (b1 sp sp' : block) 
    (f2 : meminj) (ofs size_vars sz : Z)
    (Hofs: Z.max 0 sz + align size_vars (block_alignment sz) <= Int.max_unsigned)
    (Zsizepos: size_vars >= 0)
    (ALLOC_vars: Mem.alloc tm1 0 size_vars Normal = Some (tm2, sp))
    (ALLOC_new_var: Mem.alloc m0 0 (Z.max 0 sz) Normal = Some (m2, b1))
    (MI: Mem.inject true ei f2 m0 tm2)
    (ALLOC_all: Mem.alloc tm1 0 (align (size_vars) (block_alignment sz) + Z.max 0 sz) Normal = Some (tm2', sp'))
    (overlap: forall (b : block) (delta : Z),
        f2 b = Some (sp, delta) -> delta + Mem.size_block m0 b <= ofs)
    (ofsInf: 0 <= ofs <= size_vars),
    Mem.inject true ei
               (fun bb : positive =>
                  if peq bb b1
                  then Some (sp', align ofs (block_alignment sz))
                  else f2 bb) m2 tm2'.
Proof.
  intros.
  inversion MI.
  constructor; eauto.
  - destruct mi_inj. 
    assert (sp = sp').
    {
      apply Mem.alloc_result in ALLOC_all.
      apply Mem.alloc_result in ALLOC_vars.
      subst; auto.
    } subst sp'. 
    {
      constructor; eauto.
      - intros.
        destruct (peq b0 b1); subst; inv H; eauto.
        + eapply Mem.perm_alloc_3 in H0; eauto.
          apply Mem.perm_implies with (p1:=Freeable); auto; try constructor.
          eapply Mem.perm_alloc_2; eauto. 
          generalize (align_le ofs _ (block_alignment_pos sz)).
          split; try omega.
          apply Z.lt_le_trans with (sz + align size_vars (block_alignment sz)). 
          apply Z.add_lt_le_mono. rewrite Zmax_spec in H0. destr_in H0; lia. 
          apply align_add. apply block_alignment_pos. omega.
          rewrite Z.add_comm.
          transitivity (align size_vars (block_alignment sz) + sz). lia.
          apply Z.add_le_mono_l.
          apply (Zmax_bound_r sz 0 sz). omega.
        + eapply Mem.perm_alloc_4 in H0; eauto.
          generalize (mi_perm _ _ _ _ _ _ H2 H0).
          intro.
          destruct (peq b2 sp); subst; auto. 
          * apply Mem.perm_implies with (p1:=Freeable); auto; try constructor.
            eapply Mem.perm_alloc_2 ; eauto.
            eapply Mem.perm_alloc_3 with (m2:= tm2) (hi:= size_vars) in H; eauto.
            split. omega.
            apply Z.lt_le_trans with (m:=size_vars); try omega.
            generalize (align_le size_vars _ (block_alignment_pos sz)).
            generalize (Zmax_bound_l 0 0 sz). omega.
          * eapply Mem.perm_alloc_1; eauto.
            eapply Mem.perm_alloc_4 in H; eauto.
      - intros. unfold Mem.in_bound_m in *.
        destruct (peq b0 b1); subst; inv H; eauto.
        + erewrite Mem.bounds_of_block_alloc in H0; eauto. 
          erewrite Mem.bounds_of_block_alloc; eauto.
          unfold in_bound in *; simpl in *.
          generalize (align_le ofs _  (block_alignment_pos sz)). 
          split; try omega. 
          apply Z.lt_le_trans with (Z.max 0 sz + align ofs (block_alignment sz)). lia. 
          rewrite Z.add_comm.
          apply Zmax_bound_r.
          apply Z.add_le_mono_r.
          apply align_add. apply block_alignment_pos. lia.
        + erewrite <- Mem.bounds_of_block_alloc_other in H0; eauto. 
          generalize (mi_bounds _ _ _ _ H2 H0).
          erewrite Mem.bounds_of_block_alloc_eq; eauto.
          erewrite Mem.bounds_of_block_alloc_eq with (m2:=tm2'); eauto.
          destruct (eq_block b2 sp); subst; auto.
          * unfold in_bound; simpl; try lia. split; try lia.
            apply Z.lt_le_trans with (Z.max 0 size_vars). lia.
            repeat rewrite Z.max_r by lia.
            rewrite Z.max_r.
            generalize (align_le size_vars _ (block_alignment_pos sz)).
            rewrite Zmax_spec; destr; try lia.
            generalize (align_le size_vars _ (block_alignment_pos sz)).
            rewrite Zmax_spec; destr; try lia.
          * erewrite Mem.nextblock_alloc; eauto. 
            erewrite Mem.nextblock_alloc with (m2:=tm2'); eauto. 
      - intros.
        destruct (peq b b1); subst; auto.
        + inv H.
          erewrite ! Mem.alloc_mask; eauto.
          split.
          * apply nat_ge_le. 
            apply Mem.alignment_of_size_inj.
            rewrite ! Zmax_spec. repeat destr; try lia.
            generalize (align_le size_vars _ (block_alignment_pos sz)). lia.
            apply Zle_ge.
            generalize (align_le size_vars _ (block_alignment_pos sz)); lia. 
          * apply Zdivides_trans with (y:=(block_alignment sz)).
            rewrite Zmax_spec.
            unfold block_alignment, alignment_of_size .
            des (zlt sz 0). apply Z.divide_1_l.
            repeat destr;
            exists 1; simpl; auto; try lia.
            apply align_divides. apply block_alignment_pos.
        + apply mi_align' in H.
          destruct (peq b0 sp); subst; auto.
          * erewrite <- Mem.mask_alloc_other with (m2:=m2); eauto.
            revert H.
            erewrite Mem.alloc_mask; eauto.
            eapply Mem.alloc_mask in ALLOC_all; eauto.
            rewrite ALLOC_all.
            intros; intuition try congruence.
            apply ge_trans with (Alloc.alignment_of_size size_vars); auto.
            apply Mem.alignment_of_size_inj. 
            generalize (align_le size_vars _ (block_alignment_pos sz)).
            generalize (Zmax_bound_r 0 sz 0). rewrite Z.max_comm.
            rewrite (Zmax_spec 0 (align _ _ + _)). 
            destr; try lia.
          * revert H.
            erewrite <- Mem.mask_alloc_other with (m2:=tm2'); eauto.
            erewrite <- Mem.mask_alloc_other with (m2:=tm2); eauto.
            erewrite <- Mem.mask_alloc_other with (m2:=m2); eauto.
      - intros.
        destruct (peq b0 b1); subst; auto.
        + inv H. 
          apply Mem.perm_bounds in H0. unfold Mem.in_bound_m in *.
          erewrite Mem.bounds_of_block_alloc in H0; eauto.
          unfold in_bound in H0; simpl in H0.
          apply Mem.mem_alloc_block_undefs in ALLOC_all. 
          apply Mem.mem_alloc_block_undefs in ALLOC_new_var. 
          red in ALLOC_all.
          red in ALLOC_new_var. 
          generalize (align_le size_vars _ (block_alignment_pos sz)).
          generalize (Zmax_spec 0 sz); destruct (zlt sz 0); try lia.
          specialize (ALLOC_all (ofs0 + align ofs (block_alignment sz))).
          intros.
          rewrite H in *.
          rewrite Z.add_0_r in ALLOC_all.
          rewrite ALLOC_all; try lia.
          * specialize (ALLOC_new_var ofs0).
            rewrite Z.add_0_r in ALLOC_new_var.
            rewrite ALLOC_new_var; auto.
            constructor. 
            apply vi_ei. auto.
            simpl; unfold Val.inj_undef. auto.
            (* rewrite peq_true. simpl. *)
            (* repeat f_equal. apply Val.int_add_repr. *)
            auto. 
            rewrite Zmax_spec in H0; revert H0; destr; lia.
          * split; try lia.
            generalize (align_le ofs _ (block_alignment_pos sz)). lia.
            rewrite Z.add_comm. 
            apply Z.add_le_lt_mono.
            apply align_add; try lia. apply block_alignment_pos.
            lia. 
        + erewrite Mem.alloc_contents with (m':=m2); eauto.
          eapply Mem.perm_alloc_4 with (m2:=m2) in H0; eauto.
          generalize (mi_memval _ _ _ _ H H0).
          generalize ALLOC_vars; intro.
          generalize ALLOC_all; intro.
          apply Mem.mem_alloc_block_undefs in ALLOC_all. 
          apply Mem.mem_alloc_block_undefs in ALLOC_vars. 
          red in ALLOC_vars.
          red in ALLOC_all.
          destruct (peq b2 sp); subst; auto.
          * generalize (align_le size_vars _ (block_alignment_pos sz)).
            (* generalize (Zmax_spec 0 sz); destruct (zlt sz 0); try lia.  *)
            specialize (ALLOC_all (ofs0 + delta)).
            intros.
            rewrite Z.add_0_r in ALLOC_all.
            specialize (ALLOC_vars (ofs0 + delta)).
            intros.
            rewrite Z.add_0_r in ALLOC_vars.
            assert (0 <= ofs0 + delta < size_vars).
            {
              eapply mi_perm in H0; eauto.
              apply Mem.perm_bounds in H0. 
              unfold Mem.in_bound_m in *. erewrite Mem.bounds_of_block_alloc in H0; eauto.
              unfold in_bound in H0; rewrite Zmax_spec in H0; revert H0; destr; lia.
            }
            rewrite ALLOC_all; try lia. 
            rewrite ALLOC_vars in H2; auto.
            inv H2. constructor.
            eapply ei_inj_incr; eauto.
            red; intros.
            destruct (peq b b1); subst; auto.
            rewrite mi_freeblocks in H2.
            congruence.
            unfold Mem.valid_block.
            erewrite <- Mem.alloc_result with (m2:=m2); eauto.
            xomega. 
            destruct TYPorUNDEF; auto.
             right.
            eapply same_eval_inj_incr; eauto.
            red; intros. destr.
            subst.
            exploit Mem.valid_block_inject_1; eauto.
            unfold Mem.valid_block; rewrite (Mem.alloc_result _ _ _ _ _ _ ALLOC_new_var). xomega.

          * erewrite Mem.alloc_contents with (m':=tm2); eauto.
            erewrite Mem.alloc_contents with (m':=tm2'); eauto.
            intro A; inv A. 
            constructor.
            eapply ei_inj_incr; eauto.
            red; intros.
            destruct (peq b b1); subst; auto.
            rewrite mi_freeblocks in H1.
            congruence.
            unfold Mem.valid_block.
            erewrite <- Mem.alloc_result with (m2:=m2); eauto.
            xomega.
            destruct TYPorUNDEF; auto.
            right.
            eapply same_eval_inj_incr; eauto.
            red; intros. destr.
            subst.
            exploit Mem.valid_block_inject_1; eauto.
            unfold Mem.valid_block; rewrite (Mem.alloc_result _ _ _ _ _ _ ALLOC_new_var). xomega.
      - clear  mi_align'.  
        clear mi_no_overlap' mi_memval mi_bounds mi_perm. 
        clear MI. intros.
        rewrite (Mem.nb_boxes_alloc _ _ _ _ _ _ ALLOC_all) in *.
        rewrite (Mem.nb_boxes_alloc _ _ _ _ _ _ ALLOC_vars) in *.
        rewrite (Mem.nb_boxes_alloc _ _ _ _ _ _ ALLOC_new_var) in *.

        replace (Z.max 0 (Z.max 0 sz)) with (Z.max 0 sz) by
            (rewrite ! Zmax_spec; repeat destr; lia).
        rewrite Zmax_r.
        
        cut (Mem.box_span (align size_vars (block_alignment sz) + Z.max 0 sz)  <=
             Mem.box_span (Z.max 0 size_vars) + Mem.box_span (Z.max 0 sz))%nat. intuition lia.
        etransitivity.
        apply box_span_add. apply Z.le_ge. apply Zmax_bound_l. lia.
        apply Z.le_ge. etransitivity. 2: apply align_le. lia.
        apply (block_alignment_pos sz).
        apply NPeano.Nat.add_le_mono_r.
        rewrite box_span_small_alig. rewrite Z.max_r. lia. lia. lia.
        change 0 with (0 + 0) at 1. eapply Z.add_le_mono.
        etransitivity. 
        2: apply align_le; auto. lia. apply block_alignment_pos.
        apply Z.le_max_l.
    }
  - intros.
    assert (~ Mem.valid_block m0 b).
    destruct (Mem.valid_block_dec m0 b); auto.
    eapply Mem.valid_block_alloc in v; eauto.
    apply mi_freeblocks in H0.
    rewrite H0. 
    destruct (peq b b1); subst; auto.
    apply Mem.valid_new_block in ALLOC_new_var. congruence.
  - intros.
    destruct (peq b b1); subst; simpl in *.
    + inv H.
      apply Mem.valid_new_block in ALLOC_all; auto.
    + apply mi_mappedblocks in H.
      apply Mem.nextblock_alloc in ALLOC_vars.
      apply Mem.nextblock_alloc in ALLOC_all.
      revert H; unfold Mem.valid_block. congruence. 
  - red; intros.
    generalize (Mem.alloc_result _ _ _ _ _ _ ALLOC_all)
               (Mem.alloc_result _ _ _ _ _ _ ALLOC_vars). intros; subst.
    destruct (peq b0 b1); destruct (peq b2 b1); subst; try congruence; inv H0; inv H1.
    + destruct (peq b2' (Mem.nextblock tm1)); subst; auto.
      right.
      unfold Mem.in_bound_m in *. erewrite <- Mem.bounds_of_block_alloc_other with (m2:=m2) in H3; eauto.
      generalize (Mem.mi_bounds _ _ _ _ _ mi_inj _ _ _ ofs2 H4 H3).
      intro.
      unfold Mem.in_bound_m in *. erewrite Mem.bounds_of_block_alloc in H0; eauto.
      unfold in_bound in H0. simpl in H0.
      erewrite Mem.bounds_of_block_alloc in H2; eauto.
      unfold in_bound in H2; simpl in H2.
      apply overlap in H4.
      cut (align ofs (block_alignment sz) > ofs2 + delta2).  intros. omega.
      unfold Mem.bounds_of_block, Mem.size_block, Alloc.get_size in H4, H3.
      revert H4; destr_cond_match.
      * destruct p. unfold in_bound in H3; simpl in *. 
        intros.
        apply Zlt_gt.
        apply Zlt_le_trans with (z0 + delta2). omega.
        transitivity ofs. 
        apply Mem.bounds_lo_inf0 in Heqo. subst. omega.
        apply (align_le _ _ (block_alignment_pos sz)). 
      * unfold in_bound in H3; simpl in H3. intros; omega.
    + destruct (peq b1' (Mem.nextblock tm1)); subst; auto.
      right.
      unfold Mem.in_bound_m in *. erewrite <- Mem.bounds_of_block_alloc_other with (m2:=m2) in H2; eauto.
      generalize (Mem.mi_bounds _ _ _ _ _ mi_inj _ _ _ ofs1 H5 H2).
      intro.
      unfold Mem.in_bound_m in *. erewrite Mem.bounds_of_block_alloc in H0; eauto.
      unfold in_bound in H0. simpl in H0.
      erewrite Mem.bounds_of_block_alloc in H3; eauto.
      unfold in_bound in H3; simpl in H3.
      apply overlap in H5.
      cut (align ofs (block_alignment sz) > ofs1 + delta1).  intros. omega.
      unfold Mem.bounds_of_block, Mem.size_block, Alloc.get_size in H5, H2.
      revert H5; destr_cond_match.
      * destruct p. unfold in_bound in H2; simpl in *. 
        intros.
        apply Zlt_gt.
        apply Zlt_le_trans with (z0 + delta1). omega.
        transitivity ofs. 
        apply Mem.bounds_lo_inf0 in Heqo. subst. omega.
        apply (align_le _ _ (block_alignment_pos sz)). 
      * unfold in_bound in H2; simpl in H2. intros; omega.
    + unfold Mem.in_bound_m in *.
      erewrite <- Mem.bounds_of_block_alloc_other with (m2:=m2) in H2; eauto.
      erewrite <- Mem.bounds_of_block_alloc_other with (m2:=m2) in H3; eauto.
  - intros.
    destruct (peq b b1); subst; eauto.
    inv H.
    generalize (align_le ofs _ (block_alignment_pos sz)).
    omega.
  -
    Require Import Tactics.
    intros. destr_in H. inv H.
    rewrite <- (Mem.is_block_dynamic_alloc _ _ _ _ _ ALLOC_all).
    rewrite <- (Mem.is_block_dynamic_alloc _ _ _ _ _ ALLOC_new_var).
    unfold Mem.is_dynamic_block.
    rewrite ! Mem.blocktype_valid by (eapply Mem.fresh_block_alloc; eauto).
    destr.

    
    rewrite <- (Mem.is_block_dynamic_alloc _ _ _ _ _ ALLOC_all).
    rewrite <- (Mem.is_block_dynamic_alloc _ _ _ _ _ ALLOC_new_var).
    rewrite (Mem.is_block_dynamic_alloc _ _ _ _ _ ALLOC_vars).
    specialize (mi_inj_dynamic _ _ _ H).
    des mi_inj_dynamic. des a.
    Mem.rewbnd.
    repSplit; intros; eauto.
    + trim a0; auto. des a0. repSplit; destr. rewrite e1.
      rewrite <- (Mem.bounds_of_block_alloc_other _ _ _ _ _ _ ALLOC_vars).
      rewrite <- (Mem.bounds_of_block_alloc_other _ _ _ _ _ _ ALLOC_all). auto.
      Lemma dyn_valid:
        forall m b,
          Mem.is_dynamic_block m b ->
          Mem.valid_block m b.
      Proof.
        intros.
        destruct (Mem.valid_block_dec m b); auto.
        red in H; rewrite Mem.blocktype_valid in H; auto. destr.
      Qed.
      intro; subst. revert H0.
      rewrite i. rewrite <- (Mem.is_block_dynamic_alloc _ _ _ _ _ ALLOC_vars).
      intro A; apply dyn_valid in A. revert A; eapply Mem.fresh_block_alloc; eauto.
      intro; subst. revert H0.
      rewrite i. rewrite <- (Mem.is_block_dynamic_alloc _ _ _ _ _ ALLOC_vars).
      intro A; apply dyn_valid in A. revert A; eapply Mem.fresh_block_alloc; eauto.
    + destr_in H1.
      inv H1.
      rewrite <- (Mem.is_block_dynamic_alloc _ _ _ _ _ ALLOC_vars) in H0.
      apply dyn_valid in H0. eapply Mem.fresh_block_alloc in H0; eauto. easy.
      eauto.      
Qed.

Lemma match_callstack_alloc_variables_inject:
  forall vars tm1 sp tm2 m1 e m2 f1 e1 size cenv
         (AVS: alloc_variables_right e1 m1 vars e m2)
         (NODBL: nodbl e)
         (LNR: list_norepet (map fst vars))
         (He1: forall id, In id (map fst vars) -> e1 ! id = None)
         (VB: forall (id : positive) (b : block) (z : Z),
             e ! id = Some (b, z) -> ~ Mem.valid_block m1 b)
         (ALLOC: Mem.alloc tm1 0 size Normal = Some (tm2, sp))
         (INJ: Mem.inject true expr_inj_se f1 m1 tm1)
         (SSTF: size = small_var_space vars 0)
         (size_int: 0 <= size <= Int.max_unsigned)
         (cenv_spec: fst (assign_variables (PTree.empty Z,0) (rev vars)) = cenv),
    exists f2,
      Mem.inject true expr_inj_se f2 m2 tm2 /\
      inject_incr_cs f1 f2 sp m1 e cenv.
Proof.
  induction vars. 
  - simpl; intros; subst. 
    generalize (Mem.alloc_0_inject _ _ _ _ _ _ _ _ ALLOC INJ).
    intro; exists f1; simpl; auto.
    inv AVS. split; auto.
    constructor; auto.
    intros id b z ofs; rewrite PTree.gempty; congruence.
    intros b delta FB.
    clear H; eapply Mem.mi_mappedblocks in FB; eauto.
    erewrite Mem.alloc_result in FB; eauto.
    unfold Mem.valid_block in FB; xomega.
  - simpl in *; intros; subst.
    inv AVS. simpl in *.
    destruct (Mem.alloc tm1 0 ((small_var_space vars 0)) Normal) eqn:?.
    + destruct p.  
      generalize Heqo; intro ALLOC'.
      generalize (fr_align_pos vars 0). intro H; trim H. lia. 
      eapply IHvars with (m2:=m0) in Heqo; eauto.
      * destruct Heqo as [f2 [MI IICS]]. 
        exists (fun bb =>
                  if peq bb b1
                  then Some (sp, align 
                                   (small_var_space vars 0) 
                                   (block_alignment sz))
                  else f2 bb). 
        split.
        {  
          eapply alloc_one_more; eauto.
          (* - apply wf_inj_expr_inj_se. *)
          - revert size_int. 
            (* generalize (align_le (Z.max 0 sz) 8). *)
            intros.
            (* rewrite SSTF in size_int. *)
            etransitivity.
            2: apply size_int.
            lia.
          - clear IHvars H size_int.
            intros.
            inv IICS. 
            generalize H; intro FB. 
            apply inj_env_ex0 in H.
            destruct H as [id0 [sz0 Heid]].             
            des (peq b0 b1).
            erewrite Mem.mi_freeblocks in FB; eauto. congruence.
            eapply Mem.fresh_block_alloc; eauto.
            des (peq id id0).
            erewrite (alloc_in_vars' _ _ _ _ _ H6) with (p:=(b1, Z.max 0 sz)) in Heid; eauto.
            inv Heid; congruence.
            inv LNR; auto.
            inv LNR; intros; rewrite PTree.gso. apply He1; auto. congruence.
            apply PTree.gss. inv LNR.
            destruct (in_dec peq id0 (map fst vars)).
            + generalize (alloc_in_vars_domain _ _ _ _ _ H6 H2).
              intro A.
              trim A.
              {
                intros. rewrite PTree.gso by congruence.
                apply He1; auto.
              }
              specialize (A id0 b0 sz0).
              trim A.
              {
                rewrite PTree.gso by congruence.
                apply He1; auto.
              }
              specialize (A Heid).
              destruct A as [s' [Zspec I]].
              assert (Mem.bounds_of_block m0 b0 = (0,sz0)).
              {
                refine (alloc_variables_right_bounds
                          _ _ _ _ _ _ _ _
                          H6 i Heid H2 
                          _ _
                       ).
                * intros.
                  red in NODBL.
                  apply NODBL in H5.
                  intro. subst.
                  apply H5. exists id2. rewrite H7.
                  eexists; repeat split; eauto.
                * intros.
                  rewrite PTree.gso by congruence.
                  apply He1. auto.
              }
              assert (Mem.size_block m0 b0 = sz0). 
              {
                revert H; unfold Mem.bounds_of_block, Mem.size_block, Alloc.get_size.
                destr. des p. intro A; inv A. omega.
              }
              rewrite H0. clear H0. subst.
              revert I inj_env0 Heid FB H2. clear.
              destruct ((fst (assign_variables (PTree.empty Z, 0) (rev vars)))!id0) eqn:?.
              * intros. generalize Heid; intro Heid'.
                eapply inj_env0 with (ofs:=z) in Heid; auto.
                rewrite Heid in FB. inv FB.
                clear inj_env0.
                rewrite <- (rev_involutive vars). unfold small_var_space. 
                rewrite fold_left_rev_right.
                apply in_rev in I.
                apply list_norepet_rev in H2. 
                rewrite <- map_rev in H2.
                revert I Heqo H2. 
                unfold ident in *.
                generalize (rev vars).
                clear Heid' Heid.
                intro l; revert id0 s' delta.
                assert (0 <= 0) by omega.
                revert H.
                generalize 0 at 2 3 6. 
                generalize (PTree.empty Z).
                clear.
                {
                  induction l; simpl; intros. exfalso; auto.
                  unfold assign_variable in Heqo.
                  destruct a.
                  destruct I.
                  - inv H0. inv H2.
                    rewrite assign_variables_not_in in Heqo; auto.
                    rewrite PTree.gss in Heqo.
                    inv Heqo.
                    simpl.
                    apply fl_align_add.
                    generalize (Zmax_bound_l 0 0 s').
                    generalize (align_le z _ (block_alignment_pos s')). omega.
                  - apply IHl with (s':=s') in Heqo; auto.
                    generalize (Zmax_bound_l 0 0 z0).
                    generalize (align_le z _ (block_alignment_pos z0)). omega.
                    inv H2; auto.
                }
              * intros.
                apply assign_variables_in in Heqo. exfalso; auto.
                apply in_map with (f:=fst) in I; simpl in *; auto.
                rewrite map_rev.
                apply -> in_rev; auto.
                rewrite map_rev.
                apply list_norepet_rev; auto.
            +                   (* id is not in vars, so b0 should not be injected in sp *)
              exfalso.
              apply VB with (id:=id0) (b:=b0) (z:=sz0); auto.
              generalize (alloc_in_vars_same _ _ _ _ _ H6 _ n1).
              rewrite PTree.gso by congruence.
              rewrite Heid.
              intro A.
              destruct (avr_valid_before _ _ _ _ _ H6 b0 H2); auto.
              destruct (Mem.valid_block_dec m0 b0); auto.
              erewrite Mem.mi_freeblocks in FB; eauto. congruence.
              destruct H as [i [z [C B]]].
              exfalso. 
              destruct (peq i id0); try congruence.
              generalize (NODBL _ _ _ Heid).
              intro D; apply D.
              exists i; exists (b0,z); repeat split; auto.
          - split.
            + apply Zge_le. apply fr_align_pos. omega.
            + lia. 
        }
        {
          inv IICS. 
          constructor; simpl; intros; eauto.
          - red; intros.
            destruct (peq b0 b1); subst; auto.
            erewrite Mem.mi_freeblocks with (m1:=m1) in H0; eauto.
            congruence.
            generalize (alloc_variables_nextblock _ _ _ _ _ H6).
            rewrite (Mem.alloc_result _ _ _ _ _ _ H3).
            unfold Mem.valid_block. xomega.
          - destruct (peq b0 b1); subst; auto.
            generalize (alloc_variables_nextblock _ _ _ _ _ H6).
            rewrite (Mem.alloc_result _ _ _ _ _ _ H3) in H0.
            xomega.
          - destruct (peq b0 b1); subst; auto.
            + inv H0. xomega.
            + eapply inj_above_thr_tm0 in H0; eauto.
              rewrite (Mem.alloc_result _ _ _ _ _ _ ALLOC').
              rewrite (Mem.alloc_result _ _ _ _ _ _ ALLOC) in H1. auto.
          - destruct (peq b0 b1); subst; auto.
            inv LNR.
            generalize (alloc_in_vars' _ _ _ _ _ H6 H7).
            intro A.
            assert (e!id = Some (b1,Z.max 0 sz)).
            {
              apply A; auto.
              intros; rewrite PTree.gso by congruence.
              apply He1; auto.
              apply PTree.gss.
            }
            clear A.
            assert (id = id0).
            {
              destruct (peq id id0); subst; auto.
              destruct (NODBL id b1 _ H2).
              exists id0. exists (b1,z). repeat split; auto.
            } subst.
            rewrite H0 in H2; inv H2.
            f_equal. f_equal. 
            { 
              revert H1. clear.
              rewrite assign_variables_fold_left.
              intro A; inv A.
              rewrite rev_involutive; auto.
            }
            apply inj_env0 with (ofs:=ofs) in H0.
            rewrite (Mem.alloc_result _ _ _ _ _ _ ALLOC') in H0.
            rewrite (Mem.alloc_result _ _ _ _ _ _ ALLOC). auto.
            assert (id0 <> id).
            {
              intro; subst.
              erewrite (alloc_in_vars' _ _ _ _ _ H6) with (p:=(b1,Z.max 0 sz))in H0; eauto.
              - inv H0. congruence.
              - inv LNR. auto.
              - intros. rewrite PTree.gso.
                apply He1; auto. inv LNR; intuition congruence.
              - apply PTree.gss.
            }
            clear - H1 H2.
            revert H1. generalize (PTree.empty Z).
            generalize 0. intros z t.
            assert (~ In id0 (map fst ((id,sz) :: nil))).
            {
              simpl; intuition congruence.
            }
            revert H.
            unfold ident in *.
            generalize ((id,sz)::nil).
            generalize (rev vars). clear H2.
            intros l l0.
            revert l l0 id0 ofs z t.  clear. 
            induction l; simpl; intros.
            rewrite assign_variables_not_in in H1; auto.
            unfold ident in *.
            destruct (assign_variable (t,z) a) eqn:?.
            apply IHl in H1; auto.
          - destruct (peq b0 b1); subst; intros; eauto.
            + inv H0.
              clear inj_env_ex0 inj_env0 inj_above_thr_tm0 inj_same_thr0 inj_incr0.
              exists id; exists (Z.max 0 sz).
              apply (alloc_in_vars' _ _ _ _ _ H6); auto.
              inv LNR; auto.
              intros.
              inv LNR.
              rewrite PTree.gso; auto. congruence.
              apply PTree.gss.
            + assert (b=sp).
              rewrite (Mem.alloc_result _ _ _ _ _ _ ALLOC').
              rewrite (Mem.alloc_result _ _ _ _ _ _ ALLOC). auto.
              subst.
              apply inj_env_ex0 in H0. auto.
        } 
      * inv LNR; auto.
      * intros.
        generalize (He1 _ (or_intror H0)).
        rewrite PTree.gso; auto. inv LNR; auto. 
        congruence.
      * split; try omega. 
        refine (Zle_trans _ _ _ (align_le _ _ (block_alignment_pos sz)) _).
        generalize (Zmax_bound_l 0 0 sz).
        omega.
    + generalize (fr_align_pos vars 0). intro H; trim H. omega.
      revert size_int; simpl. revert ALLOC Heqo H. 
      clear; intros.
      exfalso.
      eapply Mem.alloc_less_ok with (z0:=((align (small_var_space vars 0) (block_alignment sz) + Z.max 0 sz))); eauto.
      congruence.
      split. lia.
      generalize (Zmax_bound_l 0 0 sz).
      generalize (align_le (small_var_space vars 0) _ (block_alignment_pos sz)).
      lia.
Qed.

Lemma alloc_variables_right_bounds_old:
  forall vars e1 e m1 m2 b
         (AVR:alloc_variables_right e1 m1 vars  e m2)
         (MNB: Plt b (Mem.nextblock m1)),
    Mem.bounds_of_block m2 b = Mem.bounds_of_block m1 b.
Proof.
  induction vars; simpl; intros; try 
  intuition congruence.
  - inv AVR. auto.
  - inv AVR.
    generalize (alloc_variables_nextblock _ _ _ _ _ H6).
    apply IHvars with (b:=b) in H6; auto.
    intro. apply Mem.bounds_of_block_alloc_other with (b':=b) in H3.
    + congruence.
    + apply Mem.alloc_result in H3. subst. 
      cut (Plt b (Mem.nextblock m0)). clear.
      * intros. apply Plt_ne in H. auto.
      * xomega.
Qed.



Lemma alloc_variables_right_perm:
  forall vars e1 e2 m1 m2 b ofs p
         (AVR: alloc_variables_right e1 m1 vars e2 m2)
         (LT: Plt b (Mem.nextblock m1))
         (PERM: Mem.perm m2 b ofs Max p),
    Mem.perm m1 b ofs Max p.
Proof.
  induction vars; simpl; intros; inv AVR; auto.
  eapply Mem.perm_alloc_4 with (m1:=m0) (m2:=m2) in PERM; eauto.
  rewrite (Mem.alloc_result _ _ _ _ _ _ H3).
  generalize (alloc_variables_nextblock _ _ _ _ _ H6).
  intros. cut (Plt b (Mem.nextblock m0)). intros; intro; subst; xomega.
  xomega.
Qed.

Lemma avr_valid_ex:
  forall vars e1 m1 e m2 b,
    alloc_variables_right e1 m1 vars e m2 ->
    (forall id : ident, In id (map fst vars) -> e1 ! id = None) ->
    list_norepet (map fst vars) ->
    ~ Mem.valid_block m1 b ->
    Mem.valid_block m2 b ->
    exists id z,
      e ! id  = Some (b,z).
Proof.
  induction vars; simpl; intros.
  inv H. congruence.
  inv H.
  destruct (peq b b1); subst; auto.
  - exists id; exists (Z.max 0 sz).
    inv H1.
    rewrite (alloc_in_vars' _ _ _ _ _ H11  H6) with (p:=(b1,Z.max 0 sz)); auto.
    intros; eauto.
    rewrite PTree.gso by congruence. apply H0. auto.
    apply PTree.gss.
  - inv H1.
    generalize (IHvars _ _ _ _ b H11); eauto.
    intro A; apply A; auto.
    intros.
    rewrite PTree.gso by congruence.
    apply H0; auto.
    destruct  (Mem.valid_block_alloc_inv _ _ _ _ _ _ H8 b H3); auto. congruence.
Qed.

Lemma avr_norepet:
  forall e (NDBL: nodbl e),
    list_norepet (map fst (map fst (blocks_of_env e))).
Proof.
  unfold nodbl, blocks_of_env, block_of_binding; intros.
  rewrite ! map_map.
  rewrite map_ext with (g:= fun a => fst (snd a))
    by (intros; destruct a; destruct p; simpl; auto).
  assert (forall id b sz,
            In (id,(b,sz)) (PTree.elements e) ->
            ~ exists id' p,
                id' <> id /\
                e! id' = Some p /\
                fst p = b).
  intros. 
  apply PTree.elements_complete in H.
  eapply NDBL; eauto.
  assert (forall id b sz,
            In (id,(b,sz)) (PTree.elements e) ->
            ~ exists id' z,
                In (id',(b,z)) (PTree.elements e) /\
                id' <> id).
  intros. 
  apply H in H0.
  intro.
  apply H0.
  destruct H1 as [id' [z [A B]]].
  apply PTree.elements_complete in A.
  exists id'. exists (b,z).
  auto.
  clear H NDBL.
  apply list_map_norepet; auto.
  generalize (PTree.elements_keys_norepet e).
  apply (PTree_Properties.list_norepet_map).
  intros.
  destruct x as [a [b c]].
  destruct y as [d [f g]].
  generalize (H0 _ _ _ H).
  generalize (H0 _ _ _ H1).
  intros.
  simpl in *.
  intro; subst.
  apply H4.
  exists d. exists g. split; auto.
  intro; subst.
  generalize (PTree.elements_complete _ _ _ H1)
             (PTree.elements_complete _ _ _ H).
  intros A B; rewrite A in B; inv B.
  congruence.
Qed.

Lemma avr_hi_pos:
  forall vars e1 m1 e m2
         (init: Forall (fun bnds : ident * Z * Z => snd bnds >= 0) (blocks_of_env e1))
         (AVS : alloc_variables_right e1 m1 vars e m2),
    Forall (fun bnds : ident * Z * Z => snd bnds >= 0) (blocks_of_env e).
Proof.
  induction vars; simpl; intros.
  inv AVS. auto.
  inv AVS.
  apply IHvars in H6; auto.
  unfold blocks_of_env.
  apply Forall_forall.
  intros.
  rewrite in_map_iff in H.
  destruct H as [[x0 x1] [A B]].
  apply PTree.elements_complete in B.
  rewrite PTree.gsspec in B.
  revert B; destr.
  intro B; inv B. simpl. rewrite Zmax_spec; destr; omega. 
  des x1.
  unfold blocks_of_env in init.
  rewrite Forall_forall in init.
  specialize (init (b, 0, z)). rewrite in_map_iff in init.
  simpl in init.
  intros; apply init.
  unfold block_of_binding.
  exists (x0, (b, z)).
  split. auto. apply PTree.elements_correct. auto.
Qed.


Lemma avr_in_vars:
  forall vars e1 m1 e m2 i z'
         (LNR : list_norepet (map fst vars))
         (AVR : alloc_variables_right e1 m1 vars e m2)
         (B : In (i, z') vars),
   exists b : block, e ! i = Some (b, Z.max 0 z').
Proof.
  induction vars; simpl; intros; auto. exfalso; auto.
  inv AVR; inv LNR.
  destruct B.
  - inv H.
    exists b1.
    apply  alloc_in_vars_same with (id:=i) in H6; auto.
    rewrite <- H6.
    apply PTree.gss.
  - apply IHvars with (i:=i) (z':=z') in H6; auto.
Qed.

Lemma bvs_map_sup:
  forall vars z,
    small_var_space
      (map (fun id_sz : ident * Z => (fst id_sz, Z.max 0 (snd id_sz))) vars)
      z =
    small_var_space vars z.
Proof.
  induction vars; simpl; intros; auto.
  rewrite IHvars.
  rewrite ! Zmax_spec; repeat destr. unfold block_alignment, alignment_of_size; repeat destr; lia. 
Qed.

Lemma alloc_variables_dyn:
  forall e m v e' m',
    alloc_variables_right e m v e' m' ->
    Forall (fun b => ~ Mem.is_dynamic_block m b) (map fst (map fst (blocks_of_env e))) ->
    Forall (fun b => ~ Mem.is_dynamic_block m' b) (map fst (map fst (blocks_of_env e'))).
Proof.
  induction 1; simpl; intros; eauto.
  trim IHalloc_variables_right.
  rewrite Forall_forall; intros x IN.
  assert (x = b1 \/ In x (map fst (map fst (blocks_of_env e)))).
  {
    des (peq x b1). right. revert IN.
    unfold blocks_of_env, block_of_binding.
    rewrite ! map_map, ! in_map_iff; simpl.
    simpl. intros [[i [b z]] [EQ IN]].
    simpl in *. subst.
    apply PTree.elements_complete in IN.
    rewrite PTree.gsspec in IN. destr_in IN; try now inv IN.
    apply PTree.elements_correct in IN.
    exists (i, (x,z)); split; auto.
  }
  des H2.
  intro DYN; apply dyn_valid in DYN.
  generalize (alloc_variables_nextblock _ _ _ _ _ H0).
  exploit Mem.alloc_result; eauto. red in DYN. intros; subst. xomega.
  rewrite Forall_forall in H1; eauto.
  revert IHalloc_variables_right.
  apply Mem.Forall_impl'. intros.
  erewrite <- Mem.is_block_dynamic_alloc; eauto.
Qed.


Lemma alloc_variables_dyn':
  forall e m v e' m',
    alloc_variables_right e m v e' m' ->
    forall b, Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b.
Proof.
  induction 1; simpl; intros; eauto.
  tauto.
  rewrite IHalloc_variables_right. 
  eapply Mem.is_block_dynamic_alloc; eauto.
Qed.

Lemma box_span_mul:
  forall z,
    Mem.box_span (two_power_nat MA * z) = Z.to_nat z.
Proof.
  unfold Mem.box_span. intros.
  rewrite <- (Z.add_opp_r _ 1).
  rewrite (Z.add_comm _ (-1)).
  rewrite Z.mul_comm.
  rewrite (Z_div_plus (-1) z (two_power_nat MA) (Mem.tpMA_pos)).
  rewrite Mem.minus_1_div_eq. f_equal. lia. apply Mem.tpMA_pos.
Qed.


Lemma match_callstack_alloc_variables_cs:
  forall vars tm1 sp tm2 m1  e m2 cenv f1 cs le te  e1 size size' fid fns fnp fnv fnb f2
         (ALLOC: Mem.alloc tm1 0 size Normal = Some (tm2, sp))
         (SSMU: size' <= Int.max_unsigned)
         (AVS: alloc_variables_right e1 m1 vars e m2)
         (envs: forall id p, e1!id = Some p -> e!id = Some p)
         (NODBL: nodbl e1)
         (VB: forall (id : positive) (b : block) (z : Z),
                e1 ! id = Some (b, z) -> ~ Mem.valid_block m2 b)
         (init: Forall (fun bnds : ident * Z * Z => snd bnds >= 0) (blocks_of_env e1))
         (initdyn: Forall (fun b => ~ Mem.is_dynamic_block m1 b) (map fst (map fst (blocks_of_env e1))))
         (LNR: list_norepet (map fst vars))
         (size_sup: size' >= size)
         (Ccompat: cenv_compat cenv vars size')
         (Csep: cenv_separated cenv vars)
         (Csome_in: (forall id ofs, cenv!id = Some ofs -> In id (map fst vars)))
         (Esome_in: (forall id b z, e!id = Some (b,z) -> 
                                    exists z',
                                      Z.max 0 z' = z /\ In (id,z') vars))
         (in_vars: forall id, In id (map fst vars) -> e1!id = None)
         (INJ: Mem.inject true expr_inj_se f1 m1 tm1)
         (INJ': Mem.inject true expr_inj_se f2 m2 tm2)
         (inj_spec: inject_incr_cs f1 f2 sp m1 e cenv)
         (e_cenv: forall id, e ! id = None <-> cenv ! id = None)
         (MCS: match_callstack f1 m1 tm1 cs (Mem.nextblock m1) (Mem.nextblock tm1))
         (MTmps: match_temps f1 le te)
         (SSTF: size =
                small_var_space vars 0)
         (ss_blocks:  size <=
                      align (big_vars_block_space (rev (blocks_of_env e)) 0) (two_power_nat MA))
         (ss_pos: size >= 0),
    match_callstack f2 m2 tm2 (Frame cenv (mkfunction fid fns fnp fnv size fnb (Zge_le _ _ ss_pos)) e le te sp (Mem.nextblock m1) (Mem.nextblock m2) :: cs)
                    (Mem.nextblock m2) (Mem.nextblock tm2).
Proof.
  intros.
  constructor; auto.
  - xomega.
  - erewrite Mem.nextblock_alloc; eauto.
    erewrite (Mem.alloc_result) with (b:=sp); eauto.
    xomega.
  - red; intros.
    apply MTmps in H.
    destruct H as [v' [A B]]. exists v'; split; auto.
    destruct (wf_inj_expr_inj_se). eapply ei_inj_incr with (f:=f1); eauto.
    inv inj_spec; auto.
  - constructor; eauto. 
    + intros.
      destruct (e!id) eqn:?. destruct p.
      generalize Heqo; apply Esome_in in Heqo; auto.
      destruct Heqo as [z' [ZM I]].
      destruct (Ccompat id z') as [ofs [A [B [C D]]]].
      auto.
      rewrite A.
      constructor.
      eexists; eexists; repSplit; [reflexivity|reflexivity|].
      constructor.
      econstructor. inv inj_spec.
      erewrite inj_env0; eauto.
      rewrite Int.add_zero_l. auto.
      rewrite e_cenv in Heqo. rewrite Heqo; constructor.
    + eapply alloc_variables_nextblock; eauto.
    + intros.
      generalize (Esome_in _ _ _ H).
      intros [z' [ZM I]].
      revert AVS b sz H z' ZM I in_vars LNR. clear. revert vars e1 m1 e m2.
      induction vars; simpl ; intros.
      intuition congruence.
      inv AVS.
      specialize (IHvars _ _ _ _ H7).
      destruct I. 
      * inv H0.
        inv LNR.
        generalize (alloc_in_vars' _ _ _ _ _ H7 H3).
        intro A.
        rewrite A with (p:=(b1,Z.max 0 z')) in H; auto.
        inv H.
        rewrite (Mem.nextblock_alloc _ _ _ _ _ _ H4).
        apply Mem.alloc_result in H4. 
        generalize (alloc_variables_nextblock _ _ _ _ _ H7).
        subst b.
        intuition xomega.
        intros.
        rewrite PTree.gso by congruence. apply in_vars. auto.
        apply PTree.gss.
      * specialize (IHvars _ _ H _ eq_refl H0).
        inv LNR.
        generalize (alloc_variables_nextblock _ _ _ _ _ H7).
        rewrite (Mem.nextblock_alloc _ _ _ _ _ _ H4).
        cut (Ple (Mem.nextblock m1) b /\ Plt b (Mem.nextblock m0)).
        intuition xomega.
        apply IHvars; auto.
        intros.
        rewrite PTree.gso by congruence.
        apply in_vars; auto.
    +  inv inj_spec; auto.
    + intros.
      inv inj_spec.
      apply inj_same_thr0 in H0.
      rewrite H0 in H.
      clear - INJ ALLOC H.
      inv INJ.
      apply mi_mappedblocks in H.
      erewrite Mem.alloc_result; eauto.
  - red; intros id b sz ofs p Heid Hperm.
    generalize (Heid).
    apply Esome_in in Heid. 
    destruct Heid as [z' [ZM I]].
    intros.
    apply Mem.perm_bounds in Hperm.
    unfold Mem.in_bound_m in *. erewrite alloc_variables_right_bounds in Hperm; eauto.
    apply in_map with (f:=fst) in I; auto.
    {
      intros.
      generalize  (alloc_variables_right_nodbl _ _ _ _ _ AVS LNR in_vars NODBL VB).
      unfold nodbl.
      intro.
      apply H4 in H3.
      intro.
      subst.
      apply H3.
      exists id0. exists (b',sz0). repeat split; auto.
    }
  - red; intros id b sz Heid.
    generalize (Heid).
    apply Esome_in in Heid. 
    destruct Heid as [z' [ZM I]].
    intros.
    erewrite alloc_variables_right_bounds; eauto.
    apply in_map with (f:=fst) in I; auto.
    {
      intros.
      generalize  (alloc_variables_right_nodbl _ _ _ _ _ AVS LNR in_vars NODBL VB).
      unfold nodbl.
      intro.
      apply H4 in H3.
      intro.
      subst.
      apply H3.
      exists id0. exists (b',sz0). repeat split; auto.
    } 
  - unfold norepet_env.
    generalize (alloc_variables_right_nodbl _ _ _ _ _ AVS LNR in_vars NODBL VB).    
    apply avr_norepet.
  - eapply avr_hi_pos; eauto.
  - simpl. rewrite <- Mem.box_span_align in ss_blocks.
    etransitivity. eapply Mem.box_span_le. split. lia. apply ss_blocks.
    rewrite box_span_mul.
    rewrite Nat2Z.id.
    {
      transitivity (Mem.box_span (align (big_vars_block_space (rev (blocks_of_env e)) 0) (two_power_nat MA))).
      apply Mem.box_span_le. split.
      rewrite bvbs_rew. apply Zge_le, fr_align_pos8. lia.
      apply align_le. apply Mem.tpMA_pos.
      rewrite <- size_mem_blocks_big_vars.
      cut (Forall (fun bsz => (let '(b,lo,hi) := bsz in 0 <= hi - lo)) (blocks_of_env e)).
      generalize (blocks_of_env e). clear.
      unfold size_list_blocks , Mem.size_mem_blocks.
      set (f := fun acc x =>
                  align acc (two_power_nat MA) + Z.max 0 (snd x - snd (fst x))).

      induction 1; simpl; intros.
      rewrite align_0, <- box_span_0. lia. apply Mem.tpMA_pos.

      assert (forall l x,
                 align (fold_left f l x) (two_power_nat MA) =
                 align x (two_power_nat MA) + align (fold_left f l 0) (two_power_nat MA)).
      {
        clear.
        induction l; simpl; intros; eauto. rewrite align_0. lia.
        apply Mem.tpMA_pos.
        rewrite (IHl (f 0 a)).
        rewrite (IHl (f x a)).
        cut (align (f x a) (two_power_nat MA) = align x (two_power_nat MA) + align (f 0 a) (two_power_nat MA)). lia.
        unfold f. rewrite align_0. 2: apply Mem.tpMA_pos.
        rewrite <- align_distr. reflexivity. apply Mem.tpMA_pos.
      }

      rewrite H1.

      etransitivity. apply box_span_add.
      {
        apply Z.le_ge.
        clear. generalize 0.
        induction l; simpl; intros.
        apply align_le. apply Mem.tpMA_pos.
        etransitivity. 2: apply IHl. unfold f.
        generalize (align_le z (two_power_nat MA)). generalize Mem.tpMA_pos. lia.
      }

      {
        unfold f.
        rewrite align_0. 2: apply Mem.tpMA_pos. simpl.
        apply Zle_ge. etransitivity.
        2: apply align_le. lia. apply Mem.tpMA_pos.
      }
      rewrite Mem.fold_left_plus_rew.
      cut (Mem.box_span (align (f Z0 x) (two_power_nat MA)) <= Mem.box_span (size_of_block x))%nat. lia.


      transitivity (Mem.box_span (align (size_of_block x) (two_power_nat MA))).
      apply Mem.box_span_le.
      split.
      etransitivity. 2: apply align_le. unfold f. rewrite align_0; simpl. lia.
      apply Mem.tpMA_pos.       apply Mem.tpMA_pos.
      unfold f. rewrite align_0; simpl. unfold size_of_block. des x. des p. rewrite Z.max_r. lia.
      lia. apply Mem.tpMA_pos. 
      rewrite box_span_small_align'. lia. des x. des p. lia.
      exploit avr_hi_pos. eauto. eauto.
      clear.
      rewrite ! Forall_forall in *.
      intros H x IN.
      des x. des p.
      exploit in_blocks_of_env_inv; eauto.
      intros; dex. des H0. apply H in IN. destr. lia.
    }
    {
      rewrite bvbs_rew.
      apply fr_align_pos8. lia.
    }
  - simpl. red.
    intros.
    generalize (Mem.perm_alloc_2 _ _ _ _ _ _ ALLOC ofs Cur H).
    auto.
  - simpl.
    rewrite (Mem.bounds_of_block_alloc _ _ _ _ _ _ ALLOC). rewrite Zmax_r. auto.
    etransitivity.
    apply Zge_le. eauto.
    lia.
  - eapply alloc_variables_dyn; eauto.
  - rewrite <- Mem.is_block_dynamic_alloc; eauto.
    intro DYN; apply dyn_valid in DYN; eapply Mem.fresh_block_alloc in DYN; eauto.
  - rewrite (Mem.alloc_result _ _ _ _ _ _ ALLOC).
    apply (match_callstack_invariant _ _ _ _ _ _ _ _ _ MCS); try tauto.
    + inv inj_spec; auto.
    + intros.
      apply (alloc_variables_right_perm _ _ _ _ _ _ _ _ AVS H H0).
    + intros.
      apply (alloc_variables_right_bounds_old _ _ _ _ _ _ AVS H).
    + intros b LT.
      rewrite (Mem.bounds_of_block_alloc_other _ _ _ _ _ _ ALLOC). auto.
      rewrite (Mem.alloc_result _ _ _ _ _ _ ALLOC). intro; subst; xomega.
    + intros sp0 ofs PSM PERM.
      eapply Mem.perm_alloc_1; eauto. 
    + intros. eapply alloc_variables_dyn'; eauto.
    + intros. eapply Mem.is_block_dynamic_alloc; eauto.
    + inv inj_spec; auto.
    + inv inj_spec; auto.
      intros.
      eapply inj_above_thr_tm0; eauto.
      erewrite Mem.alloc_result; eauto.
    + red; intros.
      destruct (plt b (Mem.nextblock m1)).
      * erewrite alloc_variables_right_bounds_old in H; eauto.
        generalize (match_callstack_all_blocks_injected _ _ _ _ _ _ MCS).
        intro A.
        apply  (A _ _ _ H)  in H0.
        inv inj_spec. red in inj_incr0.
        destruct (f1 b) eqn:?; intuition try congruence.
        destruct p0. 
        erewrite inj_incr0 in H1; eauto. 
      * assert (Mem.valid_block m2 b).
        eapply Mem.bounds_of_block_valid; eauto. omega.
        destruct (avr_valid_ex _ _ _ _ _ _ AVS in_vars LNR n H1) as [id [z A]].
        erewrite alloc_variables_right_bounds in H; eauto.
        inv inj_spec.
        inv H.
        destruct (cenv!id) eqn:?.
        erewrite inj_env0; eauto.
        congruence.
        rewrite <- e_cenv in Heqo. congruence.
        apply Esome_in in A; eauto.
        destruct A as [z' [ZM I]].
        apply in_map with (f:=fst) in I; auto.
        generalize (alloc_variables_right_nodbl _ _ _ _ _ AVS LNR in_vars NODBL VB).
        clear; intros. intro; subst.
        destruct (H id b' sz H3).
        unfold block in *.
        exists id0; exists (b',sz').
        repeat split; auto.
Qed.

Lemma avr_in_not_none:
  forall vars e1 m1 e m2 id
         (AVS : alloc_variables_right e1 m1 vars e m2)
         (IN: In id (map fst vars)),
    e ! id <> None.
Proof.
  induction 1; simpl; intros.
  intuition.
  destruct IN; subst; auto.
  apply alloc_in_vars'' with (id:=id) (p:=(b1,Z.max 0 sz)) in AVS; auto.
  apply PTree.gss.
Qed.
      

(** Properties of the compilation environment produced by [build_compilenv] *)

Remark assign_variable_incr:
  forall id sz cenv stksz cenv' stksz',
  assign_variable (cenv, stksz) (id, sz) = (cenv', stksz') -> stksz <= stksz'.
Proof.
  simpl; intros. inv H. 
  generalize (align_le stksz _ (block_alignment_pos sz) ).
  assert (0 <= Zmax 0 sz). apply Zmax_bound_l. omega.
  omega.
Qed.

Remark assign_variables_incr:
  forall vars cenv sz cenv' sz',
  assign_variables (cenv, sz) vars = (cenv', sz') -> sz <= sz'.
Proof.
  induction vars; intros until sz'.
  simpl; intros. inv H. omega.
Opaque assign_variable.
  destruct a as [id s]. simpl. intros.
  destruct (assign_variable (cenv, sz) (id, s)) as [cenv1 sz1] eqn:?. 
  apply Zle_trans with sz1. eapply assign_variable_incr; eauto. eauto.
Transparent assign_variable.
Qed.

Remark inj_offset_aligned_block:
  forall stacksize sz,
  Mem.inj_offset_aligned (align stacksize (block_alignment sz)) sz.
Proof.
  intros; red; intros.
  apply Zdivides_trans with (block_alignment sz).
  unfold align_chunk.  unfold block_alignment.
  generalize Zone_divide; intro.
  generalize Zdivide_refl; intro.
  assert (2 | 4). exists 2; auto.
  assert (2 | 8). exists 4; auto.
  assert (4 | 8). exists 2; auto.
  exists 1; lia.
  apply align_divides. apply block_alignment_pos.
Qed.

Lemma assign_variable_sound:
  forall cenv1 sz1 id sz cenv2 sz2 vars,
  assign_variable (cenv1, sz1) (id, sz) = (cenv2, sz2) ->
  ~In id (map fst vars) ->
  0 <= sz1 ->
  cenv_compat cenv1 vars sz1 ->
  cenv_separated cenv1 vars ->
  cenv_compat cenv2 (vars ++ (id, sz) :: nil) sz2
  /\ cenv_separated cenv2 (vars ++ (id, sz) :: nil).
Proof.
  unfold assign_variable; intros until vars; intros ASV NOREPET POS COMPAT SEP.
  inv ASV.
  assert (LE: sz1 <= align sz1 (two_power_nat MA)). apply align_le. auto. 
  assert (EITHER: forall id' sz',
             In (id', sz') (vars ++ (id, sz) :: nil) ->
             In (id', sz') vars /\ id' <> id \/ (id', sz') = (id, sz)).
  {
    intros. rewrite in_app in H. destruct H. 
    left; split; auto. red; intros; subst id'. elim NOREPET. 
    change id with (fst (id, sz')). apply in_map; auto.
    simpl in H. destruct H. auto. contradiction.
  }
  split; red; intros.
  - apply EITHER in H. destruct H as [[P Q] | P].
    + exploit COMPAT; eauto. intros [ofs [A [B [C D]]]]. 
      exists ofs.
      split. rewrite PTree.gso; auto.
      split. auto. split. auto. transitivity sz1. auto. 
      rewrite Zmax_spec.
      generalize (align_le sz1 _ (block_alignment_pos sz)). destr; omega.
    + inv P. exists (align sz1 (block_alignment sz)).
      split. apply PTree.gss.
      split. unfold Mem.inj_offset_aligned. intros. 
      apply Zdivides_trans with (y:=(block_alignment sz)).
      unfold block_alignment, alignment_of_size; repeat destruct zlt;  try (exists 8; auto; fail);
      try (exists 4; auto; fail);
      try (exists 2; auto; fail);
      try (exists 1; auto; fail); try omega.
      apply align_divides. apply block_alignment_pos.
      split. transitivity sz1; auto.
      apply (align_le _ _ (block_alignment_pos sz)).
      omega.
  - apply EITHER in H; apply EITHER in H0.
    destruct H as [[P Q] | P]; destruct H0 as [[R S] | R].
    + rewrite PTree.gso in *; auto. eapply SEP; eauto. 
    + inv R. rewrite PTree.gso in H1; auto. rewrite PTree.gss in H2; inv H2.
      exploit COMPAT; eauto. intros [ofs [A [B [C D]]]]. 
      assert (ofs = ofs1) by congruence. subst ofs. 
      left. transitivity (ofs1 + Z.max 0 sz0). 
      generalize (Zmax_bound_r sz0 0 sz0). omega.
      transitivity sz1; auto.
      apply (align_le _ _ (block_alignment_pos sz)).
    + inv P. rewrite PTree.gso in H2; auto. rewrite PTree.gss in H1; inv H1.
      exploit COMPAT; eauto. intros [ofs [A [B [C D]]]]. 
      assert (ofs = ofs2) by congruence. subst ofs. 
      right. 
      transitivity (ofs2 + Z.max 0 sz2). 
      generalize (Zmax_bound_r sz2 0 sz2). omega.
      transitivity sz1; auto.
      apply (align_le _ _ (block_alignment_pos sz)).
    + congruence.
Qed.

Lemma assign_variables_sound:
  forall vars' cenv1 sz1 cenv2 sz2 vars,
  assign_variables (cenv1, sz1) vars' = (cenv2, sz2) ->
  list_norepet (map fst vars' ++ map fst vars) ->
  0 <= sz1 ->
  cenv_compat cenv1 vars sz1 ->
  cenv_separated cenv1 vars ->
  cenv_compat cenv2 (vars ++ vars') sz2 /\ cenv_separated cenv2 (vars ++ vars').
Proof.
  induction vars'; simpl; intros.
  rewrite app_nil_r. inv H; auto.
  destruct a as [id sz].
  simpl in H0. inv H0. rewrite in_app in H6.
  rewrite list_norepet_app in H7. destruct H7 as [P [Q R]].
  destruct (assign_variable (cenv1, sz1) (id, sz)) as [cenv' sz'] eqn:?.
  exploit assign_variable_sound.
    eauto.
    instantiate (1 := vars). tauto.
    auto. auto. auto.
  intros [A B].
  exploit IHvars'.
    eauto.
    instantiate (1 := vars ++ ((id, sz) :: nil)).
    rewrite list_norepet_app. split. auto. 
    split. rewrite map_app. apply list_norepet_append_commut. simpl. constructor; auto. 
    rewrite map_app. simpl. red; intros. rewrite in_app in H4. destruct H4. 
    eauto. simpl in H4. destruct H4. subst y. red; intros; subst x. tauto. tauto.
    generalize (assign_variable_incr _ _ _ _ _ _ Heqp). omega.
    auto. auto.
  rewrite app_ass. auto. 
Qed.

Lemma build_compilenv_sound:
  forall f cenv sz,
  build_compilenv f = (cenv, sz) ->
  list_norepet (map fst (Csharpminor.fn_vars f)) ->
  cenv_compat cenv (Csharpminor.fn_vars f) sz /\ cenv_separated cenv (Csharpminor.fn_vars f).
Proof.
  unfold build_compilenv; intros. 
  set (vars1 := Csharpminor.fn_vars f) in *.
  generalize (varsort'_permut vars1). intros P.
  set (vars2 := varsort' vars1) in *.
  assert (cenv_compat cenv vars2 sz /\ cenv_separated cenv vars2).
    change vars2 with (nil ++ vars2).
    eapply assign_variables_sound.
    eexact H.
    simpl. rewrite app_nil_r. apply permutation_norepet with (map fst vars1); auto.
    apply Permutation_map. auto.
    omega. 
    red; intros. contradiction.
    red; intros. contradiction.
  destruct H1 as [A B]. split.
  red; intros. apply A. apply Permutation_in with vars1; auto. 
  red; intros. eapply B; eauto; apply Permutation_in with vars1; auto.
Qed.

Lemma assign_variables_domain:
  forall id vars cesz,
  (fst (assign_variables cesz vars))!id <> None ->
  (fst cesz)!id <> None \/ In id (map fst vars).
Proof.
  induction vars; simpl; intros.
  auto.
  exploit IHvars; eauto. unfold assign_variable. destruct a as [id1 sz1].
  destruct cesz as [cenv stksz]. simpl. 
  rewrite PTree.gsspec. destruct (peq id id1). auto. tauto.
Qed.

Lemma build_compilenv_domain:
  forall f cenv sz id ofs,
  build_compilenv f = (cenv, sz) ->
  cenv!id = Some ofs -> In id (map fst (Csharpminor.fn_vars f)).
Proof.
  unfold build_compilenv; intros. 
  set (vars1 := Csharpminor.fn_vars f) in *.
  generalize (varsort'_permut vars1). intros P.
  set (vars2 := varsort' vars1) in *.
  generalize (assign_variables_domain id vars2 (PTree.empty Z, 0)).
  rewrite H. simpl. intros. destruct H1. congruence. 
  rewrite PTree.gempty in H1. congruence.
  apply Permutation_in with (map fst vars2); auto.
  apply Permutation_map. apply Permutation_sym; auto.
Qed.

Lemma match_callstack_alloc_variables:
  forall vars tm1 sp tm2 m1  e m2 cenv f1 cs le te  e1 size size' fid fns fnp fnv fnb 
         (ALLOC: Mem.alloc tm1 0 (size) Normal = Some (tm2, sp))
         (SSMU: size' <= Int.max_unsigned)
         (AVS: alloc_variables_right e1 m1 vars e m2)
         (init: Forall (fun bnds : ident * Z * Z => snd bnds >= 0) (blocks_of_env e1))
         (vars_fresh: 
            forall v b ofs,
              e!v = Some (b,ofs) ->
              ~Mem.valid_block m1 b
         )
         (vars_fresh':
            forall id b z,
              e1!id = Some (b,z) ->
              ~ Mem.valid_block m2 b
         )
         (NDBL: nodbl e1)
         (LNR: list_norepet (map fst vars))
         (size_sup: size' >= size )
         (Ccompat: cenv_compat cenv vars size')
         (Csep: cenv_separated cenv vars)
         (cenv_spec: True -> fst (assign_variables (PTree.empty Z, 0) (rev vars)) = cenv)
         (Csome_in: (forall id ofs, cenv!id = Some ofs -> In id (map fst vars)))
         (Esome_in: (forall id b z, e!id = Some (b,z) -> 
                                    exists z',
                                      Z.max 0 z' = z /\
                                      In (id,z') vars))
         (in_vars: forall id, In id (map fst vars) -> e1!id = None)
         (INJ: Mem.inject true expr_inj_se f1 m1 tm1)
         (MCS: match_callstack f1 m1 tm1 cs (Mem.nextblock m1) (Mem.nextblock tm1))
         (MTmps: match_temps f1 le te)
         (SSTF:  size =
                (small_var_space vars 0) )
         (ss_blocks:  size <= align (big_vars_block_space (rev (blocks_of_env e)) 0) (two_power_nat MA))
         (ss_pos: size >= 0)
         (init_dyn:    Forall (fun b : positive => ~ Mem.is_dynamic_block m1 b)
                              (map fst (map fst (blocks_of_env e1)))),
  exists f2,
    match_callstack f2 m2 tm2 (Frame cenv (mkfunction fid fns fnp fnv size fnb (Zge_le _ _ ss_pos)) e le te sp (Mem.nextblock m1) (Mem.nextblock m2) :: cs)
                    (Mem.nextblock m2) (Mem.nextblock tm2)
    /\ Mem.inject true expr_inj_se f2 m2 tm2.
Proof.
  intros.
    destruct (match_callstack_alloc_variables_inject
                _ _ _ _ _ _ _ _ _ _ cenv
                AVS
                (alloc_variables_right_nodbl _ _ _ _ _ AVS LNR
                                             in_vars NDBL vars_fresh')
                LNR
                in_vars
                vars_fresh ALLOC INJ SSTF )
    as [f2 [MI' INJ_incr']]; auto.
  - split; try omega.
  - (exists f2; split; auto).
    eapply match_callstack_alloc_variables_cs; eauto.
    + intros id p H.
      erewrite (alloc_in_vars' _ _ _ _ _ AVS)  with (p:=p); eauto.
    + intros. 
      destruct (in_dec peq id (map fst vars)).
      * assert (exists z, In (id,z) vars).
        apply in_map_iff in i.
        destruct i as [[i z0] [I J]].
        exists z0; auto. simpl in *; subst. auto.
        destruct H as [z0 K].
        destruct (Ccompat _ _ K) as [ofs [A [B [C D]]]].
        rewrite A.
        generalize (avr_in_not_none _ _ _ _ _ id AVS i).
        intuition congruence.
      * destruct (e!id) eqn:?.
        destruct p.
        apply Esome_in in Heqo; intuition try congruence.
        destruct Heqo as [z' [ZM I]].
        apply in_map with (f:=fst) in I; auto. simpl in *; intuition congruence.
        destruct (cenv!id) eqn:?. 
        apply Csome_in in Heqo0; intuition try congruence.
        tauto.
Qed.

(** Initialization of C#minor temporaries and Cminor local variables. *)

Lemma create_undef_temps_val:
  forall id temps v,
    (create_undef_temps temps)!id = Some v ->
    In id temps /\ v = Eval Vundef.
Proof.
   induction temps; simpl; intros.
  rewrite PTree.gempty in H. congruence.
  rewrite PTree.gsspec in H. destruct (peq id a).
  split. auto. congruence.
  exploit IHtemps; eauto. tauto. 
Qed.

Fixpoint set_params' (vl: list expr_sym) (il: list ident) (te: Cminor.env) : Cminor.env :=
  match il, vl with
  | i1 :: is, v1 :: vs => set_params' vs is (PTree.set i1 v1 te)
  | i1 :: is, nil => set_params' nil is (PTree.set i1 (Eval Vundef) te)
  | _, _ => te
  end.

Lemma bind_parameters_agree_rec:
  forall f vars vals tvals le1 le2 te,
  bind_parameters vars vals le1 = Some le2 ->
  expr_list_inject  f vals tvals ->
  match_temps f le1 te ->
  match_temps f le2 (set_params' tvals vars te).
Proof.
  Opaque PTree.set.
  induction vars; simpl; intros.
  - destruct vals; try discriminate. inv H. inv H0. auto. 
  - destruct vals; try discriminate. inv H0.
    simpl. eapply IHvars; eauto.
    red; intros. rewrite PTree.gsspec in *. destruct (peq id a). 
    inv H0. exists b1; auto.
    apply H1; auto.
Qed.

Lemma set_params'_outside:
  forall id il vl te, ~In id il -> (set_params' vl il te)!id = te!id.
Proof.
  induction il; simpl; intros. auto. 
  destruct vl; rewrite IHil.
  apply PTree.gso. intuition. intuition.
  apply PTree.gso. intuition. intuition.
Qed.

Lemma set_params'_inside:
  forall id il vl te1 te2,
    In id il ->
    (set_params' vl il te1)!id = (set_params' vl il te2)!id.
Proof.
    induction il; simpl; intros.
  contradiction.
  destruct vl; destruct (List.in_dec peq id il); auto;
  repeat rewrite set_params'_outside; auto;
  assert (a = id) by intuition; subst a; repeat rewrite PTree.gss; auto.
Qed.

Lemma set_params_set_params':
  forall il vl id,
  list_norepet il ->
  (set_params vl il)!id = (set_params' vl il (PTree.empty expr_sym))!id.
Proof.
 induction il; simpl; intros.
  auto.
  inv H. destruct vl. 
  rewrite PTree.gsspec. destruct (peq id a). 
  subst a. rewrite set_params'_outside; auto. rewrite PTree.gss; auto.
  rewrite IHil; auto.
  destruct (List.in_dec peq id il). apply set_params'_inside; auto.
  repeat rewrite set_params'_outside; auto. rewrite PTree.gso; auto. 
  rewrite PTree.gsspec. destruct (peq id a). 
  subst a. rewrite set_params'_outside; auto. rewrite PTree.gss; auto.
  rewrite IHil; auto.
  destruct (List.in_dec peq id il). apply set_params'_inside; auto.
  repeat rewrite set_params'_outside; auto. rewrite PTree.gso; auto. 
Qed.

Lemma set_locals_outside:
  forall e id il,
  ~In id il -> (set_locals il e)!id = e!id.
Proof.
  induction il; simpl; intros.
  auto.
  rewrite PTree.gso. eauto. eauto.
Qed.

Lemma set_locals_inside:
  forall e id il,
  In id il -> 
  (set_locals il e)!id = Some (Eval Vundef).
Proof.
  induction il; simpl; intros.
  contradiction.
  destruct H. subst a. apply PTree.gss. 
  rewrite PTree.gsspec. destr.
Qed.

Lemma set_locals_set_params':
  forall vars vals params id,
  list_norepet params ->
  list_disjoint params vars ->
  (set_locals vars (set_params vals params)) ! id =
  (set_params' vals params (set_locals vars (PTree.empty expr_sym) )) ! id.
Proof.
  intros. destruct (in_dec peq id vars).
  - assert (~In id params).
    { apply list_disjoint_notin with vars; auto. apply list_disjoint_sym; auto. }
    rewrite (set_locals_inside (set_params vals params) id vars i). 
    rewrite set_params'_outside; auto.
    rewrite (set_locals_inside (PTree.empty expr_sym) id vars i).  auto. 
  - rewrite set_locals_outside; auto. rewrite set_params_set_params'; auto. 
    destruct (in_dec peq id params). 
    + apply set_params'_inside; auto.
    + repeat rewrite set_params'_outside; auto.
      rewrite set_locals_outside; auto.
Qed.

Lemma bind_parameters_agree:
  forall f params temps vals tvals le,
  bind_parameters params vals (create_undef_temps temps) = Some le ->
  expr_list_inject  f vals tvals ->
  list_norepet params ->
  list_disjoint params temps ->
  match_temps f le (set_locals temps (set_params tvals params)).
Proof.
  intros; red; intros. 
  exploit bind_parameters_agree_rec; eauto.
  instantiate (1 := set_locals temps (PTree.empty expr_sym)).
  
  red; intros. exploit create_undef_temps_val; eauto. intros [A B]. subst v0.
  exists (Eval Vundef); split. apply set_locals_inside; auto.
  apply expr_inj_se_vundef.

  intros [v' [A B]]. exists v'; split; auto.
  rewrite <- A. apply set_locals_set_params'; auto.  
Qed.

Lemma bvs_map_sup':
  forall vars z,
    big_var_space
      (map (fun id_sz : ident * Z => (fst id_sz, Z.max 0 (snd id_sz))) vars)
      z =
    big_var_space vars z.
Proof.
  induction vars; simpl; intros; auto.
  rewrite IHvars.
  rewrite ! Zmax_spec; repeat destr. 
Qed.


Lemma avr_size_vars:
  forall vars  m1 e m2
         (LNR: list_norepet (map fst vars))
         (AVR: alloc_variables_right empty_env m1 vars e m2)
         (He1: forall id : ident, In id (map fst vars) -> empty_env ! id = None)
         (Hnodbl: nodbl empty_env)
  (He1vb: forall (id : positive) (b : block) (z : Z),
            empty_env ! id = Some (b, z) -> ~ Mem.valid_block m2 b),
    align (big_var_space vars 0) (two_power_nat MA) =
    align (big_vars_block_space ( (blocks_of_env e)) 0) (two_power_nat MA).
Proof.
  intros.
  assert (Permutation
            (map (fun id_sz => (fst id_sz, Z.max 0 (snd id_sz))) vars)
            (map (fun id_b_sz => (fst id_b_sz, snd (snd id_b_sz))) (PTree.elements e))).
  - apply NoDup_Permutation.
    + rewrite list_norepet_NoDup.
      apply PTree_Properties.list_norepet_map with (f:=fst).
      rewrite ! map_map.
      simpl.
      auto.
    + generalize (alloc_variables_right_nodbl _ _ _ _ _ AVR LNR He1 Hnodbl He1vb).
      intro N.
      rewrite list_norepet_NoDup.
      generalize (PTree.elements_keys_norepet e).
      intro A. apply PTree_Properties.list_norepet_map in A.
      apply list_map_norepet; auto.
      intros.
      des x; des y.
      intro; inv H2.
      red in N.
      apply PTree.elements_complete in H0.
      apply PTree.elements_complete in H.
      rewrite H in H0; inv H0. congruence.
    + intros.
      destruct x.
      rewrite ! in_map_iff.
      cut ((exists z', Z.max 0 z' = z /\ (In (i,z') vars)) <->
           (exists b, e ! i = Some (b, z))).
      intro A.
      split. intros [[bb zz] [C D]]. simpl in C; inv C.
      destruct A as [A B].
      destruct A as [b C].
      exists zz; auto.
      exists (i,(b,Z.max 0 zz)); split; auto.
      apply PTree.elements_correct. auto.
      intros [[p [b zz]] [C B]]. inv C; simpl in *.
      apply PTree.elements_complete in B.
      destruct A as [A C].
      destruct C as [z' [ZM I]].
      exists b; auto.
      exists (i,z'). simpl. split; subst; auto.
      split.
      * intros [z' [A B]].
        subst.
        eapply avr_in_vars in AVR; eauto.
      * intros [b A].
        apply (alloc_in_vars_domain _ _ _ _ _ AVR) with (b:=b); auto.
        rewrite PTree.gempty; auto.
  - rewrite bvbs_rew.
    rewrite <- bvs_map_sup'.
    rewrite (fr_permut' _ _ 0 H).
    unfold blocks_of_env.
    unfold block_of_binding; simpl.
    unfold big_var_space.
    f_equal.
    rewrite ! frmap.
    apply frext.
    intros (a&b&c) y; simpl.
    rewrite Z.sub_0_r. omega.
Qed.
 
Lemma avr_size_vars':
  forall vars  m1 e m2
         (LNR: list_norepet (map fst vars))
         (AVR: alloc_variables_right empty_env m1 vars e m2)
         (He1: forall id : ident, In id (map fst vars) -> empty_env ! id = None)
         (Hnodbl: nodbl empty_env)
         (He1vb: forall (id : positive) (b : block) (z : Z),
             empty_env ! id = Some (b, z) -> ~ Mem.valid_block m2 b),
    size_list_blocks (map (fun isz : ident * Z => let (_, sz0) := isz in Z.max 0 sz0) vars)
    = size_list_blocks (map size_of_block (blocks_of_env e)).
Proof.
  intros.
  assert (Permutation
            (map (fun id_sz => (fst id_sz, Z.max 0 (snd id_sz))) vars)
            (map (fun id_b_sz => (fst id_b_sz, snd (snd id_b_sz))) (PTree.elements e))).
  - apply NoDup_Permutation.
    + rewrite list_norepet_NoDup.
      apply PTree_Properties.list_norepet_map with (f:=fst).
      rewrite ! map_map.
      simpl.
      auto.
    + generalize (alloc_variables_right_nodbl _ _ _ _ _ AVR LNR He1 Hnodbl He1vb).
      intro N.
      rewrite list_norepet_NoDup.
      generalize (PTree.elements_keys_norepet e).
      intro A. apply PTree_Properties.list_norepet_map in A.
      apply list_map_norepet; auto.
      intros.
      des x; des y.
      intro; inv H2.
      red in N.
      apply PTree.elements_complete in H0.
      apply PTree.elements_complete in H.
      rewrite H in H0; inv H0. congruence.
    + intros.
      destruct x.
      rewrite ! in_map_iff.
      cut ((exists z', Z.max 0 z' = z /\ (In (i,z') vars)) <->
           (exists b, e ! i = Some (b, z))).
      intro A.
      split. intros [[bb zz] [C D]]. simpl in C; inv C.
      destruct A as [A B].
      destruct A as [b C].
      exists zz; auto.
      exists (i,(b,Z.max 0 zz)); split; auto.
      apply PTree.elements_correct. auto.
      intros [[p [b zz]] [C B]]. inv C; simpl in *.
      apply PTree.elements_complete in B.
      destruct A as [A C].
      destruct C as [z' [ZM I]].
      exists b; auto.
      exists (i,z'). simpl. split; subst; auto.
      split.
      * intros [z' [A B]].
        subst.
        eapply avr_in_vars in AVR; eauto.
      * intros [b A].
        apply (alloc_in_vars_domain _ _ _ _ _ AVR) with (b:=b); auto.
        rewrite PTree.gempty; auto.
  - unfold blocks_of_env.
    unfold block_of_binding; simpl.
    unfold size_list_blocks.
    unfold big_var_space.
    apply Mem.fold_left_plus_permut.
    apply Permutation_map.
    apply Permutation_map with (f:=snd) in H.
    rewrite map_map in H. simpl in H.
    rewrite map_map in H. simpl in H.
    unfold size_of_block. rewrite map_map. simpl.
    erewrite list_map_exten with (l:=vars).
    erewrite list_map_exten with (l:=PTree.elements e). apply H.
    simpl; intros. des x. des p0. lia.
    simpl; intros. des x.
Qed.


Lemma avr_size_vars'':
  forall vars  m1 e m2
         (LNR: list_norepet (map fst vars))
         (AVR: alloc_variables_right empty_env m1 vars e m2),
    size_list_blocks (map (fun isz : ident * Z => let (_, sz0) := isz in Z.max 0 sz0) vars)
    = size_list_blocks (map size_of_block (blocks_of_env e)).
Proof.
  intros.
  eapply avr_size_vars'; eauto.
  intros; apply PTree.gempty.
  unfold nodbl. intros id b sz. rewrite PTree.gempty; congruence.
  intros id b sz. rewrite PTree.gempty; congruence.
Qed.


(** The main result in this section. *)



Theorem match_callstack_function_entry:
  forall fn cenv tf m e m' tm tm' sp f cs args targs le sz
         (TRF: transl_function fn = OK tf)
         (SSle: sz <= tf.(fn_stackspace))
         (BCE: build_compilenv fn = (cenv, sz))
         (SSMU: tf.(fn_stackspace)  <= Int.max_unsigned)
         (LNR: list_norepet (map fst (Csharpminor.fn_vars fn)))
         (LNRparam: list_norepet (Csharpminor.fn_params fn))
         (PAR_TMP:list_disjoint (Csharpminor.fn_params fn) (Csharpminor.fn_temps fn))
         (AVR: alloc_variables_right Csharpminor.empty_env m (rev (varsort' (Csharpminor.fn_vars fn))) e m')
         (BP: bind_parameters (Csharpminor.fn_params fn) args 
                              (create_undef_temps fn.(fn_temps)) = Some le)
         (ELI: expr_list_inject  f args targs)
         (ALLOC: Mem.alloc tm 0 ((tf.(fn_stackspace))) Normal = Some (tm', sp))
         (MCS: match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm))
         (MI: Mem.inject true expr_inj_se f m tm)
   ,
    let te := set_locals (Csharpminor.fn_temps fn) (set_params targs (Csharpminor.fn_params fn)) in
    exists f',
      match_callstack f' m' tm'
                      (Frame cenv tf e le te sp (Mem.nextblock m) (Mem.nextblock m')  :: cs)
                      (Mem.nextblock m') (Mem.nextblock tm')
      /\ Mem.inject true expr_inj_se f' m' tm'.
Proof.
  intros. 
  generalize (build_compilenv_sound _ _ _ BCE LNR).  intros [C1 C2].
  destruct tf; simpl in *.
  generalize (alloc_variables_alloc_sp _ _ TRF). simpl.
  intro EQ.
  generalize (fr_align_pos (rev (varsort' (Csharpminor.fn_vars fn))) 0).
  intro ss_pos. trim ss_pos. omega. rewrite <- EQ in ss_pos.
  replace (fn_stackspace_pos) with (Zge_le _ _ ss_pos).
  eapply match_callstack_alloc_variables with (size':=fn_stackspace); eauto.
  - unfold blocks_of_env. unfold empty_env. simpl. constructor.
  - clear - AVR. 
    revert AVR.
    assert (forall v b z, empty_env ! v = Some (b,z) -> ~ Mem.valid_block m b).
    {
      intros v b z; rewrite PTree.gempty. intuition congruence.
    }
    generalize (rev (varsort' (Csharpminor.fn_vars fn))) m e m' empty_env H . clear.
    induction l; simpl; intros. inv AVR.
    apply H in H0; auto.
    inv AVR. 
    assert (
        (forall (v : positive) (b : block) (z : Z),
           (PTree.set id (b1,Z.max 0 sz) e0) ! v = Some (b, z) -> ~ Mem.valid_block m b) ->
        forall (v : positive) (b : block) (ofs : Z),
        e ! v = Some (b, ofs) -> ~ Mem.valid_block m b).
    {
      intros. eapply IHl in H8; eauto.
    } clear IHl.
    assert ((forall (v : positive) (b0 : block) (z : Z),
        (PTree.set id (b1, Z.max 0 sz) e0) ! v = Some (b0, z) ->
        ~ Mem.valid_block m b0)).
    {
      intros.
      rewrite PTree.gsspec in H2.
      destruct (peq v0 id); subst; auto.
      inv H2.
      rewrite (Mem.alloc_result _ _ _ _ _ _ H5).
      generalize (alloc_variables_nextblock _ _ _ _ _ H8).
      unfold Mem.valid_block. xomega.
      apply H in H2; auto.
    }
    specialize (H1 H2).
    apply H1 in H0; auto. 
  - intros id b z. rewrite PTree.gempty; intuition congruence.
  - red. intros id b sz'. rewrite PTree.gempty; intuition congruence.
  - rewrite map_rev. 
    apply list_norepet_rev.
    generalize (varsort'_permut (Csharpminor.fn_vars fn)). intro.
    apply Permutation_map with (f:=fst) in H.
    eapply permutation_norepet; eauto.
  - omega.
  - red; intros. 
    apply in_rev in H. 
    generalize (varsort'_permut (Csharpminor.fn_vars fn)). intro.
    apply Permutation_sym in H0.
    eapply Permutation_in in H; eauto.
    red in C1.
    apply C1 in H.
    destruct H; intuition.
    exists x; repeat split; auto.
  - red; intros.
    generalize (varsort'_permut (Csharpminor.fn_vars fn)). intro.
    symmetry in H4.
    apply in_rev in H.
    apply in_rev in H0.
    eapply Permutation_in in H; eauto. 
    eapply Permutation_in in H0; eauto. 
  - revert BCE. unfold build_compilenv.
    rewrite rev_involutive.
    auto.
    intro A; rewrite A. simpl; auto.
  - intros.
    generalize (build_compilenv_domain _ _ _ _ _ BCE H). intro.
    rewrite map_rev.
    rewrite in_rev. rewrite rev_involutive.
    generalize (varsort'_permut (Csharpminor.fn_vars fn)). intro.
    apply Permutation_map with (f:=fst) in H1.
    eapply Permutation_in; eauto.
  - intros.
    generalize AVR.
    apply avr_hi_pos in AVR.
    rewrite Forall_forall in AVR.
    generalize H. apply in_blocks_of_env in H.
    apply AVR in H. simpl in H.
    intros.
    eapply (alloc_in_vars_domain _ _ _ _ _ AVR0) in H0; eauto.
    clear - LNR.
    rewrite map_rev. 
    apply list_norepet_rev.
    generalize (varsort'_permut (Csharpminor.fn_vars fn)). intro.
    apply Permutation_map with (f:=fst) in H.
    eapply permutation_norepet; eauto.
    intros; rewrite PTree.gempty; auto.
    intros; rewrite PTree.gempty; auto.
    unfold blocks_of_env, empty_env; simpl. constructor.
  - intros; rewrite PTree.gempty; auto.
  -   eapply bind_parameters_agree; eauto.
  - generalize (alloc_variables_alloc_sp _ _ TRF). simpl.
    intro; subst.
    refine (Zle_trans _ _ _ (sp_le_vars_right _) _).
    rewrite bvbs_rew. rewrite (fr_permut' _ _ _ (Permutation_rev (map _ _))).
    rewrite map_rev. rewrite rev_involutive.
    rewrite <- bvbs_rew.
    etransitivity.
    apply align_le with (y:=two_power_nat MA); auto. 
    erewrite (avr_size_vars); eauto. lia.
    + rewrite map_rev.
      apply list_norepet_rev.
      generalize (varsort'_permut (Csharpminor.fn_vars fn)). intro.
      apply Permutation_map with (f:=fst) in H0.
      eapply permutation_norepet; eauto. 
    + intros; rewrite PTree.gempty; auto.
    + red; intros id b sz'. rewrite PTree.gempty; auto. congruence.
    + red; intros id b sz'. rewrite PTree.gempty; auto. congruence.
  - rewrite Forall_forall.
    intros x IN.
    eapply in_blocks_of_env_inv' in IN. dex. rewrite PTree.gempty in IN; destr.
  - apply Axioms.proof_irr. 
Qed.

Definition fold_alloc_fn (v: ident*Z) (m:Csharpminor.env*mem) :=
  match Mem.alloc (snd m) 0 (Z.max 0 (snd v)) Normal with
      Some (m',b') =>
      (PTree.set (fst v) (b',Z.max 0 (snd v)) (fst m), m')
    | None => m
  end.

Lemma env_independent:
  forall  vars (e e':Csharpminor.env) m,
    snd (fold_right fold_alloc_fn (e,m) vars) =
    snd (fold_right fold_alloc_fn (e',m) vars).
Proof.
  induction vars; simpl; intros; auto.
  unfold fold_alloc_fn at 1 3; simpl.
  rewrite IHvars with (e':=e'). auto.
  destr_cond_match; auto.
  destruct p; simpl; auto.
Qed.

Lemma alloc_variables_fold_right_mem:
  forall vars e m e2 m2 e3 m3,
    alloc_variables_right e m vars e2 m2 ->
    fold_right fold_alloc_fn (e,m) vars = (e3,m3) ->
    m2 = m3.
Proof.
  induction vars;
  intros e m e2 m2 e3 m3 AVS FR; inv AVS; simpl in FR. inv FR; auto.
  destruct (fold_right fold_alloc_fn (e, m) vars) eqn:?. 
  eapply IHvars with (m3:=m0) in H6. 
  subst.
  unfold fold_alloc_fn in FR. simpl in FR.
  rewrite H3 in FR. inv FR. auto.
  rewrite surjective_pairing with (p:=(fold_right _ _ _)).
  rewrite env_independent with (e':=e).
  rewrite Heqp.
  simpl. f_equal.
Qed.

Lemma fold_alloc_fn_old:
  forall vars e m e1 m0 id,
    ~ In id (map fst vars) ->
    fold_right fold_alloc_fn (e, m) vars = (e1, m0) ->
    e1 ! id = e ! id.
Proof.
  induction vars; simpl; intros.
  inv H0; auto.
  destruct (fold_right fold_alloc_fn (e, m) vars) eqn:?; simpl in *.
  eapply IHvars with (id:=id) in Heqp; auto.
  rewrite <- Heqp.
  unfold fold_alloc_fn in H0.
  simpl in H0.
  revert H0; destr.
  destruct p.
  intro; inv H0.
  rewrite PTree.gso; auto.
Qed.

Lemma fold_alloc_fn_diff:
  forall vars e m p e0 e1 m0 id
         (FAF:  fold_right fold_alloc_fn (e, m) vars = (e0, m0))
         (FAF': fold_right fold_alloc_fn (PTree.set id p e, m) vars = (e1, m0))
         id0
         (DIFF: id0 <> id),
    e0 ! id0 = e1 ! id0.
Proof.
  induction vars; simpl; intros.
  inv FAF; inv FAF'. rewrite PTree.gso by congruence. auto.
  destruct (fold_right fold_alloc_fn (e, m) vars) eqn:?.
  destruct (fold_right fold_alloc_fn (PTree.set id p e, m) vars) eqn:?.
  cut (m1=m2); [intro; subst|].
  generalize (IHvars _ _ _ _ _ _ _ Heqp0 Heqp1 _ DIFF).
  revert FAF FAF'; unfold fold_alloc_fn; simpl.
  destr_cond_match; auto.
  destruct p0.
  intros A B C; inv A; inv B.
  rewrite ! PTree.gsspec.
  rewrite C. auto.
  intros A B C; inv A; inv B. auto.
  generalize (env_independent vars e (PTree.set id p e) m).
  rewrite Heqp0. unfold Csharpminor.env in *. rewrite Heqp1. simpl; intro; subst.
  auto.
Qed.

Lemma alloc_variables_fold_right_env:
  forall vars e m e2 m2,
    list_norepet (map fst vars) ->
    alloc_variables_right e m vars e2 m2 ->
    forall e3 m3,
      fold_right fold_alloc_fn (e,m) vars = (e3,m3) ->
      forall id, e3!id = e2!id.
Proof.
  induction vars;
  intros e m e2 m2 LNR AVS e3 m3  FR; inv AVS; simpl in FR. inv FR; auto.

  destruct (fold_right fold_alloc_fn (e, m) vars) eqn:?. 
  simpl in *.
  destruct (fold_right fold_alloc_fn (PTree.set id (b1,Z.max 0 sz) e, m) vars) eqn:?. 
  generalize (alloc_variables_fold_right_mem _ _ _ _ _ _ _ H6 Heqp0).
  intro; subst.
  specialize (env_independent vars (PTree.set id (b1,Z.max 0 sz) e) e m).
  rewrite Heqp. 
  unfold Csharpminor.env in *.
  rewrite Heqp0.
  simpl; intro; subst.
  unfold fold_alloc_fn in FR.
  simpl in FR.
  rewrite H3 in FR.
  inv FR.
  inv LNR.
  specialize (IHvars _ _ _ _ H2 H6 _ _ Heqp0).
  intros.
  rewrite <- IHvars.
  rewrite PTree.gsspec.
  destruct (peq id0 id); subst; auto.
  generalize (fold_alloc_fn_old _ _ _ _ _ _ H1 Heqp0).
  rewrite PTree.gss. intros; auto.
  eapply fold_alloc_fn_diff; eauto.
Qed.

Lemma alloc_variables_fold_right:
  forall vars e m e2 m2,
    list_norepet (map fst vars) ->
    alloc_variables_right e m vars e2 m2 ->
    forall e3 m3,
      fold_right fold_alloc_fn (e,m) vars = (e3,m3) ->
      m2 = m3 /\ forall id, e3!id = e2!id.
Proof.
  intros.
  generalize (alloc_variables_fold_right_mem _ _ _ _ _ _ _ H0 H1).
  generalize (alloc_variables_fold_right_env _ _ _ _ _ H H0 _ _ H1).
  tauto.
Qed.

Lemma alloc_variables_right_just_mem:
  forall l m e e1 e' m',
    alloc_variables_right e1 m l e' m' ->
    exists (e'0 : Csharpminor.env),
      alloc_variables_right e m l e'0 m'.
Proof.
  induction l; simpl; intros; auto.
  inv H. exists e; constructor.
  inv H. eapply IHl with (e:=(PTree.set id (b1, Z.max 0 sz) e)) in H7; eauto.
  destruct H7 as [e'0 H7].
  eexists.
  econstructor; eauto.
Qed.

Lemma alloc_variables_right_decompose:
  forall vars e m l ee mm,
    alloc_variables_right e m (vars ++ l) ee mm ->
    exists e' m',
      alloc_variables_right e m l e' m'.
Proof.
  induction vars; simpl; intros.
  exists ee; exists mm; auto.
  inv H.
  apply IHvars in H7.
  destruct H7 as [e' [m' H7]].
  eapply alloc_variables_right_just_mem in H7; eauto.
  destruct H7.
  exists x; exists m'; eauto.
Qed.

Lemma alloc_variables_right_determ:
  forall l e m ee mm e' m'
         (AVR : alloc_variables_right e m l ee mm)
         (AVR' : alloc_variables_right e m l e' m'),
    ee = e' /\ mm = m'.
Proof.
  induction l; simpl; intros.
  inv AVR'. inv AVR. auto.
  inv AVR'. inv AVR.
  cut (m1=m2).
  intro; subst.
  rewrite H3 in H8; inv H8.
  generalize (IHl _ _ _ _ _ _ H9 H6); intros [A B]. subst. auto.
  destruct (fold_right fold_alloc_fn (PTree.set id (b1,Z.max 0 sz) e, m) l) eqn:?.
  destruct (fold_right fold_alloc_fn (PTree.set id (b0,Z.max 0 sz) e, m) l) eqn:?.
  generalize (alloc_variables_fold_right_mem _ _ _ _ _ _ _ H6 Heqp).
  generalize (alloc_variables_fold_right_mem _ _ _ _ _ _ _ H9 Heqp0).
  generalize (env_independent l (PTree.set id (b1,Z.max 0 sz) e) (PTree.set id (b0,Z.max 0 sz) e) m).
  unfold Csharpminor.env in *. rewrite Heqp. rewrite Heqp0. simpl. intros; subst. auto.
Qed.

Lemma alloc_variables_right_decompose':
  forall vars l e m ee mm,
    alloc_variables_right e m (vars ++ l) ee mm ->
    forall e' m',
      alloc_variables_right e m l e' m' ->
      exists ee',
      alloc_variables_right e' m' vars ee' mm.
Proof.
  induction vars; simpl; intros.
  -  generalize (alloc_variables_right_determ _ _ _ _ _ _ _ H H0). intuition subst.
     exists e'; constructor.
  - inv H. 
    destruct (alloc_variables_right_just_mem _ _ (PTree.set id (b1,Z.max 0 sz) e) _ _ _ H0).
    generalize (IHvars _ _ _ _ _ H8 _ _ H).
    intros [ee' H1].
    destruct (alloc_variables_right_just_mem _ _ (PTree.set id (b1,Z.max 0 sz) e') _ _ _ H1).
    exists x0.
    econstructor; eauto.
Qed.

Lemma alloc_variables_right_decompose'':
  forall vars l e m ee mm,
    alloc_variables_right e m (vars ++ l) ee mm ->
    exists e' m' ee',
      alloc_variables_right e m l e' m' /\
      alloc_variables_right e' m' vars ee' mm.
Proof.
  intros.
  destruct (alloc_variables_right_decompose _ _ _ _ _ _ H) as [e' [m' A]].
  destruct (alloc_variables_right_decompose' _ _ _ _ _ _ H _ _ A) as [ee' B].
  exists e'; exists m'; exists ee'; split; auto.
Qed.

Lemma fold_alloc_fn_in_vars:
  forall vars (e' e1:Csharpminor.env) m1 e2 e0 m2
         (INIT: forall id, e'!id = e1!id)
         (FR1: fold_right fold_alloc_fn (e', m1) vars = (e2, m2))
         (FR2: fold_right fold_alloc_fn (e1, m1) vars = (e0, m2))
         id
         (LNR: list_norepet (map fst vars))
         (i : In id (map fst vars)),
   e2 ! id = e0 ! id.
Proof.
  induction vars; simpl; intros.
  exfalso; auto.
  destruct (fold_right fold_alloc_fn (e', m1) vars) eqn:?.
  destruct (fold_right fold_alloc_fn (e1, m1) vars) eqn:?.
  generalize (env_independent vars e' e1 m1).
  rewrite Heqp. rewrite Heqp0.
  simpl; intro; subst.
  revert FR1 FR2; unfold fold_alloc_fn; simpl; destr_cond_match.
  destruct p. intros A B; inv A; inv B. rewrite ! PTree.gsspec.
  destruct i; subst.
  rewrite ! peq_true. auto.
  inv LNR.
  rewrite (IHvars _ _ _ _ _ _ INIT Heqp Heqp0 _ H3 H). auto.
  intros A B; inv A; inv B.
  destruct i; subst.
  inv LNR.
  generalize (fold_alloc_fn_old _ _ _ _ _ _ H1 Heqp).
  generalize (fold_alloc_fn_old _ _ _ _ _ _ H1 Heqp0).
  clear - INIT.
  intros A B. rewrite A. rewrite B. auto.
  inv LNR.
  rewrite (IHvars _ _ _ _ _ _ INIT Heqp Heqp0 _ H3 H). auto.
Qed.

Lemma fold_alloc_fn_in_vars':
  forall vars (e' e1:Csharpminor.env) m1 e2 e0 m2
         (INIT: forall id, In id (map fst vars) -> e'!id = e1!id)
         (FR1: fold_right fold_alloc_fn (e', m1) vars = (e2, m2))
         (FR2: fold_right fold_alloc_fn (e1, m1) vars = (e0, m2))
         id
         (LNR: list_norepet (map fst vars))
         (i : In id (map fst vars)),
   e2 ! id = e0 ! id.
Proof.
  induction vars; simpl; intros.
  exfalso; auto.
  destruct (fold_right fold_alloc_fn (e', m1) vars) eqn:?.
  destruct (fold_right fold_alloc_fn (e1, m1) vars) eqn:?.
  generalize (env_independent vars e' e1 m1).
  rewrite Heqp. rewrite Heqp0.
  simpl; intro; subst.
  revert FR1 FR2; unfold fold_alloc_fn; simpl; destr_cond_match.
  destruct p. intros A B; inv A; inv B. rewrite ! PTree.gsspec.
  destruct i; subst.
  rewrite ! peq_true. auto.
  inv LNR.
  assert (init: forall id, In id (map fst vars) -> e'!id = e1!id).
  intros; auto.
  rewrite (IHvars _ _ _ _ _ _ init Heqp Heqp0 _ H3 H). auto.
  intros A B; inv A; inv B.
  destruct i; subst.
  inv LNR.
  generalize (fold_alloc_fn_old _ _ _ _ _ _ H1 Heqp).
  generalize (fold_alloc_fn_old _ _ _ _ _ _ H1 Heqp0).
  clear - INIT.
  intros A B. rewrite A. rewrite B. auto.
  inv LNR.
  assert (init: forall id, In id (map fst vars) -> e'!id = e1!id).
  intros; auto.
  rewrite (IHvars _ _ _ _ _ _ init Heqp Heqp0 _ H3 H). auto.
Qed.

Lemma alloc_variables_right_app:
  forall vars l e m  ee mm,
    list_norepet (map fst (vars ++ l)) ->
    alloc_variables_right e m (vars ++ l) ee mm ->
    exists ee' mm' e2,
      alloc_variables_right e m l ee' mm' /\
      alloc_variables_right ee' mm' vars e2 mm /\ 
      forall id, e2 ! id = ee ! id.
Proof.
  intros.
  destruct (fold_right fold_alloc_fn (e,m) (vars ++ l)) eqn:?.
  generalize H0; intro AVS.
  eapply alloc_variables_fold_right in H0; eauto.
  destruct H0; subst.
  rewrite fold_right_app in Heqp.
  destruct (fold_right fold_alloc_fn (e, m) l) eqn:?.
  destruct (alloc_variables_right_decompose'' _ _ _ _ _ _ AVS) as [e' [m' [ee' [A B]]]].
  rewrite map_app in H.
  rewrite list_norepet_app in H. destruct H as [LNR_vars [LNR_l LDSJ]].
  generalize (alloc_variables_fold_right _ _ _ _ _ LNR_l A _ _ Heqp0).
  intro C; destruct C; subst.
  destruct (fold_right fold_alloc_fn (e', m1) vars) eqn:?.
  generalize (alloc_variables_fold_right _ _ _ _ _ LNR_vars B _ _ Heqp1).
  intro C; destruct C; subst.
  exists e'. exists m1.
  exists ee'.  split; auto.
  split; auto.
  intros. rewrite <- H2.
  rewrite <- H1.
  clear - Heqp1 Heqp LNR_vars H0.
  destruct (in_dec peq id (map fst vars)).
  generalize (fold_alloc_fn_in_vars _ _ _ _ _ _ _ H0 Heqp Heqp1 _ LNR_vars i).
  intros; auto.
  rewrite (fold_alloc_fn_old _ _ _ _ _ _ n Heqp1).
  rewrite (fold_alloc_fn_old _ _ _ _ _ _ n Heqp).
  rewrite H0; auto.
Qed.

Lemma alloc_variables_right_env:
  forall vars e e' m ef ef' mf
         (LNR: list_norepet (map fst vars))
         (AVR:alloc_variables_right e m vars ef mf)
         (AVR':alloc_variables_right e' m vars ef' mf)
         (INIT:forall id, In id (map fst vars) -> e!id=e'!id)
         id,
      ef!id = if in_dec peq id (map fst vars)
              then ef'!id
              else e!id.
Proof.
  intros.
  destruct (fold_right fold_alloc_fn (e,m) vars) eqn:?.
  destruct (fold_right fold_alloc_fn (e',m) vars) eqn:?.
  generalize (alloc_variables_fold_right _ _ _ _ _ LNR AVR _ _ Heqp).
  generalize (alloc_variables_fold_right _ _ _ _ _ LNR AVR' _ _ Heqp0).
  intros; intuition subst; subst.
  rewrite <- H2. rewrite <- H3.
  destr_cond_match.
  generalize (fold_alloc_fn_in_vars' _ _ _ _ _ _ _ INIT Heqp Heqp0 _ LNR i). auto.
  generalize (fold_alloc_fn_old _ _ _ _ _ _ n Heqp). auto.
Qed.

Lemma avr_old
     : forall (vars : list (ident * Z)) (e : Csharpminor.env) 
         (m : mem) (e1 : Csharpminor.env) (m0 : mem) 
         (id : ident),
       ~ In id (map fst vars) ->
       list_norepet (map fst vars) ->
       alloc_variables_right e m vars e1 m0 ->
       e1 ! id = e ! id.
Proof.
  intros.
  destruct (fold_right fold_alloc_fn (e,m) vars) eqn:?.
  generalize (alloc_variables_fold_right _ _ _ _ _ H0 H1 _ _ Heqp).
  intuition subst. rewrite <- H4.
  rewrite (fold_alloc_fn_old _ _ _ _ _ _ H Heqp). auto.
Qed.

Lemma alloc_variables_right_app':
  forall vars l e m  mm ee' mm' e2,
    list_norepet (map fst (vars ++ l)) ->
    alloc_variables_right e m l ee' mm' ->
    alloc_variables_right ee' mm' vars e2 mm ->
    exists e2',
      alloc_variables_right e m (vars ++ l) e2' mm /\ forall id, e2!id = e2'!id.
Proof.
  induction vars; simpl; intros.
  - inv H1.  exists e2; split; auto.
  - inv H. inv H1. 
    destruct (alloc_variables_right_just_mem _ _ ee' _ _ _ H10).
    destruct (IHvars _ _ _ _ _ _ _ H5 H0 H) as [x0 [A B]].
    destruct (alloc_variables_right_just_mem _ _ (PTree.set id (b1,Z.max 0 sz) e) _ _ _ A).
    eexists; split. 
    econstructor; eauto.
    simpl in *.
    generalize (alloc_variables_right_env _ _ _ _ _ _ _ H5 H1 A).
    intro C. trim C.
    intros. apply PTree.gso. congruence.
    intros; rewrite C.
    rewrite map_app in H5.
    rewrite list_norepet_app in H5. destruct H5 as [LV [Ll DSJ]].
    generalize (alloc_variables_right_env _ _ _ _ _ _ _ LV H10 H).
    intro D. trim D.
    intros. apply PTree.gso. 
    rewrite map_app in H4. rewrite in_app in H4. intuition congruence.
    rewrite D.
    clear C D.
    repeat destr.
    rewrite map_app in n. rewrite in_app in n. intuition congruence.
    rewrite PTree.gso.
    rewrite <- B.
    rewrite (avr_old _ _ _ _ _ _ n LV H).  auto.
    intro; subst. apply H4; auto.
    rewrite ! PTree.gsspec.
    destr_cond_match; auto.
    assert (~ In id0 (map fst l)).
    rewrite map_app in n0. rewrite in_app in n0.
    intuition congruence.
    rewrite (avr_old _ _ _ _ _ _ H2 Ll H0). auto.
Qed.

Lemma alloc_variables_left_right:
  forall (vars : list (ident * Z)) (e : Csharpminor.env)
         (m : mem) (e2 : Csharpminor.env) (m2 : mem)
  (LNR: list_norepet (map fst vars)),
    alloc_variables e m vars e2 m2 ->
    exists e2',
      alloc_variables_right e m (rev vars) e2' m2 /\
      forall id, e2!id=e2'!id.
Proof.
  induction vars; simpl; intros.
  inv H. exists e2; split; constructor.
  inv H.
  inv LNR.
  apply IHvars in H7; auto. 
  destruct H7 as [e2' [A B]].
  exploit (alloc_variables_right_app' (rev vars) ((id,sz)::nil) e m m2 (PTree.set id (b1,Z.max 0 sz) e) m1 e2').
  replace (rev vars ++ (id,sz) :: nil) with (rev ((id,sz)::vars)); auto.
  rewrite map_rev. apply list_norepet_rev. simpl.
  constructor; auto.
  econstructor; eauto. constructor.
  auto.
  intros [e2'0 [C D]].
  exists e2'0; split; auto.
  intros. rewrite B. apply D.
Qed.

(** * Compatibility of evaluation functions with respect to memory injections. *)

Ltac TrivialExists :=
  match goal with
  | [ |- exists y, Some ?x = Some y /\ val_inject _ _ _ ] =>
      exists x; split; [auto | try(econstructor; eauto)]
  | [ |- exists y, _ /\ val_inject _ (Vint ?x) _ ] =>
      exists (Vint x); split; [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ val_inject _ (Vfloat ?x) _ ] =>
      exists (Vfloat x); split; [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ val_inject _ (Vlong ?x) _ ] =>
      exists (Vlong x); split; [eauto with evalexpr | constructor]
  | _ => idtac
  end.

(** Compatibility of [eval_unop] with respect to [val_inject]. *)

Lemma eval_unop_compat:
  forall f op v1 tv1 v,
  eval_unop op v1 = Some v ->
  expr_inj_se  f v1 tv1 ->
  exists tv,
     eval_unop op tv1 = Some tv
  /\ expr_inj_se  f v tv.
Proof.
  intros.
  destruct (wf_inj_expr_inj_se). 
  destruct op; simpl; intros; inv H; eexists; split; eauto;
  try (apply ei_unop; auto).
Qed.

(** Compatibility of [eval_binop] with respect to [val_inject]. *)

Lemma eval_binop_compat:
  forall f op v1 tv1 v2 tv2 v m tm,
  eval_binop op v1 v2 m = Some v ->
  expr_inj_se  f v1 tv1 ->
  expr_inj_se  f v2 tv2 ->
  Mem.inject true expr_inj_se f m tm ->
  exists tv,
     eval_binop op tv1 tv2 tm = Some tv
  /\ expr_inj_se  f v tv.
Proof.
  destruct (wf_inj_expr_inj_se). 
  destruct op; simpl; intros; inv H; eexists; split; eauto;
  try (apply ei_binop; auto).
Qed.

(** * Correctness of Cminor construction functions *)

(** Correctness of the variable accessor [var_addr] *)

Lemma var_addr_correct:
  forall cenv id f tf e le te sp lo hi m cs tm b,
  match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  eval_var_addr ge e id b ->
  exists tv,
     eval_expr tge sp te tm (var_addr cenv id) tv
  /\ expr_inj_se  f (Eval (Vptr b Int.zero)) tv.
Proof.
  unfold var_addr; intros.
  assert (match_var f sp e!id cenv!id).
    inv H. inv MENV. auto.
  inv H1; inv H0; try congruence.
  - (* local *) 
    (exists (Eval (Vptr sp (Int.repr ofs)))); split.
    constructor. simpl. auto. 
    rewrite <- H2 in H1; inv H1. auto. 
  - (* global *)
    exploit match_callstack_match_globalenvs; eauto. intros [bnd MG]. inv MG.
    (exists (Eval (Vptr b (Int.zero)))); split.
    constructor. simpl. rewrite symbols_preserved. rewrite H2. auto.
    eexists; eexists; repSplit; [reflexivity|reflexivity|].
    constructor. econstructor. rewrite DOMAIN; auto.
    eapply SYMBOLS; eauto. auto.
Qed.

(** * Semantic preservation for the translation *)

(** The proof of semantic preservation uses simulation diagrams of the
  following form:
<<
       e, m1, s ----------------- sp, te1, tm1, ts
          |                                |
         t|                                |t
          v                                v
       e, m2, out --------------- sp, te2, tm2, tout
>>
  where [ts] is the Cminor statement obtained by translating the
  C#minor statement [s].  The left vertical arrow is an execution
  of a C#minor statement.  The right vertical arrow is an execution
  of a Cminor statement.  The precondition (top vertical bar)
  includes a [mem_inject] relation between the memory states [m1] and [tm1],
  and a [match_callstack] relation for any callstack having
  [e], [te1], [sp] as top frame.  The postcondition (bottom vertical bar)
  is the existence of a memory injection [f2] that extends the injection
  [f1] we started with, preserves the [match_callstack] relation for
  the transformed callstack at the final state, and validates a
  [outcome_inject] relation between the outcomes [out] and [tout].
*)

(** ** Semantic preservation for expressions *)


Lemma transl_constant_correct:
  forall f sp cst v,
  Csharpminor.eval_constant cst = Some v ->
  exists tv,
     eval_constant tge sp (transl_constant cst) = Some tv
  /\ expr_inj_se  f v tv.
Proof.
  destruct cst; simpl; intros; inv H; eexists; split; eauto;
  (eexists; eexists; repSplit; [reflexivity|reflexivity|]);
  econstructor; simpl; eauto; simpl; tauto.
Qed.

Lemma transl_expr_correct:
  forall f m tm cenv tf e le te sp lo hi cs
    (MINJ: Mem.inject true expr_inj_se f m tm)
    (MATCH: match_callstack f m tm
             (Frame cenv tf e le te sp lo hi :: cs)
             (Mem.nextblock m) (Mem.nextblock tm)),
  forall a v,
  Csharpminor.eval_expr ge e le m a v ->
  forall ta
    (TR: transl_expr cenv a = OK ta),
  exists tv,
     eval_expr tge sp te tm ta tv
     /\ expr_inj_se  f v tv.
Proof.
  induction 3; intros; simpl in TR; try (monadInv TR).
  - (* Etempvar *)
  inv MATCH. exploit MTMP; eauto. intros [tv [A B]]. 
  exists tv; split. constructor; auto. auto. 
  - (* Eaddrof *)
    exploit var_addr_correct; eauto.
  - (* Econst *)
  exploit transl_constant_correct; eauto. intros [tv [A B]].
  exists tv; split; eauto. constructor; eauto. 
  - (* Eunop *) 
  exploit IHeval_expr; eauto. intros [tv1 [EVAL1 INJ1 ]].
  exploit eval_unop_compat; eauto. intros [tv2 [EVAL INJ]].
  exists tv2. split; auto.
  econstructor; eauto.
  - (* Ebinop *)
  exploit IHeval_expr1; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit IHeval_expr2; eauto. intros [tv2 [EVAL2 INJ2]].
  exploit eval_binop_compat; eauto. intros [tv [EVAL INJ]].
  exists tv; split. econstructor; eauto. auto.
  - (* Eload *)
  exploit IHeval_expr; eauto.  intros [tv1 [EVAL1 INJ1]].  
  exploit Mem.loadv_inject. apply wf_inj_expr_inj_se.
  apply match_callstack_all_blocks_injected in MATCH; eauto.
  eauto. eauto. eauto.
  intros [tv [LOAD INJ]].
  exists tv; split. econstructor; eauto. auto.
Qed.

Lemma transl_exprlist_correct:
  forall f m tm cenv tf e le te sp lo hi cs 
    (MINJ: Mem.inject true expr_inj_se f m tm)
    (MATCH: match_callstack f m tm
             (Frame cenv tf e le te sp lo hi :: cs)
             (Mem.nextblock m) (Mem.nextblock tm)),
  forall a v,
  Csharpminor.eval_exprlist ge e le m a v ->
  forall ta
    (TR: transl_exprlist cenv a = OK ta),
  exists tv,
     eval_exprlist tge sp te tm ta tv
  /\ expr_list_inject  f v tv.
Proof.
  induction 3; intros; monadInv TR.
  exists (@nil expr_sym); split. constructor. constructor.
  exploit transl_expr_correct; eauto. intros [tv1 [EVAL1 VINJ1]].
  exploit IHeval_exprlist; eauto. intros [tv2 [EVAL2 VINJ2]].
  exists (tv1 :: tv2); split. constructor; auto. constructor; auto.
Qed.

(** ** Semantic preservation for statements and functions *)



Inductive match_cont: Csharpminor.cont -> Cminor.cont -> compilenv -> exit_env -> callstack -> Prop :=
  | match_Kstop: forall cenv xenv,
      match_cont Csharpminor.Kstop Kstop cenv xenv nil
  | match_Kseq: forall s k ts tk cenv xenv cs,
      transl_stmt cenv xenv s = OK ts ->
      match_cont k tk cenv xenv cs ->
      match_cont (Csharpminor.Kseq s k) (Kseq ts tk) cenv xenv cs
  | match_Kseq2: forall s1 s2 k ts1 tk cenv xenv cs,
      transl_stmt cenv xenv s1 = OK ts1 ->
      match_cont (Csharpminor.Kseq s2 k) tk cenv xenv cs ->
      match_cont (Csharpminor.Kseq (Csharpminor.Sseq s1 s2) k)
                 (Kseq ts1 tk) cenv xenv cs
  | match_Kblock: forall k tk cenv xenv cs,
      match_cont k tk cenv xenv cs ->
      match_cont (Csharpminor.Kblock k) (Kblock tk) cenv (true :: xenv) cs
  | match_Kblock2: forall k tk cenv xenv cs,
      match_cont k tk cenv xenv cs ->
      match_cont k (Kblock tk) cenv (false :: xenv) cs
  | match_Kcall: forall optid fn e le k tfn sp te tk cenv xenv lo hi cs sz cenv' ssp,
      transl_funbody cenv sz ssp fn = OK tfn ->
      match_cont k tk cenv xenv cs ->
      match_cont (Csharpminor.Kcall optid fn e le k)
                 (Kcall optid tfn sp te tk)
                 cenv' nil
                 (Frame cenv tfn e le te sp lo hi :: cs).

Inductive match_states: Csharpminor.state -> Cminor.state -> Prop :=
  | match_state:
      forall fn s k e le m tfn ts tk sp te tm cenv xenv f lo hi cs sz ssp
      (TRF: transl_funbody cenv sz ssp fn = OK tfn)
      (TR: transl_stmt cenv xenv s = OK ts)
      (MINJ: Mem.inject true expr_inj_se f m tm)
      (MCS: match_callstack f m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      lm tlm
      (SMP: size_mem_preserved (m::lm) (tm::tlm)
                               (Frame cenv tfn e le te sp lo hi:: cs))
      (MK: match_cont k tk cenv xenv cs),
      match_states (Csharpminor.State fn s k e le m)
                   (State tfn ts tk sp te tm)
  | match_state_seq:
      forall fn s1 s2 k e le m tfn ts1 tk sp te tm cenv xenv f lo hi cs sz ssp
      (TRF: transl_funbody cenv sz ssp fn = OK tfn)
      (TR: transl_stmt cenv xenv s1 = OK ts1)
      (MINJ: Mem.inject true expr_inj_se f m tm)
      (MCS: match_callstack f m tm
               (Frame cenv tfn e le te sp lo hi:: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      lm tlm
      (SMP: size_mem_preserved (m::lm) (tm::tlm)
               (Frame cenv tfn e le te sp lo hi :: cs))
      (MK: match_cont (Csharpminor.Kseq s2 k) tk cenv xenv cs),
      match_states (Csharpminor.State fn (Csharpminor.Sseq s1 s2) k e le m)
                   (State tfn ts1 tk sp te tm)
  | match_callstate:
      forall fd args k m tfd targs tk tm f cs cenv
      (TR: transl_fundef fd = OK tfd)
      (MINJ: Mem.inject true expr_inj_se f m tm)
      (MCS: match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      lm tlm
      (SMP: size_mem_preserved (m::lm) (tm::tlm) cs)
      (MK: match_cont k tk cenv nil cs)
      (ISCC: Csharpminor.is_call_cont k)
      (ARGSINJ: expr_list_inject  f args targs),
      match_states (Csharpminor.Callstate fd args k m)
                   (Callstate tfd targs tk tm)
  | match_returnstate:
      forall v k m tv tk tm f cs cenv
      (MINJ: Mem.inject true expr_inj_se f m tm)
      (MCS: match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      lm tlm
      (SMP: size_mem_preserved (m::lm) (tm::tlm) cs)
      (MK: match_cont k tk cenv nil cs)
      (RESINJ: expr_inj_se  f v tv),
      match_states (Csharpminor.Returnstate v k m)
                   (Returnstate tv tk tm).

Remark val_inject_function_pointer:
  forall m' m bound v fd f tv
         (MI: Mem.inject true expr_inj_se f m m')
         (FF: Genv.find_funct m ge v = Some fd)
         (MGE: match_globalenvs f bound)
         (ABI: Mem.all_blocks_injected f m)
         (EI: expr_inj_se  f v tv),
  Mem.mem_norm m' tv = Mem.mem_norm m v.
Proof.
  intros m' m bound v fd f tv MI FF MGE ABI EI.
  intros. exploit Genv.find_funct_inv; eauto. intros [b EQ]. 
  unfold Genv.find_funct in FF.
  rewrite EQ in FF. rewrite pred_dec_true in FF; auto.
  assert (f b = Some(b, 0)) by  (inv MGE; apply DOMAIN;eapply FUNCTIONS; eauto).
  generalize (Mem.norm_inject_val' _ _ wf_inj_expr_inj_se _ _ _ _ _ ABI MI EI).
  rewrite EQ.
  intro A; inv A. rewrite H in FB; inv FB. f_equal.
Qed.

Lemma match_call_cont:
  forall k tk cenv xenv cs,
  match_cont k tk cenv xenv cs ->
  match_cont (Csharpminor.call_cont k) (call_cont tk) cenv nil cs.
Proof.
  induction 1; simpl; auto; econstructor; eauto.
Qed.

Lemma match_is_call_cont:
  forall tfn te sp tm k tk cenv xenv cs,
  match_cont k tk cenv xenv cs ->
  Csharpminor.is_call_cont k ->
  exists tk',
    star (fun ge => step ge needed_stackspace ) tge (State tfn Sskip tk sp te tm)
               E0 (State tfn Sskip tk' sp te tm)
    /\ is_call_cont tk'
    /\ match_cont k tk' cenv nil cs.
Proof.
  induction 1; simpl; intros; try contradiction.
  econstructor; split. apply star_refl. split. exact I. econstructor; eauto.
  exploit IHmatch_cont; eauto.
  intros [tk' [A B]]. exists tk'; split.
  eapply star_left; eauto. constructor. traceEq. auto.
  econstructor; split. apply star_refl. split. exact I. econstructor; eauto.
Qed.

(** Properties of [switch] compilation *)

Inductive lbl_stmt_tail: lbl_stmt -> nat -> lbl_stmt -> Prop :=
  | lstail_O: forall sl,
      lbl_stmt_tail sl O sl
  | lstail_S: forall c s sl n sl',
      lbl_stmt_tail sl n sl' ->
      lbl_stmt_tail (LScons c s sl) (S n) sl'.

Lemma switch_table_default:
  forall sl base,
  exists n, 
     lbl_stmt_tail sl n (select_switch_default sl)
  /\ snd (switch_table sl base) = (n + base)%nat.
Proof.
  induction sl; simpl; intros.
- exists O; split. constructor. omega.
- destruct o. 
  + destruct (IHsl (S base)) as (n & P & Q). exists (S n); split. 
    constructor; auto. 
    destruct (switch_table sl (S base)) as [tbl dfl]; simpl in *. omega.
  + exists O; split. constructor. 
    destruct (switch_table sl (S base)) as [tbl dfl]; simpl in *. auto.
Qed.

Lemma switch_table_case:
  forall i sl base dfl,
  match select_switch_case i sl with
  | None =>
      switch_target i dfl (fst (switch_table sl base)) = dfl
  | Some sl' =>
      exists n,
         lbl_stmt_tail sl n sl'
      /\ switch_target i dfl (fst (switch_table sl base)) = (n + base)%nat
  end.
Proof.
  induction sl; simpl; intros.
- auto.
- destruct (switch_table sl (S base)) as [tbl1 dfl1] eqn:ST. 
  destruct o; simpl.
  rewrite dec_eq_sym. destruct (zeq i z).
  exists O; split; auto. constructor.
  specialize (IHsl (S base) dfl). rewrite ST in IHsl. simpl in *.
  destruct (select_switch_case i sl).
  destruct IHsl as (x & P & Q). exists (S x); split. constructor; auto. omega. 
  auto.
  specialize (IHsl (S base) dfl). rewrite ST in IHsl. simpl in *.
  destruct (select_switch_case i sl).
  destruct IHsl as (x & P & Q). exists (S x); split. constructor; auto. omega. 
  auto.
Qed.

Lemma switch_table_select:
  forall i sl,
  lbl_stmt_tail sl
                (switch_target i (snd (switch_table sl O)) (fst (switch_table sl O)))
                (select_switch i sl).
Proof.
  unfold select_switch; intros.
  generalize (switch_table_case i sl O (snd (switch_table sl O))). 
  destruct (select_switch_case i sl) as [sl'|].
  intros (n & P & Q). replace (n + O)%nat with n in Q by omega. congruence.
  intros E; rewrite E.
  destruct (switch_table_default sl O) as (n & P & Q).
  replace (n + O)%nat with n in Q by omega. congruence.
Qed.

Inductive transl_lblstmt_cont(cenv: compilenv) (xenv: exit_env): lbl_stmt -> cont -> cont -> Prop :=
  | tlsc_default: forall k,
      transl_lblstmt_cont cenv xenv LSnil k (Kblock (Kseq Sskip k))
  | tlsc_case: forall i s ls k ts k',
      transl_stmt cenv (switch_env (LScons i s ls) xenv) s = OK ts ->
      transl_lblstmt_cont cenv xenv ls k k' ->
      transl_lblstmt_cont cenv xenv (LScons i s ls) k (Kblock (Kseq ts k')).

Lemma switch_descent:
  forall cenv xenv k ls body s,
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK s ->
  exists k',
  transl_lblstmt_cont cenv xenv ls k k'
  /\ (forall f sp e m,
      plus (fun ge => step ge needed_stackspace ) tge (State f s k sp e m) E0 (State f body k' sp e m)).
Proof.
  induction ls; intros. 
- monadInv H. econstructor; split.
  econstructor.
  intros. eapply plus_two. constructor. constructor. auto. 
- monadInv H. exploit IHls; eauto. intros [k' [A B]]. 
  econstructor; split.
  econstructor; eauto.
  intros. eapply plus_star_trans. eauto. 
  eapply star_left. constructor. apply star_one. constructor. 
  reflexivity. traceEq.
Qed.

Lemma switch_ascent:
  forall f sp e m cenv xenv ls n ls',
  lbl_stmt_tail ls n ls' ->
  forall k k1,
  transl_lblstmt_cont cenv xenv ls k k1 ->
  exists k2,
  star (fun ge => step ge needed_stackspace ) tge (State f (Sexit n) k1 sp e m)
             E0 (State f (Sexit O) k2 sp e m)
  /\ transl_lblstmt_cont cenv xenv ls' k k2.
Proof.
  induction 1; intros. 
- exists k1; split; auto. apply star_refl.
- inv H0. exploit IHlbl_stmt_tail; eauto. intros (k2 & P & Q). 
  exists k2; split; auto.
  eapply star_left. constructor. eapply star_left. constructor. eexact P.
  eauto. auto. 
Qed.

Lemma switch_match_cont:
  forall cenv xenv k cs tk ls tk',
  match_cont k tk cenv xenv cs ->
  transl_lblstmt_cont cenv xenv ls tk tk' ->
  match_cont (Csharpminor.Kseq (seq_of_lbl_stmt ls) k) tk' cenv (false :: switch_env ls xenv) cs.
Proof.
  induction ls; intros; simpl.
  inv H0. apply match_Kblock2. econstructor; eauto.
  inv H0. apply match_Kblock2. eapply match_Kseq2. auto. eauto. 
Qed.

Lemma switch_match_states:
  forall fn k e le m tfn ts tk sp te tm cenv xenv f lo hi cs sz ls body tk' ssp
    (TRF: transl_funbody cenv sz ssp fn = OK tfn)
    (TR: transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts)
    (MINJ: Mem.inject true expr_inj_se f m tm)
    (MCS: match_callstack f m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
    lm tlm
    (SMP: size_mem_preserved (m::lm) (tm::tlm)
               (Frame cenv tfn e le te sp lo hi :: cs))
    (MK: match_cont k tk cenv xenv cs)
    (TK: transl_lblstmt_cont cenv xenv ls tk tk'),
  exists S,
  plus (fun ge => step ge needed_stackspace) tge (State tfn (Sexit O) tk' sp te tm) E0 S
  /\ match_states (Csharpminor.State fn (seq_of_lbl_stmt ls) k e le m) S.
Proof.
  intros. inv TK. 
- econstructor; split. eapply plus_two. constructor. constructor. auto. 
  eapply match_state; eauto.
  
- econstructor; split. eapply plus_left. constructor. apply star_one. constructor. auto.
  simpl. eapply match_state_seq; eauto. simpl. eapply switch_match_cont; eauto.
Qed.

Lemma transl_lblstmt_suffix:
  forall cenv xenv ls n ls',
  lbl_stmt_tail ls n ls' ->
  forall body ts, transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts ->
  exists body', exists ts', transl_lblstmt cenv (switch_env ls' xenv) ls' body' = OK ts'.
Proof.
  induction 1; intros. 
- exists body, ts; auto.
- monadInv H0. eauto. 
Qed.

(** Commutation between [find_label] and compilation *)

Section FIND_LABEL.

Variable lbl: label.
Variable cenv: compilenv.
Variable cs: callstack.

Lemma transl_lblstmt_find_label_context:
  forall xenv ls body ts tk1 tk2 ts' tk',
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts ->
  transl_lblstmt_cont cenv xenv ls tk1 tk2 ->
  find_label lbl body tk2 = Some (ts', tk') ->
  find_label lbl ts tk1 = Some (ts', tk').
Proof.
  induction ls; intros.
- monadInv H. inv H0. simpl. rewrite H1. auto.
- monadInv H. inv H0. simpl in H6. eapply IHls; eauto. 
  replace x with ts0 by congruence. simpl. rewrite H1. auto.
Qed.

Lemma transl_find_label:
  forall s k xenv ts tk,
  transl_stmt cenv xenv s = OK ts ->
  match_cont k tk cenv xenv cs ->
  match Csharpminor.find_label lbl s k with
  | None => find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk', exists xenv',
        find_label lbl ts tk = Some(ts', tk')
     /\ transl_stmt cenv xenv' s' = OK ts'
     /\ match_cont k' tk' cenv xenv' cs
  end

with transl_lblstmt_find_label:
  forall ls xenv body k ts tk tk1,
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts ->
  match_cont k tk cenv xenv cs ->
  transl_lblstmt_cont cenv xenv ls tk tk1 ->
  find_label lbl body tk1 = None ->
  match Csharpminor.find_label_ls lbl ls k with
  | None => find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk', exists xenv',
        find_label lbl ts tk = Some(ts', tk')
     /\ transl_stmt cenv xenv' s' = OK ts'
     /\ match_cont k' tk' cenv xenv' cs
  end.
Proof.
  intros. destruct s; try des (m:memory_chunk); try (monadInv H); simpl; auto.
  (* seq *)
  exploit (transl_find_label s1). eauto. eapply match_Kseq. eexact EQ1. eauto.  
  destruct (Csharpminor.find_label lbl s1 (Csharpminor.Kseq s2 k)) as [[s' k'] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]]. 
  exists ts'; exists tk'; exists xenv'. intuition. rewrite A; auto.
  intro. rewrite H. apply transl_find_label with xenv; auto. 
  (* ifthenelse *)
  exploit (transl_find_label s1). eauto. eauto.  
  destruct (Csharpminor.find_label lbl s1 k) as [[s' k'] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]]. 
  exists ts'; exists tk'; exists xenv'. intuition. rewrite A; auto.
  intro. rewrite H. apply transl_find_label with xenv; auto. 
  (* loop *)
  apply transl_find_label with xenv. auto. econstructor; eauto. simpl. rewrite EQ; auto.
  (* block *)
  apply transl_find_label with (true :: xenv). auto. constructor; auto. 
  (* switch *)
  simpl in H. destruct (switch_table l O) as [tbl dfl]. monadInv H. 
  exploit switch_descent; eauto. intros [k' [A B]].
  eapply transl_lblstmt_find_label. eauto. eauto. eauto. reflexivity.  
  (* return *)
  destruct o; monadInv H; auto.
  (* label *)
  destruct (ident_eq lbl l).
  exists x; exists tk; exists xenv; auto.
  apply transl_find_label with xenv; auto.

  intros. destruct ls; monadInv H; simpl.
  (* nil *)
  inv H1. rewrite H2. auto.
  (* cons *)
  inv H1. simpl in H7.
  exploit (transl_find_label s). eauto. eapply switch_match_cont; eauto. 
  destruct (Csharpminor.find_label lbl s (Csharpminor.Kseq (seq_of_lbl_stmt ls) k)) as [[s' k''] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]].
  exists ts'; exists tk'; exists xenv'; intuition. 
  eapply transl_lblstmt_find_label_context; eauto. 
  simpl. replace x with ts0 by congruence. rewrite H2. auto.
  intro. eapply transl_lblstmt_find_label. eauto. auto. eauto. 
  simpl. replace x with ts0 by congruence. rewrite H2. auto. 
Qed.

End FIND_LABEL.

Lemma transl_find_label_body:
  forall cenv xenv size f tf k tk cs lbl s' k' ssp,
  transl_funbody cenv size ssp f = OK tf ->
  match_cont k tk cenv xenv cs ->
  Csharpminor.find_label lbl f.(Csharpminor.fn_body) (Csharpminor.call_cont k) = Some (s', k') ->
  exists ts', exists tk', exists xenv',
     find_label lbl tf.(fn_body) (call_cont tk) = Some(ts', tk')
  /\ transl_stmt cenv xenv' s' = OK ts'
  /\ match_cont k' tk' cenv xenv' cs.
Proof.
  intros. monadInv H. simpl. 
  exploit transl_find_label. eexact EQ. eapply match_call_cont. eexact H0.
  instantiate (1 := lbl). rewrite H1. auto.
Qed.


(** The simulation diagram. *)

Fixpoint seq_left_depth (s: Csharpminor.stmt) : nat :=
  match s with
  | Csharpminor.Sseq s1 s2 => S (seq_left_depth s1)
  | _ => O
  end.

Definition measure (S: Csharpminor.state) : nat :=
  match S with
  | Csharpminor.State fn s k e le m => seq_left_depth s
  | _ => O
  end.

Lemma alloc_variables_size:
  forall l e m e' m'
         (AVR : alloc_variables_right e m l e' m'),
    (Mem.nb_boxes_used_m m' =
    Mem.nb_boxes_used_m m + size_list_blocks (map (fun (isz: ident * Z) => let (i,sz) := isz in Z.max 0 sz) l))%nat.
Proof.
  induction l; simpl; intros.
  - inv AVR. unfold size_list_blocks; simpl. lia.
  - inv AVR.
    rewrite (Mem.nb_boxes_alloc _ _ _ _ _ _ H3).
    specialize (IHl _ _ _ _ H6).
    rewrite IHl.
    simpl. unfold size_list_blocks. simpl.
    rewrite (Mem.fold_left_plus_rew _ (Mem.box_span _)).
    rewrite (Zmax_spec _ (Z.max _ _)). destr. contradict l0. generalize (Z.le_max_l 0 sz). lia. lia.
Qed.

(* Lemma fr_rew: *)
(*   forall l x *)
(*          (ALIGNED: x = align x (two_power_nat MA)), *)
(*     align (big_var_space l x) (two_power_nat MA) = *)
(*     align x (two_power_nat MA) + align (big_var_space l 0) (two_power_nat MA). *)
(* Proof. *)
(*   induction l. *)
(*   - simpl. intros; simpl. *)
(*     rewrite align_0; auto; lia. *)
(*   - simpl. intros. *)
(*     rewrite IHl; auto. *)
(*     rewrite IHl; auto. *)
(*     rewrite <- Z.add_assoc. *)
(*     rewrite <- Mem.align_distr; auto. symmetry; apply align_0; auto. *)
(* Qed. *)

Lemma alloc_variables_right_app'':
  forall vars l e m  mm ee' mm' e2,
    alloc_variables_right e m l ee' mm' ->
    alloc_variables_right ee' mm' vars e2 mm ->
    exists e2',
      alloc_variables_right e m (vars ++ l) e2' mm.
Proof.
  induction vars; simpl; intros.
  - inv H0.  exists e2; auto.
  - inv H0.
    destruct (alloc_variables_right_just_mem _ _ ee' _ _ _ H8).
    destruct (IHvars _ _ _ _ _ _ _ H H0) as [x0 A ].
    destruct (alloc_variables_right_just_mem _ _ (PTree.set id (b1,Z.max 0 sz) e) _ _ _ A).
    eexists.
    econstructor; eauto.
Qed.

Lemma alloc_variables_left_right':
  forall (vars : list (ident * Z)) (e : Csharpminor.env)
         (m : mem) (e2 : Csharpminor.env) (m2 : mem),
    alloc_variables e m vars e2 m2 ->
    exists e2',
      alloc_variables_right e m (rev vars) e2' m2.
Proof.
  induction vars; simpl; intros.
  inv H. exists e2; constructor.
  inv H.
  apply IHvars in H7; auto. 
  destruct H7 as [e2' A].
  destruct (alloc_variables_right_app'' (rev vars) ((id,sz)::nil) e m m2 (PTree.set id (b1,Z.max 0 sz) e) m1 e2').
  econstructor. eauto.
  constructor.
  auto.
  eexists; eauto.
Qed.

  Lemma box_span_mul_add:
    forall x z, 0 <= z -> 0 <= x ->
      (Mem.box_span (x * two_power_nat MA) + Mem.box_span z)%nat =
      Mem.box_span (x * two_power_nat MA + z).
  Proof.
    intros.
    unfold Mem.box_span.
    apply Nat2Z.inj.
    rewrite Z2Nat.id.
    rewrite Nat2Z.inj_add.
    rewrite ! Z2Nat.id.
    cut ((x * two_power_nat MA + z - 1) / two_power_nat MA = (x * two_power_nat MA - 1) / two_power_nat MA + (z - 1) / two_power_nat MA + 1). lia.

    2 : cut (-1 <= (z - 1) / two_power_nat MA). 2: lia. 2: etransitivity.
    3: eapply Z.div_le_mono with (a:= -1). 3: apply Z.gt_lt, Mem.tpMA_pos. 3: lia.
    2: rewrite Mem.minus_1_div_eq. 2: lia. 2: apply Mem.tpMA_pos.

    2 : cut (-1 <= (x * two_power_nat MA - 1) / two_power_nat MA). 2: lia. 2: etransitivity.
    3: eapply Z.div_le_mono with (a:= -1). 3: apply Z.gt_lt, Mem.tpMA_pos.
    3: generalize Mem.tpMA_pos. 3: nia.
    2: rewrite Mem.minus_1_div_eq. 2: lia. 2: apply Mem.tpMA_pos.

    2 : cut (-1 <= (x * two_power_nat MA + z - 1) / two_power_nat MA). 2: lia. 2: etransitivity.
    3: eapply Z.div_le_mono with (a:= -1). 3: apply Z.gt_lt, Mem.tpMA_pos.
    3: generalize Mem.tpMA_pos; nia.
    2: rewrite Mem.minus_1_div_eq. 2: lia. 2: apply Mem.tpMA_pos.

    cut (two_power_nat MA * ((x * two_power_nat MA + z - 1) / two_power_nat MA) =
         two_power_nat MA * ((x * two_power_nat MA - 1) / two_power_nat MA + (z - 1) / two_power_nat MA + 1)).
    generalize Mem.tpMA_pos; nia.

    rewrite ! Z.mul_add_distr_l.

    assert (forall a b, b > 0 -> (b * (a/b)) = a - a mod b).
    {
      intros.
      rewrite (Z_div_mod_eq a _ H1) at 2. lia.
    }
    rewrite ! H1 by apply Mem.tpMA_pos.
    ring_simplify.

    cut ((x * two_power_nat MA + z - 1) mod two_power_nat MA  + two_power_nat MA =
         (x * two_power_nat MA - 1) mod two_power_nat MA + (z - 1) mod two_power_nat MA  + 1). nia.
    
    assert (forall z: Z, z >= 0 -> exists a b, z = two_power_nat MA * a + b).
    {
      intros. exists (z0 / two_power_nat MA), (z0 mod two_power_nat MA).
      rewrite H1. lia. apply Mem.tpMA_pos. 
    }

    rewrite ! (Zminus_mod _ 1).
    rewrite Zplus_mod.
    rewrite Z_mod_mult. simpl.
    rewrite ! Zmod_1_l.
    rewrite Z.mod_opp_l_nz.
    rewrite Zmod_mod.
    ring_simplify .
    cut (forall z, z = z - 1 mod two_power_nat MA + 1).
    intro A; apply A. intros.
    rewrite Zmod_1_l. lia.
    generalize (Mem.tpMA_sup8). lia.
    generalize (Mem.tpMA_sup8). lia.
    rewrite Zmod_1_l. lia.
    generalize (Mem.tpMA_sup8). lia.
    generalize (Mem.tpMA_sup8). lia.
Qed.


  Lemma align_is_mul:
    forall x y,
    exists k, align x y = k * y.
  Proof.
    unfold align. intros; eauto.
  Qed.


  Lemma fold_right_plus_permut:
    forall l l' (P: Permutation l l') n,
      fold_right (fun y x => (x + y)%nat) n l =
      fold_right (fun y x => (x + y)%nat) n l'.
  Proof.
    induction 1; simpl; intros; eauto.
    lia.
    congruence.
  Qed.


  Lemma fr_le:
    forall l,
    forall z : Z,
      0 <= z ->
      z <= fold_right (fun (y : ident * Z) (x : Z) => align x (two_power_nat MA) + Z.max 0 (snd y)) z l.
  Proof.
    induction l; simpl; intros; eauto. lia. 
    etransitivity.
    2: apply Z.add_le_mono.
    2: apply align_le.
    etransitivity.
    2: apply Z.add_le_mono.
    2: apply IHl.
    instantiate (1:= 0). lia. lia. instantiate (1:=0). lia.
    apply Mem.tpMA_pos.
    lia.
  Qed.


  Lemma box_span_fold_right_align:
    forall l, 
      fold_right (fun y x : nat => (x + y)%nat) 0%nat
                 (map Mem.box_span (map (fun isz : ident * Z => let (_, sz) := isz in Z.max 0 sz) l)) =
      Mem.box_span
        (align
           (fold_right
              (fun (y : ident * Z) (x : Z) => align x (two_power_nat MA) + Z.max 0 (snd y)) 0 l)
           (two_power_nat MA)).
  Proof.
    induction l; simpl; intros; eauto.
    rewrite align_0, box_span_0. auto. apply Mem.tpMA_pos.
    rewrite IHl.
    rewrite (box_span_small_align' (Z.add _ _)).
    destruct (align_is_mul (fold_right (fun (y : ident * Z) (x : Z) => align x (two_power_nat MA) + Z.max 0 (snd y)) 0 l) (two_power_nat MA)). rewrite H.
    des a.
    Focus 2.
    apply Z.add_nonneg_nonneg.
    etransitivity. 2: apply align_le. 2: apply Mem.tpMA_pos. 2: lia.
    apply fr_le. lia.
    2: lia.
    apply box_span_mul_add. lia.
    apply Z.mul_le_mono_pos_r with (two_power_nat MA). apply Z.gt_lt, Mem.tpMA_pos.
    rewrite <- H.
    etransitivity. 2: apply align_le. 2: apply Mem.tpMA_pos. simpl.
    apply fr_le. lia.
  Qed. 


Lemma alloc_variables_alloc_sp_ok:
  forall p f m fn e m1 tf tm
    (ABI: Mem.all_blocks_injected f m)
         (INJ: Mem.inject true p f m tm)
         (AV: alloc_variables empty_env m
                              (varsort' (Csharpminor.fn_vars fn)) 
                              e m1)
         (TF: transl_function fn = OK tf)
         (ALLOC: Mem.alloc tm 0 (align 
                                   (big_var_space
                                      (rev (varsort' (Csharpminor.fn_vars fn)))
                                      0)
                                   (two_power_nat MA)) Normal = None),
    False.
Proof.
  intros. 
  apply alloc_variables_left_right' in AV; auto. 
  destruct AV as [e2' AVR].
  generalize (Mem.mi_size_mem _ _ _ _ _ (Mem.mi_inj _ _ _ _ _ INJ)); intro sizes. 
  revert AVR ALLOC. 
  generalize  (rev (varsort' (Csharpminor.fn_vars fn))); intros l AVR ALLOC.
  apply alloc_variables_size in AVR; auto. 
  apply Mem.alloc_none_too_many_boxes in ALLOC.
  generalize (Mem.wfm_alloc m1).
  cut (
      size_list_blocks (map (fun isz : ident * Z => let (_, sz) := isz in Z.max 0 sz) l)%nat
      = Mem.box_span (Z.max 0 (align (big_var_space l 0) (two_power_nat MA)))
    ). intuition lia.
  rewrite Z.max_r.
  unfold size_list_blocks.
  rewrite <- fold_left_rev_right.
  erewrite fold_right_plus_permut. 2: apply Permutation_sym, Permutation_rev.
  unfold big_var_space.
  apply box_span_fold_right_align.
  etransitivity. 2: apply align_le.
  apply Zge_le, fr_align_pos8. lia.
  apply Mem.tpMA_pos.
Qed.


Lemma mcs_frame_env_ext:
  forall f m tm ce tf x e le te sp lo hi cs b tb,
    match_callstack f m tm (Frame ce tf x le te sp lo hi :: cs) b tb ->
    (forall id, x!id = e!id) ->
    match_callstack f m tm (Frame ce tf e le te sp lo hi :: cs) b tb.
Proof.
  intros.
  inv H.
  econstructor; auto.
  - inv MENV.
    constructor; intros; try rewrite <- H0 in *; eauto.
    destruct (me_inv0 _ _ H) as [id [sz A]]; exists id; exists sz; rewrite <- H0; auto.
  - unfold match_bounds in *.
    intros. rewrite <- H0 in H; eauto.
  - unfold match_bounds' in *.
    intros. rewrite <- H0 in H; eauto.
  - clear - NRP H0.
    unfold norepet_env in *.
    unfold blocks_of_env, block_of_binding in *.
    rewrite <- PTree.elements_extensional with (m:=x); auto.
  - revert hi_pos.
    unfold blocks_of_env, block_of_binding.
    rewrite (PTree.elements_extensional _ _ H0); auto.
  - rewrite sz_stack.  f_equal.
    unfold blocks_of_env, block_of_binding.
    rewrite (PTree.elements_extensional _ _ H0); auto. 
  - unfold padding_freeable in *.
    intros.
    destruct (PERM ofs); auto.
    right.
    inv H1. rewrite H0 in H2.
    econstructor; eauto.
  - rewrite Forall_forall.
    intros.
    apply in_blocks_of_env_inv' in H. dex. rewrite <- H0 in H.
    apply in_blocks_of_env in H.
    rewrite Forall_forall in ndyn_e. apply ndyn_e. rewrite map_map, in_map_iff; eexists; split; eauto. destr.
Qed.

Lemma fl_align_add':
  forall l z1 z2,
    0 <= z1 <= z2 ->
    big_var_space l z1 <=
    big_var_space l z2.
Proof.
  induction l; simpl; intros.
  omega.
  apply Z.add_le_mono_r.
  apply align_add. auto. 
  split.
  refine (Zle_trans _ _ _ (proj1 H) (Zge_le _ _ (fr_align_pos8 _ _ _))).
  omega.
  apply IHl; auto.
Qed.

Lemma big_var_space_app:
  forall a b z,
    big_var_space (a ++ b) z = big_var_space a (big_var_space b z).
Proof.
  intros. 
  unfold big_var_space.
  rewrite fold_right_app; auto.
Qed.

Lemma build_compilenv_le8:
  forall ce sz f,
   build_compilenv f = (ce, sz) ->
   sz <= big_var_space (rev (varsort' (Csharpminor.fn_vars f))) 0.
Proof.
  unfold build_compilenv.
  intros ce sz f.
  generalize (varsort' (Csharpminor.fn_vars f)).
  intro l; revert ce sz; clear.  
  assert (0 <= 0) by omega.
  revert H. generalize 0 at 2 3 4. 
  generalize (PTree.empty Z).
  induction l; simpl; intros t z Hz ce sz AV.
  inv AV. omega.
  unfold assign_variable in AV.
  destruct a. simpl.
  assert (0 <= align z (block_alignment z0) + Z.max 0 z0).
  {
    generalize (Zmax_bound_l 0 0 z0).
    generalize (align_le z _ (block_alignment_pos z0)).
    omega.
  }
  apply IHl in AV; auto.
  etransitivity; eauto. 
  rewrite big_var_space_app; simpl.
  apply fl_align_add'.
  split. auto. 
  apply Z.add_le_mono_r.
  rewrite <- align_plus with (sz:=z0).
  apply align_le. auto. 
Qed.

(* Lemma external_call_match_callstack: *)
(*   forall f0 m tm cs  *)
(*          (MCS : match_callstack f0 m tm cs *)
(*                                 (Mem.nextblock m) (Mem.nextblock tm)) *)
(*     ef vargs tvargs t vres vres' m'    tm'  *)
(*          (EC : external_call ef ge vargs m t vres m') *)
(*          (EC' : external_call ef ge tvargs tm t vres' tm') *)
(*          (* (OUTOFREACH : Mem.unchanged_on (loc_out_of_reach f0 m) tm tm') *), *)
(*     match_callstack f0 m' tm' cs *)
(*                     (Mem.nextblock m) (Mem.nextblock tm). *)
(* Proof. *)
(*   induction 1; simpl; intros. *)
(*   - econstructor; eauto. *)
(*     red; intros. *)
(*     intro. *)
(*     apply (fun pf => H0 _ lo hi0 pf H4 H5). *)
(*     eapply H0; eauto. *)
(*     rewrite <- H3. symmetry; eapply extcall_bounds; eauto. *)
(*   - econstructor; eauto. *)
(*     + red; intros. *)
(*       eapply external_call_max_perm in H0; eauto. *)
(*       eapply me_bounded in H; eauto. *)
(*       destruct H as [A B].  *)
(*       eapply external_block_valid; eauto. *)
(*       eapply Mem.perm_valid_block; eauto. *)
(*     + red; intros. *)
(*       eapply BOUND' in H. *)
(*       rewrite <- H. *)
(*       eapply extcall_bounds; eauto. *)
(*     + red; intros. *)
(*       destruct (is_reachable_from_env_dec f0 e sp ofs) as [IRFE|NIRFE]. *)
(*       * inv IRFE. right. apply is_reachable_intro with id b sz delta; auto.  *)
(*       * exploit PERM; eauto. intros [A|A]; try contradiction. *)
(*         left. eapply Mem.perm_unchanged_on; eauto. *)
(*         red; intros; red; intros. elim NIRFE. *)
(*         exploit me_inv; eauto. intros [id [lv B]]. *)
(*         exploit BOUND0; eauto. intros C. *)
(*         apply is_reachable_intro with id b0 lv delta; auto; omega. *)
(*         eapply Mem.perm_valid_block; eauto. *)
(*     + erewrite extcall_bounds; eauto. *)
(*     + apply Forall_forall; intros x IN; erewrite extcall_bounds; eauto; *)
(*       revert x IN; apply Forall_forall; eauto. *)
(*     + apply Forall_forall; intros x IN; erewrite extcall_bounds; eauto; *)
(*       revert x IN; apply Forall_forall; eauto. *)
(* Qed. *)

Lemma fold_left_plus:
  forall r z1 z,
   fold_left
     (fun (acc : Z) (var : ident * Z) => acc + align (Z.max 0 (snd var)) (two_power_nat MA))
     r z1 + align z (two_power_nat MA)
   = fold_left
     (fun (acc : Z) (var : ident * Z) => acc + align (Z.max 0 (snd var)) (two_power_nat MA))
     r (z1 + align z (two_power_nat MA)).
Proof.
  induction r; simpl; intros; eauto.
  rewrite IHr.
  f_equal. omega.
Qed.


Lemma fold_left_plus':
  forall r z1 z,
   fold_left
     (fun (x1 : Z) (y : ident * Z) => align x1 (two_power_nat MA) + Z.max 0 (snd y))
     r z1 + align z (two_power_nat MA)
   = fold_left
       (fun (x1 : Z) (y : ident * Z) => align x1 (two_power_nat MA) + Z.max 0 (snd y))
     r (z1 + align z (two_power_nat MA)).
Proof.
  induction r; simpl; intros; eauto.
  rewrite IHr.
  f_equal.
  rewrite (Z.add_comm z1). rewrite <- align_distr. omega.
  auto.
Qed.

Lemma size_vars_rew:
  forall a r,
    size_vars (a::r) = size_vars r + align (Z.max 0 (snd a)) (two_power_nat MA).
Proof.
  unfold size_vars.
  intros.
  replace (a::r) with ((a::nil) ++ r).
  rewrite fold_left_app. simpl.
  rewrite fold_left_plus. f_equal.
  auto. 
Qed.

Lemma fl_rew:
  let f:= (fun (x1 : Z) (y : ident * Z) => align x1 (two_power_nat MA) + Z.max 0 (snd y)) in
  forall v a,
    align (fold_left f v a) (two_power_nat MA)  = align a (two_power_nat MA) + align (fold_left f v 0) (two_power_nat MA).
Proof.
  induction v; simpl; intros; eauto.
  rewrite align_0; auto; lia.
  rewrite IHv.
  unfold f at 1.
  rewrite <- Mem.align_distr.
  rewrite (IHv (f 0 a)).
  rewrite Z.add_assoc.
  f_equal. unfold f. rewrite align_0; auto; lia. auto.
Qed.

Lemma storebytes_mcs:
  forall f m1 m2 cs bb tb b o v b' o' v' m1' m2'
    (MCS: match_callstack f m1 m2 cs bb tb)
    (SB: Mem.storebytes m1 b o v = Some m1')
    (SB: Mem.storebytes m2 b' o' v' = Some m2'),
    match_callstack f m1' m2' cs bb tb.
Proof.
  intros.
  eapply match_callstack_invariant; eauto.
  - intros. eapply Mem.perm_storebytes_2; eauto.
  - intros. erewrite <- Mem.bounds_of_block_storebytes; eauto.
  - intros. erewrite <- Mem.bounds_of_block_storebytes; eauto.
  - intros. eapply Mem.perm_storebytes_1; eauto.
  - intros. eapply Mem.is_block_dynamic_storebytes; eauto.
  - intros. eapply Mem.is_block_dynamic_storebytes; eauto.
  - apply match_callstack_all_blocks_injected in MCS.
    red; intros.
    eapply MCS; eauto.
    erewrite Mem.bounds_of_block_storebytes; eauto.
Qed.

Ltac genAlloc := Mem.genAlloc.
  (* repeat match goal with *)
  (*        | H: Mem.alloc_bytes ?m ?n = Some (?m',?b') |- _ => *)
  (*          generalize (Mem.alloc_bytes_nextblock _ _ _ _ H); *)
  (*            let y := fresh "NA" in *)
  (*            intros y; subst; clear H; *)
  (*            try rewrite y in * *)
  (*        | H: Mem.alloc ?m ?lo ?hi = Some (?m',?b') |- _ => *)
  (*          generalize (Mem.nextblock_alloc _ _ _ _ _ H); *)
  (*            generalize (Mem.alloc_result _ _ _ _ _ H); *)
  (*            let x := fresh in let y := fresh "NA" in *)
  (*                              intros x y; subst; clear H; *)
  (*                              try rewrite y in * *)
  (*        end. *)

Lemma drop_inject:
  forall ei f m1 m2 b lo hi p m1' (MINJ: Mem.inject true ei f m1 m2)
    (DP: Mem.drop_perm m1 b lo hi p = Some m1')
    b' delta
    (INJ: f b = Some (b',delta)),
  exists m2',
    Mem.drop_perm m2 b' (lo + delta) (hi + delta) p = Some m2' /\ 
    Mem.inject true ei f m1' m2'.
Proof.
  intros.
  inv MINJ.
  destruct (Mem.drop_mapped_inj _ _ _ _ _ _ _ _ _ _ _ _ mi_inj DP
                                (Mem.meminj_no_overlap_impl _ _ mi_no_overlap') INJ)
    as [m2' [A B]].
  exists m2'; split; auto.
  constructor; auto.
  - intros b0 NV.
    apply mi_freeblocks. intro VB. eapply Mem.drop_perm_valid_block_1 in VB; eauto.
  - intros b0 b'0 delta0 INJ0.
    apply mi_mappedblocks in INJ0.
    eapply Mem.drop_perm_valid_block_1 in INJ0; eauto.
  - red; intros.
    eapply mi_no_overlap'; eauto.
    red; rewrite (Mem.drop_perm_bounds _ _ _ _ _ _ DP); auto.
    red; rewrite (Mem.drop_perm_bounds _ _ _ _ _ _ DP); auto.
  - intros; rewrite <- (Mem.is_block_dynamic_drop_perm _ _ _ _ _ _ A).
    intros; rewrite <- (Mem.is_block_dynamic_drop_perm _ _ _ _ _ _ DP).
    rewrite <- (Mem.drop_perm_bounds _ _ _ _ _ _ DP); auto.
    rewrite <- (Mem.drop_perm_bounds _ _ _ _ _ _ A); auto.
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
  erewrite Mem.free_bounds_exact; eauto.
Qed.

Lemma free_in_bound:
  forall m a lo hi m'
    (F : Mem.free m a lo hi = Some m')
    o b
    (IB: Mem.in_bound_m o m' b),
    Mem.in_bound_m o m b.
Proof.
  intros.
  generalize (Mem.free_bounds' _ _ _ _ _ b F).
  unfold Mem.in_bound_m in *.
  intros [A|A]. destr.
  rewrite A in IB; unfold in_bound in IB; simpl in IB; lia.
Qed.

Lemma abi_free:
  forall m b lo hi f,
      Mem.all_blocks_injected f m ->
      Mem.all_blocks_injected f (Mem.unchecked_free m b lo hi).
Proof.
  red. intros m b lo hi f ABI b0 lo0 hi0.
  rewrite (Mem.unchecked_free_bounds').
  intros H.
  repeat destr_in H; inv H.
  - omega.  
  - apply ABI; auto. 
  - eapply ABI; eauto.
Qed.

Fixpoint not_in_stackframe b cs :=
  match cs with
    nil => True
  | Frame tf cenv e te e' sp lo hi :: cs =>
    ~ (Ple lo b /\ Plt b hi) /\ not_in_stackframe b cs
  end.

Lemma ple_plt_dec:
  forall lo b hi',
    Decidable.decidable (Ple lo b /\ Plt b hi').
Proof.
  intros; red. xomega.
Qed.

Lemma match_callstack_range:
  forall f0 m tm cs lo sp,
    match_callstack f0 m tm cs lo sp ->
    forall b,
      ~ (not_in_stackframe b cs) ->
      Plt b lo.
Proof.
  induction 1; simpl; intros.
  exfalso; apply H3; auto.
  apply Decidable.not_and in H0.
  destruct H0.
  apply Decidable.dec_not_not in H0; auto. destruct H0; xomega.
  apply ple_plt_dec.
  apply IHmatch_callstack in H0. inv MENV. xomega.
  apply Decidable.dec_not; auto.
  apply ple_plt_dec.
Qed.

Lemma not_in_stackframe_dec:
  forall x cs, Decidable.decidable (not_in_stackframe x cs).
Proof.
  induction cs; simpl; intros.
  red; auto.
  destruct a.
  apply Decidable.dec_and.
  apply Decidable.dec_not. apply ple_plt_dec.
  auto.
Qed.

Lemma list_forall2_decomp:
  forall {A B} P Q (l1 : list A) (l2: list B),
    list_forall2 (fun a b => P a /\ Q b) l1 l2 <->
    (length l1 = length l2 /\ Forall P l1 /\ Forall Q l2).
Proof.
  split.
  induction 1; simpl; intros; eauto.
  repSplit; auto; try constructor; destr.
revert l2.
  induction l1; des l2.
  constructor.
  intros; destr_and. inv H0; inv H1.
  inv H; inv H0.
  constructor; destr.
  apply IHl1.
  intuition.
Qed.

Lemma smp_same_size:
  forall lm cs m m' tm tm' tlm,
    Mem.nb_boxes_used_m m = Mem.nb_boxes_used_m m' ->
    Mem.nb_boxes_used_m tm = Mem.nb_boxes_used_m tm' ->
    Mem.nb_extra m = Mem.nb_extra m' ->
    Mem.nb_extra tm = Mem.nb_extra tm' ->
    size_mem_preserved (m::lm) (tm::tlm) cs ->
    size_mem_preserved (m'::lm) (tm'::tlm) cs.
Proof.
  clear.
  induction lm; simpl; intros. inv H3. constructor. lia.
  inv H3.
  - eapply IHlm in smp.
    eapply smp_cons_same. eauto. auto. rewrite <- H; eauto. lia. rewrite <- H1; eauto. lia.
    auto. auto. auto. auto.
  - eapply smp_cons; eauto.  lia.  lia. lia. lia. lia.
Qed.

Lemma tpMA_8:
  two_power_nat MA >= 8.
Proof.
  rewrite two_power_nat_two_p.
  change 8 with (two_p (Z.of_nat 3)).
  apply Zle_ge.
  apply two_p_monotone.
  generalize (MA_bound).
  lia.
Qed.


Lemma size_mem_blocks_length:
  forall l,
    align (Mem.size_mem_blocks (map (fun b => (b,0,8)) l) 0) (two_power_nat MA) =
    (two_power_nat MA) * Z.of_nat (length l).
Proof.
  Local Opaque Z.of_nat Z.mul.
  clear; induction l; simpl; intros.
  rewrite align_0; auto. 
  rewrite Mem.size_mem_blocks_rew.
  rewrite IHl. clear IHl.
  rewrite align_0; auto.
  change (0  + Z.max 0 8) with 8.
  rewrite Mem.align_small; auto. lia.
  generalize (tpMA_8). lia.
Qed.

Lemma smp_free:
  forall lm tm sp tfn tm' m e m' tlm cenv le te lo hi cs
    (P : Mem.free tm sp 0 (fn_stackspace tfn) = Some tm')
    (FL : Mem.free_list m (blocks_of_env e) = Some m')
    (ndbl: list_norepet (map fst (map fst (blocks_of_env e))))
    (SMP : size_mem_preserved
             (m :: lm) (tm :: tlm)
             (Frame cenv tfn e le te sp lo hi :: cs))
    (Bnds1: Forall
              (fun bbnds : ident * Z * Z =>
                 Mem.bounds_of_block m (fst (fst bbnds)) =
                 (snd (fst bbnds), snd bbnds)) (blocks_of_env e))
    (Bnds2: Mem.bounds_of_block tm sp = (0, fn_stackspace tfn))
    m'' tm''
    (RES1: MemReserve.release_boxes m' (needed_stackspace (fn_id tfn)) = Some m'')
    (RES2: MemReserve.release_boxes tm' (needed_stackspace (fn_id tfn)) = Some tm'')
  ,
    exists lm' tlm',
      size_mem_preserved
        (m'' :: lm')
        (tm'' :: tlm') cs.
Proof.
  intros.


    Lemma smp_inv:
      forall lm m cs tm tlm cenv tf e le te lo hi sp
        (SMP: size_mem_preserved
                (m::lm) (tm::tlm)
                (Frame cenv tf e le te lo hi sp :: cs)),
      exists m' tm' lm' tlm' C C',
        (((Mem.nb_boxes_used_m m' + needed_stackspace (fn_id tf)
         + size_list_blocks (map size_of_block (blocks_of_env e))  + C
         = Mem.nb_boxes_used_m m + C'
         /\
         Mem.nb_boxes_used_m tm' + needed_stackspace (fn_id tf)
         + Mem.box_span (fn_stackspace tf) + C
         = Mem.nb_boxes_used_m tm + C'))
         /\
         Mem.nb_extra m' + needed_stackspace (fn_id tf) = Mem.nb_extra m
         /\
         Mem.nb_extra tm' + needed_stackspace (fn_id tf) = Mem.nb_extra tm
        )%nat
        /\
        size_mem_preserved (m'::lm') (tm'::tlm') cs.
    Proof.
      induction lm; simpl; intros; eauto.
      - inv SMP.
      - inv SMP.
        + specialize (IHlm _ _ _ _ _ _ _ _ _ _ _ _ smp).
          dex; repeat destr_and.
          exists m', tm', lm', tlm'.
          rewrite H, H3.
          rewrite smp_nb_extra1, smp_nb_extra2.
          exists (C0 + C)%nat, (C'0 + C')%nat.
          repSplit. lia. lia. reflexivity. reflexivity. auto.
        + generalize smp_rec; intro X.
          apply size_mem_preserved_inf in smp_rec. repeat eexists. 5: eauto.
          instantiate (1 := O).
          instantiate (1 := O). lia. lia. lia. lia.
    Qed.
    destruct (smp_inv _ _ _ _ _ _ _ _ _ _ _ _ _ SMP ) as (mm' & tmm' & lm' & tlm' & C & C' & ((eq1 & eq2) & ext1 & ext2) & smp).
    
    Lemma smp_remove_cst:
      (forall lm tlm cs m tm
         (smp: size_mem_preserved (m::lm) (tm::tlm) cs)
         C C' m' tm'
         (sz1: Mem.nb_boxes_used_m m + C =  Mem.nb_boxes_used_m m' + C')
         (sz2: Mem.nb_boxes_used_m tm + C = Mem.nb_boxes_used_m tm' + C')
         (szextra1: Mem.nb_extra m  =  Mem.nb_extra m')
         (szextra2: Mem.nb_extra tm = Mem.nb_extra tm')
        
        ,
          size_mem_preserved (m'::m::lm) (tm'::tm::tlm) cs)%nat.
    Proof.
      induction lm; simpl; intros.
      - inv smp.
        eapply smp_cons_same. constructor. lia. lia. eauto.  eauto. auto. auto. 
      - inv smp.
        + specialize  (IHlm _ _ _ _ smp0).
          econstructor. eapply IHlm. eauto. eauto. eauto. eauto. lia. eauto. eauto. auto. auto.
        + eapply smp_cons_same with (C:=C) (C':=C'); try lia.
          eapply smp_cons; eauto.
    Qed.

    eapply smp_remove_cst with (C:=C) (C':=C') in smp.
    exists (mm'::lm'), (tmm'::tlm').
    eapply smp_same_size.
    5: apply smp. eauto. eauto. auto. auto.

    rewrite <- (free_list_nb_boxes_used _ _ _ FL) in eq1.
    rewrite (nb_boxes_release _ _ _ RES1) in eq1. unfold size_list in eq1. lia.
    rewrite <- (free_nb_boxes_used _ _ _ _ _ P) in eq2.
    rewrite (nb_boxes_release _ _ _ RES2) in eq2. lia.

   generalize (Mem.nb_extra_free_list _ _ _ FL).
    rewrite (nb_extra_release _ _ _ RES1).
    rewrite <- ext1. lia.
    generalize (Mem.nb_extra_free _ _ _ _ _ P).
    rewrite (nb_extra_release _ _ _ RES2).
    rewrite <- ext2. lia.
Qed.

Lemma smp_free':
  forall tm sp tfn tm' m e m' lm tlm cenv le te lo hi cs
    (P : Mem.free tm sp 0 (fn_stackspace tfn) = Some tm')
    (FL : Mem.free_list m (blocks_of_env e) = Some m')
    (SMP : size_mem_preserved
             (m :: lm) (tm :: tlm)
             (Frame cenv tfn e le te sp lo hi :: cs))
    f bound bound'
    (MCS : match_callstack f m tm
                           (Frame cenv tfn e le te sp lo hi :: cs)
                           bound bound')
    m'' tm''
    (RES1: MemReserve.release_boxes m' (needed_stackspace (fn_id tfn)) = Some m'')
    (RES2: MemReserve.release_boxes tm' (needed_stackspace (fn_id tfn)) = Some tm''),
    exists lm' tlm', size_mem_preserved (m'' :: lm') (tm'' :: tlm') cs.
Proof.
  clear. intros.
  inv MCS.
  eapply smp_free; eauto.
  apply Forall_forall. intros x IN.
  unfold blocks_of_env in IN.
  rewrite in_map_iff in IN. dex; destr_and. des x0. des p.
  apply PTree.elements_complete in H0.
  eapply BOUND' in H0. auto.
Qed.

Lemma smp_ext:
  forall lm tlm cenv cenv' f e le le' te te' sp sp' lo lo' hi hi' cs,
  size_mem_preserved lm tlm (Frame cenv f e le te sp lo hi :: cs) ->
  size_mem_preserved lm tlm (Frame cenv' f e le' te' sp' lo' hi' :: cs).
Proof.
  induction lm; simpl; intros; eauto.
  inv H.
  inv H. exploit IHlm. apply smp. intro SMP.
  eapply smp_cons_same with (C:=C); eauto.
  clear IHlm.
  eapply smp_cons; eauto; rewrite H, H0 in *; lia. 
Qed.

Lemma nodbl_nodup:
  forall e,
    nodbl e ->
    NoDup (blocks_of_env e).
Proof.
  intros.
  unfold blocks_of_env, block_of_binding.
  red in H.
  generalize (PTree.elements_keys_norepet e).
  intros. rewrite list_norepet_NoDup.
  assert (ND: forall id b sz, In (id,(b,sz)) (PTree.elements e) ->
                         ~ (exists id' p, id' <> id /\ In (id',p) (PTree.elements e) /\ fst p = b)).
  {
    intros.
    apply PTree.elements_complete in H1.
    eapply H in H1.
    intro NEX; dex; destr_and. des H3. apply H1; eexists; eexists; repSplit; eauto.
    apply PTree.elements_complete; auto.
  }
  clear H.
  revert H0 ND.
  generalize (PTree.elements e).
  clear. induction l; simpl; intros; eauto.
  constructor.
  des a. des p0.
  inv H0.
  trim IHl; auto.
  trim IHl; eauto.
  intros. intro. dex; destr. des p0. des H0. des a.
  exploit ND. right; eexact H.
  exists id', (b0,z0).  repSplit; destr. auto.
  constructor; auto.
  rewrite in_map_iff in *.
  intro NIN. dex; destr. des x. des p0. des NIN. inv e. 
  destruct (peq i p); subst; auto.
  apply H2. exists (p,(b,z)); split; auto.
  generalize (ND _ _ _ (or_intror i0)).
  intro A; exfalso; apply A.
  exists p.
  exists (b,z). split. auto. split; auto.
Qed.

Lemma env_ext_blocks_permut:
  forall x e
    (EXT: forall id, x!id = e!id)
    (Nd1: nodbl x)
    (Nd2: nodbl e),
    Permutation (blocks_of_env x) (blocks_of_env e).
Proof.
  clear.
  intros. apply NoDup_Permutation.
  apply nodbl_nodup; auto.
  apply nodbl_nodup; auto.
  intros.
  destruct x0.
  unfold blocks_of_env, block_of_binding.
  rewrite ! in_map_iff.

  split;
  intros [[i [b y]] [EQ IN]]; inv EQ;
  apply PTree.elements_complete in IN;
  (rewrite EXT in IN || rewrite <- EXT in IN);
  apply PTree.elements_correct in IN;
  exists (i,(b,z)); auto.
Qed.

Lemma mcs_ext:
  forall f0 m tm m' tm' cs sp sp'
    (MCS : match_callstack f0 m' tm' cs sp sp')
    (BND: forall b, Mem.bounds_of_block m b = Mem.bounds_of_block m' b)
    (BND': forall b, Mem.bounds_of_block tm b = Mem.bounds_of_block tm' b)
    (PERM: forall b o k p, Mem.perm m b o k p <-> Mem.perm m' b o k p)
    (PERM': forall b o k p, Mem.perm tm b o k p <-> Mem.perm tm' b o k p)
    (DYN: forall b, Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b)
    (DYN': forall b, Mem.is_dynamic_block tm b <-> Mem.is_dynamic_block tm' b),
    match_callstack f0 m tm cs sp sp'.
Proof.
  induction 1; simpl; intros.
  - econstructor; eauto.
    red; intros. eapply H0; eauto. rewrite <- BND; eauto.
  - constructor; eauto.
    + red; intros. rewrite PERM0 in H0; eauto.
    + red; intros. rewrite BND; eauto.
    + red; intros. rewrite PERM'. eauto.
    + rewrite BND'; eauto.
    + apply Forall_forall. intros. rewrite DYN.
      revert x H. apply Forall_forall. eauto.
    + rewrite DYN'; eauto.
Qed.


Lemma free_list_extra:
 forall f0 n
   m' m'' cs tm'
   (MCS: match_callstack f0 m' tm' cs (Mem.nextblock m') (Mem.nextblock tm'))
   (MINJ: Mem.inject true expr_inj_se f0 m' tm')
   (FL: MemReserve.release_boxes m' n = Some m'')
   (LE: (n <= Mem.nb_extra tm')%nat),
 exists (tm'' : mem),
   MemReserve.release_boxes tm' n = Some tm'' /\
   Mem.inject true expr_inj_se f0 m'' tm'' /\
   match_callstack f0 m'' tm'' cs (Mem.nextblock m'') (Mem.nextblock tm'').
Proof.
  intros.
  unfold MemReserve.release_boxes in *. destr_in FL. inv FL.
  destr. eexists; repSplit; eauto.

  - inv MINJ; constructor; simpl; eauto.
    inv mi_inj; constructor; simpl; intros; eauto.
    + unfold Mem.perm in *; simpl; eauto.
    + unfold Mem.in_bound_m, in_bound, Mem.bounds_of_block in *; simpl; eauto.
    + revert mi_size_mem. clear.
      unfold Mem.nb_boxes_used_m. simpl.
      unfold Mem.mk_block_list, Mem.size_block. simpl. intuition lia.
  - simpl.
    eapply mcs_ext. eauto.
    reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. 
Qed.

Lemma smp_extra_enough:
  forall lm m tm tlm cenv tfn e le te sp lo hi cs
    (SMP : size_mem_preserved (m :: lm) (tm :: tlm) (Frame cenv tfn e le te sp lo hi :: cs)),
    (needed_stackspace (fn_id tfn) <= Mem.nb_extra tm)%nat.
Proof.
  induction lm; simpl; intros.
  inv SMP.
  inv SMP.
  exploit IHlm. eauto. lia.
  rewrite smp_nb_extra2. lia.
Qed.



Lemma transl_step_correct:
  forall S1 t S2, Csharpminor.step ge needed_stackspace S1 t S2 ->
  forall T1, match_states S1 T1 ->
  (exists T2, plus (fun ge => step ge needed_stackspace ) tge T1 t T2 /\ match_states S2 T2)
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 T1)%nat.
Proof.
  induction 1; intros T1 MSTATE; inv MSTATE.
 
- (* skip seq *)
  monadInv TR. left.
  dependent induction MK.
  econstructor; split. 
  apply plus_one. constructor.
  econstructor; eauto.
  econstructor; split.
  apply plus_one. constructor.
  eapply match_state_seq; eauto. 
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split. eapply plus_left. constructor. apply plus_star; eauto. traceEq.
  auto.
- (* skip block *)
  monadInv TR. left.
  dependent induction MK.
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto.
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split. eapply plus_left. constructor. apply plus_star; eauto. traceEq.
  auto.
- (* skip call *) 
  monadInv TR. left. 
  exploit match_is_call_cont; eauto. intros [tk' [A [B C]]].
  
  Lemma freelist_free_release_match:
    forall f cenv tf e le te sp lo hi cs m m' m'' tm lm tlm,
      Mem.free_list m (blocks_of_env e) = Some m' ->
      MemReserve.release_boxes m' (needed_stackspace (fn_id tf)) = Some m'' ->
      match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
      size_mem_preserved (m :: lm) (tm :: tlm) (Frame cenv tf e le te sp lo hi :: cs) ->
      Mem.inject true expr_inj_se f m tm ->
      exists tm' tm'' lm' tlm',
        Mem.free tm sp 0 (fn_stackspace tf) = Some tm' /\
        MemReserve.release_boxes tm' (needed_stackspace (fn_id tf)) = Some tm'' /\ 
        match_callstack f m'' tm'' cs (Mem.nextblock m'') (Mem.nextblock tm'') /\
        Mem.inject true expr_inj_se f m'' tm'' /\
        size_mem_preserved (m'' :: lm') (tm'' :: tlm') cs.
  Proof.
    intros f cenv tf e le te sp lo hi cs m m' m'' tm lm tlm FL RB MCS SMP MINJ.

    exploit match_callstack_freelist; eauto.  
    {
      intros.
      inv MCS. red in BOUND'.
      unfold blocks_of_env, block_of_binding in H.
      rewrite in_map_iff in H.
      destruct H as [[i [b' z]] [D E]]. inv D.
      generalize (PTree.elements_complete _ _ _ E). intro.    
      erewrite BOUND'; eauto.
    } 
    inv MCS; auto.
    intros [tm' [P [Q R]]].

    inversion MCS; subst.

    exploit free_list_extra. eauto. eauto. eauto. 
    etransitivity. eapply smp_extra_enough; eauto.
    rewrite (Mem.nb_extra_free _ _ _ _ _ P). lia.
    intros (tm'' & RB' & MINJ' & MCS').

    exploit smp_free'. eauto. eauto. eauto. eauto.
    eauto. eauto.
    intros (lm' & tlm' & SMP').

    exists tm', tm'', lm', tlm'.
    repSplit; eauto.
  Qed.

  exploit freelist_free_release_match; eauto.
  replace (Csharpminor.fn_id f) with (fn_id tfn) in H1. eauto.
  revert TRF; unfold transl_funbody; simpl.
  clear. intros. monadInv TRF. reflexivity.

  intros; dex; repeat destr_and.

  econstructor; split.
  eapply plus_right. eexact A.  
  eapply step_skip_call. auto. eauto. 
  eauto.
  traceEq.
  econstructor; eauto.
  apply expr_inj_se_vundef.

- (* set *)
  monadInv TR.
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  left; econstructor; split.
  apply plus_one. econstructor; eauto. 
  econstructor; eauto. 
  eapply match_callstack_set_temp; eauto. 
  eapply smp_ext; eauto.
  
- (* store *)
  monadInv TR. 
  exploit transl_expr_correct. eauto. eauto. eexact H. eauto. 
  intros [tv1 [EVAL1 VINJ1]].
  exploit transl_expr_correct. eauto. eauto. eexact H0. eauto. 
  intros [tv2 [EVAL2 VINJ2]].
  generalize  (Mem.storev_mapped_inject _ _ wf_inj_expr_inj_se
                                               _ _ _ _ _ _ _ _ _
                                               (match_callstack_all_blocks_injected _ _ _ _ _ _ MCS)
                                               MINJ H1 VINJ1 VINJ2
              ); eauto.
  intros [tm' [STORE' MINJ']].
  
  left; econstructor; split.
  apply plus_one. econstructor; eauto. 
  econstructor; eauto.
  inv VINJ1; simpl in H1; try discriminate. 
  rewrite (Mem.nextblock_storev _ _ _ _ _ H1).
  rewrite (Mem.nextblock_storev _ _ _ _ _ STORE').
  unfold Mem.storev in STORE', H1.
  destruct (Mem.mem_norm tm tv1) eqn:?; try discriminate.
  destruct (Mem.mem_norm m vaddr) eqn:?; try discriminate.

  eapply match_callstack_invariant with f0 m tm; eauto.
  + intros. eapply Mem.perm_store_2; eauto.
  + intros. erewrite <- Mem.bounds_of_block_store; eauto.
  + intros. erewrite <- Mem.bounds_of_block_store; eauto.
  + intros. eapply Mem.perm_store_1; eauto.
  + intros; eapply Genv.store_dyn; eauto.
  + intros; eapply Genv.store_dyn; eauto.
  + eapply match_callstack_all_blocks_injected in MCS; eauto.
    red; intros.
    erewrite <- Mem.bounds_of_block_store in H3; eauto.
  + eapply smp_same_size.
   symmetry; eapply storev_nb_boxes_used_m; eauto.
    symmetry; eapply storev_nb_boxes_used_m; eauto.

   eapply storev_nb_extra; eauto.
    eapply storev_nb_extra; eauto.
    eauto.
    
- (* call *)
  simpl in H1. exploit functions_translated; eauto. intros [tfd [FIND TRANS]].
  monadInv TR.
  exploit transl_expr_correct; eauto. intros [tvf [EVAL1 VINJ1]].
  assert (Mem.mem_norm tm tvf = Mem.mem_norm m vf).
  {
    exploit match_callstack_match_globalenvs; eauto. intros [bnd MG].
    eapply val_inject_function_pointer; eauto.
    eapply match_callstack_all_blocks_injected; eauto.
  }
  exploit transl_exprlist_correct; eauto.
  intros [tvargs [EVAL2 VINJ2]].
  left; econstructor; split.
  apply plus_one. eapply step_call; eauto.
  instantiate (1:=tfd).  unfold Genv.find_funct in *.
  rewrite  H2. auto.
  apply sig_preserved; eauto.
  econstructor; eauto.
  eapply match_Kcall with (cenv' := cenv); eauto.
  red; auto.

- (* builtin *)
  monadInv TR.
  exploit transl_exprlist_correct; eauto.
  intros [tvargs [EVAL2 VINJ2]].
  exploit match_callstack_match_globalenvs; eauto. intros [hhi' MG].
  exploit (external_call_mem_inject ef wf_inj_expr_inj_se); eauto.
  eapply match_callstack_all_blocks_injected; eauto.
  eapply inj_preserves_globals; eauto.
  eapply expr_list_inject_list_ei; eauto.
  intros [f' [vres' [tm' [EC [ABI [VINJ [MINJ' [UNMAPPED [OUTOFREACH [INCR [SEP [CC' EXTRA_BUILTIN]]]]]]]]]]]].


  left; econstructor; split.
  apply plus_one. econstructor. eauto. 
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. eexact varinfo_preserved.
  assert (MCS': match_callstack f' m' tm'
                 (Frame cenv tfn e le te sp lo hi :: cs)
                 (Mem.nextblock m') (Mem.nextblock tm')).
  {
    apply match_callstack_incr_bound with (Mem.nextblock m) (Mem.nextblock tm).
    eapply match_callstack_invariant. eauto.
    auto.
    intros; eapply external_call_max_perm; eauto.
    intros; symmetry; eapply external_call_bounds_mask; eauto.
    intros; symmetry; eapply external_call_bounds_mask; eauto.
    intros. erewrite <- external_call_perm; eauto.
    intros; eapply external_call_dyn; eauto.
    intros; eapply external_call_dyn; eauto.
    intros. des (f0 b). des p. eapply INCR; eauto.
    des (f' b). des p. generalize (SEP _ _ _ Heqo Heqo0). intros [A B]; exfalso; apply A; auto.
    intros. des (f0 b). des p. erewrite INCR in H1; eauto.
    generalize (SEP _ _ _ Heqo H1). intros [A B]; exfalso; apply B; auto.
    auto. 
    eapply external_call_nextblock; eauto.
    eapply external_call_nextblock; eauto.
  }

  destruct CC' as (C & C' & EQ1 & EQ2).
  econstructor; eauto.
Opaque PTree.set.
  unfold set_optvar. destruct optid; simpl. 
  eapply match_callstack_set_temp; eauto. 
  auto.


  eapply smp_ext.
  exploit size_mem_preserved_inf. apply SMP. intro LE.
  eapply smp_cons_same. apply SMP. auto. eauto. eauto.
  rewrite ! nb_boxes_sep.
  instantiate (1 := C'). instantiate (1 := C). lia.
  rewrite ! nb_boxes_sep. lia. lia. lia.
    
- (* seq *)
  monadInv TR. 
  left; econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto.
  econstructor; eauto.
- (* seq 2 *)
  right. split. auto. split. auto. econstructor; eauto. 

- (* ifthenelse *)
  monadInv TR.
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  left. 
  exists (State tfn (if negb (Int.eq b Int.zero) then x0 else x1) tk sp te tm); split.
  apply plus_one. eapply step_ifthenelse; eauto.
  destruct (Mem.norm_inject_val' _ _ wf_inj_expr_inj_se _ _ _ _ _ 
                                   (match_callstack_all_blocks_injected _ _ _ _ _ _ MCS)
                                   MINJ VINJ); auto; destr.

  econstructor; eauto. destruct (negb); auto.

- (* loop *)
  monadInv TR.
  left; econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto.
  econstructor; eauto. simpl. rewrite EQ; auto. 

- (* block *)
  monadInv TR.
  left; econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto.
  econstructor; eauto.

- (* exit seq *)
  monadInv TR. left.
  dependent induction MK.
  econstructor; split. 
  apply plus_one. constructor.
  econstructor; eauto. simpl. auto.
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split; auto. eapply plus_left. constructor. apply plus_star; eauto. traceEq.
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split; auto. eapply plus_left.
  simpl. constructor. apply plus_star; eauto. traceEq.

- (* exit block 0 *)
  monadInv TR. left.
  dependent induction MK.
  econstructor; split.
  simpl. apply plus_one. constructor. 
  econstructor; eauto.
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split; auto. simpl. 
  eapply plus_left. constructor. apply plus_star; eauto. traceEq.

- (* exit block n+1 *)
  monadInv TR. left.
  dependent induction MK.
  econstructor; split.
  simpl. apply plus_one. constructor. 
  econstructor; eauto. auto. 
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split; auto. simpl. 
  eapply plus_left. constructor. apply plus_star; eauto. traceEq.

- (* switch *)
  simpl in TR. destruct (switch_table cases O) as [tbl dfl] eqn:STBL. monadInv TR.
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]]. 
  assert (SA: switch_argument tm islong tv n).
  { generalize (match_callstack_all_blocks_injected _ _ _ _ _ _ MCS). intro.
    inv H0; constructor.
    generalize (Mem.norm_inject_val' _ _ wf_inj_expr_inj_se _ _ _ _ _ 
                                     (match_callstack_all_blocks_injected _ _ _ _ _ _ MCS)
                                     MINJ VINJ).
    rewrite H2; intro A; inv A. auto.
    generalize (Mem.norm_inject_val' _ _ wf_inj_expr_inj_se _ _ _ _ _ 
                                     (match_callstack_all_blocks_injected _ _ _ _ _ _ MCS)
                                     MINJ VINJ).
    rewrite H2; intro A; inv A. auto.
  }
  exploit switch_descent; eauto. intros [k1 [A B]].
  exploit switch_ascent; eauto. eapply (switch_table_select n).
  rewrite STBL; simpl. intros [k2 [C D]].
  exploit transl_lblstmt_suffix; eauto. eapply (switch_table_select n).
  simpl. intros [body' [ts' E]].
  exploit switch_match_states; eauto. intros [T2 [F G]].
  left; exists T2; split.
  eapply plus_star_trans. eapply B.  
  eapply star_left. econstructor; eauto. 
  eapply star_trans. eexact C. 
  apply plus_star. eexact F.
  reflexivity. reflexivity. traceEq.
  auto.

- (* return none *)
  monadInv TR. left.

  exploit freelist_free_release_match; eauto.
  replace (Csharpminor.fn_id f) with (fn_id tfn) in H0. eauto.
  revert TRF; unfold transl_funbody; simpl.
  clear. intros. monadInv TRF. reflexivity.
  intros; dex; repeat destr_and.
  
  econstructor; split.
  apply plus_one. eapply step_return_0. eauto.  eauto.
  econstructor; eauto.
  eapply match_call_cont; eauto.
  apply expr_inj_se_vundef.

- (* return some *)
  monadInv TR. left. 
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  exploit freelist_free_release_match; eauto.
  replace (Csharpminor.fn_id f) with (fn_id tfn) in H1. eauto.
  revert TRF; unfold transl_funbody; simpl.
  clear. intros. monadInv TRF. reflexivity.

  intros; dex; repeat destr_and.
  econstructor; split.
  apply plus_one. eapply step_return_1. eauto. eauto. eauto.
  econstructor; eauto.
  subst; eauto. eapply match_call_cont; eauto.

- (* label *)
  monadInv TR.
  left; econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto.

- (* goto *)
  monadInv TR.
  exploit transl_find_label_body; eauto. 
  intros [ts' [tk' [xenv' [A [B C]]]]].
  left; econstructor; split.
  apply plus_one. apply step_goto. eexact A. 
  econstructor; eauto.

- (* internal call *)    
  monadInv TR. generalize EQ; clear EQ; unfold transl_function.
  set (ce := fst (build_compilenv f)).
  set (sz := snd (build_compilenv f)).
  destruct zle; try congruence.
  intro TRBODY.
  generalize TRBODY; intro TMP. monadInv TMP.

  set (tf := mkfunction (Csharpminor.fn_id f) (Csharpminor.fn_sig f) 
                        (Csharpminor.fn_params f)
                        (Csharpminor.fn_temps f)
                        sz
                        x0
                        (build_compilenv_size_pos f)
      ) in *.
   caseEq (Mem.alloc tm 0 ((fn_stackspace tf)) Normal); try discriminate. 
  + destruct p as [tm' sp]. intros ALLOC'. 
    assert (LNR_sort: list_norepet (map fst (varsort' (Csharpminor.fn_vars f)))).
    {
      clear - H.
      generalize (varsort'_permut (Csharpminor.fn_vars f)). intro A.
      apply Permutation_map with (f:=fst) in A.
      eapply permutation_norepet; eauto.
    }
    generalize (alloc_variables_left_right _ _ _ _ _ LNR_sort H2). intros [x AVLR].
    exploit match_callstack_function_entry; eauto. 
    * unfold tf; unfold transl_function.
      fold sz. 
      destr; try omega. 
    * instantiate (1:=fn_stackspace tf). lia.  
    * rewrite (surjective_pairing (build_compilenv _)). f_equal. 
    * etransitivity. apply align_le with (y:=two_power_nat MA). auto. auto.  
    * instantiate (1:=m1).
      instantiate(1:=x). destruct AVLR as [AVR ID]. auto. 
    * intros [f2 [MCS2 MINJ2]].
      destruct AVLR as [AVR ID].

      Lemma reserve_boxes_inject:
        forall f m tm (MINJ: Mem.inject true expr_inj_se f m tm)
          n m' (RB: MemReserve.reserve_boxes m n = Some m'),
        exists tm',
          MemReserve.reserve_boxes tm n = Some tm' /\
          Mem.inject true expr_inj_se f m' tm'.
      Proof.
        unfold MemReserve.reserve_boxes.
        intros f m tm MINJ n m'.
        destr. intro A; inv A. destr.
        - eexists; split; eauto.
          inv MINJ. constructor; simpl; intros; eauto.
          + inv mi_inj; constructor; simpl; intros; eauto.
            * unfold Mem.perm in *; destr. eauto.
            * unfold Mem.in_bound_m, in_bound, Mem.bounds_of_block in *; simpl in *. eauto.
            * unfold Mem.nb_boxes_used_m, Mem.mk_block_list, Mem.size_block in *. simpl.
              intuition lia. 
          + red. simpl. eapply mi_mappedblocks; eauto.
        - exfalso.
          inv MINJ. inv mi_inj. intuition lia.
      Qed.

      exploit reserve_boxes_inject. eauto. eauto. intros (tm'0 & RB & MINJ').


      Lemma reserve_boxes_mcs:
        forall f m tm cs bnd tbnd (MINJ: match_callstack f m tm cs bnd tbnd)
          n m' (RB: MemReserve.reserve_boxes m n = Some m')
          tm' (RB': MemReserve.reserve_boxes tm n = Some tm'),
          match_callstack f m' tm' cs bnd tbnd.
      Proof.
        induction 1.
        - intros. econstructor; eauto.
          red; intros.
          eapply H0; eauto. rewrite <- H3.
          unfold MemReserve.reserve_boxes in *. destr_in RB. destr_in RB'.
          inv RB; inv RB'. reflexivity.
        - intros.
          econstructor; eauto. clear IHMINJ.
          + unfold MemReserve.reserve_boxes in *. destr_in RB; destr_in RB'; inv RB; inv RB'.
            red; intros. unfold Mem.perm in *; eauto.
          + unfold MemReserve.reserve_boxes in *. destr_in RB; destr_in RB'; inv RB; inv RB'.
            red; intros. rewrite <- BOUND'; eauto. reflexivity.
          + unfold MemReserve.reserve_boxes in *. destr_in RB; destr_in RB'; inv RB; inv RB'.
            red; intros. unfold Mem.perm in *; eauto.
          + unfold MemReserve.reserve_boxes in *. destr_in RB; destr_in RB'; inv RB; inv RB'.
            rewrite <- bnd_sp; eauto.
          + rewrite Forall_forall in *.
            intros. eapply ndyn_e in H. revert H.
            unfold MemReserve.reserve_boxes in *. destr_in RB; destr_in RB'; inv RB; inv RB'.
            unfold Mem.is_dynamic_block; simpl. auto.
          + revert ndyn_sp.
            unfold MemReserve.reserve_boxes in *. destr_in RB; destr_in RB'; inv RB; inv RB'.
            unfold Mem.is_dynamic_block; simpl. auto.
      Qed.

      exploit reserve_boxes_mcs. exact MCS2. eauto. eauto. intro MCS3.
      
      (* generalize (mcs_alloc_bytes _ _ _ _ _ _ _ _ _ _ _ _ MCS2). _ _ _ _ _ pf H6). *)
      left; econstructor; split.
      apply plus_one. econstructor; simpl; eauto. 
      econstructor. eexact TRBODY. eauto. eexact MINJ'.
      apply mcs_frame_env_ext with (x:=x); auto.
      replace (Mem.nextblock m2) with (Mem.nextblock m1).
      replace (Mem.nextblock tm'0) with (Mem.nextblock tm').
      apply MCS3.
      unfold MemReserve.reserve_boxes in RB. destr_in RB; inv RB. reflexivity.
      unfold MemReserve.reserve_boxes in H4. destr_in H4; inv H4. reflexivity.

      constructor; eauto.
      {
        rewrite (nb_boxes_reserve _ _ _ H4).
        rewrite (alloc_variables_size _ _ _ _ _ AVR).
        rewrite (fun lnr => avr_size_vars'' _ _ _ _ lnr AVR).
        unfold tf; simpl.

        assert (NDX: nodbl x).
        eapply alloc_variables_right_nodbl; eauto.
        * rewrite map_rev.
          apply list_norepet_rev.
          generalize (varsort'_permut (Csharpminor.fn_vars f)). intro.
          apply Permutation_map with (f:=fst) in H5.
          eapply permutation_norepet; eauto. 
        * intros; rewrite PTree.gempty; auto.
        * red; intros id b sz'. rewrite PTree.gempty; auto. congruence.
        * red; intros id b sz'. rewrite PTree.gempty; auto. congruence.
        * unfold size_list_blocks.
          erewrite Mem.fold_left_plus_permut.
          2: apply Permutation_map.
          2: apply Permutation_map.
          2: apply env_ext_blocks_permut. instantiate (1:=e). lia. auto.
          auto.
          red.  intros id b sz0 EID. rewrite ID in EID.
          apply NDX in EID.
          intro EX; dex; destr.
          apply EID.
          exists id', p; split; auto. destr. rewrite <- ID. destr.  
          
        

        (* lia. *)
        (* erewrite (Mem.alloc_bytes_size_mem _ _ m2 l); eauto. *)
        (* erewrite Mem.alloc_bytes_length; eauto. *)
        (* destruct AVLR. *)
        (* erewrite alloc_variables_size; eauto. *)
        (* generalize (Mem.size_mem_aligned' m). intro AL. *)
        (* rewrite fr_rew; auto. rewrite <- AL. *)
        (* erewrite avr_size_vars. *)
        (* rewrite (fr_permut _ _ _ (Permutation_rev _)). *)
        (* erewrite (fr_permut _  (rev (blocks_of_env e))). lia. *)
        (* + instantiate (1:=x). *)
        (*   apply Permutation_rev'. *)
        (*   assert (NDX: nodbl x). *)
        (*   eapply alloc_variables_right_nodbl; eauto. *)
        (*   * rewrite map_rev. *)
        (*     apply list_norepet_rev. *)
        (*     generalize (varsort'_permut (Csharpminor.fn_vars f)). intro. *)
        (*     apply Permutation_map with (f:=fst) in H7. *)
        (*     eapply permutation_norepet; eauto.  *)
        (*   * eauto. intros; rewrite PTree.gempty; auto. *)
        (*   * red; intros id b sz'. rewrite PTree.gempty; auto. congruence. *)
        (*   * red; intros id b sz'. rewrite PTree.gempty; auto. congruence. *)
        (*   * apply env_ext_blocks_permut; auto. *)
        (*     red.  intros id b sz0 EID. rewrite H6 in EID. *)
        (*     apply NDX in EID. *)
        (*     intro EX; dex; destr. *)
        (*     apply EID. *)
        (*     exists id', p; split; auto. destr. rewrite <- H6. destr.   *)
          
        * rewrite map_rev.
          apply list_norepet_rev.
          generalize (varsort'_permut (Csharpminor.fn_vars f)). intro.
          apply Permutation_map with (f:=fst) in H5.
          eapply permutation_norepet; eauto. 
      }
      {
        rewrite (nb_boxes_reserve _ _ _ RB).
        rewrite (Mem.nb_boxes_alloc _ _ _ _ _ _ ALLOC').
        rewrite Z.max_r.
        unfold tf; simpl. lia. destruct tf. simpl. lia.
      }
      {
        inv MINJ'. inv mi_inj. intuition lia. 
      }
      Lemma reserve_boxes_extra:
        forall m n m' (RES: MemReserve.reserve_boxes m n = Some m'),
          (Mem.nb_extra m' = Mem.nb_extra m + n)%nat.
      Proof.
        unfold MemReserve.reserve_boxes. intros. destr_in RES; inv RES. reflexivity.
      Qed.
      rewrite (reserve_boxes_extra _ _ _ H4).
      Lemma alloc_variables_nb_extra:
        forall e m l e' m' (AV: alloc_variables e m l e' m'),
          Mem.nb_extra m' = Mem.nb_extra m.
      Proof.
        induction 1; simpl; intros; eauto.
        rewrite IHAV. symmetry; eapply Mem.nb_extra_alloc; eauto.
      Qed.
      rewrite (alloc_variables_nb_extra _ _ _ _ _ H2). unfold tf; simpl. reflexivity.
      rewrite (reserve_boxes_extra _ _ _ RB).
      rewrite (Mem.nb_extra_alloc _ _ _ _ _ _ ALLOC').
      unfold tf; simpl. reflexivity. 
      
      inv MK; simpl in ISCC; contradiction || econstructor; eauto.

  + intro A. exfalso; eapply alloc_variables_alloc_sp_ok; eauto.
    eapply match_callstack_all_blocks_injected; eauto.
    unfold transl_function.
    destr; try omega. 
    eexact TRBODY.
    unfold sz in l. lia.
    erewrite alloc_variables_alloc_sp in A.
    assert (non_dec: forall {A: Type} (a: option A), { a = None } + {a <> None}).
    {
      intros. destruct a. right; congruence. left; auto.
    }
    destruct (non_dec _
                      (Mem.alloc
                   tm 0
                   (align (big_var_space
                             (rev (varsort' (Csharpminor.fn_vars f)))
                             0) (two_power_nat MA)) Normal)).
    auto.
    exfalso. apply ( Mem.alloc_less_ok _ _ _ _ A n).
    instantiate (1:=f).
    split. 
    * apply Zge_le. apply fr_align_pos. lia.
    * etransitivity. apply sp_le_vars_right. apply align_le. auto. 
    * unfold transl_function.
      destr; try omega.
      unfold sz in l; lia.
      
- (* external call *)
    monadInv TR.
    exploit match_callstack_match_globalenvs; eauto. intros [hi' MG].
    exploit (external_call_mem_inject ef wf_inj_expr_inj_se); eauto.
    eapply match_callstack_all_blocks_injected; eauto.
    eapply inj_preserves_globals; eauto.
    eapply expr_list_inject_list_ei; eauto.
    intros [f' [vres' [tm' [EC [ABI [VINJ [MINJ' [UNMAPPED [OUTOFREACH [INCR [SEP EQsz]]]]]]]]]]].
 
    assert (exists C C', Mem.nb_boxes_used_m m' + C = Mem.nb_boxes_used_m m + C' /\
                    Mem.nb_boxes_used_m tm' + C = Mem.nb_boxes_used_m tm + C')%nat as SZ.
    {
      rewrite ! nb_boxes_sep.
      des EQsz. dex.
      exists C,  C'. lia. 
    }
   
    assert (Mem.nb_extra m' = Mem.nb_extra m /\ Mem.nb_extra tm' = Mem.nb_extra tm) as EXTRA_BUILTIN.
    lia. clear EQsz.


    left; econstructor; split.
    apply plus_one. econstructor. eauto. 
    eapply external_call_symbols_preserved; eauto.
    exact symbols_preserved. eexact varinfo_preserved.
    dex. destr_and.
    econstructor; eauto.
    apply match_callstack_incr_bound with (Mem.nextblock m) (Mem.nextblock tm).
    {
      apply match_callstack_incr_bound with (Mem.nextblock m) (Mem.nextblock tm).
      eapply match_callstack_invariant. eauto.
      auto.
      intros; eapply external_call_max_perm; eauto.
      intros; symmetry; eapply external_call_bounds_mask; eauto.
      intros; symmetry; eapply external_call_bounds_mask; eauto.
      intros. erewrite <- external_call_perm; eauto.
      intros; eapply external_call_dyn; eauto.
      intros; eapply external_call_dyn; eauto.
      intros. des (f b). des p. eapply INCR; eauto.
      des (f' b). des p. generalize (SEP _ _ _ Heqo Heqo0). intros [A B]; exfalso; apply A; auto.
      intros. des (f b). des p. erewrite INCR in H2; eauto.
      generalize (SEP _ _ _ Heqo H2). intros [A B]; exfalso; apply B; auto.
      auto.
      apply Ple_refl.
      apply Ple_refl.
    }
    eapply external_call_nextblock; eauto.
    eapply external_call_nextblock; eauto.

    des SZ.
    eapply smp_cons_same. eauto.
    apply size_mem_preserved_inf in SMP. auto.
    eauto. eauto. auto. auto.
  
- (* return *) 
  inv MK. simpl.
  left; econstructor; split.
  + apply plus_one. econstructor; eauto. 
  + unfold set_optvar. destruct optid; simpl; econstructor; eauto.
    eapply match_callstack_set_temp; eauto.
    eapply smp_ext; eauto.
Qed.

Lemma match_globalenvs_init:
  forall fid sg m,
  Genv.init_mem fid sg prog = Some m ->
  match_globalenvs (Mem.flat_inj (Mem.nextblock m)) (Mem.nextblock m).
Proof.
  intros. constructor.
  intros. unfold Mem.flat_inj. apply pred_dec_true; auto. 
  intros. unfold Mem.flat_inj in H0. 
  destruct (plt b1 (Mem.nextblock m)); congruence.
  intros. eapply Genv.find_symbol_not_fresh; eauto.
  intros. eapply Genv.find_funct_ptr_not_fresh; eauto.
  intros. eapply Genv.find_var_info_not_fresh; eauto. 
Qed.

Lemma transl_initial_states:
  forall sg S, Csharpminor.initial_state prog sg S ->
  exists R, Cminor.initial_state tprog sg R /\ match_states S R.
Proof.
  induction 1.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  econstructor; split.
  - econstructor.
    + eapply (Genv.init_mem_transf_partial _ _ TRANSL); eauto.
      intros a b0 TR'.
      unfold Csharpminor.fid, fid.
      des a; des b0; try monadInv TR'.
      unfold transl_function in EQ; try monadInv EQ.
      repeat destr_in EQ.
      unfold transl_funbody in EQ.
      monadInv EQ. auto.
    + simpl. fold tge. rewrite symbols_preserved.
      replace (prog_main tprog) with (prog_main prog). eexact H0.
      symmetry. unfold transl_program in TRANSL.
      eapply transform_partial_program_main; eauto.
    + eexact FIND. 
    + rewrite <- H2. apply sig_preserved; auto.
  - eapply match_callstate with (f := Mem.flat_inj (Mem.nextblock m0)) (cs := @nil frame) (cenv := PTree.empty Z).
    auto.
    eapply Genv.initmem_inject; eauto.
    apply mcs_nil with (Mem.nextblock m0). eapply match_globalenvs_init; eauto. 
    red; intros.
    unfold Mem.flat_inj.
    destr_cond_match; try congruence.
    apply Mem.bounds_of_block_valid in H3. unfold Mem.valid_block in H3. congruence. omega.
    xomega. xomega.
    constructor. lia.
    constructor. red; auto.
    constructor. 
Qed.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> Csharpminor.final_state S r -> Cminor.final_state R r.
Proof.
  intros. inv H0. inv H. inv MK.  constructor.   
  generalize (Mem.norm_inject_val' _ _ wf_inj_expr_inj_se _ _ _ _ _ 
                                   (match_callstack_all_blocks_injected _ _ _ _ _ _ MCS)
                                   MINJ RESINJ).
  setoid_rewrite H1. intro A; inv A. eauto.
Qed.

Theorem transl_program_correct:
  forall sg, 
    forward_simulation
      (Csharpminor.semantics prog needed_stackspace sg )
      (Cminor.semantics tprog needed_stackspace sg ).
Proof.
  intros.
  eapply forward_simulation_star; eauto.
  eexact symbols_preserved.
  apply transl_initial_states.
  eexact transl_final_states.
  eexact transl_step_correct; eauto.
Qed.

End TRANSLATION.


