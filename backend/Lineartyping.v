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

(** Type-checking Linear code. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Memory.
Require Import Events.
Require Import Op.
Require Import Machregs.
Require Import Locations.
Require Import Conventions.
Require Import LTL.
Require Import Linear.

Require Import Values_symbolic.
Require Import Values_symbolictype.

(** The rules are presented as boolean-valued functions so that we
  get an executable type-checker for free. *)



Lemma eval_addressing_wt:
  forall F V (ge: Genv.t F V) sp a args v
         (EOP : eval_addressing ge sp a args = Some v),
    weak_wt v Tint.
Proof.
  red; intros.
  des a; myinv; simpl in *; intuition;
  unfold Genv.symbol_address' in *; try( revert EOP; destr; inv EOP);
  try solve [des (wt_expr_dec e Tint); try des (wt_expr_dec e0 Tint); right; intro; dex; intuition]. simpl; auto.
  des (wt_expr_dec sp Tint). right; intro; dex; intuition.
Qed.

Lemma eval_condition_wt:
  forall c l v
         (EOP : eval_condition c l = Some v),
    weak_wt v Tint.
Proof.
  red; intros; dex.
  generalize isTint.
  des c; myinv; simpl in *; intuition;
  repeat (match goal with
    | |- context [wt_expr ?e ?t] =>
      match goal with
          H1: wt_expr e t |- _ => fail 1
        | H1: wt_expr e t -> False |- _ => fail 1
        | _ => idtac
      end; des (wt_expr_dec e t)
    | |- _ => right; intro; dex; intuition
  end).
Qed.

Lemma eval_operation_wt:
  forall F V (ge : Genv.t F V) sp op args v 
         (EOP : eval_operation ge sp op args = Some v)
         (diff: op <> Omove),
    weak_wt v (Normalise.styp_of_typ (snd (type_of_operation op))).
Proof.
  intros.
  generalize isTint isTlong isTfloat isTsingle . intros. unfold weak_wt.
  pose (N:=op).
  des op;
  repeat match goal with
             H: match ?v with _ => _ end = Some _ |- _ => des v
           | H: Some _ = Some _ |- _ => inv H
           | H: None = Some _ |- _ => inv H
         end; simpl; auto;
  try match goal with
        | |- wt_expr ?e ?t /\ wt_expr ?e0 ?t0 /\ _ \/ (_ -> False) => des (wt_expr_dec e t); des (wt_expr_dec e0 t0)
        | |- (wt_expr ?e ?t /\ _) /\ (wt_expr ?e0 ?t0 /\ _) /\ _ \/ (_ -> False) => des (wt_expr_dec e t); des (wt_expr_dec e0 t0)
        | |- wt_expr ?e ?t /\ _ \/ (_ -> False) => des (wt_expr_dec e t)
  end;
  try solve [right; intro; dex; intuition].
  left; eapply symbol_address'_has_type; eauto.
  eapply eval_addressing_wt; eauto.
  eapply eval_condition_wt; eauto.
Qed.


Section WT_INSTR.

Variable funct: function.

Definition slot_valid (sl: slot) (ofs: Z) (ty: typ): bool :=
  match sl with
  | Local => zle 0 ofs
  | Outgoing => zle 0 ofs
  | Incoming => In_dec Loc.eq (S Incoming ofs ty) (loc_parameters funct.(fn_sig))
  end &&
  match ty with AST.Tlong => false | _ => true end.

Definition slot_writable (sl: slot) : bool :=
  match sl with
  | Local => true
  | Outgoing => true
  | Incoming => false
  end.

Definition loc_valid (l: loc) : bool :=
  match l with
  | R r => true
  | S Local ofs ty => slot_valid Local ofs ty
  | S _ _ _ => false
  end.

(* Definition subtype (t1 t2: typ) : bool := *)
(*   match t1, t2 with *)
(*     AST. *)
(*       (AST.Tint), (AST.Tint | AST.Tany32) *)
(*     | (AST.Tlong), (AST.Tlong | AST.Tany64) *)
(*     | AST.Tfloat, (AST.Tfloat | AST.Tany64) *)
(*     | AST.Tsingle, AST.Tsingle => true *)
(*     | _, _ => false *)
(*   end. *)

Fixpoint reg_has_typ_list (ml: list mreg) (tl: list typ) : bool :=
  match ml, tl with
      nil, nil => true
    | r::ml,t::tl => subtype (mreg_type r) t && reg_has_typ_list ml tl
    | _, _ => false
  end.

Fixpoint subtype_list (lt1 lt2: list typ) : bool :=
  match lt1, lt2 with
      nil, nil => true
    | t1::lt1, t2:: lt2 => subtype t1 t2 && subtype_list lt1 lt2
    | _, _ => false
  end.

Definition wt_instr (i: instruction) : bool :=
  match i with
  | Lgetstack sl ofs ty r =>
      subtype ty (mreg_type r) && slot_valid sl ofs ty
  | Lsetstack r sl ofs ty =>
    subtype ty (mreg_type r) &&
            slot_valid sl ofs ty && slot_writable sl
  | Lop op args res =>
      match is_move_operation op args with
      | Some arg =>
          subtype (mreg_type arg) (mreg_type res)
      | None => 
          let (targs, tres) := type_of_operation op in
          subtype tres (mreg_type res)
      end
  | Lload chunk addr args dst =>
      subtype (AST.type_of_chunk chunk) (mreg_type dst)
  | Ltailcall sg ros =>
      zeq (size_arguments sg) 0
  | Lbuiltin ef args res =>
      subtype_list (proj_sig_res' (ef_sig ef)) (map mreg_type res) 
                   (* && (reg_has_typ_list args (sig_args (ef_sig ef))) *)
  (* | Lannot ef args => *)
  (*     forallb loc_valid args *)
  | _ =>
      true
  end.

End WT_INSTR.

Definition wt_code (f: function) (c: code) : bool :=
  forallb (wt_instr f) c.

Definition wt_function (f: function) : bool :=
  wt_code f f.(fn_code).

(** Typing the run-time state. *)

Definition wt_locset (ls: locset) : Prop :=
  forall l, wt (ls l) (Loc.type l).

Lemma locmap_set_reg_rew:
  forall l v ls p,
    Locmap.set (R l) v ls p =
    if Loc.eq (R l) p then v else ls p.
Proof.
  intros.
  unfold Locmap.set.
  destruct (Loc.eq (R l) p); auto.
  destruct (Loc.diff_dec (R l) p). auto. exfalso; revert n n0; clear.
  unfold Loc.diff.
  destruct p eqn:?; simpl; intros.
  - apply n0. intro. subst.  congruence.
  - apply n0; auto.
Qed.

Lemma wt_setreg:
  forall ls r v,
    wt v (mreg_type r) -> wt_locset ls -> wt_locset (Locmap.set (R r) v ls).
Proof.
  intros; red; intros.
  rewrite locmap_set_reg_rew.
  destruct (Loc.eq (R r) l).
  - subst l; auto.
  - destruct (H0 l) as [[t [A B]]|A].
    left; eexists; split. eauto. auto.
    right; auto.
Qed.

Lemma wt_setstack:
  forall ls sl ofs ty v,
    (* wt v ty -> *)
    wt_locset ls -> wt_locset (Locmap.set (S sl ofs ty) v ls).
Proof.
  intros; red; intros.
  unfold Locmap.set. 
  destruct (Loc.eq (S sl ofs ty) l). 
  - subst l. simpl. 
    generalize (type_load_result (chunk_of_type ty) v).
    des ty.
  - destruct (Loc.diff_dec (S sl ofs ty) l).
    + apply H.
    + left; eexists; split. red; simpl. auto.
      apply subtype_refl.
Qed.

Lemma wt_undef_regs:
  forall rs ls, wt_locset ls -> wt_locset (undef_regs rs ls).
Proof.
  induction rs; simpl; intros; auto.
  apply wt_setreg.
  left; eexists; split; [red; simpl; auto|apply subtype_refl]. auto.
Qed.

Lemma wt_call_regs:
  forall ls, wt_locset ls -> wt_locset (call_regs ls).
Proof.
  intros; red; intros. unfold call_regs. destruct l. apply H. 
  destruct sl; try (left; eexists; split; [red; simpl; auto|apply subtype_refl]; fail).
  generalize (H (S Outgoing pos ty)). auto.
Qed.

Lemma wt_return_regs:
  forall caller callee,
  wt_locset caller -> wt_locset callee -> wt_locset (return_regs caller callee).
Proof.
  intros; red; intros.
  unfold return_regs. destruct l; auto.
  destruct (in_dec mreg_eq r destroyed_at_call); auto.
Qed.

Lemma wt_init:
  wt_locset (Locmap.init ).
Proof.
  red; intros. unfold Locmap.init.
  left; eexists; split; [red; simpl; auto|apply subtype_refl].
Qed.

Lemma wt_setlist:
  forall vl rl rs,
    list_forall2 wt vl (map mreg_type rl) ->
    wt_locset rs ->
    wt_locset (Locmap.setlist (map R rl) vl rs).
Proof.
  induction vl; destruct rl; simpl; intros; try contradiction; auto.
  inv H. apply IHvl; auto. apply wt_setreg; auto. 
Qed.

Lemma wt_find_label:
  forall f lbl c,
  wt_function f = true ->
  find_label lbl f.(fn_code) = Some c ->
  wt_code f c = true.
Proof.
  unfold wt_function; intros until c. generalize (fn_code f). induction c0; simpl; intros.
  discriminate.
  InvBooleans. destruct (is_label lbl a). 
  congruence.
  auto.
Qed.

(** Soundness of the type system *)

Definition wt_fundef (fd: fundef) :=
  match fd with
  | Internal f => wt_function f = true
  | External ef => True
  end.


Definition wt_sp (sp: expr_sym) : Prop :=
  Val.has_type sp Tint.


Inductive wt_callstack: list stackframe -> Prop :=
  | wt_callstack_nil:
      wt_callstack nil
  | wt_callstack_cons: forall f sp rs c s
        (WTSTK: wt_callstack s)
        (WTF: wt_function f = true)
        (WTC: wt_code f c = true)
        (WTRS: wt_locset rs)
        (WTSP: wt_sp sp),
      wt_callstack (Stackframe f sp rs c :: s).

Lemma wt_parent_locset:
  forall s, wt_callstack s -> wt_locset (parent_locset s).
Proof.
  induction 1; simpl; auto.
  apply wt_init.
Qed.

Inductive wt_state: state -> Prop :=
  | wt_regular_state: forall s f sp c rs m
        (WTSTK: wt_callstack s )
        (WTF: wt_function f = true)
        (WTC: wt_code f c = true)
        (WTRS: wt_locset rs)
        (WTSP: wt_sp sp),
      wt_state (State s f sp c rs m)
  | wt_call_state: forall s fd rs m
        (WTSTK: wt_callstack s)
        (WTFD: wt_fundef fd)
        (WTRS: wt_locset rs),
      wt_state (Callstate s fd rs m)
  | wt_return_state: forall s rs m
        (WTSTK: wt_callstack s)
        (WTRS: wt_locset rs),
      wt_state (Returnstate s rs m).

(** Preservation of state typing by transitions *)

Section SOUNDNESS.

Variable prog: program.
Let ge := Genv.globalenv prog.

Hypothesis wt_prog:
  forall i fd, In (i, Gfun fd) prog.(prog_defs) -> wt_fundef fd.

Lemma wt_find_function:
  forall m ros rs f, find_function ge m ros rs = Some f -> wt_fundef f.
Proof.
  intros. 
  assert (X: exists i, In (i, Gfun f) prog.(prog_defs)).
  {
    destruct ros as [r | s]; simpl in H.
    eapply Genv.find_funct_inversion; eauto. 
    destruct (Genv.find_symbol ge s) as [b|]; try discriminate.
    eapply Genv.find_funct_ptr_inversion; eauto.
  }
  destruct X as [i IN]. eapply wt_prog; eauto. 
Qed.


Lemma reg_type_list_args_type_list:
  forall rs args ty_args args'
         (WTRS : wt_locset rs)
         (RS: (reglist rs args) = args')
         (H4 : reg_has_typ_list args ty_args = true),
    list_forall2 wt args' ty_args.
Proof.
  induction args; simpl; intros; auto.
  - myinv. constructor. 
  - myinv. constructor; auto. 
    + generalize (WTRS (R a)). simpl.
      intros [[t0 [A B] ]| A]; [|right; auto].
      left; exists t0; split; auto.
      destruct (mreg_type a); destruct t; destruct t0; simpl in *; try congruence.
    + apply IHargs; auto.
      apply andb_true_iff in H4. intuition congruence.
Qed.

Lemma wt_trans:
  forall a t1 t2,
    subtype t1 t2 = true ->
    wt a t1 ->
    wt a t2.
Proof.
  red; intros.
  destruct H0 as [[t [A B]]|A]; auto.
  left; eexists t; destr.
  des t; des t1; des t2.
Qed.

Lemma subtype_list_has_type_list:
  forall (l l0 : list typ) (vl : list expr_sym),
    subtype_list l0 l = true ->
    list_forall2 wt vl ( l0) ->
    list_forall2 wt vl ( l).
Proof.
 induction l; simpl; intros; auto.
  + destruct l0; simpl in *; try congruence.
  + destruct l0; simpl in *; try congruence.
    apply andb_true_iff in H; intuition.
    inv H0.
    constructor. eapply wt_trans; eauto.
    eapply IHl; eauto.
Qed.

Lemma list_forall2_map:
  forall { X Y Y' } (P: X -> Y' -> Prop) (f: Y -> Y') l l'
    (LF2: list_forall2 P l (map f l')),
    list_forall2 (fun x y => P x (f y)) l l'.
Proof.
  induction l; intros; simpl; eauto.
  inv LF2. des l'. constructor.
  inv LF2. des l'. inv H1.
  constructor; auto.
Qed.
  
Theorem step_type_preservation:
  forall ns  S1 t S2, step ge ns  S1 t S2 -> wt_state S1 -> wt_state S2.
Proof.
  induction 1; intros WTS; inv WTS.
- (* getstack *)
  simpl in *; InvBooleans. 
  econstructor; eauto.
  eapply wt_setreg; eauto. generalize (WTRS (S sl ofs ty)). simpl. 
  intro; eapply wt_trans; eauto.
  apply wt_undef_regs; auto.
- (* setstack *)
  simpl in *; InvBooleans. 
  econstructor; eauto.
  apply wt_setstack; apply wt_undef_regs; auto.
  
- (* op *)
  simpl in *. destruct (is_move_operation op args) as [src | ] eqn:ISMOVE.
  + (* move *)
    InvBooleans. exploit is_move_operation_correct; eauto. intros [EQ1 EQ2]; subst. 
    simpl in *. inv H0.
    econstructor; eauto. apply wt_setreg. 
    generalize (WTRS (R src)). simpl. eapply wt_trans; eauto.
    apply wt_undef_regs; auto.
  + (* other ops *) 
    destruct (type_of_operation op) as [ty_args ty_res] eqn:TYOP. InvBooleans.
    econstructor; eauto.
    apply wt_setreg; auto.
    exploit eval_operation_wt; eauto. des op. myinv.
    rewrite TYOP. simpl.
    intros [A|A]; [|right; auto].
    left; exists ty_res; split; auto.
    apply wt_undef_regs; auto.
    
- (* load *)
  simpl in *; InvBooleans. 
  econstructor; eauto.
  apply wt_setreg. 
  unfold Mem.loadv in H1.
  destruct (Mem.mem_norm m a); simpl in H1; try congruence.
  destruct (Classical_Prop.classic (exists t, wt_expr v t)); [|red; auto].
  dex; exploit Mem.load_type; eauto. apply wt_trans; auto.
  apply wt_undef_regs; auto.
- (* store *)
  simpl in *; InvBooleans. 
  econstructor. eauto. eauto. eauto. 
  apply wt_undef_regs; auto.
  auto.
- (* call *)
  simpl in *; InvBooleans.
  econstructor; eauto. econstructor; eauto.
  eapply wt_find_function; eauto.
- (* tailcall *)
  simpl in *; InvBooleans.
  econstructor; eauto. 
  eapply wt_find_function; eauto.
  apply wt_return_regs; auto. apply wt_parent_locset; auto. 
- (* builtin *) 
  simpl in *; InvBooleans.
  econstructor; eauto.
  apply wt_setlist. 
  exploit external_call_well_typed'; eauto.
  apply subtype_list_has_type_list; auto.
  apply wt_undef_regs; auto.
(* - (* annot *) *)
(*   simpl in *; InvBooleans. *)
(*   econstructor; eauto.  *)
- (* label *)
  simpl in *. econstructor; eauto.
- (* goto *)
  simpl in *. econstructor; eauto. eapply wt_find_label; eauto. 
- (* cond branch, taken *)
  simpl in *. econstructor. auto. auto. eapply wt_find_label; eauto.
  apply wt_undef_regs; auto. auto.
- (* cond branch, not taken *)
  simpl in *. econstructor; auto. 
- (* jumptable *)
  simpl in *. econstructor; auto. eapply wt_find_label; eauto.
- (* return *)
  simpl in *. InvBooleans. 
  econstructor; eauto.
  apply wt_return_regs; auto. apply wt_parent_locset; auto.
- (* internal function *)
  simpl in WTFD.
  econstructor. eauto. eauto. eauto.
  apply wt_undef_regs. apply wt_call_regs. auto. 
  unfold wt_sp. simpl; auto.
- (* external function *)
  constructor; auto.  
  apply wt_setlist; auto.
  exploit external_call_well_typed'. eauto.
  apply subtype_list_has_type_list; auto.
  des (ef_sig ef); unfold proj_sig_res', loc_result; simpl.
  destr. destr.
- (* return *)
  inv WTSTK. econstructor; eauto.
Qed.

Theorem wt_initial_state:
  forall sg S, initial_state prog sg S -> wt_state S.
Proof.
  induction 1. econstructor. constructor. 
  unfold ge0 in H1. exploit Genv.find_funct_ptr_inversion; eauto.
  intros [id IN]. eapply wt_prog; eauto.
  apply wt_init.
Qed.

End SOUNDNESS.

(** Properties of well-typed states that are used in [Stackingproof]. *)

Lemma wt_state_getstack:
  forall s f sp sl ofs ty rd c rs m,
  wt_state (State s f sp (Lgetstack sl ofs ty rd :: c) rs m) ->
  slot_valid f sl ofs ty = true.
Proof.
  intros. inv H. simpl in WTC; InvBooleans. auto.
Qed.

Lemma wt_state_setstack:
  forall s f sp sl ofs ty r c rs m,
  wt_state (State s f sp (Lsetstack r sl ofs ty :: c) rs m) ->
  slot_valid f sl ofs ty = true /\ slot_writable sl = true.
Proof.
  intros. inv H. simpl in WTC; InvBooleans. intuition.
Qed.

Lemma wt_state_tailcall:
  forall s f sp sg ros c rs m,
  wt_state (State s f sp (Ltailcall sg ros :: c) rs m) ->
  size_arguments sg = 0.
Proof.
  intros. inv H. simpl in WTC; InvBooleans. auto.
Qed.

(* Lemma wt_state_annot: *)
(*   forall s f sp ef args c rs m, *)
(*   wt_state (State s f sp (Lannot ef args :: c) rs m) -> *)
(*   forallb (loc_valid f) args = true. *)
(* Proof. *)
(*   intros. inv H. simpl in WTC; InvBooleans. auto.  *)
(* Qed. *)

Lemma wt_callstate_wt_regs:
  forall s f rs m,
  wt_state (Callstate s f rs m) ->
  forall r, wt (rs (R r)) (mreg_type r).
Proof.
  intros. inv H. apply WTRS. 
Qed.
