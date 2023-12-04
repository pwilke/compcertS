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

Require Import Coqlib.
Require Import Zwf.
Require Import Maps.
Require Import Compopts.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import ExprEval Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Lattice.
Require Import Kildall.
Require Import Registers.
Require Import RTL.
Require Import Values_symbolic.
Require Import Values_symbolictype.
Require Import Setoid.
Require Import Classical.

Inductive block_class : Type :=
  | BCinvalid
  | BCglob (id: ident)
  | BCstack
  | BCother.

Definition block_class_eq: forall (x y: block_class), {x=y} + {x<>y}.
Proof. decide equality. apply peq. Defined.

Record block_classification : Type := BC {
  bc_img :> block -> block_class;
  bc_stack: forall b1 b2, bc_img b1 = BCstack -> bc_img b2 = BCstack -> b1 = b2;
  bc_glob: forall b1 b2 id, bc_img b1 = BCglob id -> bc_img b2 = BCglob id -> b1 = b2
}.

Definition bc_below (bc: block_classification) (bound: block) : Prop :=
  forall b, bc b <> BCinvalid -> Plt b bound.

Lemma bc_below_invalid:
  forall b bc bound, ~Plt b bound -> bc_below bc bound -> bc b = BCinvalid.
Proof.
  intros. destruct (block_class_eq (bc b) BCinvalid); auto. 
  elim H. apply H0; auto.
Qed.

Hint Extern 2 (_ = _) => congruence: va.
Hint Extern 2 (_ <> _) => congruence : va.
Hint Extern 2 (_ < _) => xomega : va.
Hint Extern 2 (_ <= _) => xomega : va.
Hint Extern 2 (_ > _) => xomega : va.
Hint Extern 2 (_ >= _) => xomega : va.

Hint Extern 2 (_ = _) => congruence : va.
Hint Extern 2 (_ <> _) => congruence : va.
Hint Extern 2 (_ < _) => xomega : va.
Hint Extern 2 (_ <= _) => xomega : va.
Hint Extern 2 (_ > _) => xomega : va.
Hint Extern 2 (_ >= _) => xomega : va.


Definition val_no_ptr (v : val) : bool :=
  match v with
    | Vptr _ _ => false
    |  _    => true
  end.

Inductive is_unop_trans : (expr_sym -> expr_sym) ->  Prop :=
| is_unop_id     : is_unop_trans (fun x => x)
| is_unop_const  : forall v, val_no_ptr v = true -> is_unop_trans (fun x => Eval v)
| is_unop_eundef : forall b i, is_unop_trans (fun x => Eundef b i)
| is_unop_eunop  : forall o s f
                           (Hunop : is_unop_trans f),
                      is_unop_trans (fun x => Eunop o s (f x))
| is_unop_ebinop : forall o s1 s2 f1 f2
                           (Hbinop1 : is_unop_trans f1)
                           (Hbinop2 : is_unop_trans f2),
                           is_unop_trans (fun x => Ebinop o s1 s2 (f1 x) (f2 x)).

Inductive is_binop_trans : (expr_sym -> expr_sym -> expr_sym) ->  Prop :=
| is_binop_proj_1     : is_binop_trans (fun x y => x)
| is_binop_proj_2     : is_binop_trans (fun x y => y)
| is_binop_const  : forall v, val_no_ptr v = true -> is_binop_trans (fun x y => Eval v)
| is_binop_eundef : forall b i, is_binop_trans (fun x y => Eundef b i)
| is_binop_eunop  : forall o s f
                           (Hunop : is_binop_trans f),
                      is_binop_trans (fun x y => Eunop o s (f x y))
| is_binop_ebinop : forall o s1 s2 f1 f2
                           (Hbinop1 : is_binop_trans f1)
                           (Hbinop2 : is_binop_trans f2),
                           is_binop_trans (fun x y => Ebinop o s1 s2 (f1 x y) (f2 x y)).

Section MATCH.
Import NormaliseSpec.

Variable bc: block_classification.

Record same_except (b : block) (cm cm' : block -> int) : Prop :=
  {
    SAME : forall b', b <> b' -> cm b' = cm' b';
    DIFF : cm b <> cm' b
  }.

Definition no_forgery (mx :Z) (bound : block -> Z * Z) (align : block -> int) : Prop :=
  forall b, exists cm1,  compat mx bound align cm1 /\
               exists cm2, compat mx bound align cm2 /\ same_except b cm1 cm2.


(** Concretisation of a constant *)
Import ExprEval.


Instance EquivExpr : Equivalence same_eval.
Proof.
  unfold same_eval.
  constructor; simpl.
  -
    unfold Reflexive.
    reflexivity.
  - 
    unfold Symmetric.
    intuition.
  - 
    unfold Transitive.
    intuition.
Qed.

Definition is_pointer (b : block) (ofs : int) (e : expr_sym) : Prop :=
  same_eval (Eval (Vptr b ofs)) e.

Definition is_constant (v : val) (e : expr_sym) : Prop :=
  same_eval (Eval v) e.



Add Parametric Morphism : is_pointer  with signature ((@eq block) ==> @eq int ==> same_eval ==> iff) as is_pointer_same_eval_morph.
Proof.
  unfold is_pointer.
  intros.
  unfold same_eval ; split ; intros.
  rewrite <- H ; eauto.
  rewrite H ; eauto.
Qed.


Add Parametric Morphism : is_constant  with signature ((@eq val) ==> same_eval ==> iff) as is_constant_same_eval_morph.
Proof.
  unfold is_constant.
  intros.
  unfold same_eval ; intuition.
Qed.

Add Parametric Morphism (o : binop_t) (t t' : styp) : (Ebinop o t t') with signature  same_eval ==> same_eval ==> same_eval as binop_same_eval.
Proof.
  intros.
  unfold same_eval in *.
  intros.
  simpl.
  erewrite H0; eauto.
  erewrite H ; eauto.
Qed.

Add Parametric Morphism (o : unop_t) (t : styp) : (Eunop o t) with signature  same_eval ==> same_eval as unop_same_eval.
Proof.
  unfold same_eval.
  intros.
  simpl.
  erewrite H; eauto.
Qed.

(** * Abstracting the result of conditions (type [option bool]) *)

Inductive abool :=
  | Bnone               (**r always [None] (undefined) *)
  | Just (b: bool)      (**r always [Some b] (defined and known to be [b]) *)
  | Maybe (b: bool)     (**r either [None] or [Some b] (known to be [b] if defined) *)
  | Btop.               (**r unknown, all results are possible *)


Inductive cmatch: option bool -> abool -> Prop :=
  | cmatch_none: cmatch None Bnone
  | cmatch_just: forall b, cmatch (Some b) (Just b)
  | cmatch_maybe_none: forall b, cmatch None (Maybe b)
  | cmatch_maybe_some: forall b, cmatch (Some b) (Maybe b)
  | cmatch_top: forall ob, cmatch ob Btop.


Definition is_wk_constant (v : val) (e : expr_sym) : Prop :=
  forall a u,
    Values.Val.lessdef (eSexpr a u e) (eSval a  v).


Definition is_bool (e : expr_sym) : Prop := 
  forall a u,
  exists i, Values.Val.lessdef (eSexpr a u e) (Vint i) /\
            (i = Int.zero \/ i = Int.one).


Definition val_of_bool (b:bool) :=
  if b then Vtrue else Vfalse.

Inductive ecmatch: expr_sym -> abool -> Prop :=
| ecmatch_none  : forall e,   is_constant Vundef e ->  ecmatch e Bnone
| ecmatch_just  : forall e b, is_constant (val_of_bool b) e -> ecmatch e (Just b)
| ecmatch_maybe : forall e b, is_wk_constant (val_of_bool b) e -> ecmatch e (Maybe b)
| ecmatch_top   : forall e, is_bool e -> ecmatch e Btop.

Ltac rew_cst H :=
  unfold is_constant, is_pointer in H ;
  erewrite <- H in *; eauto.

Lemma is_constant_refl : forall v, is_constant v (Eval v).
Proof.
  repeat intro.
  reflexivity.
Qed.  

Add Parametric Morphism : is_wk_constant  with signature ((@eq val) ==> same_eval ==> iff) as is_wk_constant_same_eval_morph.
Proof.
  assert (   forall (y : val) (x y0 : expr_sym),
               same_eval x y0 -> (is_wk_constant y x -> is_wk_constant y y0)).
  {
    intros.
    unfold  is_wk_constant in *.
    intros.
    rewrite <- H.
    eauto.
    }
  intros.
  split;
  apply H; auto.
  rewrite H0 ; reflexivity.
Qed.  


Add Parametric Morphism : is_bool with signature (same_eval ==> iff) as  is_bool_same_eval_morph.
Proof.
  assert (forall x y : expr_sym, same_eval x y -> (is_bool x -> is_bool y)).
  {
    intros.
    unfold is_bool in *.
    intros.
    destruct (H0 a u).
    exists x0 ; split ; auto.
    erewrite <- H; eauto. tauto.
    intuition.
  }
  intuition ; eapply H ; eauto.
  rewrite H0 ; auto.
  reflexivity.
Qed.  
  
  
Add Parametric Morphism : ecmatch with signature (same_eval ==> @eq abool ==> iff) as cmatch_morph.
Proof.
  assert (
      forall x y, 
        same_eval x y -> forall z : abool, ecmatch x z -> ecmatch y z).
  {
    intros.
    inv H0 ; try constructor; 
    try (rewrite H in H1; auto; fail).
  }
  intros ; split ; apply H; auto.
  rewrite H0 ; reflexivity.
Qed.

Hint Constructors cmatch : va.

Definition club (x y: abool) : abool :=
  match x, y with
  | Bnone, Bnone => Bnone
  | Bnone, (Just b | Maybe b) => Maybe b
  | (Just b | Maybe b), Bnone => Maybe b
  | Just b1, Just b2 => if eqb b1 b2 then x else Btop
  | Maybe b1, Maybe b2 => if eqb b1 b2 then x else Btop
  | Maybe b1, Just b2 => if eqb b1 b2 then x else Btop
  | Just b1, Maybe b2 => if eqb b1 b2 then y else Btop
  | _, _ => Btop
  end.

Definition cge (b1 : abool) (b2 : abool) : Prop :=
  match b1, b2 with
    | Btop , _ => True
    | _ , Btop => False
    | Maybe x , (Maybe y | Just y) => x = y
    | Maybe _  , Bnone    => True
    |   _     ,     _      => b1 = b2
  end.


Ltac case_match :=
  match goal with
    | |- context[match ?X with
                   | _ => _
                 end] => case_eq X
  end.

Lemma is_bool_undef :
   is_bool (Eval Vundef).
Proof.
  repeat intro.
  exists Int.zero ; intuition constructor.
Qed.

Lemma is_bool_true :
   is_bool (Eval Vtrue).
Proof.
  repeat intro.
  exists Int.one ; intuition constructor.
Qed.

Lemma is_bool_false :
   is_bool (Eval Vfalse).
Proof.
  repeat intro.
  exists Int.zero ; intuition constructor.
Qed.

Lemma is_bool_val_of_bool :
  forall b, 
    is_bool (Eval (val_of_bool b)).
Proof.
  repeat intro.
  destruct b ; simpl.
  exists Int.one ; intuition constructor.
  exists Int.zero ; intuition constructor.
Qed.  

Lemma is_wk_constant_is_bool :
  forall b e,
    is_wk_constant (val_of_bool b) e -> 
   is_bool e.
Proof.
  repeat intro.
  specialize (H a u).
  inv H.
  rewrite H2.
  destruct b ; [exists Int.one |  exists Int.zero] ; intuition constructor.
  exists Int.zero ; intuition constructor.
Qed.


Hint Resolve is_bool_undef is_bool_true is_bool_false is_bool_val_of_bool is_wk_constant_is_bool : va.



Lemma ecmatch_cge :
  forall e x y,
    ecmatch e x -> cge y x -> ecmatch e y.
Proof.
  intros.
  destruct x ; destruct y ; simpl in H0 ; inv H ;
  try congruence ; try constructor ; unfold is_wk_constant ; intros ; eauto ; try tauto.
  -
    rew_cst H1 ; auto.
  - 
    rew_cst H1.
    auto with va.
  - 
    inv H0 ; auto.
  - 
    rew_cst H3; auto.
  - 
    rew_cst H3.
    auto with va.
  - 
    eauto with va.
Qed.

Lemma club_ge_l : forall x y,
                  cge (club x y) x.
Proof.
  intros.
  case_eq x ; case_eq y ; simpl ; try tauto; intros; case_match ; simpl ; auto.
  intros.
  symmetry.
  apply eqb_prop ; auto.
Qed.  


Lemma ecmatch_lub_l:
  forall ob x y, ecmatch ob x -> ecmatch ob (club x y).
Proof.
  intros.
  eapply ecmatch_cge ; eauto.
  apply club_ge_l.
Qed.

Lemma club_sym : forall x y, club x y = club y x.
Proof.
  intros.
  destruct x ; destruct y ; try reflexivity; simpl;  rewrite Fcore_Raux.eqb_sym; case_match ; try reflexivity.
  - intros.
    apply eqb_prop in H ; congruence.
  - 
    intros.
    apply eqb_prop in H ; congruence.
Qed.  


Lemma ecmatch_lub_r:
  forall ob x y, ecmatch ob y -> ecmatch ob (club x y).
Proof.
  intros.
  eapply ecmatch_cge ; eauto.
  rewrite club_sym.
  apply club_ge_l.
Qed.

Definition cnot (x: abool) : abool :=
  match x with
  | Just b => Just (negb b)
  | Maybe b => Maybe (negb b)
  | _ => x
  end.


Lemma cnot_sound:
  forall ob x, cmatch ob x -> cmatch (option_map negb ob) (cnot x).
Proof.
  destruct 1; constructor.
Qed.

Lemma ecnot_sound:
  forall ob x, ecmatch ob x -> ecmatch (Val.notbool ob) (cnot x).
Proof.
  intros.
  inv H ; simpl ; try constructor.
  -
    unfold Val.notbool.
    rew_cst H0.
    repeat intro; reflexivity.
  - 
    unfold Val.notbool.
    rew_cst H0.
    destruct b ; constructor.
  -
    unfold Val.notbool.
    unfold is_wk_constant in * ; intros.
    specialize (H0 a u).
    simpl.
    inv H0.
    rewrite H2.
    destruct b ; simpl ; constructor.
    simpl ; constructor.
  - 
    unfold Val.notbool.
    repeat intro ; simpl.
    destruct (H0 a u).
    exists (Int.notbool x).
    destruct H.
    inv H.
    rewrite H4.
    intuition subst ; simpl ; constructor.
    intuition subst ; simpl ; constructor.
Qed.    

(** * Abstracting pointers *)

Inductive aptr : Type :=
  | Pbot                        (**r bottom (empty set of expressions) *)
  | Pcst                        (**r independant from memory *)
  | Gl (id: ident) (ofs: int)   (**r pointer into the block for global variable [id] at offset [ofs] *)
  | Glo (id: ident)             (**r pointer anywhere into the block for global [id] *)
  | Glob                        (**r pointer into any global variable *)
  | Stk (ofs: int)              (**r pointer into the current stack frame at offset [ofs] *)
  | Stack                       (**r pointer anywhere into the current stack frame *)
  | Nonstack                    (**r pointer anywhere but into the current stack frame *)
  | Ptop.                       (**r any valid pointer *)

Definition eq_aptr: forall (p1 p2: aptr), {p1=p2} + {p1<>p2}.
Proof.
  intros. generalize ident_eq, Int.eq_dec; intros. decide equality. 
Defined.

Inductive pmatch (b: block) (ofs: int): aptr -> Prop :=
| pmatch_gl: forall id,
               bc b = BCglob id ->
               pmatch b ofs (Gl id ofs)
| pmatch_glo: forall id,
                bc b = BCglob id ->
                pmatch b ofs (Glo id)
| pmatch_glob: forall id,
                 bc b = BCglob id ->
                 pmatch b ofs Glob
| pmatch_stk:
    bc b = BCstack ->
    pmatch b ofs (Stk ofs)
| pmatch_stack:
    bc b = BCstack ->
    pmatch b ofs Stack
| pmatch_nonstack:
    bc b <> BCstack -> bc b <> BCinvalid ->
    pmatch b ofs Nonstack
| pmatch_top:
    bc b <> BCinvalid ->
    pmatch b ofs Ptop.

Definition singleton (b:block) : block -> Prop :=
  fun b' => b = b'.

Definition depends_on_block (b : block) (e : expr_sym) :=
  depends_on_blocks (singleton b) e.

Definition depends_on_nothing (e : expr_sym) :=
  depends_on_blocks (fun  _ => False)  e.

Inductive epmatch : expr_sym ->  aptr -> Prop :=
| epmatch_cst : forall e, depends_on_nothing e -> epmatch e Pcst
| epmatch_gl: forall id b ofs e,
                bc b = BCglob id ->
                is_pointer b ofs e -> 
                epmatch e (Gl id ofs)
| epmatch_glo: forall id e,
                 depends_on_blocks (fun b => bc b = BCglob id) e -> 
                 epmatch e (Glo id)
| epmatch_glob: forall  e,
                  depends_on_blocks (fun b => exists id, bc b = BCglob id) e -> 
                  epmatch e Glob
| epmatch_stk: forall b ofs e,
                 bc b = BCstack ->
                 is_pointer b ofs e -> 
                 epmatch e (Stk ofs)
| epmatch_stack: forall e,
                   depends_on_blocks (fun b  => bc b = BCstack) e -> 
                   epmatch e Stack
| epmatch_nonstack: forall e,
                      depends_on_blocks
                        (fun b =>
                           bc b <> BCstack /\ bc b <> BCinvalid) e -> 
                      epmatch e Nonstack
| epmatch_top: forall e,
                 depends_on_blocks (fun b => bc b <> BCinvalid) e -> 
                 epmatch e Ptop.

Hint Constructors pmatch: va.
Hint Constructors epmatch: va.

Inductive pge: aptr -> aptr -> Prop :=
  | pge_top: forall p, pge Ptop p
  | pge_bot: forall p, pge p Pbot
  | pge_refl: forall p, pge p p
  | pge_glo_gl: forall id ofs, pge (Glo id) (Gl id ofs)
  | pge_glob_gl: forall id ofs, pge Glob (Gl id ofs)
  | pge_glob_glo: forall id, pge Glob (Glo id)
  | pge_ns_gl: forall id ofs, pge Nonstack (Gl id ofs)
  | pge_ns_glo: forall id, pge Nonstack (Glo id)
  | pge_ns_glob: pge Nonstack Glob
  | pge_stack_stk: forall ofs, pge Stack (Stk ofs).

Hint Constructors pge: va.

Lemma pge_trans:
  forall p q, pge p q -> forall r, pge q r -> pge p r.
Proof.
  induction 1; intros r PM; inv PM; auto with va.
Qed.

Lemma pmatch_ge:
  forall b ofs p q, pge p q -> pmatch b ofs q -> pmatch b ofs p.
Proof.
  induction 1; intros PM; inv PM; eauto with va.
Qed.


Lemma eSexpr_same :
  forall A A' E e,
  (forall b, block_appears e b -> A b = A' b) -> 
  eSexpr A E e = eSexpr A' E e.
Proof.
  induction e ; simpl; auto.
  - destruct v ; try tauto.
    simpl.
    intros.
    rewrite H ; auto.
  - 
    intros.
    rewrite IHe ; auto.
  - 
    intros.
    rewrite IHe1 ; auto.
    rewrite IHe2 ; auto.
Qed.
    
(*
Lemma is_constant_block_appears :
  forall b ofs e, is_constant (Vptr b ofs) e -> block_appears e b.
Proof.
  intros b ofs e.
  revert b ofs.
  unfold is_constant, same_eval.
  intros.
  destruct (block_appears_dec b e).
  auto.
  exfalso.
  set (A1 := fun (b':block) => Int.zero).
  set (A2 := fun (b':block) => if eq_block b b' then Int.one else Int.zero).
  set (EM := fun (b:block) (i:int)  => Byte.zero).
  generalize (H A1 EM).
  generalize (H A2 EM).
  rewrite eSexpr_same with (A':= A1) (e:=e).
  intros.
  rewrite <- H1 in H0.
  simpl in H0.
  unfold A1 , A2 in H0.
  destruct (eq_block b b) ; auto.
  rewrite Int.add_zero_l in *.
  inversion H0.
  generalize (add_one_zero_diff ofs ofs).    
  rewrite Int.add_zero_l.
  intuition.
  intros.
  unfold A1 , A2.
  destruct (eq_block b b0) ; auto.
  congruence.
Qed.
 *)

Definition deps_of_val (v : val)  : block -> Prop :=
  match v with
    | Vptr b ofs => singleton b
    |    _       => (fun _ => False)
  end.
                              
Add Parametric Morphism (S : block -> Prop) : (depends_on_blocks S) with
    signature same_eval ==> iff as depends_on_blocks_same_eval.
Proof.
  unfold depends_on_blocks.
  unfold same_eval ; intuition.
  repeat erewrite <- H ; eauto.
  repeat erewrite H ; eauto.
Qed.


Lemma is_constant_depends :
  forall v e, is_constant v e -> depends_on_blocks (deps_of_val v) e.
Proof.
  intros.
  unfold is_constant in H.
  rewrite <- H.
  repeat intro.
  destruct v ; simpl ; try reflexivity.
  rewrite H0; auto.
  simpl. unfold singleton; auto.
Qed.

Lemma is_pointer_depends :
  forall b o e, is_pointer b o e -> depends_on_blocks (singleton b) e.
Proof.
  intros.
  unfold is_pointer in H.
  rewrite <- H.
  repeat intro.
  simpl.
  rewrite H0. reflexivity.
  unfold singleton; auto.
Qed.

Lemma depends_on_blocks_le :
  forall (S S': block -> Prop) e,
    (forall b, S b -> S' b) -> 
  depends_on_blocks S e -> depends_on_blocks S' e.
Proof.
  unfold depends_on_blocks.
  intros.
  eapply H0 ; eauto.
Qed.

Lemma depends_on_blocks_appears :
  forall (S: block -> Prop) e,
  (forall b, (block_appears e b -> S b)) -> 
  depends_on_blocks S e.
Proof.
  unfold depends_on_blocks.
  intros.
  induction e ; simpl ; try reflexivity.
  -
    destruct v ; simpl in * ; try reflexivity.
    rewrite H0 ; auto.
  - 
    rewrite IHe ; auto.
  -
    simpl in H.
    rewrite IHe1; auto.
    rewrite IHe2 ; auto.
Qed.
    
Add Parametric Morphism : epmatch with signature  same_eval ==> @eq aptr ==> iff as epmatch_same_eval.
Proof.
  assert (forall x y, same_eval x y -> forall ptr, epmatch x ptr -> epmatch y ptr).
  {
    intros.
    inv H0; rewrite H in * ; econstructor ; eauto.
  }
  intros.
  intuition.
  eapply H ; eauto.
  eapply H ; eauto.
  rewrite H0 ; auto.
  reflexivity.
Qed.



Lemma depends_binop : 
  forall (S: block -> Prop) o t t' e1 e2,
    depends_on_blocks S e1 ->
    depends_on_blocks S e2 -> 
    depends_on_blocks S (Ebinop o t t' e1 e2).
Proof.
  unfold depends_on_blocks ; simpl.
  intros.
  erewrite H with (a':=a');eauto.
  erewrite H0 with (a':=a'); eauto.
Qed.

Lemma depends_unop : 
  forall (S: block -> Prop) o t e1,
    depends_on_blocks S e1 ->
    depends_on_blocks S (Eunop o t  e1).
Proof.
  unfold depends_on_blocks ; simpl.
  intros.
  erewrite H with (a':=a'); eauto.
Qed.



Ltac is_constant_depends :=
  match goal with
    | H : is_constant ?V ?E |- depends_on_blocks ?S ?E =>
      apply is_constant_depends in H 
  end.

Ltac is_pointer_depends := 
  match goal with
    | H : is_pointer ?B ?O ?E |- depends_on_blocks ?S ?E =>
      apply is_pointer_depends in H 
  end.


Ltac depends_on_blocks_le :=
  match goal with
    | H : depends_on_blocks ?S1 ?E |- depends_on_blocks ?S' ?E =>
      apply depends_on_blocks_le with (S:= S1)
  end.



Lemma depends_on_blocks_const :
  forall v S,
    val_no_ptr v = true -> 
    depends_on_blocks S (Eval v).
Proof.
  intros.
  apply depends_on_blocks_appears.
  destruct v ; simpl in * ; intuition congruence.
Qed.



Ltac depends_on_blocks_const :=
  match goal with
    | |- depends_on_blocks _ (Eval ?V) =>
      let v := (eval compute in  (val_no_ptr V)) in
      match v with
        | true => apply depends_on_blocks_const ; reflexivity
        | false => fail
      end
  end.


Ltac depends_prf := 
  unfold depends_on_nothing, depends_on_block in *;
  try (apply depends_binop; eauto); 
  try (apply depends_unop ; eauto);
  (try is_constant_depends) ; 
  (try is_pointer_depends) ; 
  try (depends_on_blocks_const);
  try depends_on_blocks_le ; simpl; intros ;
  unfold singleton in *  ; try tauto.

Hint Extern 2 (depends_on_blocks _ _) => depends_prf : va.

Lemma epmatch_top_def :
  forall v p, 
    epmatch v p -> 
    epmatch v Ptop.
Proof.
  intros; constructor.
  inv H; depends_prf; try congruence.
  destruct H ; congruence.
Qed.

Lemma epmatch_bot_def :
  forall v p,
    epmatch v Pbot ->
    epmatch v p.
Proof.
  intros.
  inv H.
Qed.

Definition epge (p q : aptr) : Prop :=
  match p, q with
    | Ptop , _ => True
    | Nonstack , (Nonstack| Glob | Glo _ | Gl _ _ | Pcst | Pbot) => True
    | Glob     , (Glob | Glo _ | Gl _ _ | Pcst | Pbot) => True
    | Glo  id   , (Glo id' | Gl id' _) => id  = id'
    | Glo  _   , Pcst                 => True
    | Gl id o   , Gl id' o'          => id = id' /\ o = o'
    | Stack    , (Stack | Stk _ | Pcst )   => True
    | Stk o , Stk o'    => o = o'
    | Pbot , Pbot       => True
    | _    , Pbot       => True
    |  Pbot , _         => False
    | Pcst  , Pcst      => True
    | _  ,   _       => False
  end.
      
Lemma  epge_trans :
  forall p q r,
    epge p q -> epge q r -> epge p r.
Proof.
  intros.
  destruct p ; destruct q ; destruct r ; try (simpl in * ; intuition congruence).
Qed.  
  
Lemma epmatch_ge:
  forall e p q, epge p q -> epmatch e q -> epmatch e p.
Proof.
  intros.
  destruct p, q ; simpl in H ; inv H0 ; try tauto; eauto with va.
  -
    intuition subst.
    econstructor; eauto.
  - 
    econstructor ; depends_prf.
    exists id ; congruence.
  - 
    econstructor ; depends_prf.
    destruct H0 ; intuition.
  - 
    constructor ; depends_prf.
    destruct H0 ; intuition.
Qed.    

Lemma epmatch_top': forall e p, epmatch e p -> epmatch e Ptop.
Proof.
  intros. apply epmatch_ge with p; auto with va. 
  simpl ; exact I.
Qed.

Definition plub (p q: aptr) : aptr :=
  match p, q with
  | Pbot, _ => q
  | _, Pbot => p
  | Gl id1 ofs1, Gl id2 ofs2 =>
      if ident_eq id1 id2 then if Int.eq_dec ofs1 ofs2 then p else Glo id1 else Glob
  | Gl id1 ofs1, Glo id2 =>
      if ident_eq id1 id2 then q else Glob
  | Glo id1, Gl id2 ofs2 =>
      if ident_eq id1 id2 then p else Glob
  | Glo id1, Glo id2 =>
      if ident_eq id1 id2 then p else Glob
  | (Gl _ _ | Glo _ | Glob), Glob => Glob
  | Glob, (Gl _ _ | Glo _) => Glob
  | (Gl _ _ | Glo _ | Glob | Nonstack), Nonstack =>
      Nonstack
  | Nonstack, (Gl _ _ | Glo _ | Glob) =>
      Nonstack
  | Stk ofs1, Stk ofs2 =>
      if Int.eq_dec ofs1 ofs2 then p else Stack
  | (Stk _ | Stack), Stack => 
      Stack
  | Stack, Stk _ =>
      Stack
  | _, _ => Ptop
  end.

(*
Lemma plub_comm:
  forall p q, plub p q = plub q p.
Proof.
  intros; unfold plub; destruct p; destruct q; auto.
  destruct (ident_eq id id0). subst id0. 
  rewrite dec_eq_true. 
  destruct (Int.eq_dec ofs ofs0). subst ofs0. rewrite dec_eq_true. auto.
  rewrite dec_eq_false by auto. auto. 
  rewrite dec_eq_false by auto. auto. 
  destruct (ident_eq id id0). subst id0. 
  rewrite dec_eq_true; auto.
  rewrite dec_eq_false; auto.
  destruct (ident_eq id id0). subst id0. 
  rewrite dec_eq_true; auto.
  rewrite dec_eq_false; auto.
  destruct (ident_eq id id0). subst id0. 
  rewrite dec_eq_true; auto.
  rewrite dec_eq_false; auto.
  destruct (Int.eq_dec ofs ofs0). subst ofs0. rewrite dec_eq_true; auto.
  rewrite dec_eq_false; auto. 
Qed.

Lemma pge_lub_l:
  forall p q, pge (plub p q) p.
Proof.
  unfold plub; destruct p, q; auto with va.
- destruct (ident_eq id id0).
  destruct (Int.eq_dec ofs ofs0); subst; constructor.
  constructor.
- destruct (ident_eq id id0); subst; constructor.
- destruct (ident_eq id id0); subst; constructor.
- destruct (ident_eq id id0); subst; constructor.
- destruct (Int.eq_dec ofs ofs0); subst; constructor.
Qed.

Lemma pge_lub_r:
  forall p q, pge (plub p q) q.
Proof.
  intros. rewrite plub_comm. apply pge_lub_l.
Qed.

Lemma pmatch_lub_l:
  forall b ofs p q, pmatch b ofs p -> pmatch b ofs (plub p q).
Proof.
  intros. eapply pmatch_ge; eauto. apply pge_lub_l.
Qed.
*)

Definition eplub (p q: aptr) : aptr :=
  match p, q with
  | Pbot, _ => q
  | _, Pbot => p
  | Pcst , Pcst => Pcst
  | Pcst , Gl id _ | Gl id _, Pcst => Glo id
  | Pcst , Glo id  | Glo id , Pcst      => Glo id
  | Pcst , Glob    | Glob , Pcst        => Glob
  | Pcst , Stk  _  | Stk _ , Pcst        => Stack
  | Pcst , Stack   | Stack , Pcst       => Stack
  | Gl id1 ofs1, Gl id2 ofs2 =>
      if ident_eq id1 id2 then if Int.eq_dec ofs1 ofs2 then p else Glo id1 else Glob
  | Gl id1 ofs1, Glo id2 =>
      if ident_eq id1 id2 then q else Glob
  | Glo id1, Gl id2 ofs2 =>
      if ident_eq id1 id2 then p else Glob
  | Glo id1, Glo id2 =>
      if ident_eq id1 id2 then p else Glob
  | (Gl _ _ | Glo _ | Glob), Glob => Glob
  | Glob, (Gl _ _ | Glo _) => Glob
  | (Gl _ _ | Glo _ | Glob | Nonstack | Pcst), Nonstack =>
      Nonstack
  | Nonstack, (Gl _ _ | Glo _ | Glob | Pcst) =>
      Nonstack
  | Stk ofs1, Stk ofs2 =>
      if Int.eq_dec ofs1 ofs2 then p else Stack
  | (Stk _ | Stack), Stack => 
      Stack
  | Stack, Stk _ =>
      Stack
  |  _   ,  _ => Ptop
  end.

Lemma eplub_comm:
  forall p q, eplub p q = eplub q p.
Proof.
  intros; unfold eplub; destruct p; destruct q; auto.
  destruct (ident_eq id id0). subst id0. 
  rewrite dec_eq_true. 
  destruct (Int.eq_dec ofs ofs0). subst ofs0. rewrite dec_eq_true. auto.
  rewrite dec_eq_false by auto. auto. 
  rewrite dec_eq_false by auto. auto. 
  destruct (ident_eq id id0). subst id0. 
  rewrite dec_eq_true; auto.
  rewrite dec_eq_false; auto.
  destruct (ident_eq id id0). subst id0. 
  rewrite dec_eq_true; auto.
  rewrite dec_eq_false; auto.
  destruct (ident_eq id id0). subst id0. 
  rewrite dec_eq_true; auto.
  rewrite dec_eq_false; auto.
  destruct (Int.eq_dec ofs ofs0). subst ofs0. rewrite dec_eq_true; auto.
  rewrite dec_eq_false; auto. 
Qed.



Lemma epge_lub_l:
  forall p q, epge (eplub p q) p.
Proof.
  unfold eplub; destruct p, q; auto with va ; try (simpl ; auto; fail);
  repeat case_match ; try (simpl;intuition; fail).
Qed.

Lemma epge_lub_r:
  forall p q, epge (eplub p q) q.
Proof.
  intros. rewrite eplub_comm. apply epge_lub_l.
Qed.

Lemma epmatch_lub_l:
  forall e p q, epmatch e p -> epmatch e (eplub p q).
Proof.
  intros. eapply epmatch_ge; eauto. apply epge_lub_l.
Qed.

(*
Lemma pmatch_lub_r:
  forall b ofs p q, pmatch b ofs q -> pmatch b ofs (plub p q).
Proof.
  intros. eapply pmatch_ge; eauto. apply pge_lub_r.
Qed.
*)
Lemma epmatch_lub_r:
  forall e p q, epmatch e q -> epmatch e (eplub p q).
Proof.
  intros. eapply epmatch_ge; eauto. apply epge_lub_r.
Qed.


Lemma eplub_least:
  forall r p q, epge r p -> epge r q -> epge r (eplub p q).
Proof.
  intros.
  destruct r, p, q ; try (simpl in * ; try tauto ; repeat case_match ; intuition congruence).
Qed.

Definition pincl (p q: aptr) : bool :=
  match p, q with
  | Pbot, _ => true
  | Gl id1 ofs1, Gl id2 ofs2 => peq id1 id2 && Int.eq_dec ofs1 ofs2
  | Gl id1 ofs1, Glo id2 => peq id1 id2
  | Glo id1, Glo id2 => peq id1 id2
  | (Gl _ _ | Glo _ | Glob), Glob => true
  | (Gl _ _ | Glo _ | Glob | Nonstack), Nonstack => true
  | Stk ofs1, Stk ofs2 => Int.eq_dec ofs1 ofs2
  | Stk ofs1, Stack => true
  | Stack, Stack => true
  | _, Ptop => true
  | _, _ => false
  end.


Definition ege_bool (p q : aptr) : bool :=
  match p, q with
    | Ptop , _ => true
    | Nonstack , (Nonstack| Glob | Glo _ | Gl _ _ | Pcst | Pbot) => true
    | Glob     , (Glob | Glo _ | Gl _ _ | Pcst | Pbot) => true
    | Glo  id   , (Glo id' | Gl id' _) => peq id  id'
    | Glo  _   , Pcst                 => true
    | Gl id o   , Gl id' o'          => peq id  id' && Int.eq_dec o  o'
    | Stack    , (Stack | Stk _ | Pcst )   => true
    | Stk o , Stk o'    => Int.eq_dec o  o'
    | Pbot , Pbot       => true
    | _    , Pbot       => true
    |  Pbot , _         => false
    | Pcst  , Pcst      => true
    | _  ,   _       => false
  end.

Definition epincl (p q : aptr) : bool := ege_bool q p.

Lemma epincl_ge: forall p q, epincl p q = true -> epge q p.
Proof.
  intros.
  destruct p , q ; simpl in * ; try discriminate ; auto with va;
  InvBooleans; subst; auto with va.
Qed.

Lemma pincl_ge_2: forall p q, epge p q -> epincl q p = true.
Proof.
  destruct p, q ; simpl ; try (intuition congruence).
  - intuition subst.
    rewrite ! proj_sumbool_is_true ; auto.
  - intro ; subst.
    rewrite ! proj_sumbool_is_true; auto.
  - intro ; subst.
    rewrite ! proj_sumbool_is_true; auto.
  - 
    destruct (Int.eq_dec ofs ofs0) ; auto.
Qed.

Lemma epincl_sound:
  forall e p q,
  epincl p q = true -> epmatch e p -> epmatch e q.
Proof.
  intros. eapply epmatch_ge; eauto. apply epincl_ge; auto. 
Qed.

Lemma depends_is_pointer :
  forall  S b ofs align bound (NOFORGERY : no_forgery Int.max_unsigned bound align), 
    depends_on_blocks  S (Eval (Vptr b ofs)) -> S b.
Proof.
  unfold depends_on_blocks.
  intros. simpl in *.
  assert (NOF := NOFORGERY).
  destruct (NOFORGERY b) as [CM1 [COMPAT1 CM2EQ]].
  destruct (CM2EQ) as [CM2 [COMPAT2 SAMEX]].
  destruct (classic (S b)); auto.
  assert  (Vint (Int.add (CM1 b) ofs) = Vint (Int.add (CM2 b) ofs)).
  {
    eapply H; eauto.
    intros.
    destruct (peq b b0) ; subst. tauto.
    apply (SAME _ _ _ SAMEX); auto.
    intros ; apply Byte.zero.
  }
  apply inj_vint in H1.
  rewrite Int.add_commut in H1.
  rewrite (Int.add_commut (CM2 b)) in H1.
  apply int_add_eq_l in H1. 
  generalize (DIFF _ _ _ SAMEX); auto.  congruence.
Qed.


Lemma depends_on_block_pointer : 
  forall (S : block -> Prop) b ofs e
          align bound (NOFORGERY : no_forgery Int.max_unsigned bound align)
  ,
             (S b -> False) -> 
       is_pointer b ofs e   -> 
       depends_on_blocks S e -> False.
Proof.
  repeat intro.
  rew_cst H0.
  eapply depends_is_pointer in H1; eauto.
Qed.

Lemma epincl_not_ge: forall p q, epincl p q = false -> ~ epge q p.
Proof.
 intros.
 intro.   destruct p , q ; simpl in * ; try discriminate ; auto with va;
  InvBooleans; subst; auto with va.
  destruct H0 ; subst.
  unfold proj_sumbool in H.
  destruct (peq id id) ; try congruence.
  destruct (Int.eq_dec ofs ofs) ; simpl in * ; try congruence.
  destruct (peq id id) ; simpl in * ; congruence.
  destruct (peq id id) ; simpl in * ; congruence.
  destruct (Int.eq_dec ofs ofs) ; simpl in * ; try congruence.
Qed.

Definition padd (p: aptr) (n: int) : aptr :=
  match p with
  | Gl id ofs => Gl id (Int.add ofs n)
  | Stk ofs => Stk (Int.add ofs n)
  | _ => p
  end.



Ltac seval_prf :=
  unfold is_constant, Val.add, Val.sub in *;
  match goal with
    | H : same_eval ?X ?Y |- same_eval ?Z ?T =>
      match Z with
        | context[X] => rewrite H
        | context[Y] => rewrite <- H
      end
    | H : same_eval ?X ?Y |- same_eval ?Z ?T =>
      match T with
        | context[X] => rewrite H
        | context[Y] => rewrite <- H
      end; repeat intro ; simpl
  end.



Hint Extern 2 (same_eval _  _) => seval_prf : va.
Hint Extern 2 (depends_on_block _  _) => depends_prf : va.
Hint Extern 2 (depends_on_blocks _  _) => depends_prf : va.
 
Lemma is_pointer_add :
  forall b ofs e delta,
    is_pointer b ofs e -> 
    is_pointer b (Int.add ofs delta) (Val.add e (Eval (Vint delta))).
Proof.
  unfold is_pointer ; intros.
  unfold Val.add.
  rewrite <- H.
  repeat intro ; simpl.
  rewrite Int.add_assoc.  
  reflexivity.
Qed.
  
Lemma epadd_sound:
  forall e p delta,
  epmatch e p ->
  epmatch (Val.add e (Eval (Vint delta))) (padd p delta).
Proof.
  intros. inv H; simpl padd; econstructor ; unfold is_constant in * ; eauto with va.
  -
    depends_prf.
  -     
    apply  is_pointer_add; auto.
  - 
    apply  is_pointer_add; auto.
Qed.

Definition psub (p: aptr) (n: int) : aptr :=
  match p with
  | Gl id ofs => Gl id (Int.sub ofs n)
  | Stk ofs => Stk (Int.sub ofs n)
  | _ => p
  end.

Lemma psub_sound:
  forall b ofs p delta,
  pmatch b ofs p ->
  pmatch b (Int.sub ofs delta) (psub p delta).
Proof.
  intros. inv H; simpl psub; eauto with va. 
Qed.

Lemma is_pointer_sub :
  forall b ofs e delta,  
    is_pointer b ofs e -> 
   is_pointer b (Int.sub ofs delta) (Val.sub e (Eval (Vint delta))).
Proof.
  unfold is_pointer ; intros.
  unfold Val.sub.
  rewrite <- H.
  repeat intro ; simpl.
  repeat rewrite Int.sub_add_opp.
  rewrite Int.add_assoc.
  reflexivity.
Qed.

Lemma epsub_sound:
  forall e p delta,
  epmatch e p ->
  epmatch (Val.sub e (Eval (Vint delta))) (psub p delta).
Proof.
  intros. inv H; simpl psub; unfold is_constant in * ; econstructor; eauto with va.
  - 
    depends_prf.
  - 
    eapply is_pointer_sub ; eauto.
  - 
    eapply is_pointer_sub ; eauto.
Qed.


Definition poffset (p: aptr) : aptr :=
  match p with
  | Gl id ofs => Glo id
  | Stk ofs => Stack
  | _ => p
  end.

Lemma poffset_sound :
  forall e p,
    epmatch e p -> 
    epmatch e (poffset p).
Proof.
  intros.
  inv H ; constructor ; auto with va.
Qed.

Hint Resolve poffset_sound : va.


Definition psub2 (p q: aptr) : option int :=
  match p, q with
  | Gl id1 ofs1, Gl id2 ofs2 =>
      if peq id1 id2 then Some (Int.sub ofs1 ofs2) else None
  | Stk ofs1, Stk ofs2 =>
      Some (Int.sub ofs1 ofs2)
  | _, _ =>
      None
  end.


Lemma psub2_sound:
  forall b1 ofs1 p1 b2 ofs2 p2 delta,
  psub2 p1 p2 = Some delta ->
  pmatch b1 ofs1 p1 ->
  pmatch b2 ofs2 p2 ->
  b1 = b2 /\ delta = Int.sub ofs1 ofs2.
Proof.
  intros. destruct p1; try discriminate; destruct p2; try discriminate; simpl in H.
- destruct (peq id id0); inv H. inv H0; inv H1.
  split. eapply bc_glob; eauto. reflexivity.
- inv H; inv H0; inv H1. split. eapply bc_stack; eauto. reflexivity.
Qed.

Lemma epsub2_sound:
  forall e1 p1 e2 p2 delta,
    psub2 p1 p2 = Some delta ->
    epmatch e1 p1 ->
    epmatch e2 p2 ->
    is_constant (Vint delta) (Val.sub e1 e2).
Proof.
  intros.
  assert (HDIFF : forall b b' ofs ofs',
                    b = b' ->
                    is_pointer b ofs e1 ->
                    is_pointer b' ofs' e2 ->
                    is_constant (Vint (Int.sub ofs ofs')) (Val.sub e1 e2)).
  {
    unfold is_constant,is_pointer in *.
    unfold Val.sub. intros.
    subst.
    rewrite <- H3.
    rewrite <- H4.
    repeat intro.
    simpl.
    apply f_equal.
    repeat rewrite Int.sub_add_opp.
    rewrite Int.neg_add_distr.
    rewrite (Int.add_commut (cm b')).
    rewrite Int.add_assoc.
    apply f_equal.
    rewrite <- Int.add_assoc.
    rewrite Int.add_neg_zero.
    rewrite Int.add_zero_l.
    reflexivity.
  } 
  destruct p1; try discriminate; destruct p2; try discriminate; simpl in H.
  - destruct (peq id id0); inv H. inv H0; inv H1.
    eapply HDIFF with (b:=b) (b':=b0); eauto.
    eapply bc_glob ; eauto.
  - 
    inv H; inv H0; inv H1.
    eapply HDIFF with (b:=b) (b':=b0); eauto.    
    eapply bc_stack; eauto.
Qed.

Definition cmp_different_blocks (c: comparison) : abool :=
  match c with
  | Ceq => Maybe false
  | Cne => Maybe true
  | _   => Bnone
  end.

Definition cmp_in_bound_different_blocks (c: comparison) : abool :=
  match c with
  | Ceq => Just false
  | Cne => Just true
  | _   => Btop
  end.



Lemma cmp_different_blocks_none:
  forall c, cmatch None (cmp_different_blocks c).
Proof.
  intros; destruct c; constructor.
Qed.

Lemma cmp_different_blocks_sound:
  forall c, cmatch (Val.cmp_different_blocks c) (cmp_different_blocks c).
Proof.
  intros; destruct c; constructor.
Qed.

Definition in_boundb (o : Z) (itv : Z * Z) : bool :=
  (zle (fst itv) o) && (zlt o (snd itv)).

Lemma in_boundb_bound :
  forall o itv, in_boundb o itv = true <-> in_bound o itv.
Proof.
  intros.
  unfold in_boundb.
  rewrite andb_true_iff.
  unfold in_bound.
  destruct (zle (fst itv) o);
    destruct (zlt o (snd itv)); intuition.
Qed.
  
Definition in_bound_glob (id:ident) (ofs : int)  : bool := false.
(*  match glob_size ms id with
    | None => false
    | Some ub => in_boundb (Int.unsigned ofs) (0,ub)
  end.
*)

Definition in_bound_stack  (ofs : int)  : bool := false.
(*  in_boundb (Int.unsigned ofs) (0,stack_size ms).*)

Definition pcmp (c: comparison) (p1 p2: aptr) : abool :=
  match p1, p2 with
  | Pbot, _ | _, Pbot => Bnone
  | Gl id1 ofs1, Gl id2 ofs2 =>
    if in_bound_glob id1 ofs1 && in_bound_glob id2 ofs2
    then
      if peq id1 id2 then Just (Int.cmpu c ofs1 ofs2)
      else cmp_in_bound_different_blocks c
    else Btop (* could do better for equality and disequality *)
  | Gl id1 ofs1, Glo id2 => Btop
  | Glo id1, Gl id2 ofs2 => Btop
  | Glo id1, Glo id2 => Btop
  | Stk ofs1, Stk ofs2 =>
    if in_bound_stack ofs1 && in_bound_stack ofs2
    then Just (Int.cmpu c ofs1 ofs2)
    else Btop
  | _, _ => Btop 
  end.

(*
Lemma in_bound_glob_size :
  forall b id o ub
         (HASZ : glob_size ms id = Some ub),
    in_bound o (0, ub) -> 
    bc b = BCglob id -> 
    forall bd,
      szmatch bd  -> 
      in_bound o (bd b).
Proof.
  intros.
  intros.
  apply szmatch_glob with (bound := bd) (b:=b) in HASZ ; auto.
  generalize (szmatch_lb bd H1 b).
  destruct (bd b) ; simpl in * ; congruence.
Qed.

Lemma in_bound_stk_size :
  forall b o,
         in_bound o (0, stack_size ms) -> 
         bc b = BCstack -> 
         forall bd,
         szmatch bd  -> 
         in_bound o (bd b).
Proof.
  intros.
  intros.
  rewrite <- szmatch_stack with (bound := bd) (b:=b) in H ; auto.
  generalize (szmatch_lb bd H1 b).
  destruct (bd b) ; simpl in * ; congruence.
Qed.
*)
Lemma no_overlap :
  forall a b1 b2 ofs1 ofs2 bound align
         (NEQ     : b1 <> b2)
         (COMPAT  : compat Int.max_unsigned bound align a)
         (BOUND1  : in_bound (Int.unsigned ofs1) (bound b1))
         (BOUND2  : in_bound (Int.unsigned ofs2) (bound b2)),
    Int.add (a b1) ofs1 = Int.add (a b2) ofs2 -> False.
Proof.
  intros.
  apply f_equal with (f:= Int.unsigned) in H.
  revert H.
  eapply overlap ; eauto.
Qed.  

Lemma is_bool_cmpu_bool : forall c e1 e2,
                    is_bool (Val.cmpu_bool c e1 e2).
Proof.
  intros.
  repeat intro ; simpl.
  destruct (eSexpr a u e1) ; destruct (eSexpr a u e2) ; simpl;
  try (exists Int.zero ; simpl ; intuition constructor).
  destruct (Int.cmpu c i i0) ;
    try (exists Int.zero ; simpl ; intuition constructor);
    try (exists Int.one ; simpl ; intuition constructor).
Qed.  

(*
Lemma ecmatch_cmpu_diff_blocks :
  forall c e1 e2 b1 b2 ofs1 ofs2 bound 
         (NEQ : b1 <> b2)
         (C1     : is_pointer b1 ofs1 e1 )
         (C2     : is_pointer b2 ofs2 e2 )
         (SZ :
            in_bound (Int.unsigned ofs1) (bound b1)
            /\
            in_bound (Int.unsigned ofs2) (bound b2)),
    ecmatch (Val.cmpu_bool c e1 e2) (cmp_in_bound_different_blocks c).
Proof.
  intros.
  assert (BOOL := is_bool_cmpu_bool c e1 e2).
  unfold Val.cmpu_bool in *.
  rew_cst C1.
  rew_cst C2.
  destruct c; simpl; try constructor ; simpl; auto.
  - 
    repeat intro ; simpl.
    predSpec Int.eq Int.eq_spec (Int.add (a b1) ofs1) (Int.add (a b2) ofs2); auto.
    exfalso.
    destruct SZ.
    eapply no_overlap ; eauto.
  - 
    repeat intro. simpl.
    predSpec Int.eq Int.eq_spec (Int.add (a b1) ofs1) (Int.add (a b2) ofs2); simpl ; auto.    
    exfalso.
    destruct SZ.
    eapply no_overlap ; eauto.
Qed.
*)

Lemma pcmp_sound:
  forall  c e1 p1 e2 p2,
  epmatch e1 p1 -> epmatch e2 p2 ->
  ecmatch (Val.cmpu_bool c e1 e2) (pcmp c p1 p2).
Proof.
  intros.
(*  assert (SAME:
            forall b1 ofs1 b2 ofs2
                   (EQ : b1 = b2)
                   (C1     : is_constant (Vptr b1 ofs1) e1 )
                   (C2     : is_constant (Vptr b2 ofs2) e2 )
                   (SZ :   in_bound (Int.unsigned ofs1) (bound b1)
                                     /\
                                     in_bound (Int.unsigned ofs2) (bound b2))
            ,
              
   is_constant (val_of_bool (Int.cmpu c ofs1 ofs2)) (Val.cmpu_bool c e1 e2)).
  {
    intros. subst b2.
    unfold Val.cmpu_bool.
    simpl.
    rew_cst C1.
    rew_cst C2.
    clear C1 C2.
    unfold is_constant in *.
    unfold same_eval in *.
    simpl. intros.
    rewrite Int.add_commut.
    rewrite (Int.add_commut (a b1)).
    erewrite Cop.compat_conserve_cmp ; eauto.
    destruct (Int.cmpu c ofs1 ofs2) ; reflexivity.
    omega.
    apply szmatch_lb; auto.
    tauto.
    tauto.
  } *)
  unfold pcmp; inv H ; inv H0; try (constructor ; apply is_bool_cmpu_bool; fail).
  Qed.
(*  -
    case_match ; try constructor.
    destruct (peq id id0) ; try constructor.
    +
      eapply SAME with (2:= H2) (3:= H3) ; eauto.
      eapply bc_glob ; eauto. congruence.
      intros.
      rewrite andb_true_iff in H0.
      subst.
      unfold in_bound_glob in *.
      revert H0.      
      case_eq (glob_size ms id0) ; simpl ; try intuition congruence.
      intros.
      repeat rewrite in_boundb_bound in *.
      destruct H4 as [IBO IBO'].
      split ; eapply in_bound_glob_size ; eauto.
    + 
      intros.
      eapply ecmatch_cmpu_diff_blocks with (2:= H2) (3:= H3); eauto.
      congruence.
      rewrite andb_true_iff in H0.      
      unfold in_bound_glob in *.
      revert H0.
      case_eq (glob_size ms id) ; simpl ; try intuition congruence.
      case_eq (glob_size ms id0) ; simpl ; try intuition congruence.
      intros.
      repeat rewrite in_boundb_bound in *.
      destruct H5.
      split.
      eapply in_bound_glob_size ; eauto.
      clear H1 H4.
      eapply in_bound_glob_size ; eauto.
    + apply is_bool_cmpu_bool.
  - 
    case_match ; try constructor.
    eapply SAME with (2:= H2) (3:= H3) ; eauto.
    eapply bc_stack ; eauto. 
    intros.
    rewrite andb_true_iff in H0.
    destruct H0 as [IBO IBO'].
    unfold in_bound_stack in *.
    rewrite in_boundb_bound in *.
    split ; eapply in_bound_stk_size ; eauto.
    apply is_bool_cmpu_bool.
Qed.
*)
(*
Lemma pcmp_none:
  forall c p1 p2, cmatch None (pcmp c p1 p2).
Proof.
  intros.
  unfold pcmp; destruct p1; try constructor; destruct p2;
  try (destruct (peq id id0));  try constructor; try (apply cmp_different_blocks_none).
Qed.
*)

Definition pdisjoint (p1: aptr) (sz1: Z) (p2: aptr) (sz2: Z) : bool :=
  match p1, p2 with
  | Pbot, _ => true
  | _, Pbot => true
  | Gl id1 ofs1, Gl id2 ofs2 =>
      if peq id1 id2
      then zle (Int.unsigned ofs1 + sz1) (Int.unsigned ofs2)
           || zle (Int.unsigned ofs2 + sz2) (Int.unsigned ofs1)
      else true
  | Gl id1 ofs1, Glo id2 => negb(peq id1 id2)
  | Glo id1, Gl id2 ofs2 => negb(peq id1 id2)
  | Glo id1, Glo id2 => negb(peq id1 id2)
  | Stk ofs1, Stk ofs2 =>
      zle (Int.unsigned ofs1 + sz1) (Int.unsigned ofs2)
      || zle (Int.unsigned ofs2 + sz2) (Int.unsigned ofs1)
  | (Gl _ _ | Glo _ | Glob | Nonstack), (Stk _ | Stack) => true
  | (Stk _ | Stack), (Gl _ _ | Glo _ | Glob | Nonstack) => true
  | _, _ => false
  end.

Lemma pdisjoint_sound:
  forall sz1 b1 ofs1 p1 sz2 b2 ofs2 p2,
  pdisjoint p1 sz1 p2 sz2 = true ->
  pmatch b1 ofs1 p1 -> pmatch b2 ofs2 p2 ->
  b1 <> b2 \/ Int.unsigned ofs1 + sz1 <= Int.unsigned ofs2 \/ Int.unsigned ofs2 + sz2 <= Int.unsigned ofs1.
Proof.
  intros. inv H0; inv H1; simpl in H; try discriminate; try (left; congruence).
- destruct (peq id id0). subst id0. destruct (orb_true_elim _ _ H); InvBooleans; auto.
  left; congruence.
- destruct (peq id id0); try discriminate. left; congruence.
- destruct (peq id id0); try discriminate. left; congruence.
- destruct (peq id id0); try discriminate. left; congruence.
- destruct (orb_true_elim _ _ H); InvBooleans; auto.
Qed.

(** We need to prevent overflows + there is no way to ensure that stack and gl are disjoint.
    We would need the the size of the block!

Lemma epdisjoint_sound :
  forall sz1 e1 p1 sz2 e1 p2,
    pdisjoint p1 sz1 p2 sz2 = true ->
    epmatch e1 p1 -> epmatch e2 p2 ->
    forall i j, i
    eSexpr 
*)


(** * Abstracting values *)

Inductive aval : Type :=
(*  | Vbot                     (**r bottom (empty set of values) *)*)
  | I (n: int)               (**r exactly [Vint n] *)
  | Uns (p: aptr) (n: Z)     (**r a [n]-bit unsigned integer, or [Vundef] *)
  | Sgn (p: aptr) (n: Z)     (**r a [n]-bit signed integer, or [Vundef] *)
  | L (n: int64)             (**r exactly [Vlong n] *)
  | F (f: float)             (**r exactly [Vfloat f] *)
  | FS (f: float32)          (**r exactly [Vsingle f] *)
  | Ptr (p: aptr)            (**r a pointer from the set [p], or [Vundef] *)
(*  | Ifptr (p: aptr)*).         (**r a pointer from the set [p], or a number, or [Vundef] *)

(** The "top" of the value domain is defined as any pointer, or any
    number, or [Vundef]. *)

Definition Vtop := Ptr Ptop.

(** The [p] parameter (an abstract pointer) to [Uns] and [Sgn] helps keeping
  track of pointers that leak through arithmetic operations such as shifts.
  See the section "Tracking leakage of pointers" below.
  In strict analysis mode, [p] is always [Pbot]. *)

Definition eq_aval: forall (v1 v2: aval), {v1=v2} + {v1<>v2}.
Proof.
  intros. generalize zeq Int.eq_dec Int64.eq_dec Float.eq_dec Float32.eq_dec eq_aptr; intros.
  decide equality. 
Defined.

Definition is_uns (n: Z) (i: int) : Prop :=
  forall m, 0 <= m < Int.zwordsize -> m >= n -> Int.testbit i m = false.
Definition is_sgn (n: Z) (i: int) : Prop :=
  forall m, 0 <= m < Int.zwordsize -> m >= n - 1 -> Int.testbit i m = Int.testbit i (Int.zwordsize - 1).

Definition is_unsigned (n: Z) (e: expr_sym) : Prop :=
  forall a  u 
  ,
  exists i, Values.Val.lessdef (eSexpr a u e) (Vint i) /\ is_uns n i.

Definition is_signed (n: Z) (e: expr_sym) : Prop :=
  forall a u 
  ,
  exists i, Values.Val.lessdef (eSexpr a u e) (Vint i) /\ is_sgn n i.

Add Parametric Morphism (n:Z) : (is_unsigned n) with signature (same_eval ==> iff) as is_unsigned_same_eval_morph.
Proof.
  assert (
      forall x y : expr_sym,
        same_eval x y -> (is_unsigned n x -> is_unsigned n y) ).
  {
  unfold is_unsigned.
  intros.
  intuition.
  destruct (H0 a  u); auto.
  exists x0.
  erewrite <- H; eauto.
  }
  intuition ; eapply H ; eauto.
  rewrite H0 ; reflexivity.
Qed.  

Add Parametric Morphism (n:Z) : (is_signed n) with signature (same_eval ==> iff) as is_signed_same_eval_morph.
Proof.
  assert (   forall x y : expr_sym, same_eval x y -> (is_signed n x -> is_signed n y)).
  {
  unfold is_signed.
  intros.
  intuition.
  destruct (H0 a u); auto.
  exists x0.
  erewrite <- H; eauto.
  }
  intuition ; eapply H ; eauto.
  rewrite H0 ; reflexivity.
Qed.  




Inductive evmatch : expr_sym -> aval -> Prop :=
  | evmatch_i: forall i e, is_constant (Vint i) e -> evmatch e (I i)
  | evmatch_Uns: forall p e n, 0 <= n ->
                               is_unsigned n e ->
                               epmatch e p     -> 
                               evmatch e (Uns p n)
(*  | evmatch_Uns_undef: forall p n, vmatch Vundef (Uns p n)*)
  | evmatch_Sgn: forall p e n, 0 < n ->
                               is_signed n e ->
                               epmatch e p   -> 
                               evmatch e (Sgn p n)
(*  | evmatch_Sgn_undef: forall p n, vmatch Vundef (Sgn p n)*)
  | evmatch_l: forall e i, is_constant (Vlong i) e -> evmatch e (L i)
  | evmatch_f: forall e f, is_constant (Vfloat f) e -> evmatch e (F f)
  | evmatch_s: forall e f, is_constant (Vsingle f) e -> evmatch e (FS f)
  | evmatch_ptr: forall e p, epmatch e p -> evmatch e (Ptr p)
(*  | evmatch_ptr_undef: forall p, vmatch Vundef (Ptr p)
  | evmatch_ifptr_undef: forall p, vmatch Vundef (Ifptr p) *)
(*  | evmatch_ifptr_i: forall i p, vmatch (Vint i) (Ifptr p)
  | evmatch_ifptr_l: forall i p, vmatch (Vlong i) (Ifptr p)
  | evmatch_ifptr_f: forall f p, vmatch (Vfloat f) (Ifptr p)
  | evmatch_ifptr_s: forall f p, vmatch (Vsingle f) (Ifptr p)
  | evmatch_ifptr_p: forall b ofs p, pmatch b ofs p -> vmatch (Vptr b ofs) (Ifptr p).
*).
(*
Lemma vmatch_ifptr:
  forall v p,
  (forall b ofs, v = Vptr b ofs -> pmatch b ofs p) ->
  vmatch v (Ifptr p).
Proof.
  intros. destruct v; constructor; auto. 
Qed.
 *)
(*
Lemma vmatch_top: forall v x, vmatch v x -> vmatch v Vtop.
Proof.
  intros. apply vmatch_ifptr. intros. subst v. inv H; eapply pmatch_top'; eauto.
Qed.
*)

Add Parametric Morphism : evmatch with signature (same_eval ==> @eq aval ==> iff) as evmatch_same_eval_morph.
Proof.
  assert (   forall x y : expr_sym,
               same_eval x y -> forall y0 : aval, evmatch x y0 -> evmatch y y0).
  {
    intros.
    inv H0 ; try constructor; auto with va; try rewrite H in *; auto.
  }
  intuition ; eapply H ; eauto.
  rewrite H0 ; reflexivity.
Qed.  




Hint Resolve epmatch_top_def : va.

Lemma evmatch_top: forall v x, evmatch v x -> evmatch v Vtop.
Proof.
  intros.
  constructor.
  inv H ; eauto with va ; unfold is_constant in * ; constructor.
Qed.

(*Hint Extern 1 (vmatch _ _) => constructor : va.*)
Hint Extern 1 (evmatch _ _) => constructor : va.

(* Some properties about [is_uns] and [is_sgn]. *)

Lemma is_uns_mon: forall n1 n2 i, is_uns n1 i -> n1 <= n2 -> is_uns n2 i.
Proof.
  intros; red; intros. apply H; omega.
Qed.

Lemma is_sgn_mon: forall n1 n2 i, is_sgn n1 i -> n1 <= n2 -> is_sgn n2 i.
Proof.
  intros; red; intros. apply H; omega.
Qed.

Lemma is_uns_sgn: forall n1 n2 i, is_uns n1 i -> n1 < n2 -> is_sgn n2 i.
Proof.
  intros; red; intros. rewrite ! H by omega. auto.
Qed.

Definition usize := Int.size.

Definition ssize (i: int) := Int.size (if Int.lt i Int.zero then Int.not i else i) + 1.

Lemma is_uns_usize:
  forall i, is_uns (usize i) i.
Proof.
  unfold usize; intros; red; intros. 
  apply Int.bits_size_2. omega. 
Qed.

Lemma is_sgn_ssize:
  forall i, is_sgn (ssize i) i.
Proof.
  unfold ssize; intros; red; intros.
  destruct (Int.lt i Int.zero) eqn:LT.
- rewrite <- (negb_involutive (Int.testbit i m)).
  rewrite <- (negb_involutive (Int.testbit i (Int.zwordsize - 1))).
  f_equal.
  generalize (Int.size_range (Int.not i)); intros RANGE.
  rewrite <- ! Int.bits_not by omega.
  rewrite ! Int.bits_size_2 by omega.
  auto.
- rewrite ! Int.bits_size_2 by omega.
  auto.
Qed.

Lemma is_uns_zero_ext:
  forall n i, is_uns n i <-> Int.zero_ext n i = i.
Proof.
  intros; split; intros. 
  Int.bit_solve. destruct (zlt i0 n); auto. symmetry; apply H; auto. omega.
  rewrite <- H. red; intros. rewrite Int.bits_zero_ext by omega. rewrite zlt_false by omega. auto.
Qed.

Lemma is_sgn_sign_ext:
  forall n i, 0 < n -> (is_sgn n i <-> Int.sign_ext n i = i).
Proof.
  intros; split; intros. 
  Int.bit_solve. destruct (zlt i0 n); auto.
  transitivity (Int.testbit i (Int.zwordsize - 1)).
  apply H0; omega. symmetry; apply H0; omega. 
  rewrite <- H0. red; intros. rewrite ! Int.bits_sign_ext by omega.
  f_equal. transitivity (n-1). destruct (zlt m n); omega. 
  destruct (zlt (Int.zwordsize - 1) n); omega.
Qed.

Lemma is_zero_ext_uns:
  forall i n m,
  is_uns m i \/ n <= m -> is_uns m (Int.zero_ext n i).
Proof.
  intros. red; intros. rewrite Int.bits_zero_ext by omega.
  destruct (zlt m0 n); auto. destruct H. apply H; omega. omegaContradiction. 
Qed.

Lemma is_zero_ext_sgn:
  forall i n m,
  n < m ->
  is_sgn m (Int.zero_ext n i).
Proof.
  intros. red; intros. rewrite ! Int.bits_zero_ext by omega. 
  transitivity false. apply zlt_false; omega.
  symmetry; apply zlt_false; omega.
Qed.

Lemma is_sign_ext_uns:
  forall i n m,
  0 <= m < n ->
  is_uns m i ->
  is_uns m (Int.sign_ext n i).
Proof.
  intros; red; intros. rewrite Int.bits_sign_ext by omega. 
  apply H0. destruct (zlt m0 n); omega. destruct (zlt m0 n); omega.
Qed.
  
Lemma is_sign_ext_sgn:
  forall i n m,
  0 < n -> 0 < m ->
  is_sgn m i \/ n <= m -> is_sgn m (Int.sign_ext n i).
Proof.
  intros. apply is_sgn_sign_ext; auto.
  destruct (zlt m n). destruct H1. apply is_sgn_sign_ext in H1; auto. 
  rewrite <- H1. rewrite (Int.sign_ext_widen i) by omega. apply Int.sign_ext_idem; auto. 
  omegaContradiction.
  apply Int.sign_ext_widen; omega.
Qed.

Hint Resolve is_uns_mon is_sgn_mon is_uns_sgn is_uns_usize is_sgn_ssize : va.

Lemma is_uns_1:
  forall n, is_uns 1 n -> n = Int.zero \/ n = Int.one.
Proof.
  intros. destruct (Int.testbit n 0) eqn:B0; [right|left]; apply Int.same_bits_eq; intros.
  rewrite Int.bits_one. destruct (zeq i 0). subst i; auto. apply H; omega. 
  rewrite Int.bits_zero. destruct (zeq i 0). subst i; auto. apply H; omega.
Qed.

(** Tracking leakage of pointers through arithmetic operations.

In the CompCert semantics, arithmetic operations (e.g. "xor") applied
to pointer values are undefined or produce the [Vundef] result.
So, in strict mode, we can abstract the result values of such operations
as [Ifptr Pbot], namely: [Vundef], or any number, but not a pointer.

In real code, such arithmetic over pointers occurs, so we need to be
more prudent.  The policy we take, inspired by that of GCC, is that
"undefined" arithmetic operations involving pointer arguments can
produce a pointer, but not any pointer: rather, a pointer to the same
block, but possibly with a different offset.  Hence, if the operation
has a pointer to abstract region [p] as argument, the result value
can be a pointer to abstract region [poffset p].  In other words,
the result value is abstracted as [Ifptr (poffset p)].

We encapsulate this reasoning in the following [ntop1] and [ntop2] functions
("numerical top"). *)


Definition aptr_of_aval (x : aval) : aptr :=
  match x with
    | Ptr p  | Uns p _ | Sgn p _ =>  p
    | I _ | L _ | F _ | FS _ => Pcst
  end.

Definition provenance (x: aval) : aptr :=
  poffset (aptr_of_aval x).

Definition ntop : aval := Ptr Pcst.

Definition ntop1 (x: aval) : aval := Ptr (provenance x).

Definition ntop2 (x y: aval) : aval := Ptr (eplub (provenance x) (provenance y)).


(** Smart constructors for [Uns] and [Sgn]. *)

Definition uns (p: aptr) (n: Z) : aval :=
  if zle n 1 then Uns p 1
  else if zle n 7 then Uns p 7
  else if zle n 8 then Uns p 8
  else if zle n 15 then Uns p 15
  else if zle n 16 then Uns p 16
  else Ptr p.

Definition sgn (p: aptr) (n: Z) : aval :=
  if zle n 8 then Sgn p 8 else if zle n 16 then Sgn p 16 else Ptr p.

Definition is_bot (v : aval) :=
           aptr_of_aval v = Pbot.


Inductive evge: aval -> aval -> Prop :=
  | evge_refl: forall v, evge v v
  | evge_uns_i: forall  n p i, 0 <= n -> is_uns n i -> epge p Pcst -> 
                             evge (Uns p n) (I i)
  | evge_p_i : forall p i, epge p Pcst -> evge (Ptr p) (I i)
  | evge_p_l : forall p i, epge p Pcst -> evge (Ptr p) (L i)
  | evge_p_f : forall p i, epge p Pcst -> evge (Ptr p) (F i)
  | evge_p_s : forall p i, epge p Pcst -> evge (Ptr p) (FS i)                                               
  | evge_uns_uns: forall p1 n1 p2 n2, n1 >= n2 -> epge p1 p2 -> evge (Uns p1 n1) (Uns p2 n2)
  | evge_sgn_i: forall n p i, 0 < n -> is_sgn n i -> epge p Pcst -> evge (Sgn p n) (I i)
  | evge_sgn_sgn: forall p1 n1 p2 n2, n1 >= n2 -> epge p1 p2 -> evge (Sgn p1 n1) (Sgn p2 n2)
  | evge_sgn_uns: forall p1 n1 p2 n2, n1 > n2 -> epge p1 p2 -> evge (Sgn p1 n1) (Uns p2 n2)
  | evge_p_uns  : forall p1 p2 n1, epge p1 p2 -> evge (Ptr p1) (Uns p2 n1)
  | evge_p_sgn  : forall p1 p2 n1, epge p1 p2 -> evge (Ptr p1) (Sgn p2 n1)
  | evge_p_p: forall p q, epge p q -> evge (Ptr p) (Ptr q)
  | evge_top_v: forall v, evge (Ptr Ptop) v
  | evge_bot: forall v v', is_bot v' -> evge v v'
.

Lemma evge_top: forall v, evge Vtop v.
Proof.
  unfold Vtop.
  intro. apply evge_top_v.
Qed.

Hint Resolve evge_top : va.

Lemma epge_top : forall p, epge p Ptop -> p = Ptop.
Proof.
  intros.
  destruct p ; simpl in H ; tauto.
Qed.

Lemma epge_bot : forall p, epge Pbot p -> p = Pbot.
Proof.
  intros.
  destruct p ; simpl in H ; tauto.
Qed.



Lemma evge_trans: forall u v, evge u v -> forall w, evge v w -> evge u w.
Proof.
  induction 1; intros w V; inv V; unfold is_bot, aptr_of_aval in * ; subst;
  eauto using epge_trans with va ; try (constructor; auto; try omega; eauto using epge_trans ; eauto with va ; fail) ; (try (simpl in * ; tauto)).
  - 
    apply epge_top in H. subst. constructor.
  - apply epge_bot in H1.  subst.   apply evge_bot. reflexivity.
  - apply epge_bot in H1. subst.
    apply evge_bot. reflexivity.
  - apply epge_bot in H1. subst.
    apply evge_bot. reflexivity.
  - apply epge_bot in H0. subst.
    apply evge_bot. reflexivity.
  - apply epge_bot in H0. subst.
    apply evge_bot. reflexivity.
  - apply epge_bot in H0. subst.
    apply evge_bot. reflexivity.
  - congruence.
Qed.

(*
Lemma evge_trans: forall u v, evge u v -> forall w, evge v w -> evge u w.
Proof.
  induction 1; intros w V; inv V; eauto using epge_trans with va ; try constructor ; try omega; eauto using epge_trans ; eauto with va ; (try (simpl in * ; tauto)).
  - 
    apply epge_bot in H0. congruence.
  - apply epge_bot in H0. congruence.
  - apply epge_bot in H0. subst.
    econstructor.
  - apply epge_top in H ; subst.    
    constructor.
Qed.
*)

Lemma is_uns_unsigned :
  forall n i,
    is_uns n i -> 
    is_unsigned n (Eval (Vint i)).
Proof.
  unfold is_unsigned.
  intros. exists i.
  simpl ; intuition.
Qed.

Lemma is_sgn_signed :
  forall n i,
    is_sgn n i -> 
    is_signed n (Eval (Vint i)).
Proof.
  unfold is_signed.
  intros. exists i.
  simpl ; intuition.
Qed.

Lemma is_constant_unsigned :
  forall n i v, 
    is_uns n i -> 
    is_constant (Vint i) v -> 
    is_unsigned n v.
Proof.
  intros.
  
  unfold is_constant in H0.
  rewrite <- H0.
  eapply is_uns_unsigned ; eauto.
Qed.

Lemma is_sgn_unsigned :
  forall n i,
    is_sgn n i -> 
    is_signed n (Eval (Vint i)).
Proof.
  unfold is_signed.
  intros. exists i.
  simpl ; intuition.
Qed.

Lemma is_constant_signed :
  forall n i v, 
    is_sgn n i -> 
    is_constant (Vint i) v -> 
    is_signed n v.
Proof.
  intros.
  unfold is_constant in H0.
  rewrite <- H0.
  eapply is_sgn_signed ; eauto.
Qed.

Hint Resolve is_constant_unsigned is_constant_signed : va.

Inductive valid_constant : val -> Prop  :=
| vc_Vint    : forall i, valid_constant (Vint i)
| vc_Vlong   : forall l, valid_constant (Vlong l)
| vc_Vfloat  : forall f, valid_constant (Vfloat f)
| vc_Vsingle : forall s, valid_constant (Vsingle s)
| vc_Vptr    : forall b o, bc b <> BCinvalid -> valid_constant (Vptr b o).

Lemma is_constant_epmatch_top :
  forall c v, 
    valid_constant c -> 
    is_constant c v -> 
    epmatch v Ptop.
Proof.
  intros.
  unfold is_constant in *.
  rewrite <- H0.
  constructor ; auto.
  apply  depends_on_blocks_appears.
  intros.
  inv H ; simpl in H1 ; congruence.
Qed.

Ltac is_constant_epmatch_top :=
  match goal with
    | H : is_constant ?C ?V |- epmatch ?V Ptop => apply is_constant_epmatch_top with (c:=C) (2:= H) ; constructor
  end.

Hint Extern 2 (epmatch _ Ptop) => is_constant_epmatch_top : va.  
Import NormaliseSpec.

Lemma is_unsigned_unsigned :
  forall n n' (Ti : int -> int) (Te : expr_sym -> expr_sym)
         (Hsame : forall a u e i,  Values.Val.lessdef (eSexpr a u e) (Vint i) ->
                                   Values.Val.lessdef (eSexpr a u (Te e)) (Vint (Ti i))),
    (forall i, is_uns n i -> is_uns n' (Ti i)) ->
    (forall e, is_unsigned n e -> is_unsigned n' (Te e)).
Proof.
  intros.
  unfold is_unsigned in *.
  intros.
  destruct (H0 a u); auto.
  intuition.
  exists (Ti x).
  intuition.
Qed.

Lemma is_signed_signed :
  forall n n' (Ti : int -> int) (Te : expr_sym -> expr_sym)
         (Hsame : forall a u e i,  Values.Val.lessdef (eSexpr a u e) (Vint i) ->
                                   Values.Val.lessdef (eSexpr a u (Te e)) (Vint (Ti i))),
    (forall i, is_sgn n i -> is_sgn n' (Ti i)) ->
    (forall e, is_signed n e -> is_signed n' (Te e)).
Proof.
  intros.
  unfold is_signed in *.
  intros.
  destruct (H0 a u); auto.
  intuition.
  exists (Ti x).
  intuition.
Qed.

Lemma is_unsigned_signed :
  forall n n' (Ti : int -> int) (Te : expr_sym -> expr_sym)
         (Hsame : forall a u e i,  Values.Val.lessdef (eSexpr a u e) (Vint i) ->
                                   Values.Val.lessdef (eSexpr a u (Te e)) (Vint (Ti i))),
    (forall i, is_uns n i -> is_sgn n' (Ti i)) ->
    (forall e, is_unsigned n e -> is_signed n' (Te e)).
Proof.
  intros.
  unfold is_signed,is_unsigned in *.
  intros.
  destruct (H0 a u); auto.
  intuition.
  exists (Ti x).
  intuition.
Qed.

Lemma is_unsigned_mon :
  forall n1 n2 v,
    n1 >= n2 -> 
    is_unsigned n2 v ->
    is_unsigned n1 v.
Proof.
  intros n1 n2 v Hge.
  revert v.
  apply  is_unsigned_unsigned with (Ti := fun x => x) ; auto.
  intros. eapply is_uns_mon ; eauto with va.
Qed.

Lemma is_signed_mon :
  forall n1 n2 v,
    n1 >= n2 -> 
    is_signed n2 v ->
    is_signed n1 v.
Proof.
  intros n1 n2 v Hge.
  revert v.
  apply  is_signed_signed with (Ti := fun x => x) ; auto.
  intros. eapply is_sgn_mon ; eauto with va.
Qed.

Lemma is_unsigned_signed_mon :
  forall n1 n2 i,
    n1 < n2 -> 
    is_unsigned n1 i ->
    is_signed n2 i.
Proof.
  intros n1 n2 i Hge.
  revert i.
  apply  is_unsigned_signed with (Ti := fun x => x) ; auto.
  intros. eapply is_uns_sgn ; eauto with va.
Qed.

Hint Resolve is_unsigned_mon is_signed_mon is_unsigned_signed_mon : va.


Lemma evmatch_ge:
  forall v x y, evge x y -> evmatch v y -> evmatch v x.
Proof.
  induction 1; intros V; inv V; 
  unfold is_bot,aptr_of_aval in *; subst;
  eauto using epmatch_ge with va ; try constructor ; eauto using epmatch_ge with va ; try omega;
  try congruence.
  - 
    unfold is_constant in H4.
    rewrite <- H4.
    destruct p ; simpl in * ; try tauto ;
    constructor; depends_prf.
  -    
    unfold is_constant in H2.
    rewrite <- H2.
    destruct p ; simpl in * ; try tauto ;
    constructor ; depends_prf.
  - 
    unfold is_constant in H2.
    rewrite <- H2.
    destruct p ; simpl in * ; try tauto ;
    constructor ; depends_prf.
  - 
    unfold is_constant in H2.
    rewrite <- H2.
    destruct p ; simpl in * ; try tauto ;
    constructor ; depends_prf.
  - 
    unfold is_constant in H2.
    rewrite <- H2.
    destruct p ; simpl in * ; try tauto ;
    constructor ; depends_prf.
  - 
    unfold is_constant in H4.
    rewrite <- H4.
    destruct p ; simpl in * ; try tauto ;
    constructor ; depends_prf.
  - 
    eapply is_unsigned_signed_mon ; eauto.
    omega.
  - inv H2.
  - inv H2.
  - inv H0.
Qed.

(** Least upper bound *)
(*
Definition vlub (v w: aval) : aval :=
  match v, w with
  | Vbot, _ => w
  | _, Vbot => v
  | I i1, I i2 =>
      if Int.eq i1 i2 then v else
      if Int.lt i1 Int.zero || Int.lt i2 Int.zero
      then sgn Pbot (Z.max (ssize i1) (ssize i2))
      else uns Pbot (Z.max (usize i1) (usize i2))
  | I i, Uns p n | Uns p n, I i =>
      if Int.lt i Int.zero
      then sgn p (Z.max (ssize i) (n + 1))
      else uns p (Z.max (usize i) n)
  | I i, Sgn p n | Sgn p n, I i =>
      sgn p (Z.max (ssize i) n)
  | I i, (Ptr p | Ifptr p) | (Ptr p | Ifptr p), I i =>
      if va_strict tt || Int.eq i Int.zero then Ifptr p else Vtop
  | Uns p1 n1, Uns p2 n2 => Uns (plub p1 p2) (Z.max n1 n2)
  | Uns p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (Z.max (n1 + 1) n2)
  | Sgn p1 n1, Uns p2 n2 => sgn (plub p1 p2) (Z.max n1 (n2 + 1))
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (Z.max n1 n2)
  | F f1, F f2 =>
      if Float.eq_dec f1 f2 then v else ntop
  | FS f1, FS f2 =>
      if Float32.eq_dec f1 f2 then v else ntop
  | L i1, L i2 =>
      if Int64.eq i1 i2 then v else ntop
  | Ptr p1, Ptr p2 => Ptr(plub p1 p2)
  | Ptr p1, Ifptr p2 => Ifptr(plub p1 p2)
  | Ifptr p1, Ptr p2 => Ifptr(plub p1 p2)
  | Ifptr p1, Ifptr p2 => Ifptr(plub p1 p2)
  | (Ptr p1 | Ifptr p1), (Uns p2 _ | Sgn p2 _) => Ifptr(plub p1 p2)
  | (Uns p1 _ | Sgn p1 _), (Ptr p2 | Ifptr p2) => Ifptr(plub p1 p2)
  | _, (Ptr p | Ifptr p) | (Ptr p | Ifptr p), _ => if va_strict tt then Ifptr p else Vtop
  | _, _ => Vtop
  end.
 *)
(*
Lemma vlub_comm:
  forall v w, vlub v w = vlub w v.
Proof.
  intros. unfold vlub; destruct v; destruct w; auto.
- rewrite Int.eq_sym. predSpec Int.eq Int.eq_spec n0 n.
  congruence.
  rewrite orb_comm. 
  destruct (Int.lt n0 Int.zero || Int.lt n Int.zero); f_equal; apply Z.max_comm. 
- f_equal. apply plub_comm. apply Z.max_comm.
- f_equal. apply plub_comm. apply Z.max_comm.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
- f_equal. apply plub_comm. apply Z.max_comm.
- f_equal. apply plub_comm. apply Z.max_comm.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
- rewrite Int64.eq_sym. predSpec Int64.eq Int64.eq_spec n0 n; congruence.
- rewrite dec_eq_sym. destruct (Float.eq_dec f0 f). congruence. auto.
- rewrite dec_eq_sym. destruct (Float32.eq_dec f0 f). congruence. auto.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
Qed.
 *)

Definition evlub (v w: aval) : aval :=
  match v, w with
  | I i1, I i2 =>
      if Int.eq i1 i2 then v else
      if Int.lt i1 Int.zero || Int.lt i2 Int.zero
      then sgn Pcst (Z.max (ssize i1) (ssize i2))
      else uns Pcst (Z.max (usize i1) (usize i2))
  | I i, Uns p n | Uns p n, I i =>
      if Int.lt i Int.zero
      then sgn (eplub  p Pcst) (Z.max (ssize i) (n + 1))
      else uns (eplub  p Pcst) (Z.max (usize i) n)
  | I i, Sgn p n | Sgn p n, I i =>
      sgn (eplub p  Pcst) (Z.max (ssize i) n)
  | I i, Ptr p | Ptr p , I i => Ptr (eplub p Pcst)
  | Uns p1 n1, Uns p2 n2 => Uns (eplub p1 p2) (Z.max n1 n2)
  | Uns p1 n1, Sgn p2 n2 => sgn (eplub p1 p2) (Z.max (n1 + 1) n2)
  | Sgn p1 n1, Uns p2 n2 => sgn (eplub p1 p2) (Z.max n1 (n2 + 1))
  | Sgn p1 n1, Sgn p2 n2 => sgn (eplub p1 p2) (Z.max n1 n2)
  | F f1, F f2 =>
      if Float.eq_dec f1 f2 then v else Vtop
  | FS f1, FS f2 =>
      if Float32.eq_dec f1 f2 then v else Vtop
  | L i1, L i2 =>
      if Int64.eq i1 i2 then v else Vtop
  | Ptr p1, Ptr p2 => Ptr(eplub p1 p2)
  | Ptr p1 , (Uns p2 _ | Sgn p2 _) => Ptr(eplub p1 p2)
  | (Uns p1 _ | Sgn p1 _), (Ptr p2 ) => Ptr(eplub p1 p2)
  | _, (Ptr p ) | (Ptr p ), _ =>  Vtop
  | _, _ => Vtop
  end.

Lemma evlub_comm:
  forall v w, evlub v w = evlub w v.
Proof.
  intros. unfold evlub; destruct v; destruct w; auto.
- rewrite Int.eq_sym. predSpec Int.eq Int.eq_spec n0 n.
  congruence.
  rewrite orb_comm. 
  destruct (Int.lt n0 Int.zero || Int.lt n Int.zero); f_equal; apply Z.max_comm. 
- f_equal. apply eplub_comm. apply Z.max_comm.
- f_equal. apply eplub_comm. apply Z.max_comm.
- f_equal; apply eplub_comm.
- rewrite eplub_comm. rewrite Z.max_comm. reflexivity.
- rewrite eplub_comm. rewrite Z.max_comm. reflexivity.
- f_equal. apply eplub_comm. 
- rewrite Int64.eq_sym. predSpec Int64.eq Int64.eq_spec n0 n; congruence.
- rewrite dec_eq_sym. destruct (Float.eq_dec f0 f). congruence. auto.
- rewrite dec_eq_sym. destruct (Float32.eq_dec f0 f). congruence. auto.
- f_equal; apply eplub_comm.
- f_equal; apply eplub_comm.
- f_equal; apply eplub_comm.
Qed.



Lemma epge_refl : forall p, epge p p.
Proof.
  destruct p ; simpl ; intuition.
Qed.  

Hint Resolve epge_refl : va.


Definition is_dep (p : aptr) : Prop :=
  match p with
    | Gl _ _ | Stk _ | Pbot => False
    | _   => True
  end.

Lemma epge_poffset_Pcst :
  forall v p,
    epmatch v p -> 
    epge (poffset p) Pcst.
Proof.
  intros.
  inv H ; simpl ; constructor ; auto.
Qed.

Lemma epge_poffset : forall p, epge (poffset p) p.
Proof.
  destruct p ; simpl ; repeat constructor.
Qed.

Hint Resolve epge_poffset epge_poffset_Pcst : va.
(*
Definition is_dep_dec (p : aptr) : { is_dep p} + { ~ is_dep p}.
  destruct p ; simpl; intuition.
Qed.
*)

Lemma evge_uns_uns': forall p n, evge (uns p n) (Uns p n).
Proof.
  unfold uns; intros. 
  destruct (zle n 1). constructor ; auto with va.
  destruct (zle n 7). constructor ; auto with va.
  destruct (zle n 8). constructor ; auto with va.
  destruct (zle n 15). constructor ; auto with va.
  destruct (zle n 16); auto with va.
  constructor ; auto with va.
  constructor; auto with va.
Qed.

Lemma evge_uns_i': forall p n i, 0 <= n -> is_uns n i -> epge p Pcst -> evge (uns p n) (I i).
Proof.
  intros. apply evge_trans with (Uns p n). apply evge_uns_uns'.
  constructor; auto.
Qed.


Lemma evge_sgn_sgn': forall p n, evge (sgn p n) (Sgn p n).
Proof.
  unfold sgn; intros. 
  destruct (zle n 8). constructor; auto with va. 
  destruct (zle n 16); constructor ; auto with va. 
Qed.

Lemma evge_sgn_i': forall p n i, 0 < n -> is_sgn n i -> epge p Pcst -> evge (sgn p n) (I i).
Proof.
  intros. apply evge_trans with (Sgn p n). apply evge_sgn_sgn'.
  constructor; auto with va. 
Qed.


Hint Resolve evge_uns_uns' evge_uns_i' evge_sgn_sgn' evge_sgn_i' : va.

Lemma usize_pos: forall n, 0 <= usize n.
Proof.
  unfold usize; intros. generalize (Int.size_range n); omega.
Qed.

Lemma ssize_pos: forall n, 0 < ssize n.
Proof.
  unfold ssize; intros. 
  generalize (Int.size_range (if Int.lt n Int.zero then Int.not n else n)); omega.
Qed.
(*
Lemma vge_lub_l:
  forall x y, vge (vlub x y) x.
Proof.
  assert (IFSTRICT: forall (cond: bool) x1 x2 y, vge x1 y -> vge x2 y -> vge (if cond then x1 else x2) y).
  { destruct cond; auto with va. }
  unfold vlub; destruct x, y; eauto using pge_lub_l with va.
- predSpec Int.eq Int.eq_spec n n0. auto with va.
  destruct (Int.lt n Int.zero || Int.lt n0 Int.zero).
  apply vge_sgn_i'. generalize (ssize_pos n); xomega. eauto with va. 
  apply vge_uns_i'. generalize (usize_pos n); xomega. eauto with va. 
- destruct (Int.lt n Int.zero).
  apply vge_sgn_i'. generalize (ssize_pos n); xomega. eauto with va. 
  apply vge_uns_i'. generalize (usize_pos n); xomega. eauto with va. 
- apply vge_sgn_i'. generalize (ssize_pos n); xomega. eauto with va. 
- destruct (Int.lt n0 Int.zero).
  eapply vge_trans. apply vge_sgn_sgn'.
  apply vge_trans with (Sgn p (n + 1)); eauto with va.
  eapply vge_trans. apply vge_uns_uns'. eauto with va. 
- eapply vge_trans. apply vge_sgn_sgn'.
  apply vge_trans with (Sgn p (n + 1)); eauto using pge_lub_l with va.
- eapply vge_trans. apply vge_sgn_sgn'. eauto with va.
- eapply vge_trans. apply vge_sgn_sgn'. eauto using pge_lub_l with va.
- eapply vge_trans. apply vge_sgn_sgn'. eauto using pge_lub_l with va.
- destruct (Int64.eq n n0); constructor.
- destruct (Float.eq_dec f f0); constructor.
- destruct (Float32.eq_dec f f0); constructor.
Qed.

Lemma vge_lub_r:
  forall x y, vge (vlub x y) y.
Proof.
  intros. rewrite vlub_comm. apply vge_lub_l. 
Qed.

Lemma vmatch_lub_l:
  forall v x y, vmatch v x -> vmatch v (vlub x y).
Proof.
  intros. eapply vmatch_ge; eauto. apply vge_lub_l.
Qed.

Lemma vmatch_lub_r:
  forall v x y, vmatch v y -> vmatch v (vlub x y).
Proof.
  intros. rewrite vlub_comm. apply vmatch_lub_l; auto.
Qed.
*)
Definition Vbot := Ptr Pbot.

Hint Constructors evmatch : va.

Lemma eplub_bot : 
      forall p q, eplub p q = Pbot -> p = Pbot /\ q = Pbot.
Proof.
 destruct p, q ; simpl ; intuition try congruence;
 try  destruct (ident_eq id id0) ; 
 try  destruct (Int.eq_dec ofs ofs0) ; try congruence.
Qed.

Lemma evge_lub_l:
  forall x y, evge (evlub x y) x.
Proof.
  assert (IFSTRICT: forall (cond: bool) x1 x2 y, evge x1 y -> evge x2 y -> evge (if cond then x1 else x2) y).
  { destruct cond; auto with va. }
  unfold evlub; destruct x, y; simpl ; try (constructor ; eauto using epge_lub_l with va;  try reflexivity;fail).
  - predSpec Int.eq Int.eq_spec n n0. apply evge_refl.
  destruct (Int.lt n Int.zero || Int.lt n0 Int.zero).
  apply evge_sgn_i'. generalize (ssize_pos n); xomega. eauto with va. 
  reflexivity.
  apply evge_uns_i'. generalize (usize_pos n); xomega. eauto with va. 
  reflexivity.
  - destruct (Int.lt n Int.zero).
  apply evge_sgn_i'. generalize (ssize_pos n); xomega. eauto with va. 
  apply epge_lub_r.
  apply evge_uns_i'. generalize (usize_pos n); xomega. eauto with va. 
  apply epge_lub_r.
  - apply evge_sgn_i'. generalize (ssize_pos n); xomega. eauto with va. 
    apply epge_lub_r.
  - constructor.
    apply epge_lub_r.
  - 
    destruct (Int.lt n0 Int.zero).
  eapply evge_trans. apply evge_sgn_sgn'.
  apply evge_trans with (Sgn p (n + 1)); constructor ;  eauto with va.
  apply epge_lub_l.
  eapply evge_trans. apply evge_uns_uns'.  constructor ; eauto with va. 
  apply epge_lub_l.
  -  eapply evge_trans. apply evge_sgn_sgn'.
    apply evge_trans with (Sgn p (n + 1)); constructor ; eauto using epge_lub_l with va.
  -   
    eapply evge_trans. apply evge_sgn_sgn'. constructor ; eauto with va.
    apply epge_lub_l.
  - eapply evge_trans. apply evge_sgn_sgn'. constructor ; eauto using epge_lub_l with va.
  - eapply evge_trans. apply evge_sgn_sgn'. constructor ; eauto using epge_lub_l with va.
  - destruct (Int64.eq n n0); constructor.
    constructor.
  - destruct (Float.eq_dec f f0); repeat constructor.
  - destruct (Float32.eq_dec f f0); repeat constructor.
Qed.


Lemma evmatch_lub_l:
  forall v x y, evmatch v x -> evmatch v (evlub x y).
Proof.
  intros. eapply evmatch_ge; eauto. apply evge_lub_l.
Qed.

Lemma evmatch_lub_r:
  forall v x y, evmatch v y -> evmatch v (evlub x y).
Proof.
  intros. rewrite evlub_comm. apply evmatch_lub_l; auto.
Qed.

(** In the CompCert semantics, a memory load or store succeeds only
  if the address is a pointer value.  Hence, in strict mode,
  [aptr_of_aval x] returns [Pbot] (no pointer value) if [x]
  denotes a number or [Vundef].  However, in real code, memory
  addresses are sometimes synthesized from integers, e.g. an absolute
  address for a hardware device.  It is a reasonable assumption
  that these absolute addresses do not point within the stack block,
  however.  Therefore, in relaxed mode, [aptr_of_aval x] returns
  [Nonstack] (any pointer outside the stack) when [x] denotes a number. *)

Definition is_bot_bool (v : aval) :=
 match aptr_of_aval v with
 | Pbot => true
 |  _   => false
end.

Definition evge_bool (v w : aval) :  bool :=
  match v , w with
    | I i , I j  => if Int.eq_dec i j then true else false
    | L l , L l' => if Int64.eq_dec l l' then true else false
    | F f , F f' => if Float.eq_dec f f' then true else false
    | Ptr p , Ptr q => ege_bool p q
    | Uns p n, I i  => Int.eq_dec (Int.zero_ext n i) i && zle 0 n && epincl Pcst p 
    | Sgn p n, I i => Int.eq_dec (Int.sign_ext n i) i && zlt 0 n && epincl Pcst p
    | Uns q m , Uns p n  => zle n m && epincl p q
    | Sgn q m, Uns p n  => zlt n m && epincl p q 
    | Sgn q m , Sgn p n  => zle n m && epincl p q
    |   _     ,  x       => is_bot_bool x
  end.

Lemma evge_bool_ge: forall v w, evge_bool w v = true -> evge w v.
Proof.
  unfold evge_bool; destruct v; destruct w; unfold is_bot_bool,aptr_of_aval in *;
  intros; try discriminate; try InvBooleans; try subst; try (constructor ; auto using epincl_ge with va ; fail); try (destruct p ; try congruence; apply evge_bot; reflexivity).
  - 
    destruct (Int.eq_dec n0 n) ; try congruence; subst ; constructor.
  - constructor; auto.
    rewrite is_uns_zero_ext; auto. apply epincl_ge; auto.
  - constructor ; auto.
     rewrite is_sgn_sign_ext; auto. apply epincl_ge ; auto.
  - destruct (Int64.eq_dec n0 n) ; try congruence; subst ; constructor.
  -  destruct (Float.eq_dec f0 f) ; try congruence; subst ; constructor.
Qed.

Definition vincl (v w: aval) : bool := evge_bool w v.

Lemma evincl_ge: forall v w, vincl v w = true -> evge w v.
Proof.
  unfold vincl. apply evge_bool_ge.
Qed.

(** Loading constants *)

Definition genv_match (ge: genv) : Prop :=
  (forall id b, Genv.find_symbol ge id = Some b <-> bc b = BCglob id)
/\(forall b, Plt b (Genv.genv_next ge) -> bc b <> BCinvalid /\ bc b <> BCstack).

Lemma symbol_address_sound:
  forall ge id ofs b e,
    genv_match ge ->
    Genv.symbol_address ge id ofs =  (Vptr b ofs) -> 
    is_pointer b ofs e -> 
    evmatch e (Ptr (Gl id ofs)).
Proof.
  intros. unfold Genv.symbol_address in H0. destruct (Genv.find_symbol ge id) as [b'|] eqn:F. 
  -
    inv H0.
    rew_cst H1.
    constructor.
    econstructor.
    apply H;eauto.
    repeat intro. reflexivity.
  -  discriminate.
Qed.

Lemma vmatch_ptr_gl:
  forall ge v id ofs,
  genv_match ge ->
  evmatch v (Ptr (Gl id ofs)) ->
  Val.lessdef v (Eval (Genv.symbol_address ge id ofs)).
Proof.
  intros. unfold Genv.symbol_address. inv H0. 
  - inv H3. replace (Genv.find_symbol ge id) with (Some b).
    repeat intro.
    simpl. unfold is_pointer in H5.
    rewrite <- H5.
    simpl. constructor.
    symmetry. apply H; auto.
Qed.

Lemma vmatch_ptr_stk:
  forall v ofs sp,
  evmatch v (Ptr(Stk ofs)) ->
  bc sp = BCstack ->
  Val.lessdef v (Eval (Vptr sp ofs)).
Proof.
  intros. inv H. 
  - inv H3.
    assert (b = sp) by  (eapply bc_stack; eauto).
    subst.
    unfold is_pointer in H4.
    unfold Val.lessdef.
    simpl.
    intros.
    erewrite <- H4; eauto.
Qed.

Lemma is_pointer_eval :
  forall  b ofs b' ofs',
    is_pointer  b ofs   (Eval (Vptr b' ofs')) ->
    b = b' /\ ofs = ofs'.
Proof.
  intros.
  unfold is_pointer in H.
  unfold same_eval in H.
  generalize (H (fun _ => Int.zero) (fun  _ _ => Byte.zero)).
  simpl.
  intros. apply inj_vint in H0.
  repeat rewrite Int.add_zero_l in H0. subst.
  split ; auto.
  generalize (H (fun (b':block) => if eq_block b b' then Int.one else Int.zero) (fun  _ _ => Byte.zero)).
  simpl.
  intros.  apply inj_vint in H0.
  destruct (eq_block b b') ; auto.
  destruct (eq_block b b) ; try congruence.
  generalize (add_one_zero_diff ofs' ofs') ; intuition.
  repeat rewrite Int.add_zero_l in *. intuition.
Qed.


Lemma aptr_of_aval_stack:
  forall b o r av i,
    aptr_of_aval av = Stk i ->
    evmatch r av ->
    is_pointer b o r -> bc b = BCstack /\ i = o.
Proof.
  intros.
  rew_cst H1. clear H1.
  inv H0 ; simpl in H ; try congruence ; subst.
  - inv H3.
    apply is_pointer_eval in H5.
    intuition.
  - inv H3.
    apply is_pointer_eval in H5.
    intuition.
  - inv H1.
    apply is_pointer_eval in H3.
    intuition.
Qed.



(** Generic operations that just do constant propagation. *)



Definition unop_int (sem: int -> int) (x: aval) :=
  match x with I n => I (sem n) | _ => ntop1 x end.

Hint Resolve poffset_sound : va.

Lemma aptr_of_aval_sound :
  forall v x,
    evmatch v x -> 
   epmatch v (aptr_of_aval x).
Proof.
  intros.
  inv H; simpl ; try constructor ; depends_prf.
Qed.  



Hint Resolve aptr_of_aval : va.



Lemma epmatch_cst_Pcst :
  forall v, 
    val_no_ptr v = true -> 
    epmatch (Eval v) Pcst.
Proof.
  intros.
  destruct v ; simpl in * ; constructor ; red ; intros ; simpl ; depends_prf.
  congruence.
Qed.



Lemma evmatch_unop_ntop1 :
  forall o s v x, 
    evmatch v x -> 
    evmatch (Eunop o s v) (ntop1 x).
Proof.
    unfold ntop1 in *.
    intros.
    unfold provenance in *.
    constructor.
    inv H ; simpl ; try constructor ; depends_prf.
    - 
      inv H2 ; simpl ; try constructor ; depends_prf; congruence. 
    - 
    inv H2 ; simpl ; try constructor ; depends_prf; congruence.
    - 
    inv H0 ; simpl ; try constructor ; depends_prf; congruence.
Qed.

Lemma epmatch_binop_lub :
  forall o s1 s2 v w x y,
    epmatch v x ->
    epmatch w y -> 
    epmatch (Ebinop o s1 s2 v w) (eplub (poffset x) (poffset y)).
Proof.
  intros.
  apply poffset_sound in H.
  apply poffset_sound in H0.
  apply epmatch_lub_l with (q := poffset y) in H.
  apply epmatch_lub_l with (q := poffset x) in H0.
  rewrite eplub_comm in H0.
  inv H ; inv H0 ; try constructor; try congruence; depends_prf ; try congruence.
  -
    rewrite <- H1 in H.
    destruct x ; destruct y ; simpl in H1; try discriminate;
    destruct (ident_eq id1 id2) ; congruence.
  - 
    destruct x ; destruct y ; simpl in H1; try discriminate;
    destruct (ident_eq id id0) ; congruence.
Qed.

Lemma evmatch_ntop1 :
  forall T v x, 
    is_unop_trans T -> 
    (evmatch v x) -> 
    evmatch (T v) (ntop1 x).
Proof.
  induction 1.
  - unfold ntop1.
    apply evmatch_ge.
    unfold provenance.
    destruct x ; simpl ; repeat  constructor ; eauto with va.
  - 
    intros.
    unfold ntop1.
    unfold provenance.
    constructor.
    apply epmatch_ge with (q:= Pcst).
    inv H0 ; simpl ; eauto with va.
    constructor.
    destruct v0 ; simpl ; depends_prf.
    simpl in H ; congruence.
  - 
    intros.
    unfold ntop1.
    unfold provenance.
    constructor.
    apply epmatch_ge with (q:= Pcst).
    inv H ; simpl ; eauto with va.
    constructor.
    depends_prf.
    repeat intro.
    reflexivity.
  - 
    intros.
    specialize  (IHis_unop_trans H0).
    revert IHis_unop_trans.
    generalize (f v).
    intros.
    unfold ntop1 in *.
    inv IHis_unop_trans.
    constructor.
    revert H3.
    unfold provenance in *.
    generalize (aptr_of_aval x).
    intros.
    destruct a ; inv H3 ; simpl ; repeat constructor ; depends_prf.
  - 
    intros.
    specialize  (IHis_unop_trans1 H1).
    specialize  (IHis_unop_trans2 H1).
    revert IHis_unop_trans1 IHis_unop_trans2.
    generalize (f1 v) (f2 v).
    unfold ntop1 in *.
    intros.
    constructor.
    inv IHis_unop_trans1.
    inv IHis_unop_trans2.
    unfold provenance in *.
    revert H4 H5.
    generalize (aptr_of_aval x).
    intros.
    destruct a ; inv H4 ; inv H5 ; repeat constructor; depends_prf.
Qed.


Lemma eplub_poffset :
  forall x y,
    eplub (poffset x) (poffset y) =
    poffset (eplub x y).
Proof.
  destruct x ; destruct y ; simpl ; auto; intros;
  repeat case_match ; simpl ; auto.
  congruence.
Qed.
  
Lemma poffset_idem :
  forall x, poffset (poffset x) = poffset x.
Proof.
  destruct x ; try reflexivity.
Qed.

Lemma eplub_idem : forall x, eplub x x = x.
Proof.
  destruct x ; try reflexivity; simpl;
    repeat case_match ; congruence.
Qed.


Lemma epmatch_poffset :
  forall v p T
         (HT : is_unop_trans T)
         (HM : epmatch v p),
    epmatch (T v) (poffset p).
Proof.
  induction 1.
  - apply poffset_sound.
  - 
    intros.
    apply epmatch_ge with (q:= Pcst).
    inv HM ; simpl ; eauto with va.
    constructor.
    destruct v0 ; simpl ; depends_prf.
    simpl in H ; congruence.
  - 
    intros.
    apply epmatch_ge with (q:= Pcst).
    inv HM ; simpl ; eauto with va.
    constructor.
    depends_prf.
    repeat intro.
    reflexivity.
  - 
    intros.
    specialize  (IHHT HM).
    revert IHHT.
    generalize (f v).
    intros.
    inv IHHT ; try constructor ; depends_prf.
    destruct p ; simpl in H ; congruence.
    destruct p ; simpl in H ; congruence.
  - 
    intros.
    specialize  (IHHT1 HM).
    specialize  (IHHT2 HM).
    revert IHHT1 IHHT2.
    generalize (f1 v) (f2 v).
    intros.
    rewrite <- eplub_idem.
    rewrite <- (poffset_idem p).
    apply epmatch_binop_lub; auto.
Qed.

Lemma eunop_int_sound:
  forall sem Esem e x
         (HSem : is_unop_trans Esem),
    (forall a u i, eSexpr a u e = Vint i -> eSexpr a u (Esem e) = Vint (sem i)) ->  
    evmatch e x ->
    evmatch (Esem e) (unop_int sem x).
Proof.
  intros.
  unfold unop_int.
  destruct x ; auto; try apply evmatch_ntop1 ; auto.
  - 
    inv H0. constructor.
    unfold is_constant in *.
    repeat intro.
    simpl.
    symmetry. apply H.
    erewrite <-H3 ; eauto. 
Qed.

Definition binop_int (sem: int -> int -> int) (x y: aval) :=
  match x, y with I n, I m => I (sem n m) | _, _ => ntop2 x y end.


  


Lemma evmatch_binop_ntop2 :
  forall v w x y o s1 s2, 
    (evmatch v x) -> 
    (evmatch w y) -> 
    evmatch (Ebinop o s1 s2 v w) (ntop2 x y).
Proof.
  intros.
  unfold ntop2.
  constructor.
  unfold provenance.
  apply epmatch_binop_lub.
  clear H0.
  inv H ; simpl ; auto;  constructor ; depends_prf.
  inv H0 ; simpl ; auto;  constructor ; depends_prf.
Qed.  



Lemma evmatch_ntop2 :
  forall T v w x y
  (HT : is_binop_trans T), 
    (evmatch v x) -> 
    (evmatch w y) -> 
    evmatch (T v w) (ntop2 x y).
Proof.
  induction 1.
  - unfold ntop2.
    intros.
    unfold provenance.
    apply aptr_of_aval_sound in H.
    constructor.
    apply epmatch_ge with (q:= (poffset (aptr_of_aval x))).
    apply epge_lub_l.
    apply poffset_sound ; auto.
  - 
    unfold ntop2.
    intros.
    unfold provenance.
    apply aptr_of_aval_sound in H0.
    constructor.
    apply epmatch_ge with (q:= (poffset (aptr_of_aval y))).
    apply epge_lub_r.
    apply poffset_sound ; auto.
  - 
    intros.
    constructor.
    unfold provenance.
    apply epmatch_lub_r.
    apply epmatch_ge with (q:= Pcst).
    eapply epge_poffset_Pcst ; eauto with va.
    apply aptr_of_aval_sound ; eauto.
    apply epmatch_cst_Pcst ; auto.
  - 
    intros.
    unfold ntop2.
    unfold provenance.
    constructor.
    apply epmatch_lub_r.
    apply epmatch_ge with (q:= Pcst).
    +
    eapply epge_poffset_Pcst ; eauto with va.
    apply aptr_of_aval_sound ; eauto.
    +
    constructor. repeat intro ; reflexivity.
  - 
    intros.
    specialize (IHHT H H0).
    apply evmatch_unop_ntop1 with (o:=o) (s:=s) in IHHT.
    eapply evmatch_ge ; eauto.
    unfold ntop2,ntop1.
    constructor.
    unfold provenance.
    unfold aptr_of_aval at 3.
    rewrite eplub_poffset.
    rewrite poffset_idem.
    apply epge_refl.
  - 
    intros.
    specialize (IHHT1 H H0).
    specialize (IHHT2 H H0).
    apply evmatch_ge  with (y:= ntop2 (ntop2 x y) (ntop2 x y)).
    unfold ntop2.
    unfold provenance.
    constructor.
    rewrite eplub_poffset.
    unfold aptr_of_aval at 3.
    unfold aptr_of_aval at 5.
    rewrite poffset_idem.
    rewrite eplub_poffset.
    rewrite eplub_idem.
    apply epge_refl.
    apply evmatch_binop_ntop2; auto.
Qed.


Lemma ebinop_int_sound:
  forall sem Esem e1 e2 x y
         (HSem : is_binop_trans Esem)
  ,
    (forall a u i j, eSexpr a u e1 = Vint i ->
                   eSexpr a u e2 = Vint j -> 
                   eSexpr a u (Esem e1 e2) = Vint (sem i j)) ->  
    evmatch e1 x ->
    evmatch e2 y -> 
    evmatch (Esem e1 e2) (binop_int sem x y).
Proof.
  intros.
  unfold binop_int.
  destruct x ; auto; try apply evmatch_ntop2; auto.
  - 
    destruct y ;  try apply evmatch_ntop2 ; auto.
    inv H0 ; inv H1.
    unfold is_constant in *.
    repeat intro.
    simpl.
    constructor.
    unfold is_constant in *.
    repeat intro.
    symmetry. apply H.
    erewrite <- H4 ; eauto. 
    erewrite <- H3 ; eauto.
Qed.

(*
Lemma binop_int_sound:
  forall sem v x w y,
  vmatch v x -> vmatch w y ->
  vmatch (match v, w with Vint i, Vint j => Vint(sem i j) | _, _ => Vundef end) (binop_int sem x y).
Proof.
  intros. unfold binop_int; inv H; auto with va; inv H0; auto with va.
Qed.
*)

Definition unop_float (sem: float -> float) (x: aval) :=
  match x with F n => F (sem n) | _ => ntop1 x end.

(*
Lemma unop_float_sound:
  forall sem v x,
  vmatch v x ->
  vmatch (match v with Vfloat i => Vfloat(sem i) | _ => Vundef end) (unop_float sem x).
Proof.
  intros. unfold unop_float; inv H; auto with va.
Qed.
*)

Lemma eunop_float_sound:
  forall sem Esem e x
         (HSem : is_unop_trans Esem),
    (forall a u i, eSexpr a u e = Vfloat i -> eSexpr a u (Esem e) = Vfloat (sem i)) ->  
    evmatch e x ->
    evmatch (Esem e) (unop_float sem x).
Proof.
  intros.
  unfold unop_float.
  destruct x ; auto; try apply evmatch_ntop1 ; auto.
  - 
    inv H0. constructor.
    unfold is_constant in *.
    repeat intro.
    simpl.
    symmetry. apply H.
    erewrite <- H3 ; eauto.
Qed.

Definition binop_float (sem: float -> float -> float) (x y: aval) :=
  match x, y with F n, F m => F (sem n m) | _, _ => ntop2 x y end.


Lemma ebinop_float_sound:
  forall sem Esem e1 e2 x y
         (HSem : is_binop_trans Esem)
  ,
    (forall a u i j, eSexpr a u e1 = Vfloat i ->
                   eSexpr a u e2 = Vfloat j -> 
                   eSexpr a u (Esem e1 e2) = Vfloat (sem i j)) ->  
    evmatch e1 x ->
    evmatch e2 y -> 
    evmatch (Esem e1 e2) (binop_float sem x y).
Proof.
  intros.
  unfold binop_float.
  specialize (evmatch_ntop2 _ _ _ _ _ HSem H0 H1).
  destruct x ; auto.
  destruct y ; auto.
  - 
    inv H0 ; inv H1  ; constructor; auto.
    unfold is_constant in *.
    repeat intro.
    simpl.
    symmetry. apply H.
    erewrite <- H4 ; eauto.
    erewrite <- H3 ; eauto.
Qed.

(*Lemma binop_float_sound:
  forall sem v x w y,
  vmatch v x -> vmatch w y ->
  vmatch (match v, w with Vfloat i, Vfloat j => Vfloat(sem i j) | _, _ => Vundef end) (binop_float sem x y).
Proof.
  intros. unfold binop_float; inv H; auto with va; inv H0; auto with va.
Qed.
*)

Definition unop_single (sem: float32 -> float32) (x: aval) :=
  match x with FS n => FS (sem n) | _ => ntop1 x end.

Lemma eunop_single_sound:
  forall sem Esem e x
         (HSem : is_unop_trans Esem),
    (forall a u i, eSexpr a u e = Vsingle i -> eSexpr a u (Esem e) = Vsingle (sem i)) ->  
    evmatch e x ->
    evmatch (Esem e) (unop_single sem x).
Proof.
  intros.
  unfold unop_single.
  destruct x ; auto; try apply evmatch_ntop1 ; auto.
  - 
    inv H0. constructor.
    unfold is_constant in *.
    repeat intro.
    simpl.
    symmetry. apply H.
    erewrite <- H3 ; eauto.
Qed.

(*
Lemma unop_single_sound:
  forall sem v x,
  vmatch v x ->
  vmatch (match v with Vsingle i => Vsingle(sem i) | _ => Vundef end) (unop_single sem x).
Proof.
  intros. unfold unop_single; inv H; auto with va.
Qed.
 *)

Definition binop_single (sem: float32 -> float32 -> float32) (x y: aval) :=
  match x, y with FS n, FS m => FS (sem n m) | _, _ => ntop2 x y end.

Lemma ebinop_single_sound:
  forall sem Esem e1 e2 x y
         (HSem : is_binop_trans Esem)
  ,
    (forall a u i j, eSexpr a u e1 = Vsingle i ->
                   eSexpr a u e2 = Vsingle j -> 
                   eSexpr a u (Esem e1 e2) = Vsingle (sem i j)) ->  
    evmatch e1 x ->
    evmatch e2 y -> 
    evmatch (Esem e1 e2) (binop_single sem x y).
Proof.
  intros.
  unfold binop_single.
  specialize (evmatch_ntop2 _ _ _ _ _ HSem H0 H1).
  destruct x ; auto. destruct y ; auto.
  - 
    inv H0 ; inv H1 ; constructor; auto.
    unfold is_constant in *.
    repeat intro.
    simpl.
    symmetry. apply H.
    erewrite <- H4 ; eauto.
    erewrite <- H3 ; eauto.
Qed.

(*
Lemma binop_single_sound:
  forall sem v x w y,
  vmatch v x -> vmatch w y ->
  vmatch (match v, w with Vsingle i, Vsingle j => Vsingle(sem i j) | _, _ => Vundef end) (binop_single sem x y).
Proof.
  intros. unfold binop_single; inv H; auto with va; inv H0; auto with va.
Qed.
 *)




  
(** Logical operations *)

Definition shl (v w: aval) :=
  match w with
  | I amount =>
      if Int.ltu amount Int.iwordsize then
        match v with
        | I i => I (Int.shl i amount)
        | Uns p n => uns (poffset p) (n + Int.unsigned amount)
        | Sgn p n => sgn (poffset p) (n + Int.unsigned amount)
        | _ => ntop1 v
        end
      else ntop1 v
  | _ => ntop2 v w
  end.

Lemma evmatch_uns':
  forall p e n, is_unsigned (Zmax 0 n) e -> epmatch e p -> evmatch e (uns p n).
Proof.
  intros.
  assert (A: forall n', n' >= 0 -> n' >= n -> is_unsigned n' e).
  {
    intros.
    assert (n' >= Z.max 0 n) by auto with va.
    eapply is_unsigned_mon; eauto. 
  }
  unfold uns. 
  destruct (zle n 1). auto with va. 
  destruct (zle n 7). auto with va.
  destruct (zle n 8). auto with va.
  destruct (zle n 15). auto with va.
  destruct (zle n 16). auto with va.
  constructor ; auto.
Qed.

Lemma evmatch_uns:
  forall p e n, is_unsigned n e -> epmatch e p -> evmatch e (uns p n).
Proof.
  intros. apply evmatch_uns';auto.
  eapply is_unsigned_mon ; eauto with va.
  auto with va.
Qed.

(*Lemma vmatch_uns_undef: forall p n, vmatch Vundef (uns p n).
Proof.
  intros. unfold uns. 
  destruct (zle n 1). auto with va. 
  destruct (zle n 7). auto with va.
  destruct (zle n 8). auto with va.
  destruct (zle n 15). auto with va.
  destruct (zle n 16); auto with va.
Qed.
 *)
Lemma evmatch_sgn':
  forall p e n, is_signed (Zmax 1 n) e -> epmatch e p -> evmatch e (sgn p n).
Proof.
  intros.
  assert (A: forall n', n' >= 1 -> n' >= n -> is_signed n' e).
  {
    intros.
    eapply is_signed_mon with (n2 := Z.max 1 n); eauto.
    eauto with va.
  }
  unfold sgn. 
  destruct (zle n 8). constructor; eauto with va.
  destruct (zle n 16); constructor ; eauto with va.
Qed.

Lemma vmatch_sgn:
  forall p e n, is_signed n e -> epmatch e p -> evmatch e (sgn p n).
Proof.
  intros. apply evmatch_sgn'; auto with va. 
  eapply is_signed_mon ; eauto.
  zify; omega.
Qed.

(*
Lemma vmatch_sgn_undef: forall p n, vmatch Vundef (sgn p n).
Proof.
  intros. unfold sgn.
  destruct (zle n 8). auto with va.
  destruct (zle n 16); auto with va.
Qed.
*)

Lemma inv_lessdef : forall x y, Values.Val.lessdef x y ->
                                x = Vundef \/ x = y.
Proof.
  intros.
  inv H ; intuition.
Qed.
  

Ltac lessdef :=
  match goal with
    | H : Values.Val.lessdef ?X ?V |-
      Values.Val.lessdef ?Y ?W =>
      match Y with
        | context[X] => apply inv_lessdef in H ;
            let LD := fresh "LD" in
            destruct H as [LD | LD] ; rewrite LD in * ; simpl ; try constructor
      end
  end.


Lemma shl_sound: 
  forall v w x y, evmatch v x -> evmatch w y -> evmatch (Val.shl v w) (shl x y).
Proof.
  intros.
  assert (DEFAULT: evmatch (Val.shl v w) (ntop2 x y)). 
  {
    apply evmatch_ntop2 ; auto.
    repeat constructor ; auto.
  }
  destruct y; auto. simpl. inv H0. unfold Val.shl.
  destruct (Int.ltu n Int.iwordsize) eqn:LTU; auto.
  -
  exploit Int.ltu_inv; eauto. intros RANGE.
  inv H; auto with va.
  +
  constructor.
  unfold is_constant in H3.
  rewrite <- H3.
  unfold is_constant in H0.
  rewrite <- H0.
  repeat intro. simpl.
  rewrite LTU. reflexivity.
  + 
    apply evmatch_uns'.
    * 
      unfold is_constant in H3. rewrite <- H3.
      revert H1.
      apply is_unsigned_unsigned with
      (Ti := fun v => Int.shl v n)
      (Te := (fun v => (Ebinop OpShl Tint Tint v (Eval (Vint n))))).
      simpl. intros.
      lessdef.
      rewrite LTU. constructor.
      red ; intros. rewrite Int.bits_shl by omega.
      destruct (zlt m (Int.unsigned n)). auto. apply H; xomega.
    *
      apply epmatch_ge with (q := eplub (poffset p) (poffset Pcst)).
      inv H2 ; try (simpl ; auto ; fail).
      apply epmatch_binop_lub; auto.
      constructor.
      depends_prf.
  + 
    apply evmatch_sgn'.
    * 
      unfold is_constant in H3. rewrite <- H3.
      revert H1.
      apply is_signed_signed with
      (Ti := fun v => Int.shl v n)
      (Te := (fun v => (Ebinop OpShl Tint Tint v (Eval (Vint n))))).
      simpl. intros.
      lessdef.
      rewrite LTU. constructor.
      red ; intros. zify.
      rewrite ! Int.bits_shl by omega.
      rewrite ! zlt_false by omega.
      rewrite H by omega. symmetry. rewrite H by omega. auto.
    *
      apply epmatch_ge with (q := eplub (poffset p) (poffset Pcst)).
      inv H2 ; try (simpl ; auto ; fail).
      apply epmatch_binop_lub; auto.
      constructor.
      depends_prf.
  +
    unfold is_constant in H3.
    rewrite <- H3.
    apply evmatch_ntop1 with (T := fun v => (Ebinop OpShl Tint Tint v (Eval (Vint n)))).
    repeat constructor. constructor ; auto.
  -
    unfold is_constant in H3.
    rewrite <- H3.
    apply evmatch_ntop1 with (T := fun v => (Ebinop OpShl Tint Tint v (Eval (Vint n)))).
    repeat constructor. auto.
Qed.

(*Definition is_integer (p : aptr) : bool :=
  match p with
    | 
    |
  end
*)

Definition shru (v w: aval) :=
  match w with
  | I amount =>
      if Int.ltu amount Int.iwordsize then
        match v with
        | I i => I (Int.shru i amount)
        | Uns p n => uns (poffset p) (n - Int.unsigned amount)
        | _  => uns (provenance v) (Int.zwordsize - Int.unsigned amount)
        end
      else ntop1 v
  | _ => ntop2 v w
  end.

Lemma inj_unsigned :
  forall x y, 
    x <> y -> Int.unsigned x <> Int.unsigned y.
Proof.
  intros.
  destruct x ; destruct y ; simpl in *.
  intro.
  subst.
  assert (intrange = intrange0) by apply Axioms.proof_irr.
  congruence.
Qed.
  

Lemma is_constant_int_ptr :
  forall i b o e   ,
    is_constant (Vint i) e -> 
    is_constant (Vptr b o) e ->
False.
Proof.
  intros.
  unfold is_constant in *.
  unfold same_eval in *.
  generalize (H (fun _ => Int.zero) (fun _ _ => Byte.zero)).
  generalize (H (fun _ => Int.one) (fun _ _ => Byte.zero)).
  generalize (H0 (fun _ => Int.zero) (fun _ _ => Byte.zero)).
  generalize (H0 (fun _ => Int.one) (fun _ _ => Byte.zero)).
  simpl.
  generalize (eSexpr (fun _ => Int.zero) (fun (_ : block) (_ : int) => Byte.zero) e).
  generalize (eSexpr (fun _ => Int.one) (fun (_ : block) (_ : int) => Byte.zero) e).
  intros ; subst.
  rewrite H4 in H3.
  clear H4.
  apply inj_vint in H3.
  rewrite Int.add_zero_l in H3.
  generalize (add_one_zero_diff o o).
  intuition.
  rewrite Int.add_zero_l in H2. intuition.
Qed.  

Lemma is_constant_epmatch_epge :
  forall i e x,
    is_constant (Vint i) e ->  epmatch e x -> 
   epge x Pcst.
Proof.
  intros.
  inv H0 ; simpl ; auto.
  eapply is_constant_int_ptr ; eauto.
  eapply is_constant_int_ptr ; eauto.
Qed.  



Lemma is_constant_epmatch_Pcst :
  forall i e,
    is_constant (Vint i) e -> 
   epmatch e Pcst.
Proof.
  intros.
  rew_cst H.
  constructor.
  depends_prf.
Qed.  


Lemma eSexpr_rew :
  forall a ud e ,
    eSexpr a ud e = 
    match e with
      | Eval v               => eSval a v
      | Eundef p i           => Vint (Int.repr (Byte.unsigned (ud p i)))
      | Eunop u t e          => fun_of_unop u t (eSexpr a ud e)
      | Ebinop b t1 t2 e1 e2 => fun_of_binop b t1 t2 (eSexpr a ud e1) (eSexpr a ud e2)
    end.
Proof.
  destruct e ; auto.
Qed.  

Lemma evmatch_epge :
  forall v x,
    evmatch v x -> 
    epge (poffset (aptr_of_aval x))
         (eplub (poffset (aptr_of_aval x)) (poffset Pcst)).
Proof.
  intros.
  inv H ; try (simpl ; auto ; fail).
  simpl. inv H2 ; try (simpl ; auto ; fail).
  simpl. inv H2 ; try (simpl ; auto ; fail).
  simpl. inv H0 ; try (simpl ; auto ; fail).
Qed.  

Lemma shru_sound: 
  forall v w x y, evmatch v x -> evmatch w y -> evmatch (Val.shru v w) (shru x y).
Proof.
  intros.
  assert (DEFAULT: evmatch (Val.shru v w) (ntop2 x  y)). 
  {
    apply evmatch_ntop2 ; auto.
    repeat constructor.
  }
  destruct y; auto. inv H0. unfold shru, Val.shru in *.
  unfold is_constant in H3. rewrite <- H3 in *. clear H3.
  destruct (Int.ltu n Int.iwordsize) eqn:LTU; auto.
  exploit Int.ltu_inv; eauto. intros RANGE. change (Int.unsigned Int.iwordsize) with Int.zwordsize in RANGE.
  assert (DEFAULT2: evmatch (Val.shru v (Eval (Vint n))) (uns (provenance x) (Int.zwordsize - Int.unsigned n))).
  {
    intros. apply evmatch_uns. red; intros. 
    -
      unfold Val.shru.
      rewrite eSexpr_rew.
      case_eq (eSexpr a u v);  intros ; try (exists Int.zero ; split ; [constructor|]);
      try (red ; intros ; rewrite Int.bits_zero ; reflexivity).
      exists (Int.shru i n).
      repeat rewrite eSexpr_rew.
      split. unfold fun_of_binop. 
      unfold shr_t. simpl.
      rewrite LTU.
      constructor.
      red ; intros.
      rewrite Int.bits_shru by omega. apply zlt_false. omega.
    - 
      unfold provenance.
      unfold Val.shru.
      apply epmatch_ge with (q := eplub (poffset (aptr_of_aval x)) (poffset Pcst)).
      eapply evmatch_epge; eauto.
      apply epmatch_binop_lub; auto.
      eapply aptr_of_aval_sound ; eauto.
      constructor.
      depends_prf.
  }
  inv H; eauto with va.
  -
    constructor.
    unfold is_constant in *.
    rewrite <- H0.
    repeat intro ; simpl.
    rewrite LTU. reflexivity.
  -
    apply evmatch_uns'.
    revert H1.
    apply is_unsigned_unsigned with
    (Te := fun v => (Ebinop (OpShr SEUnsigned) Tint Tint v (Eval (Vint n))))
      (Ti := fun x => Int.shru x n).
    + simpl. intros.
      lessdef. rewrite LTU. constructor.
    +
    red; intros. zify.
    rewrite Int.bits_shru by omega.
    destruct (zlt (m + Int.unsigned n) Int.zwordsize); auto.
    apply H; omega. 
    +
      apply epmatch_ge with (q := eplub (poffset p) (poffset Pcst)).
      inv H2 ; try (simpl ; auto ; fail).
      apply epmatch_binop_lub; auto.
      constructor.
      depends_prf.
  -
    apply evmatch_ntop1 with (T := (fun v => (Ebinop (OpShr SEUnsigned) Tint Tint v (Eval (Vint n))))).
    repeat constructor. auto.
Qed.

Definition shr (v w: aval) :=
  match w with
  | I amount =>
      if Int.ltu amount Int.iwordsize then
        match v with
        | I i => I (Int.shr i amount)
        | Uns p n => sgn (poffset p) (n + 1 - Int.unsigned amount)
        | Sgn p n => sgn (poffset p) (n - Int.unsigned amount)
        | _ => sgn (provenance v) (Int.zwordsize - Int.unsigned amount)
        end
      else ntop1 v
  | _ => ntop2 v w
  end.

Lemma shr_sound: 
  forall v w x y, evmatch v x -> evmatch w y -> evmatch (Val.shr v w) (shr x y).
Proof.
  intros.
  assert (DEFAULT: evmatch (Val.shr v w) (ntop2 x y)). 
  {
    apply evmatch_ntop2 ; auto.
    repeat constructor.
  }
  destruct y; auto. inv H0. unfold shr, Val.shr.
  destruct (Int.ltu n Int.iwordsize) eqn:LTU; auto.
  exploit Int.ltu_inv; eauto. intros RANGE. change (Int.unsigned Int.iwordsize) with Int.zwordsize in RANGE.
  assert (DEFAULT2: evmatch (Val.shr v (Eval (Vint n))) (sgn (provenance x) (Int.zwordsize - Int.unsigned n))).
  {
    intros. apply vmatch_sgn. red ; intros.
    -
      unfold Val.shr.
      rewrite eSexpr_rew.
      case_eq (eSexpr a u v);  intros ; try (exists Int.zero ; split ; [constructor|]);
      try (red ; intros ; rewrite Int.bits_zero ; reflexivity).
      exists (Int.shr i n).
      repeat rewrite eSexpr_rew.
      split. unfold fun_of_binop. 
      unfold shr_t. simpl.
      rewrite LTU.
      constructor.
      red; intros. 
      rewrite ! Int.bits_shr by omega. f_equal.
      destruct (zlt (m + Int.unsigned n) Int.zwordsize);
        destruct (zlt (Int.zwordsize - 1 + Int.unsigned n) Int.zwordsize);
        omega.
    - 
      unfold provenance.
      unfold Val.shr.
      apply epmatch_ge with (q := eplub (poffset (aptr_of_aval x)) (poffset Pcst)).
      eapply evmatch_epge; eauto.
      apply epmatch_binop_lub; auto.
      eapply aptr_of_aval_sound ; eauto.
      constructor.
      depends_prf.
  }
  assert (SGN: forall p, is_signed p v -> 0 < p ->
                         evmatch (Val.shr v (Eval (Vint n))) (sgn (provenance x) (p - Int.unsigned n))).
  {
    intros. apply evmatch_sgn'.
    - 
      revert H0.
      apply is_signed_signed with (Te := fun e => (Val.shr e (Eval (Vint n)))) (Ti := fun i =>
                                                                                        Int.shr i n).
      +
      intros.
      simpl. lessdef.
      rewrite LTU. constructor.
      + 
        red; intros. zify.
        rewrite ! Int.bits_shr by omega.
        transitivity (Int.testbit i (Int.zwordsize - 1)).
        destruct (zlt (m + Int.unsigned n) Int.zwordsize).
        apply H0; omega.
        auto.
        symmetry.
        destruct (zlt (Int.zwordsize - 1 + Int.unsigned n) Int.zwordsize).
        apply H0; omega.
        auto.
    -
      unfold provenance.
      unfold Val.shr.
      apply epmatch_ge with (q := eplub (poffset (aptr_of_aval x)) (poffset Pcst)).
      eapply evmatch_epge; eauto.
      apply epmatch_binop_lub; auto.
      eapply aptr_of_aval_sound ; eauto.
      constructor.
      depends_prf.
  }
  unfold is_constant in H3.
  rewrite <- H3.
  unfold Val.shr in SGN.
  unfold provenance in SGN.
  inv H; simpl in SGN ; eauto with va.
  -
    constructor.
    unfold is_constant in *.
    rewrite <- H0.
    repeat intro ; simpl.
    rewrite LTU. reflexivity.
  - 
    apply SGN.
    revert H1.
    apply is_unsigned_signed with (Te := (fun v => v)) (Ti := fun v => v); auto.
    intros.
    eapply is_uns_sgn ; eauto.
    omega.
    omega.
  - 
    unfold is_constant in H3.
    rewrite <- H3.
    eapply evmatch_ntop1 with (T :=fun v => (Ebinop (OpShr SESigned) Tint Tint v (Eval (Vint n)))).
    repeat constructor ; auto.
    auto.
Qed.

Definition and (v w: aval) := ntop2 v w.

(*
Definition and (v w: aval) :=
  match v, w with
  | I i1, I i2 => I (Int.and i1 i2)
  | I i, Uns p n | Uns p n, I i => uns p (Z.min n (usize i))
  | I i, x | x, I i => uns (provenance x) (usize i)
  | Uns p1 n1, Uns p2 n2 => uns (plub p1 p2) (Z.min n1 n2)
  | Uns p n, _ => uns (plub p (provenance w)) n
  | _, Uns p n => uns (plub (provenance v) p) n
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (Z.max n1 n2)
  | _, _ => ntop2 v w
  end.
*)


Lemma and_sound: 
  forall v w x y, evmatch v x -> evmatch w y -> evmatch (Val.and v w) (and x y).
Proof.
  intros.
  eapply evmatch_ntop2 ; eauto.
  repeat constructor.
Qed.

(*
Lemma and_sound: 
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.and v w) (and x y).
Proof.
  assert (UNS_l: forall i j n, is_uns n i -> is_uns n (Int.and i j)).
  {
    intros; red; intros. rewrite Int.bits_and by auto. rewrite (H m) by auto. 
    apply andb_false_l.
  }
  assert (UNS_r: forall i j n, is_uns n i -> is_uns n (Int.and j i)).
  {
    intros. rewrite Int.and_commut. eauto.
  }
  assert (UNS: forall i j n m, is_uns n i -> is_uns m j -> is_uns (Z.min n m) (Int.and i j)).
  {
    intros. apply Z.min_case; auto. 
  }
  assert (SGN: forall i j n m, is_sgn n i -> is_sgn m j -> is_sgn (Z.max n m) (Int.and i j)).
  {
    intros; red; intros. rewrite ! Int.bits_and by auto with va.
    rewrite H by auto with va. rewrite H0 by auto with va. auto.
  }
  intros. unfold and, Val.and; inv H; eauto with va; inv H0; eauto with va.
Qed.
*)

Definition or (v w:aval):= ntop2 v w.

Lemma or_sound: 
  forall v w x y, evmatch v x -> evmatch w y -> evmatch (Val.or v w) (or x y).
Proof.
  intros.
  eapply evmatch_ntop2 ; eauto.
  repeat constructor.
Qed.

(*
Definition or (v w: aval) :=
  match v, w with
  | I i1, I i2 => I (Int.or i1 i2)
  | I i, Uns p n | Uns p n, I i => uns p (Z.max n (usize i))
  | Uns p1 n1, Uns p2 n2 => uns (plub p1 p2) (Z.max n1 n2)
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (Z.max n1 n2)
  | _, _ => ntop2 v w
  end.


Lemma or_sound: 
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.or v w) (or x y).
Proof.
  assert (UNS: forall i j n m, is_uns n i -> is_uns m j -> is_uns (Z.max n m) (Int.or i j)).
  {
    intros; red; intros. rewrite Int.bits_or by auto. 
    rewrite H by xomega. rewrite H0 by xomega. auto.
  }
  assert (SGN: forall i j n m, is_sgn n i -> is_sgn m j -> is_sgn (Z.max n m) (Int.or i j)).
  {
    intros; red; intros. rewrite ! Int.bits_or by xomega.
    rewrite H by xomega. rewrite H0 by xomega. auto.
  }
  intros. unfold or, Val.or; inv H; eauto with va; inv H0; eauto with va.
Qed.
*)

Definition same_pointer (p q : aptr) : bool := 
match p , q with 
     | Stk i , Stk j => Int.eq i j
     | Gl id1 o1 , Gl id2 o2 => ident_eq id1 id2 && Int.eq o1 o2
     |  _ ,  _   => false
   end.

Definition xor (v w: aval) :=
  match v, w with
  | I i1, I i2 => I (Int.xor i1 i2)
  | I i, Uns p n | Uns p n, I i => uns (poffset p) (Z.max n (usize i))
  | Uns p1 n1, Uns p2 n2 => uns (eplub (poffset p1) (poffset p2)) (Z.max n1 n2)
  | Sgn p1 n1, Sgn p2 n2 => sgn (eplub (poffset p1) (poffset p2)) (Z.max n1 n2)
  | Ptr p , Ptr q  => if same_pointer p q then I (Int.zero)
                      else ntop2 v w
  | _, _ => ntop2 v w
  end.

Lemma is_constant_usize : forall i v, 
     is_constant (Vint i) v -> 
     is_unsigned (usize i) v.
Proof.
  intros.
  rew_cst H.
  repeat intro ; simpl.
  exists i ; intuition.
Qed.

Lemma evge_uns : forall p q i,
    epge p q -> 
    evge (uns p i) (uns q i).
Proof.
  unfold uns.
  intros.
  repeat case_match; constructor; try xomega; auto.
Qed.



Lemma xor_sound: 
  forall v w x y, evmatch v x -> evmatch w y -> evmatch (Val.xor v w) (xor x y).
Proof.
  intros.
  assert (UNS :
            forall n m p p',
              is_unsigned n v -> 
              is_unsigned m w -> 
              epmatch w p ->
              epmatch v p' -> 
              evmatch (Val.xor v w) (uns (eplub (poffset p') (poffset p)) (Z.max n m))).
  {
    intros.
    unfold Val.xor.
    apply evmatch_uns.
    repeat intro.
    destruct (H1 a u) as [v1 [LD1 UNS1]].
    destruct (H2 a u) as [v2 [LD2 UNS2]].
    simpl.
    inv LD1 ; inv LD2.
    - rewrite H7 ; rewrite H8.
    exists (Int.xor v1 v2).
    intuition.
    intros; red; intros. rewrite Int.bits_xor by auto. 
    rewrite UNS1 by xomega.
    rewrite UNS2 by xomega. auto.
    - exists Int.zero.
      rewrite H7.
      intuition.
      repeat intro. rewrite Int.bits_zero.
      reflexivity.
    - exists Int.zero.
      intuition.
      repeat intro. rewrite Int.bits_zero.
      reflexivity.
    -  exists Int.zero.
      intuition.
      repeat intro. rewrite Int.bits_zero.
      reflexivity.
    - apply epmatch_binop_lub; auto.
  }
  assert (SGN :
            forall n m p p',
              is_signed n v -> 
              is_signed m w -> 
              epmatch w p ->
              epmatch v p' -> 
              evmatch (Val.xor v w) (sgn (eplub (poffset p') (poffset p)) (Z.max n m))).
  {
    intros.
    unfold Val.xor.
    apply evmatch_sgn'.
    repeat intro.
    destruct (H1 a u) as [v1 [LD1 UNS1]].
    destruct (H2 a u) as [v2 [LD2 UNS2]].
    simpl.
    inv LD1 ; inv LD2.
    - rewrite H7 ; rewrite H8.
    exists (Int.xor v1 v2).
    intuition.
    intros; red; intros.
    rewrite ! Int.bits_xor by xomega.
    rewrite UNS1 by xomega.
    rewrite UNS2 by xomega. auto.
    - exists Int.zero.
      rewrite H7.
      intuition.
      repeat intro. rewrite Int.bits_zero.
      reflexivity.
    - exists Int.zero.
      intuition.
      repeat intro. rewrite Int.bits_zero.
      reflexivity.
    -  exists Int.zero.
      intuition.
      repeat intro. rewrite Int.bits_zero.
      reflexivity.
    - apply epmatch_binop_lub; auto.
  }
  assert (TOP : evmatch (Val.xor v w) (ntop2 x y)).
  {
    eapply evmatch_ntop2 ; eauto.
    repeat constructor.
  }
  assert (SAMEPTR: forall b o,
             is_pointer b o v ->
             is_pointer b o w -> 
             evmatch (Val.xor v w) (I Int.zero)).
  {
    constructor.
    unfold Val.xor; simpl.
    rew_cst H1. rew_cst H2.
    repeat intro ; simpl.
    rewrite Int.xor_idem. reflexivity.
  }
  inv H ; inv H0 ; auto.
  - simpl ; constructor.
    unfold Val.xor.
    repeat intro ; simpl.
    rew_cst H1. rew_cst H.
  - simpl.
    clear TOP.
    assert (UNSI := H1).
    apply is_constant_usize in UNSI.
    apply is_constant_epmatch_Pcst in H1.
    exploit UNS ; eauto.
    eapply evmatch_ge.
    rewrite Z.max_comm.
    apply evge_uns.
    inv H3 ; simpl; auto.
  - simpl.
    clear TOP.
    assert (UNSI := H).
    apply is_constant_usize in UNSI.
    apply is_constant_epmatch_Pcst in H.
    exploit UNS ; eauto.
    eapply evmatch_ge.
    apply evge_uns.
    inv H3 ; simpl; auto.
  - simpl.   
    eauto.
  - simpl.
    eauto.
  -
    simpl.
    case_eq (same_pointer p p0) ; auto.
    intros.
    unfold same_pointer in H0.
    destruct p ; destruct p0 ; try congruence.
    +
      InvBooleans.
      generalize (Int.eq_spec ofs ofs0).
      rewrite H3. intuition subst.
      inv H ; inv H1.
      assert (b = b0) by (eapply bc_glob ; eauto).
      subst ; eauto.
    +
      generalize (Int.eq_spec ofs ofs0).
      rewrite H0. intuition subst.
      inv H ; inv H1.
      assert (b = b0) by (eapply bc_stack ; eauto).
      subst ; eauto.
Qed.

Definition notint (v:aval) := ntop1 v.

Lemma notint_sound:
  forall v x, evmatch v x -> evmatch (Val.notint v) (notint x).
Proof.
  intros. eapply evmatch_ntop1 ; repeat constructor;auto.
Qed.

(*
Definition notint (v: aval) :=
  match v with
  | I i => I (Int.not i)
  | Uns p n => sgn p (n + 1)
  | Sgn p n => Sgn p n
  | _ => ntop1 v
  end.

Lemma notint_sound:
  forall v x, vmatch v x -> vmatch (Val.notint v) (notint x).
Proof.
  assert (SGN: forall n i, is_sgn n i -> is_sgn n (Int.not i)).
  {
    intros; red; intros. rewrite ! Int.bits_not by omega. 
    f_equal. apply H; auto.
  }
  intros. unfold Val.notint, notint; inv H; eauto with va.
Qed.
*)

Definition ror (x y: aval) := ntop2 x y.

Lemma ror_sound: 
  forall v w x y, evmatch v x -> evmatch w y -> evmatch (Val.ror v w) (ror x y).
Proof.
  intros.
  eapply evmatch_ntop2 ; eauto.
  repeat constructor.
Qed.


(*
Definition ror (x y: aval) :=
  match y, x with
  | I j, I i => if Int.ltu j Int.iwordsize then I(Int.ror i j) else ntop
  | _, _ => ntop1 x
  end.

Lemma ror_sound: 
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.ror v w) (ror x y).
Proof.
  intros. 
  assert (DEFAULT: forall p, vmatch (Val.ror v w) (Ifptr p)). 
  {
    destruct v; destruct w; simpl; try constructor. 
    destruct (Int.ltu i0 Int.iwordsize); constructor.
  }
  unfold ror; destruct y; try apply DEFAULT; auto. inv H0. unfold Val.ror.
  destruct (Int.ltu n Int.iwordsize) eqn:LTU.
  inv H; auto with va.
  inv H; auto with va.
Qed.
*)

Definition rolm (x: aval) (amount mask: int) := ntop1 x.

Lemma rolm_sound:
  forall v x amount mask,
  evmatch v x -> evmatch (Val.rolm v amount mask) (rolm x amount mask).
Proof.
 repeat intro.
 eapply evmatch_ntop1 ; repeat constructor ; auto.
Qed.


(*
Definition rolm (x: aval) (amount mask: int) :=
  match x with
  | I i => I (Int.rolm i amount mask)
  | _   => uns (provenance x) (usize mask)
  end.

Lemma rolm_sound:
  forall v x amount mask,
  vmatch v x -> vmatch (Val.rolm v amount mask) (rolm x amount mask).
Proof.
  intros.
  assert (UNS_r: forall i j n, is_uns n j -> is_uns n (Int.and i j)).
  {
    intros; red; intros. rewrite Int.bits_and by auto. rewrite (H0 m) by auto. 
    apply andb_false_r.
  }
  assert (UNS: forall i, vmatch (Vint (Int.rolm i amount mask))
                                (uns (provenance x) (usize mask))).
  { intros. unfold Int.rolm. apply vmatch_uns. apply UNS_r. auto with va. }
  unfold Val.rolm, rolm. inv H; auto with va.
Qed.
 *)

(** Integer arithmetic operations *)

Definition neg := unop_int Int.neg.

Lemma neg_sound: 
  forall v x, evmatch v x -> evmatch (Val.neg v) (neg x).
Proof.
  intros.
  apply eunop_int_sound ; auto.
  - 
  repeat constructor.
  - 
    unfold Val.neg.
    intros.
    simpl.
    rewrite H0.
    reflexivity.
Qed.
    
Definition add (x y: aval) :=
  match x, y with
  | I i, I j => I (Int.add i j)
  | Ptr p, I i | I i, Ptr p => Ptr (padd p i)
  (* intervals are missing *) 
  (*  | Ptr p, _   | _, Ptr p   => Ptr (poffset p)*)
  | _, _ => ntop2 x y
  end.

Lemma add_sound:
  forall v w x y, evmatch v x -> evmatch w y -> evmatch (Val.add v w) (add x y).
Proof.
  intros.
  assert (evmatch (Val.add v w) (ntop2 x y)).
  {
    apply evmatch_ntop2 ; auto.
    repeat constructor.
  }
  unfold Val.add, add; inv H; inv H0; auto.
  - 
    constructor.
    rew_cst H2.
    rew_cst H.
    repeat intro.
    reflexivity.
  - 
    constructor.
    unfold is_constant in H2.
    rewrite <- H2.
    rewrite epmatch_same_eval with (y:= (Ebinop OpAdd Tint Tint  w (Eval (Vint i)))) ; eauto.
    apply epadd_sound; auto.
    red ; intros ; simpl.
    destruct (eSexpr cm em w) ; try reflexivity.
    rewrite Int.add_commut. reflexivity.
  -
    constructor.
    unfold is_constant in H.
    rewrite <- H.
    apply epadd_sound ; auto.
Qed.

Definition sub (v w: aval) :=
  match v, w with
  | I i1, I i2 => I (Int.sub i1 i2)
  | Ptr p, I i => Ptr (psub p i)
(* problem with undefs *)
  | Ptr p1, Ptr p2 => match psub2 p1 p2 with Some n => I n | _ => ntop2 v w end
  | _, _ => ntop2 v w
  end.

Lemma sub_sound: 
  forall v w x y, evmatch v x -> evmatch w y -> evmatch (Val.sub v w) (sub x y).
Proof.
  intros.
  assert (evmatch (Val.sub v w) (ntop2 x y)).
  {
    apply evmatch_ntop2 ; auto.
    repeat constructor.
  }
  unfold Val.sub, sub; inv H; inv H0; auto.
  - 
    constructor.
    rew_cst H2.
    rew_cst H.
    repeat intro ; reflexivity.
  -
    constructor.
    unfold is_constant in H.
    rewrite <- H.
    apply epsub_sound ; auto.
  - 
    case_eq (psub2 p p0).
    +
    intros.
    assert (is_constant (Vint i) (Val.sub v w)).
    eapply epsub2_sound ; eauto.
    unfold is_constant in H3.
    rewrite <- H3.
    constructor.
    seval_prf.
    reflexivity.
    +
      auto.
Qed.

Definition mul := binop_int Int.mul.

Lemma mul_sound: 
  forall v x w y, evmatch v x -> evmatch w y -> evmatch (Val.mul v w) (mul x y).
Proof.
  intros.
  apply ebinop_int_sound ; auto.
  repeat constructor.
  intros.
  unfold Val.mul ; simpl.
  rewrite H1 ; rewrite H2.
  reflexivity.
Qed.
  

Definition mulhs := binop_int Int.mulhs.

Lemma mulhs_sound: 
  forall v x w y, evmatch v x -> evmatch w y -> evmatch (Val.mulhs v w) (mulhs x y).
Proof.
  intros.
  apply ebinop_int_sound ; auto.
  repeat constructor.
  intros.
  unfold Val.mulhs ; simpl.
  rewrite H1 ; rewrite H2.
  reflexivity.
Qed.

Definition mulhu := binop_int Int.mulhu.

Lemma mulhu_sound: 
  forall v x w y, evmatch v x -> evmatch w y -> evmatch (Val.mulhu v w) (mulhu x y).
Proof.
  intros.
  apply ebinop_int_sound ; auto.
  repeat constructor.
  intros.
  unfold Val.mulhu ; simpl.
  rewrite H1 ; rewrite H2.
  reflexivity.
Qed.

Definition divs (v w: aval) :=
  match w, v with
  | I i2, I i1 =>
      if Int.eq i2 Int.zero
      || Int.eq i1 (Int.repr Int.min_signed) && Int.eq i2 Int.mone
      then  Ptr Pcst (* Should Pbot contain undef? *)
      else I (Int.divs i1 i2)
  | _, _ => ntop2 v w
  end.

Lemma divs_sound:
  forall v w  x y, evmatch v x -> evmatch w y -> evmatch (Val.divs v w) (divs x y).
Proof.
  intros.
  assert (DEFAULT : evmatch (Val.divs v w) (ntop2 x y)).
  {
    apply evmatch_ntop2; repeat constructor ; auto.
  }
  unfold divs. destruct x ; destruct y ; auto.
  inv H ; inv H0.
  unfold is_constant in *.
  unfold Val.divs.
  rewrite <- H3 ; rewrite <- H2.
  destruct (Int.eq n0 Int.zero
                   || Int.eq n (Int.repr Int.min_signed) && Int.eq n0 Int.mone) eqn:E.
  +
  constructor.
  constructor.
  depends_prf.
  +
    constructor.
    unfold is_constant.
    red ; intros.
    simpl.
    rewrite E. reflexivity.
Qed.

Definition divu (v w: aval) :=
  match w, v with
  | I i2, I i1 =>
      if Int.eq i2 Int.zero
       then Ptr Pcst (* Should Pbot contain undef *)
      else I (Int.divu i1 i2)
  | _, _ => ntop2 v w
  end.

Lemma divu_sound:
  forall v w x y, evmatch v x -> evmatch w y -> 
                    evmatch (Val.divu v w) (divu x y).
Proof.
  intros.
  assert (DEFAULT : evmatch (Val.divu v w) (ntop2 x y)).
  {
    apply evmatch_ntop2; repeat constructor ; auto.
  }
  unfold divu. destruct x ; destruct y ; auto.
  inv H ; inv H0.
  unfold is_constant in *.
  unfold Val.divu.
  rewrite <- H3 ; rewrite <- H2.
  destruct (Int.eq n0 Int.zero) eqn:E.
  +
  constructor.
  constructor.
  depends_prf.
  +
    constructor.
    unfold is_constant.
    red ; intros.
    simpl.
    rewrite E. reflexivity.
Qed.

Definition mods (v w: aval) :=
  match w, v with
  | I i2, I i1 =>
      if Int.eq i2 Int.zero
      || Int.eq i1 (Int.repr Int.min_signed) && Int.eq i2 Int.mone
      then Ptr Pcst
      else I (Int.mods i1 i2)
  | _, _ => ntop2 v w
  end.

Lemma mods_sound:
  forall v w  x y, evmatch v x -> evmatch w y -> evmatch (Val.mods v w) (mods x y).
Proof.
  intros.
  assert (DEFAULT : evmatch (Val.mods v w) (ntop2 x y)).
  {
    apply evmatch_ntop2; repeat constructor ; auto.
  }
  unfold mods. destruct x ; destruct y ; auto.
  inv H ; inv H0.
  unfold is_constant in *.
  unfold Val.mods.
  rewrite <- H3 ; rewrite <- H2.
  case_match; intro E.
  +
  constructor.
  constructor.
  depends_prf.
  +
    constructor.
    unfold is_constant.
    red ; intros.
    simpl.
    rewrite E. reflexivity.
Qed.

Definition modu (v w: aval) :=
  match w, v with
  | I i2, I i1 =>
      if Int.eq i2 Int.zero
      then Ptr Pcst 
      else I (Int.modu i1 i2)
  | I i2, _ => uns (provenance v) (usize i2)
  | _, _ => ntop2 v w
  end.

Lemma modu_sound:
  forall v w x y, evmatch v x -> evmatch w y -> evmatch (Val.modu v w) (modu x y).
Proof.
  assert (UNS: forall i j, j <> Int.zero -> is_uns (usize j) (Int.modu i j)).
  {
    intros. apply is_uns_mon with (usize (Int.modu i j)); auto with va.
    unfold usize, Int.size. apply Int.Zsize_monotone.
    generalize (Int.unsigned_range_2 j); intros RANGE.
    assert (Int.unsigned j <> 0). 
    { red; intros; elim H. rewrite <- (Int.repr_unsigned j). rewrite H0. auto. }
    exploit (Z_mod_lt (Int.unsigned i) (Int.unsigned j)). omega. intros MOD.
    unfold Int.modu. rewrite Int.unsigned_repr. omega. omega. 
  }
  intros.
  assert (DEFAULT2 : forall i,
            evmatch (Val.modu v (Eval (Vint i))) (uns (provenance x) (usize i))).
  {
    unfold provenance.
    clear H0.
    intros.
    eapply evmatch_uns'.
    unfold Val.modu.
    red ; intros.
    simpl.
    assert (HZ : is_uns (Z.max 0 (usize i)) Int.zero).
    { red ; intros.  rewrite Int.bits_zero. reflexivity. }
    case_eq (eSexpr a u v) ; simpl;
    try (exists Int.zero ; split ; [ constructor |]) ; auto.
    intros.
    destruct (Int.eq i Int.zero) eqn:Z.    
    +
      exists Int.zero ; split ; [constructor | auto].
    + 
      exists (Int.modu i0 i).
      split ; [constructor | auto].
      eapply is_uns_mon; eauto.
      apply UNS. 
      (generalize (Int.eq_spec i Int.zero); rewrite Z; auto). 
      zify ; omega.
    + 
      assert (evmatch (Val.modu v (Eval (Vint i))) (ntop1 x)).
      {
        apply evmatch_ntop1 with (T:= fun v => (Val.modu v (Eval (Vint i)))).
        repeat constructor.
        auto.
      }
      unfold ntop1 in H0.
      inv H0.
      apply H3.
  }
  assert (DEFAULT : evmatch (Val.modu v w) (ntop2 x y)).
  {
    apply evmatch_ntop2 ; repeat constructor ; auto.
  }
  unfold modu.
  destruct y ; auto.
  - 
    inv H0.
    unfold is_constant in H3.
    unfold Val.modu in *.
    rewrite <- H3.
    inv H ; eauto.
    destruct (Int.eq n Int.zero) eqn:Z.
    +
      constructor.
      constructor.
      unfold Val.modu.
      depends_prf.
    + 
      assert (n <> Int.zero) by (generalize (Int.eq_spec n Int.zero); rewrite Z; auto). 
      unfold Val.modu.
      constructor.
      unfold is_constant in *.
      rewrite <- H0.
      repeat intro ; simpl.
      rewrite Z. reflexivity.
Qed.

Definition shrx (v w: aval) :=
  match v, w with
  | I i, I j => if Int.ltu j (Int.repr 31) then I(Int.shrx i j) else ntop
  | _, _ => ntop2 v w
  end.


Lemma shrx_sound: 
  forall v w x y,
    evmatch v x -> evmatch w y ->
    evmatch (Val.shrx v w) (shrx x y).
Proof.
  intros.
  assert (evmatch (Val.shrx v w) (ntop2 x y)).
  {
    apply evmatch_ntop2; auto.
    repeat constructor.
  }
  inv H ; inv H0 ; auto.
  unfold Val.shrx.
  rew_cst H2.
  rew_cst H.
  simpl.
  destruct (Int.ltu i0 (Int.repr 31)) eqn:LTU.
  -
    constructor.
    clear H2 H.
    repeat intro.
    simpl. rewrite LTU ; reflexivity.
  - 
    unfold ntop.
    constructor.
    constructor.
    depends_prf.
Qed.

(** Floating-point arithmetic operations *)

Definition negf := unop_float Float.neg.

Lemma negf_sound: 
  forall v x, evmatch v x -> evmatch (Val.negf v) (negf x).
Proof.
  intros.
  apply eunop_float_sound ; auto.
  - repeat constructor.
  - unfold Val.negf.
    simpl.
    intros. rewrite H0 ; reflexivity.
Qed.    

Definition absf := unop_float Float.abs.

Lemma absf_sound: 
  forall v x, evmatch v x -> evmatch (Val.absf v) (absf x).
Proof.
  intros.
  apply eunop_float_sound ; auto.
  - repeat constructor.
  - unfold Val.absf.
    simpl.
    intros. rewrite H0 ; reflexivity.
Qed.    

Definition addf := binop_float Float.add.

Lemma addf_sound: 
  forall v x w y, evmatch v x -> evmatch w y -> evmatch (Val.addf v w) (addf x y).
Proof.
  intros.
  apply ebinop_float_sound ; auto.
  - repeat constructor.
  - unfold Val.addf.
    simpl.
    intros. rewrite H1 ; rewrite H2; reflexivity.
Qed.    

Definition subf := binop_float Float.sub.

Lemma subf_sound: 
  forall v x w y, evmatch v x -> evmatch w y -> evmatch (Val.subf v w) (subf x y).
Proof.
  intros.
  apply ebinop_float_sound ; auto.
  - repeat constructor.
  - unfold Val.subf.
    simpl.
    intros. rewrite H1 ; rewrite H2; reflexivity.
Qed.    

Definition mulf := binop_float Float.mul.

Lemma mulf_sound: 
  forall v x w y, evmatch v x -> evmatch w y -> evmatch (Val.mulf v w) (mulf x y).
Proof.
  intros.
  apply ebinop_float_sound ; auto.
  - repeat constructor.
  - unfold Val.mulf.
    simpl.
    intros. rewrite H1 ; rewrite H2; reflexivity.
Qed.    

Definition divf := binop_float Float.div.

Lemma divf_sound: 
  forall v x w y, evmatch v x -> evmatch w y -> evmatch (Val.divf v w) (divf x y).
Proof.
  intros.
  apply ebinop_float_sound ; auto.
  - repeat constructor.
  - unfold Val.mulf.
    simpl.
    intros. rewrite H1 ; rewrite H2; reflexivity.
Qed.    

Definition negfs := unop_single Float32.neg.

Lemma negfs_sound: 
  forall v x, evmatch v x -> evmatch (Val.negfs v) (negfs x).
Proof.
  intros.
  apply eunop_single_sound ; auto.
  - repeat constructor.
  - unfold Val.negfs.
    simpl.
    intros. rewrite H0 ; reflexivity.
Qed.    

Definition absfs := unop_single Float32.abs.

Lemma absfs_sound: 
  forall v x, evmatch v x -> evmatch (Val.absfs v) (absfs x).
Proof.
  intros.
  apply eunop_single_sound ; auto.
  - repeat constructor.
  - unfold Val.absfs.
    simpl.
    intros. rewrite H0 ; reflexivity.
Qed.

Definition addfs := binop_single Float32.add.

Lemma addfs_sound: 
  forall v x w y, evmatch v x -> evmatch w y -> evmatch (Val.addfs v w) (addfs x y).
Proof.
  intros.
  apply ebinop_single_sound ; auto.
  - repeat constructor.
  - unfold Val.addfs.
    simpl.
    intros. rewrite H1 ; rewrite H2; reflexivity.
Qed.    

Definition subfs := binop_single Float32.sub.

Lemma subfs_sound: 
  forall v x w y, evmatch v x -> evmatch w y -> evmatch (Val.subfs v w) (subfs x y).
Proof.
  intros.
  apply ebinop_single_sound ; auto.
  - repeat constructor.
  - unfold Val.subfs.
    simpl.
    intros. rewrite H1 ; rewrite H2; reflexivity.
Qed.    

Definition mulfs := binop_single Float32.mul.

Lemma mulfs_sound: 
  forall v x w y, evmatch v x -> evmatch w y -> evmatch (Val.mulfs v w) (mulfs x y).
Proof.
  intros.
  apply ebinop_single_sound ; auto.
  - repeat constructor.
  - unfold Val.mulfs.
    simpl.
    intros. rewrite H1 ; rewrite H2; reflexivity.
Qed.    

Definition divfs := binop_single Float32.div.

Lemma divfs_sound: 
  forall v x w y, evmatch v x -> evmatch w y -> evmatch (Val.divfs v w) (divfs x y).
Proof.
  intros.
  apply ebinop_single_sound ; auto.
  - repeat constructor.
  - unfold Val.divfs.
    simpl.
    intros. rewrite H1 ; rewrite H2; reflexivity.
Qed.    

(** Conversions *)

Definition not_int (v : aval) : bool :=
  match v with
    | L _ | F _ | FS _ => true
    | _  => false
  end.


Definition zero_ext (nbits: Z) (v: aval) :=
  if zlt nbits Int.zwordsize || not_int v
  then
    match v with
      | I i => I (Int.zero_ext nbits i)
      | Ptr p   =>  uns (provenance v) nbits
      | Uns p n => uns (poffset p) (Z.min n nbits)
      | _ => uns (provenance v) nbits
    end
  else v.

Lemma is_uns_zwordsize :
  forall n i, n >= Int.zwordsize -> is_uns n i.
Proof.
  intros.
  unfold is_uns.
  intros.
  omega.
Qed.  

Lemma zero_ext_zero :
  forall nbits, Int.zero_ext nbits Int.zero = Int.zero.
Proof.
  intros.
  rewrite <- is_uns_zero_ext.
  repeat intro.
  apply Int.bits_zero.
Qed.  
  
Lemma epmatch_zero_ext :
  forall v p nbits
         (MATCH : epmatch v p)
         (GE : nbits >= Int.zwordsize),
   epmatch (Val.zero_ext nbits v) p.
Proof.
  intros.
  inv MATCH ; try constructor ; depends_prf.
  *
    rewrite epmatch_same_eval with (y:=v) (y0 := Gl id ofs).
    econstructor ; eauto.
    unfold Val.zero_ext.
    rew_cst H0.
    repeat intro.
    simpl. rewrite Int.zero_ext_above;auto.
    reflexivity. 
  *
    rewrite epmatch_same_eval with (y:=v) (y0 := Stk ofs).
    econstructor ; eauto.
    unfold Val.zero_ext.
    rew_cst H0.
    repeat intro.
    simpl. rewrite Int.zero_ext_above;auto.
    reflexivity. 
Qed.

  
Lemma zero_ext_sound:
  forall nbits v x, evmatch v x -> evmatch (Val.zero_ext nbits v) (zero_ext nbits x).
Proof.
  assert (DFL: forall nbits i, is_uns nbits (Int.zero_ext nbits i)).
  {
    intros; red; intros. rewrite Int.bits_zero_ext by omega. apply zlt_false; auto. 
  }
  assert (DEFAULTMX : 
            forall nbits v p ,
              epmatch v p -> 
              evmatch (Val.zero_ext nbits v) (uns (poffset p) Int.zwordsize)).
  {
    intros.
    apply evmatch_uns.
    unfold is_unsigned.
    unfold Val.zero_ext.
    simpl.
    intros.
    case_eq (eSexpr a u v) ; simpl ; intros;
    try 
      (exists (Int.zero_ext nbits Int.zero); 
        split;[constructor | auto]);    try (apply is_uns_zwordsize;omega).
    exists (Int.zero_ext nbits i).
    split ; simpl ; auto.
    apply is_uns_zwordsize; omega.
    apply epmatch_poffset ; auto.
    repeat constructor.
  }
  assert (DEFAULT2 : 
            forall nbits v p ,
              epmatch v p -> 
              evmatch (Val.zero_ext nbits v) (uns (poffset p) nbits)).
  {
    intros.
    apply evmatch_uns.
    unfold is_unsigned.
    unfold Val.zero_ext.
    simpl.
    intros.
    case_eq (eSexpr a u v) ; simpl ; intros;
    try 
      (exists (Int.zero_ext nbits Int.zero); 
        split;[constructor | auto]).
    exists (Int.zero_ext nbits i).
    split ; simpl ; auto.
    apply epmatch_poffset ; auto.
    repeat constructor.
  }
  assert (DEFAULT : forall n nbits v p
                           (HLE : 0 <= n),
                      is_unsigned n v -> 
                      epmatch v p -> 
                      evmatch (Val.zero_ext nbits v) (uns (poffset p) (Z.min n nbits))).
  {
    intros.
    apply evmatch_uns.
    revert H.
    apply is_unsigned_unsigned with (Ti := fun i => Int.zero_ext nbits i).
    - 
      intros.
      unfold Val.zero_ext.
      simpl.
      inv H; try constructor.
      rewrite H3.
      constructor.
    - 
      intros.
      red; intros. zify.
      rewrite Int.bits_zero_ext by omega.
      destruct (zlt m nbits); auto. apply H; omega. 
    - 
      apply epmatch_poffset ; auto.
      repeat constructor.
  }
  intros.
  unfold zero_ext.
  case_eq ((zlt nbits Int.zwordsize) || not_int x); intro CASE.
  inv H; simpl; unfold provenance, aptr_of_aval ; auto with va.
  -  constructor.
     unfold Val.zero_ext.
     rew_cst H0.
     repeat intro.
     simpl. reflexivity.
  -
    apply DEFAULT2; auto.
    constructor; auto. depends_prf.
  - 
    apply DEFAULT2; auto.
    constructor; auto. depends_prf.
  -  apply DEFAULT2 ; auto.
    constructor; auto. depends_prf.
  - 
    rewrite orb_false_iff in CASE.
    destruct CASE as [C1 C2].
    unfold proj_sumbool in C1.
    destruct (zlt nbits Int.zwordsize); try congruence.
    inv H ; constructor; try omega ; simpl in C2 ; try congruence.
    +
      unfold Val.zero_ext.
      rew_cst H0.
      repeat intro.
      simpl.
      rewrite Int.zero_ext_above ; auto.
    + 
      revert H1.
      apply is_unsigned_unsigned with (Ti := fun x => Int.zero_ext nbits x);
        unfold Val.zero_ext.
      *
        repeat intro; simpl.
        inv H. rewrite H4 ; simpl ; constructor.
        constructor.
      * 
        intros.
        rewrite Int.zero_ext_above ; auto.
    + 
      apply epmatch_zero_ext ; auto.
    + 
      revert H1.
      apply is_signed_signed with (Ti := fun x => Int.zero_ext nbits x);
        unfold Val.zero_ext.
      *
        repeat intro; simpl.
        inv H. rewrite H4 ; simpl ; constructor.
        constructor.
      * 
        intros.
        rewrite Int.zero_ext_above ; auto.
    + 
      apply epmatch_zero_ext ; auto.
    + 
      apply epmatch_zero_ext ; auto.
Qed.

Definition sign_ext (nbits: Z) (v: aval) :=
  match v with
  | I i => I (Int.sign_ext nbits i)
  | Ptr p   => if zlt nbits Int.zwordsize then sgn (provenance v) nbits
               else Ptr p
  | Uns p n => if zlt nbits Int.zwordsize
               then
                 if zlt n nbits then Uns (poffset p) n
                 else sgn (poffset p) nbits
               else Uns  p n
  | Sgn p n => if zlt nbits Int.zwordsize
               then sgn (poffset p) (Z.min n nbits)
               else Sgn  p n
  | _ => sgn (provenance v) nbits
  end.

Lemma sign_ext_deflt : 
  forall  nbits,
    0 < nbits ->
    forall p v,
      epmatch v p-> 
      evmatch (Val.sign_ext nbits v) (sgn (poffset p) nbits).
Proof.
  intros. apply vmatch_sgn.
  repeat intro.
  unfold Val.sign_ext.
  simpl.
  case_eq (eSexpr a u v) ; intros ; simpl;
  try 
    (exists Int.zero;
            split ; [constructor|
                     red ; intros;
                     repeat rewrite Int.bits_zero ;auto]).
  exists (Int.sign_ext nbits i).
    split. simpl; constructor.
    apply is_sign_ext_sgn; auto with va.
    apply epmatch_poffset; auto. repeat constructor ; auto.
Qed.

Lemma sign_ext_zwordsize :
  forall v p nbits, 
    epmatch v p -> 
    nbits >= Int.zwordsize -> 
   epmatch (Val.sign_ext nbits v) p.
Proof.
  intros.
  inv H ; try constructor ; depends_prf.
  -
    rewrite epmatch_same_eval with (y:=v) (y0 := Gl id ofs).
    econstructor ; eauto.
    unfold Val.sign_ext.
    rew_cst H2.
    repeat intro.
    simpl. rewrite Int.sign_ext_above;auto.
    reflexivity. 
  - 
    rewrite epmatch_same_eval with (y:=v) (y0 := Stk ofs).
    econstructor ; eauto.
    unfold Val.sign_ext.
    rew_cst H2.
    repeat intro.
    simpl. rewrite Int.sign_ext_above;auto.
    reflexivity. 
Qed.  

Lemma sign_ext_sound:
  forall nbits v x, 0 < nbits -> evmatch v x -> evmatch (Val.sign_ext nbits v) (sign_ext nbits x).
Proof.
  assert (DFL:= sign_ext_deflt).
  intros. inv H0; simpl; auto with va. 
  -
    unfold Val.sign_ext.
    rew_cst H1.
    constructor.
    repeat intro; simpl.
    reflexivity.
  - 
    destruct (zlt nbits Int.zwordsize).
    +
    destruct (zlt n nbits); eauto with va.
    constructor; auto.
    revert H2.
    apply is_unsigned_unsigned with (Ti := fun i => Int.sign_ext nbits i).
    *
      intros.
      unfold Val.sign_ext; simpl.
      inv H0.
      rewrite H5. simpl ; constructor.
      simpl ; constructor.
    * intros.
      eapply is_sign_ext_uns; eauto with va. 
    * 
      apply epmatch_poffset ; auto.
      repeat constructor.
    + 
      constructor ; auto.
      revert H2.
      apply is_unsigned_unsigned with (Ti := fun i => Int.sign_ext nbits i).
      *    
        intros.
        unfold Val.sign_ext; simpl.
        inv H0.
        rewrite H5. simpl ; constructor.
        simpl ; constructor.
      * intros.
        repeat intro.
        rewrite Int.sign_ext_above ; auto.
      * 
        apply sign_ext_zwordsize ; auto.
  - 
    destruct (zlt nbits Int.zwordsize).
    + 
    apply vmatch_sgn.
    revert H2.
    apply is_signed_signed with (Ti := fun i => Int.sign_ext nbits i).    
      intros.
      unfold Val.sign_ext; simpl.
      inv H0.
      rewrite H5. simpl ; constructor.
      simpl ; constructor.
    * intros.
      eapply is_sign_ext_sgn; eauto with va. 
      apply Z.min_case; auto with va.
    * 
      apply epmatch_poffset ; auto ; repeat constructor.
    + 
      constructor; auto.
      revert H2.
      apply is_signed_signed with (Ti := fun i => Int.sign_ext nbits i).
      *    
        intros.
        unfold Val.sign_ext; simpl.
        inv H0.
        rewrite H5. simpl ; constructor.
        simpl ; constructor.
      * intros.
        repeat intro.
        rewrite Int.sign_ext_above ; auto.
      * 
        apply sign_ext_zwordsize ; auto.
  - 
    unfold provenance.
    apply DFL; auto.
    simpl. constructor ; depends_prf.
  - 
    unfold provenance.
    apply DFL; auto.
    simpl. constructor ; depends_prf.
  - 
    unfold provenance.
    apply DFL; auto.
    simpl. constructor ; depends_prf.
  - 
    unfold provenance.
    destruct (zlt nbits Int.zwordsize).
    apply DFL; auto.
    constructor.
    apply sign_ext_zwordsize; auto.
Qed.

Definition singleoffloat (v: aval) :=
  match v with
  | F f => FS (Float.to_single f)
  | _   => ntop1 v
  end.

Lemma singleoffloat_sound:
  forall v x, evmatch v x -> evmatch (Val.singleoffloat v) (singleoffloat x).
Proof.
  intros.  
  assert (DEFAULT: evmatch (Val.singleoffloat v) (ntop1 x)).
  {
    apply evmatch_ntop1; auto.
    repeat constructor; auto.
  }
  destruct x; auto. inv H. constructor. 
  repeat intro.
  simpl.
  rew_cst H2; auto.
Qed.

Definition floatofsingle (v: aval) :=
  match v with
  | FS f => F (Float.of_single f)
  | _   => ntop1 v
  end.

Lemma floatofsingle_sound:
  forall v x, evmatch v x -> evmatch (Val.floatofsingle v) (floatofsingle x).
Proof.
  intros.  
  assert (DEFAULT: evmatch (Val.floatofsingle v) (ntop1 x)).
  {
    apply evmatch_ntop1 ; auto.
    repeat constructor.
  }
  destruct x; auto. inv H. constructor. 
  repeat intro.
  simpl. rew_cst H2; auto.
Qed.

Definition intoffloat (x:aval) := ntop1 x.

Lemma intoffloat_sound:
  forall v x, evmatch v x ->  evmatch (Val.intoffloat v) (intoffloat x).
Proof.
  intros. eapply evmatch_ntop1 ; repeat constructor ; auto.
Qed.


(*
Definition intoffloat (x: aval) :=
  match x with
  | F f =>
      match Float.to_int f with
      | Some i => I i
      | None => if va_strict tt then Vbot else ntop
      end
  | _ => ntop1 x
  end.

Lemma intoffloat_sound:
  forall v x w, vmatch v x -> Val.intoffloat v = Some w -> vmatch w (intoffloat x).
Proof.
  unfold Val.intoffloat; intros. destruct v; try discriminate. 
  destruct (Float.to_int f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor. 
Qed.
*)

Definition intuoffloat (x: aval) := ntop1 x.

Lemma intuoffloat_sound:
  forall v x, evmatch v x -> evmatch (Val.intuoffloat v) (intuoffloat x).
Proof.
 intros.
 eapply evmatch_ntop1 ; repeat constructor ; auto.
Qed.

(*
Definition intuoffloat (x: aval) :=
  match x with
  | F f =>
      match Float.to_intu f with
      | Some i => I i
      | None => if va_strict tt then Vbot else ntop
      end
  | _ => ntop1 x
  end.

Lemma intuoffloat_sound:
  forall v x w, vmatch v x -> Val.intuoffloat v = Some w -> vmatch w (intuoffloat x).
Proof.
  unfold Val.intuoffloat; intros. destruct v; try discriminate. 
  destruct (Float.to_intu f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor. 
Qed.
*)

Definition floatofint (x: aval) := ntop1 x.

Lemma floatofint_sound:
  forall v x, evmatch v x ->  evmatch (Val.floatofint v) (floatofint x).
Proof.
 intros.
 eapply evmatch_ntop1 ; repeat constructor ; auto.
Qed.

(*
Definition floatofint (x: aval) :=
  match x with
  | I i => F(Float.of_int i)
  | _   => ntop1 x
  end.

Lemma floatofint_sound:
  forall v x w, vmatch v x -> Val.floatofint v = Some w -> vmatch w (floatofint x).
Proof.
  unfold Val.floatofint; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.
*)

Definition floatofintu (x: aval) := ntop1 x.

Lemma floatofintu_sound:
  forall v x, evmatch v x ->  evmatch (Val.floatofintu v) (floatofintu x).
Proof.
 intros.
 eapply evmatch_ntop1 ; repeat constructor ; auto.
Qed.

(*
Definition floatofintu (x: aval) :=
  match x with
  | I i => F(Float.of_intu i)
  | _   => ntop1 x
  end.

Lemma floatofintu_sound:
  forall v x w, vmatch v x -> Val.floatofintu v = Some w -> vmatch w (floatofintu x).
Proof.
  unfold Val.floatofintu; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.
*)

Definition intofsingle (x: aval) := ntop1 x.

Lemma intofsingle_sound:
  forall v x, evmatch v x -> evmatch (Val.intofsingle v) (intofsingle x).
Proof.
 intros.
 eapply evmatch_ntop1 ; repeat constructor ; auto.
Qed.

(*
Definition intofsingle (x: aval) :=
  match x with
  | FS f =>
      match Float32.to_int f with
      | Some i => I i
      | None => if va_strict tt then Vbot else ntop
      end
  | _ => ntop1 x
  end.

Lemma intofsingle_sound:
  forall v x w, vmatch v x -> Val.intofsingle v = Some w -> vmatch w (intofsingle x).
Proof.
  unfold Val.intofsingle; intros. destruct v; try discriminate. 
  destruct (Float32.to_int f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor. 
Qed.
*)

Definition intuofsingle (x: aval) := ntop1 x.

Lemma intuofsingle_sound:
  forall v x, evmatch v x ->  evmatch (Val.intuofsingle v) (intuofsingle x).
Proof.
 intros.
 eapply evmatch_ntop1 ; repeat constructor ; auto.
Qed.

(*
Definition intuofsingle (x: aval) :=
  match x with
  | FS f =>
      match Float32.to_intu f with
      | Some i => I i
      | None => if va_strict tt then Vbot else ntop
      end
  | _ => ntop1 x
  end.

Lemma intuofsingle_sound:
  forall v x w, vmatch v x -> Val.intuofsingle v = Some w -> vmatch w (intuofsingle x).
Proof.
  unfold Val.intuofsingle; intros. destruct v; try discriminate. 
  destruct (Float32.to_intu f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor. 
Qed.
*)

Definition singleofint (x: aval) := ntop1 x.

Lemma singleofint_sound:
  forall v x, evmatch v x -> evmatch (Val.singleofint v) (singleofint x).
Proof.
 intros.
 eapply evmatch_ntop1 ; repeat constructor ; auto.
Qed.

(*
Definition singleofint (x: aval) :=
  match x with
  | I i => FS(Float32.of_int i)
  | _   => ntop1 x
  end.

Lemma singleofint_sound:
  forall v x w, vmatch v x -> Val.singleofint v = Some w -> vmatch w (singleofint x).
Proof.
  unfold Val.singleofint; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.
*)

Definition singleofintu (x: aval) := ntop1 x.
 
Lemma singleofintu_sound:
  forall v x, evmatch v x -> evmatch (Val.singleofintu v) (singleofintu x).
Proof.
 intros.
 eapply evmatch_ntop1 ; repeat constructor ; auto.
Qed.


(*
Definition singleofintu (x: aval) :=
  match x with
  | I i => FS(Float32.of_intu i)
  | _   => ntop1 x
  end.

Lemma singleofintu_sound:
  forall v x w, vmatch v x -> Val.singleofintu v = Some w -> vmatch w (singleofintu x).
Proof.
  unfold Val.singleofintu; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.
*)

Definition floatofwords (x y: aval) := ntop2 x y.

Lemma floatofwords_sound:
  forall v  x y w, evmatch v x -> evmatch w y -> evmatch (Val.floatofwords v w) (floatofwords x y).
Proof.
 intros.
 eapply evmatch_ntop2 ; repeat constructor ; auto.
Qed.


(*
Definition floatofwords (x y: aval) :=
  match x, y with
  | I i, I j => F(Float.from_words i j)
  | _, _     => ntop2 x y
  end.

Lemma floatofwords_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.floatofwords v w) (floatofwords x y).
Proof.
  intros. unfold floatofwords; inv H; simpl; auto with va; inv H0; auto with va.
Qed.
*)

Definition longofwords (x y : aval) := ntop2 x y.

Lemma longofwords_sound:
  forall v w x y, evmatch v x -> evmatch w y -> evmatch (Val.longofwords v w) (longofwords x y).
Proof.
 intros.
 eapply evmatch_ntop2 ; repeat constructor ; auto.
Qed.

(*
Definition longofwords (x y: aval) :=
  match y, x with
  | I j, I i => L(Int64.ofwords i j)
  | _, _     => ntop2 x y
  end.

Lemma longofwords_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.longofwords v w) (longofwords x y).
Proof.
  intros. unfold longofwords; inv H0; inv H; simpl; auto with va.
Qed.
*)

Definition loword (x: aval) := ntop1 x.

Lemma loword_sound: forall v x, evmatch v x -> evmatch (Val.loword v) (loword x).
Proof.
 intros.
 eapply evmatch_ntop1 ; repeat constructor ; auto.
Qed.

(*
Definition loword (x: aval) :=
  match x with
  | L i => I(Int64.loword i)
  | _   => ntop1 x
  end.

Lemma loword_sound: forall v x, vmatch v x -> vmatch (Val.loword v) (loword x).
Proof.
  destruct 1; simpl; auto with va.
Qed.
*)

Definition hiword (x: aval) := ntop1 x.

Lemma hiword_sound: forall v x, evmatch v x -> evmatch (Val.hiword v) (hiword x).
Proof.
 intros.
 eapply evmatch_ntop1 ; repeat constructor ; auto.
Qed.

(*
Definition hiword (x: aval) :=
  match x with
  | L i => I(Int64.hiword i)
  | _   => ntop1 x
  end.

Lemma hiword_sound: forall v x, vmatch v x -> vmatch (Val.hiword v) (hiword x).
Proof.
  destruct 1; simpl; auto with va.
Qed.
 *)

(** Comparisons and variation intervals *)

Definition cmp_intv (c: comparison) (i: Z * Z) (n: Z) : abool :=
  let (lo, hi) := i in
  match c with
  | Ceq => if zlt n lo || zlt hi n then Maybe false else Btop
  | Cne => Btop
  | Clt => if zlt hi n then Maybe true else if zle n lo then Maybe false else Btop
  | Cle => if zle hi n then Maybe true else if zlt n lo then Maybe false else Btop
  | Cgt => if zlt n lo then Maybe true else if zle hi n then Maybe false else Btop
  | Cge => if zle n lo then Maybe true else if zlt hi n then Maybe false else Btop
  end.

Definition zcmp (c: comparison) (n1 n2: Z) : bool :=
  match c with
  | Ceq => zeq n1 n2
  | Cne => negb (zeq n1 n2)
  | Clt => zlt n1 n2
  | Cle => zle n1 n2
  | Cgt => zlt n2 n1
  | Cge => zle n2 n1
  end.

Lemma zcmp_intv_sound:
  forall c i x n,
  fst i <= x <= snd i ->
  cmatch (Some (zcmp c x n)) (cmp_intv c i n).
Proof.
  intros c [lo hi] x n; simpl; intros R.
  destruct c; unfold zcmp, proj_sumbool.
- (* eq *)
  destruct (zlt n lo). rewrite zeq_false by omega. constructor. 
  destruct (zlt hi n). rewrite zeq_false by omega. constructor.
  constructor.
- (* ne *)
  constructor.
- (* lt *)
  destruct (zlt hi n). rewrite zlt_true by omega. constructor.
  destruct (zle n lo). rewrite zlt_false by omega. constructor.
  constructor.
- (* le *)
  destruct (zle hi n). rewrite zle_true by omega. constructor.
  destruct (zlt n lo). rewrite zle_false by omega. constructor.
  constructor.
- (* gt *)
  destruct (zlt n lo). rewrite zlt_true by omega. constructor.
  destruct (zle hi n). rewrite zlt_false by omega. constructor.
  constructor.
- (* ge *)
  destruct (zle n lo). rewrite zle_true by omega. constructor.
  destruct (zlt hi n). rewrite zle_false by omega. constructor.
  constructor.
Qed.

Lemma cmp_intv_None:
  forall c i n, cmatch None (cmp_intv c i n).
Proof.
  unfold cmp_intv; intros. destruct i as [lo hi].
  destruct c.
- (* eq *)
  destruct (zlt n lo). constructor. destruct (zlt hi n); constructor.
- (* ne *)
  constructor.
- (* lt *)
  destruct (zlt hi n). constructor. destruct (zle n lo); constructor.
- (* le *)
  destruct (zle hi n). constructor. destruct (zlt n lo); constructor.
- (* gt *)
  destruct (zlt n lo). constructor. destruct (zle hi n); constructor.
- (* ge *)
  destruct (zle n lo). constructor. destruct (zlt hi n); constructor.
Qed.

Definition uintv (v: aval) : Z * Z :=
  match v with
  | I n => (Int.unsigned n, Int.unsigned n)
  | Uns _ n => if zlt n Int.zwordsize then (0, two_p n - 1) else (0, Int.max_unsigned)
  | _ => (0, Int.max_unsigned)
  end.

Lemma is_unsigned_const :
  forall n i align bound
         (NOFORGERY : no_forgery Int.max_unsigned bound align)
  ,
    is_unsigned n (Eval (Vint i)) ->
    is_uns n i.
Proof.
  intros.
  unfold is_unsigned in H.
  destruct (NOFORGERY xH) as [cm [COMPAT HH]].
  destruct (H cm (fun _ _ => Byte.zero) ); auto.
  simpl in H0.
  destruct H0. inv H0. auto.
Qed.

(*
Definition is_interval (lb : Z) (ub : Z) (e : expr_sym) :=
  forall a u
         (COMPAT : compat Int.max_unsigned bound align a),
    exists i, Values.Val.lessdef (eSexpr a u e) (Vint i) /\ lb <= Int.unsigned i <= ub.

Definition is_integer (e : expr_sym) :=
  forall a u (COMPAT : compat Int.max_unsigned bound align a),
    exists i, eSexpr a u e = Vint i.
*)

Lemma uintv_sound:
  forall e v          (MATCH : evmatch e v)
         a
         u i
         (EVAL : eSexpr a u e = Vint i)
  ,
    (fst (uintv v)) <= Int.unsigned i <= (snd (uintv v)).
Proof.
  intros.
  assert (DFL :  0 <= Int.unsigned i <= Int.max_unsigned).
  {
    apply Int.unsigned_range_2.
  }
    inv MATCH; simpl; try apply DFL.
  -
    rew_cst H;auto.
    simpl in EVAL. inv EVAL ; omega.
  - destruct (zlt n Int.zwordsize); simpl.
  +
    unfold is_unsigned in H0.
    destruct (H0 a u ).
    destruct H2. rewrite EVAL in H2.
    inv H2.
    rewrite is_uns_zero_ext in H3. rewrite <- H3. rewrite Int.zero_ext_mod by omega. 
  exploit (Z_mod_lt (Int.unsigned x) (two_p n)). apply two_p_gt_ZERO; auto. omega.
  +
    apply DFL.
Qed.

Lemma cmpu_intv_sound:
  forall  c e  v1 n2,
    evmatch e v1 ->
    ecmatch (Val.cmpu_bool c e (Eval (Vint n2))) (cmp_intv c (uintv v1) (Int.unsigned n2)).
Proof.
  intros.
  assert (HUNINT := uintv_sound e v1 H).
  destruct (uintv v1) as [lb ub].
  clear H.
  simpl in *.
  destruct c.
  - (* eq *)
    case_eq (zlt (Int.unsigned n2) lb || zlt ub (Int.unsigned n2)) ; constructor.
    simpl.
    repeat intro.
    simpl.
    case_eq (eSexpr a u e) ; simpl ; try constructor.
    intros.
    predSpec Int.eq Int.eq_spec i n2 ; try constructor.
    exfalso.
    subst.
    rewrite orb_true_iff in H.
    unfold proj_sumbool in H.
    specialize (HUNINT a u _ H0).
    destruct H.
    destruct (zlt (Int.unsigned n2) lb) ; try congruence.
    omega. 
    destruct (zlt ub (Int.unsigned n2)) ; try congruence.
    omega.
    apply is_bool_cmpu_bool.
  - (* ne *)
  constructor. apply is_bool_cmpu_bool.
- (* lt *)
  destruct (zlt ub (Int.unsigned n2)).
  constructor.
  repeat intro. simpl.
  case_eq (eSexpr a u e) ; simpl ; try constructor.
  unfold Int.ltu.
  intros. eapply HUNINT in H ; eauto.
  destruct (zlt (Int.unsigned i) (Int.unsigned n2) ) ; try constructor.
  omega.
  destruct (zle (Int.unsigned n2) lb) ; try constructor.
  repeat intro ; simpl.
  case_eq (eSexpr a u e) ; simpl ; try constructor.
  unfold Int.ltu.
  intros. eapply HUNINT in H ; eauto.
  destruct (zlt (Int.unsigned i) (Int.unsigned n2) ) ; try constructor.
  omega.
  apply is_bool_cmpu_bool.
- (* le *)
  destruct (zle ub (Int.unsigned n2)).
  +
  constructor.
  repeat intro. simpl.
  case_eq (eSexpr a u e) ; simpl ; try constructor.
  unfold Int.ltu.
  intros. eapply HUNINT in H ; eauto.
  destruct (zlt (Int.unsigned n2) (Int.unsigned i) ) ; try constructor.
  omega.
  + 
    destruct (zlt (Int.unsigned n2) lb );
    constructor.
    repeat intro. simpl.
    case_eq (eSexpr a u e) ; simpl ; try constructor.
    unfold Int.ltu.
    intros. eapply HUNINT in H ; eauto.
    destruct (zlt (Int.unsigned n2) (Int.unsigned i) ) ; try constructor.
    omega.
    apply is_bool_cmpu_bool.
- (* gt *)
  destruct (zlt (Int.unsigned n2) lb) ; try constructor.
  repeat intro;simpl.
  case_eq (eSexpr a u e) ; simpl ; try constructor.
  unfold Int.ltu.
  intros. eapply HUNINT in H ; eauto.
  destruct (zlt (Int.unsigned n2) (Int.unsigned i) ) ; try constructor.
  omega.
  destruct (zle ub (Int.unsigned n2)) ; try constructor.
  repeat intro;simpl.
  case_eq (eSexpr a u e) ; simpl ; try constructor.
  unfold Int.ltu.
  intros. eapply HUNINT in H ; eauto.
  destruct (zlt (Int.unsigned n2) (Int.unsigned i) ) ; try constructor.
  omega. apply is_bool_cmpu_bool.
- (* ge *)
  destruct (zle (Int.unsigned n2) lb) ; try constructor.
  repeat intro;simpl.
  case_eq (eSexpr a u e) ; simpl ; try constructor.
  unfold Int.ltu.
  intros. eapply HUNINT in H ; eauto.
  destruct (zlt (Int.unsigned i) (Int.unsigned n2) ) ; try constructor.
  omega.
  destruct (zlt ub (Int.unsigned n2)) ; try constructor.
  repeat intro;simpl.
  case_eq (eSexpr a u e) ; simpl ; try constructor.
  unfold Int.ltu.
  intros. eapply HUNINT in H ; eauto.
  destruct (zlt (Int.unsigned i) (Int.unsigned n2) ) ; try constructor.
  omega.
  apply is_bool_cmpu_bool.
Qed.


Lemma cmpu_intv_sound_2:
  forall  c e v1 n2,
  evmatch e v1 ->
  ecmatch (Val.cmpu_bool  c (Eval (Vint n2)) e) (cmp_intv (swap_comparison c) (uintv v1) (Int.unsigned n2)).
Proof.
  intros.
  rewrite cmatch_morph with (y := Val.cmpu_bool (swap_comparison c) e (Eval (Vint n2))).
  apply cmpu_intv_sound.
  apply H.
  repeat intro.
  simpl.
  destruct (eSexpr cm em e) ; destruct c ; simpl ; try reflexivity.
  - 
  rewrite Int.eq_sym. reflexivity.
  -   rewrite Int.eq_sym. reflexivity.
  - reflexivity.
Qed.

Definition sintv (v: aval) : Z * Z :=
  match v with
  | I n => (Int.signed n, Int.signed n)
  | Uns _ n =>
      if zlt n Int.zwordsize then (0, two_p n - 1) else (Int.min_signed, Int.max_signed)
  | Sgn _ n =>
      if zlt n Int.zwordsize
      then (let x := two_p (n-1) in (-x, x-1))
      else (Int.min_signed, Int.max_signed)
  | _ => (Int.min_signed, Int.max_signed)
  end.

(*
Lemma sintv_sound:
  forall n v, vmatch (Vint n) v -> fst (sintv v) <= Int.signed n <= snd (sintv v).
Proof.
  intros. inv H; simpl; try (apply Int.signed_range).
- omega.
- destruct (zlt n0 Int.zwordsize); simpl.
+ rewrite is_uns_zero_ext in H2. rewrite <- H2. 
  assert (Int.unsigned (Int.zero_ext n0 n) = Int.unsigned n mod two_p n0) by (apply Int.zero_ext_mod; omega).
  exploit (Z_mod_lt (Int.unsigned n) (two_p n0)). apply two_p_gt_ZERO; auto. intros.
  replace (Int.signed (Int.zero_ext n0 n)) with (Int.unsigned (Int.zero_ext n0 n)).
  rewrite H. omega. 
  unfold Int.signed. rewrite zlt_true. auto. 
  assert (two_p n0 <= Int.half_modulus). 
  { change Int.half_modulus with (two_p (Int.zwordsize - 1)). 
    apply two_p_monotone. omega. }
  omega.  
+ apply Int.signed_range.
- destruct (zlt n0 (Int.zwordsize)); simpl.
+ rewrite is_sgn_sign_ext in H2 by auto. rewrite <- H2. 
  exploit (Int.sign_ext_range n0 n). omega. omega. 
+ apply Int.signed_range.
Qed.

Lemma cmp_intv_sound:
  forall c n1 v1 n2,
  vmatch (Vint n1) v1 ->
  cmatch (Val.cmp_bool c (Vint n1) (Vint n2)) (cmp_intv c (sintv v1) (Int.signed n2)).
Proof.
  intros. simpl. replace (Int.cmp c n1 n2) with (zcmp c (Int.signed n1) (Int.signed n2)).
  apply zcmp_intv_sound; apply sintv_sound; auto.
  destruct c; simpl; rewrite ? Int.eq_signed; auto.
  unfold Int.lt. destruct (zle (Int.signed n1) (Int.signed n2)); [rewrite zlt_false|rewrite zlt_true]; auto; omega.
  unfold Int.lt. destruct (zle (Int.signed n2) (Int.signed n1)); [rewrite zlt_false|rewrite zlt_true]; auto; omega.
Qed.

Lemma cmp_intv_sound_2:
  forall c n1 v1 n2,
  vmatch (Vint n1) v1 ->
  cmatch (Val.cmp_bool c (Vint n2) (Vint n1)) (cmp_intv (swap_comparison c) (sintv v1) (Int.signed n2)).
Proof.
  intros. rewrite <- Val.swap_cmp_bool. apply cmp_intv_sound; auto. 
Qed. 
*)
(** Comparisons *)
Definition not_a_pointer (i : int) : bool :=
  Int.eq i Int.zero || Int.eq i Int.mone.

Definition ceq  (i : int) : abool :=
  if not_a_pointer i
  then Just false
  else Btop.

Definition clt (i : int) : abool :=
  if Int.eq i Int.mone
  then Just true
  else if Int.eq i Int.zero
       then Just false
       else Btop.

Definition cmeet (b1 b2 : abool) : abool :=
  match b1, b2 with
    | Btop , x | x , Btop => x
    | Maybe b1 , Just b2
    | Just b2 , Maybe b1  => if eqb b1 b2 then Just b2 else Bnone
    | Bnone , _ | _ , Bnone => Bnone
    | Just b1 , Just b2   => if eqb b1 b2 then Just b1 else Bnone
    | Maybe b1 , Maybe b2   => if eqb b1 b2 then Maybe b1 else Bnone
  end.

Lemma eval_expr_val_of_bool :
  forall b b' a u,
    eSexpr a u (Eval (val_of_bool b)) =
    eSexpr a u (Eval (val_of_bool b')) -> 
    b = b'.
Proof.
  intros.
  simpl in H.
  assert (Vtrue <> Vfalse).
  {   unfold Vtrue, Vfalse.
      generalize  Int.one_not_zero.
      congruence.
  }
  destruct b ; destruct b' ; simpl in H ; try congruence.
Qed.


Lemma same_eval_val_of_bool :
  forall b b',
    same_eval (Eval (val_of_bool b)) (Eval (val_of_bool b')) -> 
    b = b'.
Proof.
  intros.
  unfold same_eval in H.
  eapply eval_expr_val_of_bool with (a:=(fun _ => Int.zero)) (u :=fun _ _ => Byte.zero);
    eauto.
Qed.
  
Lemma is_wk_cst_bool :
  forall b b' e
         (WK : is_wk_constant (val_of_bool b) e)
         (CST : is_constant (val_of_bool b') e),
   ecmatch e (if eqb b b' then Just b' else Bnone).
Proof.
  unfold is_constant, is_wk_constant in *.
  intros.
  case_eq (eqb b b') ; constructor.
  -
    rewrite eqb_true_iff in H.
    subst.
    repeat intro.
    unfold same_eval in CST.
    generalize (CST cm em).
    generalize (WK cm em).
    intros. auto.
  -   
    rewrite eqb_false_iff in H.
    repeat intro.
    unfold same_eval in CST.
    generalize (CST cm em).
    generalize (WK cm em).
    intros.
    inv H0; auto.
    rewrite <- H1 in H4.
    apply eval_expr_val_of_bool in H4.
    congruence.
Qed.
    
Lemma eqb_sym : forall b b', eqb b b' = eqb b' b.
Proof.
  destruct b ; destruct b' ; reflexivity.
Qed.
  


Definition cor (b b' : abool) : abool :=
  match b , b' with
    | Bnone , _ | _ , Bnone => Bnone
    | Just b, Just b' => Just (b || b')
    | Maybe b , Maybe b' => Maybe (b || b')
    | Just b , Maybe b' | Maybe b' , Just b => Maybe (b || b')
    |   _ , Btop | Btop , _ => Btop

  end.


Definition ccomp (c : comparison) (i:int) : abool :=
  match c with
    | Ceq => ceq i
    | Cne => cnot (ceq i)
    | Clt => clt i
    | Cle => cor  (clt i) (ceq i)
    | Cgt => cnot (cor (clt i) (ceq i) )
    | Cge => cnot (clt i)
  end.
    
Definition pcmp_int (c : comparison) (p : aptr) (i : int) : abool :=
  match p with
    | Pbot => Bnone (* Is this really bot? *)
    | Pcst => Btop
    | Gl id ofs => if in_bound_glob id ofs 
                   then ccomp c i
                   else Btop
    | Stk ofs    => if in_bound_stack ofs
                   then ccomp c i
                   else Btop
    |  _        => Btop
  end.

Definition cmpu_bool (c: comparison) (v w: aval) : abool :=
  match v, w with
  | I i1, I i2 => Just (Int.cmpu c i1 i2)
  | Ptr p, I i => pcmp_int c p i
  | I i, Ptr p => pcmp_int (swap_comparison c) p i
  | Ptr p1, Ptr p2 => pcmp c p1 p2
  | Ptr p1, ( Uns p2 _ | Sgn p2 _) =>
    (* club (pcmp c p1 p2) (cmp_different_blocks c) 
         -- if p2 is not a constant, this does not make sense *)
    Btop
  | ( Uns p1 _ | Sgn p1 _), Ptr p2 => Btop (*club (pcmp c p1 p2) (cmp_different_blocks c)*)
  | _, I i => (cmp_intv c (uintv v) (Int.unsigned i)) 
  | I i, _ => (cmp_intv (swap_comparison c) (uintv w) (Int.unsigned i))
  | _, _ => Btop
  end.

Lemma not_a_pointer_sound :
  forall ofs b a align bound
         (BD : in_bound (Int.unsigned ofs) (bound b))
         (COMPAT : compat Int.max_unsigned bound align a)
         (NOTPTR : not_a_pointer (Int.add (a b) ofs) = true),
    False.
Proof.
  intros.
  exploit addr_space ; eauto.
  unfold not_a_pointer in NOTPTR.
  rewrite orb_true_iff in NOTPTR.
  destruct NOTPTR;
    apply Cop.int_eq_true in H;
    rewrite H.
  rewrite Int.unsigned_zero.  omega.
  unfold Int.max_unsigned.
  rewrite Int.unsigned_mone.  
  compute. intuition congruence.
Qed.  

Lemma cmpu_bool_negate :
  forall c e e',
         same_eval
         (Val.cmpu_bool c e e')
         (Val.notbool (Val.cmpu_bool (negate_comparison c) e e')).
Proof.
  repeat intro.
  unfold Val.cmpu_bool, Val.notbool.
  simpl.
  unfold ExprEval.cmpu_bool.
  destruct (eSexpr cm em e) ; destruct (eSexpr cm em e') ; try reflexivity.
  rewrite Int.negate_cmpu.
  simpl.
  destruct (Int.cmpu c i i0); auto.
Qed.


Lemma same_eval_cmpu_le :
  forall x y, 
  same_eval
    (Val.cmpu_bool Cle x y)
    (Val.or (Val.cmpu_bool Clt x y)
            (Val.cmpu_bool Ceq x y)).
Proof.
  repeat intro.
  simpl.
  destruct (eSexpr cm em x) , (eSexpr cm em y) ; simpl ; try reflexivity.
  unfold Int.ltu.
  destruct (zlt (Int.unsigned i0) (Int.unsigned i)) ; try reflexivity.
  destruct (zlt (Int.unsigned i) (Int.unsigned i0)) ; try reflexivity.
  omega.
  predSpec Int.eq Int.eq_spec i i0; try reflexivity.
  simpl. subst. omega.
  simpl.
  destruct (zlt (Int.unsigned i) (Int.unsigned i0)) ; try reflexivity.
  predSpec Int.eq Int.eq_spec i i0; try reflexivity.  
  predSpec Int.eq Int.eq_spec i i0; try reflexivity.  
  assert (Int.unsigned i = Int.unsigned i0) by omega.
  apply inj_unsigned  in H0; auto.
  tauto.
Qed.

Definition is_val_bool (v : val) :=
  v = Vundef \/ v = Vfalse \/ v = Vtrue.

Lemma is_bool_or :
  forall e1 e2  
  ,
    is_bool e1 -> is_bool e2 -> 
    is_bool (Val.or e1 e2).
Proof.
  repeat intro.
  simpl.
  destruct (H a u).
  destruct (H0 a u).
  destruct H1 ; destruct H2.
  destruct (eSexpr a u e1), (eSexpr a u e2) ;
    try (exists Int.zero ; intuition constructor);
    try (exists Int.one ; intuition constructor).
  simpl.
  inv H1.
  inv H2.
  intuition subst ; 
  try (exists Int.zero ; intuition constructor);
    try (exists Int.one ; intuition constructor).
Qed.  
  
Lemma or_bool_sound : forall e1 v1 e2 v2,
                        ecmatch e1 v1 ->
                        ecmatch e2 v2 ->
                        ecmatch (Val.or e1 e2) (cor v1 v2).
Proof.
  intros.
  inv H ; simpl ; try constructor; unfold Val.or.
  - 
    rew_cst H1 ; repeat intro ; reflexivity.
  - 
    rew_cst H1.
    inv H0 ; try constructor.
    +
    rew_cst H.
    repeat intro ; simpl.
    destruct (eSval cm (val_of_bool b)) ; reflexivity.
    +
    rew_cst H.
    repeat intro ; try reflexivity.
    destruct b ; destruct b0 ; reflexivity.
    +
      repeat intro.
      specialize (H a u).
      inv H.
      simpl. rewrite H3.
      destruct b ; destruct b0 ; constructor.
      simpl. rewrite <- H2.
      destruct b ; destruct b0 ; constructor.
    +  apply is_bool_or; auto with va.
  -
    inv H0 ; constructor.
    +
    rew_cst H.
    repeat intro ; simpl.
    destruct (eSexpr cm em e1) ; reflexivity.
    +
    repeat intro.
    simpl.
    rew_cst H.
    specialize (H1 a u).
    inv H1.
    erewrite H; eauto. erewrite <- H ; eauto.
    rewrite H3.
    destruct b ; destruct b0 ; constructor.
    auto.
    +
    repeat intro.
    specialize (H1 a u).
    specialize (H a u).
    simpl.
    inv H1 ; inv H ; try constructor.
    rewrite H3 ; rewrite H2 ; simpl.
    destruct b ; destruct b0 ; constructor.
    rewrite H3.
    destruct b ; simpl ; constructor.
    +
      apply is_bool_or; auto.
      eapply is_wk_constant_is_bool ; eauto.
  - 
    inv H0 ; constructor.
    rew_cst H.
    repeat intro ; simpl.
    destruct (eSexpr cm em e1) ; reflexivity.
    apply is_bool_or ; eauto with va.
    rew_cst H ; auto with va.
    apply is_bool_or ; eauto with va.
    apply is_bool_or ; eauto with va.
Qed.      

    
Lemma cmpu_pointer_int_sound :
  forall v p i w c
         (PMATCH : epmatch v p)
         (CONST  : is_constant (Vint i) w),
    ecmatch (Val.cmpu_bool c v w) (pcmp_int c p i).
Proof.
  intros.
  unfold Val.cmpu_bool.
  rew_cst CONST.
  clear CONST.
(*  assert (DFL : forall b ofs v
                       (PTR : is_pointer b ofs v)
                       (BD : in_bound (Int.unsigned ofs) (bound b)),
                  ecmatch (Val.cmpu_bool c v (Eval (Vint i))) (ccomp c i)).
  {
    intros.
    unfold is_pointer in PTR.
    assert (EQ : ecmatch (Val.cmpu_bool Ceq v0 (Eval (Vint i))) (ceq i)).
    {
      unfold Val.cmpu_bool.
      rewrite <- PTR.
      unfold ceq.
      case_eq (not_a_pointer i); try constructor.
      repeat intro ; simpl.
      predSpec Int.eq Int.eq_spec (Int.add (a b) ofs) i; try constructor.
      exfalso.
      subst.
      eapply not_a_pointer_sound ; eauto.
      apply is_bool_cmpu_bool.
    }
    assert (LT : ecmatch (Val.cmpu_bool Clt v0 (Eval (Vint i))) (clt i)).
    {
      unfold Val.cmpu_bool.
      rewrite <- PTR.
      unfold clt.
      predSpec Int.eq Int.eq_spec  i Int.mone; try constructor.
      - 
        repeat intro.
        simpl.
        subst.
        unfold Int.ltu.
        destruct (zlt (Int.unsigned (Int.add (a b) ofs)) (Int.unsigned Int.mone)); auto.
        exploit addr_space ; eauto.
        unfold Int.max_unsigned.
        rewrite Int.unsigned_mone in g.
        omega.
      - 
        predSpec Int.eq Int.eq_spec  i Int.zero; try constructor.        
        subst.
        repeat intro.
        simpl. unfold Int.ltu.
        destruct (zlt (Int.unsigned (Int.add (a b) ofs)) (Int.unsigned Int.zero)); auto.        
        exfalso.
        exploit addr_space ; eauto.
        rewrite Int.unsigned_zero in l.
        omega.
        apply is_bool_cmpu_bool.
    }
    destruct c ; simpl ;auto.
    - (* cne *)
      rewrite cmpu_bool_negate.
      apply ecnot_sound.
      simpl ; auto.
    - (* cle *)
      rewrite same_eval_cmpu_le.
      apply or_bool_sound ; auto.
    - (* cgt *)
      rewrite cmpu_bool_negate.
      simpl.
      apply ecnot_sound.
      rewrite same_eval_cmpu_le.
      apply or_bool_sound ; auto.
    - (* cge *)
      rewrite cmpu_bool_negate.
      simpl.
      apply ecnot_sound.      
      auto.
  } *)
  inv PMATCH ; simpl; try constructor; try apply is_bool_cmpu_bool.
Qed.

(*  - case_eq (in_bound_glob id ofs).
  intros.
  unfold in_bound_glob in H1.
  revert H1.
  case_eq (glob_size ms id) ; try congruence.
  intros.
  rewrite in_boundb_bound in H2.
  eapply DFL ; eauto.
  eapply in_bound_glob_size ; eauto.
  constructor.
  apply is_bool_cmpu_bool ; eauto with va.
  - case_eq (in_bound_stack ofs).
  intros.
  eapply DFL ; eauto.
  eapply in_bound_stk_size ; eauto.
  unfold in_bound_stack in H1.
  rewrite in_boundb_bound in H1.
  auto.
  constructor.
  apply is_bool_cmpu_bool ; eauto with va.
Qed.
 *)
  
Lemma cmpu_bool_swap_comparison :
  forall c e e',
         same_eval
         (Val.cmpu_bool c e e')
         (Val.cmpu_bool (swap_comparison c) e' e).
Proof.
  repeat intro.
  unfold Val.cmpu_bool.
  simpl.
  unfold ExprEval.cmpu_bool.
  destruct (eSexpr cm em e) ; destruct (eSexpr cm em e') ; try reflexivity.
  rewrite Int.swap_cmpu.
  reflexivity.
Qed.




Lemma cmpu_bool_sound:
  forall  c v w x y, evmatch v x -> evmatch w y -> ecmatch (Val.cmpu_bool c v w) (cmpu_bool c x y).
Proof.
  intros.
(*  assert (IP: forall i b ofs,
    cmatch (Val.cmpu_bool valid c (Vint i) (Vptr b ofs)) (cmp_different_blocks c)).
  {
    intros. simpl. destruct (Int.eq i Int.zero && (valid b (Int.unsigned ofs) || valid b (Int.unsigned ofs - 1))).
    apply cmp_different_blocks_sound. apply cmp_different_blocks_none.
  }
  assert (PI: forall i b ofs,
    cmatch (Val.cmpu_bool valid c (Vptr b ofs) (Vint i)) (cmp_different_blocks c)).
  {
    intros. simpl. destruct (Int.eq i Int.zero && (valid b (Int.unsigned ofs) || valid b (Int.unsigned ofs - 1))).
    apply cmp_different_blocks_sound. apply cmp_different_blocks_none.
  } *)
  inv H ; inv H0 ; unfold cmpu_bool; try (simpl ; constructor; fail);
  try (constructor ; apply is_bool_cmpu_bool ; eauto with va);
  try (unfold Val.cmpu_bool; rew_cst H1;apply cmpu_intv_sound_2; constructor ; auto; fail);
  try (unfold Val.cmpu_bool; rew_cst H;apply cmpu_intv_sound; constructor ; auto; fail).
  - (* consts *)
    constructor.
    unfold Val.cmpu_bool.
    rew_cst H1. rew_cst H.
    repeat intro.
    simpl.
    destruct (Int.cmpu c i i0) ; reflexivity.
  - (* pointer int *)
    rewrite cmpu_bool_swap_comparison.
    eapply cmpu_pointer_int_sound ; eauto.
  -      eapply cmpu_pointer_int_sound ; eauto.
  - 
    eapply pcmp_sound; auto.
Qed.

Definition cmp_bool (c: comparison) (v w: aval) := Btop.

Lemma cmp_bool_sound:
  forall c v w x y, evmatch v x -> evmatch w y -> ecmatch (Val.cmp_bool c v w) (cmp_bool c x y).
Proof.
 intros.
 unfold cmp_bool.
 constructor.
 repeat intro.
 unfold Val.cmp_bool. simpl.
 destruct (eSexpr a u v); destruct (eSexpr a u w) ; simpl;
 try ( exists Int.zero ; repeat constructor; fail).
 destruct (Int.cmp c i i0).
 exists Int.one ; repeat split. constructor. tauto.
 exists Int.zero ; repeat split. constructor. tauto.
Qed.


(*
Definition cmp_bool (c: comparison) (v w: aval) : abool :=
  match v, w with
  | I i1, I i2 => Just (Int.cmp c i1 i2)
  | _, I i => cmp_intv c (sintv v) (Int.signed i)
  | I i, _ => cmp_intv (swap_comparison c) (sintv w) (Int.signed i)
  | _, _ => Btop
  end.

Lemma cmp_bool_sound:
  forall c v w x y, vmatch v x -> vmatch w y -> cmatch (Val.cmp_bool c v w) (cmp_bool c x y).
Proof.
  intros. 
  unfold cmp_bool; inversion H; subst; inversion H0; subst;
  auto using cmatch_top, cmp_intv_sound, cmp_intv_sound_2, cmp_intv_None.
- constructor.
Qed.
 *)

Lemma eSval_bool : forall b a,
   eSval a (val_of_bool b) =
   (if b then Vtrue else Vfalse).
Proof.
  destruct b ; reflexivity.
Qed.

Definition cmpf_bool (c: comparison) (v w: aval) : abool :=
  match v, w with
  | F f1, F f2 => Just (Float.cmp c f1 f2)
  | _, _ => Btop
  end.

Lemma cmpf_is_bool : 
  forall c v w,  is_bool (Val.cmpf_bool c v w).
Proof.
  unfold Val.cmpf_bool.
  repeat intro ; simpl.
  generalize ((Values.Val.cmpf_bool c (eSexpr a u v) (eSexpr a u w))).
  intros.
  destruct o ; simpl.
  destruct b;
    try (exists Int.zero ; intuition constructor);
    try (exists Int.one ; intuition constructor).
  exists Int.zero ; intuition.
Qed.
  
Lemma cmpf_bool_sound:
  forall c v w x y, evmatch v x -> evmatch w y -> ecmatch (Val.cmpf_bool c v w) (cmpf_bool c x y).
Proof.
  intros.
  generalize (cmpf_is_bool c v w).
  inv H; try constructor; inv H0; try constructor;
  unfold Val.cmpf_bool in * ; auto.
  rew_cst  H1.
  rew_cst  H.
  repeat intro; simpl.
  apply eSval_bool.
Qed.


Definition cmpfs_bool (c: comparison) (v w: aval) : abool :=
  match v, w with
  | FS f1, FS f2 => Just (Float32.cmp c f1 f2)
  | _, _ => Btop
  end.

Lemma cmpfs_is_bool : 
  forall c v w,  is_bool (Val.cmpfs_bool c v w).
Proof.
  unfold Val.cmpfs_bool.
  repeat intro ; simpl.
  generalize ((Values.Val.cmpfs_bool c (eSexpr a u v) (eSexpr a u w))).
  intros.
  destruct o ; simpl.
  destruct b;
    try (exists Int.zero ; intuition constructor);
    try (exists Int.one ; intuition constructor).
  exists Int.zero ; intuition.
Qed.


Lemma cmpfs_bool_sound:
  forall c v w x y, evmatch v x -> evmatch w y -> ecmatch (Val.cmpfs_bool c v w) (cmpfs_bool c x y).
Proof.
  intros.
  generalize (cmpfs_is_bool c v w).
  inv H; try constructor; inv H0; try constructor;
  unfold Val.cmpfs_bool in * ; auto.
  rew_cst  H1.
  rew_cst  H.
  repeat intro; simpl.
  apply eSval_bool.
Qed.


Definition maskzero (x: aval) (mask: int) : abool :=
  match x with
  | I i => Just (Int.eq (Int.and i mask) Int.zero)
  | Uns p n => if Int.eq (Int.zero_ext n mask) Int.zero then Maybe true else Btop
  | _ => Btop
  end.

Lemma is_bool_of_optbool :
  forall v,
  exists i : int,
     Values.Val.lessdef
       (Val.of_optbool v) (Vint i) /\ (i = Int.zero \/ i = Int.one).
Proof.
  intros.
  destruct v; simpl ; try destruct b ; 
  try (exists Int.zero  ; intuition constructor);
  try (exists Int.one  ; intuition constructor).
Qed.

Lemma maskzero_is_bool : forall v m,
   is_bool (Val.maskzero_bool v m).
Proof.
  intros.
  repeat intro.
  unfold Val.maskzero_bool.
  apply is_bool_of_optbool.
Qed.

  
Lemma maskzero_sound:
  forall mask v x,
  evmatch v x ->
  ecmatch (Val.maskzero_bool v mask) (maskzero x mask).
Proof.
  intros.
  assert  (MSK := maskzero_is_bool v mask). 
  unfold Val.maskzero_bool in *.
  inv H; simpl; auto with va; try constructor; auto.
  -
    unfold Val.maskzero_bool.
    rew_cst H0.
    repeat intro.
    simpl.
    apply eSval_bool.
  - 
    predSpec Int.eq Int.eq_spec (Int.zero_ext n mask) Int.zero; auto with va;
    constructor.
    repeat intro.
    unfold is_unsigned in H1.
    destruct (H1 a u); intuition.
    rewrite is_uns_zero_ext in H5.
    inversion H4 ; clear H4; subst v0 ; simpl ; try constructor.
    rewrite H7 ; simpl.
    predSpec Int.eq Int.eq_spec (Int.and x mask) Int.zero; auto with va.
    exfalso.
    apply H3.
    rewrite Int.zero_ext_and in * by auto.
    rewrite <- H5.
    rewrite Int.and_assoc.
    rewrite Int.and_commut in H.
    rewrite H.
    rewrite Int.and_zero; auto.
    rewrite <- H6.
    simpl. constructor.
    auto.
Qed.

Definition of_optbool (p : aptr) (ab: abool) : aval :=
  match ab with
  | Just b => I (if b then Int.one else Int.zero)
  | _ => Uns p 1
  end.

Lemma ecmatch_is_bool :
  forall ob ab,
    ecmatch ob ab -> is_bool ob.
Proof.
  intros.
  inv H ; eauto with va.
  rew_cst H0. auto with va.
  rew_cst H0. auto with va.
Qed.
  
Lemma of_optbool_sound:
  forall ob ab p (PMATCH : epmatch ob p), ecmatch ob ab -> evmatch  ob (of_optbool p ab).
Proof.
  intros.
  assert (DEFAULT: evmatch ob (Uns p 1)).
  {
    constructor; auto.
    omega.
    repeat intro.
    apply ecmatch_is_bool in H.
    destruct (H a u).
    exists x ; intuition subst.
    unfold is_uns. intros. rewrite Int.bits_zero.
    reflexivity.
    unfold is_uns. intros. rewrite Int.bits_one.
    unfold proj_sumbool.
    destruct (zeq m 0); try omega.
    reflexivity.
  }
  inv H ; simpl ; auto.
  - rew_cst H0.
    constructor.
    destruct b ; repeat intro ; reflexivity.
Qed.

Definition resolve_branch (ab: abool) : option bool :=
  match ab with
  | Just b => Some b
  | Maybe b => Some b
  | _ => None
  end.

Lemma resolve_branch_sound:
  forall e ab b',
    ecmatch e ab ->
    resolve_branch ab = Some b' -> is_wk_constant (val_of_bool b') e.
Proof.
  intros. inv H; simpl in H0; try congruence.
  inv H0 ; auto with va.
  rew_cst  H1.
  destruct b' ; constructor.
  inv H0 ; assumption.
Qed.

(*
Lemma resolve_branch_sound:
  forall b ab b',
  cmatch (Some b) ab -> resolve_branch ab = Some b' -> b' = b.
Proof.
  intros. inv H; simpl in H0; congruence.
Qed.
*)
(** Normalization at load time *)

Definition vnormalize (chunk: memory_chunk) (v: aval) :=
  match chunk, v with
  | Mint8signed, v => sign_ext 8 v
  | Mint8unsigned, v => zero_ext 8 v
  | Mint16signed, v => sign_ext 16 v
  | Mint16unsigned, v => zero_ext 16 v
  | Mint32, v => sign_ext 32 v
  | Mint64, L _ => v
  | Mint64, (Ptr p | Uns p _ | Sgn p _) => Ptr (poffset p)
  | Mfloat32, FS f => v
  | Mfloat64, F f => v
  | Many32, (I _ | Uns _ _ | Sgn _ _ | Ptr _  | FS _) => v
  | Many64, _ => v
  | _, v => ntop1 v
  end.

Lemma epmatch_undef_wt_expr : 
  forall v p
         (WT : ~ wt_expr v Tint)
         (PTR : epmatch v p),
   epmatch (Eval Vundef) p.
Proof.
  intros.
  inv PTR; try constructor ; depends_prf.
  - 
  econstructor ; eauto.
  repeat intro.
  unfold is_pointer,same_eval  in H0.
  specialize (H0 cm em).
  simpl in H0.
  symmetry in H0.
  apply expr_nu_type with (t:= Tint) in H0; simpl ; auto; try congruence.
  - 
  econstructor ; eauto.
  repeat intro.
  specialize (H0 cm em).
  simpl in H0.
  symmetry in H0.
  apply expr_nu_type with (t:= Tint) in H0; simpl ; auto; try congruence.
Qed.

Lemma vnormalize_sound:
  forall chunk v x (VMATCH : evmatch v x),
    evmatch (Val.load_result chunk v) (vnormalize chunk x).
Proof.
  intros.
  generalize sign_ext_sound.
  generalize zero_ext_sound.
  assert (DEFAULT: evmatch (Val.load_result chunk v) (ntop1 x)). 
  {
    unfold Val.load_result.
    destruct chunk ; 
      try (apply evmatch_ntop1 ; auto ; repeat constructor ; auto;fail).
    destruct (wt_expr_dec v Tint) ; auto.
    apply evmatch_ntop1 with (T:= fun x => x); repeat constructor; auto.
    destruct (wt_expr_dec v Tsingle) ; auto.
    apply evmatch_ntop1 with (T:= fun x => x); repeat constructor; auto.
    apply evmatch_ntop1 with (T:= fun v => (Eval Vundef)) (v:=v); repeat constructor; auto.
    apply evmatch_ntop1 with (T:= fun x => x); repeat constructor; auto.
  }
  intros.
  case_eq chunk; simpl ; intros ; eauto.
  -
    apply H0 ; auto. omega.
  - apply H0 ; auto. omega.
  - apply H0 ; auto ; omega.
  -
    subst.
    destruct x ; try apply DEFAULT.
    constructor.
    inv VMATCH.
    rew_cst H3.
    repeat intro.
    simpl.
    rewrite Int64.sign_ext_above.
    reflexivity.
    compute. congruence.
  - 
    subst.
    destruct x ; try apply DEFAULT.
    constructor.
    inv VMATCH.
    rew_cst H3.
    repeat intro.
    reflexivity.
  - 
    subst.
    destruct x ; try apply DEFAULT.
    constructor.
    inv VMATCH.
    rew_cst H3.
    repeat intro.
    reflexivity.
  - 
    subst.
    simpl in DEFAULT.
    destruct (wt_expr_dec v Tint).
    +
    destruct x ; try apply DEFAULT ; auto.
    + 
      destruct (wt_expr_dec v Tsingle).
      destruct x  ; try apply DEFAULT ; auto.
      {
      destruct x  ; try apply DEFAULT ; auto.
      - 
      inv VMATCH.
      unfold is_constant in H3.
      constructor.
      repeat intro.
      simpl. 
      specialize (H3 cm em).
      simpl in H3.
      symmetry in H3.
      apply expr_nu_type with (t:= Tint) in H3; simpl ; auto; try congruence.
      - 
      inv VMATCH.
      constructor; auto.
      repeat intro.
      unfold is_unsigned in H5.
      destruct (H5 a u).
      destruct H1.
      simpl.  exists x ; simpl ; repeat constructor ; auto. 
      eapply epmatch_undef_wt_expr ; eauto.
      - 
      inv VMATCH.
      constructor; auto.
      repeat intro. 
      destruct (H5 a u).
      destruct H1.
      simpl.  exists x ; simpl ; repeat constructor ; auto. 
      eapply epmatch_undef_wt_expr ; eauto.
      -
        inv VMATCH.
        constructor.
        repeat intro.
        simpl. 
        specialize (H3 cm em).
        simpl in H3.
        symmetry in H3.
        apply expr_nu_type with (t:= Tsingle) in H3; simpl ; auto; try congruence.
      - 
        inv VMATCH.
        constructor.
        eapply epmatch_undef_wt_expr ; eauto.        
      }

Qed.


Lemma vnormalize_cast_ptr:
  forall chunk m b ofs v p,
  Mem.load chunk m b ofs = Some v ->
  epmatch v p ->
  evmatch v (vnormalize chunk (Ptr p)).
Proof.
  intros.
  exploit Mem.load_cast; eauto. 
  exploit Mem.load_type; eauto. 
  intros.
  assert (MATCH : evmatch v (Ptr p)).
   constructor ; auto.
   clear H0.
  destruct chunk;  unfold vnormalize;  
  try rewrite H2; try apply sign_ext_sound ; 
  try apply zero_ext_sound ; auto ; try omega.
  -
  inv MATCH ; constructor. apply poffset_sound; auto.
  -
  apply evmatch_ntop1 with (T :=fun x => x);
  repeat constructor; auto. inv MATCH ; auto.
  -
  inv MATCH.
  apply evmatch_ntop1 with (T :=fun x => x);                                           
    repeat constructor; auto. 
Qed.

Lemma vnormalize_cast:
  forall chunk m b ofs v p,
  Mem.load chunk m b ofs = Some v ->
  evmatch v p ->
  evmatch v (vnormalize chunk p).
Proof.
  intros.
  exploit Mem.load_cast; eauto. 
  exploit Mem.load_type; eauto.
  assert (PTR := vnormalize_cast_ptr chunk m b ofs v).
  assert (TOP : evmatch v (ntop1 p)).
   apply evmatch_ntop1 with (T:= fun x => x).
   constructor. auto.
  intros.
  destruct chunk;  unfold vnormalize;  
  try rewrite H2; try apply sign_ext_sound ; 
  try apply zero_ext_sound ; auto ; try omega.
  -
    destruct p ; try apply TOP.
    constructor.
    inv H0; auto.
  - 
    destruct p ; try apply TOP.
    constructor.
    inv H0; auto.
  - 
    destruct p ; try apply TOP.
    constructor.
    inv H0; auto.
  - 
    destruct p ; try apply TOP; auto.
Qed.


Remark poffset_monotone:
  forall p q, epge p q -> epge (poffset p) (poffset q).
Proof.

  intros.
  destruct p ; destruct q ; simpl in * ; tauto.
Qed.


Lemma epge_poffset_Pcst' :
  forall p,
    epge p Pcst -> 
    epge (poffset p) Pcst.
Proof.
  destruct p ; simpl ; auto.
Qed.  

Hint Resolve epge_poffset_Pcst epge_poffset_Pcst' poffset_monotone : va.
Hint Resolve epge_refl : va.
Hint Resolve evge_refl : va.

Lemma sgn_mono :
  forall p q n n',
    n >= n' -> 
    epge p q -> 
    evge (sgn p n) (sgn q n').
Proof.
  intros.
  unfold sgn.
  intros.
  repeat case_match ; intros ; try constructor ; auto with va ; omega.
Qed.

Lemma uns_mono :
  forall p q n n',
    n >= n'  -> 
    epge p q -> 
    evge (uns p n) (uns q n').
Proof.
  unfold uns.
  intros.
  repeat case_match ; try constructor ; auto ; intros ; try omega.
Qed.


Hint Resolve sgn_mono  uns_mono : va.

Lemma is_bot_sgn : forall n,
     is_bot (sgn Pbot n).
Proof.
   unfold sgn.
   intros.
   repeat case_match ; reflexivity.
Qed       .


Lemma sign_ext_mono :
  forall x y n, 
    n > 0 -> 
    evge x y -> 
    evge (sign_ext n x) (sign_ext n y).
Proof with (eauto with va).
  intros. unfold sign_ext.
  inv H0 ; simpl; try (constructor ; auto ; fail).
  - 
    destruct (zlt n Int.zwordsize).
    destruct (zlt n0 n).
  +
    constructor; auto.
    apply is_sign_ext_uns...
    eapply epge_poffset_Pcst'; eauto.
  +
    eapply evge_trans with (v := Sgn (poffset p) n).
    apply evge_sgn_sgn'.
    constructor ; auto.
    omega.
    apply is_sign_ext_sgn ; auto with va.
    eapply epge_poffset_Pcst'; eauto.    
  +
    constructor ; auto with va.
    repeat intro.
    rewrite Int.sign_ext_above ; auto.
  - 
    destruct (zlt n Int.zwordsize).
    eapply evge_trans with (v := Sgn (provenance (Ptr p)) n).
    apply evge_sgn_sgn'.
    constructor ; auto.
    omega.
    apply is_sign_ext_sgn ; auto with va.
    eapply epge_poffset_Pcst'; eauto.    
    constructor; auto.
  - 
    destruct (zlt n Int.zwordsize).
    apply sgn_mono. omega.
    unfold provenance ; simpl...
    unfold sgn ; repeat case_match ; try constructor...
  - 
    destruct (zlt n Int.zwordsize).
    apply sgn_mono; try omega. unfold provenance ; simpl...
    unfold sgn ; repeat case_match ; try constructor...
  - 
    destruct (zlt n Int.zwordsize).
    apply sgn_mono ; try omega. unfold provenance ; simpl...
    unfold sgn ; repeat case_match ; try constructor...
  - 
    unfold sgn.
    repeat case_match ; try constructor ; intros;  try xomega...
  -
    destruct (zlt n Int.zwordsize).
    + unfold sgn.
    repeat case_match ; try constructor...
    apply is_sign_ext_sgn ; try omega.
    assert (n0 <= 8 \/ n <= 8) by (zify ; omega).
    destruct H4 ; auto.
    left.
    eapply is_sgn_mon; eauto.
    apply is_sign_ext_sgn ; try omega.
    assert (n0 <= 16 \/ n <= 16) by (zify ; omega).
    destruct H5 ; auto.
    left.
    eapply is_sgn_mon; eauto.
    + 
      constructor; auto.
      apply is_sign_ext_sgn ; auto with va.      
  -
    destruct (zlt n Int.zwordsize); auto with va.
    constructor; auto.
  - 
    destruct (zlt n Int.zwordsize) ; try (constructor; auto with va;fail).
    destruct (zlt n2 n).
    +
      eapply evge_trans with (v := Sgn (poffset p1) (Z.min n1 n)).
      apply evge_sgn_sgn'.
      constructor; auto with va.
    + 
      apply sgn_mono...
  - 
    destruct (zlt n Int.zwordsize) ; try (constructor ; auto with va; fail).
    destruct (zlt n1 n).
    +
      eapply evge_trans with (v := Sgn (poffset p1) n).
      apply evge_sgn_sgn'.
      constructor; auto with va.
    + 
      apply sgn_mono...
      unfold provenance.
      simpl...
  - 
    destruct (zlt n Int.zwordsize) ; try (constructor ; auto with va; fail).
    apply sgn_mono...
    unfold provenance;   simpl...
  - 
    destruct (zlt n Int.zwordsize) ; try (constructor ; auto with va; fail).
    apply sgn_mono...
    unfold provenance;   simpl...
  - 
    destruct (zlt n Int.zwordsize) ; try (constructor ; auto with va; fail).
    destruct y ; try apply sgn_mono; unfold provenance; simpl...
    apply evge_sgn_i'...
    apply is_sign_ext_sgn ; try omega.
    intuition.
    constructor.
    destruct (zlt n0 n)...
    apply evge_trans with (v:= Sgn Ptop n).
    apply evge_sgn_sgn'.
    constructor; auto...
    constructor.
    apply sgn_mono...
    constructor.
  - unfold is_bot in H1.
    unfold aptr_of_aval in H1.
    destruct y ; subst ; try congruence.
    constructor. repeat case_match ; try reflexivity. simpl.
    intros. apply is_bot_sgn.
    constructor.
    repeat case_match ; try reflexivity. simpl.
    intros. apply is_bot_sgn.
    constructor.
    repeat case_match ; try reflexivity. simpl.
    intros. apply is_bot_sgn.
Qed.
    Require Import Psatz.


Lemma is_bot_uns : forall n,
     is_bot (uns Pbot n).
Proof.
   unfold uns.
   intros.
   repeat case_match ; reflexivity.
Qed       .

Lemma zero_ext_bot : 
      forall n x, is_bot x -> 
      is_bot (zero_ext n x).
Proof.
 intros.
 unfold is_bot, aptr_of_aval in H.
 destruct x ; try congruence ; try reflexivity;
 unfold zero_ext.
 - subst.
  case_eq (zlt n Int.zwordsize || not_int (Uns Pbot n0)).
  simpl. intros.
  apply is_bot_uns.
  simpl. reflexivity.
 - subst.
   repeat case_match; simpl; try reflexivity.
   intros.
   apply is_bot_uns.
 - subst.
   repeat case_match; simpl; try reflexivity.
   intros.
   apply is_bot_uns.
Qed.

Lemma is_bot_bool_true_iff : forall x, is_bot_bool x = true <-> is_bot x.
Proof.
  unfold is_bot_bool, is_bot.
  intro. destruct (aptr_of_aval x) ; simpl ; intuition congruence.
Qed.

Lemma is_bot_bool_false_iff : forall x, is_bot_bool x = false <-> ~ is_bot x.
Proof.
  unfold is_bot_bool, is_bot.
  intro. destruct (aptr_of_aval x) ; simpl ; intuition congruence.
Qed.


Lemma zero_ext_mono :
  forall x y n, 
    n > 0 -> 
    evge x y -> 
    evge (zero_ext n x) (zero_ext n y).
Proof with (eauto with va).
  intros. 
  case_eq (is_bot_bool y).
  * intros. 
    apply is_bot_bool_true_iff in H1.
    apply zero_ext_bot with (n:= n) in H1.
    apply evge_trans with (v:= Ptr Pbot).
    constructor. reflexivity.
    constructor. auto.
  * 
  intro.
  apply is_bot_bool_false_iff in H1.
  rename H1 into NBOT.
  unfold zero_ext.
  case_eq (zlt n Int.zwordsize || not_int x) ;
    case_eq (zlt n Int.zwordsize || not_int y).
  intros.
  rewrite orb_true_iff in H1.
  rewrite orb_true_iff in H2.
  inv H0 ; simpl ;  try (constructor ; eauto with va ; fail).
  - 
    apply evge_uns_i'...
    apply is_zero_ext_uns.
    zify. intuition (subst ; try omega); intuition auto.
  - 
    apply evge_uns_i'...
    apply is_zero_ext_uns...
    unfold provenance ; simpl...
  -
    apply uns_mono ; unfold provenance ; simpl...
  - 
    apply uns_mono ; unfold provenance ; simpl...
  - 
    apply uns_mono ; unfold provenance ; simpl...
  - 
    apply uns_mono ; unfold provenance ; simpl...
  - 
    apply evge_uns_i'...
    simpl in *.
    apply is_zero_ext_uns...
    unfold provenance ; simpl...
  - 
    eapply uns_mono; try omega.
    unfold provenance ; simpl...
  - 
    eapply uns_mono; try lia.
    unfold provenance ; simpl...
  - 
    eapply uns_mono; try lia.
    unfold provenance ; simpl...
  - 
    eapply uns_mono; try lia.
    unfold provenance ; simpl...
  - 
    eapply uns_mono; try lia.
    unfold provenance ; simpl...
  - 
    simpl in *.
    destruct y.
    +
    apply evge_uns_i'...
    simpl in *.
    apply is_zero_ext_uns...
    unfold provenance ; simpl...
    +
    eapply uns_mono; try lia.
    unfold provenance ; simpl...
    +
    eapply uns_mono; try lia.
    unfold provenance ; simpl...
    +
    eapply uns_mono; try lia.
    unfold provenance ; simpl...
    +
    eapply uns_mono; try lia.
    unfold provenance ; simpl...
    +
    eapply uns_mono; try lia.
    unfold provenance ; simpl...
    +
    eapply uns_mono; try lia.
    unfold provenance ; simpl...
  - tauto.
  - 
    intros.
    rewrite orb_true_iff in H2.
    rewrite orb_false_iff in H1.
    intuition.
    unfold proj_sumbool in H3.
    destruct (zlt n Int.zwordsize) ; try congruence.
    eapply evge_trans ; eauto.
    destruct x; try (constructor ; simpl in H1 ; try congruence; fail).
    inv H0; simpl in * ; try congruence.
    inv H0; simpl in * ; try congruence.
    inv H0; simpl in * ; try congruence.
  - 
    intros.
    rewrite orb_true_iff in H1.
    rewrite orb_false_iff in H2.
    intuition.
    unfold proj_sumbool in H3.
    destruct (zlt n Int.zwordsize) ; try congruence.
    destruct x ; destruct y ; try (constructor ; simpl in H0 ; try congruence; fail); inv H0;
    simpl in * ; try congruence; try (constructor ; fail).
    +
    apply evge_trans with (v:= Ptr Pcst).
    constructor; auto.
    unfold uns. repeat case_match ; constructor; simpl; auto.
    +     apply evge_trans with (v:= Ptr Pcst).
    constructor; auto.
    unfold uns. repeat case_match ; constructor; simpl; auto.
    +      apply evge_trans with (v:= Ptr Pcst).
    constructor; auto.
    unfold uns. repeat case_match ; constructor; simpl; auto.
    -      
    intros.
    rewrite orb_false_iff in H2.
    rewrite orb_false_iff in H1.
    intuition.
Qed.

Lemma vnormalize_monotone:
  forall chunk x y,
  evge x y -> evge (vnormalize chunk x) (vnormalize chunk y).
Proof with (auto with va).
  intros chunk x y V. destruct chunk ; simpl.
- apply sign_ext_mono; auto; lia.
- apply zero_ext_mono; auto; lia.
- apply sign_ext_mono; auto; lia.
- apply zero_ext_mono; auto; lia.
- apply sign_ext_mono; auto; lia.  
- 
  unfold ntop1.
  inv V ;  try constructor ; unfold provenance ; simpl...
   unfold is_bot, aptr_of_aval in *.
   destruct y ; simpl in * ; subst ; try congruence; reflexivity.
- 
  unfold ntop1.
  inv V ;  try constructor ; unfold provenance ; simpl...
   unfold is_bot, aptr_of_aval in *.
   destruct y ; simpl in * ; subst ; try congruence; reflexivity.
- unfold ntop1.
  inv V ;  try constructor ; unfold provenance ; simpl...
   unfold is_bot, aptr_of_aval in *.
   destruct y ; simpl in * ; subst ; try congruence; reflexivity.
- unfold ntop1.
  inv V ;  try constructor ; unfold provenance ; simpl...
   unfold is_bot, aptr_of_aval in *.
   destruct y ; simpl in * ; subst ; try congruence; reflexivity.
-  auto.
Qed.



(** Abstracting memory blocks *)

Inductive acontent : Type :=
  | ACany
  | ACval (chunk: memory_chunk) (av: aval).

Definition eq_acontent : forall (c1 c2: acontent), {c1=c2} + {c1<>c2}.
Proof.
  intros. generalize chunk_eq eq_aval. decide equality. 
Defined.

Record ablock : Type := ABlock {
  ab_contents: ZMap.t acontent;
  ab_summary: aptr;
  ab_default: fst ab_contents = ACany
}.

Local Notation "a ## b" := (ZMap.get b a) (at level 1).

Definition ablock_init (p: aptr) : ablock :=
  {| ab_contents := ZMap.init ACany; ab_summary := p; ab_default := refl_equal _ |}.

Definition chunk_compat (chunk chunk': memory_chunk) : bool :=
  match chunk, chunk' with
  | (Mint8signed | Mint8unsigned), (Mint8signed | Mint8unsigned) => true
  | (Mint16signed | Mint16unsigned), (Mint16signed | Mint16unsigned) => true
  | Mint32, Mint32 => true
  | Mfloat32, Mfloat32 => true
  | Mint64, Mint64 => true
  | Mfloat64, Mfloat64 => true
  | Many32, Many32 => true
  | Many64, Many64 => true
  | _, _ => false
  end.

Definition ablock_load (chunk: memory_chunk) (ab: ablock) (i: Z) : aval :=
  match ab.(ab_contents)##i with
  | ACany => vnormalize chunk (Ptr ab.(ab_summary))
  | ACval chunk' av =>
      if chunk_compat chunk chunk'
      then vnormalize chunk av
      else vnormalize chunk (Ptr ab.(ab_summary))
  end.

Definition ablock_load_anywhere (chunk: memory_chunk) (ab: ablock) : aval :=
  vnormalize chunk (Ptr ab.(ab_summary)).

Function inval_after (lo: Z) (hi: Z) (c: ZMap.t acontent) { wf (Zwf lo) hi } : ZMap.t acontent :=
  if zle lo hi
  then inval_after lo (hi - 1) (ZMap.set hi ACany c)
  else c.
Proof.
  intros; red; omega.
  apply Zwf_well_founded.
Qed.

Definition inval_if (hi: Z) (lo: Z) (c: ZMap.t acontent) :=
  match c##lo with
  | ACany => c
  | ACval chunk av => if zle (lo + size_chunk chunk) hi then c else ZMap.set lo ACany c
  end.

Function inval_before (hi: Z) (lo: Z) (c: ZMap.t acontent) { wf (Zwf_up hi) lo } : ZMap.t acontent :=
  if zlt lo hi
  then inval_before hi (lo + 1) (inval_if hi lo c)
  else c.
Proof.
  intros; red; omega.
  apply Zwf_up_well_founded.
Qed.

Remark fst_inval_after: forall lo hi c, fst (inval_after lo hi c) = fst c.
Proof.
  intros. functional induction (inval_after lo hi c); auto.
Qed.

Remark fst_inval_before: forall hi lo c, fst (inval_before hi lo c) = fst c.
Proof.
  intros. functional induction (inval_before hi lo c); auto.
  rewrite IHt. unfold inval_if. destruct c##lo; auto. 
  destruct (zle (lo + size_chunk chunk) hi); auto.
Qed.

Definition evplub (av : aval) (ap : aptr) : aptr :=
  eplub (provenance av) ap.

Program Definition ablock_store (chunk: memory_chunk) (ab: ablock) (i: Z) (av: aval) : ablock :=
  {| ab_contents :=
       ZMap.set i (ACval chunk av)
         (inval_before i (i - 7)
            (inval_after (i + 1) (i + size_chunk chunk - 1) ab.(ab_contents)));
     ab_summary :=
       evplub  av ab.(ab_summary);
     ab_default := _ |}.
Next Obligation.
  rewrite fst_inval_before, fst_inval_after. apply ab_default. 
Qed.

Definition ablock_store_anywhere (chunk: memory_chunk) (ab: ablock) (av: aval) : ablock :=
  ablock_init (eplub (provenance av) ab.(ab_summary)).

Definition ablock_loadbytes (ab: ablock) : aptr :=  ab.(ab_summary).

Program Definition ablock_storebytes (ab: ablock) (p: aval) (ofs: Z) (sz: Z) :=
  {| ab_contents :=
       inval_before ofs (ofs - 7)
         (inval_after ofs (ofs + sz - 1) ab.(ab_contents));
     ab_summary :=
       evplub p ab.(ab_summary);
     ab_default := _ |}.
Next Obligation.
  rewrite fst_inval_before, fst_inval_after. apply ab_default.
Qed.

Definition ablock_storebytes_anywhere (ab: ablock) (p: aptr) :=
  ablock_init (eplub p ab.(ab_summary)).


Lemma epmatch_dep : 
  forall T
         (HT    : is_unop_trans T)
         v p
         (DEP   : is_dep p)
         (MATCH : epmatch v p),
    epmatch (T v) p.
Proof.
  induction 1 ; auto.
  - 
    intros.
    destruct p ; destruct v ; simpl in * ; intuition try congruence ; constructor; depends_prf.
  - 
    intros.
    inv MATCH ; try constructor ; repeat intro; simpl in * ; intuition try congruence ; try reflexivity.
  - 
    intros.
    specialize (IHHT _ _ DEP MATCH).
    revert IHHT.
    generalize (f v) as X.
    intros.
    clear MATCH.
    inv IHHT ; simpl in DEP ; try congruence ; try constructor ; depends_prf.
  - 
    intros.
    specialize (IHHT1 _ _ DEP MATCH).
    specialize (IHHT2 _ _ DEP MATCH).
    revert IHHT1 IHHT2.
    generalize (f1 v) as X.
    generalize (f2 v) as Y.
    intros.
    clear MATCH.
    inv IHHT1 ; inv IHHT2 ; simpl in DEP ; try congruence ; try constructor ; depends_prf.
Qed.


Lemma epmatch_dep2 : 
  forall T 
         (HT    : is_binop_trans T)
         v1 v2 p
         (DEP   : is_dep p)
         (MATCH1 : epmatch v1 p)
         (MATCH2 : epmatch v2 p),
    epmatch (T v1 v2) p.
Proof.
  induction 1 ; auto.
  - 
    intros.
    destruct p ; destruct v ; simpl in * ; intuition try congruence ; constructor; depends_prf.
  - 
    intros.
    destruct p ; try constructor ; repeat intro; simpl in * ; intuition try congruence ; try reflexivity.
  - 
    intros.
    specialize (IHHT _ _ _ DEP MATCH1 MATCH2).
    revert IHHT.
    generalize (f v1 v2) as X.
    intros.
    inv IHHT ; simpl in DEP ; try congruence ; try constructor ; depends_prf.
  - 
    intros.
    specialize (IHHT1 _ _ _ DEP MATCH1 MATCH2).
    specialize (IHHT2 _ _ _ DEP MATCH1 MATCH2).
    revert IHHT1 IHHT2.
    generalize (f1 v1 v2) as X.
    generalize (f2 v1 v2) as Y.
    intros.
    inv IHHT1 ; inv IHHT2 ; simpl in DEP ; try congruence ; try constructor ; depends_prf.
Qed.


Ltac find_trans V :=
  match goal with
    | |- ?Pred ?X ?P => 
      set (x := X) ; pattern V in x ; 
      match goal with
        | x := ?F V |- _ => change (Pred (F V) P)
      end
  end.


Lemma epmatch_to_bits : 
  forall p v chunk
         (DEP : is_dep p)
         (MATCH : epmatch v p),
    epmatch (to_bits chunk v) p.
Proof.
  intros.
  destruct chunk; simpl; repeat case_match; intros;
  try (find_trans v; apply epmatch_dep; repeat constructor; auto).
Qed.

Definition mvmatch  (mv : memval) (a : aptr) : Prop :=
  match mv with
    | Symbolic e _ _ => epmatch  e a
  end.


Lemma epmatch_inj_symbolic : 
  forall p mv n o e
         (DEP : is_dep p)
         (MATCH: epmatch e p)
         (HIN : In mv (inj_symbolic n e o)),
    mvmatch mv p.
Proof.
  intros.
  unfold inj_symbolic in HIN.
  repeat rewrite <- in_rev in HIN.
  unfold rev_if_be in HIN.
  assert (HIN' : In mv (inj_symbolic' n e o) -> mvmatch mv p).
  {
    clear HIN.
    unfold mvmatch.
    destruct mv.
    induction n ; simpl ; intuition congruence.
    }
  destruct big_endian ; try rewrite <- in_rev in HIN ; auto.
Qed.


Lemma epmatch_encode_val : 
  forall v p chunk
         (DEP   : is_dep p)
         (MATCH : epmatch v p),
    forall mv, In mv (encode_val chunk v) -> mvmatch mv p.
Proof.
  unfold encode_val.
  intros.
  eapply epmatch_inj_symbolic with (3:= H) ; eauto.
  eapply epmatch_to_bits  ; eauto.
Qed.


Lemma epmatch_proj_symbolic_aux_le : 
  forall p bytes
         (DEP : is_dep p)
         (MEMVAL : forall mv : memval, In mv bytes -> mvmatch mv p),
         epmatch (proj_symbolic_aux_le bytes) p.
Proof.
    induction bytes ; simpl ; intros.
    destruct p ; simpl in DEP ; try tauto ; try constructor; depends_prf.
    try find_trans (proj_symbolic_aux_le bytes) ; try (find_trans (expr_of_memval a));
    eapply epmatch_dep2; auto; repeat constructor.
    clear x.
    assert (mvmatch a p).
    apply MEMVAL ; intuition.
    unfold expr_of_memval.
    destruct a.
    clear MEMVAL IHbytes.
    unfold mvmatch in H.
    revert e H.
    induction n ; simpl in * ; intros.
    find_trans e ; eapply epmatch_dep ; repeat constructor ; auto.
    apply IHn.
    find_trans e ; eapply epmatch_dep ; repeat constructor ; auto.
    clear x.
    find_trans (proj_symbolic_aux_le bytes) ; eapply epmatch_dep; auto; repeat constructor.
Qed.



Lemma epmatch_proj_symbolic_le : 
  forall p bytes
         (DEP : is_dep p)
         (MEMVAL : forall mv : memval, In mv bytes -> mvmatch mv p),
         epmatch (proj_symbolic_le bytes) p.
Proof.
  unfold proj_symbolic_le.
  unfold rev_if_be.
  intros.
  destruct big_endian ; auto.
  eapply epmatch_proj_symbolic_aux_le ; eauto.
  intros.
  rewrite <- in_rev in H.
  intuition.
  eapply epmatch_proj_symbolic_aux_le ; eauto.  
Qed.


Lemma epmatch_decode_val : 
  forall  chunk bytes p,
    is_dep p -> 
    (forall mv, In mv bytes -> mvmatch mv p) -> 
    epmatch (decode_val chunk bytes) p.
Proof.
  unfold decode_val, from_bits.
  intros.
  repeat case_match ; intros ; try find_trans (proj_symbolic_le bytes) ; eapply epmatch_dep ;  repeat constructor ; auto ; try apply epmatch_proj_symbolic_le ; auto.
  destruct s; repeat constructor ; auto.
  destruct s; repeat constructor ; auto.
Qed.  

Lemma mvmatch_lub_r : 
  forall mv av p,
    mvmatch mv p ->
    mvmatch mv (eplub av p).
Proof.
  destruct mv ; simpl.
  apply epmatch_lub_r.
Qed.


Definition mkdep (p:aptr) : aptr :=
  eplub (poffset p) Pcst.

Lemma epmatch_provenance :
  forall v av, 
    evmatch v av -> 
    epmatch v (provenance av).
Proof.
  intros.
  unfold provenance.
  inv H ; simpl ; try constructor ; auto ; depends_prf.
  eapply poffset_sound ; eauto.
  eapply poffset_sound ; eauto.
  eapply poffset_sound ; eauto.
Qed.

Lemma epmatch_is_dep :
  forall v p, 
    epmatch v p -> 
    is_dep (poffset p).
Proof.
  intros.
  inv H ; simpl ; auto.
Qed.  


Lemma evmatch_provenance_is_dep :
  forall v av,
    evmatch v av -> 
    is_dep (provenance av).
Proof.
  unfold provenance.
  intros.
  inv H ; simpl ; auto; eapply epmatch_is_dep; eauto.
Qed.

Lemma evmatch_aptr_of_aval : 
  forall addr aaddr,
    evmatch addr aaddr -> 
    epmatch addr  (aptr_of_aval aaddr).
Proof.
  intros.
  inv H; simpl ; try constructor ; depends_prf.
Qed.  

Ltac depends_dep B DEPENDS:=
     match goal with
     | H : depends_on_blocks ?S ?A |- _ => 
      let dep := fresh "DEP" in
       assert (dep : S B \/ ~ S B);[|destruct dep ; [
       | exfalso ; apply DEPENDS in H ; eauto ]]
       end.

Lemma normalise_sound :
  forall addr aaddr b i bound align
         (NOFORGERY : no_forgery Int.max_unsigned bound align)
         (MATCH : epmatch  addr aaddr)
         (NORM  : Normalise.normalise bound align addr = Vptr b i),
   pmatch b i aaddr.
Proof.
  intros.
  destruct (Normalise.norm_correct bound align addr).

  rewrite NORM in eval_ok.
  unfold lessdef_on in eval_ok.
  simpl in eval_ok.
  destruct (NOFORGERY b) as [CM1 [COMPAT1 CM2EQ]].
  destruct (CM2EQ) as [CM2 [COMPAT2 SAMEX]].
  assert (EVAL1 := eval_ok CM1 (fun  _ _ => Byte.zero) COMPAT1).
  assert (EVAL2 := eval_ok CM2 (fun  _ _ => Byte.zero) COMPAT2).
  inv EVAL1. rename H1 into EVAL1.
  inv EVAL2. rename H1 into EVAL2.
  rewrite Int.add_commut in EVAL2.
  rewrite Int.add_commut in EVAL1.
  assert (HDIFF := DIFF _ _ _ SAMEX).  
  assert (DEPENDS : forall (S: block -> Prop), 
                  (S b ->  False) -> 
                  depends_on_blocks S addr -> False).
  {               
    intros.
    unfold depends_on_blocks in H0.
    erewrite H0 with (a' := CM2) in EVAL1; eauto.
    rewrite <- EVAL1 in EVAL2.
    apply inj_vint in EVAL2.
    apply int_add_eq_l  in EVAL2.
    congruence.
    intros.
    apply (SAME _ _ _ SAMEX).
    congruence.
  }   
  inv MATCH.
  - 
   unfold depends_on_nothing in H.
   depends_dep b DEPENDS. tauto.
   tauto.
  - 
  rew_cst  H0; auto.
  simpl in *.
  destruct (eq_block b b0).
  +
  subst.
  apply inj_vint in EVAL2.  
  rewrite Int.add_commut in EVAL2.
  apply int_add_eq_l in EVAL2. subst.
  constructor ; auto.
  + 
  rewrite (SAME _ _ _ SAMEX b0) in EVAL1; auto.
  rewrite <- EVAL1 in EVAL2.
  apply inj_vint in EVAL2.
  apply int_add_eq_l in EVAL2.
  generalize (DIFF _ _ _ SAMEX).  
  congruence.
 -
 depends_dep b DEPENDS.
  { destruct (bc b) ; intuition try congruence.
    destruct (ident_eq id id0) ; intuition try congruence.
    }        
   constructor ; auto.
  -              
 depends_dep b DEPENDS.
  { 
    destruct (bc b) ; intuition try congruence.
    right.
    intro HH ; destruct HH ; congruence.
    left ; exists id ; reflexivity.
    right.
    intro HH ; destruct HH ; congruence.
    right.
    intro HH ; destruct HH ; congruence.
    }        
   destruct  H0.
   econstructor ; eauto.
  - 
  rew_cst  H0; auto.
  simpl in *.
  destruct (eq_block b b0).
  +
  subst.
  apply inj_vint in EVAL2.  
  rewrite Int.add_commut in EVAL2.
  apply int_add_eq_l in EVAL2. subst.
  constructor ; auto.
  + 
  rewrite (SAME _ _ _ SAMEX b0) in EVAL1; auto.
  rewrite <- EVAL1 in EVAL2.
  apply inj_vint in EVAL2.
  apply int_add_eq_l in EVAL2.
  generalize (DIFF _ _ _ SAMEX).  
  congruence.
  -
  depends_dep b DEPENDS. 
  { destruct (bc b) ; intuition try congruence.
      }        
   constructor ; auto.
  - 
  depends_dep b DEPENDS.
  { destruct (bc b) ; intuition try congruence.
      }        
   constructor ; tauto.
  -
  depends_dep b DEPENDS.
  { destruct (bc b) ; intuition try congruence.
      }        
   constructor ; tauto.
Qed. 

Import Memory.

Lemma mem_no_forgery : forall m,
   no_forgery Int.max_unsigned (Mem.bounds_of_block m) (Mem.nat_mask m).
Proof.
  red; intros.
  destruct (Mem.exists_two_cms m b) as (cm & cm' & A & B & C & D); eauto.
  exists cm; split; auto.
  exists cm'; split; auto.
  constructor; auto.
Qed.

Lemma aptr_of_aval_stack_norm:
  forall m b o r av i,
    aptr_of_aval av = Stk i ->
    evmatch r av ->
    Mem.mem_norm m r  = Vptr b o -> bc b = BCstack /\ i = o.
Proof.
  intros.
  exploit normalise_sound; eauto.
  apply mem_no_forgery.
  apply evmatch_aptr_of_aval; eauto.
  intros PM.
  rewrite H in PM.
  inv PM. auto.
Qed.


Record smatch (m: mem) (b:block) (p:aptr) : Prop :=
{
  SMOFF : is_dep p;
  SMLD : forall  ofs n l,
        n >=  0 -> 
        Mem.loadbytes m b ofs n = Some l -> 
        forall mv,  In mv l -> mvmatch  mv p

}.

Lemma smatch_load : 
  forall m chunk b a v ofs,
    smatch  m b a -> 
    Mem.load chunk m b ofs = Some v -> 
    epmatch  v a.
Proof.
  intros.
  apply Mem.load_loadbytes in H0.
  destruct H0 ; intuition. subst.
  inv H.
  eapply epmatch_decode_val; eauto.
  eapply SMLD0; eauto.
  destruct chunk ; compute ; congruence.
Qed.

Remark loadbytes_load_ext:
  forall b m m',
  (forall ofs n bytes, Mem.loadbytes m' b ofs n = Some bytes -> n >= 0 -> Mem.loadbytes m b ofs n = Some bytes) ->
  forall chunk ofs v, Mem.load chunk m' b ofs = Some v -> Mem.load chunk m b ofs = Some v.
Proof.
  intros. exploit Mem.load_loadbytes; eauto. intros [bytes [A B]].
  exploit Mem.load_valid_access; eauto. intros [C D]. 
  subst v. apply Mem.loadbytes_load; auto. apply H; auto. generalize (size_chunk_pos chunk); omega.
Qed.



Definition fun_ext (A B : Type) (f g : A -> B) : Prop :=
           forall x, f x = g x.

Instance EquiFun (A B : Type) : Equivalence (fun_ext A B).
Proof.
unfold fun_ext.
 constructor; auto.
 repeat intro ; eauto.
 rewrite H. rewrite H0.
reflexivity.
Qed.
 

Definition compat_ext (a a' : block -> int) (bd bd' : block -> Z * Z) : Prop :=
  forall cm, compat Int.max_unsigned bd' a' cm ->
             compat Int.max_unsigned bd a cm.

(*Lemma epmatch_ext : 
      forall a a' bd bd'
             (COMPAT : compat_ext a a' bd bd')
             (*(A : forall b, a b = a' b) *)
             (*(B : forall b, bd b = bd' b) *),
       forall v p,
         epmatch a bd v p -> epmatch a' bd' v p.
Proof.
  intros.
  inv H ; econstructor; eauto;
  try ( unfold depends_on_blocks in *; intuition).
  - unfold depends_on_nothing, depends_on_blocks in *.
    intros.
    apply H0; auto.
  -  unfold is_pointer in *.
     unfold same_eval in *.
     simpl in *.
     intros. apply H1 ; auto.
  - unfold is_pointer in *.
     unfold same_eval in *.
     simpl in *.
     intros. apply H1 ; auto.
Qed.


Lemma mvmatch_ext : 
      forall a a' bd bd'
             (COMPAT : compat_ext a a' bd bd')
      (*       (A : forall b, a b = a' b)
       (B : forall b, bd b = bd' b) *),
       forall mv p,
         mvmatch a bd mv p -> mvmatch a' bd' mv p.
Proof.
  intros.
  destruct mv ; simpl in *.
  eapply epmatch_ext ; eauto.
Qed.
  
Lemma evmatch_ext : 
      forall a a' bd bd'
             (COMPAT : compat_ext a a' bd bd'),
       forall v p,
         evmatch a bd v p -> evmatch a' bd' v p.
Proof.
  intros.
  generalize (epmatch_ext a a' bd bd' COMPAT v).
  intros.
  inv H ; econstructor ; eauto ;   unfold is_constant, same_eval in * ; intuition.
  - 
  unfold is_unsigned in *.
  intros. apply COMPAT in COMPAT0.
  apply H2 with (u:= u) in COMPAT0.
  destruct COMPAT0.
  exists x ; intuition.
  - 
  unfold is_signed in *.
  intros. apply COMPAT in COMPAT0.
  apply H2 with (u:= u) in COMPAT0.
  destruct COMPAT0.
  exists x ; intuition.
Qed.
  
Definition compat_mem_ext (m m' : mem) : Prop :=
  compat_ext (Mem.nat_mask m) (Mem.nat_mask m') (Mem.bounds_of_block m) (Mem.bounds_of_block m').
*)


Lemma smatch_ext:
  forall m b p m'
(*  (CMP : compat_mem_ext m m')*)
(*  (BOUND : forall b, Mem.bounds_of_block m b = Mem.bounds_of_block m' b)*)
,
  smatch m b p ->
  (forall ofs n bytes, Mem.loadbytes m' b ofs n = Some bytes -> n >= 0 -> Mem.loadbytes m b ofs n = Some bytes) ->
  smatch m' b p.
Proof.
  intros. destruct H. split; intros;auto.
  apply H0 in H1 ; try omega.
  eapply SMLD0 in H1; eauto.
Qed.

Lemma smatch_inv:
  forall m b p m'
  ,
  smatch m b p ->
  (forall ofs n, n >= 0 -> Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n) ->
  smatch m' b p.
Proof.
  intros. eapply smatch_ext with (1:= H); eauto.
  intros. rewrite <- H0; eauto.
Qed.

Lemma smatch_ge:
  forall m b p q, smatch m b p -> epge q p -> smatch m b q.
Proof.
  intros. destruct H as [A B]. split; intros. 
  clear B.
  destruct p ; destruct q ; simpl in * ; tauto.
  apply B with (mv := mv) in H1; auto.
  destruct mv ; simpl in *.
  eapply epmatch_ge  ; eauto. 
Qed.


Lemma In_loadbytes:
  forall m b byte n ofs bytes,
  Mem.loadbytes m b ofs n = Some bytes ->
  In byte bytes ->
  exists ofs', ofs <= ofs' < ofs + n /\ Mem.loadbytes m b ofs' 1 = Some(byte :: nil).
Proof.
  intros until n. pattern n. 
  apply well_founded_ind with (R := Zwf 0).
- apply Zwf_well_founded.
- intros sz REC ofs bytes LOAD IN.
  destruct (zle sz 0). 
  + rewrite (Mem.loadbytes_empty m b ofs sz) in LOAD by auto.
    inv LOAD. contradiction.
  + exploit (Mem.loadbytes_split m b ofs 1 (sz - 1) bytes).
    replace (1 + (sz - 1)) with sz by omega. auto.
    omega.
    omega.
    intros (bytes1 & bytes2 & LOAD1 & LOAD2 & CONCAT). 
    subst bytes. 
    exploit Mem.loadbytes_length. eexact LOAD1. change (nat_of_Z 1) with 1%nat. intros LENGTH1.
    rewrite in_app_iff in IN. destruct IN.
  * destruct bytes1; try discriminate. destruct bytes1; try discriminate. 
    simpl in H. destruct H; try contradiction. subst m0.
    exists ofs; split. omega. auto.
  * exploit (REC (sz - 1)). red; omega. eexact LOAD2. auto.
    intros (ofs' & A & B). 
    exists ofs'; split. omega. auto.
Qed.

Lemma smatch_loadbytes:
  forall m b p mv  n ofs bytes,
    n >= 0 -> 
    Mem.loadbytes m b ofs n = Some bytes ->
    smatch m b p ->
    In mv bytes ->
    mvmatch  mv p.
Proof.
  intros.
  inv H1.
  eauto.
Qed.


Lemma setN_in:
  forall vl p q c,
  p <= q < p + Z_of_nat (length vl) ->
  In (ZMap.get q (Mem.setN vl p c)) vl.
Proof.
  induction vl; intros.
  simpl in H. omegaContradiction.
  simpl length in H. rewrite inj_S in H. simpl. 
  destruct (zeq p q). subst q. rewrite Mem.setN_outside. rewrite ZMap.gss. 
  auto with coqlib. omega.
  right. apply IHvl. omega.
Qed.


Lemma load_store_overlap:
  forall chunk m1 b ofs v m2 chunk' ofs' v',
  Mem.store chunk m1 b ofs v = Some m2 ->
  Mem.load chunk' m2 b ofs' = Some v' ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  exists mv1 mvl mv1' mvl',
    encode_val chunk v = (mv1 :: mvl)
  /\  decode_val chunk' (mv1' :: mvl') = v'
  /\  (   (ofs' = ofs /\ mv1' = mv1)
       \/ (ofs' > ofs /\ In mv1' mvl)
       \/ (ofs' < ofs /\ In mv1 mvl')).
Proof.
  intros. 
  exploit Mem.load_result; eauto. erewrite Mem.store_mem_contents by eauto; simpl.
  rewrite PMap.gss. 
  set (c := (Mem.mem_contents m1)#b). intros V'. 
  destruct (size_chunk_nat_pos chunk) as [sz SIZE]. 
  destruct (size_chunk_nat_pos chunk') as [sz' SIZE'].
  destruct (encode_val chunk v) as [ | mv1 mvl] eqn:ENC.
  generalize (encode_val_length chunk v); rewrite ENC; simpl; congruence.
  set (c' := Mem.setN (mv1::mvl) ofs c) in *.
  exists mv1, mvl, (ZMap.get ofs' c'), (Mem.getN sz' (ofs' + 1) c').
  split. rewrite <- ENC. auto.
  split. rewrite V', SIZE'. reflexivity.
  destruct (zeq ofs' ofs).
- subst ofs'. left; split. auto. unfold c'. simpl. 
  rewrite Mem.setN_outside by omega. apply ZMap.gss.
- right. destruct (zlt ofs ofs').
(* If ofs < ofs':  the load reads (at ofs') a continuation byte from the write.
       ofs   ofs'   ofs+|chunk|
        [-------------------]       write
             [-------------------]  read
*)
+ left; split. omega. unfold c'. simpl. apply setN_in. 
  assert (Z.of_nat (length (mv1 :: mvl)) = size_chunk chunk).
  { rewrite <- ENC; rewrite encode_val_length. rewrite size_chunk_conv; auto. }
  simpl length in H3. rewrite inj_S in H3. omega.
(* If ofs > ofs':  the load reads (at ofs) the first byte from the write.
       ofs'   ofs   ofs'+|chunk'|
               [-------------------]  write
         [----------------]           read
*)
+ right; split. omega. replace mv1 with (ZMap.get ofs c'). 
  apply Mem.getN_in. 
  assert (size_chunk chunk' = Zsucc (Z.of_nat sz')).
  { rewrite size_chunk_conv. rewrite SIZE'. rewrite inj_S; auto. }
  omega.
  unfold c'. simpl. rewrite Mem.setN_outside by omega. apply ZMap.gss.
Qed.


Lemma loadbytes_mem_contents : 
  forall m1 b ofs n r,
    Mem.loadbytes m1 b ofs n = Some r -> 
    r = (Mem.getN (nat_of_Z n) ofs (m1.(Mem.mem_contents)#b)).
Proof.
  Transparent Mem.loadbytes.
  unfold Mem.loadbytes.
  intros.
  destruct (Mem.range_perm_dec m1 b ofs (ofs + n) Cur Readable).
  congruence.
  congruence.
Qed.


Lemma getN_in_ex:
  forall c  n p x,
    In x (Mem.getN n p c) ->
    exists q, p <= q < p + Z_of_nat n /\
              ZMap.get q c = x.
Proof.
  induction n; intros.
  -  simpl in H. tauto.
  - simpl.
    simpl in H.
    destruct H.
    + exists p ; intuition.
    + apply IHn in H.
      destruct H.
      exists x0.
      intuition.
Qed.

Lemma getN_in_iff:
  forall c  n p x,
    In x (Mem.getN n p c) <->
    exists q, p <= q < p + Z_of_nat n /\
              ZMap.get q c = x.
Proof.
  split ; intros.
  eapply getN_in_ex ; eauto.
  destruct H.
  destruct H ; subst.
  eapply Mem.getN_in ; eauto.
Qed.

Lemma load_store_in_memval :
  forall  m1 b ofs ofs' l1 m2 n l1' l2'
          (STORE  : Mem.storebytes m1 b ofs l1 = Some m2)
          (LOADM1 : Mem.loadbytes  m1 b ofs' n = Some l1')
          (LOADM2 : Mem.loadbytes  m2 b ofs' n = Some l2'),
    (forall mv, In mv l2' -> (In mv l1 \/ In mv l1')).
Proof.
  intros.
  apply Mem.storebytes_mem_contents  in STORE.
  apply loadbytes_mem_contents in LOADM1.
  apply loadbytes_mem_contents in LOADM2.
  subst.
  rewrite STORE in *. clear STORE.
  revert H.
  rewrite PMap.gss.
  generalize ((Mem.mem_contents m1) # b) as B.
  generalize (nat_of_Z n) as N.
  revert ofs.
  intros.
  rewrite getN_in_iff in H.
  destruct H.
  intuition subst.
  rewrite getN_in_iff.
  destruct (classic (x < ofs \/ x >= ofs + Z.of_nat (length l1))).
  rewrite Mem.setN_outside; auto.
  - 
  right.
  exists x ; intuition.
  -
    left.
    apply setN_in.
    omega.
Qed.

Lemma is_dep_eplub : 
  forall p p',
    is_dep p -> 
    is_dep (eplub p' p).
Proof.
  destruct p ; destruct p' ;  simpl ; try tauto.
  destruct (ident_eq id0 id) ; simpl; auto.
  destruct (ident_eq id0 id) ; simpl; auto.
Qed.


Add Parametric Morphism : compat  with signature
    @eq Z ==> (fun_ext block (Z * Z)) ==> (fun_ext block int) ==> (fun_ext block int) ==> iff as
        compat_morph.
Proof.
  assert (   forall (y : Z) (x y0 : block -> Z * Z),
   fun_ext block (Z * Z) x y0 ->
   forall x0 y1 : block -> int,
   fun_ext block int x0 y1 ->
   forall x1 y2 : block -> int,
     fun_ext block int x1 y2 -> (compat y x x0 x1 -> compat y y0 y1 y2)).
  {
    intros.
    inv H2 ; constructor; eauto ; intros; repeat rewrite <- H1 in *.
    -
      eapply  addr_space ; eauto.
      rewrite <- H in H2. auto.
    -
      eapply overlap ; eauto;
      rewrite <- H in * ; auto.
    -
      rewrite <- H0 in *.
      eapply alignment ; eauto;
      rewrite <- H in * ; auto.
  }
  split ; intros; eapply H ; eauto; symmetry; auto.
Qed.
  

Add Parametric Morphism : compat_ext with signature
    (fun_ext block int) ==> (fun_ext block int) ==> 
                        (fun_ext block (Z * Z)) ==> (fun_ext block (Z * Z)) ==>  iff as compat_ext_morph.
Proof.
  assert (   forall x y : block -> int,
   fun_ext block int x y ->
   forall x0 y0 : block -> int,
   fun_ext block int x0 y0 ->
   forall x1 y1 : block -> Z * Z,
   fun_ext block (Z * Z) x1 y1 ->
   forall x2 y2 : block -> Z * Z,
   fun_ext block (Z * Z) x2 y2 ->
   (compat_ext x x0 x1 x2 -> compat_ext y y0 y1 y2)).
  {
  intros.
  unfold compat_ext in *.
  intros.
  rewrite <- H1 in *.
  rewrite <- H in *.
  eapply H3 ; eauto.
  rewrite H2 in *.
  rewrite H0 in *.
  auto.
  }
  split ; intros ; eapply H ; eauto ; symmetry ; auto.
Qed.
                                                                                           
Lemma compat_ext_refl : forall al bd,
compat_ext al al bd bd.
Proof.
  unfold compat_ext.
  auto.
Qed.




Lemma smatch_storebytes:
  forall m b ofs bytes m' b' p p',
  Mem.storebytes m b ofs bytes = Some m' ->
  smatch m b' p ->
  (forall mv, In mv bytes -> mvmatch  mv p') ->
  smatch m' b' (eplub p' p).
Proof.
  intros. destruct H0 as [A B]. split.
  - eapply is_dep_eplub ; eauto.
  - 
  intros ofs' n bytes' GE LOAD.
  case_eq (Mem.loadbytes m b' ofs' n).
  +
    {
    intros bytes2 LOAD2 mv HIN.
    destruct (peq b b').
    -
    subst.
    specialize B with (2:=LOAD2);auto.
    assert (forall mv, In mv bytes' -> In mv  bytes \/ In mv bytes2).
    {
      eapply load_store_in_memval with (1:= H);eauto.
    }
    apply is_dep_eplub  with (p':=p') in A.
    intros.
    +
    apply H0 in HIN.
    destruct HIN as [HIN | HIN].
    apply H1 in HIN.
    destruct mv ; simpl in *.
    eapply epmatch_lub_l; eauto.
    apply B in HIN; auto.
    destruct mv ; simpl in *.
    eapply epmatch_lub_r; eauto.
    -
    rewrite  Mem.loadbytes_storebytes_disjoint with (1:= H) in LOAD; auto.
    apply mvmatch_lub_r.
    eapply B ; eauto.
    congruence. 
    }
  + 
  intros.
  exfalso.
  apply Mem.loadbytes_range_perm in LOAD.
  unfold Mem.loadbytes in H0.
  destruct (Mem.range_perm_dec m b' ofs' (ofs' + n) Cur Readable) ; try congruence.
  unfold Mem.range_perm in *.
  apply n0.
  intros.
  apply LOAD in H3.
  eapply Mem.perm_storebytes_2; eauto.
Qed.

Lemma smatch_store:
  forall chunk m b ofs v m' b' p av,
  Mem.store chunk m b ofs v = Some m' ->
  smatch m b' p ->
  is_dep av -> 
  epmatch  v av ->
  smatch m' b' (eplub av p).
Proof.
  intros.
  apply Mem.store_storebytes in H.
  eapply smatch_storebytes ; eauto.
  apply epmatch_encode_val; auto.
Qed.  


Record bmatch (m: mem) (b: block) (ab: ablock) : Prop :=
  {
    BMS : smatch m b ab.(ab_summary) ;
    BML : forall chunk ofs v, Mem.load chunk m b ofs = Some v -> 
    evmatch  v (ablock_load chunk ab ofs)
    }.

Record ablock_summary (ab : ablock) :=
  {
    SUMDEP : is_dep (ab_summary ab);
    SUMUB  : forall chunk ofs,
        epge ab.(ab_summary) (aptr_of_aval (ablock_load chunk ab ofs))
  }.


Lemma bmatch_ext:
  forall m b ab m'
(*  (BOUND : forall b, Mem.bounds_of_block m b= Mem.bounds_of_block m' b)*)
,
  bmatch m b ab ->
  (forall ofs n bytes, Mem.loadbytes m' b ofs n = Some bytes -> n >= 0 -> Mem.loadbytes m b ofs n = Some bytes) ->
  bmatch m' b ab.
Proof.
  intros.
   destruct H as [A B]. split; intros.
   apply smatch_ext with m; auto.
  eapply B; eauto. eapply loadbytes_load_ext; eauto. 
Qed.

Lemma bmatch_inv:
  forall m b ab m'
,
  bmatch m b ab ->
  (forall ofs n, n >= 0 -> Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n) ->
  bmatch m' b ab.
Proof.
  intros. eapply bmatch_ext with m; eauto.
  intros. rewrite <- H0; eauto.
Qed.


Lemma ablock_load_sound:
  forall chunk m b ofs v ab,
  Mem.load chunk m b ofs = Some v ->
  bmatch m b ab ->
  evmatch  v (ablock_load chunk ab ofs).
Proof.
  intros. destruct H0. eauto.
Qed.

Lemma ablock_load_anywhere_sound:
  forall chunk m b ofs v ab,
  Mem.load chunk m b ofs = Some v ->
  bmatch m b ab ->
  evmatch  v (ablock_load_anywhere chunk ab).
Proof.
  intros. destruct H0.
  eapply smatch_load in BMS0 ; eauto.
  unfold ablock_load_anywhere. 
  eapply vnormalize_cast; eauto. 
  constructor; auto.
Qed.

Lemma ablock_init_sound:
  forall m b p, smatch m b p -> bmatch m b (ablock_init p).
Proof.
  intros; split; auto; intros. 
  unfold ablock_load, ablock_init; simpl. rewrite ZMap.gi.
  eapply vnormalize_cast; eauto.
  eapply smatch_load in H ; eauto.
  constructor ; auto.
Qed.

Lemma epge_vnormalize :
  forall p chunk,
    epge p (poffset p) -> 
    epge p (aptr_of_aval (vnormalize chunk (Ptr p))).
Proof.
  intros.
  destruct chunk ; simpl; unfold provenance ; simpl; auto;
  apply epge_refl.
Qed.


Lemma ablock_init_summary :
  forall p, is_dep p -> ablock_summary (ablock_init p).
Proof.
  intros.
  constructor; unfold ablock_load, ablock_init; simpl. auto.
  intros. rewrite ZMap.gi.
  eapply epge_vnormalize ; eauto.
  destruct p ; simpl in * ; tauto.
Qed.
  


Lemma ablock_store_anywhere_sound:
  forall chunk m b ofs v m' b' ab av,
  Mem.store chunk m b ofs v = Some m' ->
  bmatch m b' ab ->
  evmatch  v av ->
  bmatch m' b' (ablock_store_anywhere chunk ab av).
Proof.
  intros. destruct H0 as [A B]. unfold ablock_store_anywhere.
  apply ablock_init_sound. eapply smatch_store; eauto.
  eapply evmatch_provenance_is_dep ; eauto.
  apply epmatch_provenance ; auto.
Qed.

Local Notation "a ## b" := (ZMap.get b a) (at level 1).

Remark inval_after_outside:
  forall i lo hi c, (i < lo \/ i > hi)%Z -> (inval_after lo hi c)##i = c##i.
Proof.
  intros until c. functional induction (inval_after lo hi c); intros.
  rewrite IHt by omega. apply ZMap.gso. unfold ZIndexed.t; omega. 
  auto.
Qed.

Remark inval_after_contents:
  forall chunk av i lo hi c,
  (inval_after lo hi c)##i = ACval chunk av ->
  c##i = ACval chunk av /\ (i < lo \/ i > hi).
Proof.
  intros until c. functional induction (inval_after lo hi c); intros.
  destruct (zeq i hi). 
  subst i. rewrite inval_after_outside in H by omega. rewrite ZMap.gss in H. discriminate.
  exploit IHt; eauto. intros [A B]. rewrite ZMap.gso in A by auto. split. auto. omega.
  split. auto. omega.
Qed.

Remark inval_before_outside:
  forall i hi lo c, i < lo \/ i >= hi -> (inval_before hi lo c)##i = c##i.
Proof.
  intros until c. functional induction (inval_before hi lo c); intros.
  rewrite IHt by omega. unfold inval_if. destruct (c##lo); auto. 
  destruct (zle (lo + size_chunk chunk) hi); auto.
  apply ZMap.gso. unfold ZIndexed.t; omega. 
  auto.
Qed.

Remark inval_before_contents_1:
  forall i chunk av lo hi c,
  lo <= i < hi -> (inval_before hi lo c)##i = ACval chunk av ->
  c##i = ACval chunk av /\ i + size_chunk chunk <= hi.
Proof.
  intros until c. functional induction (inval_before hi lo c); intros.
- destruct (zeq lo i).
+ subst i. rewrite inval_before_outside in H0 by omega. 
  unfold inval_if in H0. destruct (c##lo) eqn:C. congruence. 
  destruct (zle (lo + size_chunk chunk0) hi).
  rewrite C in H0; inv H0. auto. 
  rewrite ZMap.gss in H0. congruence.
+ exploit IHt. omega. auto. intros [A B]; split; auto. 
  unfold inval_if in A. destruct (c##lo) eqn:C. auto.
  destruct (zle (lo + size_chunk chunk0) hi); auto.
  rewrite ZMap.gso in A; auto. 
- omegaContradiction.
Qed.

Lemma max_size_chunk: forall chunk, size_chunk chunk <= 8.
Proof.
  destruct chunk; simpl; omega.
Qed.

Remark inval_before_contents:
  forall i c chunk' av' j,
  (inval_before i (i - 7) c)##j = ACval chunk' av' ->
  c##j = ACval chunk' av' /\ (j + size_chunk chunk' <= i \/ i <= j).
Proof.
  intros. destruct (zlt j (i - 7)). 
  rewrite inval_before_outside in H by omega. 
  split. auto. left. generalize (max_size_chunk chunk'); omega.
  destruct (zlt j i). 
  exploit inval_before_contents_1; eauto. omega. tauto.
  rewrite inval_before_outside in H by omega. 
  split. auto. omega.
Qed.

Lemma ablock_store_contents:
  forall chunk ab i av j chunk' av',
  (ablock_store chunk ab i av).(ab_contents)##j = ACval chunk' av' ->
     (i = j /\ chunk' = chunk /\ av' = av)
  \/ (ab.(ab_contents)##j = ACval chunk' av' 
      /\ (j + size_chunk chunk' <= i \/ i + size_chunk chunk <= j)).
Proof.
  unfold ablock_store; simpl; intros.
  destruct (zeq i j). 
  subst j. rewrite ZMap.gss in H. inv H; auto. 
  right. rewrite ZMap.gso in H by auto.
  exploit inval_before_contents; eauto. intros [A B].
  exploit inval_after_contents; eauto. intros [C D].
  split. auto. omega.
Qed.

Lemma chunk_compat_true:
  forall c c',
  chunk_compat c c' = true ->
  size_chunk c = size_chunk c' /\ align_chunk c <= align_chunk c' /\ type_of_chunk c = type_of_chunk c'.
Proof.
  destruct c, c'; intros; try discriminate; simpl; auto with va.
Qed.

Lemma compat_ext_store :
  forall chunk m b ofs' v m'

    (STORE : Mem.store chunk m b ofs' v = Some m'),
   compat_ext (Mem.nat_mask m) (Mem.nat_mask m') (Mem.bounds_of_block m)
              (Mem.bounds_of_block m').
Proof.
  intros.
  generalize (compat_ext_refl (Mem.nat_mask m') (Mem.bounds_of_block m')).
  intros.
  rewrite compat_ext_morph ; eauto; try reflexivity.
  repeat intro.
  eapply Mem.nat_mask_store ; eauto. 
  repeat intro.
  eapply Mem.bounds_of_block_store ; eauto.
Qed.



Lemma compat_ext_storebytes :
  forall  m b ofs' l m'

    (STORE : Mem.storebytes m b ofs' l = Some m'),
   compat_ext (Mem.nat_mask m) (Mem.nat_mask m') (Mem.bounds_of_block m)
              (Mem.bounds_of_block m').
Proof.
  intros.
  generalize (compat_ext_refl (Mem.nat_mask m') (Mem.bounds_of_block m')).
  intros.
  rewrite compat_ext_morph ; eauto; try reflexivity.
  repeat intro.
  eapply Mem.nat_mask_storebytes ; eauto. 
  repeat intro.
  eapply Mem.bounds_of_block_storebytes ; eauto.
Qed.

Lemma ablock_store_sound:
  forall chunk m b ofs v m' ab av,
  Mem.store chunk m b ofs v = Some m' ->
  bmatch m b ab ->
  evmatch  v av ->
  bmatch m' b (ablock_store chunk ab ofs av).
Proof.
  intros until av; intros STORE BIN VIN. destruct BIN as [BIN1 BIN2]. split.
  eapply smatch_store; eauto.
  eapply evmatch_provenance_is_dep ; eauto.
  eapply epmatch_provenance ; eauto.
  intros chunk' ofs' v' LOAD.
  assert (SUMMARY: evmatch  v' (vnormalize chunk' (Ptr (evplub av ab.(ab_summary))))).
  {
    eapply smatch_store with (av := provenance av) in STORE ; eauto.
    eapply vnormalize_cast; eauto. constructor.
    eapply smatch_load  with (2:= LOAD) in STORE ; auto.
    eapply evmatch_provenance_is_dep ; eauto.
    eapply epmatch_provenance ; eauto.
  }
  unfold ablock_load. 
  destruct ((ab_contents (ablock_store chunk ab ofs av)) ## ofs') as [ | chunk1 av1] eqn:C.
  apply SUMMARY.
  destruct (chunk_compat chunk' chunk1) eqn:COMPAT; auto.
  exploit chunk_compat_true; eauto. intros (U & V & W).
  exploit ablock_store_contents; eauto. intros [(P & Q & R) | (P & Q)].
- (* same offset and compatible chunks *)
  subst. 
  assert (same_eval v'  (Val.load_result chunk' v)). 
  {
    eapply Mem.load_store_similar_2; eauto.
  }
  rewrite evmatch_same_eval_morph with (1:= H) by reflexivity.
  apply vnormalize_sound; auto.
- (* disjoint load/store *)
  assert (Mem.load chunk' m b ofs' = Some v').
  { rewrite <- LOAD. symmetry. eapply Mem.load_store_other; eauto.
    rewrite U. auto. }
  exploit BIN2; eauto. unfold ablock_load. rewrite P. rewrite COMPAT.
  auto.
Qed.

Lemma ablock_loadbytes_sound:
  forall m b ab mv n ofs bytes,
    n >= 0 -> 
    Mem.loadbytes m b ofs n = Some bytes ->
    bmatch m b ab ->
    In mv bytes ->
    mvmatch  mv (ablock_loadbytes ab).
Proof.
  intros. destruct H1.
  eapply smatch_loadbytes; eauto. 
Qed.

Lemma ablock_storebytes_anywhere_sound:
  forall m b ofs bytes p m' b' ab,
  Mem.storebytes m b ofs bytes = Some m' ->
  (forall mv, In mv bytes -> mvmatch  mv p) ->
  bmatch m b' ab ->
  bmatch m' b' (ablock_storebytes_anywhere ab p).
Proof.
  intros. destruct H1 as [A B]. apply ablock_init_sound.
  eapply smatch_storebytes; eauto.
Qed.

Lemma ablock_storebytes_contents:
  forall ab p i sz j chunk' av',
  (ablock_storebytes ab p i sz).(ab_contents)##j = ACval chunk' av' ->
  ab.(ab_contents)##j = ACval chunk' av' 
  /\ (j + size_chunk chunk' <= i \/ i + Zmax sz 0 <= j).
Proof.
  unfold ablock_storebytes; simpl; intros.
  exploit inval_before_contents; eauto. clear H. intros [A B].
  exploit inval_after_contents; eauto. clear A. intros [C D].
  split. auto. xomega.
Qed.

Lemma ablock_storebytes_sound:
  forall m b ofs bytes m' p p' ab sz
  ,
  Mem.storebytes m b ofs bytes = Some m' ->
  length bytes = nat_of_Z sz ->
  (forall mv, In mv bytes -> mvmatch  mv p') ->
  bmatch m b ab ->
  epge (provenance p) p' -> 
  bmatch m' b (ablock_storebytes ab p ofs sz).
Proof.
  intros until sz; intros STORE LENGTH CONTENTS BM PGE. destruct BM as [BM1 BM2]. split. 
  eapply smatch_storebytes; eauto. 
  intros. apply CONTENTS in H. destruct mv ; simpl in *.
  eapply epmatch_ge ; eauto.
  intros chunk' ofs' v' LOAD'.
  assert (SUMMARY: evmatch  v' (vnormalize chunk' (Ptr (evplub p ab.(ab_summary))))).
  {
    eapply smatch_storebytes  in STORE ; eauto.
    eapply vnormalize_cast; eauto. constructor.
    eapply smatch_load  with (2:= LOAD') in STORE ; auto.
    eapply epmatch_ge ; eauto.
    unfold evplub.
    apply eplub_least.
    eapply epge_trans ; eauto.
    apply epge_lub_l.
    apply epge_lub_r.
  }
  unfold ablock_load. 
  destruct (ab_contents (ablock_storebytes ab p ofs sz))##ofs' eqn:C.
  exact SUMMARY.
  destruct (chunk_compat chunk' chunk) eqn:COMPAT; auto. 
  exploit chunk_compat_true; eauto. intros (U & V & W).
  exploit ablock_storebytes_contents; eauto. intros [A B].
  assert (Mem.load chunk' m b ofs' = Some v').
  { rewrite <- LOAD'; symmetry. eapply Mem.load_storebytes_other; eauto.
    rewrite U. rewrite LENGTH. rewrite nat_of_Z_max. right; omega. }
  exploit BM2; eauto. unfold ablock_load. rewrite A. rewrite COMPAT.
  auto.
Qed.


Lemma is_dep_epge : forall p q,
    is_dep p -> epge q p -> is_dep q.
Proof.
  destruct p ; destruct q ; simpl ; try tauto.
Qed.

Lemma is_dep_poffset :
  forall p, is_dep p -> 
            epge p (poffset p).
Proof. destruct p ; simpl in * ; try tauto.
Qed.

Lemma poffset_ub : forall p, epge (poffset p) p.
Proof.
  destruct p ; simpl; auto.
Qed.

Lemma epge_vnormalize_provenance : 
  forall av chunk, 
    epge (provenance av) (aptr_of_aval (vnormalize chunk av)).
Proof.
  unfold provenance.
  intros.
  destruct chunk ; destruct av ; simpl ; intros ; auto;
  repeat (unfold sgn,uns,zero_ext ; case_match) ; simpl;   intros;  try apply epge_refl;
  apply poffset_ub.
Qed.
    
Lemma ablock_store_summary :
  forall ab chunk i av,
    ablock_summary ab -> 
    ablock_summary (ablock_store chunk ab i av).
Proof.
  intros.
  destruct H.
  assert (HDEP : is_dep    (ab_summary (ablock_store chunk ab i av))).
  {
    unfold ablock_store. simpl.
    eapply is_dep_epge ; eauto.
    unfold evplub.
    apply epge_lub_r.
  }
  constructor ; auto.
  - 
    intros.
    simpl. unfold ablock_load in *.
    case_eq ((ab_contents (ablock_store chunk ab i av)) ## ofs).
    +  intros.
    unfold ablock_store ; simpl.
    apply epge_vnormalize.
    unfold evplub.     unfold provenance.
    repeat rewrite <- eplub_poffset.
    rewrite poffset_idem.
    eapply eplub_least.
    apply epge_lub_l.
    apply epge_trans with (q :=  (ab_summary ab)).
    apply epge_lub_r. apply  is_dep_poffset.
    auto.
    + intros.
      apply ablock_store_contents in H.
      intuition subst.
      case_eq (chunk_compat chunk0 chunk).
      *
      intros.
      unfold evplub.
      apply epge_trans with (q := provenance av).
      apply epge_lub_l. apply epge_vnormalize_provenance.
      *
        intros.
        eapply epge_trans with (q := ((ab_summary (ablock_store chunk ab ofs av)))).
        unfold ablock_store. simpl. apply epge_refl.
        apply epge_vnormalize.
        apply is_dep_poffset; auto.
      * {
        case_eq (chunk_compat chunk0 chunk1).
        -
        intros.
        specialize (SUMUB0 chunk0 ofs).
        rewrite H in SUMUB0.
        rewrite H1 in SUMUB0.
        eapply epge_trans ; eauto.
        apply epge_lub_r.
        -
          intros.
          eapply epge_trans with (q := ((ab_summary (ablock_store chunk ab ofs av)))).
          unfold ablock_store. simpl. apply epge_refl.
          apply epge_vnormalize.
          apply is_dep_poffset; auto.
        }
      *
        case_eq (chunk_compat chunk0 chunk1).
        specialize (SUMUB0 chunk0 ofs).
        rewrite H in SUMUB0.
        intro.
        rewrite H1 in SUMUB0.
        eapply epge_trans ; eauto.
        apply epge_lub_r.
          intros.
          eapply epge_trans with (q := ((ab_summary (ablock_store chunk ab ofs av)))).
          unfold ablock_store. simpl. apply epge_refl.
          apply epge_vnormalize.
          apply is_dep_poffset; auto.
Qed.
        
        
(** Boolean equality *)

Definition bbeq (ab1 ab2: ablock) : bool :=
  eq_aptr ab1.(ab_summary) ab2.(ab_summary) &&
  PTree.beq (fun c1 c2 => proj_sumbool (eq_acontent c1 c2)) 
            (snd ab1.(ab_contents)) (snd ab2.(ab_contents)).

Lemma bbeq_load:
  forall ab1 ab2,
  bbeq ab1 ab2 = true ->
  ab1.(ab_summary) = ab2.(ab_summary)
  /\ (forall chunk i, ablock_load chunk ab1 i = ablock_load chunk ab2 i).
Proof.
  unfold bbeq; intros. InvBooleans. split.
- unfold ablock_load_anywhere; intros; congruence.
- rewrite PTree.beq_correct in H1.
  assert (A: forall i, ZMap.get i (ab_contents ab1) = ZMap.get i (ab_contents ab2)).
  {
    intros. unfold ZMap.get, PMap.get. set (j := ZIndexed.index i). 
    specialize (H1 j).
    destruct (snd (ab_contents ab1))!j; destruct (snd (ab_contents ab2))!j; try contradiction.
    InvBooleans; auto.
    rewrite ! ab_default. auto.
  }
  intros. unfold ablock_load. rewrite A, H.
  destruct (ab_contents ab2)##i; auto.
Qed.

Lemma bbeq_sound:
  forall ab1 ab2,
  bbeq ab1 ab2 = true ->
  forall m b, bmatch m b ab1 <-> bmatch m b ab2.
Proof.
  intros. exploit bbeq_load; eauto. intros [A B]. 
  split ; intro BM ; constructor ; inv BM; try congruence.
  -
    intros.
    rewrite <- B ; eauto.
  - 
    intros.
    rewrite B ; eauto.
Qed. 

(** Least upper bound *)

Definition combine_acontents_opt (c1 c2: option acontent) : option acontent :=
  match c1, c2 with
  | Some (ACval chunk1 v1), Some (ACval chunk2 v2) =>
      if chunk_eq chunk1 chunk2 then Some(ACval chunk1 (evlub v1 v2)) else None
  | _, _ =>
      None
  end.

Definition combine_contentmaps (m1 m2: ZMap.t acontent) : ZMap.t acontent :=
  (ACany, PTree.combine combine_acontents_opt (snd m1) (snd m2)).

Definition blub (ab1 ab2: ablock) : ablock :=
  {| ab_contents := combine_contentmaps ab1.(ab_contents) ab2.(ab_contents);
     ab_summary := eplub ab1.(ab_summary) ab2.(ab_summary);
     ab_default := refl_equal _ |}.

Definition combine_acontents (c1 c2: acontent) : acontent :=
  match c1, c2 with
  | ACval chunk1 v1, ACval chunk2 v2 =>
      if chunk_eq chunk1 chunk2 then ACval chunk1 (evlub v1 v2) else ACany
  | _, _ => ACany
  end.

Lemma get_combine_contentmaps:
  forall m1 m2 i,
  fst m1 = ACany -> fst m2 = ACany ->
  ZMap.get i (combine_contentmaps m1 m2) = combine_acontents (ZMap.get i m1) (ZMap.get i m2).
Proof.
  intros. destruct m1 as [dfl1 pt1]. destruct m2 as [dfl2 pt2]; simpl in *.
  subst dfl1 dfl2. unfold combine_contentmaps, ZMap.get, PMap.get, fst, snd. 
  set (j := ZIndexed.index i). 
  rewrite PTree.gcombine by auto.
  destruct (pt1!j) as [[]|]; destruct (pt2!j) as [[]|]; simpl; auto.
  destruct (chunk_eq chunk chunk0); auto. 
Qed.

Lemma smatch_lub_l:
  forall m b p q, smatch m b p -> smatch m b (eplub p q).
Proof.
  intros. destruct H as [A B]. split.
  -
  rewrite eplub_comm.
  apply is_dep_eplub; auto.
  - 
    intros.
    eapply B in H0; eauto.
    destruct mv ; simpl in *.
    apply epmatch_lub_l; auto.  
Qed.

Lemma smatch_lub_r:
  forall m b p q, smatch m b q -> smatch m b (eplub p q).
Proof.
  intros. destruct H as [A B]. split.
  -
  apply is_dep_eplub; auto.
  - 
    intros.
    eapply B in H0; eauto.
    destruct mv ; simpl in *.
    apply epmatch_lub_r; auto.  
Qed.

Lemma bmatch_lub_l:
  forall m b x y, bmatch m b x -> bmatch m b (blub x y).
Proof.
  intros. destruct H as [BM1 BM2]. split; unfold blub; simpl.
- apply smatch_lub_l; auto. 
- intros.
  assert (SUMMARY: evmatch  v (vnormalize chunk (Ptr (eplub (ab_summary x) (ab_summary y))))
).
  { exploit smatch_lub_l; eauto. instantiate (1 := ab_summary y).
    intros.
    exploit smatch_load ; eauto.
    intros.
    eapply vnormalize_cast; eauto.
    constructor. auto.
  }
  exploit BM2; eauto.
  unfold ablock_load; simpl. rewrite get_combine_contentmaps by (apply ab_default).
  unfold combine_acontents; destruct (ab_contents x)##ofs, (ab_contents y)##ofs; auto.
  destruct (chunk_eq chunk0 chunk1); auto. subst chunk0.
  destruct (chunk_compat chunk chunk1); auto.
  intros.
  eapply evmatch_ge; eauto. apply vnormalize_monotone. apply evge_lub_l. 
Qed.

Lemma bmatch_lub_r:
  forall m b x y, bmatch m b y -> bmatch m b (blub x y).
Proof.
  intros. destruct H as [BM1 BM2]. split; unfold blub; simpl.
- apply smatch_lub_r; auto. 
- intros.
  assert (SUMMARY: evmatch  v (vnormalize chunk (Ptr (eplub (ab_summary x) (ab_summary y))))
).
  { exploit smatch_lub_r; eauto. instantiate (1 := ab_summary x).
    intros.
    exploit smatch_load ; eauto.
    intros. 
    eapply vnormalize_cast; eauto.
    constructor. auto.
  }
  exploit BM2; eauto.
  unfold ablock_load; simpl. rewrite get_combine_contentmaps by (apply ab_default).
  unfold combine_acontents; destruct (ab_contents x)##ofs, (ab_contents y)##ofs; auto.
  destruct (chunk_eq chunk0 chunk1); auto. subst chunk0.
  destruct (chunk_compat chunk chunk1); auto.
  intros. eapply evmatch_ge; eauto. apply vnormalize_monotone.
  rewrite evlub_comm.
  apply evge_lub_l. 
Qed.

(** * Abstracting read-only global variables *)

Definition romem := PTree.t ablock.

Definition is_romem (p : aptr) := 
match p with
| Gl _ _ | Pcst | Glo _ | Glob => True 
| _ => False
end.

Record is_romem_block (ab: ablock) : Prop :=
  {
    ROSU : is_romem ab.(ab_summary);
    ROBL : ablock_summary ab
  }.


Definition romatch  (m: mem) (rm: romem) : Prop :=
  forall b id ab,
  bc b = BCglob id ->
  rm!id = Some ab ->
  is_romem_block ab
  /\ bmatch m b ab
  /\ forall ofs, ~Mem.perm m b ofs Max Writable.

Lemma romatch_store:
  forall chunk m b ofs v m' rm,
  Mem.store chunk m b ofs v = Some m' ->
  romatch m rm ->
  romatch m' rm.
Proof.
  intros; red; intros. exploit H0; eauto. intros (A & B & C). split; auto. split.
- exploit Mem.store_valid_access_3; eauto. intros [P _].
  apply bmatch_inv with m; auto.
+ intros. eapply Mem.loadbytes_store_other; eauto.  
  left. red; intros; subst b0. elim (C ofs). apply Mem.perm_cur_max.
  apply P. generalize (size_chunk_pos chunk); omega.
- intros; red; intros; elim (C ofs0). eauto with mem.
Qed.

Lemma romatch_storebytes:
  forall m b ofs bytes m' rm,
  Mem.storebytes m b ofs bytes = Some m' ->
  romatch m rm ->
  romatch m' rm.
Proof.
  intros; red; intros. exploit H0; eauto. intros (A & B & C). split; auto. split.
  - apply bmatch_inv with m; auto.
  intros. eapply Mem.loadbytes_storebytes_disjoint; eauto. 
  destruct (eq_block b0 b); auto. subst b0. right; red; unfold Intv.In; simpl; red; intros.
  elim (C x). apply Mem.perm_cur_max. eapply Mem.storebytes_range_perm; eauto.
- intros; red; intros; elim (C ofs0). eauto with mem.
Qed.

Lemma romatch_ext:
  forall m rm m'
  ,
  romatch m rm ->
  (forall b id ofs n bytes, bc b = BCglob id -> Mem.loadbytes m' b ofs n = Some bytes -> Mem.loadbytes m b ofs n = Some bytes) ->
  (forall b id ofs p, bc b = BCglob id -> Mem.perm m' b ofs Max p -> Mem.perm m b ofs Max p) ->
  romatch m' rm.
Proof.
  intros; red; intros. exploit H; eauto. intros (A & B & C).
  split. auto.
  split. apply bmatch_ext with m; auto. 
  intros. eapply H0; eauto.
  intros; red; intros. elim (C ofs). eapply H1; eauto. 
Qed.



Lemma romatch_free:
  forall m b lo hi m' rm,
  Mem.free m b lo hi = Some m' ->
  romatch m rm ->
  romatch m' rm.
Proof.
  intros. apply romatch_ext with m; auto. 
  intros. eapply Mem.loadbytes_free_2; eauto. 
  intros. eauto with mem.
Qed.


Lemma romatch_alloc:
  forall m b lo hi m' rm bt,
  Mem.alloc m lo hi bt = Some (m', b) ->
  bc_below bc (Mem.nextblock m) ->
  romatch m rm ->
  romatch m' rm.
Proof.
  intros. apply romatch_ext with m; auto. 
  intros. rewrite <- H3; symmetry. eapply Mem.loadbytes_alloc_unchanged; eauto.
  apply H0. congruence.
  intros. eapply Mem.perm_alloc_4; eauto. apply Mem.valid_not_valid_diff with m; eauto with mem.
  apply H0. congruence.
Qed.

(** * Abstracting memory states *)

Record amem : Type := AMem {
  am_stack: ablock;
  am_glob: PTree.t ablock;
  am_nonstack: aptr;
  am_top: aptr
}.

Record mmatch (m: mem) (am: amem) : Prop := mk_mem_match {
  mmatch_stack: forall b,
    bc b = BCstack ->
    bmatch m b am.(am_stack);
  mmatch_glob: forall id ab b,
    bc b = BCglob id -> 
    am.(am_glob)!id = Some ab ->
    bmatch m b ab;
  mmatch_nonstack: forall b,
    bc b <> BCstack -> bc b <> BCinvalid ->
    smatch m b am.(am_nonstack);
  mmatch_top: forall b,
    bc b <> BCinvalid ->
    smatch m b am.(am_top);
  mmatch_below:
    bc_below bc (Mem.nextblock m)
}.

Definition minit (p: aptr) :=
  {| am_stack := ablock_init p;
     am_glob := PTree.empty _;
     am_nonstack := p;
     am_top := p |}.

Definition mbot := minit Pbot.
Definition mtop := minit Ptop.

Definition load (chunk: memory_chunk) (rm: romem) (m: amem) (p: aptr) : aval :=
  match p with
  | Pbot => Ptr Pbot
  | Pcst => Ptr Pbot
  | Gl id ofs =>
      match rm!id with
      | Some ab => ablock_load chunk ab (Int.unsigned ofs)
      | None =>
          match m.(am_glob)!id with
          | Some ab => ablock_load chunk ab (Int.unsigned ofs)
          | None => vnormalize chunk (Ptr m.(am_nonstack))
          end
      end
  | Glo id =>
      match rm!id with
      | Some ab => ablock_load_anywhere chunk ab
      | None =>
          match m.(am_glob)!id with
          | Some ab => ablock_load_anywhere chunk ab
          | None => vnormalize chunk (Ptr m.(am_nonstack))
          end
      end
  | Stk ofs => ablock_load chunk m.(am_stack) (Int.unsigned ofs)
  | Stack => ablock_load_anywhere chunk m.(am_stack)
  | Glob | Nonstack => vnormalize chunk (Ptr m.(am_nonstack))
  | Ptop => vnormalize chunk (Ptr m.(am_top))
  end.

Definition loadv (chunk: memory_chunk) (rm: romem) (m: amem) (addr: aval) : aval :=
  load chunk rm m (aptr_of_aval addr).

Definition store (chunk: memory_chunk) (m: amem) (p: aptr) (av: aval) : amem :=
  {| am_stack :=
       match p with
       | Stk ofs      => ablock_store chunk m.(am_stack) (Int.unsigned ofs) av
       | Stack | Ptop => ablock_store_anywhere chunk m.(am_stack) av
       | _ => m.(am_stack)
       end;
     am_glob :=
       match p with
       | Gl id ofs =>
           let ab := match m.(am_glob)!id with Some ab => ab | None => ablock_init m.(am_nonstack) end in
           PTree.set id (ablock_store chunk ab (Int.unsigned ofs) av) m.(am_glob)
       | Glo id =>
           let ab := match m.(am_glob)!id with Some ab => ab | None => ablock_init m.(am_nonstack) end in
           PTree.set id (ablock_store_anywhere chunk ab av) m.(am_glob)
       | Glob | Nonstack | Ptop => PTree.empty _
       | _ => m.(am_glob)
       end;
     am_nonstack :=
       match p with
       | Gl _ _ | Glo _ | Glob | Nonstack | Ptop => evplub av m.(am_nonstack)
       | _ => m.(am_nonstack)
       end;
     am_top := evplub av m.(am_top)
  |}.

Definition storev (chunk: memory_chunk) (m: amem) (addr: aval) (v: aval): amem :=
  store chunk m (aptr_of_aval addr) v.

Definition loadbytes (m: amem) (rm: romem) (p: aptr) : aptr :=
  match p with
  | Pbot | Pcst =>  Pbot
  | Gl id _ | Glo id =>
      match rm!id with
      | Some ab => ablock_loadbytes ab
      | None =>
          match m.(am_glob)!id with
          | Some ab => ablock_loadbytes ab
          | None => m.(am_nonstack)
          end
      end
  | Stk _ | Stack => ablock_loadbytes m.(am_stack)
  | Glob | Nonstack => m.(am_nonstack)
  | Ptop => m.(am_top)
  end.

Definition storebytes (m: amem) (dst: aptr) (sz: Z) (p: aptr) : amem :=
  {| am_stack :=
       match dst with
       | Stk ofs      => ablock_storebytes m.(am_stack) (Ptr p) (Int.unsigned ofs) sz
       | Stack | Ptop => ablock_storebytes_anywhere m.(am_stack) p
       | _ => m.(am_stack)
       end;
     am_glob :=
       match dst with
       | Gl id ofs =>
           let ab := match m.(am_glob)!id with Some ab => ab | None => ablock_init m.(am_nonstack) end in
           PTree.set id (ablock_storebytes ab (Ptr p) (Int.unsigned ofs) sz) m.(am_glob)
       | Glo id =>
           let ab := match m.(am_glob)!id with Some ab => ab | None => ablock_init m.(am_nonstack) end in
           PTree.set id (ablock_storebytes_anywhere ab p) m.(am_glob)
       | Glob | Nonstack | Ptop => PTree.empty _
       | _ => m.(am_glob)
       end;
     am_nonstack :=
       match dst with
       | Gl _ _ | Glo _ | Glob | Nonstack | Ptop => eplub p m.(am_nonstack)
       | _ => m.(am_nonstack)
       end;
     am_top := eplub p m.(am_top)
  |}.



Theorem load_sound:
  forall chunk m b ofs v rm am p,
  Mem.load chunk m b (Int.unsigned ofs) = Some v ->
  romatch m rm ->
  mmatch m am ->
  pmatch b ofs p ->
  evmatch  v (load chunk rm am p).
Proof.
  intros. unfold load. inv H2. 
- (* Gl id ofs *)
  destruct (rm!id) as [ab|] eqn:RM. 
  eapply ablock_load_sound; eauto. eapply H0; eauto. 
  destruct (am_glob am)!id as [ab|] eqn:AM.
  eapply ablock_load_sound; eauto. eapply mmatch_glob; eauto. 
  eapply vnormalize_cast; eauto.
  constructor.
  apply mmatch_nonstack with (b:=b) in H1 ; try congruence.
  eapply smatch_load ; eauto.
- (* Glo id *)
  destruct (rm!id) as [ab|] eqn:RM. 
  eapply ablock_load_anywhere_sound; eauto. eapply H0; eauto. 
  destruct (am_glob am)!id as [ab|] eqn:AM.
  eapply ablock_load_anywhere_sound; eauto. eapply mmatch_glob; eauto. 
  eapply vnormalize_cast; eauto.
  constructor.
  apply mmatch_nonstack with (b:=b) in H1 ; try congruence.
  eapply smatch_load ; eauto.
- (* Glob *)
  eapply vnormalize_cast; eauto.
  constructor.
  apply mmatch_nonstack with (b:=b) in H1 ; try congruence.
  eapply smatch_load ; eauto.
- (* Stk ofs *)
  eapply ablock_load_sound; eauto. eapply mmatch_stack; eauto.
- (* Stack *)
  eapply ablock_load_anywhere_sound; eauto. eapply mmatch_stack; eauto.
- (* Nonstack *)
  eapply vnormalize_cast; eauto.
  constructor.
  apply mmatch_nonstack with (b:=b) in H1 ; try congruence.
  eapply smatch_load ; eauto.
- (* Top *)
  eapply vnormalize_cast; eauto.
  constructor.
  eapply smatch_load ; eauto.
  eapply mmatch_top; eauto.
Qed.

Theorem store_sound:
  forall chunk m b ofs v m' am p av,
  Mem.store chunk m b (Int.unsigned ofs) v = Some m' ->
  mmatch  m am ->
  pmatch b ofs p ->
  evmatch  v av ->
  mmatch m' (store chunk am p av).
Proof.
  intros until av; intros STORE MM PM VM.
  unfold store; constructor; simpl; intros.
- (* Stack *)
  assert (DFL: bc b <> BCstack -> bmatch m' b0 (am_stack am)).
  { intros. apply bmatch_inv with m.
  eapply mmatch_stack; eauto. 
    intros. eapply Mem.loadbytes_store_other; eauto. left; congruence. }
  inv PM; try (apply DFL; congruence).
  + assert (b0 = b) by (eapply bc_stack; eauto). subst b0. 
    eapply ablock_store_sound; eauto. eapply mmatch_stack; eauto. 
  + assert (b0 = b) by (eapply bc_stack; eauto). subst b0. 
    eapply ablock_store_anywhere_sound; eauto. eapply mmatch_stack; eauto. 
  + eapply ablock_store_anywhere_sound; eauto. eapply mmatch_stack; eauto.

- (* Globals *)
  rename b0 into b'.
  assert (DFL: bc b <> BCglob id -> (am_glob am)!id = Some ab -> 
               bmatch m' b' ab).
  { intros. apply bmatch_inv with m.
    eapply mmatch_glob; eauto.
    intros. eapply Mem.loadbytes_store_other; eauto. left; congruence. }
  inv PM. 
  + rewrite PTree.gsspec in H0. destruct (peq id id0).
    subst id0; inv H0.
    assert (b' = b) by (eapply bc_glob; eauto). subst b'.
    eapply ablock_store_sound; eauto.
    destruct (am_glob am)!id as [ab0|] eqn:GL. 
    eapply mmatch_glob; eauto.
    apply ablock_init_sound. eapply mmatch_nonstack; eauto; congruence.
    eapply DFL; eauto. congruence.
  + rewrite PTree.gsspec in H0. destruct (peq id id0).
    subst id0; inv H0.
    assert (b' = b) by (eapply bc_glob; eauto). subst b'.
    eapply ablock_store_anywhere_sound; eauto.
    destruct (am_glob am)!id as [ab0|] eqn:GL. 
    eapply mmatch_glob; eauto.
    apply ablock_init_sound. eapply mmatch_nonstack; eauto; congruence.
    eapply DFL; eauto. congruence.
  + rewrite PTree.gempty in H0; congruence.
  + eapply DFL; eauto. congruence.
  + eapply DFL; eauto. congruence. 
  + rewrite PTree.gempty in H0; congruence.
  + rewrite PTree.gempty in H0; congruence.

- (* Nonstack *)
  assert (DFL: smatch m' b0 (evplub av (am_nonstack am))).
  { eapply smatch_store; eauto. eapply mmatch_nonstack; eauto.
    eapply evmatch_provenance_is_dep ; eauto.
    apply epmatch_provenance; auto.
  }
  assert (STK: bc b = BCstack -> smatch m' b0 (am_nonstack am)).
  { intros. apply smatch_inv with m. 
  eapply mmatch_nonstack; eauto; congruence.
    intros. eapply Mem.loadbytes_store_other; eauto. left. congruence.
  }
  inv PM; (apply DFL || apply STK; congruence).

- (* Top *)
  eapply smatch_store; eauto. eapply mmatch_top; eauto.
  eapply evmatch_provenance_is_dep ; eauto.
  apply epmatch_provenance; auto.
- (* Below *)
  erewrite Mem.nextblock_store by eauto. eapply mmatch_below; eauto.
Qed.

Existing Instance EquivExpr.

(*Add Parametric Morphism (bound : ident -> Z * Z) (align : ident -> int) : 
    (Normalise.normalise bound align) 
    with signature (same_eval ) ==> (@eq result) ==> @eq val as normalise_morph.
Proof.
  assert    (forall x y : expr_sym,
   same_eval align bound x y ->
   forall r : result,
     Values.Val.lessdef (Normalise.normalise bound align x r)
                 (Normalise.normalise bound align y r)).
   {
     intros.
     destruct (Normalise.norm_correct bound align x r).   
     eapply Normalise.norm_complete.
     constructor; auto.
     - 
     repeat intro.
     rewrite <- H; auto.
   }       
   intros.
   apply lessdef_antisym; apply H ; auto.          
   rewrite H0 ; reflexivity.
Qed.
*)



Theorem loadbytes_sound:
  forall m b ofs sz bytes am rm p
  (SIZE: sz >= 0)
,
  Mem.loadbytes m b (Int.unsigned ofs) sz = Some bytes ->
  romatch m rm ->
  mmatch m am ->
  pmatch b ofs p ->
  forall  mv, In mv bytes -> mvmatch  mv (loadbytes am rm p).
Proof.
  intros. unfold loadbytes; inv H2.
- (* Gl id ofs *)
  destruct (rm!id) as [ab|] eqn:RM.
  exploit H0; eauto. intros (A & B & C). eapply ablock_loadbytes_sound; eauto.
  destruct (am_glob am)!id as [ab|] eqn:GL.
  eapply ablock_loadbytes_sound; eauto. eapply mmatch_glob; eauto. 
  eapply smatch_loadbytes; eauto. eapply mmatch_nonstack; eauto with va.
- (* Glo id *)
  destruct (rm!id) as [ab|] eqn:RM.
  exploit H0; eauto. intros (A & B & C). eapply ablock_loadbytes_sound; eauto.
  destruct (am_glob am)!id as [ab|] eqn:GL.
  eapply ablock_loadbytes_sound; eauto. eapply mmatch_glob; eauto. 
  eapply smatch_loadbytes; eauto. eapply mmatch_nonstack; eauto with va.
- (* Glob *)
  eapply smatch_loadbytes; eauto. eapply mmatch_nonstack; eauto with va.
- (* Stk ofs *)
  eapply ablock_loadbytes_sound; eauto. eapply mmatch_stack; eauto. 
- (* Stack *)
  eapply ablock_loadbytes_sound; eauto. eapply mmatch_stack; eauto.
- (* Nonstack *) 
  eapply smatch_loadbytes; eauto. eapply mmatch_nonstack; eauto with va.
- (* Top *)
  eapply smatch_loadbytes; eauto. eapply mmatch_top; eauto with va.
Qed.

Theorem storebytes_sound:
  forall m b ofs bytes m' am p sz q,
  Mem.storebytes m b (Int.unsigned ofs) bytes = Some m' ->
  mmatch m am ->
  pmatch b ofs p ->
  length bytes = nat_of_Z sz ->
  (forall mv, In mv bytes -> mvmatch  mv q) ->
  mmatch m' (storebytes am p sz q).
Proof.
  intros until q; intros STORE MM PM LENGTH BYTES.
  unfold storebytes; constructor; simpl; intros.
- (* Stack *)
  assert (DFL: bc b <> BCstack -> bmatch m' b0 (am_stack am)).
  { intros. apply bmatch_inv with m. 
  eapply mmatch_stack; eauto. 
    intros. eapply Mem.loadbytes_storebytes_other; eauto. left; congruence. }
  inv PM; try (apply DFL; congruence).
  + assert (b0 = b) by (eapply bc_stack; eauto). subst b0. 
    eapply ablock_storebytes_sound; eauto. eapply mmatch_stack; eauto. 
    apply epge_poffset.
  + assert (b0 = b) by (eapply bc_stack; eauto). subst b0. 
    eapply ablock_storebytes_anywhere_sound; eauto. eapply mmatch_stack; eauto. 
  + eapply ablock_storebytes_anywhere_sound; eauto. eapply mmatch_stack; eauto.

- (* Globals *)
  rename b0 into b'.
  assert (DFL: bc b <> BCglob id -> (am_glob am)!id = Some ab -> 
               bmatch m' b' ab).
  { intros. apply bmatch_inv with m. 
   eapply mmatch_glob; eauto.
    intros. eapply Mem.loadbytes_storebytes_other; eauto. left; congruence. }
  inv PM. 
  + rewrite PTree.gsspec in H0. destruct (peq id id0).
    subst id0; inv H0.
    assert (b' = b) by (eapply bc_glob; eauto). subst b'.
    eapply ablock_storebytes_sound; eauto.
    destruct (am_glob am)!id as [ab0|] eqn:GL. 
    eapply mmatch_glob; eauto.
    apply ablock_init_sound. eapply mmatch_nonstack; eauto; congruence.
    apply epge_poffset.
    eapply DFL; eauto. congruence.
  + rewrite PTree.gsspec in H0. destruct (peq id id0).
    subst id0; inv H0.
    assert (b' = b) by (eapply bc_glob; eauto). subst b'.
    eapply ablock_storebytes_anywhere_sound; eauto.
    destruct (am_glob am)!id as [ab0|] eqn:GL. 
    eapply mmatch_glob; eauto.
    apply ablock_init_sound. eapply mmatch_nonstack; eauto; congruence.
    eapply DFL; eauto. congruence.
  + rewrite PTree.gempty in H0; congruence.
  + eapply DFL; eauto. congruence.
  + eapply DFL; eauto. congruence. 
  + rewrite PTree.gempty in H0; congruence.
  + rewrite PTree.gempty in H0; congruence.

- (* Nonstack *)
  assert (DFL: smatch m' b0 (eplub q (am_nonstack am))).
  { 
  eapply smatch_storebytes; eauto. eapply mmatch_nonstack; eauto. }
  assert (STK: bc b = BCstack -> smatch m' b0 (am_nonstack am)).
  { intros. apply smatch_inv with m. 
    eapply mmatch_nonstack; eauto; congruence.
    intros. eapply Mem.loadbytes_storebytes_other; eauto. left. congruence.
  }
  inv PM; (apply DFL || apply STK; congruence).

- (* Top *)
  eapply smatch_storebytes; eauto. eapply mmatch_top; eauto.

- (* Below *)
  erewrite Mem.nextblock_storebytes by eauto. eapply mmatch_below; eauto.
Qed.

Theorem loadv_sound:
  forall chunk m addr v rm am aaddr,
  Mem.loadv chunk m addr = Some v ->
  romatch  m rm ->
  mmatch  m am ->
  evmatch  addr aaddr ->
  evmatch  v (loadv chunk rm am aaddr).
Proof.
  intros.
  unfold Mem.loadv in H.
  revert H.
  case_eq (Mem.mem_norm m addr ) ; try congruence.
  intros.
  unfold loadv.
  eapply load_sound; eauto.
  apply evmatch_aptr_of_aval in H2.
  eapply normalise_sound ; eauto.
  apply mem_no_forgery.
Qed.



Lemma mmatch_ext:
  forall m am m'
  ,
  mmatch  m am ->
  (forall b ofs n bytes, bc b <> BCinvalid -> n >= 0 -> Mem.loadbytes m' b ofs n = Some bytes -> Mem.loadbytes m b ofs n = Some bytes) ->
  Ple (Mem.nextblock m) (Mem.nextblock m') ->
  mmatch  m' am.
Proof.
  intros. inv H. constructor; intros.
- apply bmatch_ext with m; auto with va.
- apply bmatch_ext with m; eauto with va.
- apply smatch_ext with m; auto with va.
- apply smatch_ext with m; auto with va.
- red; intros. exploit mmatch_below0; eauto. xomega.
Qed.

Theorem storev_sound:
  forall chunk m addr v m' am aaddr av,
  Mem.storev chunk m addr v = Some m' ->
  mmatch  m am ->
  evmatch  addr aaddr ->
  evmatch  v av ->
  mmatch  m' (storev chunk am aaddr av).
Proof.
  intros.
  unfold Mem.storev in H.
  revert H.
  case_eq (Mem.mem_norm m addr ) ; try congruence.
  intros.
  unfold storev.
  eapply store_sound; eauto.
  apply evmatch_aptr_of_aval in H1.
  eapply normalise_sound ; eauto.
  apply mem_no_forgery.
Qed.


(** Free is problematic because the size is changing,
    There should be monotonicty of memory_size ?  *)

Lemma mmatch_free:
  forall m b lo hi m' am,
  Mem.free m b lo hi = Some m' ->
  mmatch  m am ->
  mmatch  m' am.
Proof.
  intros. apply mmatch_ext with m; auto. 
  intros. eapply Mem.loadbytes_free_2; eauto. 
  erewrite <- Mem.nextblock_free by eauto. xomega. 
Qed.

Lemma mmatch_top':
  forall m am, mmatch m am -> mmatch m mtop.
Proof.
  intros. constructor; simpl; intros.
- apply ablock_init_sound. apply smatch_ge with (ab_summary (am_stack am)). 
  eapply mmatch_stack; eauto. constructor.
- rewrite PTree.gempty in H1; discriminate.
- eapply smatch_ge. eapply mmatch_nonstack; eauto. constructor.
- eapply smatch_ge. eapply mmatch_top; eauto. constructor.
- eapply mmatch_below; eauto.
Qed.


(** Boolean equality *)

Definition mbeq (m1 m2: amem) : bool :=
  eq_aptr m1.(am_top) m2.(am_top)
  && eq_aptr m1.(am_nonstack) m2.(am_nonstack)
  && bbeq m1.(am_stack) m2.(am_stack)
  && PTree.beq bbeq m1.(am_glob) m2.(am_glob).

Lemma mbeq_sound:
  forall m1 m2, mbeq m1 m2 = true -> 
  forall m, 
  mmatch  m m1 <-> 
  mmatch  m m2.
Proof.
  unfold mbeq; intros. InvBooleans. rewrite PTree.beq_correct in H1.
  split; intros M; inv M; constructor; intros.
- erewrite <- bbeq_sound; eauto. 
- specialize (H1 id). rewrite H4 in H1. destruct (am_glob m1)!id eqn:G; try contradiction. 
  erewrite <- bbeq_sound; eauto. 
- rewrite <- H; eauto. 
- rewrite <- H0; eauto.
- auto.
- erewrite bbeq_sound; eauto. 
- specialize (H1 id). rewrite H4 in H1. destruct (am_glob m2)!id eqn:G; try contradiction. 
  erewrite bbeq_sound; eauto. 
- rewrite H; eauto. 
- rewrite H0; eauto.
- auto.
Qed.

(** Least upper bound *)

Definition combine_ablock (ob1 ob2: option ablock) : option ablock :=
  match ob1, ob2 with
  | Some b1, Some b2 => Some (blub b1 b2)
  | _, _ => None
  end.

Definition mlub (m1 m2: amem) : amem :=
{| am_stack := blub m1.(am_stack) m2.(am_stack);
   am_glob  := PTree.combine combine_ablock m1.(am_glob) m2.(am_glob);
   am_nonstack := eplub m1.(am_nonstack) m2.(am_nonstack);
   am_top := eplub m1.(am_top) m2.(am_top) |}.

Lemma mmatch_lub_l:
  forall m x y, mmatch  m x -> 
  mmatch  m (mlub x y).
Proof.
  intros. inv H. constructor; simpl; intros. 
- apply bmatch_lub_l; auto. 
- rewrite PTree.gcombine in H0 by auto. unfold combine_ablock in H0. 
  destruct (am_glob x)!id as [b1|] eqn:G1;
  destruct (am_glob y)!id as [b2|] eqn:G2;
  inv H0.
  apply bmatch_lub_l; eauto. 
-  apply smatch_lub_l; auto. 
- apply smatch_lub_l; auto.
- auto.
Qed.

Lemma mmatch_lub_r:
  forall m x y, mmatch  m y -> 
  mmatch  m (mlub x y).
Proof.
  intros. inv H. constructor; simpl; intros. 
- apply bmatch_lub_r; auto. 
- rewrite PTree.gcombine in H0 by auto. unfold combine_ablock in H0. 
  destruct (am_glob x)!id as [b1|] eqn:G1;
  destruct (am_glob y)!id as [b2|] eqn:G2;
  inv H0.
  apply bmatch_lub_r; eauto. 
- apply smatch_lub_r; auto. 
- apply smatch_lub_r; auto.
- auto.
Qed.

End MATCH.

(** * Monotonicity properties when the block classification changes. *)

Lemma genv_match_exten:
  forall ge (bc1 bc2: block_classification),
  genv_match bc1 ge ->
  (forall b id, bc1 b = BCglob id <-> bc2 b = BCglob id) ->
  (forall b, bc1 b = BCother -> bc2 b = BCother) ->
  genv_match bc2 ge.
Proof.
  intros. destruct H as [A B]. split; intros. 
- rewrite <- H0. eauto. 
- exploit B; eauto. destruct (bc1 b) eqn:BC1. 
  + intuition congruence.
  + rewrite H0 in BC1. intuition congruence.
  + intuition congruence.
  + erewrite H1 by eauto. intuition congruence.
Qed.


Lemma epmatch_exten : 
      forall (bc1 bc2: block_classification)  e p
        (BC :forall b id, bc2 b = BCglob id <-> bc1 b = BCglob id)
        (GE : epge Glob p),
      epmatch bc1 e p -> 
      epmatch bc2 e p.
 Proof.
  intros.
  inv H ; simpl in GE; try tauto ; try constructor; auto.
  - 
  econstructor ; eauto.
  rewrite BC0 ; auto.
  - repeat intro.
    eapply H0 ; eauto.
    intros. apply H ; auto. rewrite BC0. auto.
  - repeat intro.
    eapply H0 ; eauto.
    intros. apply H ; auto. 
    destruct H1 as [i HH] ; exists i.
   rewrite BC0 ; auto.
Qed.

Lemma depends_on_blocks_same : 
      forall  S S' e, 
             (forall b, S b <-> S' b) -> 
   depends_on_blocks  S e -> depends_on_blocks  S' e.
Proof.
 repeat intro.
 rewrite H0 ; eauto.
 intuition. apply H1. rewrite <- H ; auto.
Qed.
    
Import NormaliseSpec.

Definition le (S S' : block -> Prop) :=
  forall b, S b -> S' b.

Definition of_list (l : list block) : block -> Prop :=
  fun b => In b l.


Lemma depends_on_blocks_appears_ex : forall e, 
    depends_on_blocks (block_appears e) e.
Proof.
  intros.
  apply depends_on_blocks_appears.
  auto.
Qed.

Require Import Wf_nat.

Definition inter (S S' : block -> Prop) :=
  fun b => S b /\ S' b.

Section IN.
  Variable A : Type.
  Variable Aeq_dec : forall (x y : A), {x = y} + {x <> y}.

  Lemma remove_not_in' :
  forall l x,
    ~ In x l -> 
    remove Aeq_dec x l = l.
Proof.
  induction l ; simpl ; intuition.
  destruct (Aeq_dec x a) ; simpl ; intuition try congruence.
  rewrite IHl ; intuition.
Qed.

Lemma remove_not_in :
  forall x v l, x <> v -> 
              (In x (remove Aeq_dec v l) <-> In x l).
Proof.
  induction l ; simpl ; intuition.
  destruct (Aeq_dec v a) ; intuition.
  simpl in H0 ; intuition.
  destruct (Aeq_dec v a) ; simpl;  intuition try congruence.
  destruct (Aeq_dec v a) ; simpl;  intuition try congruence.
Qed.

Open Scope nat_scope.
Lemma length_remove : forall l x,
                        In x l ->
                        length (remove Aeq_dec x l) < length l.
Proof.
  induction l ; simpl ; intuition subst.
  destruct (Aeq_dec x x) ; simpl ; try congruence .
  destruct (In_dec Aeq_dec x l).
  intuition.
  rewrite remove_not_in' ; auto.
  destruct (Aeq_dec x a) ; simpl ; try congruence .
  subst.
  apply IHl in H0;intuition.
  apply IHl in H0 ; intuition.
Qed.


End IN.


Lemma is_romem_epmatch : 
  forall  (bc1 bc2: block_classification) e v,
    (forall b id, bc2 b = BCglob id <-> bc1 b = BCglob id) ->
    is_romem v -> 
    epmatch bc1 e v  -> 
    epmatch bc2 e v.
Proof.
  intros.
  destruct v ; simpl in * ; inv H1 ; econstructor ; eauto; try tauto.
  - rewrite H ; congruence.
  - eapply depends_on_blocks_le ; eauto.
    simpl. intros. rewrite H ; congruence.
  - eapply depends_on_blocks_le ; eauto.
    simpl. intros. destruct H1. exists x ; rewrite H. auto.
Qed.

Lemma not_forall : forall A (P: A -> Prop), ~ (forall (a:A), P a) -> (exists a, ~ P a).
Proof.
  intuition.
  destruct (classic (exists a, ~ P a)).
  destruct H0. exists x ; auto.
  exfalso.
  apply H.
  intros.
  destruct (classic (P a)).
  auto.
  exfalso. apply H0.
  exists a ; auto.
Qed.  

Lemma not_impl : forall (P Q: Prop), ~ (P -> Q) -> P /\ ~ Q.
Proof.
  intuition.
  destruct (classic P).
  auto.
  exfalso.
  destruct (classic Q).
  tauto. tauto.
Qed.

Definition union (S S' : block -> Prop) :=
  fun b => S b \/ S' b.


Lemma depends_on_blocks_S :
  forall e (S: block -> Prop) b align bound
         (NOFORGERY : no_forgery Int.max_unsigned bound align )
         (DEP1 : depends_on_blocks S e)
         (DEP  : depends Int.max_unsigned  bound align  e b), S b.
Proof.
  intros.
  destruct (classic (S b)). auto.
  destruct (NOFORGERY b) as (cm & COMP & (cm' & COMP' & (SE1 & SE2))).
  generalize (DEP _ COMP _ COMP' SE2 Normalise.dummy_em).
  assert (EQM : forall b : block, S b -> cm b = cm' b).
  { intros. apply SE1. congruence. }
  specialize (DEP1 cm cm' EQM (fun _ _ => Byte.zero)).  
  intuition.
Qed.

Definition minus (S S' : block -> Prop)  :=
  fun b => S b /\ ~ S' b.

Lemma not_ex : forall (A :  Type) P, (~ exists (x : A), P x) <-> (forall x, ~ P x).
Proof.
  repeat intro.
  split ; repeat intro.
  apply H. exists x ; auto.
  destruct H0. specialize (H x) ; tauto.
Qed.

Lemma not_or : forall (P Q : Prop), ~ (P /\ Q) <-> (~ P \/ ~ Q).
Proof.
  intros.
  tauto.
Qed.

Lemma depends_pointer : forall bound align b i
                               (NOFORGERY :  no_forgery Int.max_unsigned bound align)
  ,
    depends Int.max_unsigned bound align (Eval (Vptr b i)) b.
Proof.
  intros.
  repeat red; intros. simpl in H. 
  apply inj_vint in H.
  rewrite ! (Int.add_commut _ i) in H.
  apply  int_add_eq_l in H.
  congruence.
Qed.




Lemma romatch_exten:
  forall (bc1 bc2: block_classification) m rm,
  romatch bc1 m rm ->
  (forall b id, bc2 b = BCglob id <-> bc1 b = BCglob id) ->
  romatch bc2 m rm.
Proof.
  intros; red; intros. rewrite H0 in H1. exploit H; eauto. intros ((A1 &[AD AUP]) & B & C).
  split.
  repeat constructor ; auto.
  assert (PM: forall e chunk ofs , epmatch bc1 e (aptr_of_aval (ablock_load chunk ab ofs))  ->
                         epmatch bc2 e (aptr_of_aval (ablock_load chunk ab ofs))).
  {
    intros.
    specialize (AUP chunk ofs).
    revert A1 AD AUP H3.
    generalize (ab_summary ab). generalize (aptr_of_aval (ablock_load chunk ab ofs)).
    intros. inv H3; econstructor ; eauto; try (destruct a0 ; simpl in * ; tauto).
    - rewrite H0 ; auto.
    - eapply depends_on_blocks_le ; eauto.
      simpl. intros. rewrite H0 ; congruence.
    - eapply depends_on_blocks_le ; eauto.
      simpl. intros. destruct H3 as [id2 H3] ; exists id2 ; rewrite H0 ; congruence.
  }
  assert (VM: forall v chunk ofs , evmatch bc1 v (ablock_load chunk ab ofs)  ->
                                   evmatch bc2 v (ablock_load chunk ab ofs)).
  {
    intros.
    specialize (AUP chunk ofs).
    specialize (PM v chunk ofs).
    inv H3 ; econstructor; eauto.
    - rewrite <- H4 in *. simpl in *. auto.
    - rewrite <- H4 in *. simpl in *. auto.
    - rewrite <- H4 in *. simpl in *. auto.
  } 

  destruct B as [[B1 B2] B3].
  split. split.
  - constructor.
    + auto.
    + intros. exploit B2 ; eauto.
      destruct mv ; simpl.
      eapply is_romem_epmatch ; eauto.
  - intros.
    exploit B3 ; eauto.
  - auto.
Qed.


Definition bc_incr (bc1 bc2: block_classification) : Prop :=
  forall b, bc1 b <> BCinvalid -> bc2 b = bc1 b.

Section MATCH_INCR.

Variables bc1 bc2: block_classification.
Hypothesis INCR: bc_incr bc1 bc2.


Lemma epmatch_incr: forall  e p, epmatch bc1  e p -> epmatch bc2  e p.
Proof.
  induction 1 ; econstructor;eauto; try (eapply depends_on_blocks_le ; eauto); simpl.
  - rewrite <- H. apply INCR ; congruence.      
  - simpl. intros. rewrite INCR; congruence.
  - simpl. intros. destruct H0. exists x. rewrite INCR ; congruence.
  - simpl. rewrite INCR; congruence.
  - simpl. intros ; rewrite INCR; congruence.
  - simpl. intros. rewrite INCR; intuition congruence.
  - simpl. intros. rewrite INCR; intuition congruence.
Qed.


Lemma vmatch_incr: forall  v x, evmatch bc1  v x -> evmatch bc2  v x.
Proof.
  induction 1; constructor; auto; apply epmatch_incr; auto. 
Qed.

Lemma smatch_incr: forall m b p, smatch bc1 m b p -> smatch bc2 m b p.
Proof.
  intros. destruct H as [A B]. split; intros. 
  - auto.
  - exploit B ; eauto. destruct mv ; simpl. apply epmatch_incr ; eauto.
Qed.

Lemma bmatch_incr: forall m b ab, bmatch bc1 m b ab -> bmatch bc2 m b ab.
Proof.
  intros. destruct H as [B1 B2]. split. 
  apply smatch_incr; auto. 
  intros. apply vmatch_incr; eauto. 
Qed.

End MATCH_INCR.

(** * Matching and memory injections. *)

Definition inj_of_bc (bc: block_classification) : meminj :=
  fun b => match bc b with BCinvalid => None | _ => Some(b, 0) end.

Lemma inj_of_bc_valid:
  forall (bc: block_classification) b, bc b <> BCinvalid -> inj_of_bc bc b = Some(b, 0).
Proof.
  intros. unfold inj_of_bc. destruct (bc b); congruence. 
Qed.

Lemma inj_of_bc_inv:
  forall (bc: block_classification) b b' delta,
  inj_of_bc bc b = Some(b', delta) -> bc b <> BCinvalid /\ b' = b /\ delta = 0.
Proof.
  unfold inj_of_bc; intros. destruct (bc b); intuition congruence.
Qed.

Lemma pmatch_inj:
  forall bc b ofs p, pmatch bc b ofs p -> inj_of_bc bc b = Some(b, 0).
Proof.
  intros. apply inj_of_bc_valid. inv H; congruence. 
Qed.

Definition bc_nostack (bc: block_classification) : Prop :=
  forall b, bc b <> BCstack.





(** * Abstracting RTL register environments *)

Module AVal <: SEMILATTICE_WITH_TOP.

  Definition t := aval.
  Definition eq (x y: t) := (x = y).
  Definition eq_refl: forall x, eq x x := (@refl_equal t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@sym_equal t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@trans_equal t).
  Definition beq (x y: t) : bool := proj_sumbool (eq_aval x y).
  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof. unfold beq; intros. InvBooleans. auto. Qed.
  Definition ge := evge.
  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof. unfold eq, ge; intros. subst y. apply evge_refl. Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof. unfold ge; intros. eapply evge_trans; eauto. Qed.
  Definition bot : t := Ptr Pbot.
  Lemma ge_bot: forall x, ge x bot.
  Proof. constructor. reflexivity.
  Qed.
  Definition top : t := Vtop.
  Lemma ge_top: forall x, ge top x.
  Proof. intros. apply evge_top. Qed.
  Definition lub := evlub.
  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof evge_lub_l.
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof. unfold lub. intros. rewrite evlub_comm.
  apply evge_lub_l. Qed.
End AVal.

Module AE := LPMap(AVal).

Definition aenv := AE.t. 

Section MATCHENV.

Variable bc: block_classification.

Definition ematch (e: regset) (ae: aenv) : Prop :=
  forall r, evmatch bc  e#r (AE.get r ae). 

Lemma ematch_ge:
  forall e ae1 ae2,
  ematch e ae1 -> AE.ge ae2 ae1 -> ematch e ae2.
Proof.
  intros; red; intros. apply evmatch_ge with (AE.get r ae1); auto. apply H0. Qed.

Lemma ematch_update:
  forall e ae v av r,
  ematch e ae -> evmatch bc  v av -> ematch (e#r <- v) (AE.set r av ae).
Proof.
  intros; red; intros. rewrite AE.gsspec. rewrite PMap.gsspec. 
  destruct (peq r0 r); auto. 
  red; intros. specialize (H xH). subst ae. simpl in H. inv H. inv H3.
  unfold AVal.eq; red; intros. subst av. inv H0. inv H3.
Qed.

Fixpoint einit_regs (rl: list reg) : aenv :=
  match rl with
  | r1 :: rs => AE.set r1 (Ptr Nonstack) (einit_regs rs)
  | nil => AE.top
  end.

Lemma ematch_init:
  forall rl vl,
  (forall v, In v vl -> evmatch bc  v (Ptr Nonstack)) ->
  ematch (init_regs vl rl) (einit_regs rl).
Proof.
  induction rl; simpl; intros. 
- red; intros. rewrite Regmap.gi. simpl AE.get. rewrite PTree.gempty. 
  constructor. constructor. repeat intro; reflexivity.
- destruct vl as [ | v1 vs ]. 
  + assert (ematch (init_regs nil rl) (einit_regs rl)).
    { apply IHrl. simpl; tauto. }
    replace (init_regs nil rl) with (Regmap.init (Eval Vundef)) in H0 by (destruct rl; auto). 
    red; intros. rewrite AE.gsspec. destruct (peq r a). 
    rewrite Regmap.gi. constructor. constructor. repeat intro ; reflexivity.
    apply H0. 
    red; intros EQ; rewrite EQ in H0. specialize (H0 xH). simpl in H0. inv H0. inv H3.
    unfold AVal.eq, AVal.bot. congruence.
  + assert (ematch (init_regs vs rl) (einit_regs rl)).
    { apply IHrl. eauto with coqlib. }
    red; intros. rewrite Regmap.gsspec. rewrite AE.gsspec. destruct (peq r a). 
    auto with coqlib.
    apply H0. 
    red; intros EQ; rewrite EQ in H0. specialize (H0 xH). simpl in H0. inv H0. inv H3.
    unfold AVal.eq, AVal.bot. congruence.
Qed.

Fixpoint eforget (rl: list reg) (ae: aenv) {struct rl} : aenv :=
  match rl with
  | nil => ae
  | r1 :: rs => eforget rs (AE.set r1 Vtop ae)
  end.

Lemma eforget_ge:
  forall rl ae, AE.ge (eforget rl ae) ae.
Proof.
  unfold AE.ge; intros. revert rl ae; induction rl; intros; simpl.
  apply AVal.ge_refl. apply AVal.eq_refl.
  destruct ae. unfold AE.get at 2. apply AVal.ge_bot.
  eapply AVal.ge_trans. apply IHrl. rewrite AE.gsspec.
  destruct (peq p a). apply AVal.ge_top. apply AVal.ge_refl. apply AVal.eq_refl.
  congruence. 
  unfold AVal.eq, Vtop, AVal.bot. congruence.
Qed.

Lemma ematch_forget:
  forall e rl ae, ematch e ae -> ematch e (eforget rl ae).
Proof.
  intros. eapply ematch_ge; eauto. apply eforget_ge. 
Qed.

End MATCHENV.

Lemma ematch_incr:
  forall bc bc'  e ae, ematch bc e ae -> bc_incr bc bc' -> ematch bc'  e ae.
Proof.
  intros; red; intros. apply vmatch_incr with bc; auto. 
Qed.

(** * Lattice for dataflow analysis *)

Module VA <: SEMILATTICE.

  Inductive t' := Bot | State (ae: aenv) (am: amem).
  Definition t := t'.

  Definition eq (x y: t) :=
    match x, y with
    | Bot, Bot => True
    | State ae1 am1, State ae2 am2 =>
        AE.eq ae1 ae2 /\ forall bc m, mmatch bc m am1 <-> mmatch bc m am2
    | _, _ => False
    end.

  Lemma eq_refl: forall x, eq x x.
  Proof.
    destruct x; simpl. auto. split. apply AE.eq_refl. tauto. 
  Qed.
  Lemma eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    destruct x, y; simpl; auto. intros [A B]. 
    split. apply AE.eq_sym; auto. intros. rewrite B. tauto. 
  Qed.
  Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    destruct x, y, z; simpl; try tauto. intros [A B] [C D]; split.
    eapply AE.eq_trans; eauto.
    intros. rewrite B; auto.
  Qed.

  Definition beq (x y: t) : bool :=
    match x, y with
    | Bot, Bot => true
    | State ae1 am1, State ae2 am2 => AE.beq ae1 ae2 && mbeq am1 am2
    | _, _ => false
    end.
 
  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    destruct x, y; simpl; intros. 
    auto.
    congruence.
    congruence.
    InvBooleans; split.
    apply AE.beq_correct; auto.
    intros. apply mbeq_sound; auto. 
  Qed.

  Definition ge (x y: t) : Prop :=
    match x, y with
    | _, Bot => True
    | Bot, _ => False
    | State ae1 am1, State ae2 am2 => AE.ge ae1 ae2 /\ forall bc m, mmatch bc m am2 -> mmatch bc m am1
    end.

  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    destruct x, y; simpl; try tauto. intros [A B]; split. 
    apply AE.ge_refl; auto.
    intros. rewrite B; auto. 
  Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    destruct x, y, z; simpl; try tauto. intros [A B] [C D]; split.
    eapply AE.ge_trans; eauto. 
    eauto. 
  Qed.

  Definition bot : t := Bot.
  Lemma ge_bot: forall x, ge x bot.
  Proof.
    destruct x; simpl; auto. 
  Qed.

  Definition lub (x y: t) : t :=
    match x, y with
    | Bot, _ => y
    | _, Bot => x
    | State ae1 am1, State ae2 am2 => State (AE.lub ae1 ae2) (mlub am1 am2)
    end.

  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    destruct x, y.
    apply ge_refl; apply eq_refl.
    simpl. auto.
    apply ge_refl; apply eq_refl.
    simpl. split. apply AE.ge_lub_left. intros; apply mmatch_lub_l; auto.
  Qed.
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    destruct x, y.
    apply ge_refl; apply eq_refl.
    apply ge_refl; apply eq_refl.
    simpl. auto.
    simpl. split. apply AE.ge_lub_right. intros; apply mmatch_lub_r; auto.
  Qed.

End VA.

Hint Constructors cmatch : va.
Hint Constructors epmatch: va.
Hint Constructors evmatch: va.
Hint Resolve cnot_sound symbol_address_sound
       shl_sound shru_sound shr_sound
       and_sound or_sound xor_sound notint_sound 
       ror_sound rolm_sound
       neg_sound add_sound sub_sound
       mul_sound mulhs_sound mulhu_sound
       divs_sound divu_sound mods_sound modu_sound shrx_sound
       negf_sound absf_sound
       addf_sound subf_sound mulf_sound divf_sound
       negfs_sound absfs_sound
       addfs_sound subfs_sound mulfs_sound divfs_sound
       zero_ext_sound sign_ext_sound singleoffloat_sound floatofsingle_sound
       intoffloat_sound intuoffloat_sound floatofint_sound floatofintu_sound
       intofsingle_sound intuofsingle_sound singleofint_sound singleofintu_sound
       longofwords_sound loword_sound hiword_sound  
       cmpu_bool_sound cmp_bool_sound cmpf_bool_sound cmpfs_bool_sound
       maskzero_sound : va.
