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

(** Correctness proof for operator strength reduction. *)

Require Import Coqlib.
Require Import Compopts.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Values_symbolic.
Require Import Values_symbolictype.
Require Import ValueDomain.
Require Import ConstpropOp.
Require Import Setoid.
(* Require Import PpsimplCompcert. *)
Require Import Psatz.




Add Parametric Morphism : Val.sub with signature  same_eval  ==> same_eval ==> same_eval as sub_lessdef.
Proof.
  intros.
  apply binop_same_eval; auto.
Qed.

Add Parametric Morphism : Val.and with signature  same_eval  ==> same_eval ==> same_eval as and_lessdef.
Proof.
  intros.
  apply binop_same_eval; auto.
Qed.

Add Parametric Morphism : Val.modu with signature  same_eval  ==> same_eval ==> same_eval as modu_lessdef.
Proof.
  intros.
  apply binop_same_eval; auto.
Qed.

Add Parametric Morphism : Val.or with signature  same_eval  ==> same_eval ==> same_eval as or_lessdef.
Proof.
  intros.
  apply binop_same_eval; auto.
Qed.

Add Parametric Morphism : Val.xor with signature  same_eval  ==> same_eval ==> same_eval as xor_lessdef.
Proof.
  intros.
  apply binop_same_eval; auto.
Qed.

Add Parametric Morphism : Val.divs with signature  same_eval  ==> same_eval ==> same_eval as divs_lessdef.
Proof.
  intros.
  apply binop_same_eval; auto.
Qed.

Add Parametric Morphism : Val.divu with signature  same_eval  ==> same_eval ==> same_eval as divu_lessdef.
Proof.
  intros.
  apply binop_same_eval; auto.
Qed.

Add Parametric Morphism : Val.shru with signature  same_eval  ==> same_eval ==> same_eval as shru_lessdef.
Proof.
  intros.
  apply binop_same_eval; auto.
Qed.


Add Parametric Morphism : Val.shrx with signature  same_eval  ==> same_eval ==> same_eval as shrx_lessdef.
Proof.
  intros.
  apply binop_same_eval; auto.
Qed.



Lemma val_mul_commut :
  forall x y, 
    same_eval (Val.mul x y) (Val.mul y x).
Proof.
  repeat intro.
  simpl. rewrite  Val.mul_commut.
  reflexivity.
Qed.


Lemma val_and_commut :
  forall x y, 
    same_eval (Val.and x y) (Val.and y x).
Proof.
  repeat intro.
  simpl. rewrite  Val.and_commut.
  reflexivity.
Qed.

Lemma val_or_commut :
  forall x y, 
    same_eval (Val.or x y) (Val.or y x).
Proof.
  repeat intro.
  simpl. rewrite  Val.or_commut.
  reflexivity.
Qed.


(** We now show that strength reduction over operators and addressing
  modes preserve semantics: the strength-reduced operations and
  addressings evaluate to the same values as the original ones if the
  actual arguments match the static approximations used for strength
  reduction. *)

Section STRENGTH_REDUCTION.

Variable bc: block_classification.
Variable ge: genv.
Hypothesis GENV: genv_match bc ge.
Variable sp: block.
Hypothesis STACK: bc sp = BCstack.
Variable ae: AE.t.
Variable e: regset.
Variable m: mem.
Hypothesis MATCH: ematch bc e ae.

Lemma match_G:
  forall r id ofs,
  AE.get r ae = Ptr(Gl id ofs) -> Val.lessdef e#r (Eval (Genv.symbol_address ge id ofs)).
Proof.
  intros.
  apply vmatch_ptr_gl with bc; auto. rewrite <- H. apply MATCH. 
Qed.

Lemma match_S:
  forall r ofs,
  AE.get r ae = Ptr(Stk ofs) -> Val.lessdef e#r (Eval (Vptr sp ofs)).
Proof.
  intros. apply vmatch_ptr_stk with bc; auto. rewrite <- H. apply MATCH.
Qed.

Lemma inj_hd : forall (A : Type) (e:A) l e' l',
    e :: l =  e' :: l' -> e = e'.
Proof.
  intros. injection H ; auto.
Qed.

Lemma inj_tl : forall (A : Type) (e:A) l e' l',
    e :: l =  e' :: l' -> l = l'.
Proof.
  intros. injection H ; auto.
Qed.

Lemma inj_some : forall (A : Type) (x y :  A),
    Some x = Some y -> x = y.
Proof.
  intros.
  injection  H ; auto.
Qed.
  
Ltac InvApproxRegs :=
  match goal with
  | [H : ?A :: nil = ?B :: nil |- _ ] => 
     generalize (inj_hd _  A nil B nil H);
       clear H; intros; InvApproxRegs
    | [ H: ?A :: ?B = ?C :: ?D |- _ ] => 
    generalize (inj_tl _  A B C D H);
      generalize (inj_hd _  A B C D H) ;
      clear H; intros; InvApproxRegs
  | [ H: ?v = AE.get ?r ae |- _ ] => 
        generalize (MATCH r); rewrite <- H; clear H; intro; InvApproxRegs
  | [H : Some ?A = Some ?B |- _ ] =>  apply inj_some in H ; InvApproxRegs
  | _ => idtac
  end.

Ltac rew_cst H :=
  unfold is_constant, is_pointer in H ;
  erewrite <- H in *; eauto.


Lemma swap_cmp_bool : forall c e1 e2,
    same_eval (Val.cmp_bool (swap_comparison c) e1 e2)  (Val.cmp_bool c e2 e1).
Proof.
  repeat intro.
  unfold Val.cmp_bool. simpl.
  rewrite Val.swap_cmp_bool.
  reflexivity.
Qed.

Add Parametric Morphism (c : comparison) :
  (Val.cmp_bool c) with signature (same_eval ==> same_eval ==> same_eval) as cmp_bool_morph.
Proof.
  intros. unfold Val.cmp_bool.
  apply binop_same_eval; eauto.
Qed.

Add Parametric Morphism (c : comparison) :
  (Val.cmpu_bool c) with signature (same_eval ==> same_eval ==> same_eval) as cmpu_bool_morph.
Proof.
  intros. unfold Val.cmpu_bool.
  apply binop_same_eval; eauto.
Qed.

Existing Instance Op.EquiOptSameEval.

Lemma shift_symbol_address' :
  forall id ofs F e
  ,
    
    evmatch bc e (Ptr (Gl id ofs)) ->
    exists b, Genv.symbol_address' ge id (F ofs) = Some (Eval (Vptr b (F ofs)))
              /\ bc b = BCglob id.
Proof.
  intros.
  unfold Genv.symbol_address'.
  inv H. inv H2.
  replace (Genv.find_symbol ge id) with (Some b).
  exists b ; intuition.
  symmetry.
  apply GENV. auto.
Qed.

Ltac get_shift_symbol_match := 
  match goal with
  | H : evmatch _ ?E (Ptr (Gl ?id ?ofs)) |-
    context [Genv.symbol_address' _ _ ?F = Some _]  => constr:(F,E,H,ofs)
  |  H : evmatch _ ?E (Ptr (Gl ?id ?ofs)) |-
     exists res' : expr_sym,
       option_map _
                  (Genv.symbol_address' _ _ ?F) = Some _ /\ _ => constr:(F,E,H,ofs)
  end.


Ltac shift_symbol' :=
    let R := get_shift_symbol_match in 
    match R with
      (?F,?E,?H,?ofs) => 
    let xx := fresh in 
    set (xx := F) ; pattern ofs in xx ; 
    match goal with
    | xx := ?F ofs |- _ =>
      let B := fresh "B" in
      let EQ := fresh "EQ" in
      let BC := fresh "BC" in 
      destruct (shift_symbol_address' _ _ F E H) as [B [EQ BC]] ;
        unfold xx ; clear xx ; rewrite EQ;
        inv H ;
        match goal with
        | H1 : epmatch _ E _ |- _ => inv H1
        end
    end
  end.


Lemma vmatch_ptr_stk :
  forall v ofs b,
         bc b = BCstack -> 
         evmatch bc v (Ptr (Stk ofs)) ->
         is_pointer b ofs  v.
Proof.
  intros.
  inv H0. inv H3.
  assert (b = b0) by (eapply bc_stack ; eauto).
  congruence.
Qed.
  

Ltac SimplVM :=
  match goal with
  | [ H: evmatch _ ?v (I ?n) |- _ ] =>
      let E := fresh in
      assert (E: is_constant (Vint n)  v) by (inversion H; auto);
      try rew_cst  E  ; clear H; SimplVM
  | [ H: evmatch _ ?v (F ?n) |- _ ] =>
      let E := fresh in
      assert (E: v = Vfloat n) by (inversion H; auto);
      rewrite E in *; clear H; SimplVM
  | [ H: evmatch _ ?v (FS ?n) |- _ ] =>
      let E := fresh in
      assert (E: v = Vsingle n) by (inversion H; auto);
      rewrite E in *; clear H; SimplVM
  | [ _: evmatch _ ?v (Ptr(Gl ?id ?ofs)) |- _ ] =>
    shift_symbol'; SimplVM
  | [ H: evmatch _ ?v (Ptr(Stk ?ofs)) |- _ ] =>
      assert (E: is_pointer sp ofs v) by (eapply vmatch_ptr_stk; eauto); 
      clear H; SimplVM
  | _ => idtac
  end.

Unset Ltac Debug.

Lemma cond_strength_reduction_correct:
  forall cond args vl,
  vl = map (fun r => AE.get r ae) args ->
  let (cond', args') := cond_strength_reduction cond args vl in
  opt_same_eval (eval_condition cond' e##args') (eval_condition cond e##args).
Proof.
  intros until vl. unfold cond_strength_reduction.
  case (cond_strength_reduction_match cond args vl); simpl; intros; InvApproxRegs;
  try constructor ; SimplVM.
  - apply swap_cmp_bool.
  - reflexivity.
  - symmetry.
    apply cmpu_bool_swap_comparison.
  -  reflexivity.
  -  reflexivity.
Qed.

Lemma is_unop_trans_same_eval :
  forall G x y
        (Unop : is_unop_trans G)
        (Same : same_eval x y),
    same_eval (G x) (G y).
Proof.
  intros.
  induction  Unop; try reflexivity; auto.
  apply unop_same_eval; auto.
  apply binop_same_eval ; auto.
Qed.
    


(*
Lemma shift_symbol_address' :
  forall id ofs F G e
         (Unop : is_unop_trans G)
         (FG : forall b, same_eval (G (Eval (Vptr b ofs))) (Eval (Vptr b (F ofs))))
  ,
    
    evmatch bc e (Ptr (Gl id ofs)) ->
    exists res', Genv.symbol_address' ge id (F ofs) = Some res' /\
                 Val.lessdef (G e) res'.
Proof.
  intros.
  unfold Genv.symbol_address'.
  inv H. inv H2.
  replace (Genv.find_symbol ge id) with (Some b).
  TrivialExists.
  - unfold is_pointer in H4.
    apply is_unop_trans_same_eval with (G := G) in H4; auto.
    symmetry in H4.
    repeat intro. rewrite H4. rewrite FG.
    constructor.
  - 
  symmetry. apply GENV. auto.
Qed.
*)

Ltac find_trans X V :=
  set (x := X) ; pattern V in x ; 
  match goal with
  | x := ?F V |- _ => change x with (F V) ; clear x
  end.


Unset Ltac Debug.

Lemma same_eval_lessdef :
  forall x y,  same_eval x y -> Val.lessdef x y.
Proof.
  repeat intro.
  rewrite H.
  constructor.
Qed.

Add Parametric Morphism : Val.lessdef with signature same_eval ==> same_eval ==> iff as same_eval_lessdef_morph.
Proof.
  intros.
  split ; intros.
  repeat intro.
  rewrite <- H. rewrite <- H0. apply H1.
  repeat intro.
  rewrite H. rewrite H0. apply H1.
Qed.
    
  Add Parametric Morphism (bo : binop_t) (st st' : styp) :
  (Ebinop bo st st') with signature (same_eval ==> same_eval ==> Val.lessdef) as Ebinop_same_eval_lessdef.
Proof.
  intros.
  apply Val.lessdef_binop.
  apply same_eval_lessdef; auto.
  apply same_eval_lessdef ; eauto.
Qed.

  Add Parametric Morphism  :
  (Val.add) with signature (same_eval ==> same_eval ==> same_eval) as add_same_eval.
Proof.
  intros.
  apply binop_same_eval ; auto.
Qed.

  Add Parametric Morphism  :
  (Val.add) with signature (same_eval ==> same_eval ==> Val.lessdef) as add_lessdef.
Proof.
  intros.
  apply Val.lessdef_binop ; auto.
  apply same_eval_lessdef ; auto.
  apply same_eval_lessdef ; auto.
Qed.



Instance lessdefRef : Reflexive Val.lessdef.
Proof.
  unfold Reflexive.
  apply Val.lessdef_refl.
Qed.

Instance lessdefTrans : Transitive Val.lessdef.
Proof.
  unfold Transitive.
  apply Val.lessdef_trans.
Qed.

Lemma same_eval_add_Eval : forall b  o o',
    same_eval (Val.add (Eval (Vptr b o)) (Eval (Vint o'))) (Eval (Vptr b (Int.add o o'))).
Proof.
  repeat intro.
  simpl. 
  rewrite <- Int.add_assoc. reflexivity.
Qed.

Lemma same_eval_mul_Eval : forall o o',
    same_eval (Val.mul (Eval (Vint o)) (Eval (Vint o'))) (Eval (Vint (Int.mul o o'))).
Proof.
  repeat intro.
  simpl.  reflexivity.
Qed.



Add Parametric Morphism : Val.mul with signature  same_eval  ==> same_eval ==> same_eval as mul_same_eval.
Proof.
  apply binop_same_eval.
Qed.

Add Parametric Morphism : Val.shl with signature  same_eval  ==> same_eval ==> same_eval as shl_same_eval.
Proof.
  apply binop_same_eval.
Qed.

Add Parametric Morphism : Val.shr with signature  same_eval  ==> same_eval ==> same_eval as shr_same_eval.
Proof.
  apply binop_same_eval.
Qed.

Add Parametric Morphism : Val.shru with signature  same_eval  ==> same_eval ==> same_eval as shru_same_eval.
Proof.
  apply binop_same_eval.
Qed.


Add Parametric Morphism : Val.mul with signature  same_eval  ==> same_eval ==> Val.lessdef as mul_lessdef.
Proof.
  intros.
  apply Val.lessdef_binop.
  rewrite H. constructor.
  rewrite H0. constructor.
Qed.


Add Parametric Morphism : Val.mulf with signature  same_eval  ==> same_eval ==> same_eval as mulf_same_eval.
Proof.
  intros.
  apply binop_same_eval;
  auto.
Qed.


Add Parametric Morphism : Val.mulfs with signature  same_eval  ==> same_eval ==> same_eval as mulfs_same_eval.
Proof.
  intros.
  apply binop_same_eval;
  auto.
Qed.




Lemma addr_strength_reduction_correct:
  forall addr args vl res,
  vl = map (fun r => AE.get r ae) args ->
  eval_addressing ge (Eval (Vptr sp Int.zero)) addr e##args = Some res ->
  let (addr', args') := addr_strength_reduction addr args vl in
  exists res', eval_addressing ge (Eval (Vptr sp Int.zero)) addr' e##args' = Some res' /\ Val.lessdef res res'.
Proof.
  intros until res. unfold addr_strength_reduction.
  destruct (addr_strength_reduction_match addr args vl); simpl;
  intros VL EA ;InvApproxRegs; inv EA; SimplVM; simpl; TrivialExists.
  - apply same_eval_lessdef.
    rew_cst H4.
    assert (b = B) by (eapply bc_glob ; eauto).
    subst.
    rewrite same_eval_add_Eval.
    reflexivity.
  - apply same_eval_lessdef.
    rew_cst E.
    repeat rewrite same_eval_add_Eval.
    rewrite Int.add_zero_l. reflexivity.
  -
    apply same_eval_lessdef.
    rew_cst H1.
    rew_cst H5.
    assert (b = B) by (eapply bc_glob ; eauto).
    subst.
    repeat rewrite same_eval_add_Eval.
    reflexivity.
  - apply same_eval_lessdef.
    rew_cst H1.
    rew_cst H5.
    assert (b = B) by (eapply bc_glob ; eauto).
    subst.
    rewrite Val.add_assoc.
    repeat rewrite same_eval_add_Eval.
    rewrite Val.add_commut.
    repeat rewrite same_eval_add_Eval.
    rewrite Int.add_commut.
    rewrite Int.add_assoc. reflexivity.
  - apply same_eval_lessdef.
    rew_cst  H1. rew_cst E.
    repeat rewrite same_eval_add_Eval.
    rewrite Int.add_zero_l. reflexivity.    
  - apply same_eval_lessdef.
     rew_cst  H1. rew_cst E.
     repeat rewrite same_eval_add_Eval.
     rewrite Int.add_zero_l.
     rewrite (Val.add_commut (Eval (Vint n1))).
     repeat rewrite same_eval_add_Eval.
     rewrite (Int.add_commut n2).
     reflexivity.
  - 
    rewrite (Val.add_commut (e #r1)).
    rewrite Val.add_assoc.
     apply Val.lessdef_binop.
     constructor.
     rew_cst H5.
     repeat rewrite same_eval_add_Eval.
     assert (b = B) by (eapply bc_glob ; eauto).
     subst ; constructor.
  -  assert (b = B) by (eapply bc_glob ; eauto).
     subst.
     rewrite Val.add_assoc.
     rew_cst H5.
     repeat rewrite same_eval_add_Eval.
     constructor.
  -  rew_cst H1.
     rewrite (Val.add_commut (Eval (Vint n1))).
     rewrite Val.add_assoc.
     apply Val.lessdef_binop.
     constructor.
     constructor.
  -  rew_cst H1.
     rewrite Val.add_assoc.
     apply Val.lessdef_binop.
     constructor.
     constructor.
  - rew_cst H5.
    rew_cst H1.
    assert (b = B) by (eapply bc_glob ; eauto).
    subst.
    repeat rewrite same_eval_mul_Eval.
    rewrite <- Val.add_assoc.
    repeat rewrite same_eval_add_Eval.
    reflexivity.
  - rew_cst H5.
    assert (b = B) by (eapply bc_glob ; eauto).
    subst.
    rewrite <- Val.add_assoc.
    rewrite (Val.add_commut (Eval (Vptr B n1))).
    rewrite Val.add_assoc.
    repeat rewrite same_eval_add_Eval.
    constructor.
  - rew_cst H1.
    repeat rewrite same_eval_mul_Eval.
    apply Val.lessdef_binop.
    constructor.
    constructor.
  -
    exploit Op.option_map_symbol_address'_some ; eauto.
    intros (B & EQ1 & EQ2).
    subst. exists (Eval (Vptr B (Int.add ofs n1))).
    split.
    apply Genv.symbol_address'_same in EQ1.
    rewrite <- Genv.symbol_address'_same.
    unfold Genv.symbol_address in *.
    destruct (Genv.find_symbol ge id) ; intuition.
    rew_cst H0.
    rewrite Val.add_commut.
    repeat rewrite same_eval_add_Eval.
    constructor.
  - 
    exploit Op.option_map_symbol_address'_some ; eauto.
    intros (B & EQ1 & EQ2).
    subst. exists (Eval (Vptr B (Int.add ofs (Int.mul sc n1)))).
    split.
    apply Genv.symbol_address'_same in EQ1.
    rewrite <- Genv.symbol_address'_same.
    unfold Genv.symbol_address in *.
    destruct (Genv.find_symbol ge id) ; intuition.
    rew_cst H0.
    rewrite Val.add_commut.
    repeat rewrite same_eval_mul_Eval.
    repeat rewrite same_eval_add_Eval.
    rewrite Int.mul_commut.
    constructor.
Qed.


Inductive opt_lessdef  : option expr_sym -> option expr_sym -> Prop :=
| opt_lessdef_None : opt_lessdef None None
| opt_lessdef_Some : forall e e',
    Val.lessdef e e' ->
    opt_lessdef (Some e) (Some e').


Lemma make_cmp_base_correct:
  forall c args vl,
  vl = map (fun r => AE.get r ae) args ->
  let (op', args') := make_cmp_base c args vl in
  opt_lessdef (eval_condition c e##args)
              (eval_operation ge (Eval (Vptr sp Int.zero)) op' e##args').
Proof.
  intros. unfold make_cmp_base. 
  generalize (cond_strength_reduction_correct c args vl H). 
  destruct (cond_strength_reduction c args vl) as [c' args']. intros EQ.
  simpl; eauto.
  inv EQ. constructor.
  constructor. rewrite OPTSAME. constructor.
Qed.

Lemma vincl_Ptop_one :
  forall r1 ae F G
         (MATCH : ematch bc e ae)
         (INCL  : vincl (AE.get r1 ae) (Uns Ptop 1) = true)
         (FEQ : forall a em v,
             (ExprEval.eSexpr a em v = Vundef \/
              ExprEval.eSexpr a em v = Vint Int.zero \/
              ExprEval.eSexpr a em v = Vint Int.one)-> 
            ExprEval.eSexpr a em (F v) = ExprEval.eSexpr a em (G v)),
    Val.lessdef (F (e # r1)) (G (e # r1)).
Proof.
  intros.
  eapply evincl_ge in INCL.
  eapply evmatch_ge in INCL ; eauto.
  inv INCL.
  repeat intro.
  destruct (H3 alloc em).
  destruct H.
  apply is_uns_1 in H0.
  destruct H0 ; subst.
  inv H.
  rewrite FEQ; intuition auto.
  rewrite FEQ; intuition auto.
  inv H.
  rewrite FEQ; intuition auto.
  rewrite FEQ; intuition auto.
Qed.
  
Lemma make_cmp_correct:
  forall c args vl,
  vl = map (fun r => AE.get r ae) args ->
  let (op', args') := make_cmp c args vl in
  opt_lessdef (eval_condition c e##args) (eval_operation ge (Eval (Vptr sp Int.zero)) op' e##args').
Proof.
  intros c args vl.
  unfold make_cmp. case (make_cmp_match c args vl); intros.
  destruct (Int.eq_dec n Int.one && vincl v1 (Uns Ptop 1)) eqn:E1.
  {
    simpl in H; inv H. InvBooleans. subst n.
    simpl. constructor.
    eapply vincl_Ptop_one with (F := (fun x => (Val.cmp_bool Ceq x (Eval (Vint Int.one)))))
                                 (G := (fun x => x))
    ; eauto.
    intuition subst.
    simpl. rewrite H1. reflexivity.
    simpl. rewrite H ; reflexivity.
    simpl. rewrite H ; reflexivity.
  }
  destruct (Int.eq_dec n Int.zero && vincl v1 (Uns Ptop 1)) eqn:E0.
  {
    simpl in H; inv H. InvBooleans. subst n.
    simpl. constructor.
    set (F := (fun x => (Val.cmp_bool Ceq x (Eval (Vint Int.zero))))).
    set (G := (fun x => (Val.xor x (Eval (Vint Int.one))))).
    change (Val.lessdef (F (e #r1)) (G (e#r1))).
    eapply vincl_Ptop_one; eauto.
    unfold F, G.
    intuition subst.
    simpl ; rewrite H1 ; reflexivity.
    simpl ; rewrite H ; reflexivity.
    simpl ; rewrite H ; reflexivity.
  }
  simpl. constructor. constructor.
  destruct (Int.eq_dec n Int.zero && vincl v1 (Uns Ptop 1)) eqn:E1.
  {
  simpl in H; inv H. InvBooleans. subst n.
  simpl. constructor.
    set (F := (fun x => (Val.cmp_bool Cne x (Eval (Vint Int.zero))))).
    change (Val.lessdef (F (e #r1)) ((fun x => x) (e#r1))).
    eapply vincl_Ptop_one; eauto.
    unfold F.
    intuition subst.
    simpl ; rewrite H1 ; reflexivity.
    simpl ; rewrite H ; reflexivity.
    simpl ; rewrite H ; reflexivity.
  }
  destruct (Int.eq_dec n Int.one && vincl v1 (Uns Ptop 1)) eqn:E2.
  {
    simpl in H; inv H. InvBooleans. subst n.
    simpl. constructor.
    set (F := (fun x => (Val.cmp_bool Cne x (Eval (Vint Int.one))))).
    set (G := (fun x => (Val.xor x (Eval (Vint Int.one))))).
    change (Val.lessdef (F (e #r1)) (G (e#r1))).
    eapply vincl_Ptop_one; eauto.
    unfold F,G.
    intuition subst.
    simpl ; rewrite H1 ; reflexivity.
    simpl ; rewrite H ; reflexivity.
    simpl ; rewrite H ; reflexivity.
  }
  apply make_cmp_base_correct; auto.
 apply make_cmp_base_correct; auto.
Qed.

Ltac lessdef_dest x :=
  let a := fresh "a" in
  let u := fresh "u" in
  intros a u ; simpl ; destruct (ExprEval.eSexpr a u x) ; simpl; auto.
  

Lemma make_addimm_correct:
  forall n r c,
    is_constant (Vint n) c -> 
    let (op, args) := make_addimm n r in
    opt_lessdef (Some (Val.add e#r c)) (eval_operation ge (Eval (Vptr sp Int.zero)) op e##args).
Proof.
  intros. unfold make_addimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. 
  subst.
  constructor. rew_cst H.
  lessdef_dest (e # r); auto; simpl; rewrite Int.add_zero ; auto.
  simpl. constructor. rew_cst H.
Qed.
  
Lemma make_shlimm_correct:
  forall n r1 r2,
    is_constant (Vint n) e#r2 -> 
  let (op, args) := make_shlimm n r1 r2 in
  opt_lessdef (Some (Val.shl e#r1 e #r2)) (eval_operation ge (Eval (Vptr sp Int.zero)) op e##args).
Proof.
  intros; unfold make_shlimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  - 
    constructor. rew_cst H.
    lessdef_dest (e#r1); simpl; auto. rewrite Int.shl_zero. auto.
  - 
    destruct (Int.ltu n Int.iwordsize).
    constructor. rew_cst H.
    repeat constructor.
Qed.

Lemma make_shrimm_correct:
  forall n r1 r2,
    is_constant (Vint n) e#r2 -> 
  let (op, args) := make_shrimm n r1 r2 in
  opt_lessdef (Some ((Val.shr e#r1 e#r2))) (eval_operation ge (Eval (Vptr sp Int.zero)) op e##args).
Proof.
  intros; unfold make_shrimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  constructor. rew_cst H.  lessdef_dest (e#r1); simpl; auto. rewrite Int.shr_zero. auto.
  destruct (Int.ltu n Int.iwordsize).
  simpl ; repeat constructor.
  simpl.  rew_cst H. repeat constructor. 
Qed.

Lemma make_shruimm_correct:
  forall n r1 r2,
    is_constant  (Vint n) e#r2 ->
  let (op, args) := make_shruimm n r1 r2 in
  opt_lessdef (Some (Val.shru e#r1 e # r2)) (eval_operation ge (Eval (Vptr sp Int.zero)) op e##args).
Proof.
  intros; unfold make_shruimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  simpl ; constructor.  rew_cst H.
  lessdef_dest (e#r1); simpl; auto. rewrite Int.shru_zero. auto.
  destruct (Int.ltu n Int.iwordsize).
  repeat constructor. rew_cst H.
  repeat constructor. 
Qed.

Lemma val_mul_pow2 : 
  forall x y (n logn : int),
    is_constant (Vint n) y ->
    Int.is_power2 n = Some logn ->
    same_eval (Val.mul x y) (Val.shl x (Eval (Vint logn))).
Proof.
  repeat intro.
  simpl. rew_cst H. simpl.
  erewrite Val.mul_pow2; eauto.
Qed.


Lemma make_mulimm_correct:
  forall n r1 en,
    is_constant (Vint n) en -> 
  let (op, args) := make_mulimm n r1 in
  opt_lessdef (Some (Val.mul e#r1 en)) (eval_operation ge (Eval(Vptr sp Int.zero)) op e##args).
Proof.
  intros; unfold make_mulimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  simpl. constructor. rew_cst H. 
  lessdef_dest (e#r1); simpl; auto. rewrite Int.mul_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.one; intros. subst.
  simpl ; constructor. rew_cst H ; lessdef_dest (e#r1); simpl; auto. rewrite Int.mul_one; auto.
  destruct (Int.is_power2 n) eqn:?; intros.
  simpl. constructor. rew_cst H. rewrite <- val_mul_pow2; eauto. repeat intro ; reflexivity.
  simpl ; repeat constructor.
  rew_cst H.
Qed.

Lemma val_divs_pow2
     : forall x (n logn : int),
       Int.is_power2 n = Some logn ->
       Int.ltu logn (Int.repr 31) = true ->
       same_eval (Val.divs x (Eval (Vint n)))
                 (Val.shrx x (Eval (Vint logn))).
Proof.
  repeat intro ; simpl.
  apply f_equal.
  case_eq (Values.Val.divs (ExprEval.eSexpr alloc em x) (Vint n)).
  intros. symmetry. eapply Val.divs_pow2; eauto.
  destruct ((ExprEval.eSexpr alloc em x)) ; simpl; auto.
  rewrite H0.
  erewrite Int.divs_pow2; eauto.
  case_eq (Int.eq n Int.zero
           || Int.eq i (Int.repr Int.min_signed) && Int.eq n Int.mone); auto.  intros. rewrite orb_true_iff in H1.
  destruct H1 ; subst.
  apply Cop.int_eq_true in H1. subst.
  discriminate.
  InvBooleans. apply Cop.int_eq_true in H4 ; subst.
  discriminate.
Qed.
  
Lemma make_divimm_correct:
  forall n r1 r2,
  is_constant (Vint n) e#r2   ->
  let (op, args) := make_divimm n r1 r2 in
  opt_lessdef (Some (Val.divs e#r1 e#r2)) (eval_operation ge (Eval(Vptr sp Int.zero)) op e##args).
Proof.
intros; unfold make_divimm.
  destruct (Int.is_power2 n) eqn:?.
  destruct (Int.ltu i (Int.repr 31)) eqn:?.
  simpl ; constructor.
  rew_cst H.
  erewrite val_divs_pow2; eauto.
  constructor. rew_cst H. repeat constructor.
Qed.

Lemma val_divu_pow2
     : forall x (n logn : int),
       Int.is_power2 n = Some logn ->
       same_eval (Val.divu x (Eval (Vint n)))
                 (Val.shru x (Eval (Vint logn))).
Proof.
  repeat intro ; simpl.
  case_eq (Values.Val.divu (ExprEval.eSexpr alloc em x) (Vint n)).
  intros. symmetry. eapply Val.divu_pow2; eauto.
  simpl.
  destruct ((ExprEval.eSexpr alloc em x)) ; simpl; auto.
  predSpec Int.eq Int.eq_spec n Int.zero; intros;
  subst; discriminate.
Qed.

Lemma make_divuimm_correct:
  forall n r1 r2,
  is_constant (Vint n) e#r2  ->
  let (op, args) := make_divuimm n r1 r2 in
  opt_lessdef  (Some (Val.divu e#r1 e#r2)) (eval_operation ge (Eval (Vptr sp Int.zero)) op e##args).
Proof.
intros; unfold make_divuimm.
destruct (Int.is_power2 n) eqn:?.
constructor.
rew_cst H. rewrite val_divu_pow2 ; eauto.
repeat constructor.
Qed.

Lemma val_modu_pow2 : 
  forall x n logn,
    Int.is_power2 n = Some logn ->
    same_eval (Val.modu x (Eval (Vint n)))  (Val.and x (Eval (Vint (Int.sub n Int.one)))).
Proof.
  repeat intro ; simpl.
  destruct (ExprEval.eSexpr alloc em x) ; simpl; auto.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst.
  discriminate.
  simpl. apply f_equal. eapply Int.modu_and ; eauto.
Qed.
  

Lemma make_moduimm_correct:
  forall n r1 r2,
  is_constant (Vint n) e#r2   ->
  let (op, args) := make_moduimm n r1 r2 in
  opt_lessdef  (Some (Val.modu e#r1 e#r2)) (eval_operation ge (Eval (Vptr sp Int.zero)) op e##args).
Proof.
intros; unfold make_moduimm.
destruct (Int.is_power2 n) eqn:?.
simpl ; constructor. rew_cst H.
simpl. rewrite val_modu_pow2; eauto.
repeat constructor.
Qed.

Lemma and_zero  : forall x, 
    Val.lessdef (Val.and x (Eval (Vint Int.zero))) (Eval (Vint Int.zero)).
Proof.
  intros.
  lessdef_dest x.
  rewrite Int.and_zero ; auto.
Qed.

Lemma and_mone : forall x,
    Val.lessdef (Val.and x (Eval (Vint Int.mone))) x.
Proof.
  intros.
  lessdef_dest x.
  rewrite Int.and_mone ; auto.
Qed.


Lemma make_andimm_correct:
  forall n r x v,
  evmatch bc e#r x ->
  is_constant (Vint n) v -> 
  let (op, args) := make_andimm n r x in
  opt_lessdef (Some (Val.and e#r v)) (eval_operation ge (Eval (Vptr sp Int.zero)) op e##args).
Proof.
  intros; unfold make_andimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst n. simpl. constructor. rew_cst H0.  apply and_zero.
  predSpec Int.eq Int.eq_spec n Int.mone; intros.
  subst n. simpl. constructor. rew_cst H0. apply and_mone.
  destruct (match x with Uns _ k => Int.eq (Int.zero_ext k (Int.not n)) Int.zero
                       | _ => false end) eqn:UNS.
  destruct x; try congruence. 
  constructor.
  inv H; auto.
  generalize (Int.eq_spec (Int.zero_ext n0 (Int.not n)) Int.zero); rewrite UNS; intro EQ. rew_cst H0.
  repeat intro.
  simpl. destruct (H7 alloc em) as [i [LD ISUNS]].
  inv LD. rewrite H4. simpl.
  replace (Int.and i n) with i; auto.
  Int.bit_solve. destruct (zlt i0 n0).
  replace (Int.testbit n i0) with (negb (Int.testbit Int.zero i0)).
  rewrite Int.bits_zero. simpl. rewrite andb_true_r. auto. 
  rewrite <- EQ. rewrite Int.bits_zero_ext by omega. rewrite zlt_true by auto. 
  rewrite Int.bits_not by auto. apply negb_involutive. 
  rewrite ISUNS by auto. auto.
  constructor.
  repeat constructor.
  rew_cst H0.
Qed.

Lemma make_orimm_correct:
  forall n r x,
    is_constant (Vint n) x -> 
    let (op, args) := make_orimm n r in
    opt_lessdef (Some (Val.or e#r x)) (eval_operation ge (Eval(Vptr sp Int.zero)) op e##args).
Proof.
intros; unfold make_orimm.
predSpec Int.eq Int.eq_spec n Int.zero; intros.
{
  subst n. constructor.
  rew_cst H.  lessdef_dest (e#r); simpl; auto. rewrite Int.or_zero; auto.
}
predSpec Int.eq Int.eq_spec n Int.mone; intros.
{
  subst n. constructor.
  rew_cst H.
  lessdef_dest (e#r); simpl; auto. rewrite Int.or_mone; auto.
}
simpl. constructor. rew_cst H.
Qed.

Lemma make_xorimm_correct:
  forall n r x,
    is_constant (Vint n) x -> 
    let (op, args) := make_xorimm n r in
  opt_lessdef (Some (Val.xor e#r x)) (eval_operation ge (Eval (Vptr sp Int.zero)) op e##args).
Proof.
intros; unfold make_xorimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst n. constructor. rew_cst H. lessdef_dest (e#r) ; simpl ; auto.
  rewrite Int.xor_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.mone; intros.
  subst n.  simpl ; constructor. rew_cst H. lessdef_dest (e#r) ; simpl ; auto.
  repeat constructor. rew_cst H.
Qed.


Lemma make_mulfimm_correct:
  forall n r1 r2,
  is_constant (Vfloat n) e#r2  ->
  let (op, args) := make_mulfimm n r1 r1 r2 in
  opt_lessdef (Some (Val.mulf e#r1 e#r2))
              (eval_operation ge (Eval(Vptr sp Int.zero)) op e##args).
Proof.
  intros; unfold make_mulfimm. 
  destruct (Float.eq_dec n (Float.of_int (Int.repr 2))); intros. 
  simpl. constructor. rew_cst H. subst.
  lessdef_dest (e#r1); simpl; auto. rewrite Float.mul2_add; auto. 
  repeat constructor.
Qed.

Lemma make_mulfimm_correct_2:
  forall n r1 r2,
  is_constant (Vfloat n) e#r1   ->
  let (op, args) := make_mulfimm n r2 r1 r2 in
  opt_lessdef (Some (Val.mulf e#r1 e#r2)) (eval_operation ge (Eval(Vptr sp Int.zero)) op e##args).
Proof.
intros; unfold make_mulfimm. 
  destruct (Float.eq_dec n (Float.of_int (Int.repr 2))); intros. 
  simpl. constructor. rew_cst H. subst n.
  lessdef_dest (e#r2); simpl; auto. rewrite Float.mul2_add; auto. 
  rewrite Float.mul_commut; auto. 
  simpl. repeat constructor.
Qed.

Lemma make_mulfsimm_correct:
  forall n r1 r2,
    is_constant (Vsingle n) e#r2   ->
  let (op, args) := make_mulfsimm n r1 r1 r2 in
  opt_lessdef (Some (Val.mulfs e#r1 e#r2))
              (eval_operation ge (Eval(Vptr sp Int.zero)) op e##args).
Proof.
intros; unfold make_mulfsimm. 
  destruct (Float32.eq_dec n (Float32.of_int (Int.repr 2))); intros. 
  simpl. constructor. rew_cst H. subst n.
  lessdef_dest (e#r1); simpl; auto. rewrite Float32.mul2_add; auto.
  repeat constructor.
Qed.


Lemma make_mulfsimm_correct_2:
  forall n r1 r2,
  is_constant (Vsingle n) e#r1   ->
  let (op, args) := make_mulfsimm n r2 r1 r2 in
  opt_lessdef  (Some (Val.mulfs e#r1 e#r2)) (eval_operation ge (Eval (Vptr sp Int.zero)) op e##args).
Proof.
intros; unfold make_mulfsimm. 
  destruct (Float32.eq_dec n (Float32.of_int (Int.repr 2))); intros. 
  simpl. constructor. rew_cst H. subst n.
  lessdef_dest (e#r2); simpl; auto. rewrite Float32.mul2_add; auto. 
  rewrite Float32.mul_commut; auto. 
  simpl. repeat constructor.
Qed.


Lemma make_cast8signed_correct:
  forall r x,
  evmatch bc e#r x ->
  let (op, args) := make_cast8signed r x in
  opt_lessdef (Some (Val.sign_ext 8 e#r)) (eval_operation ge (Eval(Vptr sp Int.zero)) op e##args).
Proof.
  intros; unfold make_cast8signed. destruct (vincl x (Sgn Ptop 8)) eqn:INCL. 
  assert (V: evmatch bc e#r (Sgn Ptop 8)).
  { eapply evmatch_ge; eauto. apply evincl_ge; auto. }
  inv V; simpl; auto. constructor.
  repeat intro.
  simpl. destruct (H4 alloc em) as [v [LD UNS]].
  inv LD.
  rewrite is_sgn_sign_ext in UNS by auto. rewrite H3; auto.
  simpl. rewrite UNS ; auto.
  repeat constructor.
  repeat constructor.
Qed.

Lemma make_cast8unsigned_correct:
  forall r x,
  evmatch bc e#r x ->
  let (op, args) := make_cast8unsigned r x in
  opt_lessdef (Some (Val.zero_ext 8 e#r)) (eval_operation ge (Eval(Vptr sp Int.zero)) op e##args).
Proof.
  intros; unfold make_cast8unsigned. destruct (vincl x (Uns Ptop 8)) eqn:INCL.
  {
    assert (V: evmatch bc e#r (Uns Ptop 8)).
    { eapply evmatch_ge; eauto. apply evincl_ge; auto. }
    inv V; simpl; auto. constructor.
    repeat intro.
    simpl. destruct (H4 alloc em) as [v [LD UNS]].
    inv LD.
    rewrite is_uns_zero_ext in UNS by auto.
    rewrite H3. simpl. rewrite UNS. constructor.
    simpl. constructor.
  }
  simpl. repeat constructor.
Qed.

Lemma make_cast16signed_correct:
  forall r x,
  evmatch bc e#r x ->
  let (op, args) := make_cast16signed r x in
  opt_lessdef (Some (Val.sign_ext 16 e#r))  (eval_operation ge (Eval(Vptr sp Int.zero)) op e##args).
Proof.
  intros; unfold make_cast16signed. destruct (vincl x (Sgn Ptop 16)) eqn:INCL.
  {
    assert (V: evmatch bc e#r (Sgn Ptop 16)).
    { eapply evmatch_ge; eauto. apply evincl_ge; auto. }
    inv V; simpl; auto. constructor.
    repeat intro.
    simpl. destruct (H4 alloc em) as [v [LD UNS]].
    inv LD.
    rewrite is_sgn_sign_ext in UNS by auto.
    rewrite H3. simpl. rewrite UNS. constructor.
    simpl. constructor.
  }
  simpl. repeat constructor.
Qed.


Lemma make_cast16unsigned_correct:
  forall r x,
  evmatch bc e#r x ->
  let (op, args) := make_cast16unsigned r x in
  opt_lessdef (Some (Val.zero_ext 16 e#r)) (eval_operation ge (Eval(Vptr sp Int.zero)) op e##args).
Proof.
  intros; unfold make_cast16unsigned. destruct (vincl x (Uns Ptop 16)) eqn:INCL. 
  assert (V: evmatch bc e#r (Uns Ptop 16)).
  { eapply evmatch_ge; eauto. apply evincl_ge; auto. }
  inv V; simpl; auto. constructor.
  repeat intro.
  simpl. destruct (H4 alloc em) as [v [LD UNS]].
  inv LD.
  rewrite is_uns_zero_ext in UNS by auto.
  rewrite H3 ; simpl. rewrite UNS; auto.
  constructor.
  repeat constructor.
Qed.

Lemma val_sub_add_opp :
  forall x y n,
    is_constant (Vint n) y -> 
    same_eval (Val.sub x y) (Val.add x (Val.neg y)).

Proof.
  intros.
  repeat intro ; simpl.
  rew_cst H.
  destruct (ExprEval.eSexpr alloc em x) ; simpl; try constructor.
  rewrite Int.sub_add_opp. constructor.
  rewrite Int.sub_add_opp. constructor.
Qed.

Lemma xor_commut :
  forall x y, same_eval (Val.xor x y) (Val.xor y x).
Proof.
  repeat intro.
  simpl.
  apply Val.xor_commut.
Qed.
     


Lemma same_eval_opt_lessdef : forall x y z,
    same_eval x y ->
    (opt_lessdef (Some x) z <-> opt_lessdef (Some y) z).
Proof.
  split ; intros.
  inv H0. constructor. rewrite H in H2. auto.
  inv H0. constructor. rewrite <- H in H2 ; auto.
Qed.

Lemma move_let :
  forall    v (F:operation * list reg) ,
  (let (op', args') := F in
   opt_lessdef  (Some v) (eval_operation ge (Eval(Vptr sp Int.zero)) op' e##args')) <->
  opt_lessdef  (Some v) (let (op', args') := F in
                         eval_operation ge (Eval(Vptr sp Int.zero)) op' e##args').
Proof.
  intros.
  destruct F.
  tauto.
Qed.

Lemma op_strength_reduction_correct_opt:
  forall op args vl v,
  vl = map (fun r => AE.get r ae) args ->
  eval_operation ge (Eval(Vptr sp Int.zero)) op e##args = Some v ->
  let (op', args') := op_strength_reduction op args vl in
  opt_lessdef  (Some v) (eval_operation ge (Eval(Vptr sp Int.zero)) op' e##args').
Proof.
intros until v; unfold op_strength_reduction;
  case (op_strength_reduction_match op args vl); simpl; intros.
 - (* cast8signed *)
   InvApproxRegs; SimplVM; inv H0. apply make_cast8signed_correct; auto.
- (* cast8unsigned *)
  InvApproxRegs; SimplVM; inv H0. apply make_cast8unsigned_correct; auto.
- (* cast16signed *)
  InvApproxRegs; SimplVM; inv H0. apply make_cast16signed_correct; auto.
- (* cast16unsigned *)
  InvApproxRegs; SimplVM; inv H0. apply make_cast16unsigned_correct; auto.
- (* sub *)
  InvApproxRegs; SimplVM; inv H0.
  rewrite move_let.
  rewrite same_eval_opt_lessdef by (eapply val_sub_add_opp ; eauto).
  rewrite <- move_let.
  eapply make_addimm_correct ; eauto.
  repeat intro. simpl. rew_cst H2 ; reflexivity.
- (* mul *)
  InvApproxRegs; SimplVM; inv H0.
  rewrite move_let.
  rewrite same_eval_opt_lessdef by (eapply val_mul_commut ; eauto).
  rewrite <- move_let.
  eapply make_mulimm_correct ; eauto.
- 
  InvApproxRegs; SimplVM; inv H0.
  eapply make_mulimm_correct ; eauto.
-   (* divs *)
  InvApproxRegs. subst.
  apply make_divimm_correct; auto.  inv H1 ; auto.
- (* divu *)
  InvApproxRegs. subst.
  apply make_divuimm_correct; auto. inv H1 ; auto.
- (* modu *) 
  InvApproxRegs. subst.
  apply make_moduimm_correct; auto. inv H1 ; auto.
- (* and *)
  InvApproxRegs. subst v.
  rewrite move_let.
  rewrite same_eval_opt_lessdef by (eapply val_and_commut ; eauto).
  rewrite <- move_let.
  apply make_andimm_correct; eauto. inv H ; auto.
-   InvApproxRegs. subst v. inv H1.
    apply make_andimm_correct; eauto.
-  InvApproxRegs. inv H0.
   apply make_andimm_correct; eauto. repeat intro ; auto.
-  (* or *)
  InvApproxRegs. subst v. inv H.
  rewrite move_let.
  rewrite same_eval_opt_lessdef by (eapply val_or_commut ; eauto).
  rewrite <- move_let.
  apply make_orimm_correct; eauto.
- InvApproxRegs. subst. inv H1.
  apply make_orimm_correct; eauto.
- (* xor *)
  InvApproxRegs. subst v. inv H.
  rewrite move_let.
  rewrite same_eval_opt_lessdef by (eapply xor_commut ; eauto).
  rewrite <- move_let.
  apply make_xorimm_correct; eauto.
- InvApproxRegs. subst. inv H1.
  apply make_xorimm_correct; eauto.
- (* shl *)
  InvApproxRegs; SimplVM; inv H0.
  apply make_shlimm_correct; auto.
- (* shr *)
  InvApproxRegs; SimplVM; inv H0. apply make_shrimm_correct; auto.
- (* shru *)
  InvApproxRegs; SimplVM; inv H0. apply make_shruimm_correct; auto.
- (* lea *)
  exploit addr_strength_reduction_correct; eauto. 
  destruct (addr_strength_reduction addr args0 vl0) as [addr' args'].
  intro. destruct H1. destruct H1. simpl. rewrite H1. constructor ; auto.
- (* cond *)
  inv H0. apply make_cmp_correct; auto.
- (* mulf *)
  InvApproxRegs; SimplVM; inv H0. apply make_mulfimm_correct; auto.
  inv H1 ; auto.
-  InvApproxRegs; SimplVM; inv H0. apply make_mulfimm_correct_2; auto.
   inv H ; auto.
- (* mulfs *)
  InvApproxRegs; SimplVM; inv H0. apply make_mulfsimm_correct; auto. inv H1 ; auto.
-   InvApproxRegs; SimplVM; inv H0. apply make_mulfsimm_correct_2; auto. inv H ; auto.
- (* default *)
  rewrite H0.
  repeat constructor.
Qed.

Lemma op_strength_reduction_correct:
  forall op args vl v,
  vl = map (fun r => AE.get r ae) args ->
  eval_operation ge (Eval(Vptr sp Int.zero)) op e##args = Some v ->
  let (op', args') := op_strength_reduction op args vl in
  exists w, eval_operation ge (Eval(Vptr sp Int.zero)) op' e##args' = Some w /\ Val.lessdef v w.
Proof.
  intros.
  exploit op_strength_reduction_correct_opt ; eauto.
  intros.
  destruct (op_strength_reduction op args vl).
  inv H1.
  exists e'; intuition.
Qed.

  


End STRENGTH_REDUCTION.
