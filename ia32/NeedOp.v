Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import ExprEval Values_symbolictype Values_symbolic Memory.
Require Import Globalenvs.
Require Import Op.
Require Import NeedDomain.
Require Import RTL.

(** Neededness analysis for IA32 operators *)

Definition op1 (nv: nval) := nv :: nil.
Definition op2 (nv: nval) := nv :: nv :: nil.

Definition needs_of_condition (cond: condition): list nval :=
  match cond with
  | Cmaskzero n | Cmasknotzero n => op1 (maskzero n)
  | _ => nil
  end.

Definition needs_of_addressing (addr: addressing) (nv: nval): list nval :=
  match addr with
  | Aindexed n => op1 (modarith nv)
  | Aindexed2 n => op2 (modarith nv)
  | Ascaled sc ofs => op1 (modarith (modarith nv))
  | Aindexed2scaled sc ofs => op2 (modarith nv)
  | Aglobal s ofs => nil
  | Abased s ofs => op1 (modarith nv)
  | Abasedscaled sc s ofs => op1 (modarith (modarith nv))
  | Ainstack ofs => nil
  end.

Definition needs_of_operation (op: operation) (nv: nval): list nval :=
  match op with
  | Omove => op1 nv
  | Ointconst n => nil
  | Ofloatconst n => nil
  | Osingleconst n => nil
  | Oindirectsymbol id => nil
  | Ocast8signed => op1 (sign_ext 8 nv)
  | Ocast8unsigned => op1 (zero_ext 8 nv)
  | Ocast16signed => op1 (sign_ext 16 nv)
  | Ocast16unsigned => op1 (zero_ext 16 nv)
  | Oneg => op1 (modarith nv)
  | Osub => op2 (default nv)
  | Omul => op2 (modarith nv)
  | Omulimm n => op1 (modarith nv)
  | Omulhs | Omulhu | Odiv | Odivu | Omod | Omodu => op2 (default nv)
  | Oand => op2 (bitwise nv)
  | Oandimm n => op1 (andimm nv n)
  | Oor => op2 (bitwise nv)
  | Oorimm n => op1 (orimm nv n)
  | Oxor => op2 (bitwise nv)
  | Oxorimm n => op1 (bitwise nv)
  | Onot => op1 (bitwise nv)
  | Oshl => op2 (default nv)
  | Oshlimm n => op1 (shlimm nv n)
  | Oshr => op2 (default nv)
  | Oshrimm n => op1 (shrimm nv n)
  | Oshrximm n => op1 (default nv)
  | Oshru => op2 (default nv)
  | Oshruimm n => op1 (shruimm nv n)
  | Ororimm n => op1 (ror nv n)
  | Oshldimm n => op1 (default nv)
  | Olea addr => needs_of_addressing addr nv
  | Onegf | Oabsf => op1 (default nv)
  | Oaddf | Osubf | Omulf | Odivf => op2 (default nv)
  | Onegfs | Oabsfs => op1 (default nv)
  | Oaddfs | Osubfs | Omulfs | Odivfs => op2 (default nv)
  | Osingleoffloat | Ofloatofsingle => op1 (default nv)
  | Ointoffloat | Ofloatofint | Ointofsingle | Osingleofint => op1 (default nv)
  | Omakelong => op2 (default nv)
  | Olowlong | Ohighlong => op1 (default nv)
  | Ocmp c => needs_of_condition c
  end.

Definition operation_is_redundant (op: operation) (nv: nval): bool :=
  match op with
  | Ocast8signed => sign_ext_redundant 8 nv
  | Ocast8unsigned => zero_ext_redundant 8 nv
  | Ocast16signed => sign_ext_redundant 16 nv
  | Ocast16unsigned => zero_ext_redundant 16 nv
  | Oandimm n => andimm_redundant nv n
  | Oorimm n => orimm_redundant nv n
  | _ => false
  end.

Ltac InvAgree :=
  match goal with
  | [H: vagree_list nil _ _ |- _ ] => inv H; InvAgree
  | [H: vagree_list (_::_) _ _ |- _ ] => inv H; InvAgree
  | _ => idtac
  end.

Ltac TrivialExists :=
  match goal with
  | [ |- exists v, Some ?x = Some v /\ _ ] => exists x; split; auto
  | _ => idtac
  end.

Section SOUNDNESS.

Variable ge: genv.
Variable sp: block.
Variables m m': mem.
Hypothesis PERM: forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p.

Lemma needs_of_condition_sound:
  forall cond args b args',
  eval_condition cond args = Some b ->
  vagree_list args args' (needs_of_condition cond) ->
  exists b',
    eval_condition cond args' = Some b' /\
    Val.lessdef b b'.
Proof.
  intros. destruct cond; simpl in H;
  try (eapply default_needs_of_condition_sound; eauto; fail);
  simpl in *; FuncInv; InvAgree.
- eexists; split; eauto. eapply maskzero_sound; eauto. 
- eexists; split; eauto.
  simpl in H5.
  ldt.
Qed.

Lemma needs_of_addressing_sound:
  forall (ge: genv) sp addr args v nv args',
  eval_addressing ge (Eval (Vptr sp Int.zero)) addr args = Some v ->
  vagree_list args args' (needs_of_addressing addr nv) ->
  exists v',
     eval_addressing ge (Eval (Vptr sp Int.zero)) addr args' = Some v'
  /\ vagree v v' nv.
Proof.
  unfold needs_of_addressing; intros.
  destruct addr; simpl in *; FuncInv; InvAgree; TrivialExists;
  auto using add_sound, mul_sound with na.
  apply add_sound; auto with na. apply add_sound; rewrite modarith_idem; auto. 
  apply add_sound; auto. apply add_sound; rewrite modarith_idem; auto with na. 
  apply mul_sound; rewrite modarith_idem; auto with na.
  rewrite H; eexists; split; eauto. apply vagree_same.
  unfold option_map in *. destr_in H. eexists; split; eauto. inv H.
  apply add_sound; auto with na.
  unfold option_map in *. destr_in H. eexists; split; eauto. inv H.
  apply add_sound; auto with na.
  apply mul_sound; rewrite modarith_idem; auto with na.
  rewrite modarith_idem in H5; auto.
Qed.

Lemma needs_of_operation_sound:
  forall op args v nv args',
  eval_operation ge (Eval (Vptr sp Int.zero)) op args = Some v ->
  vagree_list args args' (needs_of_operation op nv) ->
  nv <> Nothing ->
  exists v',
     eval_operation ge (Eval (Vptr sp Int.zero)) op args' = Some v'
  /\ vagree v v' nv.
Proof.
  unfold needs_of_operation; intros; destruct op; try (eapply default_needs_of_operation_sound; eauto; fail);
  simpl in *; FuncInv; InvAgree; TrivialExists.
- apply sign_ext_sound; auto. compute; auto. 
- apply zero_ext_sound; auto. omega.
- apply sign_ext_sound; auto. compute; auto. 
- apply zero_ext_sound; auto. omega.
- apply neg_sound; auto.
- apply mul_sound; auto.
- apply mul_sound; auto with na.
- apply and_sound; auto.
- apply andimm_sound; auto.
- apply or_sound; auto.
- apply orimm_sound; auto.
- apply xor_sound; auto.
- apply xor_sound; auto with na.
- apply notint_sound; auto.
- apply shlimm_sound; auto.
- apply shrimm_sound; auto.
- apply shruimm_sound; auto. 
- apply ror_sound; auto. 
- eapply needs_of_addressing_sound; eauto.
- destruct (eval_condition c args) as [b|] eqn:EC; simpl in H0. 
  destruct (needs_of_condition_sound _ _ _ _ EC H0) as [v' [EC' VA]].
  rewrite EC'. eexists; split; eauto. inv H.
  eapply vagree_lessdef; eauto. inv H.
Qed.

Lemma operation_is_redundant_sound:
  forall op nv arg1 args v arg1' args',
  operation_is_redundant op nv = true ->
  eval_operation ge (Eval (Vptr sp Int.zero)) op (arg1 :: args) = Some v ->
  vagree_list (arg1 :: args) (arg1' :: args') (needs_of_operation op nv) ->
  vagree v arg1' nv.
Proof.
  intros. destruct op; simpl in *; try discriminate; inv H1; FuncInv; subst.
- apply sign_ext_redundant_sound; auto. omega.
- apply zero_ext_redundant_sound; auto. omega.
- apply sign_ext_redundant_sound; auto. omega.
- apply zero_ext_redundant_sound; auto. omega.
- apply andimm_redundant_sound; auto. 
- apply orimm_redundant_sound; auto.
Qed.

End SOUNDNESS.


