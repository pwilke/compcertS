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
Require Import Compopts.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Op.
Require Import Values_symbolic.
Require Import Values_symbolictype.
Require Import ValueDomain.
Require Import RTL.
Section S.

(** Value analysis for IA32 operators *)

Definition eval_static_condition (cond: condition) (vl: list aval): abool :=
  match cond, vl with
  | Ccomp c, v1 :: v2 :: nil => cmp_bool c v1 v2
  | Ccompu c, v1 :: v2 :: nil => cmpu_bool  c v1 v2
  | Ccompimm c n, v1 :: nil => cmp_bool c v1 (I n)
  | Ccompuimm c n, v1 :: nil => cmpu_bool  c v1 (I n)
  | Ccompf c, v1 :: v2 :: nil => cmpf_bool c v1 v2
  | Cnotcompf c, v1 :: v2 :: nil => cnot (cmpf_bool c v1 v2)
  | Ccompfs c, v1 :: v2 :: nil => cmpfs_bool c v1 v2
  | Cnotcompfs c, v1 :: v2 :: nil => cnot (cmpfs_bool c v1 v2)
  | Cmaskzero n, v1 :: nil => maskzero v1 n
  | Cmasknotzero n, v1 :: nil => cnot (maskzero v1 n)
  | _, _ => Bnone
  end.

Definition eval_static_addressing (addr: addressing) (vl: list aval): aval :=
  match addr, vl with
  | Aindexed n, v1::nil => add v1 (I n)
  | Aindexed2 n, v1::v2::nil => add (add v1 v2) (I n)
  | Ascaled sc ofs, v1::nil => add (mul v1 (I sc)) (I ofs)
  | Aindexed2scaled sc ofs, v1::v2::nil => add v1 (add (mul v2 (I sc)) (I ofs))
  | Aglobal s ofs, nil => Ptr (Gl s ofs)
  | Abased s ofs, v1::nil => add (Ptr (Gl s ofs)) v1
  | Abasedscaled sc s ofs, v1::nil => add (Ptr (Gl s ofs)) (mul v1 (I sc))
  | Ainstack ofs, nil => Ptr(Stk ofs)
  | _, _ => Vbot
  end.

Definition provenance_list (l : list aval) : aptr :=
    List.fold_left (fun acc av => eplub acc (provenance av)) l Pbot.

Definition eval_static_operation (op: operation) (vl: list aval): aval :=
  match op, vl with
  | Omove, v1::nil => v1
  | Ointconst n, nil => I n
  | Ofloatconst n, nil => if propagate_float_constants tt then F n else ntop
  | Osingleconst n, nil => if propagate_float_constants tt then FS n else ntop
  | Oindirectsymbol id, nil => Ptr (Gl id Int.zero)
  | Ocast8signed, v1 :: nil => sign_ext 8 v1
  | Ocast8unsigned, v1 :: nil => zero_ext 8 v1
  | Ocast16signed, v1 :: nil => sign_ext 16 v1
  | Ocast16unsigned, v1 :: nil => zero_ext 16 v1
  | Oneg, v1::nil => neg v1
  | Osub, v1::v2::nil => sub v1 v2
  | Omul, v1::v2::nil => mul v1 v2
  | Omulimm n, v1::nil => mul v1 (I n)
  | Omulhs, v1::v2::nil => mulhs v1 v2
  | Omulhu, v1::v2::nil => mulhu v1 v2
  | Odiv, v1::v2::nil => divs v1 v2
  | Odivu, v1::v2::nil => divu v1 v2
  | Omod, v1::v2::nil => mods v1 v2
  | Omodu, v1::v2::nil => modu v1 v2
  | Oand, v1::v2::nil => and v1 v2
  | Oandimm n, v1::nil => and v1 (I n)
  | Oor, v1::v2::nil => or v1 v2
  | Oorimm n, v1::nil => or v1 (I n)
  | Oxor, v1::v2::nil => xor v1 v2
  | Oxorimm n, v1::nil => xor v1 (I n)
  | Onot, v1::nil => notint v1
  | Oshl, v1::v2::nil => shl v1 v2
  | Oshlimm n, v1::nil => shl v1 (I n)
  | Oshr, v1::v2::nil => shr v1 v2
  | Oshrimm n, v1::nil => shr v1 (I n)
  | Oshrximm n, v1::nil => shrx v1 (I n)
  | Oshru, v1::v2::nil => shru v1 v2
  | Oshruimm n, v1::nil => shru v1 (I n)
  | Ororimm n, v1::nil => ror v1 (I n)
  | Oshldimm n, v1::v2::nil => or (shl v1 (I n)) (shru v2 (I (Int.sub Int.iwordsize n)))
  | Olea addr, _ => eval_static_addressing addr vl
  | Onegf, v1::nil => negf v1
  | Oabsf, v1::nil => absf v1
  | Oaddf, v1::v2::nil => addf v1 v2
  | Osubf, v1::v2::nil => subf v1 v2
  | Omulf, v1::v2::nil => mulf v1 v2
  | Odivf, v1::v2::nil => divf v1 v2
  | Onegfs, v1::nil => negfs v1
  | Oabsfs, v1::nil => absfs v1
  | Oaddfs, v1::v2::nil => addfs v1 v2
  | Osubfs, v1::v2::nil => subfs v1 v2
  | Omulfs, v1::v2::nil => mulfs v1 v2
  | Odivfs, v1::v2::nil => divfs v1 v2
  | Osingleoffloat, v1::nil => singleoffloat v1
  | Ofloatofsingle, v1::nil => floatofsingle v1
  | Ointoffloat, v1::nil => intoffloat v1
  | Ofloatofint, v1::nil => floatofint v1
  | Ointofsingle, v1::nil => intofsingle v1
  | Osingleofint, v1::nil => singleofint v1
  | Omakelong, v1::v2::nil => longofwords v1 v2
  | Olowlong, v1::nil => loword v1
  | Ohighlong, v1::nil => hiword v1
  | Ocmp c, _ => of_optbool (provenance_list vl) (eval_static_condition c vl)
  |   _   , _ => Vbot
  end.


Ltac InvHyps :=
  match goal with
  | [H: None = Some _ |- _ ] => discriminate
  | [H: Some _ = Some _ |- _] => inv H
  | [H1: match ?vl with nil => _ | _ :: _ => _ end = Some _ ,
     H2: list_forall2 _ ?vl _ |- _ ] => inv H2; InvHyps
  | _ => idtac
  end.


Hint Resolve add_sound mul_sound : va.

Lemma evmatch_cst : forall bc i,
    evmatch bc (Eval (Vint i)) (I i).
Proof.
  repeat constructor ; reflexivity.
Qed.

Hint Resolve evmatch_cst : va.


Section SOUNDNESS.

Variable bc: block_classification.
Variable ge: genv.
Hypothesis GENV: genv_match bc ge.
Variable sp: block.
Hypothesis STACK: bc sp = BCstack.



Definition opt_cmatch (e: option expr_sym) (v : abool) : Prop :=
  match e with
  | None => True
  | Some e => ecmatch  e v
  end.

Theorem eval_static_condition_sound:
  forall cond vargs aargs,
  list_forall2 (evmatch bc ) vargs aargs ->
  opt_cmatch  (eval_condition cond vargs) (eval_static_condition cond aargs).
Proof.
  intros until aargs; intros VM.
  inv VM.
  -
  destruct cond; simpl ; auto with va.
  -
  inv H0.
  destruct cond; simpl ; eauto with va.
  + eapply ecnot_sound ; eauto. eauto with va.
  + inv H2; destruct cond; simpl; eauto with va.
    eapply ecnot_sound ; eauto. eauto with va.
    eapply ecnot_sound ; eauto. eauto with va.
Qed.

Lemma symbol_address_sound:
  forall id ofs b,
    Genv.symbol_address ge id ofs = Vptr b ofs -> 
    evmatch bc  (Eval (Vptr b ofs)) (Ptr (Gl id ofs)).
Proof.
  intros. eapply symbol_address_sound; eauto.
  repeat intro ; reflexivity.
Qed.

(*
Lemma symbol_address_sound_2:
  forall id ofs,
  vmatch bc (Genv.symbol_address ge id ofs) (Ifptr (Gl id ofs)).
Proof.
  intros. unfold Genv.symbol_address. destruct (Genv.find_symbol ge id) as [b|] eqn:F. 
  constructor. constructor. apply GENV; auto.
  constructor.
Qed.
*)
Hint Resolve symbol_address_sound (*symbol_address_sound_2*): va.

Lemma ntop2_commut : forall x y,
    ntop2 x y  = ntop2 y x.
Proof.
  unfold ntop2. intros. rewrite eplub_comm.
  reflexivity.
Qed.


Lemma add_commut : forall x y, add x y = add y x.
Proof.
  destruct x ; destruct y ; simpl; try reflexivity;
  try rewrite ntop2_commut ; auto.
  rewrite Int.add_commut. reflexivity.
Qed.

Theorem eval_static_addressing_sound:
  forall addr vargs vres aargs  e
         (STKPTR : epmatch bc  e (Stk Int.zero)),
    eval_addressing ge e addr vargs = Some vres ->
  list_forall2 (evmatch bc) vargs aargs ->
  evmatch bc  vres (eval_static_addressing addr aargs).
Proof.
  unfold eval_addressing, eval_static_addressing; intros;
  destruct addr; InvHyps ;try (eauto with va ; fail).
  -
    exploit Genv.symbol_address'_ptr ; eauto.
    intros (B & EQ) ; intuition subst.
    rewrite <- Genv.symbol_address'_same in H.
    eapply symbol_address_sound ; eauto.
  - 
    exploit Op.option_map_symbol_address'_some ; eauto.
    intros (B & SYMB & EQ) ; intuition subst.
    rewrite <- Genv.symbol_address'_same in SYMB.
    rewrite add_commut. eauto with va.
  -
    exploit Op.option_map_symbol_address'_some ; eauto.
    intros (B & SYMB & EQ) ; intuition subst.
    rewrite <- Genv.symbol_address'_same in SYMB.
    rewrite add_commut. eauto with va.
  - 
    constructor. inv STKPTR.
    econstructor; eauto.
    repeat intro. unfold Val.add. simpl. rewrite <- H2 ; eauto.
    simpl. rewrite (Int.add_commut (cm b) Int.zero).
    rewrite Int.add_zero_l; auto with va. 
Qed.

Theorem eval_static_operation_sound:
  forall op vargs  vres aargs e
         (STKPTR : epmatch bc e (Stk Int.zero))
  ,
    eval_operation ge e op vargs = Some vres ->
  list_forall2 (evmatch bc) vargs aargs ->
  evmatch bc  vres (eval_static_operation op aargs).
Proof.
  unfold eval_operation, eval_static_operation; intros;
  destruct op; InvHyps; eauto with va. 
  destruct (propagate_float_constants tt); repeat constructor.
  destruct (propagate_float_constants tt); repeat constructor.
  - 
  exploit Genv.symbol_address'_ptr ; eauto.
  intros (B  & EQ) ; intuition subst.
  rewrite <- Genv.symbol_address'_same in H.
  eapply symbol_address_sound ; eauto.
  -
    eapply eval_static_addressing_sound; eauto.
  - 
    generalize (eval_static_condition_sound   c vargs _ H0).
    rewrite H.
    apply of_optbool_sound.
    + 
    assert (evmatch bc  vres (Ptr (provenance_list aargs))).
    unfold provenance_list.
    destruct c ; simpl in H; InvHyps;
    try (apply evmatch_ntop2; repeat constructor ; auto).
    apply evmatch_ntop1 with (T :=  fun a1 => (Val.cmp_bool c a1 (Eval (Vint i)))) ; repeat constructor ; auto.
    apply evmatch_ntop1 with (T :=  fun a1 => (Val.cmpu_bool c a1 (Eval (Vint i)))) ; repeat constructor ; auto.
    apply evmatch_ntop2 with (T:= fun a1 a0 => (Eunop OpNotbool Tint (Val.cmpf_bool c a1 a0))) ;
      repeat constructor; auto.
    apply evmatch_ntop2 with (T:= fun a1 a0 => (Eunop OpNotbool Tint (Val.cmpfs_bool c a1 a0))) ;
      repeat constructor; auto.
    apply evmatch_ntop1 with (T :=  fun a1 => (Val.maskzero_bool a1 i)) ; repeat constructor ; auto.
    apply evmatch_ntop1 with (T :=  fun a1 => ((Eunop OpNotbool Tint (Val.maskzero_bool a1 i)))) ; repeat constructor ; auto.
    inv H1 ; auto.
Qed.


End SOUNDNESS.

End S.