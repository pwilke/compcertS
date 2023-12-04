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

(** Correctness proof for IA32 generation: auxiliary results. *)

Require Import Coqlib.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import NormaliseSpec.
Require Import ExprEval.
Require Import Memory.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Asm.
Require Import Asmgen.
Require Import Asmgenproof0.
Require Import Conventions.

Require Import Values_symbolictype.
Require Import Values_symbolic.
Require Import MemRel.

Hint Resolve wf_mr_ld wf_mr_norm_ld.

Open Local Scope error_monad_scope.

(** * Correspondence between Mach registers and IA32 registers *)

Lemma agree_nextinstr_nf:
  forall ms sp rs,
  agree ms sp rs -> agree ms sp (nextinstr_nf rs).
Proof.
  intros. unfold nextinstr_nf. apply agree_nextinstr. 
  apply agree_undef_nondata_regs. auto.
  intro. simpl. des r. 
Qed.

(** Useful properties of the PC register. *)

(** Useful simplification tactic *)

Ltac repSplit' T :=
  repeat match goal with
           | |- _ /\ _ => split; T
         end.

Ltac repSplit := repSplit' idtac.

Lemma reg_ptr_undef_regs:
  forall lr rs r b o,
    reg_ptr rs r b o ->
    ~ In r lr ->
    reg_ptr (undef_regs lr rs) r b o.
Proof.
  induction lr; simpl; intros; destr.
  apply IHlr; auto.
  Simplifs.
Qed.

Lemma ptru_undef_regs:
  forall lr rs r,
    ptr_or_zero rs r ->
    ~ In r lr ->
    ptr_or_zero (undef_regs lr rs) r.
Proof.
  induction lr; simpl; intros; destr.
  apply IHlr; auto.
  Simplifs.
Qed.

Lemma nextinstr_nf_pc :
  forall rs b o,
    reg_ptr rs PC b o ->
    reg_ptr (nextinstr_nf rs) PC b (incr o).
Proof.
  unfold nextinstr_nf.
  intros.
  apply nextinstr_pc.
  eapply reg_ptr_undef_regs; auto.
  destr.
Qed.


Lemma nextinstr_nf_pcu :
  forall rs,
    ptr_or_zero rs PC ->
    ptr_or_zero (nextinstr_nf rs) PC.
Proof.
  unfold nextinstr_nf.
  intros.
  apply nextinstr_pcu.
  eapply ptru_undef_regs; auto.
  destr.
Qed.


(* Ltac norm_ni' Npc Rng := *)
(*   repeat  *)
(*     match goal with *)
(*       | |- context [Mem.mem_norm ?m (nextinstr_nf ?rs PC) Ptr] => *)
(*         rewrite (Mem.same_eval_eqm m Ptr _ _ (nextinstr_nf_pc _)) *)
(*       | |- context [Mem.mem_norm ?m (nextinstr ?rs PC) Ptr] => *)
(*         rewrite (Mem.same_eval_eqm m Ptr _ _ *)
(*                                    (nextinstr_pc _)) *)
(*       | |- Mem.mem_norm ?m ?e ?r = ?v => *)
(*         apply Mem.eq_norm; [ *)
(*             let al := fresh "al" in *)
(*             let em := fresh "em" in *)
(*             let COMP := fresh "COMP" in *)
(*             intros al em COMP ;  *)
(*               generalize (Mem.norm_ld _ _ _ _ Npc al em COMP); *)
(*               simpl; *)
(*               let A := fresh "A" in *)
(*               intro A; inv A; simpl; sint; auto *)
(*            |simpl; try apply Rng; auto; try omega|seval; try congruence] *)
(*     end. *)

(* Ltac norm_ni Rng := *)
(*   repeat match goal with *)
(*            | H: Mem.mem_norm ?m ?e ?r = _, *)
(*                 H1: context[Mem.mem_norm ?m ?e ?r] |- _ => rewrite H in H1 *)
(*            | H: Mem.mem_norm ?m ?e ?r = _ *)
(*              |- context [Mem.mem_norm ?m ?e ?r] => rewrite H; simpl; sint *)
(*            | H: Mem.mem_norm ?m ?e ?r = _ *)
(*              |- Mem.mem_norm ?m _ ?r = _ => *)
(*              norm_ni' H Rng; Simplifs *)
(*            | H: _ = eSexpr ?al ?em ?e |- *)
(*              context [eSexpr ?al ?em ?e] => rewrite <- H; simpl; sint; auto *)
(*            | |- _ <= _ <= _ => vm_compute; intuition congruence *)
(*            | |- context[Mem.mem_norm ?m (Val.add ?e (Eval Vone)) ?r] => *)
(*              replace (Mem.mem_norm m (Val.add e (Eval Vone)) r) with *)
(*              (Values.Val.add (Mem.mem_norm m e r) Vone); [|symmetry] *)
(*            | H: Mem.mem_norm ?m (_#PC) Ptr = _ *)
(*              |- context[Mem.mem_norm ?m (nextinstr _ PC) ?r] => *)
(*              norm_ni' H Rng; Simplifs; auto *)
(*            | |- in_bound _ _ => apply Rng; vm_compute; intuition congruence *)
(*            | |- Vptr _ _ <> Vundef => congruence *)
(*            | |- Val.lessdef ?v ?v => auto *)
(*          end. *)


(** * Correctness of IA32 constructor functions *)


Ltac pc_trans :=
  repeat match goal with
           | H1: reg_ptr ?rs PC ?b ?o, H2: incr_pc ?rs ?rs2 |- _ =>
             match goal with
                 H: reg_ptr rs2 PC _ _ |- _ => fail 1
               | |- _ => let i := fresh "RP" in
                         generalize (incr_pc_reg_ptr rs rs2 _ _ H2 H1); intro i
             end
         end.


Ltac srp :=
      repeat
      match goal with
        | H:reg_ptr ?rs1 PC ?b ?o
          |- incr_pc _ _ =>
          red; intros; exists b; eexists; split;
          [ 
          | apply nextinstr_pc; unfold reg_ptr; Simplifs ]
        | |- _ => apply nextinstr_pc; Simplifs; eauto
        | H: reg_ptr ?rs1 PC ?b ?o |- reg_ptr ?rs1 PC ?b _ => eauto
        | |- _ => pc_trans; Simplifs; auto
      end.
  (* repeat match goal with *)
  (*          | H: reg_ptr ?rs1 PC ?b ?o |- incr_pc _ _ => *)
  (*            red; intros; exists b, o; split; *)
  (*            [ exact H *)
  (*            | apply nextinstr_pc; unfold reg_ptr; Simplifs *)
  (*            ] *)
  (*          | |- _ => pc_trans *)
  (*        end. *)

Section CONSTRUCTORS.

Variable ge: genv.
Variable fn: function.

(** Smart constructor for moves. *)

Lemma incr_pc_nextinstr:
  forall rs1 (i: ireg) i0 b o,
    reg_ptr rs1 PC b o ->
    incr_pc rs1 (nextinstr rs1 # i <- i0).
Proof.
  red; intros.
  eexists;  eexists ; split; eauto.
  apply nextinstr_pc.
  red.
  Simplifs.
Qed.


Lemma incr_pc_nextinstr_f:
  forall rs1 (i: freg) i0 b o,
    reg_ptr rs1 PC b o ->
    incr_pc rs1 (nextinstr rs1 # i <- i0).
Proof.
  red; intros.
  eexists;  eexists ; split; eauto.
  apply nextinstr_pc.
  red.
  Simplifs.
Qed.

Lemma mk_mov_correct:
  forall rd rs k c rs1 m b o,
    mk_mov rd rs k = OK c ->
    reg_ptr rs1 PC b o ->
    exists rs2,
      exec_straight ge fn c rs1 m k rs2 m
      /\ rs2#rd = rs1#rs
      /\ forall r, data_preg r = true -> r <> rd -> rs2#r = rs1#r.
Proof.
  unfold mk_mov; intros.   
  destruct rd; try (monadInv H); destruct rs; monadInv H.
  - (* mov *)
    econstructor. split. eapply exec_straight_one. simpl. eauto.
    eapply incr_pc_nextinstr; eauto.
    split. Simplifs. intros; Simplifs.
  - (* movd *)
    econstructor. split. eapply exec_straight_one. simpl. eauto.
    eapply incr_pc_nextinstr_f; eauto.
    split. Simplifs. intros; Simplifs.
Qed.

(** Smart constructor for [shrx] *)


Theorem shrx_shr:
  forall x y,
    Val.lessdef
      (Val.shrx x y)
      (Val.shr
         (Val.add x
                  (Val.mul
                     (Val.cmp Clt x (Eval (Vint Int.zero)))
                     (Val.sub (Val.shl (Eval (Vint Int.one)) y) (Eval (Vint Int.one))))) y).
Proof.
  intros. red; simpl; intros.
  seval; try solve [destruct (Int.lt); simpl; auto]; auto.
  destruct (Int.ltu i0 (Int.repr 31)) eqn:?; simpl; auto.
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 31)) with 31. intros.
  assert (Int.ltu i0 Int.iwordsize = true). 
  {
    unfold Int.ltu. apply zlt_true. change (Int.unsigned Int.iwordsize) with 32. omega.
  }
  rewrite Int.shrx_shr. rewrite H0.  destruct Int.lt; simpl; auto.
  rewrite H0; simpl. rewrite Int.mul_commut. rewrite Int.mul_one. auto.
  rewrite H0; simpl. rewrite Int.mul_commut. rewrite Int.mul_zero. rewrite Int.add_zero. auto.
  auto.
Qed.


Lemma lift_vint:
  forall a: bool, 
    (if a then Vtrue else Vfalse) =
    Vint (if a then Int.one else Int.zero).
Proof.
  intros; destr.
Qed.





Lemma mk_shrximm_correct:
  forall n k c (rs1: regset) m b o,
    mk_shrximm n k = OK c ->
    reg_ptr rs1 PC b o ->
    exists rs2,
      exec_straight ge fn c rs1 m k rs2 m
      /\ Val.lessdef (Val.shrx (rs1#EAX) (Eval (Vint n))) rs2#EAX
      /\ forall r, data_preg r = true -> r <> EAX -> r <> ECX -> rs2#r = rs1#r.
Proof.
  unfold mk_shrximm; intros. inv H.
  generalize (shrx_shr (rs1 EAX) (Eval (Vint n))). intros A.
  set (tnm1 := Int.sub (Int.shl Int.one n) Int.one).
  set (x' := Val.add (rs1 EAX) (Val.add (Eval Vzero) (Eval (Vint tnm1)))).
  set (rs2 := nextinstr (compare_ints (Val.and (rs1 EAX) (rs1 EAX)) (Eval (Vint Int.zero)) rs1 m)).
  set (rs3 := nextinstr (rs2#ECX <- x')).
  set (cond := test_one (Val.xor (rs3 OF) (rs3 SF))).
  set (expr_cond := Val.add (Val.mul cond rs3#ECX)
                            (Val.mul (Val.notbool cond) rs3#EAX)).
  set (rs4 := nextinstr (rs3#EAX <- expr_cond)).
  set (rs5 := nextinstr_nf (rs4#EAX <- (Val.shr rs4#EAX (Eval (Vint n))))).
  
  assert (E: incr_pc rs1 rs2). 
  { unfold rs2, compare_ints. srp. }
  assert (B: incr_pc rs2 rs3). 
  { unfold rs3. srp. }
  assert (C: incr_pc rs3 rs4). 
  { unfold rs4. srp. }
  assert (D: incr_pc rs4 rs5).
  { unfold rs5. srp. }
  exists rs5. repSplit.
  - eapply exec_straight_step with (rs2:=rs2) (m2:=m); simpl; eauto.
    eapply exec_straight_step with (rs2:=rs3) (m2:=m); simpl; eauto.
    replace (rs2 EAX) with (rs1 EAX); auto.
    unfold rs2; Simplifs.
    eapply exec_straight_step with (rs2:=rs4) (m2:=m);simpl; eauto.
    eapply exec_straight_one; simpl; auto.
  -
    unfold rs5, rs4, expr_cond, cond, rs3, rs2, compare_ints.
    Simplifs.
    unfold x'; simpl.
    assert (forall i, Int.ltu i (Int.repr 31) = true ->
                      Int.ltu i (Int.iwordsize) = true).
    {
      clear; intros.
      exploit Int.ltu_inv; eauto.
      change (Int.unsigned (Int.repr 31)) with 31;
        unfold Int.ltu; intro; rewrite zlt_true;
        change (Int.unsigned Int.iwordsize) with 32; auto. omega.
    }
    red; intros; simpl; seval; auto.
    destr; auto. rewrite Int.and_idem.
    rewrite Int.sub_zero_l. unfold Vtrue, Vfalse.
    repeat (rewrite ! lift_vint; simpl).
    generalize (Int.lt_sub_overflow i Int.zero);
      unfold Int.negative; rewrite Int.sub_zero_l;
      intro G; rewrite G; clear G.
    rewrite Int.add_zero_l.
    rewrite Int.shrx_shr.
    des (Int.lt i Int.zero);
      repeat rewrite Int.eq_true in *;
      repeat rewrite Int.eq_false in * by discriminate; simpl; rewrite H; auto;
      rewrite (Int.mul_commut Int.zero); rewrite Int.mul_zero;
      rewrite Int.mul_commut; rewrite Int.mul_one; try rewrite (Int.add_commut Int.zero);
      rewrite Int.add_zero; auto.
    exact Heqb0.
  - intros. unfold rs5. Simplifs. unfold rs4. Simplifs.
    unfold rs3. Simplifs. unfold rs2. Simplifs.
    unfold compare_ints. Simplifs.
Qed.

(** Smart constructor for integer conversions *)

Lemma mk_intconv_correct:
  forall mk sem rd rs k c rs1 m b o
         (RP: reg_ptr rs1 PC b o)
         (MI: mk_intconv mk rd rs k = OK c)
         (fEI: forall c rd rs r m,
                 exec_instr ge c (mk rd rs) r m = Next (nextinstr (r#rd <- (sem r#rs))) m),
  exists rs2,
    exec_straight ge fn c rs1 m k rs2 m
    /\ rs2#rd = sem rs1#rs
    /\ forall r, data_preg r = true -> r <> rd -> r <> EAX -> rs2#r = rs1#r.
Proof.
  unfold mk_intconv; intros. destruct (low_ireg rs); monadInv MI.
  - econstructor. repSplit.
    + eapply exec_straight_one. rewrite fEI. eauto.
      srp.
    + Simplifs.
    + intros; Simplifs.
  - econstructor. repSplit. eapply exec_straight_two.
    simpl. eauto. apply fEI. srp. srp.
    srp. intros; srp.
Qed.

(** Smart constructor for small stores *)

Lemma addressing_mentions_correct:
  forall a r (rs1 rs2: regset),
  (forall (r': ireg), r' <> r -> rs1 r' = rs2 r') ->
  addressing_mentions a r = false ->
  eval_addrmode ge a rs1 = eval_addrmode ge a rs2.
Proof.
  intros until rs2; intro AG. unfold addressing_mentions, eval_addrmode.
  destruct a. intros. destruct (orb_false_elim _ _ H). unfold proj_sumbool in *.
  decEq. destruct base; auto. apply AG. destruct (ireg_eq r i); congruence.
  decEq. destruct ofs as [[r' sc] | ]; auto. rewrite AG; auto. destruct (ireg_eq r r'); congruence.
Qed.

Lemma eval_addrmode_int:
  forall addr rs alloc em,
    wt_val (eSexpr alloc em (eval_addrmode ge addr rs)) Tint.
Proof.
  destruct addr; simpl; intros.
  repeat destr; seval.
Qed.

Lemma mk_smallstore_correct:
  forall chunk sto addr r k c rs1 m1 m2 b o
         (Rpc: reg_ptr rs1 PC b o)
         (MKSS: mk_smallstore sto addr r k = OK c)
         (SV: Mem.storev chunk m1 (eval_addrmode ge addr rs1) (rs1 r) = Some m2)
         (EIES: forall c r addr rs m,
                  exec_instr ge c (sto addr r) rs m =
                  exec_store ge chunk m addr rs r nil),
  exists rs2,
    exec_straight ge fn c rs1 m1 k rs2 m2
    /\ forall r, data_preg r = true -> r <> EAX /\ r <> ECX -> rs2#r = rs1#r.
Proof.
  unfold mk_smallstore; intros. 
  remember (low_ireg r) as low. destruct low.
  - (* low reg *)
    monadInv MKSS. econstructor; split.
    eapply exec_straight_one. rewrite EIES. 
    unfold exec_store. rewrite SV. eauto.
    srp.
    intros; Simplifs.
  - (* high reg *)
    remember (addressing_mentions addr EAX) as mentions. destruct mentions; monadInv MKSS.
    + (* EAX is mentioned. *)
      assert (r <> ECX). { red; intros; subst r; discriminate. }
      set (rs2 := nextinstr (rs1#ECX <- (eval_addrmode ge addr rs1))).
      set (rs3 := nextinstr (rs2#EAX <- (rs1 r))).
      econstructor; split.
      * eapply exec_straight_three with (rs2:=rs2) (m2:=m1) (rs3:=rs3) (m3:=m1); auto.
        simpl. replace (rs2 r) with (rs1 r). auto. unfold rs2; Simplifs. 
        rewrite EIES. unfold exec_store. simpl. 
        replace (rs3 EAX) with (rs1 r).
        replace (rs3 ECX) with (eval_addrmode ge addr rs1).
        revert SV; unfold Mem.storev.
        rewrite (Mem.same_eval_eqm m1 (eval_addrmode ge addr rs1)
                                   (Val.add (eval_addrmode ge addr rs1)
                                            (Val.add (Eval (Vint Int.zero))
                                                     (Eval (Vint Int.zero))))).
        destr. rewrite SV; auto.
        red; simpl; intros.
        generalize (eval_addrmode_int addr rs1 cm em).
        seval. rewrite Int.add_zero. auto.
        unfold rs3, rs2; srp.
        unfold rs3, rs2; srp.  srp. srp. srp. 
      * intros. Simplifs.
        destr.
        unfold rs3, rs2; Simplifs. 
    + (* EAX is not mentioned *)
      set (rs2 := nextinstr (rs1#EAX <- (rs1 r))).
      econstructor; split.
      eapply exec_straight_two with (rs2:=rs2) (m2:=m1); eauto.
      rewrite EIES. unfold exec_store. 
      rewrite (addressing_mentions_correct addr EAX rs2 rs1); auto.
      replace (rs2 EAX) with (rs1 r). rewrite SV. eauto. 
      intros. unfold rs2; Simplifs. 
      intros. unfold rs2; Simplifs.
      srp. srp. intros; srp. simpl. unfold rs2; Simplifs.
      destr; Simplifs.
Qed.

(** Accessing slots in the stack frame *)

Lemma loadv_se:
  forall m c ptr ptr',
    same_eval ptr ptr' ->
    Mem.loadv c m ptr = Mem.loadv c m ptr'.
Proof.
  intros; unfold Mem.loadv.
  rewrite (Mem.same_eval_eqm _ _ _ H). auto.
Qed.
        

Lemma loadind_correct:
  forall (base: ireg) ofs ty dst k (rs: regset) c m v b o
         (Npc: reg_ptr rs PC b o)
         (LI: loadind base ofs ty dst k = OK c)
         (LV: Mem.loadv (chunk_of_type ty) m (Val.add rs#base (Eval (Vint ofs))) = Some v),
  exists rs',
    exec_straight ge fn c rs m k rs' m
    /\ rs'#(preg_of dst) = v
    /\ forall r, data_preg r = true -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  unfold loadind; intros.
  set (addr := Addrmode (Some base) None (inl (ident * int) ofs)) in *.
  assert (SE: same_eval (eval_addrmode ge addr rs) (Val.add rs#base (Eval (Vint ofs)))).
  {
    unfold addr. simpl. red; simpl; intros; seval; sint. rewrite Int.add_zero_l; auto.
  }
  exists (nextinstr_nf (rs#(preg_of dst) <- v)); split.
  - destruct ty; try discriminate; destruct (preg_of dst); inv LI;
    eapply exec_straight_one; eauto; simpl; unfold exec_load; simpl in LV;
    try (erewrite loadv_se; eauto); try (setoid_rewrite LV; auto);
    srp.
  - intuition Simplifs.
Qed.

Lemma storev_se:
  forall m c ptr ptr' v,
    same_eval ptr ptr' ->
    Mem.storev c m ptr v = Mem.storev c m ptr' v.
Proof.
  intros; unfold Mem.storev.
  rewrite (Mem.same_eval_eqm _ _ _ H). auto.
Qed.

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k (rs: regset) c m m' b o
         (Rpc: reg_ptr rs PC b o)
         (SI: storeind src base ofs ty k = OK c)
         (SV: Mem.storev (chunk_of_type ty) m
                         (Val.add rs#base (Eval (Vint ofs))) (rs#(preg_of src)) = Some m'),
  exists rs',
    exec_straight ge fn c rs m k rs' m'
    /\ forall r, data_preg r = true -> preg_notin r (destroyed_by_setstack ty) -> rs'#r = rs#r.
Proof.
  Local Transparent destroyed_by_setstack.
  unfold storeind; intros.
  set (addr := Addrmode (Some base) None (inl (ident * int) ofs)) in *.
  assert (SE:same_eval (eval_addrmode ge addr rs) (Val.add rs#base (Eval (Vint ofs)))).
  {
    unfold addr. red; simpl; intros; seval; sint; auto.
    rewrite Int.add_zero_l; auto.
  }
  rewrite <- (storev_se _ _ _ _ _ SE) in SV. clear SE. 
  destruct ty; try discriminate; destruct (preg_of src); inv SI;
  (econstructor; split;
   [eapply exec_straight_one; eauto ; simpl ; unfold exec_store;
    try setoid_rewrite SV; eauto
   |simpl; intros; unfold undef_regs; repeat Simplifs]);
  srp.
Qed.

(** Translation of addressing modes *)

Lemma transl_addressing_mode_correct:
  forall addr args am (rs: regset) v,
  transl_addressing addr args = OK am ->
  eval_addressing ge (rs ESP) addr (List.map rs (List.map preg_of args)) = Some v ->
  Val.lessdef v (eval_addrmode ge am rs).
Proof.
  assert (A: forall n, Int.add Int.zero n = n). 
  { intros. rewrite Int.add_commut. apply Int.add_zero. }
  assert (B: forall n i, (if Int.eq i Int.one then Vint n else Vint (Int.mul n i)) = Vint (Int.mul n i)).
  {
    intros. predSpec Int.eq Int.eq_spec i Int.one. 
    subst i. rewrite Int.mul_one. auto. auto.
  }
  assert (C: forall v i,
    Val.lessdef (Val.mul v (Eval (Vint i)))
               (if Int.eq i Int.one then v else Val.mul v (Eval (Vint i)))).
  {
    red; intros; simpl. predSpec Int.eq Int.eq_spec i Int.one.
    subst i. seval; auto. rewrite Int.mul_one; auto.
    simpl; auto.
  }
  unfold transl_addressing; intros.
  destruct addr; repeat (destruct args; try discriminate); simpl in H0; inv H0.
  - (* indexed *)
    monadInv H. rewrite (ireg_of_eq _ _ EQ). simpl.
    red; intros; simpl; seval; sint; auto. rewrite A; auto.
  - (* indexed2 *)
    monadInv H. rewrite (ireg_of_eq _ _ EQ); rewrite (ireg_of_eq _ _ EQ1). simpl.
    rewrite Int.eq_true. red; intros; simpl; seval; sint; auto.  
  - (* scaled *)
    monadInv H. rewrite (ireg_of_eq _ _ EQ). unfold eval_addrmode.
    predSpec Int.eq Int.eq_spec i Int.one;
    destr; red; intros; simpl; seval; sint; auto. rewrite A.
    rewrite Int.mul_one. auto.
    rewrite A. auto.
  - (* indexed2scaled *)
    monadInv H. rewrite (ireg_of_eq _ _ EQ); rewrite (ireg_of_eq _ _ EQ1); simpl.
    predSpec Int.eq Int.eq_spec i Int.one;
    destr; red; intros; simpl; seval; sint; auto. rewrite Int.mul_one; auto.
  - (* global *)
    inv H. simpl.
    rewrite H2.
    unfold Genv.symbol_address' in H2; revert H2; destr; inv H2.
    red; intros; simpl; seval; sint; auto. rewrite ! A. auto.
  - (* based *)
    monadInv H. simpl.
    destruct (Genv.symbol_address' ge i i0); destr; try congruence.
    inv H2. erewrite ireg_of_eq; eauto.
    red; intros; simpl; seval; sint; auto. rewrite A. auto. 
  - (* basedscaled *)
    monadInv H. simpl.
    predSpec Int.eq Int.eq_spec i Int.one;
      repeat (revert H2; destr); inv H2; rewrite (ireg_of_eq _ _ EQ); red; intros; seval; sint; inv Heqv; auto; rewrite ! A.
    rewrite Int.mul_one. rewrite Int.add_commut; auto.
    rewrite Int.add_commut; auto.
  - (* instack *)
    inv H; simpl. red; intros; simpl; seval; sint; auto. rewrite A; auto.
Qed.

(** Processor conditions and comparisons *)

Lemma compare_ints_spec:
  forall rs v1 v2 m,
  let rs' := nextinstr (compare_ints v1 v2 rs m) in
     rs'#ZF = Val.cmpu Ceq v1 v2
  /\ rs'#CF = Val.cmpu Clt v1 v2
  /\ rs'#SF = (Ebinop (OpCmp SESigned Clt) Tint Tint (Val.sub v1 v2) (Eval (Vint Int.zero)))
  /\ rs'#OF = (Ebinop OpSubOverflow Tint Tint v1 v2)
  /\ (forall r, data_preg r = true -> rs'#r = rs#r).
Proof.
  intros. unfold rs'; unfold compare_ints.
  repeat (split; intros; Simplifs).
Qed.

Lemma int_signed_eq:
  forall x y, Int.eq x y = zeq (Int.signed x) (Int.signed y).
Proof.
  intros. unfold Int.eq. unfold proj_sumbool. 
  destruct (zeq (Int.unsigned x) (Int.unsigned y));
  destruct (zeq (Int.signed x) (Int.signed y)); auto.
  elim n. unfold Int.signed. rewrite e; auto.
  elim n. apply Int.eqm_small_eq; auto with ints. 
  eapply Int.eqm_trans. apply Int.eqm_sym. apply Int.eqm_signed_unsigned.
  rewrite e. apply Int.eqm_signed_unsigned. 
Qed.

Lemma int_not_lt:
  forall x y, negb (Int.lt y x) = (Int.lt x y || Int.eq x y).
Proof.
  intros. unfold Int.lt. rewrite int_signed_eq. unfold proj_sumbool.
  destruct (zlt (Int.signed y) (Int.signed x)).
  rewrite zlt_false. rewrite zeq_false. auto. omega. omega.
  destruct (zeq (Int.signed x) (Int.signed y)). 
  rewrite zlt_false. auto. omega. 
  rewrite zlt_true. auto. omega.
Qed.

Lemma int_lt_not:
  forall x y, Int.lt y x = negb (Int.lt x y) && negb (Int.eq x y).
Proof.
  intros. rewrite <- negb_orb. rewrite <- int_not_lt. rewrite negb_involutive. auto.
Qed.

Lemma int_not_ltu:
  forall x y, negb (Int.ltu y x) = (Int.ltu x y || Int.eq x y).
Proof.
  intros. unfold Int.ltu, Int.eq.
  destruct (zlt (Int.unsigned y) (Int.unsigned x)).
  rewrite zlt_false. rewrite zeq_false. auto. omega. omega.
  destruct (zeq (Int.unsigned x) (Int.unsigned y)). 
  rewrite zlt_false. auto. omega. 
  rewrite zlt_true. auto. omega.
Qed.

Lemma int_ltu_not:
  forall x y, Int.ltu y x = negb (Int.ltu x y) && negb (Int.eq x y).
Proof.
  intros. rewrite <- negb_orb. rewrite <- int_not_ltu. rewrite negb_involutive. auto.
Qed.

Lemma testcond_for_signed_comparison_correct:
  forall c v1 v2 rs m,
    same_eval (Val.cmp_bool c v1 v2)
              (eval_testcond (testcond_for_signed_comparison c)
                             (nextinstr (compare_ints v1 v2 rs m))).
Proof.
  intros. generalize (compare_ints_spec rs v1 v2 m).
  set (rs' := nextinstr (compare_ints v1 v2 rs m)).
  intros [A [B [C [D E]]]].
  red; simpl; intros.
  unfold eval_testcond. rewrite A; rewrite B; rewrite C; rewrite D.
  simpl.
  des c; seval; try solve [destr].
  des (Int.eq i i0).
  rewrite ! lift_vint. rewrite Int.lt_sub_overflow.
  destr.
  rewrite ! lift_vint.
  rewrite int_not_lt. rewrite Int.lt_sub_overflow.
  destruct (Int.lt i i0); simpl; destruct (Int.eq i i0); auto.
  rewrite ! lift_vint. rewrite Int.lt_sub_overflow.
  rewrite (int_lt_not i i0). destruct (Int.lt i i0); destruct (Int.eq i i0); reflexivity.
  rewrite ! lift_vint. rewrite Int.lt_sub_overflow.
  destruct (Int.lt i i0); reflexivity.
Qed.


Lemma testcond_for_unsigned_comparison_correct:
  forall c v1 v2 rs m,
    same_eval (Val.cmpu_bool c v1 v2)
              (eval_testcond (testcond_for_unsigned_comparison c)
                             (nextinstr (compare_ints v1 v2 rs m))).
Proof.
  intros. generalize (compare_ints_spec rs v1 v2 m).
  set (rs' := nextinstr (compare_ints v1 v2 rs m)).
  intros [A [B [C [D E]]]].
  red; simpl; intros.
  unfold eval_testcond. rewrite A; rewrite B; rewrite C; rewrite D.
  simpl.
 
  des c; seval; try solve [destr].
  des (Int.eq i i0).
  rewrite ! (lift_vint (Int.ltu _ _)). rewrite int_not_ltu.
  repeat destr;
    repeat match goal with
             | H: context[?a || false] |- _ => rewrite orb_false_r in H
             | H: context[?a || true] |- _ => rewrite orb_true_r in H; try congruence
             | H : context [if ?a then _ else _],
                   H1: ?a = _ |- _ => rewrite H1 in H                           
             | |- context [Int.or ?x Int.zero] => rewrite Int.or_zero
             | |- context [Int.or Int.zero ?x] => rewrite Int.or_zero_l
             | |- context [Int.or ?x ?x] => rewrite Int.or_idem
             | H: Int.eq ?x ?x = false |- _ => rewrite Int.eq_true in H; congruence
             | H: Int.eq Int.zero Int.one = true |- _ => rewrite Int.eq_false in H by discriminate; try congruence
           end.
  rewrite int_ltu_not.
  repeat destr;
    repeat match goal with
             | H: context[?a || false] |- _ => rewrite orb_false_r in H
             | H: context[?a || true] |- _ => rewrite orb_true_r in H; try congruence
             | H : context [if ?a then _ else _],
                   H1: ?a = _ |- _ => rewrite H1 in H                           
             | |- context [Int.or ?x Int.zero] => rewrite Int.or_zero
             | |- context [Int.or Int.zero ?x] => rewrite Int.or_zero_l
             | |- context [Int.or ?x ?x] => rewrite Int.or_idem
             | H: Int.eq ?x ?x = false |- _ => rewrite Int.eq_true in H; congruence
             | H: Int.eq Int.zero Int.one = true |- _ => rewrite Int.eq_false in H by discriminate; try congruence
             | H: Int.eq Int.one Int.zero = true |- _ => rewrite Int.eq_false in H by discriminate; try congruence
           end.
  destruct (Int.ltu i i0); simpl;
  reflexivity.
Qed.

Lemma compare_floats_spec:
  forall rs n1 n2,
  let rs' := nextinstr (compare_floats n1 n2 rs) in
     rs'#ZF = Val.cmpf Ceq n1 n2
     /\ rs'#CF = Val.notbool (Val.cmpf Cge n1 n2)
  /\ rs'#PF = Val.notbool (Val.or (Val.cmpf Ceq n1 n2)
                                  (Val.or (Val.cmpf Clt n1 n2) (Val.cmpf Cgt n1 n2)))
  /\ (forall r, data_preg r = true -> rs'#r = rs#r).
Proof.
  intros. unfold rs'; unfold compare_floats.
  repeat (split; intros; Simplifs).
Qed.


Lemma compare_floats32_spec:
  forall rs n1 n2,
  let rs' := nextinstr (compare_floats32 n1 n2 rs) in
     rs'#ZF = Val.cmpfs Ceq n1 n2
  /\ rs'#CF = Val.notbool (Val.cmpfs Cge n1 n2)
  /\ rs'#PF = Val.notbool (Val.or (Val.cmpfs Ceq n1 n2)
                                  (Val.or (Val.cmpfs Clt n1 n2) (Val.cmpfs Cgt n1 n2)))
  /\ (forall r, data_preg r = true -> rs'#r = rs#r).
Proof.
  intros. unfold rs'; unfold compare_floats32.
  repeat (split; intros; Simplifs).
Qed.

Definition eval_extcond (xc: extcond) (rs: regset) : expr_sym :=
  match xc with
  | Cond_base c =>
      eval_testcond c rs
  | Cond_and c1 c2 =>
    Val.and (eval_testcond c1 rs) (eval_testcond c2 rs)
  | Cond_or c1 c2 =>
    Val.or (eval_testcond c1 rs) (eval_testcond c2 rs)
  end.

Definition swap_floats {A: Type} (c: comparison) (n1 n2: A) : A :=
  match c with
  | Clt | Cle => n2
  | Ceq | Cne | Cgt | Cge => n1
  end.

 
Lemma testcond_for_float_comparison_correct:
  forall c n1 n2 rs,
    same_eval (eval_extcond (testcond_for_condition (Ccompf c))
                            (nextinstr (compare_floats ((swap_floats c n1 n2))
                                                       ((swap_floats c n2 n1)) rs)))
              (Val.cmpf c n1 n2).
Proof.
  intros.
  generalize (compare_floats_spec rs (swap_floats c n1 n2) (swap_floats c n2 n1)).
  set (rs' := nextinstr (compare_floats ((swap_floats c n1 n2))
                                        ((swap_floats c n2 n1)) rs)).
  intros [A [B [C D]]]. 
  unfold eval_extcond, eval_testcond. rewrite A; rewrite B; rewrite C.
destruct c; simpl; red; simpl; intros; seval; 
  repeat match goal with
           | |- _ => solve [repeat destr]
           | |- context [Float.cmp Cne ?a ?b] => rewrite (Float.cmp_ne_eq a b); simpl
           | |- context [Float.cmp Cge ?a ?b] => rewrite <- (Float.cmp_swap Cge b a); simpl
           | |- context [Float.cmp Cgt ?a ?b] => rewrite <- (Float.cmp_swap Cgt b a); simpl
           | |- context [Float.cmp Cle ?a ?b] => rewrite (Float.cmp_le_lt_eq a b); simpl
           | |- context [Float.cmp Cge ?a ?b] => rewrite (Float.cmp_ge_gt_eq a b); simpl
           | |- context [Float.cmp Ceq ?f0 ?f] =>
             repeat match goal with
                        |- context [Float.cmp Ceq f f0] => rewrite <- (Float.cmp_swap Ceq f0 f); simpl
                    end
         end; repeat destr;
  repeat match goal with
           | H: Int.eq Int.zero Int.one = true |- _ => rewrite Int.eq_false in H by discriminate; try congruence
           | H: Int.eq Int.one Int.zero = true |- _ => rewrite Int.eq_false in H by discriminate; try congruence
           | H: Int.eq ?x ?x = false |- _ => rewrite Int.eq_true in H; try congruence
           | H: Float.cmp Clt ?f ?f0 = true,
                H1: Float.cmp Ceq ?f ?f0 = true |- _ =>
             generalize (Float.cmp_lt_eq_false _ _ H H1); contradiction
           | H: Float.cmp Cgt ?f ?f0 = true,
                H1: Float.cmp Ceq ?f ?f0 = true |- _ =>
             generalize (Float.cmp_gt_eq_false _ _ H H1); contradiction
         end.
Qed.

Lemma testcond_for_neg_float_comparison_correct:
  forall c n1 n2 rs,
    same_eval
      (eval_extcond (testcond_for_condition (Cnotcompf c))
                    (nextinstr (compare_floats ((swap_floats c n1 n2))
                                               ((swap_floats c n2 n1)) rs)))
      (Val.notbool (Val.cmpf c n1 n2)).
Proof.
  intros.
  generalize (compare_floats_spec rs (swap_floats c n1 n2) (swap_floats c n2 n1)).
  set (rs' := nextinstr (compare_floats ((swap_floats c n1 n2))
                                        ((swap_floats c n2 n1)) rs)).
  intros [A [B [C D]]].
  unfold eval_extcond, eval_testcond. rewrite A; rewrite B; rewrite C.
  destruct c; simpl; red; simpl; intros; seval; 
  repeat match goal with
           | |- _ => solve [repeat destr]
           | |- context [Float.cmp Cne ?a ?b] => rewrite (Float.cmp_ne_eq a b); simpl
           | |- context [Float.cmp Cge ?a ?b] => rewrite <- (Float.cmp_swap Cge b a); simpl
           | |- context [Float.cmp Cgt ?a ?b] => rewrite <- (Float.cmp_swap Cgt b a); simpl
           | |- context [Float.cmp Cle ?a ?b] => rewrite (Float.cmp_le_lt_eq a b); simpl
           | |- context [Float.cmp Cge ?a ?b] => rewrite (Float.cmp_ge_gt_eq a b); simpl
           | |- context [Float.cmp Ceq ?f0 ?f] =>
             repeat match goal with
                        |- context [Float.cmp Ceq f f0] => rewrite <- (Float.cmp_swap Ceq f0 f); simpl
                    end
         end; repeat destr;
  repeat match goal with
           | H: Int.eq Int.zero Int.one = true |- _ => rewrite Int.eq_false in H by discriminate; try congruence
           | H: Int.eq ?x ?x = false |- _ => rewrite Int.eq_true in H; try congruence
           | H: Float.cmp Clt ?f ?f0 = true,
                H1: Float.cmp Ceq ?f ?f0 = true |- _ =>
             generalize (Float.cmp_lt_eq_false _ _ H H1); contradiction
           | H: Float.cmp Cgt ?f ?f0 = true,
                H1: Float.cmp Ceq ?f ?f0 = true |- _ =>
             generalize (Float.cmp_gt_eq_false _ _ H H1); contradiction
         end.
Qed.

Lemma testcond_for_float32_comparison_correct:
  forall c n1 n2 rs,
    same_eval (eval_extcond (testcond_for_condition (Ccompfs c))
                            (nextinstr (compare_floats32 ((swap_floats c n1 n2))
                                                         ((swap_floats c n2 n1)) rs)))
              (Val.cmpfs c n1 n2).
Proof.
  intros.
  generalize (compare_floats32_spec rs (swap_floats c n1 n2) (swap_floats c n2 n1)).
  set (rs' := nextinstr (compare_floats32 ((swap_floats c n1 n2))
                                        ((swap_floats c n2 n1)) rs)).
  intros [A [B [C D]]].
  unfold eval_extcond, eval_testcond. rewrite A; rewrite B; rewrite C.
  destruct c; simpl; red; simpl; intros; seval; 
  repeat match goal with
           | |- _ => solve [repeat destr]
           | |- context [Float32.cmp Cne ?a ?b] => rewrite (Float32.cmp_ne_eq a b); simpl
           | |- context [Float32.cmp Cge ?a ?b] => rewrite <- (Float32.cmp_swap Cge b a); simpl
           | |- context [Float32.cmp Cgt ?a ?b] => rewrite <- (Float32.cmp_swap Cgt b a); simpl
           | |- context [Float32.cmp Cle ?a ?b] => rewrite (Float32.cmp_le_lt_eq a b); simpl
           | |- context [Float32.cmp Cge ?a ?b] => rewrite (Float32.cmp_ge_gt_eq a b); simpl
           | |- context [Float32.cmp Ceq ?f0 ?f] =>
             repeat match goal with
                        |- context [Float32.cmp Ceq f f0] => rewrite <- (Float32.cmp_swap Ceq f0 f); simpl
                    end
         end; repeat destr;
  repeat match goal with
           | H: Int.eq Int.zero Int.one = true |- _ => rewrite Int.eq_false in H by discriminate; try congruence
           | H: Int.eq Int.one Int.zero = true |- _ => rewrite Int.eq_false in H by discriminate; try congruence
           | H: Int.eq ?x ?x = false |- _ => rewrite Int.eq_true in H; try congruence
           | H: Float32.cmp Clt ?f ?f0 = true,
                H1: Float32.cmp Ceq ?f ?f0 = true |- _ =>
             generalize (Float32.cmp_lt_eq_false _ _ H H1); contradiction
           | H: Float32.cmp Cgt ?f ?f0 = true,
                H1: Float32.cmp Ceq ?f ?f0 = true |- _ =>
             generalize (Float32.cmp_gt_eq_false _ _ H H1); contradiction
         end.
Qed.

Lemma testcond_for_neg_float32_comparison_correct:
  forall c n1 n2 rs,
    same_eval (eval_extcond (testcond_for_condition (Cnotcompfs c))
                            (nextinstr (compare_floats32 ((swap_floats c n1 n2))
                                                         ((swap_floats c n2 n1)) rs)))
              (Val.notbool (Val.cmpfs c n1 n2)).
Proof.
  intros.
  generalize (compare_floats32_spec rs (swap_floats c n1 n2) (swap_floats c n2 n1)).
  set (rs' := nextinstr (compare_floats32 ((swap_floats c n1 n2))
                                          ((swap_floats c n2 n1)) rs)).
  intros [A [B [C D]]].
  unfold eval_extcond, eval_testcond. rewrite A; rewrite B; rewrite C.

  destruct c; simpl;red ; simpl; intros; seval; 
  repeat match goal with
           | |- _ => solve [repeat destr]
           | |- context [Float32.cmp Cne ?a ?b] => rewrite (Float32.cmp_ne_eq a b); simpl
           | |- context [Float32.cmp Cge ?a ?b] => rewrite <- (Float32.cmp_swap Cge b a); simpl
           | |- context [Float32.cmp Cgt ?a ?b] => rewrite <- (Float32.cmp_swap Cgt b a); simpl
           | |- context [Float32.cmp Cle ?a ?b] => rewrite (Float32.cmp_le_lt_eq a b); simpl
           | |- context [Float32.cmp Cge ?a ?b] => rewrite (Float32.cmp_ge_gt_eq a b); simpl
           | |- context [Float32.cmp Ceq ?f0 ?f] =>
             repeat match goal with
                        |- context [Float32.cmp Ceq f f0] => rewrite <- (Float32.cmp_swap Ceq f0 f); simpl
                    end
         end; repeat destr;
  repeat match goal with
           | H: Int.eq Int.zero Int.one = true |- _ => rewrite Int.eq_false in H by discriminate; try congruence
           | H: Int.eq Int.one Int.zero = true |- _ => rewrite Int.eq_false in H by discriminate; try congruence
           | H: Int.eq ?x ?x = false |- _ => rewrite Int.eq_true in H; try congruence
           | H: Float32.cmp Clt ?f ?f0 = true,
                H1: Float32.cmp Ceq ?f ?f0 = true |- _ =>
             generalize (Float32.cmp_lt_eq_false _ _ H H1); contradiction
           | H: Float32.cmp Cgt ?f ?f0 = true,
                H1: Float32.cmp Ceq ?f ?f0 = true |- _ =>
             generalize (Float32.cmp_gt_eq_false _ _ H H1); contradiction
         end.
Qed.

Remark swap_floats_commut:
  forall (A B: Type) c (f: A -> B) x y, swap_floats c (f x) (f y) = f (swap_floats c x y).
Proof.
  intros. destruct c; auto. 
Qed.

Remark compare_floats_inv:
  forall vx vy rs r,
  r <> CR ZF -> r <> CR CF -> r <> CR PF -> r <> CR SF -> r <> CR OF ->
  compare_floats vx vy rs r = rs r.
Proof.
  intros. 
  assert (DFL: undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs r = rs r).
  simpl. Simplifs. 
  unfold compare_floats. Simplifs. 
Qed.

Remark compare_floats32_inv:
  forall vx vy rs r,
  r <> CR ZF -> r <> CR CF -> r <> CR PF -> r <> CR SF -> r <> CR OF ->
  compare_floats32 vx vy rs r = rs r.
Proof.
  intros. 
  assert (DFL: undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs r = rs r).
    simpl. Simplifs. 
  unfold compare_floats32. Simplifs. 
Qed.

Lemma transl_cond_correct':
  forall cond args k c rs m b o
         (Rpc: reg_ptr rs PC b o)
         (TC: transl_cond cond args k = OK c),
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ match eval_condition cond (map rs (map preg_of args)) with
     | None => False
     | Some b => same_eval (eval_extcond (testcond_for_condition cond) rs') b
     end
  /\ forall r, data_preg r = true -> rs'#r = rs r.
Proof.
  unfold transl_cond; intros. 
  destruct cond; repeat (destruct args; try discriminate); monadInv TC.
  - (* comp *)
    simpl. rewrite (ireg_of_eq _ _ EQ). rewrite (ireg_of_eq _ _ EQ1).
    econstructor. split. eapply exec_straight_one. simpl. eauto.
    unfold compare_ints. srp. 
    split.
    rewrite testcond_for_signed_comparison_correct; eauto. reflexivity.
    intros. unfold compare_ints. Simplifs.
  - (* compu *)
    simpl. rewrite (ireg_of_eq _ _ EQ). rewrite (ireg_of_eq _ _ EQ1).
    econstructor. split. eapply exec_straight_one. simpl. eauto.
    unfold compare_ints. srp.
    split. 
    rewrite testcond_for_unsigned_comparison_correct; eauto.  reflexivity.
    intros. unfold compare_ints. Simplifs.
  - (* compimm *)
    simpl. rewrite (ireg_of_eq _ _ EQ). destruct (Int.eq_dec i Int.zero).
    econstructor; split. eapply exec_straight_one. simpl; eauto.
    unfold compare_ints.
    srp.
    split. rewrite <- testcond_for_signed_comparison_correct; eauto. 
    red; simpl; intros; seval. rewrite Int.and_idem; auto.
    intros. unfold compare_ints. Simplifs.
    econstructor; split. eapply exec_straight_one. simpl; eauto.
    unfold compare_ints.
    srp.
    split. rewrite <- testcond_for_signed_comparison_correct; eauto. reflexivity.
    intros. unfold compare_ints. Simplifs.
  - (* compuimm *)
    simpl. rewrite (ireg_of_eq _ _ EQ).
    econstructor. split. eapply exec_straight_one. simpl. eauto.
    unfold compare_ints.
    srp.
    split. rewrite <- testcond_for_unsigned_comparison_correct; eauto.
    reflexivity.
    intros. unfold compare_ints. Simplifs.
  - (* compf *)
    simpl. rewrite (freg_of_eq _ _ EQ). rewrite (freg_of_eq _ _ EQ1).
    exists (nextinstr (compare_floats (swap_floats c0 (rs x) (rs x0)) (swap_floats c0 (rs x0) (rs x)) rs)).
    split. eapply exec_straight_one. 
    destruct c0; simpl; auto.
    unfold compare_floats.
    srp.
    split. rewrite <- testcond_for_float_comparison_correct.
    destruct c0; simpl; reflexivity.
    intros. Simplifs. apply compare_floats_inv; auto with asmgen. 
  - (* notcompf *)
    simpl. rewrite (freg_of_eq _ _ EQ). rewrite (freg_of_eq _ _ EQ1).
    exists (nextinstr (compare_floats (swap_floats c0 (rs x) (rs x0)) (swap_floats c0 (rs x0) (rs x)) rs)).
    split. eapply exec_straight_one. 
    destruct c0; simpl; auto.
    unfold compare_floats.
    srp.
    split. 
    apply testcond_for_neg_float_comparison_correct.
    intros. Simplifs. apply compare_floats_inv; auto with asmgen. 
  - (* compfs *)
    simpl. rewrite (freg_of_eq _ _ EQ). rewrite (freg_of_eq _ _ EQ1).
    exists (nextinstr (compare_floats32 (swap_floats c0 (rs x) (rs x0)) (swap_floats c0 (rs x0) (rs x)) rs)).
    split. eapply exec_straight_one. 
    destruct c0; simpl; auto.
    unfold compare_floats32.
    srp.
    split. apply testcond_for_float32_comparison_correct.
    intros. Simplifs. apply compare_floats32_inv; auto with asmgen. 
  - (* notcompfs *)
    simpl. rewrite (freg_of_eq _ _ EQ). rewrite (freg_of_eq _ _ EQ1).
    exists (nextinstr (compare_floats32 (swap_floats c0 (rs x) (rs x0)) (swap_floats c0 (rs x0) (rs x)) rs)).
    split. eapply exec_straight_one. 
    destruct c0; simpl; auto.
    unfold compare_floats32.
    srp.
    split. apply testcond_for_neg_float32_comparison_correct.
    intros. Simplifs. apply compare_floats32_inv; auto with asmgen. 
  - (* maskzero *)
    simpl. rewrite (ireg_of_eq _ _ EQ).
    econstructor. split. eapply exec_straight_one. simpl; eauto.
    unfold compare_ints.
    srp.
    split.
    generalize (compare_ints_spec rs (Val.and (rs x) (Eval (Vint i))) (Eval Vzero) m).
    intros [A B]. rewrite A.
    red; simpl; intros; seval. destr.
    intros. unfold compare_ints. Simplifs.
  - (* masknotzero *)
    simpl. rewrite (ireg_of_eq _ _ EQ).
    econstructor. split. eapply exec_straight_one. simpl; eauto.
    unfold compare_ints.
    srp.
    split. 
    generalize (compare_ints_spec rs (Val.and (rs x) (Eval (Vint i))) (Eval Vzero) m).
    intros [A B]. rewrite A.
    red; simpl; intros; seval; destr.
    intros. unfold compare_ints. Simplifs.
Qed.


Lemma transl_cond_correct:
  forall cond args k c rs m b o
         (Rpc: reg_ptr rs PC b o)
         (TC: transl_cond cond args k = OK c),
  exists rs' b,
     exec_straight ge fn c rs m k rs' m
     /\ eval_condition cond (map rs (map preg_of args)) = Some b
     /\ same_eval (eval_extcond (testcond_for_condition cond) rs') b
     /\ forall r, data_preg r = true -> rs'#r = rs r.
Proof.
  intros.
  exploit transl_cond_correct'; eauto.
  intros (rs'  & A & B & C).
  revert B; destr.
  (exists rs', e). eauto.
Qed.

Remark eval_testcond_nextinstr:
  forall c rs, eval_testcond c (nextinstr rs) = eval_testcond c rs.
Proof.
  intros. unfold eval_testcond. repeat rewrite nextinstr_inv; auto with asmgen.
Qed.

Remark eval_testcond_set_ireg:
  forall c rs r v, eval_testcond c (rs#(IR r) <- v) = eval_testcond c rs.
Proof.
  intros. unfold eval_testcond. repeat rewrite Pregmap.gso; auto with asmgen.
Qed.

Lemma mk_setcc_base_correct:
  forall cond rd k rs1 m b o
         (Rpc: reg_ptr rs1 PC b o),
  exists rs2,
    exec_straight ge fn (mk_setcc_base cond rd k) rs1 m k rs2 m
    /\ same_eval rs2#rd (eval_extcond cond rs1)
    /\ forall r, data_preg r = true -> r <> EAX /\ r <> ECX -> r <> rd -> rs2#r = rs1#r.
Proof.
  intros. destruct cond; simpl in *.
- (* base *)
  econstructor; split.
  eapply exec_straight_one. simpl; eauto.
  srp.
  split. rewrite nextinstr_inv by discriminate. rewrite Pregmap.gss; reflexivity.
  intros; Simplifs. 
- (* or *)
  destruct (ireg_eq rd EAX).
  + subst rd. econstructor; split. 
    * eapply exec_straight_three; eauto.
      simpl; eauto.
      simpl. rewrite eval_testcond_nextinstr. repeat rewrite eval_testcond_set_ireg. eauto.
      simpl; eauto.
      srp.
      srp; auto.
      srp; auto.
    * split. Simplifs. reflexivity.
      intuition Simplifs.
  + econstructor; split.
    eapply exec_straight_three.
    simpl; eauto.
    simpl. rewrite eval_testcond_nextinstr. repeat rewrite eval_testcond_set_ireg. eauto. 
    simpl. eauto.
    srp.
    srp; auto.
    srp; auto.
    split. Simplifs. red; simpl; intros; seval. rewrite Int.or_commut; auto. 
    intuition Simplifs.
- (* and *)
  destruct (ireg_eq rd EAX).
  + subst rd. econstructor; split.
    * eapply exec_straight_three.
      simpl; eauto.
      simpl. rewrite eval_testcond_nextinstr. repeat rewrite eval_testcond_set_ireg. eauto.
      simpl; eauto.
      srp.
      srp; auto.
      srp; auto.
    * split. Simplifs. reflexivity.
      intuition Simplifs.
  + econstructor; split.
    eapply exec_straight_three.
    simpl; eauto.
    simpl. rewrite eval_testcond_nextinstr. repeat rewrite eval_testcond_set_ireg. eauto. 
    simpl. eauto.
    srp; auto.
    srp; auto.
    srp; auto.
    split. Simplifs. red; simpl; intros; seval. rewrite Int.and_commut; auto.
    intuition Simplifs.
Qed.

Lemma sn_minus_n:
  forall (n:nat),
    (Datatypes.S n - n = 1)%nat.
Proof.
  induction n; simpl; intros; auto.
Qed.

Lemma exec_straight_length:
  forall i rs1 m k rs2 m'
         (RS: exec_straight ge fn i rs1 m k rs2 m'),
    (length i >= length k)%nat.
Proof.
  induction 1; simpl; intros. omega.
  omega.
Qed.
  
Lemma exec_straight_wfpc:
  forall i rs1 m k rs2 m'
         (ES:     exec_straight ge fn i rs1 m k rs2 m')
         b o (Rpc: reg_ptr rs1 PC b o),
    reg_ptr rs2 PC b (Int.add o (Int.repr (Z.of_nat (length i - length k)))).
Proof.
  Opaque minus.
  induction 1; simpl; intros.
  - srp. red; rewrite RP. 
    rewrite sn_minus_n. auto.
  - srp. apply IHES in RP.
    red; rewrite RP. unfold incr, Int.one. sint. rewrite Val.int_add_repr.
    f_equal. f_equal. f_equal. f_equal.
    exploit exec_straight_length; eauto.
    zify; omega.
Qed.

Lemma sn_minus_sm:
  forall n m,
    (Datatypes.S n - Datatypes.S m = n - m)%nat.
Proof.
  induction n; simpl; intros; auto.
Qed.

Lemma mk_setcc_base_length:
  forall cond rd k,
    (length (mk_setcc_base cond EAX (Pmov_rr rd EAX :: k)) - Datatypes.S (length k)
    = match cond with
          Cond_base _ => 1
        | _ => 3
      end)%nat.
Proof.
  des cond; omega.
Qed.

Lemma mk_setcc_correct:
  forall cond rd k rs1 m b o
         (Rpc: reg_ptr rs1 PC b o),
  exists rs2,
    exec_straight ge fn (mk_setcc cond rd k) rs1 m k rs2 m
    /\ same_eval rs2#rd (eval_extcond cond rs1)
    /\ forall r, data_preg r = true -> r <> EAX /\ r <> ECX -> r <> rd -> rs2#r = rs1#r.
Proof.
  intros. unfold mk_setcc. destruct (low_ireg rd).
- eapply mk_setcc_base_correct; eauto.
- exploit mk_setcc_base_correct. eauto. 
  intros [rs2 [A [B C]]].
  exploit exec_straight_wfpc; eauto. intros D.
  econstructor; split. eapply exec_straight_trans. eexact A. eapply exec_straight_one. 
  simpl. eauto. srp.
  split. Simplifs. 
  intuition Simplifs. 
Qed. 

(** Translation of arithmetic operations. *)

Ltac ArgsInv :=
  match goal with
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: match ?args with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct args eqn:?; ArgsInv
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H; ArgsInv
  | [ H: match _ with left _ => _ | right _ => assertion_failed end = OK _ |- _ ] => monadInv H; ArgsInv
  | [ H: match _ with true => _ | false => assertion_failed end = OK _ |- _ ] => monadInv H; ArgsInv
  | [ H: ireg_of _ = OK _ |- _ ] => progress (simpl in *; rewrite (ireg_of_eq _ _ H) in *; ArgsInv)
  | [ H: freg_of _ = OK _ |- _ ] => progress (simpl in *; rewrite (freg_of_eq _ _ H) in *; ArgsInv)
  | _ => idtac
  end.

(* Ltac TranslOp := *)
(*   econstructor; split; *)
(*    [ eapply exec_straight_one; [ simpl; eauto  | eauto  |  apply nextinstr_pc; auto] *)
(*    | split; [ Simplifs | intros; Simplifs ] ]. *)

(* Definition size_op (op: operation) (r: list mreg) (res: mreg) : Z := *)
(*   match op with *)
(*     | (Ocast8signed | Ocast8unsigned *)
(*        | Ocast16signed | Ocast16unsigned) => *)
(*       match r with *)
(*           r::nil => *)
(*           match  ireg_of r with *)
(*               OK r => if low_ireg r then 1 else 2 *)
(*             | _ => 0 *)
(*           end *)
(*         | _ => 0 *)
(*       end *)
(*     | Oshrximm _ => 4 *)
(*     | Ocmp cond => match testcond_for_condition cond with *)
(*                         Cond_base _ => 1 *)
(*                       | _ => 3 *)
(*                     end + *)
(*                     match ireg_of res with *)
(*                         OK r => if low_ireg r then 1 else 2 *)
(*                       | _ => 1 *)
(*                     end *)
(*     | _  => 1 *)
(*   end. *)
                                                          

Lemma pos_add_pos:
  forall a b,
    0 <= a -> 0 <= b -> 
    0 <= a + b.
Proof. intros; omega. Qed.

Lemma transl_cond_length:
  forall c0 args x k c,
    transl_cond c0 args (mk_setcc (testcond_for_condition c0) x k) = OK c ->
    (length c - length (mk_setcc (testcond_for_condition c0) x k) = 1)%nat.
Proof.
  destruct c0 eqn:?; simpl; intros; ArgsInv;
  simpl; try (rewrite sn_minus_n; solve [auto]).
  destr; rewrite sn_minus_n; auto.
Qed.

Opaque plus.

Lemma transl_op_correct:
  forall op args res k c (rs: regset) m v b o
         (Npc: reg_ptr rs PC b o)
         (TR: transl_op op args res k = OK c)
         (EV: eval_operation ge (rs#ESP) op (map rs (map preg_of args)) = Some v),
    exists rs',
      exec_straight ge fn c rs m k rs' m
      /\ Val.lessdef v rs'#(preg_of res)
      /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r.
Proof.
  Transparent destroyed_by_op.
  intros.
  assert (SAME:
  (exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of res) = v
  /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r) ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef v rs'#(preg_of res)
  /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r).
  {
    intros [rs' [A [B C]]]. subst v. exists rs'; auto.
  } 
 
  Ltac TranslOp :=
    econstructor; split;
    [ eapply exec_straight_one; [simpl; eauto|srp]
    | split; [ Simplifs | intuition Simplifs]].

  destruct op; 
  simpl in TR; ArgsInv; simpl in EV; try (inv EV); try (apply SAME; TranslOp; fail).
- (* move *) 
  exploit mk_mov_correct; eauto. intros [rs2 [A [B C]]]. 
  apply SAME. exists rs2. eauto. 
- (* intconst *)
  apply SAME. destruct (Int.eq_dec i Int.zero). subst i.
  TranslOp. TranslOp.
- (* floatconst *)
  destr. TranslOp. subst; auto.
  TranslOp.
- (* singleconst *)
  apply SAME. destruct (Float32.eq_dec f Float32.zero). subst f. TranslOp. TranslOp.
- unfold Genv.symbol_address' in H0; revert H0; destr. inv H0.
  apply SAME. clear SAME.
  econstructor; split;
   [ eapply exec_straight_one; [ simpl; eauto  | srp ]
   | split].
  unfold Genv.symbol_address; rewrite Heqo0.
  eauto. unfold nextinstr_nf; eauto.
  srp. srp. rewrite undef_regs_other. srp. destr. intuition Simplifs.
  rewrite undef_regs_other. srp. simpl; intros.
  des r.
- (* cast8signed *)
  apply SAME. eapply mk_intconv_correct; eauto.
- (* cast8unsigned *)
  apply SAME. eapply mk_intconv_correct; eauto.
- (* cast16signed *)
  apply SAME. eapply mk_intconv_correct; eauto.
- (* cast16unsigned *)
  apply SAME. eapply mk_intconv_correct; eauto.
- (* mulhs *)
  apply SAME. TranslOp. destruct H1. Simplifs. 
- (* mulhu *)
  apply SAME. TranslOp. destruct H1. Simplifs. 
- (* div *)
  apply SAME. TranslOp.
  rewrite Pregmap.gso by des r. auto.
- (* divu *)
  apply SAME.
   TranslOp.
  rewrite Pregmap.gso by des r. auto.
(* - (* mod *) *)
(*   apply SAME. *)
(*   TranslOp. *)
(*   rewrite Pregmap.gso by des r. auto. *)
(* - (* modu *) *)
(*   apply SAME. *)
(*    TranslOp. *)
(*   rewrite Pregmap.gso by des r. auto. *)
- (* shrximm *)
  eapply mk_shrximm_correct; eauto.
- (* lea *)
  generalize (transl_addressing_mode_correct _ _ _ _ _ EQ H0).
  intros EA.
  TranslOp. 
(* - (* intoffloat *) *)
(*   apply SAME. TranslOp. rewrite H0; auto. *)
(* - (* floatofint *) *)
(*   apply SAME. TranslOp. rewrite H0; auto. *)
(* - (* intofsingle *) *)
(*   apply SAME. TranslOp. rewrite H0; auto. *)
(* - (* singleofint *) *)
(*   apply SAME. TranslOp. rewrite H0; auto. *)
- (* condition *)

  exploit transl_cond_correct. eexact Npc. eexact EQ0. intros [rs2 [be [P [Q [R S']]]]].
  exploit exec_straight_wfpc. eexact P. eexact Npc. intro A.
  exploit (mk_setcc_correct (testcond_for_condition c0) x). eexact A.
  intros [rs3 [S [T U]]].
  exists rs3. repSplit.
  + eapply exec_straight_trans. eexact P. eexact S.
  + unfold PregEq.t in H0.
    rewrite H0 in Q. inv Q. red; intros. rewrite T. rewrite R. auto.
  + intros. transitivity (rs2 r); auto.
Qed.

(** Translation of memory loads. *)

Lemma transl_load_correct:
  forall chunk addr args dest k c (rs: regset) m a v b o
         (Rpc: reg_ptr rs PC b o)
         (TL: transl_load chunk addr args dest k = OK c)
         (EVA: eval_addressing ge (rs#ESP) addr (map rs (map preg_of args)) = Some a)
         (LV: Mem.loadv chunk m a = Some v),
  exists rs',
    exec_straight ge fn c rs m k rs' m
    /\ rs'#(preg_of dest) = v
    /\ forall r, data_preg r = true -> r <> preg_of dest -> rs'#r = rs#r.
Proof.
  unfold transl_load; intros. monadInv TL.
  generalize (transl_addressing_mode_correct _ _ _ _ _ EQ EVA). intro EA.
  set (rs2 := nextinstr_nf (rs#(preg_of dest) <- v)).
  assert (exec_load ge chunk m x rs (preg_of dest) = Next rs2 m).
  {
    unfold exec_load.
    revert LV.  unfold Mem.loadv.
    generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ (mem_lessdef_refl m) EA).
    rewrite lessdef_val.
    destr. inv H. rewrite LV. auto. 
  }
  exists rs2. repSplit. 
  - destruct chunk; ArgsInv; eapply exec_straight_one; eauto; srp;
    rewrite undef_regs_other by destr; Simplifs.
  - unfold rs2. rewrite nextinstr_nf_inv1. Simplifs. apply preg_of_data.
  - intros. unfold rs2. Simplifs. 
Qed.

Lemma transl_store_correct:
  forall chunk addr args src k c (rs: regset) m a m' b o
         (Rpc: reg_ptr rs PC b o)
         (TS: transl_store chunk addr args src k = OK c)
         (EVA: eval_addressing ge (rs#ESP) addr (map rs (map preg_of args)) = Some a)
         (SV: Mem.storev chunk m a (rs (preg_of src)) = Some m'),
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, data_preg r = true -> preg_notin r (destroyed_by_store chunk addr) -> rs'#r = rs#r.
Proof.
  unfold transl_store; intros. monadInv TS. 
  generalize (transl_addressing_mode_correct _ _ _ _ _ EQ EVA); intro EA.
  assert (Mem.storev chunk m (eval_addrmode ge x rs) (rs (preg_of src)) = Some m').
  {
    rewrite <- SV.
    unfold Mem.storev in *.
    generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _  (mem_lessdef_refl m) EA).
    rewrite lessdef_val. repeat destr; inv H.
    auto.
  }
  destruct chunk; ArgsInv.
  - (* int8signed *)
    eapply mk_smallstore_correct; eauto.
    intros. simpl. unfold exec_store.
    unfold Mem.storev. destruct (Mem.mem_norm m0 _); auto.
    rewrite Mem.store_signed_unsigned_8; auto.
  - (* int8unsigned *)
    eapply mk_smallstore_correct; eauto.
  - (* int16signed *)
    econstructor; split.
    eapply exec_straight_one; eauto. simpl. unfold exec_store. 
    replace (Mem.storev Mint16unsigned m (eval_addrmode ge x rs) (rs x0))
    with (Mem.storev Mint16signed m (eval_addrmode ge x rs) (rs x0)).
    rewrite H. eauto.
    unfold Mem.storev. destruct (Mem.mem_norm m (eval_addrmode ge x rs)); auto. rewrite Mem.store_signed_unsigned_16; auto.
    srp.
    intros. Simplifs.
  - (* int16unsigned *)
    econstructor; split.
    eapply exec_straight_one. simpl. unfold exec_store. rewrite H. eauto.
    srp. 
    intros. Simplifs.
  - (* int32 *)
    econstructor; split.
    eapply exec_straight_one; eauto. simpl. unfold exec_store. rewrite H. eauto.
    srp. 
    intros. Simplifs.
  - (* float32 *)
    econstructor; split.
    eapply exec_straight_one; eauto. simpl. unfold exec_store. rewrite H. eauto.
    srp. 
    intros. Simplifs.
  - (* float32 *)
    econstructor; split.
    eapply exec_straight_one; eauto. simpl. unfold exec_store. rewrite H. eauto.
    srp. 
    intros. Simplifs.
Qed.

End CONSTRUCTORS.


