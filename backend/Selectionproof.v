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

(** Correctness of instruction selection *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Values.
Require Import NormaliseSpec.
Require Import ExprEval.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Switch.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.
Require Import SelectDiv.
Require Import SelectLong.
Require Import Selection.
Require Import SelectOpproof.
Require Import SelectDivproof.
Require Import SelectLongproof.
Require Import SameEvalCmp.
Require Import Values_symbolictype.
Require Import Values_symbolic.
Require Import Floats.
Require Import IntFacts.
Require Import MemRel.
Local Open Scope cminorsel_scope.
Local Open Scope error_monad_scope.


(** * Correctness of the instruction selection functions for expressions *)

Section PRESERVATION.

Variable prog: Cminor.program.
Variable tprog: CminorSel.program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Variable hf: helper_functions.
Hypothesis HELPERS: i64_helpers_correct tge hf.
Hypothesis TRANSFPROG: transform_partial_program (sel_fundef hf ge) prog = OK tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros. eapply Genv.find_symbol_transf_partial; eauto. 
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: Cminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ sel_fundef hf ge f = OK tf.
Proof.  
  intros. eapply Genv.find_funct_ptr_transf_partial; eauto.
Qed.

Lemma functions_translated:
  forall (m:mem) (v v': expr_sym) (f: Cminor.fundef),
  Genv.find_funct m ge v = Some f ->
  Val.lessdef v v' ->
  exists tf, Genv.find_funct m tge v' = Some tf /\ sel_fundef hf ge f = OK tf.
Proof.  
  intros.
  unfold Genv.find_funct in *.
  eapply (Mem.lessdef_eqm m) in H0.
  unfold Mem.mem_norm in *. inv H0.
  repeat destr.
  eapply Genv.find_funct_ptr_transf_partial2; eauto.
  rewrite <- H2 in H. congruence.
Qed.

Lemma sig_function_translated:
  forall f tf, sel_fundef hf ge f = OK tf -> funsig tf = Cminor.funsig f.
Proof.
  intros. destruct f; monadInv H; auto. monadInv EQ. auto. 
Qed.

Lemma stackspace_function_translated:
  forall f tf, sel_function hf ge f = OK tf -> fn_stackspace tf = Cminor.fn_stackspace f.
Proof.
  intros. monadInv H. auto. 
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros; eapply Genv.find_var_info_transf_partial; eauto.
Qed.

Lemma helper_implements_preserved:
  forall id sg vargs vres,
  helper_implements ge id sg vargs vres ->
  helper_implements tge id sg vargs vres.
Proof.
  intros. destruct H as (b & ef & A & B & C & D).
  exploit function_ptr_translated; eauto. simpl. intros (tf & P & Q). inv Q. 
  exists b; exists ef. 
  split. rewrite symbols_preserved. auto.
  split. auto.
  split. auto.
  intros. eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
Qed.

Lemma builtin_implements_preserved:
  forall id sg vargs vres,
  builtin_implements ge id sg vargs vres ->
  builtin_implements tge id sg vargs vres.
Proof.
  unfold builtin_implements; intros.
  eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
Qed.

Lemma helpers_correct_preserved:
  forall h, i64_helpers_correct ge h -> i64_helpers_correct tge h.
Proof.
  unfold i64_helpers_correct; intros.
  repeat (match goal with [ H: _ /\ _ |- _ /\ _ ] => destruct H; split end);
  intros; try (eapply helper_implements_preserved; eauto);
  try (eapply builtin_implements_preserved; eauto).
Qed.

Section CMCONSTR.

Variable sp: expr_sym.
Variable e: env.
Variable m: mem.


Lemma eval_condexpr_of_expr:
  forall a le v i,
    eval_expr tge sp e m le a v ->
    Mem.mem_norm m v = Vint i ->
    eval_condexpr tge sp e m le (condexpr_of_expr a) (negb (Int.eq i Int.zero)).
Proof.
  intros until a. functional induction (condexpr_of_expr a); intros.
  - (* compare *)
    inv H. econstructor; eauto. 
  - (* condition *)
    inv H.
    econstructor; eauto.
    destruct va; eauto.
  - (* let *)
    inv H. econstructor; eauto.
  - (* default *)
    assert (Mem.mem_norm m (Val.cmpu_bool Cne v (Eval (Vint Int.zero))) =
            (if negb (Int.eq i Int.zero) then Vtrue else Vfalse)).
    {
      generalize (Mem.norm_correct m v).
      rewrite H0. clear.
      intro A; inv A.
      generalize (Mem.norm_complete
                    m (Val.cmpu_bool Cne v (Eval (Vint Int.zero)))
                    (if negb (Int.eq i Int.zero) then Vtrue else Vfalse)).
      intro A; trim A.
      - constructor; try red; intros; eauto.
        + specialize (eval_ok_m _ em Pcm). simpl in eval_ok_m.
          inv eval_ok_m.
          simpl. rewrite <- H1. simpl.
          destr; auto.
      - destr; inv A; eauto.
    }
    replace (negb (Int.eq i Int.zero))
    with (negb (Int.eq (if negb (Int.eq i Int.zero) then Int.one else Int.zero) Int.zero)) by (destr; auto).
    econstructor.
    constructor. eauto. constructor. 
    simpl. eauto. rewrite H1.
    destr; auto.
Qed.

Lemma eval_load:
  forall le a v chunk v',
  eval_expr tge sp e m le a v ->
  Mem.loadv chunk m v = Some v' ->
  eval_expr tge sp e m le (load chunk a) v'.
Proof.
  intros.
  unfold load.
  generalize H0.
  unfold Mem.loadv; destr.
  exploit (fun m e v => Mem.norm_type m e v Tint). eauto. congruence. simpl; auto.
  simpl; intro.
  generalize (eval_addressing _ _ _ _ _ chunk _ _ H H2).
  destruct (addressing chunk a). intros [vl [v'0 [EV [EQ SE]]]]. 
  eapply eval_Eload; eauto.
  unfold Mem.loadv.
  generalize (Mem.lessdef_eqm m  _ _ SE). rewrite Heqv0. intro A; inv A. auto.
Qed.

(* Variable needed_stackspace: ident -> nat . *)

Lemma eval_store:
  forall needed_stackspace  chunk a1 a2 v1 v2 f k m',
  eval_expr tge sp e m nil a1 v1 ->
  eval_expr tge sp e m nil a2 v2 ->
  Mem.storev chunk m v1 v2 = Some m' ->
  step tge needed_stackspace  (State f (store chunk a1 a2) k sp e m)
        E0 (State f Sskip k sp e m').
Proof.
  intros.
  generalize H1; unfold Mem.storev. destr. 
  unfold store. 
  exploit (fun m e v => Mem.norm_type m e v Tint). eauto. congruence. simpl; auto.
  simpl; intro WT.
  generalize (eval_addressing _ _ _ _ _ chunk _ _ H WT).
  destruct (addressing chunk a1). intros [vl [v' [EV [EQ SE]]]]. 
  eapply step_store; eauto.
  unfold Mem.storev.
  generalize (Mem.lessdef_eqm m _ _ SE). rewrite Heqv. intro A; inv A. auto.
Qed.

Ltac UseHelper :=
  red in HELPERS;
  repeat (eauto; match goal with | [ H: _ /\ _ |- _ ] => destruct H end).


Lemma eval_intuoffloat:
  forall le a1 v1
    (EVAL : eval_expr tge sp e m le a1 v1),
   exists v',
     eval_expr tge sp e m le (intuoffloat hf a1) v' /\
     Val.lessdef (Val.intuoffloat v1) v'.
Proof.
  intros; unfold intuoffloat. econstructor; split. 
  eapply eval_helper_1; eauto.
  UseHelper.
  auto.
Qed.

Lemma eval_floatofintu:
  forall le a1 v1
    (EVAL : eval_expr tge sp e m le a1 v1),
   exists v',
     eval_expr tge sp e m le (floatofintu hf a1) v' /\
     Val.lessdef (Val.floatofintu v1) v'.
Proof.
  intros; unfold floatofintu. econstructor; split. 
  eapply eval_helper_1; eauto. UseHelper.
  auto.
Qed.


Lemma eval_intuofsingle:
  forall le a1 v1
    (EVAL : eval_expr tge sp e m le a1 v1),
   exists v',
     eval_expr tge sp e m le (intuofsingle hf a1) v' /\
     Val.lessdef (Val.intuofsingle v1) v'.
Proof.
  intros; unfold intuofsingle, intuoffloat, floatofsingle.

  eexists; split.
  eapply eval_helper_1; eauto.
  repeat (econstructor; simpl; eauto).
  UseHelper.
  unfold Val.intuofsingle, Val.intuoffloat, Val.floatofsingle.
  red; intros; simpl; unfold convert_t.
  seval; simpl; auto.
  change (Float.of_single f) with (Float32.to_double f).
  des (Float32.to_intu f); try constructor.
  exploit Float32.to_intu_double; eauto. intro.
  rewrite H. simpl. auto.
Qed.

Lemma eval_singleofintu:
  forall le a1 v1
    (EVAL : eval_expr tge sp e m le a1 v1),
   exists v',
     eval_expr tge sp e m le (singleofintu hf a1) v' /\
     Val.lessdef (Val.singleofintu v1) v'.
Proof.
  intros; unfold singleofintu. destr.
  InvEval.
  eexists; split. repeat (econstructor; simpl; eauto).
  ld. unfold convert_t. simpl.
  rewrite Float32.of_intu_double. auto.
  exploit eval_floatofintu. eauto.
  intros (v & A & B).
  eexists; split. repeat ( econstructor; simpl; eauto).
  unfold Val.singleoffloat.
  ldt. ld.
Qed.


(** Correctness of instruction selection for operators *)

Lemma eval_sel_unop:
  forall le op a1 v1 v,
  eval_expr tge sp e m le a1 v1 ->
  eval_unop op v1 = Some v ->
  exists v', eval_expr tge sp e m le (sel_unop hf op a1) v' /\ Val.lessdef v v'.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_cast8unsigned; auto.
  apply eval_cast8signed; auto.
  apply eval_cast16unsigned; auto.
  apply eval_cast16signed; auto.
  apply eval_negint; auto.
  apply eval_notint; auto.
  apply eval_negf; auto.
  apply eval_absf; auto.
  apply eval_negfs; auto.
  apply eval_absfs; auto.
  apply eval_singleoffloat; auto.
  apply eval_floatofsingle; auto.
  eapply eval_intoffloat; eauto.
  eapply eval_intuoffloat; eauto.
  eapply eval_floatofint; eauto.
  eapply eval_floatofintu; eauto.
  eapply eval_intofsingle; eauto.
  eapply eval_intuofsingle; eauto.
  eapply eval_singleofint; eauto.
  eapply eval_singleofintu; eauto.
  eapply eval_negl; eauto.
  eapply eval_notl; eauto.
  eapply eval_intoflong; eauto.
  eapply eval_longofint; eauto.
  eapply eval_longofintu; eauto.
  eapply eval_longoffloat; eauto.
  eapply eval_longuoffloat; eauto.
  eapply eval_floatoflong; eauto.
  eapply eval_floatoflongu; eauto.
  eapply eval_longofsingle; eauto.
  eapply eval_longuofsingle; eauto.
  eapply eval_singleoflong; eauto.
  eapply eval_singleoflongu; eauto.
Qed.

Lemma eval_sel_binop:
  forall le op a1 a2 v1 v2 v,
  eval_expr tge sp e m le a1 v1 ->
  eval_expr tge sp e m le a2 v2 ->
  eval_binop op v1 v2 m = Some v ->
  exists v', eval_expr tge sp e m le (sel_binop hf op a1 a2) v' /\ Val.lessdef v v'.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_add; auto.
  apply eval_sub; auto.
  apply eval_mul; auto.
  eapply eval_divs; eauto.
  eapply eval_divu; eauto.
  eapply eval_mods; eauto.
  eapply eval_modu; eauto.
  apply eval_and; auto.
  apply eval_or; auto.
  apply eval_xor; auto.
  apply eval_shl; auto.
  apply eval_shr; auto.
  apply eval_shru; auto.
  apply eval_addf; auto.
  apply eval_subf; auto.
  apply eval_mulf; auto.
  apply eval_divf; auto.
  apply eval_addfs; auto.
  apply eval_subfs; auto.
  apply eval_mulfs; auto.
  apply eval_divfs; auto.
  eapply eval_addl; eauto.
  eapply eval_subl; eauto.
  eapply eval_mull; eauto.
  eapply eval_divl; eauto.
  eapply eval_divlu; eauto.
  eapply eval_modl; eauto.
  eapply eval_modlu; eauto.
  eapply eval_andl; eauto.
  eapply eval_orl; eauto.
  eapply eval_xorl; eauto.
  eapply eval_shll; eauto.
  eapply eval_shrl; eauto.
  eapply eval_shrlu; eauto.
  apply eval_comp; auto.
  apply eval_compu; auto.
  apply eval_compf; auto.
  apply eval_compfs; auto.
  eapply eval_cmpl; eauto.
  eapply eval_cmplu; eauto.
Qed.

End CMCONSTR.

(** Recognition of calls to built-in functions *)

Lemma expr_is_addrof_ident_correct:
  forall e id,
  expr_is_addrof_ident e = Some id ->
  e = Cminor.Econst (Cminor.Oaddrsymbol id Int.zero).
Proof.
  intros e id. unfold expr_is_addrof_ident. 
  destruct e; try congruence.
  destruct c; try congruence.
  predSpec Int.eq Int.eq_spec i0 Int.zero; congruence.
Qed.


Lemma classify_call_correct:
  forall sp e m a v fd,
  Cminor.eval_expr ge sp e m a v ->
  Genv.find_funct m ge v = Some fd ->
  match classify_call ge a with
  | Call_default => True
  | Call_imm id => exists b, Genv.find_symbol ge id = Some b /\ v = Eval (Vptr b Int.zero)
  | Call_builtin ef => fd = External ef
  end.
Proof.
  unfold classify_call; intros. 
  destruct (expr_is_addrof_ident a) as [id|] eqn:?; auto.
  exploit expr_is_addrof_ident_correct; eauto. intros EQ; subst a.
  inv H. inv H2. 
  destruct (Genv.find_symbol ge id) as [b|] eqn:?; try discriminate. inv H1.
  (* rewrite Genv.find_funct_find_funct_ptr in H0.  *)
  unfold Genv.find_funct in H0.
  rewrite Mem.norm_val in H0.
  rewrite pred_dec_true in H0; auto.
  rewrite H0. 
  destruct fd. exists b; auto. 
  destruct (ef_inline e0). auto. exists b; auto.
Qed.


Lemma classify_call_correct_free:
  forall sp e m a v fd m' m'' sz
    (EXPR: Cminor.eval_expr ge sp e m a v)
    (FREE: Mem.free m sp 0 sz = Some m')
    n (REL: MemReserve.release_boxes m' n = Some m'')
    (FF: Genv.find_funct m'' ge v = Some fd),
    match classify_call ge a with
    | Call_default => True
    | Call_imm id => exists b, Genv.find_symbol ge id = Some b /\ v = Eval (Vptr b Int.zero)
    | Call_builtin ef => fd = External ef
    end.
Proof.
  unfold classify_call; intros. 
  destruct (expr_is_addrof_ident a) as [id|] eqn:?; auto.
  exploit expr_is_addrof_ident_correct; eauto. intros EQ; subst a.
  inv EXPR. inv H0.
  destruct (Genv.find_symbol ge id) as [b|] eqn:?; try discriminate. inv H1.
  unfold Genv.find_funct in FF.
  rewrite Mem.norm_val in FF.
  rewrite pred_dec_true in FF; auto.
  rewrite FF. 
  destruct fd. exists b; auto. 
  destruct (ef_inline e0). auto. exists b; auto.
Qed.


(** Translation of [switch] statements *)



Inductive Rint: mem -> Z -> expr_sym -> Prop :=
| Rint_intro: forall m n e, Mem.mem_norm m e = Vint n ->
                          Rint m (Int.unsigned n) e.

Inductive Rlong: mem -> Z -> expr_sym -> Prop :=
| Rlong_intro: forall m n e,
                 Mem.mem_norm m e = Vlong n ->
                 Rlong m (Int64.unsigned n) e.

Section SEL_SWITCH.

Variable make_cmp_eq: expr -> Z -> expr.
Variable make_cmp_ltu: expr -> Z -> expr.
Variable make_sub: expr -> Z -> expr.
Variable make_to_int: expr -> expr.
Variable modulus: Z.
Variable R: mem -> Z -> expr_sym -> Prop.

Hypothesis eval_make_cmp_eq: forall sp e m le a v i n,
  eval_expr tge sp e m le a v -> R m i v -> 0 <= n < modulus ->
  exists vn,
    eval_expr tge sp e m le (make_cmp_eq a n) vn /\
    Mem.mem_norm m vn = Values.Val.of_bool (zeq i n).
Hypothesis eval_make_cmp_ltu: forall sp e m le a v i n,
  eval_expr tge sp e m le a v -> R m i v -> 0 <= n < modulus ->
  exists vn,
    eval_expr tge sp e m le (make_cmp_ltu a n) vn /\
    Mem.mem_norm m vn = Values.Val.of_bool (zlt i n).

Hypothesis eval_make_sub: forall sp e m le a v i n,
  eval_expr tge sp e m le a v -> R m i v -> 0 <= n < modulus ->
  exists v', eval_expr tge sp e m le (make_sub a n) v' /\ R m ((i - n) mod modulus) v'.

Hypothesis eval_make_to_int: forall sp e m le a v i,
  eval_expr tge sp e m le a v -> R m i v ->
  exists v', eval_expr tge sp e m le (make_to_int a) v' /\ Rint m (i mod Int.modulus) v'.

Lemma sel_switch_correct_rec:
  forall sp e m varg i x,
  R m i varg ->
  forall t arg le,
  wf_comptree modulus t ->
  nth_error le arg = Some varg ->
  comptree_match modulus i t = Some x ->
  eval_exitexpr tge sp e m le (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg t) x.
Proof.
  intros until x; intros Ri. induction t; simpl; intros until le; intros WF ARG MATCH.
- (* base case *)
  inv MATCH. constructor. 
- (* eq test *)
  inv WF. 
  assert (exists vn,
            eval_expr tge sp e m le (make_cmp_eq (Eletvar arg) key) vn /\
            Mem.mem_norm m vn = Values.Val.of_bool (zeq i key)).
  { eapply eval_make_cmp_eq; eauto. constructor; auto. }
  destruct H as [vn [Y Z]].  
  exploit (eval_condexpr_of_expr sp e m). eexact Y.
  instantiate (1:=if zeq i key then Int.one else Int.zero); destr; auto.
  destruct (zeq i key); simpl.
  + inv MATCH. econstructor; eauto. rewrite Int.eq_false by discriminate.
    simpl. constructor.
  + rewrite Int.eq_true. simpl. intro.
    econstructor. eauto. simpl. eapply IHt; eauto.
- (* lt test *)
  inv WF.
  assert (exists vn,
            eval_expr tge sp e m le (make_cmp_ltu (Eletvar arg) key) vn /\
            Mem.mem_norm m vn = (Values.Val.of_bool (zlt i key))).
  { eapply eval_make_cmp_ltu; eauto. constructor; auto. }
  destruct H as [vn [Y Z]].
  exploit (eval_condexpr_of_expr).  eexact Y. 
  rewrite Z. instantiate (1:= if zlt i key then Int.one else Int.zero); destr; auto.
  intro. eapply eval_XEcondition; eauto. 
  destruct (zlt i key); simpl. 
  + rewrite Int.eq_false in * by discriminate. simpl in *. eapply IHt1; eauto.
  + rewrite Int.eq_true in *; simpl in *. eapply IHt2; eauto.
- (* jump table *)
  inv WF.
  exploit (eval_make_sub sp e m le). eapply eval_Eletvar. eauto. eauto.
  instantiate (1 := ofs). auto.
  intros (v' & A & B).
  set (i' := (i - ofs) mod modulus) in *.
  assert (exists vn,
            eval_expr tge sp e m (v' :: le) (make_cmp_ltu (Eletvar O) sz) vn /\
            Mem.mem_norm m vn =  (Values.Val.of_bool (zlt i' sz))).
  { eapply eval_make_cmp_ltu; eauto. constructor; auto. }
  destruct H as [vn [Y Z]].
  econstructor. eauto. 
  exploit (eval_condexpr_of_expr). eexact Y.
  instantiate(1:= if zlt i' sz then Int.one else Int.zero); destr; auto.
  intro. eapply eval_XEcondition; eauto. 
  destruct (zlt i' sz); simpl.
  + rewrite Int.eq_false in * by discriminate. simpl in *.
    exploit (eval_make_to_int sp e m (v' :: le) (Eletvar O)).
    constructor. simpl; eauto. eauto. intros (v'' & E & F). inv F. 
    econstructor; eauto. congruence. 
  + rewrite Int.eq_true in *; simpl in *. eapply IHt; eauto.
Qed.

Lemma sel_switch_correct:
  forall dfl cases arg sp e m varg i t le,
  validate_switch modulus dfl cases t = true ->
  eval_expr tge sp e m le arg varg ->
  R m i varg ->
  0 <= i < modulus ->
  eval_exitexpr tge sp e m le
     (XElet arg (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int O t))
     (switch_target i dfl cases).
Proof.
  intros. exploit (validate_switch_correct modulus); eauto. omega. intros [A B].
  econstructor. eauto. eapply sel_switch_correct_rec; eauto.
Qed.

End SEL_SWITCH.
Require Import Psatz.
Lemma sel_switch_int_correct:
  forall dfl cases arg sp e m i vi t le,
  validate_switch Int.modulus dfl cases t = true ->
  eval_expr tge sp e m le arg vi ->
  Mem.mem_norm m vi = Vint i ->
  eval_exitexpr tge sp e m le (XElet arg (sel_switch_int O t)) (switch_target (Int.unsigned i) dfl cases).
Proof.
  assert (INTCONST: forall n sp e m le, 
            eval_expr tge sp e m le (Eop (Ointconst n) Enil) (Eval (Vint n))).
  { intros. econstructor. constructor. auto. } 
  intros. eapply sel_switch_correct with (R := Rint); eauto.
 - intros until n; intros EVAL R RANGE.
   exploit eval_comp. eexact EVAL. apply (INTCONST (Int.repr n)).
   instantiate (1 := Ceq). intros (vb & A & B). 
   inv R.
   exists vb; split; eauto.
   apply Mem.eq_norm; try solve [destruct zeq; simpl; auto; discriminate].
   constructor; red; simpl; auto; intros.
   eapply Mem.norm_ld in H2; eauto.
   simpl in H2; inv H2.
   specialize (B cm em). simpl in B. rewrite <- H5 in B. simpl in B. 
   revert B.
   unfold Int.eq. rewrite  Int.unsigned_repr. des (zeq (Int.unsigned n0) n).
   unfold Int.max_unsigned; lia.
- intros until n; intros EVAL R RANGE.
  exploit eval_compu. eexact EVAL. apply (INTCONST (Int.repr n)).  
  instantiate (1 := Clt). intros (vb & A & B). 
  inv R. eexists; split; eauto.
  apply Mem.eq_norm; try constructor; red; simpl; auto; intros; try solve [destruct zlt; simpl; auto; discriminate].
   intros. eapply Mem.norm_ld in H2; eauto.
   simpl in H2; inv H2.
   specialize (B cm em). simpl in B. rewrite <- H5 in B. simpl in B. 
   revert B.
   unfold Int.ltu. rewrite  Int.unsigned_repr. des (zlt (Int.unsigned n0) n).
   unfold Int.max_unsigned; lia.  
- intros until n; intros EVAL R RANGE.
  exploit eval_sub. eexact EVAL. apply (INTCONST (Int.repr n)).
  intros (vb & A & B).
  inv R.  econstructor; split; eauto. 
  replace ((Int.unsigned n0 - n) mod Int.modulus)
     with (Int.unsigned (Int.sub n0 (Int.repr n))).
  constructor.
   apply Mem.eq_norm;   try constructor; red; simpl; auto; intros; try solve [simpl; auto; discriminate].
   intros. eapply Mem.norm_ld in H2; eauto.
   simpl in H2; inv H2.
   specialize (B cm em). simpl in B. rewrite <- H5 in B. simpl in B. 
   revert B. simpl; auto.
  unfold Int.sub. rewrite Int.unsigned_repr_eq. f_equal. f_equal. 
  apply Int.unsigned_repr. unfold Int.max_unsigned; lia.
- intros until i0; intros EVAL R. exists v; split; auto. 
  inv R. rewrite Zmod_small by (apply Int.unsigned_range). constructor. auto.
- constructor. auto.
- apply Int.unsigned_range.
Qed.

Lemma sel_switch_long_correct:
  forall dfl cases arg sp e m i vi t le,
  validate_switch Int64.modulus dfl cases t = true ->
  eval_expr tge sp e m le arg vi ->
  Mem.mem_norm m vi = Vlong i ->
  eval_exitexpr tge sp e m le (XElet arg (sel_switch_long hf O t)) (switch_target (Int64.unsigned i) dfl cases).
Proof.
  intros. eapply sel_switch_correct with (R := Rlong); eauto.
  - intros until n; intros EVAL R RANGE.
    destruct (eval_longconst tge sp0 e0 m0 le0 (Int64.repr n)) as [v' [A B]].
    exploit eval_cmpl. eexact EVAL. eexact A.
    instantiate (1:=Ceq).
    intros (v0 & C & D). eexists; split; eauto.
    inv R. 
    apply Mem.eq_norm;   try constructor; red; simpl; auto; try intros alloc em Pcm; try solve [destruct zeq; simpl; auto; discriminate].
    intros. eapply Mem.norm_ld in H2; eauto.
    simpl in H2; inv H2.
    specialize (D alloc em). simpl in D. rewrite <- H5 in D.
    destr. rewrite B in D.
    simpl in D. 
    revert D.
    unfold Int64.eq. rewrite  Int64.unsigned_repr. des (zeq (Int64.unsigned n0) n).
    unfold Int64.max_unsigned; lia.
  - intros until n; intros EVAL R RANGE.
    destruct (eval_longconst tge sp0 e0 m0 le0 (Int64.repr n)) as [v' [A B]].
    exploit eval_cmplu. eexact EVAL. eexact A. 
    intros (v0 & C & D). eexists; split; eauto.
    inv R.
    apply Mem.eq_norm;  try constructor; red; simpl; auto; try intros alloc em Pcm; try solve [destruct zlt; simpl; auto; discriminate].
    intros. eapply Mem.norm_ld in H2; eauto.
    simpl in H2; inv H2.
    specialize (D alloc em). simpl in D. rewrite <- H5 in D.
    destr. rewrite B in D.
    simpl in D. 
    revert D.
    unfold Int64.ltu. rewrite  Int64.unsigned_repr. des (zlt (Int64.unsigned n0) n).
    unfold Int64.max_unsigned; lia.
  - intros until n; intros EVAL R RANGE.
    destruct (eval_longconst tge sp0 e0 m0 le0 (Int64.repr n)) as [v' [A B]].
    exploit eval_subl. eexact HELPERS. eexact EVAL. eexact A.
    intros (vb & C & D). eexists; split; eauto.
    inv R. 
    replace ((Int64.unsigned n0 - n) mod Int64.modulus)
    with (Int64.unsigned (Int64.sub n0 (Int64.repr n))).
    constructor.
    apply Mem.eq_norm;  try constructor; red; simpl; auto; try intros alloc em Pcm; try solve [simpl; auto; discriminate].
    intros. eapply Mem.norm_ld in H2; eauto.
    simpl in H2; inv H2.
    specialize (D alloc em). simpl in D. rewrite <- H5 in D.
    destr. rewrite B in D.
    simpl in D.  auto.
    unfold Int64.sub. rewrite Int64.unsigned_repr_eq. f_equal. f_equal. 
    apply Int64.unsigned_repr. unfold Int64.max_unsigned; lia.
  - intros until i0; intros EVAL R. 
    exploit eval_lowlong. eexact EVAL.
    intros (vb & A & B). eexists; split; eauto.
    inv R.
    replace (Int64.unsigned n mod Int.modulus) with (Int.unsigned (Int64.loword n)).
    constructor.     apply Mem.eq_norm;  try constructor; red; simpl; auto; try intros alloc em Pcm; try solve [simpl; auto; discriminate].
    intros. eapply Mem.norm_ld in H2; eauto.
    simpl in H2; inv H2.
    specialize (B alloc em). simpl in B. rewrite <- H5 in B. auto.
    unfold Int64.loword. apply Int.unsigned_repr_eq. 
  - constructor.  auto.
  - apply Int64.unsigned_range.
Qed.

(** Compatibility of evaluation functions with the "less defined than" relation. *)

Ltac TrivialExists :=
  match goal with
  | [ |- exists v, Some ?x = Some v /\ _ ] => exists x; split; auto
  | _ => idtac
  end.

Lemma eval_unop_lessdef:
  forall op v1 v1' v,
  eval_unop op v1 = Some v -> Val.lessdef v1 v1' ->
  exists v', eval_unop op v1' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until v; intros EV LD.
  destruct op; simpl in *; inv EV; TrivialExists;
  repeat ((apply Val.lessdef_unop; auto)
            ||
            (apply Val.lessdef_binop; auto)).
Qed.

Lemma eval_binop_lessdef:
  forall op v1 v1' v2 v2' v m m',
  eval_binop op v1 v2 m = Some v -> 
  Val.lessdef v1 v1' -> Val.lessdef v2 v2' ->
  exists v', eval_binop op v1' v2' m' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until m'; intros EV LD1 LD2.
  destruct op; destruct v1'; simpl in *; inv EV; TrivialExists;
    repeat ((apply Val.lessdef_unop; auto)
            ||
            (apply Val.lessdef_binop; auto)).
Qed.

(** * Semantic preservation for instruction selection. *)

(** Relationship between the local environments. *)

Definition env_lessdef (e1 e2: env) : Prop :=
  forall id v1, e1!id = Some v1 -> exists v2, e2!id = Some v2 /\ Val.lessdef v1 v2.

Lemma set_var_lessdef:
  forall e1 e2 id v1 v2,
  env_lessdef e1 e2 -> Val.lessdef v1 v2 ->
  env_lessdef (PTree.set id v1 e1) (PTree.set id v2 e2).
Proof.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id); eauto.
  inv H1. eauto.
Qed.

Lemma env_lessdef_refl:
  forall e,
    env_lessdef e e.
Proof.
  red; intros.
  eexists; split; eauto. 
Qed.

Lemma set_params_lessdef:
  forall il vl1 vl2, 
    Val.lessdef_list vl1 vl2 ->
    env_lessdef (set_params vl1 il) (set_params vl2 il).
Proof.
  induction il; simpl; intros.
  - red; intros. rewrite PTree.gempty in H0; congruence.
  - inv H; apply set_var_lessdef; auto.
Qed.

Lemma set_locals_lessdef:
  forall e1 e2, env_lessdef e1 e2 ->
  forall il, env_lessdef (set_locals il e1) (set_locals il e2).
Proof.
  induction il; simpl. auto. apply set_var_lessdef; auto.
Qed.

(** Semantic preservation for expressions. *)


Lemma sel_expr_correct:
  forall sp e m a v
         (EXPR: Cminor.eval_expr ge sp e m a v),
    forall e' le m',
      env_lessdef e e' -> mem_lessdef m m' ->
      exists v',
        eval_expr tge (Eval (Vptr sp Int.zero)) e' m' le (sel_expr hf a) v' /\
        Val.lessdef v v'.
Proof.
  induction 1; intros; simpl.
  - (* Evar *)
    exploit H0; eauto. intros [v' [A B]]. exists v'; split; auto. constructor; auto.
  - (* Econst *)
    destruct cst; simpl in *; inv H. 
    + (exists (Eval (Vint i)); split; auto). econstructor. constructor. auto. 
    + (exists (Eval (Vfloat f)); split; auto). econstructor. constructor. auto. 
    + (exists (Eval (Vsingle f)); split; auto). econstructor. constructor. auto.
    + (exists (Val.longofwords (Eval (Vint (Int64.hiword i)))
                               (Eval (Vint (Int64.loword i))))); split.
      eapply eval_Eop. constructor. EvalOp. simpl; eauto. constructor. EvalOp. simpl; eauto.
      constructor. auto.
      red; intros; simpl; intros; seval; auto.
      rewrite Int64.ofwords_recompose. auto.
    + revert H3; destr. inv H3.
      rewrite <- symbols_preserved in Heqo. fold (Genv.symbol_address tge i i0).
      exploit (eval_addrsymbol tge (Eval (Vptr sp Int.zero)) e' m' le i i0 b).
      unfold Genv.symbol_address'. rewrite Heqo. eauto.
      intros [v [A B]]; eexists; split; eauto.
      red; intros; simpl. destr. rewrite B. simpl; auto. 
    + exploit eval_addrstack.
      intros [v [A B]].
      eexists; split; eauto.
      destr. red; intros. rewrite <- B.
      simpl.
      rewrite Int.add_zero. auto.
  - (* Eunop *)
    exploit IHEXPR; eauto. intros [v1' [A B]].
    exploit eval_unop_lessdef; eauto. intros [v' [C D]].
    exploit eval_sel_unop; eauto. intros [v'' [E F]].
    exists v''; split; eauto. eapply Val.lessdef_trans; eauto. 
  - (* Ebinop *)
    exploit IHEXPR1; eauto. intros [v1' [A B]].
    exploit IHEXPR2; eauto. intros [v2' [C D]].
    exploit eval_binop_lessdef; eauto. intros [v' [E F]].
    exploit eval_sel_binop. eexact A. eexact C.
    eauto. intros [v'' [P Q]].
    exists v''; split; eauto. eapply Val.lessdef_trans; eauto. 
  - (* Eload *)
    exploit IHEXPR; eauto. intros [vaddr' [A B]].
    exploit loadv_mem_rel; eauto. apply wf_mr_ld. intros [v' [C D]].
    exists v'; split; auto. eapply eval_load; eauto.
    revert C. unfold Mem.loadv.
    generalize (Mem.lessdef_eqm m' _ _ B).
    intro E; repeat destr; inv E. auto. 
Qed.

Lemma sel_exprlist_correct:
  forall sp e m a v,
    Cminor.eval_exprlist ge sp e m a v ->
    forall e' le m',
      env_lessdef e e' -> mem_lessdef m m' ->
      exists v',
        eval_exprlist tge (Eval (Vptr sp Int.zero)) e' m' le (sel_exprlist hf a) v' /\
        Val.lessdef_list  v v'.
Proof.
  induction 1; intros; simpl. 
  - (exists (@nil expr_sym); split; auto). constructor. 
  -  exploit sel_expr_correct; eauto. intros [v1' [A B]].
    exploit IHeval_exprlist; eauto. intros [vl' [C D]].
    exists (v1' :: vl'); split; auto. constructor; eauto.
Qed.

(** Semantic preservation for functions and statements. *)

Inductive match_cont: Cminor.cont -> CminorSel.cont -> Prop :=
  | match_cont_stop:
      match_cont Cminor.Kstop Kstop
  | match_cont_seq: forall s s' k k',
      sel_stmt hf ge s = OK s' ->
      match_cont k k' ->
      match_cont (Cminor.Kseq s k) (Kseq s' k')
  | match_cont_block: forall k k',
      match_cont k k' ->
      match_cont (Cminor.Kblock k) (Kblock k')
  | match_cont_call: forall id f sp e k f' e' k',
      sel_function hf ge f = OK f' ->
      match_cont k k' -> env_lessdef e e' ->
      match_cont (Cminor.Kcall id f sp e k) (Kcall id f' (Eval (Vptr sp Int.zero)) e' k').

Inductive match_states: Cminor.state -> CminorSel.state -> Prop :=
  | match_state: forall f f' s k s' k' sp e m e' m'
        (TF: sel_function hf ge f = OK f')
        (TS: sel_stmt hf ge s = OK s')
        (MC: match_cont k k')
        (LD: env_lessdef e e')
        (ME: mem_lessdef m m'),
      match_states
        (Cminor.State f s k sp e m)
        (State f' s' k' (Eval (Vptr sp Int.zero)) e' m')
  | match_callstate: forall f f' args args' k k' m m'
        (TF: sel_fundef hf ge f = OK f')
        (MC: match_cont k k')
        (LD: Val.lessdef_list args args')
        (ME: mem_lessdef m m'),
      match_states
        (Cminor.Callstate f args k m)
        (Callstate f' args' k' m')
  | match_returnstate: forall v v' k k' m m'
        (MC: match_cont k k')
        (LD: Val.lessdef v v')
        (ME: mem_lessdef m m'),
      match_states
        (Cminor.Returnstate v k m)
        (Returnstate v' k' m')
  | match_builtin_1: forall ef args args' optid f sp e k m al f' e' k' m'
        (TF: sel_function hf ge f = OK f')
        (MC: match_cont k k')
        (LDA: Val.lessdef_list args args')
        (LDE: env_lessdef e e')
        (ME: mem_lessdef m m')
        (EA: eval_exprlist tge (Eval (Vptr sp Int.zero)) e' m' nil al args'),
      match_states
        (Cminor.Callstate (External ef) args (Cminor.Kcall optid f sp e k) m)
        (State f' (Sbuiltin optid ef al) k' (Eval (Vptr sp Int.zero)) e' m')
  | match_builtin_2: forall v v' optid f sp e k m f' e' m' k'
        (TF: sel_function hf ge f = OK f')
        (MC: match_cont k k')
        (LDV: Val.lessdef v v')
        (LDE: env_lessdef e e')
        (ME: mem_lessdef m m'),
      match_states
        (Cminor.Returnstate v (Cminor.Kcall optid f sp e k) m)
        (State f' Sskip k' (Eval (Vptr sp Int.zero)) (set_optvar optid v' e') m').

Remark call_cont_commut:
  forall k k', match_cont k k' -> match_cont (Cminor.call_cont k) (call_cont k').
Proof.
  induction 1; simpl; auto. constructor. constructor; auto.
Qed.

Remark find_label_commut:
  forall lbl s k s' k',
  match_cont k k' ->
  sel_stmt hf ge s = OK s' ->
  match Cminor.find_label lbl s k, find_label lbl s' k' with
  | None, None => True
  | Some(s1, k1), Some(s1', k1') => sel_stmt hf ge s1 = OK s1' /\ match_cont k1 k1'
  | _, _ => False
  end.
Proof.
  induction s; intros until k'; simpl; intros MC SE; try (monadInv SE); simpl; auto.
  - (* store *)
    unfold store. destruct (addressing m (sel_expr hf e)); simpl; auto. 
  - (* call *)
    destruct (classify_call ge e); simpl; auto.
  - (* tailcall *)
    destruct (classify_call ge e); simpl; auto.
  - (* seq *)
    exploit (IHs1 (Cminor.Kseq s2 k)). constructor; eauto. eauto.  
    destruct (Cminor.find_label lbl s1 (Cminor.Kseq s2 k)) as [[sx kx] | ];
      destruct (find_label lbl x (Kseq x0 k')) as [[sy ky] | ];
      intuition. apply IHs2; auto.
  - (* ifthenelse *)
    exploit (IHs1 k); eauto. 
    destruct (Cminor.find_label lbl s1 k) as [[sx kx] | ];
      destruct (find_label lbl x k') as [[sy ky] | ];
      intuition. apply IHs2; auto.
  - (* loop *)
    apply IHs. constructor; auto. simpl; rewrite EQ; auto. auto.
  - (* block *)
    apply IHs. constructor; auto. auto.
  - (* switch *)
    destruct b. 
    destruct (validate_switch Int64.modulus n l (compile_switch Int64.modulus n l)); inv SE.
    simpl; auto.
    destruct (validate_switch Int.modulus n l (compile_switch Int.modulus n l)); inv SE.
    simpl; auto.
  - (* return *)
    destruct o; inv SE; simpl; auto.
  - (* label *)
    destruct (ident_eq lbl l). auto. apply IHs; auto.
Qed.

Definition measure (s: Cminor.state) : nat :=
  match s with
  | Cminor.Callstate _ _ _ _ => 0%nat
  | Cminor.State _ _ _ _ _ _ => 1%nat
  | Cminor.Returnstate _ _ _ => 2%nat
  end.

Lemma ld_list_ok:
  forall v v',
    Val.lessdef_list v v' ->
    list_forall2 Val.lessdef v v'.
Proof.
  induction 1; simpl; intros; repeat constructor; eauto.
Qed.

Variable needed_stackspace : ident -> nat .


Lemma sel_step_correct:
  forall S1 t S2,
    Cminor.step ge needed_stackspace  S1 t S2 ->
    forall T1,
      match_states S1 T1 ->
      (exists T2, step tge needed_stackspace  T1 t T2 /\ match_states S2 T2) \/
      (measure S2 < measure S1 /\ t = E0 /\ match_states S2 T1)%nat.
Proof.
  induction 1; intros T1 ME; inv ME; try (monadInv TS).
  - (* skip seq *)
    inv MC. left; econstructor; split. econstructor. constructor; auto.
  - (* skip block *)
    inv MC. left; econstructor; split. econstructor. constructor; auto.
  - (* skip call *)
    exploit free_mem_rel; eauto. intros [m2' [A B]].
    exploit MemReserve.release_boxes_rel; eauto. intros [m3' [C D]].
    left; econstructor; split. 
    econstructor. inv MC; simpl in H; simpl; auto. 
    erewrite stackspace_function_translated; eauto.
    replace (fn_id f') with (Cminor.fn_id f). eauto.
    monadInv TF. reflexivity.
    constructor; auto.
  - (* assign *)
    exploit sel_expr_correct; eauto. intros [v' [A B]].
    left; econstructor; split.
    econstructor; eauto.
    constructor; auto. apply set_var_lessdef; auto.
  - (* store *)
    exploit sel_expr_correct. eexact H. eauto. eauto.
    intros [vaddr' [A B]].
    exploit sel_expr_correct. eexact H0.
    eauto. eauto. intros [v' [C D]]. 
    exploit storev_rel; eauto. apply wf_mr_ld. apply wf_mr_norm_ld.
    intros [m2'0 [R S]].
    left; econstructor; split.
    eapply eval_store; eauto.
    constructor; auto.
  - (* Scall *)
    exploit sel_exprlist_correct; eauto. intros [vargs' [C D]].
    exploit classify_call_correct; eauto. 
    destruct (classify_call ge a) as [ | id | ef].
    + (* indirect *)
      exploit sel_expr_correct; eauto. intros [vf' [A B]].
      exploit functions_translated; eauto. intros (fd' & U & V).
      left; econstructor; split.
      econstructor; eauto. econstructor; eauto.
      erewrite <- Genv.find_funct_lessdef with (v:=vf') (v':=vf'); eauto. 
      apply sig_function_translated; auto.
      constructor; auto. constructor; auto.
    + (* direct *)
      intros [b [U V]]. 
      exploit functions_translated; eauto. intros (fd' & X & Y).
      left; econstructor; split.
      econstructor; eauto.
      subst vf. econstructor; eauto. rewrite symbols_preserved; eauto.
      erewrite <- Genv.find_funct_lessdef with (v:=vf) (v':=vf); eauto. 
      subst. auto.
      apply sig_function_translated; auto.
      constructor; auto. constructor; auto.
    + (* turned into Sbuiltin *)
      intros EQ. subst fd. 
      right; split. simpl. lia. split. auto. 
      econstructor; eauto.
  - (* Stailcall *)
    exploit free_mem_rel; eauto. intros [m2' [P Q]].
    exploit MemReserve.release_boxes_rel; eauto. intros [m3' [R S]].
    erewrite <- stackspace_function_translated in P by eauto.
    exploit sel_expr_correct; eauto.
    instantiate (1:=nil). intros [vf' [A B]].
    generalize (functions_translated _ _ _ _ H1 B). intros [tf [E F]].
    exploit sel_exprlist_correct; eauto. intros [vargs' [C D]].

    left; econstructor; split.
    + exploit classify_call_correct_free; eauto.
      destruct (classify_call ge a) as [ | id | ef]; intros. 
      * apply step_tailcall with (m':=m2') (vf:=vf'). econstructor; eauto.  eauto.
        erewrite Genv.find_funct_lessdef with (v:=vf') (v':=vf'); eauto.
        eapply sig_function_translated; eauto.
        auto.
        replace (fn_id f') with (Cminor.fn_id f). eauto.
        monadInv TF. reflexivity.
      * destruct H2 as [b [U V]]. subst vf.
        eapply (step_tailcall).
        constructor. rewrite symbols_preserved; eauto.
        apply C.
        eapply Genv.find_funct_lessdef. eauto. apply Val.lessdef_sym. apply B. congruence. eauto.
        apply (sig_function_translated _ _ F).
        eauto.
        replace (fn_id f') with (Cminor.fn_id f). eauto.
        monadInv TF. reflexivity.
      * eapply (fun eeos gff =>
                  step_tailcall _ needed_stackspace  _ _ _ _ _ _ _ _ _ _ _ _ _ 
                                eeos C gff (sig_function_translated _ _ F)
                                P); auto.
        econstructor; eauto. 
        erewrite <- Genv.find_funct_lessdef.  eauto.  eauto.
        apply Val.lessdef_refl. eauto.
        replace (fn_id f') with (Cminor.fn_id f). eauto.
        monadInv TF. reflexivity.
    + constructor; auto. apply call_cont_commut; auto.

  - (* Sbuiltin *)
    exploit sel_exprlist_correct; eauto. intros [vargs' [P Q]].
    exploit external_call_rel; eauto.
    apply wf_mr_ld.
    apply wf_mr_norm_ld.
    eapply ld_list_ok; eauto.
    intros [vres' [m2' [A [B C]]]].
    left; econstructor; split.
    econstructor. eauto. eapply external_call_symbols_preserved; eauto.
    exact symbols_preserved. exact varinfo_preserved.
    constructor; auto.
    destruct optid; simpl; auto. apply set_var_lessdef; auto.
  - (* Seq *)
    left; econstructor; split.
    constructor. constructor; auto. constructor; auto.
  - (* Sifthenelse *)
    exploit sel_expr_correct; eauto. intros [v' [A B]].
    generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ ME0 B). rewrite H0.
    rewrite lessdef_val.
    intro C; inv C.
    exploit eval_condexpr_of_expr. eexact A. eauto.  
    intro C.
    (* assert (exists i, Values.Val.of_bool (negb (Int.eq b Int.zero)) = Vint i). *)
    (* { *)
    (*   des (negb (Int.eq b Int.zero)); eexists; unfold Vtrue, Vfalse; eauto.  *)
    (* } *)
    (* destruct H1 as [ i H1]. *)
    left; exists (State f' (if negb (Int.eq b Int.zero) then x else x0) k' (Eval (Vptr sp Int.zero)) e' m'); split.
    econstructor; eauto. 
    constructor; auto.
    destruct (Int.eq b Int.zero); simpl in *; unfold Vtrue, Vfalse in *; simpl in *; auto.
  - (* Sloop *)
    left; econstructor; split. constructor. constructor; auto.
    constructor; auto. simpl; rewrite EQ; auto.
  - (* Sblock *)
    left; econstructor; split. constructor. constructor; auto. constructor; auto.
  - (* Sexit seq *)
    inv MC. left; econstructor; split. constructor. constructor; auto.
  - (* Sexit0 block *)
    inv MC. left; econstructor; split. constructor. constructor; auto.
  - (* SexitS block *)
    inv MC. left; econstructor; split. constructor. constructor; auto.
  - (* Sswitch *)
    inv H0; simpl in TS.
    + set (ct := compile_switch Int.modulus default cases) in *.
      destruct (validate_switch Int.modulus default cases ct) eqn:VALID; inv TS.
      exploit sel_expr_correct; eauto. intros [v' [A B]]. 
      left; econstructor; split. 
      econstructor. eapply sel_switch_int_correct; eauto.
      instantiate (1:=i).
      generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ ME0 B).
      rewrite lessdef_val. rewrite H1; intro C; inv C; auto.
      constructor; auto.
    + set (ct := compile_switch Int64.modulus default cases) in *.
      destruct (validate_switch Int64.modulus default cases ct) eqn:VALID; inv TS.
      exploit sel_expr_correct; eauto. intros [v' [A B]]. 
      left; econstructor; split.
      econstructor. eapply sel_switch_long_correct; eauto.
      instantiate (1:=i).
      generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ ME0 B).
      rewrite lessdef_val. rewrite H1; intro C; inv C; auto.
      constructor; auto.
  - (* Sreturn None *)
    exploit free_mem_rel; eauto. intros [m2' [P Q]].
    exploit MemReserve.release_boxes_rel; eauto. intros [m3' [R S]].
    erewrite <- stackspace_function_translated in P by eauto.
    left; econstructor; split. 
    econstructor. eauto.
    replace (fn_id f') with (Cminor.fn_id f). eauto.
    monadInv TF. reflexivity.
    constructor; auto. apply call_cont_commut; auto.
  - (* Sreturn Some *)
    exploit free_mem_rel; eauto. intros [m2' [P Q]].
    exploit MemReserve.release_boxes_rel; eauto. intros [m3' [R S]].
    erewrite <- stackspace_function_translated in P by eauto.
    exploit sel_expr_correct; eauto. intros [v' [A B]].
    left; econstructor; split. 
    econstructor; eauto.
    replace (fn_id f') with (Cminor.fn_id f). eauto.
    monadInv TF. reflexivity.
    constructor; auto. apply call_cont_commut; auto.
  - (* Slabel *)
    left; econstructor; split. constructor. constructor; auto.
  - (* Sgoto *)
    assert (sel_stmt hf ge (Cminor.fn_body f) = OK (fn_body f')).
    { monadInv TF; simpl; auto. }
    exploit (find_label_commut lbl (Cminor.fn_body f) (Cminor.call_cont k)).
    apply call_cont_commut; eauto. eauto.
    rewrite H. 
    destruct (find_label lbl (fn_body f') (call_cont k'0))
      as [[s'' k'']|] eqn:?; intros; try contradiction.
    destruct H1. 
    left; econstructor; split.
    econstructor; eauto. 
    constructor; auto.
  - (* internal function *)
    monadInv TF. generalize EQ; intros TF; monadInv TF.
    exploit alloc_mem_rel. eapply wf_mr_ld. eauto. eauto. 
    intros [m2' [A B]].
    destruct (MemReserve.reserve_boxes_rel _ _ _ B _ _ H0) as [m3' [C D]].
    left; econstructor; split.
    econstructor; simpl; eauto.    
    simpl. 
    constructor; simpl; auto. apply set_locals_lessdef. apply set_params_lessdef; auto.
  - (* external call *)
    monadInv TF.
    exploit external_call_rel; eauto.
    apply wf_mr_ld.
    apply wf_mr_norm_ld.
    eapply ld_list_ok; eauto.
    intros [vres' [m2' [A [B C]]]].
    left; econstructor; split.
    econstructor. eapply external_call_symbols_preserved; eauto.
    exact symbols_preserved. exact varinfo_preserved.
    constructor; auto.
  - (* external call turned into a Sbuiltin *)
    exploit external_call_rel; eauto.
    apply wf_mr_ld.
    apply wf_mr_norm_ld.
    eapply ld_list_ok; eauto.
    intros [vres' [m2 [A [B C]]]].
    left; econstructor; split.
    econstructor. eauto. eapply external_call_symbols_preserved; eauto.
    exact symbols_preserved. exact varinfo_preserved.
    constructor; auto.
  - (* return *)
    inv MC. 
    left; econstructor; split. 
    econstructor. 
    constructor; auto. destruct optid; simpl; auto. apply set_var_lessdef; auto.
  - (* return of an external call turned into a Sbuiltin *)
    right; split. simpl; lia. split. auto. constructor; auto. 
    destruct optid; simpl; auto. apply set_var_lessdef; auto.
Qed.

Lemma sel_initial_states:
  forall sg S, Cminor.initial_state prog sg S ->
  exists R, initial_state tprog sg R /\ match_states S R.
Proof.
  induction 1.
  exploit function_ptr_translated; eauto. intros (f' & A & B).
  econstructor; split.
  - econstructor.
    + eapply Genv.init_mem_transf_partial; eauto.
      intros a b0 TR.
      unfold Cminor.fid, fid; des a; des b0; try monadInv TR.
      unfold sel_function in EQ. monadInv EQ. auto.
    + simpl. fold tge. rewrite symbols_preserved.
      erewrite transform_partial_program_main by eauto. eexact H0.
    + eauto.
    + rewrite <- H2. apply sig_function_translated; auto.
  - constructor; auto. constructor. reflexivity. 
Qed.

Lemma sel_final_states:
  forall S R r,
  match_states S R -> Cminor.final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H. inv MC. constructor.
  generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ ME LD).
  setoid_rewrite H1. rewrite lessdef_val. intro A; inv A; auto.
Qed.

End PRESERVATION.

Axiom get_helpers_correct:
  forall ge hf, get_helpers ge = OK hf -> i64_helpers_correct ge hf.

Theorem transf_program_correct:
  forall prog tprog ns sg,
  sel_program prog = OK tprog ->
  forward_simulation (Cminor.semantics prog ns sg)
                     (CminorSel.semantics tprog ns sg).
Proof.
  intros. unfold sel_program in H. 
  destruct (get_helpers (Genv.globalenv prog)) as [hf|] eqn:E; simpl in H; try discriminate.
  apply forward_simulation_opt with (match_states := match_states prog tprog hf) (measure := measure). 
  eapply symbols_preserved; eauto.
  apply sel_initial_states; auto.
  apply sel_final_states; auto.
  apply sel_step_correct; auto.
  eapply helpers_correct_preserved; eauto.
  apply get_helpers_correct. auto.
Qed.
