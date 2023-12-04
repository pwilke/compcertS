Require Import AST.
Require Import Coqlib.
Require Import Clight2.
Require Import CCClight.
Require Import Maps.
Require Import Values.
Require Import Values_symbolictype.
Require Import Values_symbolic.
Require Import ExprEval. 
Require Import Memory.
Require Import Memdata.
Require Import Integers.
Require Import Floats.
Require Import Memtype.
Require Import Memperm.

Definition tree_of_tree {A B} (f: A -> B) (t: Maps.PTree.t A): Maps.PTree.t B :=
  PTree.map (fun _ => f) t.

Definition cfunction_of_function (f: function) : Clight2.function :=
  Clight2.mkfunction
    xH
    (fn_return f)
    (fn_callconv f)
    (fn_params f)
    (fn_vars f)
    (fn_temps f)
    (fn_body f)
    O.

Definition cfundef_of_fundef (f: fundef) : Clight2.fundef :=
  match f with
    Internal inf => Clight2.Internal (cfunction_of_function inf)
  | External ef tl t cc => Clight2.External ef tl t cc
  end.

Lemma tree_get_node:
  forall {A} i l x r (f:A),
  Maps.PTree.get i (Maps.PTree.Node l x r) = Some f ->
  match i with
    xH => x
  | xI p => Maps.PTree.get p r
  | xO p => Maps.PTree.get p l
  end = Some f.
Proof.
  intros.
  destruct i; auto. 
Qed.

Lemma tree_of_tree_get:
  forall t b f
    (GET : Maps.PTree.get b (tree_of_tree cfundef_of_fundef t) = Some f),
  exists f', Maps.PTree.get b t = Some f'.
Proof.
  intros.
  unfold tree_of_tree in GET. rewrite PTree.gmap in GET.
  des (t!b). eexists; eauto.  
Qed.

Definition genv_of_ccgenv (ge: genv) : Clight2.genv.
Proof.
  destruct ge.
  refine (Globalenvs.Genv.mkgenv genv_symb
                                 (tree_of_tree cfundef_of_fundef genv_funs)
                                 genv_vars
                                 _ _ _ _ _); eauto.
  - intros.
    eapply tree_of_tree_get in H.
    dex; eapply genv_funs_range; eauto.
  - intros.
    eapply tree_of_tree_get in H.
    dex; eapply genv_funs_vars; eauto.
Defined.

Definition match_expr (v: expr_sym) (e: expr_sym) : Prop :=
  Val.lessdef v e.

Definition match_val (v: val) (e: expr_sym) : Prop :=
  match_expr (Eval v) e.

Definition match_temp_env le tle :=
  forall id v,
    le ! id = Some v ->
    exists e, tle ! id = Some e /\ match_val v e.

Definition as_long (v:val) : expr_sym :=
  let chunk :=
      match v with
      | Vundef => Mint32
      | Vint x => Mint32
      | Vlong x => Mint64
      | Vfloat x => Mfloat64
      | Vsingle x => Mfloat32
      | Vptr x x0 => Mint32
      end in
  to_bits chunk (Eval v).    

Definition expr_of_fragment v q n :=
  let m :=
      if Archi.big_endian
      then n
      else match q with
             CCMemdata.Q32 => (3 - n)%nat
           | CCMemdata.Q64 => (7 - n)%nat
           end
  in
  expr_of_memval
    (Symbolic (as_long v)
              None
              m).

Definition match_memval (mv: CCMemdata.memval) (tmv: memval) : Prop :=
  match mv with
    CCMemdata.Undef => True
  | CCMemdata.Fragment v q n =>
    match_expr (expr_of_fragment v q n) (expr_of_memval tmv)
  | CCMemdata.Byte b =>
    match_val (Vlong (Int64.repr (Byte.unsigned b))) (expr_of_memval tmv)
  end.

Record match_mem (m: CCMemory.mem) (tm: Memory.mem) : Prop :=
  mk_match_mem
    {
      match_contents:
        forall b (o: Z),
          match_memval (ZMap.get o (CCMemory.Mem.mem_contents m) !! b)
                       (ZMap.get o (Mem.mem_contents tm) !! b);
      match_next:
        CCMemory.Mem.nextblock m = Mem.nextblock tm;
      match_perm:
        forall b o k p,
          CCMemory.Mem.perm m b o k p ->
          Mem.perm tm b o k p
    }.

(* In order to prove the preservation of external calls, we need the following
axions. The first two axioms are related to external functions and inline
assembly about which we know nothing and therefore we can only assume they
satisfy the properties we are interested in.

The malloc_match and free_match axioms are needed because CompCertS changed the
way those are handled. In particular, we do not store the size of dynamically
allocated blocks at negative offsets as CompCert does. This is to avoid
answering the question: does the alignment of a block apply to the offset 0 or
to the first valid offset of a block? We make those the same and avoid the
problem. Therefore we axiomatise their behaviour to avoid introducing a more
complex relationship between memories (injection?).


 *)

Axiom external_functions_sem_match:
  forall m tm 
    (MM : match_mem m tm)
    sg ge vargs eargs t vres m' name
    (EC : CCEvents.external_functions_sem name sg ge vargs m t vres m')
    (EVL : list_forall2 match_val vargs eargs),
   exists (eres : expr_sym) (tm' : Memory.mem),
     Events.external_functions_sem name sg (genv_of_ccgenv ge)
       (map (try_norm tm) eargs) tm t eres tm' /\
     match_val vres eres /\ match_mem m' tm'.

Axiom inline_assembly_match:
  forall m tm
    (MM : match_mem m tm)
    ge vargs t vres m' eargs text
    (EC : CCEvents.inline_assembly_sem text ge vargs m t vres m')
    (EVL : list_forall2 match_val vargs eargs),
  exists (eres : expr_sym) (tm' : Memory.mem),
    Events.inline_assembly_sem text (genv_of_ccgenv ge) (map (try_norm tm) eargs) tm t eres tm' /\
    match_val vres eres /\ match_mem m' tm'.

Axiom malloc_match:
  forall m tm
    (MM : match_mem m tm)
    ge vargs t vres eargs m'
    (EC : CCEvents.extcall_malloc_sem ge vargs m t vres m')
    (EVL : list_forall2 match_val vargs eargs),
  exists (eres : expr_sym) (tm' : Memory.mem),
    Events.extcall_malloc_sem (genv_of_ccgenv ge) (map (try_norm tm) eargs) tm t eres tm' /\
    match_val vres eres /\ match_mem m' tm'.

Axiom mfree_match:
  forall m tm
    (MM : match_mem m tm)
    ge vargs t vres eargs m'
    (EC : CCEvents.extcall_free_sem ge vargs m t vres m')
    (EVL : list_forall2 match_val vargs eargs),
  exists (eres : expr_sym) (tm' : Memory.mem),
    Events.extcall_free_sem (genv_of_ccgenv ge) (map (try_norm tm) eargs) tm t eres tm' /\
    match_val vres eres /\ match_mem m' tm'.

(* Finally, we make the assumption that the allocation is our model never fails.
This is so that the proof of semantic preservation goes through.

Intuitively the final proof (clight_eq) states that except for CompCert programs
that exhaust the memory space, the symbolic semantics are a refinement of the
original CompCert semantics. *)

Axiom alloc_succeeds:
  forall m lo hi al bt,
  exists m' b,
    Mem.low_alloc m lo hi al bt = Some (m',b).



Require Import CopGeneric.
Require Import Cop.

Definition unop_preserved ccop op :=
  forall tm
    v v' (t: Ctypes.type) res
    (MV : match_val v v')
    (SemCC : ccop (vptr tm) v t = Some res),
    match_val res (try_norm tm (op v' t)).

Ltac do_unop :=
  match goal with
    SemCC: ?opcc ?vptr ?v ?t = Some ?res
           , MV: match_val ?v ?v'
    |- match_val ?res (try_norm _ (?op ?v' ?t)) =>
    unfold opcc, op in *;
      match goal with
        |- context [match ?classify with _ => _ end]
        => destruct classify eqn:?;
                   try (now inv SemCC);
          try match goal with
                H : context[match ?v with _ => _ end] |- _
                => destruct v eqn:?; inv H;
                  let al := fresh "al" in
                  let em := fresh "em" in
                  red; intros al em;
                  let MV' := fresh "MV" in
                  generalize (MV al em); intro MV'; simpl in *;
                  try (inv MV'; [idtac])
              end
      end
  end.

Ltac do_unop_s :=
  match goal with
    SemCC: ?opcc ?v ?t = Some ?res
           , MV: match_val ?v ?v'
    |- match_val ?res (try_norm _ (?op ?v' ?t)) =>
    unfold opcc, op in *;
      match goal with
        |- context [match ?classify with _ => _ end]
        => destruct classify eqn:?;
                   try (now inv SemCC);
          try match goal with
                H : context[match ?v with _ => _ end] |- _
                => destruct v eqn:?; inv H;
                  let al := fresh "al" in
                  let em := fresh "em" in
                  red; intros al em;
                  let MV' := fresh "MV" in
                  generalize (MV al em); intro MV'; simpl in *;
                  try (inv MV'; [idtac])
              end
      end
  end.

Ltac do_unf :=
  match goal with
    |- Values.Val.lessdef _ (?f _) => unfold f; auto
  end.

Require Import Psatz.


Require Import NormaliseSpec.

Lemma norm_eundef:
  forall m b i,
    Mem.mem_norm m (Eundef b i) = Vundef.
Proof.
  intros.
  (* generalize (Mem.norm_gr m (Eundef b i) r). *)
  destruct (Mem.concrete_mem m) as [al COMP].
  generalize (fun pf em => Mem.norm_ld m (Eundef b i) _ eq_refl al em (compat_larger _ _ _ _ _ pf COMP)).
  intro A.
  trim A. simpl; unfsize. lia.
  generalize (A (fun _ _ => Byte.zero)) (A (fun _ _ => Byte.one)).
  clear A.
  simpl.
  des (Mem.mem_norm m (Eundef b i) );
  apply lessdef_nu_eq in H; try congruence;
  apply lessdef_nu_eq in H0; try congruence;
  apply inj_vint in H;
  apply inj_vint in H0.
  subst.
  discriminate.
  rewrite H in H0. discriminate.
Qed.

Definition styp_of_val v :=
  match v with
    Vundef => Tint
  | Vint _ => Tint
  | Vlong _ => Tlong
  | Vsingle _ => Tsingle
  | Vfloat _ => Tfloat
  | Vptr b i => Tint
  end.

Definition is_val e :=
  match e with
    Eval _ => True
  | _ => False
  end.               

Definition is_val_dec e : { is_val e } + { ~ is_val e }.
Proof.
  des e.
Qed.

Require Import ExprEval.

Lemma same_eval_eq_val:
  forall v1 v2,
    same_eval (Eval v1) (Eval v2) ->
    v1 = v2.
Proof.
  intros v1 v2 SE.
  generalize (SE (fun _ => Int.zero) (fun _ _ => Byte.zero)).
  generalize (SE (fun _ => Int.one) (fun _ _ => Byte.zero)).
  simpl.
  intros A B.
  des v1; des v2.
  - apply inj_vint in A.
    apply inj_vint in B.
    rewrite A in B.
    rewrite ! (Int.add_commut _ i0) in B.
    apply int_add_eq_l in B. discriminate.
  - apply inj_vint in A.
    apply inj_vint in B.
    rewrite <- A in B.
    rewrite ! (Int.add_commut _ i) in B.
    apply int_add_eq_l in B. discriminate.
  - apply inj_vint in A.
    apply inj_vint in B.
    apply int_add_eq_l in A. subst.
    generalize (SE (fun bb => if peq bb b then Int.one else Int.zero) (fun _ _ => Byte.zero)).
    simpl.
    intro C.
    apply inj_vint in C.
    rewrite peq_true in C.
    destr_in C.
    rewrite ! (Int.add_commut _ i0) in C.
    apply int_add_eq_l in C. discriminate. 
Qed.

Lemma try_norm_val:
  forall m e,
    is_val e ->
    try_norm m e = e.
Proof.
  intros; des e.
  unfold try_norm. rewrite Mem.norm_val.
  des v.
Qed.

Lemma try_norm_eq:
  forall m e,
    try_norm m e = max_def (Mem.mem_norm m e) e.
Proof.
  intros; des e.
Qed.

Definition try_norm_rew:
  forall m e v
    (NU: v <> Vundef)
    (SE: same_eval e (Eval v)),
    try_norm m e = Eval v.
Proof.
  intros.
  destruct (is_val_dec e).
  rewrite try_norm_val; auto.
  des e. apply same_eval_eq_val in SE; subst; auto.
  rewrite try_norm_eq; auto.
  rewrite ! (Mem.same_eval_eqm _ _ _ SE).
  rewrite Mem.norm_val. des v.
Qed.

Ltac rew_norm :=
  repeat rewrite Mem.norm_val in *.

Lemma compat_31_32:
  forall m al,
    Mem.compat_m m Mem.M31 al ->
    Mem.compat_m m Mem.M32 al.
Proof.
  intros m al COMP.
  eapply compat_larger in COMP. eauto.
  generalize (Mem.size31_inf); simpl; auto.
Qed.

Definition try_norm_rew':
  forall m e v
    (NU: v <> Vundef) 
    (SE: Mem.mem_norm m e = v),
    try_norm m e = Eval v.
Proof.
  unfold try_norm; intros.
  rewrite SE. des v.
Qed.

Ltac norm_rew v :=
  match goal with
    MV : match_val _ _ |- _ =>
    rewrite (try_norm_rew _ _ v); try congruence;
    [ destr; auto
    | red;
      let cm := fresh "cm" in
      let em0 := fresh "em0" in
      intros cm em0; simpl; specialize (MV cm em0); simpl in MV; inv MV;
      simpl; destr; auto]
  end.

Ltac norm_rew' v :=
  match goal with
    MV: match_val _ _ ,
        Heqb0: in_bound _ _ |- _ =>
    rewrite (try_norm_rew' _ _ v); try congruence; auto;
    apply Mem.eq_norm; try congruence; constructor;
    [ let al := fresh "al" in
      let em := fresh "em" in
      let COMP := fresh "COMP" in
      intros al em COMP;
        specialize (MV al em); simpl in MV; inv MV;
        simpl;
        eapply (NormaliseSpec.addr_space _ _ _ _ COMP) in Heqb0; auto
    ]
  end.


Lemma try_norm_rew_ptr:
  forall m e b i
    (NORM: Mem.mem_norm m e = Vptr b i),
    try_norm m e = Eval (Vptr b i).
Proof.
  unfold try_norm; intros.
  rewrite NORM; auto.
Qed.

Hint Constructors
     is_float_typ
     is_lval_typ.

Lemma match_val_typ:
  forall v e t,
    wt_val v t ->
    v <> Vundef ->
    match_val v e ->
    wt_expr e t.
Proof.
  intros v e t Wt Nu Mv.
  specialize (Mv (fun _ => Int.zero) (fun _ _ => Byte.zero)). simpl in Mv.
  generalize (expr_nu_type (fun _ => Int.zero) (fun _ _ => Byte.zero) e t (eSval (fun _ => Int.zero) v)).
  intro A.
  apply A; try now (des v; auto).
  inv Mv; auto. des v.
Qed.

Lemma match_val_depends:
  forall m b ofs e,
    match_val (Vptr b ofs) e ->
    depends Int.max_unsigned (Mem.bounds_of_block m) (Mem.nat_mask m) e b.
Proof.
  intros.
  red; intros.
  intro EQ.
  generalize (H cm em) (H cm' em).
  simpl; intros A B; inv A; inv B. rewrite <- EQ in H3; rewrite <- H3 in H2.
  apply inj_vint in H2.
  rewrite ! (Int.add_commut _ ofs) in H2.
  apply int_add_eq_l in H2; congruence.
Qed.

Lemma match_val_norm:
  forall tm b o tvf
    (MV : match_val (Vptr b o) tvf),
    Mem.mem_norm tm tvf = Vptr b o.
Proof.
  intros.
  apply Mem.eq_norm; simpl; auto.
  constructor. red; simpl; intros.
  apply MV.
  congruence.
Qed.

Lemma match_val_eval:
  forall v,
    match_val v (Eval v).
Proof.
  repeat red; auto.
Qed.


Lemma match_val_ptr_tn:
  forall tm b i e
    (MV : match_val (Vptr b i) e),
    match_val (Vptr b i) (try_norm tm e).
Proof.
  intros.
  destruct (is_val_dec e).
  - des e. rewrite try_norm_val; auto.
  - rewrite try_norm_eq; auto. erewrite match_val_norm; eauto.
    simpl.
    apply match_val_eval.
Qed.

Opaque try_norm.
    
Lemma notbool_preserved:
  unop_preserved sem_notbool sem_notbool_expr.
Proof.
  red; intros.
  do_unop.
  - unfold Values.Val.notbool, Values.Val.of_bool.
    norm_rew (Vint (if Int.eq i Int.zero then Int.one else Int.zero)).    
  - unfold Values.Val.of_bool, Values.Val.cmpf_bool; simpl.
    norm_rew (Vint (if Float.cmp Ceq f Float.zero then Int.one else Int.zero)).
  - unfold Values.Val.of_bool, Values.Val.cmpfs_bool; simpl.
    norm_rew (Vint (if Float32.cmp Ceq f Float32.zero then Int.one else Int.zero)).
  - unfold Values.Val.notbool, Values.Val.of_bool.
    norm_rew (Vint (if Int.eq i Int.zero then Int.one else Int.zero)).
  - revert H0; destr. inv H0.
    apply valid_pointer in Heqb0.
    norm_rew' (Vint Int.zero).
    rewrite <- H1.
    simpl. unfold Values.Val.of_bool. destr; auto.
    apply int_eq_true in Heqb1. rewrite Heqb1 in H.
    rewrite Int.unsigned_zero in H; lia.
  - unfold Values.Val.cmpl_bool, Values.Val.of_bool.
    norm_rew (Vint (if Int64.eq i Int64.zero then Int.one else Int.zero)).
Qed.

Lemma notint_preserved:
  unop_preserved (fun vptr => sem_notint) sem_notint_expr.
Proof.
  red; intros.
  do_unop_s.
  - norm_rew (Vint (Int.not i)).
  - norm_rew (Vlong (Int64.not i)).
Qed.

Lemma neg_preserved:
  unop_preserved (fun vptr => sem_neg) sem_neg_expr.
Proof.
  red; intros.
  generalize (fun al em => expr_nu_type al em v' (styp_of_val v) v).
  intro A.
  do_unop_s;
    match goal with
      |- Values.Val.lessdef ?v _ => norm_rew v
    end;
    symmetry in H1; apply A in H1; destr.
Qed.

Lemma absfloat_preserved:
  unop_preserved (fun vptr => sem_absfloat) sem_absfloat_expr.
Proof.
  red; intros.
  generalize (fun al em => expr_nu_type al em v' (styp_of_val v) v).
  generalize (isTfloat) isTsingle.
  intros II III A.
  do_unop_s;
    match goal with
      |- Values.Val.lessdef ?v _ => norm_rew v
    end;
    symmetry in H1; apply A in H1; destr.
  des s. des s.
Qed.

Lemma eval_unary:
  forall op,
    unop_preserved (fun vptr => sem_unary_operation vptr op)
                   (sem_unary_operation_expr op).
Proof.
  destruct op.
  apply notbool_preserved.
  apply notint_preserved.
  apply neg_preserved.
  apply absfloat_preserved.
Qed.

Definition binop_preserved ccop op :=
  forall tm
    v1 v1' v2 v2' (t1 t2: Ctypes.type) res
    (MV1: match_val v1 v1')
    (MV2: match_val v2 v2')
    (SemCC: ccop (vptr tm) v1 t1 v2 t2 = Some res),
  exists res',
    op v1' t1 v2' t2 = Some res' /\
    match_val res (try_norm tm res').

Ltac zext32 :=
  simpl; rewrite Int.zero_ext_above by (IntFacts.unfsize; lia); auto.

Ltac sext32 :=
  rewrite Int.sign_ext_above by (IntFacts.unfsize; lia); auto.

Ltac boolvalt := unfold Values.Val.boolval; destr; auto.

Ltac mauto := (now zext32) || (now sext32) || (now boolvalt) || auto.

Ltac mtot_unfold :=
  match goal with
    |- context[Val.maketotal (?f _)] =>
    unfold f; simpl
  end.


Ltac autoinv :=
  repeat
    match goal with
      H : Some _ = Some _ |- _ => inv H
    | H : Some _ = None |- _ => inv H
    | H : None = Some _ |- _ => inv H
    end.

Ltac mvauto :=
  match goal with
    |- match_val ?v _ => norm_rew v; repeat red; mauto
  end.

Lemma is_undef v : { v = Vundef } + { v <> Vundef }.
Proof.
  des v.
Qed.

Lemma match_val_tn:
  forall tm e v
    (MV : match_val v e),
    match_val v (try_norm tm e).
Proof.
  intros.
  destruct (is_val_dec e).
  - des e. rewrite try_norm_val; auto.
  - rewrite try_norm_eq; auto.
    generalize (fun t => Mem.norm_type tm (Eval v) _ t eq_refl). intro NT0.

    destruct (is_undef v).
    + subst. repeat red; auto.
    +
      assert (same_eval e (Eval v)).
      red; intros cm em. specialize (MV cm em); inv MV. auto. des v.
      rewrite Mem.same_eval_eqm with (v2:=Eval v) in * by auto.
      rewrite Mem.norm_val in *.
      des v; apply match_val_eval.
Qed.

Lemma sem_cast_preserved:
  forall tm v t1 t2 res e
    (SC: sem_cast (vptr tm) v t1 t2 = Some res)
    (MV: match_val v e),
    exists res',
      sem_cast_expr e t1 t2 = Some res' /\
      match_val res (try_norm tm res').
Proof.
  intros.
  generalize (fun t wt nu => match_val_typ v e t wt nu MV). intro Typ.
  Ltac try_typ Typ :=
    (specialize (Typ Tint I)
     || specialize (Typ Tlong I)
     || specialize (Typ Tfloat I)
     || specialize (Typ Tsingle I)); destr.
  unfold sem_cast, sem_cast_expr in *.
  destruct (classify_cast t1 t2) eqn:?; des v;
    autoinv;
  try (eexists; split; [eauto|]; [idtac]);
  try now (red; red; red; simpl; intros;

           match goal with
             |- Values.Val.lessdef ?v _ => norm_rew v
           end; mauto).
  
  - eapply match_val_tn. 
    repeat red; auto.
    intros.
    specialize (MV alloc em).
    simpl. inv MV.
    simpl. sext32.
  - des sz2; des si2; simpl; mvauto.
  - des si1; unfold convert_t; mvauto; try_typ Typ.
  - des si1; mvauto; try_typ Typ;  unfold convert_t; mtot_unfold.
    rewrite Float32.of_int_double; auto.
    rewrite Float32.of_intu_double; auto.
  - destr_in SC; autoinv.
    unfold expr_cast_gen, expr_cast_int_int.
    des sz2; des si2; mvauto; try_typ Typ; unfold convert_t; mtot_unfold;
    rewrite Heqo; simpl; mauto;
    rewrite Heqb; simpl; auto.
  - destr_in SC; autoinv.
    unfold expr_cast_gen, expr_cast_int_int.
    des sz2; des si2; mvauto; try_typ Typ; unfold convert_t; mtot_unfold;
    rewrite Heqo; simpl; mauto;
    rewrite Heqb; simpl; auto.
  - des si1; unfold cast_int_long, expr_cast_gen; mvauto; try_typ Typ. 
  - unfold cast_int_int, expr_cast_int_int.
    des sz2; des si2; mvauto; try_typ Typ; setoid_rewrite Heqb; simpl; auto.
  - des si1; mvauto; try_typ Typ.
  - des si1; mvauto; try_typ Typ. 
  - destr_in SC; autoinv;
    des si2; mvauto; try_typ Typ; unfold convert_t; mtot_unfold; rewrite Heqo; simpl; auto.
  - destr_in SC; autoinv;
    des si2; mvauto; try_typ Typ; unfold convert_t; mtot_unfold; rewrite Heqo; simpl; auto.
  - destr_in SC; autoinv.
    apply Cop.valid_pointer in Heqb0.
    rewrite (try_norm_rew' _ _ (Vint Int.one)); try congruence.
    repeat red; auto.
    apply Mem.eq_norm; simpl; try congruence; auto.
    constructor.
    intros cm em COMP.
    inv COMP.
    apply addr_space in Heqb0.
    unfold Values.Val.notbool.
    specialize (MV cm em). simpl in MV. inv MV. simpl.
    rewrite <- H1. simpl. destr; auto.
    apply int_eq_true in Heqb1. rewrite Heqb1 in H.
    rewrite Int.unsigned_zero in H; lia.
  - destr_in SC; autoinv.
    apply andb_true_iff in Heqb0. destruct Heqb0 as [A B].
    eexists; split; eauto.
    eapply match_val_ptr_tn; eauto.
  - destr_in SC; autoinv.
    apply andb_true_iff in Heqb0. destruct Heqb0 as [A B].
    eexists; split; eauto.
    eapply match_val_ptr_tn; eauto.
  - repeat red; auto.
  - eapply match_val_tn; eauto.
Qed.

Section BinArith.

  Variable sem_int: Ctypes.signedness -> int -> int -> option val.
  Variable sem_long: Ctypes.signedness -> int64 -> int64 -> option val.
  Variable sem_float: float -> float -> option val.
  Variable sem_single: float32 -> float32 -> option val.

  Variable sem_int_expr: Ctypes.signedness -> expr_sym -> expr_sym -> option expr_sym.
  Variable sem_long_expr: Ctypes.signedness -> expr_sym -> expr_sym -> option expr_sym.
  Variable sem_float_expr: expr_sym -> expr_sym -> option expr_sym.
  Variable sem_single_expr: expr_sym -> expr_sym -> option expr_sym.

  Definition sem_preserved {A} ccsem sem (vcons : A -> val) :=
    forall tm (s: Ctypes.signedness) i1 i2 v e1 e2,
      match_val (vcons i1) (try_norm tm e1) ->
      match_val (vcons i2) (try_norm tm e2) ->
      ccsem s i1 i2 = Some v ->
      exists res,
        sem s e1 e2 = Some res /\
        match_val v (try_norm tm res).
  
  Hypothesis sem_int_preserved: sem_preserved sem_int sem_int_expr Vint.
  Hypothesis sem_long_preserved: sem_preserved sem_long sem_long_expr Vlong.
  Hypothesis sem_float_preserved: sem_preserved (fun s => sem_float) (fun s => sem_float_expr) Vfloat.
  Hypothesis sem_single_preserved: sem_preserved (fun s => sem_single) (fun s => sem_single_expr) Vsingle.
  
  Lemma sem_binarith_preserved:
    forall tm v1 v1' v2 v2' t1 t2
      (MV1 : match_val v1 v1')
      (MV2 : match_val v2 v2')
      res
      (SemCC : sem_binarith (vptr tm)
                            sem_int sem_long sem_float sem_single
                            v1 t1 v2 t2 = Some res),
    exists res',
      sem_binarith_expr
        sem_int_expr sem_long_expr sem_float_expr sem_single_expr
        v1' t1 v2' t2 = Some res' /\
      match_val res (try_norm tm res').
  Proof.
    intros.
    unfold sem_binarith in SemCC; unfold sem_binarith_expr.
    destr_in SemCC.
    destr_in SemCC.
    generalize (sem_cast_preserved _ _ _ _ _ _ Heqo MV1). intros [res' [SC' MV']].
    generalize (sem_cast_preserved _ _ _ _ _ _ Heqo0 MV2). intros [res2' [SC2' MV2']].
    rewrite SC', SC2'.
    destr.
    - des v; des v0. eapply sem_int_preserved; eauto.
    - des v; des v0. eapply sem_long_preserved; eauto.
    - des v; des v0. eapply sem_float_preserved; eauto. exact Ctypes.Signed.
    - des v; des v0. eapply sem_single_preserved; eauto. exact Ctypes.Signed.
  Qed.

End BinArith.


  Ltac do_binop :=
  match goal with
    SemCC: ?opcc ?vptr ?v1 ?t1 ?v2 ?t2 = Some ?res
           , MV1: match_val ?v1 ?v1'
                  , MV2: match_val ?v2 ?v2'
    |- exists r, ?op _ _ _ _ = Some ?r /\ match_val ?res (try_norm _ ?r) =>
    unfold opcc, op in *;
      match goal with
        |- context [match ?classify with _ => _ end]
        => destruct classify eqn:?;
                   try (now inv SemCC);
          try (eexists; split; eauto; [idtac]);
          
          repeat match goal with
                H : context[match ?v with _ => _ end] |- _
                => destruct v eqn:?; inv H;
                  idtac
              end
      | _ => idtac
      end
  end.

Lemma match_val_tn_forall:
  forall m v e,
    match_val v (try_norm m e) ->
    forall cm
      (COMP: Mem.compat_m m Mem.M32 cm)
      em,
      Values.Val.lessdef (eSval cm v) (eSexpr cm em e).
Proof.
  intros m v e MV cm COMP em.
  destruct (is_val_dec e). rewrite try_norm_val in MV; auto.
  apply MV.
  rewrite try_norm_eq in MV; auto.
  specialize (MV cm em). destr.
  eapply Values.Val.lessdef_trans.
  apply MV.
  generalize (Mem.norm_ld m e _ eq_refl cm em COMP).
  des (Mem.mem_norm m e). auto.
Qed.


Lemma try_norm_wt:
  forall m e t,
    wt_expr (try_norm m e) t -> wt_expr e t.
Proof.
  intros. destruct (is_val_dec e).
  rewrite try_norm_val in H; auto.
  rewrite try_norm_eq in H; auto.
  generalize (Mem.norm_type m e _ t eq_refl).
  des (Mem.mem_norm m e); des t.
Qed.

Lemma match_val_tnorm:
  forall m v e t,
    match_val v (try_norm m e) ->
    wt_val v t ->
    v <> Vundef ->
    wt_expr e t.
Proof.
  intros.
  exploit match_val_typ; eauto.
  apply try_norm_wt.
Qed.

Ltac ba_oblig :=
  clear; red;
  let tm := fresh "tm" in
  let sg := fresh "sg" in
  let i1 := fresh "i1" in
  let i2 := fresh "i2" in
  let v := fresh "v" in
  let e1 := fresh "e1" in
  let e2 := fresh "e2" in
  let MV1 := fresh "MV1" in
  let MV2 := fresh "MV2" in
  intros tm sg i1 i2 v e1 e2 MV1 MV2 ?; autoinv; simpl;
  eexists; split; eauto;
  rewrite try_norm_eq; 
    match goal with
       |- match_val ?va _ =>
       (rewrite Mem.eq_norm with (v:=va) ; try congruence); 
         [ repeat intro; auto
         | constructor; [
             red; intros;
             eapply match_val_tn_forall in MV1; eauto;
             eapply match_val_tn_forall in MV2; eauto;
             let v1 := fresh "v1" in
             let V1 := fresh "V1" in
             let V1' := fresh "V1'" in
             let v2 := fresh "v2" in
             let V2 := fresh "V2" in
             let V2' := fresh "V2'" in
             inversion MV1 as [v1 V1 V1'|];
               inversion MV2 as [v2 V2 V2'|]; subst;
               simpl; try rewrite <- V1', <- V2'; simpl; auto ] | ..
         ]
     end.

Lemma add_preserved: binop_preserved sem_add sem_add_expr.
Proof.
  red; intros.
  do_binop;
    try (eapply match_val_tn;
          repeat red; intros;
          specialize (MV1 alloc em); specialize (MV2 alloc em); simpl in *;
          inv MV1; inv MV2; simpl; sint; rewrite Int.mul_commut; auto).
  - eapply sem_binarith_preserved; eauto;
    ba_oblig.
Qed.

Lemma sub_preserved: binop_preserved sem_sub sem_sub_expr.
Proof.
  red; intros.
  do_binop;
      try (eapply match_val_tn;
          repeat red; intros;
          specialize (MV1 alloc em); specialize (MV2 alloc em); simpl in *;
          inv MV1; inv MV2; simpl in *; auto).
  - rewrite ! Int.sub_add_opp.  sint. rewrite Int.mul_commut; auto.
  - rewrite Heqb. simpl. 
    rewrite ! (Int.add_commut (alloc b0)).
    rewrite Int.sub_shifted; auto. 
  - simpl. rewrite ! Int.sub_add_opp.  sint.
    rewrite Int.mul_commut; auto. 
  - eapply sem_binarith_preserved; eauto;
    ba_oblig.
Qed.

Lemma mul_preserved: binop_preserved sem_mul sem_mul_expr.
Proof.
  red; intros.
  do_binop.
  eapply sem_binarith_preserved; eauto;
      ba_oblig.
Qed.

Lemma div_preserved: binop_preserved sem_div sem_div_expr.
Proof.
  red; intros.
  do_binop.
  eapply sem_binarith_preserved; eauto;
  ba_oblig; repeat destr_in H; autoinv; simpl; auto.
Qed.

Lemma mod_preserved: binop_preserved sem_mod sem_mod_expr.
Proof.
    red; intros.
  do_binop.
  eapply sem_binarith_preserved; eauto;
  try (ba_oblig; repeat destr_in H; autoinv; simpl; auto).
Qed.

Lemma and_preserved: binop_preserved sem_and sem_and_expr.
Proof.
  red; intros.
  do_binop.
  eapply sem_binarith_preserved; eauto;
  ba_oblig.
Qed.

Lemma or_preserved: binop_preserved sem_or sem_or_expr.
Proof.
  red; intros.
  do_binop.
  eapply sem_binarith_preserved; eauto; try ba_oblig; red; destr.
Qed.

Lemma xor_preserved: binop_preserved sem_xor sem_xor_expr.
Proof.
  red; intros.
  do_binop.
  eapply sem_binarith_preserved; eauto; try ba_oblig; red; destr.
Qed.

Section Shifts.

  Variable sem_int: Ctypes.signedness -> int -> int -> int.
  Variable sem_long: Ctypes.signedness -> int64 -> int64 -> int64.

  Variable sem_int_expr: Ctypes.signedness -> expr_sym -> expr_sym -> expr_sym.
  Variable sem_long_expr: Ctypes.signedness -> expr_sym -> expr_sym -> expr_sym.

  Definition sem_shifts_preserved {A} ccsem sem (vcons : A -> val) (P: A -> Prop) :=
    forall tm (s: Ctypes.signedness) i1 i2 e1 e2,
      P i2 ->
      match_val (vcons i1) e1 ->
      match_val (vcons i2) e2 ->
      match_val (vcons (ccsem s i1 i2)) (try_norm tm (sem s e1 e2)).
  
  Hypothesis sem_int_preserved: sem_shifts_preserved sem_int sem_int_expr Vint (fun i2 => Int.ltu i2 Int.iwordsize = true).
  Hypothesis sem_long_preserved: sem_shifts_preserved sem_long sem_long_expr Vlong (fun i2 => Int64.ltu i2 Int64.iwordsize = true).
  
  Lemma sem_shift_preserved:
    forall tm v1 v1' v2 v2' t1 t2
      (MV1 : match_val v1 v1')
      (MV2 : match_val v2 v2')
      res
      (SemCC : sem_shift sem_int sem_long v1 t1 v2 t2 = Some res),
    exists res',
      sem_shift_expr sem_int_expr sem_long_expr v1' t1 v2' t2 = Some res' /\
      match_val res (try_norm tm res').
  Proof.
    intros.
    unfold sem_shift in SemCC; unfold sem_shift_expr.
    destr; des v1; des v2; destr_in SemCC; autoinv; simpl.
    - eexists; split; eauto. 
    - eexists; split; eauto.
    - eexists; split; eauto.
      eapply sem_int_preserved; eauto.
      unfold Int64.ltu, Int.ltu in *.
      destr_in Heqb. destr. 
      unfold Int64.loword in g.
      change (Int64.unsigned (Int64.repr 32)) with 32 in l.
      change (Int.unsigned Int.iwordsize) with 32 in g.
      rewrite Int.unsigned_repr in g. lia.
      generalize (Int64.unsigned_range i0).  IntFacts.unfsize. lia.
      red; red; red; intros. specialize (MV2 alloc em).
      simpl in *; inv MV2; unfold convert_t. des s; auto.
    - eexists; split; eauto.
      eapply sem_long_preserved; eauto.
      unfold Int64.ltu, Int.ltu in *.
      destr_in Heqb. destr. 
      change (Int.unsigned (Int64.iwordsize')) with 64 in l.
      change (Int64.unsigned Int64.iwordsize) with 64 in g.
      rewrite Int64.unsigned_repr in g. lia.
      generalize (Int.unsigned_range i0).  IntFacts.unfsize. lia.
      red; red; red; intros. specialize (MV2 alloc em).
      simpl in *; inv MV2; unfold convert_t. auto. 
  Qed.

End Shifts.

Ltac sh_oblig :=
  clear; red;
  let tm := fresh "tm" in
  let sg := fresh "sg" in
  let i1 := fresh "i1" in
  let i2 := fresh "i2" in
  let e1 := fresh "e1" in
  let e2 := fresh "e2" in
  let MV1 := fresh "MV1" in
  let MV2 := fresh "MV2" in
  let al := fresh "al" in
  let em := fresh "em" in
  let COMP := fresh "COMP" in
  let P := fresh "P" in
  intros tm sg i1 i2 e1 e2 P MV1 MV2 al em;
    specialize (MV1 al em);
    specialize (MV2 al em); simpl in *;
    inv MV1; inv MV2; simpl; auto.

Ltac do_binop' :=
  match goal with
    SemCC: ?opcc ?v1 ?t1 ?v2 ?t2 = Some ?res
           , MV1: match_val ?v1 ?v1'
                  , MV2: match_val ?v2 ?v2'
    |- exists res',
      (?op ?v1' ?t1 ?v2' ?t2) = Some res' /\
      match_val ?res (try_norm ?tm ?res') =>
    unfold opcc, op in *;
      match goal with
        |- context [match ?classify with _ => _ end]
        => destruct classify eqn:?;
                   try (now inv SemCC);
          try match goal with
                H : context[match ?v with _ => _ end] |- _
                => destruct v eqn:?; inv H;
                  let al := fresh "al" in
                  let em := fresh "em" in
                  red; intros al em;
                  specialize (MV1 al em); simpl in *;
                  specialize (MV2 al em); simpl in *;
                  try match goal with
                        H : context[match ?v with _ => _ end] |- _
                        => destruct v eqn:?; inv H
                      end;
                  try (inv MV1; [idtac]);
                  try (inv MV2; [idtac])
              end
      | _ => idtac
      end
  end.


Lemma shl_preserved: binop_preserved (fun vptr => sem_shl) sem_shl_expr.
Proof.
  red; intros.
  do_binop'.
  eapply sem_shift_preserved; eauto.
  clear; red; intros.

  rewrite try_norm_eq; auto.
  rewrite Mem.eq_norm with (v:=Vint (Int.shl i1 i2)); simpl; auto; try congruence.
  repeat red; auto.
  constructor.
  red; intros alloc em COMP;
  specialize (H0 alloc em); specialize (H1 alloc em); simpl;
  inv H0; inv H1; simpl; auto.
  rewrite H; auto.
  simpl; auto.

  clear; red; intros.
  rewrite try_norm_eq; auto.
  rewrite Mem.eq_norm with (v:=Vlong (Int64.shl i1 i2)); simpl; auto; try congruence.
  repeat red; auto.
  constructor. red; simpl; intros alloc em COMP.
  specialize (H0 alloc em); specialize (H1 alloc em); inv H0; inv H1; simpl; auto.
  destr. unfold Int64.shl', Int64.shl. unfold Int64.loword.
  rewrite Int.unsigned_repr; auto.
  apply Int64.ltu_inv in H. IntFacts.unfsize. change (Int64.unsigned Int64.iwordsize) with 64 in H.
  lia.
  
  
  clear - Heqb H. 
  unfold Int.ltu in Heqb. 
  apply Int64.ltu_inv in H.
  change (Int.unsigned Int64.iwordsize') with 64 in Heqb.
  change (Int64.unsigned Int64.iwordsize) with 64 in H.
  destr_in Heqb.
  revert g.
  unfold Int64.loword.
  rewrite Int.unsigned_repr. lia.
  generalize (Int64.unsigned_range i2); split. lia.
  transitivity 64. lia. IntFacts.unfsize; lia.
Qed.

Lemma shr_preserved: binop_preserved (fun vptr => sem_shr) sem_shr_expr.
Proof.
  red; intros.
  do_binop'.
  eapply sem_shift_preserved; eauto.
  -  red; intros.
     norm_rew  (Vint (match s with
                      | Ctypes.Signed => Int.shr i1 i2
                      | Ctypes.Unsigned => Int.shru i1 i2
                      end)).
     repeat red; auto.
     repeat red; auto.
     specialize (H0 cm em0); inv H0; simpl; auto. rewrite H; auto.
     specialize (H0 cm em0); inv H0; simpl; auto. rewrite H; auto.
  - red; intros.
    assert (Int.ltu (Int64.loword i2) Int64.iwordsize' = true).
    {
      unfold Int.ltu. destr. 
      apply Int64.ltu_inv in H.
      change (Int.unsigned Int64.iwordsize') with 64 in g.
      change (Int64.unsigned Int64.iwordsize) with 64 in H.  
      revert g.
      unfold Int64.loword.
      rewrite Int.unsigned_repr. lia.
      split. lia. transitivity 64. lia. IntFacts.unfsize; lia.
    }
    assert (Int.unsigned (Int64.loword i2) = Int64.unsigned i2).
    {
      unfold Int64.loword.
      rewrite Int.unsigned_repr. auto.
      generalize (Int64.unsigned_range i2); split. lia.
      transitivity 64.
      apply Int64.ltu_inv in H.
      change (Int64.unsigned Int64.iwordsize) with 64 in H. lia. IntFacts.unfsize; lia.
    }
    norm_rew (Vlong
        match s with
        | Ctypes.Signed => Int64.shr i1 i2
        | Ctypes.Unsigned => Int64.shru i1 i2
        end).
    repeat red; auto.
     repeat red; auto.
     specialize (H0 cm em0); inv H0; simpl; auto. rewrite H2; auto.
     unfold Int64.shr', Int64.shr. rewrite H3; auto.
     specialize (H0 cm em0); inv H0; simpl; auto. rewrite H2; auto.
     unfold Int64.shru', Int64.shru.
     rewrite H3; auto.
Qed.

Lemma weak_valid_pointer:
  forall m b0 i0,
    Mem.valid_pointer m b0 (Int.unsigned i0) = false ->
    Mem.valid_pointer m b0 (Int.unsigned i0 - 1) = true ->
    Int.unsigned i0 = snd (Mem.bounds_of_block m b0) \/
    NormaliseSpec.in_bound (Int.unsigned i0) (Mem.bounds_of_block m b0).
Proof.
  intros.
  eapply weak_valid_pointer; eauto.
  intro bb. generalize (Mem.bounds_lo_inf0 m bb).
  unfold Mem.bounds_of_block. destr. des p.
  specialize (H1 _ _ eq_refl). lia.
  apply valid_pointer.
  intros b i1 nin.
  des (Mem.valid_pointer m b i1).
  apply valid_pointer in Heqb1; auto.
  exfalso; apply nin; auto.
Qed.

Lemma compat_conserve_cmp:
  forall m (c : comparison) (al : block -> int) (b : block) (i i0 : int) q,
    Mem.compat_m m q al ->
    NormaliseSpec.in_bound (Int.unsigned i) (Mem.bounds_of_block m b) ->
    NormaliseSpec.in_bound (Int.unsigned i0) (Mem.bounds_of_block m b) ->
    Int.cmpu c (Int.add i (al b)) (Int.add i0 (al b)) = Int.cmpu c i i0.
Proof.
  intros.
  eapply compat_conserve_cmp; eauto.
  generalize (Mem.size31_inf); des q. lia.
  intro bb. generalize (Mem.bounds_lo_inf0 m bb).
  unfold Mem.bounds_of_block. destr. des p.
  specialize (H2 _ _ eq_refl). lia.
Qed.

Lemma compat_conserve_cmp':
  forall m (c : comparison) (al : block -> int) 
    (b : block) (i i0 : int) q,
    Mem.compat_m m q al ->
    NormaliseSpec.in_bound (Int.unsigned i) (Mem.bounds_of_block m b) ->
    Int.unsigned i0 = snd (Mem.bounds_of_block m b) ->
    Int.cmpu c (Int.add i (al b)) (Int.add i0 (al b)) = Int.cmpu c i i0.
Proof.
  intros.
  eapply compat_conserve_cmp'; eauto.
  generalize (Mem.size31_inf); des q. lia.
  intro bb. generalize (Mem.bounds_lo_inf0 m bb).
  unfold Mem.bounds_of_block. destr. des p.
  specialize (H2 _ _ eq_refl). lia.
Qed.

Lemma compat_conserve_cmp'':
  forall m (c : comparison) (al : block -> int) 
    (b : block) (i i0 : int) q,
    Mem.compat_m m q al ->
    NormaliseSpec.in_bound (Int.unsigned i) (Mem.bounds_of_block m b) ->
    Int.unsigned i0 = snd (Mem.bounds_of_block m b) \/
    NormaliseSpec.in_bound (Int.unsigned i0) (Mem.bounds_of_block m b) ->
    Int.cmpu c (Int.add i (al b)) (Int.add i0 (al b)) = Int.cmpu c i i0.
Proof.
  intros.
  destruct H1.
  eapply compat_conserve_cmp'; eauto.
  eapply compat_conserve_cmp; eauto.
Qed.

Lemma zlt_not_refl:
  forall {A} i (a b: A),
    (if zlt i i then a else b) = b.
Proof.
  intros; destruct (zlt i i). lia.  auto.
Qed.

Lemma wvp_cmp:
  forall m b i i',
    Mem.weak_valid_pointer m b (Int.unsigned i) = true ->
    Mem.weak_valid_pointer m b (Int.unsigned i') = true ->
    forall al q c,
      Mem.compat_m m q al ->
      Int.cmpu c (Int.add i (al b)) (Int.add i' (al b)) = Int.cmpu c i i'.
Proof.
  intros.
  unfold Mem.weak_valid_pointer in *.
  des (Mem.valid_pointer m b (Int.unsigned i));
    des (Mem.valid_pointer m b (Int.unsigned i')).
  - eapply compat_conserve_cmp; eauto; apply valid_pointer; auto.
  - apply weak_valid_pointer in Heqb1; auto.
    eapply compat_conserve_cmp''; eauto.
    apply valid_pointer; auto.
  - apply weak_valid_pointer in H; auto.
    rewrite <- ! (Int.swap_cmpu c).
    eapply compat_conserve_cmp''; eauto.
    apply valid_pointer; auto.
  - apply weak_valid_pointer in H; auto.
    apply weak_valid_pointer in Heqb1; auto.
    destruct H.
    destruct Heqb1.
    + unfold Int.add, Int.cmpu, Int.eq, Int.ltu.
      rewrite H, H2.
      rewrite ! zeq_true.
      rewrite ! zlt_not_refl. auto.
    + rewrite <- ! (Int.swap_cmpu c).
      eapply compat_conserve_cmp''; eauto.
    + eapply compat_conserve_cmp''; eauto.
Qed.

Definition cmp_pres cmp :=
  forall tm
    v1 v1' v2 v2' (t1 t2: Ctypes.type) res
    (MV1: match_val v1 v1')
    (MV2: match_val v2 v2')
    (SemCC: sem_cmp cmp v1 t1 v2 t2 (Mem.valid_pointer tm) = Some res),
  exists res',
    (sem_cmp_expr cmp v1' t1 v2' t2) = Some res' /\
    match_val res (try_norm tm res').

Opaque try_norm.

Lemma cmp_preserved:
  forall cmp, cmp_pres cmp.
Proof.
  Ltac t MV1 MV2 := red; red; red; intros al em; specialize (MV1 al em);
            specialize (MV2 al em); simpl in *; inv MV1; inv MV2; simpl; mauto.
  red; intros.
  unfold sem_cmp, sem_cmp_expr in *.
  destr_in SemCC.
  - unfold Values.Val.cmpu_bool in SemCC.
    des v1; des v2; autoinv; eexists; split; eauto.
    + unfold Values.Val.of_bool.
      norm_rew (Vint (if Int.cmpu cmp i i0 then Int.one else Int.zero)).
      repeat red; auto.
      repeat red; auto.
      specialize (MV1 cm em0); inv MV1; simpl; rewrite Heqb; auto.
      specialize (MV1 cm em0); inv MV1; simpl; rewrite Heqb; auto.
    + repeat destr_in SemCC.
      des (Values.Val.cmp_different_blocks cmp); autoinv.
      rewrite try_norm_rew' with (v:=Vint (if b0 then Int.one else Int.zero)).
      repeat red; destr; auto. congruence.
      apply Mem.eq_norm; simpl; intros; try congruence; auto.
      constructor; red; intros; simpl; auto.
      apply valid_pointer in Heqb0. inv Pcm; apply addr_space in Heqb0.
      apply int_eq_true in Heqb1; subst.
      specialize (MV1 cm em);
        specialize (MV2 cm em); inv MV1; inv MV2. simpl.
      des cmp; repeat destr; autoinv; simpl; auto.
      apply int_eq_true in Heqb0. rewrite <- Heqb0 in H. rewrite Int.unsigned_zero in H; lia.
      rewrite negb_false_iff in Heqb0.
      apply int_eq_true in Heqb0. rewrite <- Heqb0 in H. rewrite Int.unsigned_zero in H; lia.
    + repeat destr_in SemCC.
      des (Values.Val.cmp_different_blocks cmp); autoinv.
      rewrite try_norm_rew' with (v:=Vint (if b0 then Int.one else Int.zero)).
      repeat red; destr; auto. congruence.

      apply Mem.eq_norm; try constructor; simpl; try red; intros; try congruence; auto.
      inv Pcm.
      apply valid_pointer in Heqb0. apply addr_space in Heqb0.
      apply int_eq_true in Heqb1; subst. simpl.
      specialize (MV1 cm em);
        specialize (MV2 cm em); inv MV1; inv MV2. simpl.
      des cmp; repeat destr; autoinv; simpl; auto.
      apply int_eq_true in Heqb0. rewrite  Heqb0 in H. rewrite Int.unsigned_zero in H; lia.
      rewrite negb_false_iff in Heqb0.
      apply int_eq_true in Heqb0. rewrite  Heqb0 in H. rewrite Int.unsigned_zero in H; lia.
      
    + repeat destr_in SemCC. autoinv.
      apply andb_true_iff in Heqb. destruct Heqb as [A B].
      *  
        rewrite try_norm_rew' with (v:=Vint (if Int.cmpu cmp i i0 then Int.one else Int.zero)).
        unfold Values.Val.of_bool; repeat red; destr; auto. congruence.
        apply Mem.eq_norm; simpl; intros; auto; try congruence.
        constructor.
        red; intros alloc em Pcm. simpl.
        specialize (MV1 alloc em);
          specialize (MV2 alloc em); inv MV1; inv MV2. simpl.
        rewrite !(Int.add_commut (alloc b0)).
        erewrite wvp_cmp; eauto. destr; auto.

      * apply andb_true_iff in Heqb1; destruct Heqb1 as [A B].
        des (Values.Val.cmp_different_blocks cmp). autoinv.
        rewrite try_norm_rew' with (v:=Vint (if b1 then Int.one else Int.zero)).
        unfold Values.Val.of_bool; repeat red; destr; auto. congruence.
        
        apply Mem.eq_norm; simpl; intros; auto; try congruence.
        constructor; red; simpl; intros.
        specialize (MV1 cm em);
          specialize (MV2 cm em); inv MV1; inv MV2. simpl.
        inv Pcm.
        generalize (overlap _ _ _ _ n (valid_pointer _ _ _ A) (valid_pointer _ _ _ B)).
        des cmp; autoinv.
        unfold Int.eq. destruct (zeq _ _). congruence. simpl; auto.
        unfold Int.eq. destruct (zeq _ _). congruence. simpl; auto.

        
  - eexists; split; eauto.
    unfold Values.Val.cmpu_bool, cmpu_bool in *.
    des v2; des v1; autoinv.
    apply match_val_tn.
    repeat red; intros; simpl.
    specialize (MV1 alloc em);
      specialize (MV2 alloc em); inv MV1; inv MV2. simpl.
    unfold Values.Val.of_bool.
    unfold Int64.loword; destr; auto.
    repeat destr_in SemCC.
    apply int_eq_true in Heqb1.
    des (Values.Val.cmp_different_blocks cmp). autoinv.
    rewrite try_norm_rew' with (v:=Vint (if b0 then Int.one else Int.zero)).
    unfold Values.Val.of_bool; repeat red; destr; auto. congruence.
    
    apply Mem.eq_norm; simpl; intros; auto; try congruence.
    constructor; red; simpl; auto; intros alloc em H; auto.
    specialize (MV1 alloc em);
      specialize (MV2 alloc em); inv MV1; inv MV2. simpl.
    unfold Int64.loword; rewrite Heqb1.
    inv H.
    apply valid_pointer in Heqb0.
    generalize (addr_space _ _ Heqb0).
    des cmp; destr; destr; autoinv; simpl; auto.
    apply int_eq_true in Heqb3; rewrite Heqb3 in H0; rewrite Int.unsigned_zero in H0; lia.
    rewrite negb_false_iff in Heqb3.
    apply int_eq_true in Heqb3; rewrite Heqb3 in H0; rewrite Int.unsigned_zero in H0; lia.
    
  - eexists; split; eauto. 
    des v2; des v1; autoinv.
    apply match_val_tn.
    repeat red; intros; simpl.
    specialize (MV1 alloc em);
      specialize (MV2 alloc em); inv MV1; inv MV2. simpl.
    unfold Values.Val.of_bool.
    unfold Int64.loword; destr; auto.
    repeat destr_in SemCC.
    apply int_eq_true in Heqb1.
    des (Values.Val.cmp_different_blocks cmp). autoinv.
    rewrite try_norm_rew' with (v:=Vint (if b0 then Int.one else Int.zero)).
    unfold Values.Val.of_bool; repeat red; destr; auto. congruence.
    
    apply Mem.eq_norm; simpl; intros; auto; try congruence.
    constructor; red; simpl; auto; intros alloc em H; auto.
    specialize (MV1 alloc em);
      specialize (MV2 alloc em); inv MV1; inv MV2. simpl.
    unfold Int64.loword; rewrite Heqb1.
    inv H.
    apply valid_pointer in Heqb0.
    generalize (addr_space _ _ Heqb0).
    des cmp; destr; destr; autoinv; simpl; auto.
    apply int_eq_true in Heqb3; rewrite <- Heqb3 in H0; rewrite Int.unsigned_zero in H0; lia.
    rewrite negb_false_iff in Heqb3.
    apply int_eq_true in Heqb3; rewrite <- Heqb3 in H0; rewrite Int.unsigned_zero in H0; lia.

  -
    unfold Values.Val.of_bool in *.
    eapply sem_binarith_preserved; eauto; clear;
    ba_oblig; des sg; mauto; destr_in H; inv H.

Qed.

Lemma eval_binary:
  forall op tm v1 v1' v2 v2' t1 t2 res,
    match_val v1 v1' ->
    match_val v2 v2' ->
    sem_binary_operation op v1 t1 v2 t2 (Mem.valid_pointer tm) = Some res ->
    exists res',
      (sem_binary_operation_expr op v1' t1 v2' t2) = Some res' /\
      match_val res (try_norm tm res').
Proof.
  destruct op.
  apply add_preserved.
  apply sub_preserved.
  apply mul_preserved.
  apply div_preserved.
  apply mod_preserved.
  apply and_preserved.
  apply or_preserved.
  apply xor_preserved.
  apply shl_preserved.
  apply shr_preserved.
  apply cmp_preserved.
  apply cmp_preserved.
  apply cmp_preserved.
  apply cmp_preserved.
  apply cmp_preserved.
  apply cmp_preserved.
Qed.

Definition ldb (b1 b2:bool) := b1 = true -> b2 = true.

Definition ldov (v1 v2: option val) :=
  match v1, v2 with
    None, _ => True
  | Some v1, Some v2 => Values.Val.lessdef v1 v2
  | _, _ => False
  end.

Lemma unary_vptr_ext:
  forall v v' (EXT:forall b i, ldb (v b i) (v' b i)) u v1 t1,
    ldov (sem_unary_operation v u v1 t1)
         (sem_unary_operation v' u v1 t1).
Proof.
  destruct u; simpl; intros;
  match goal with
    |- context [ldov (?f _ _ _) _] => unfold f; repeat destr; auto
  | |- context [ldov (?f _ _) _] => unfold f; repeat destr; auto
  end.  
  apply EXT in Heqb0; congruence.
Qed.

Lemma ldov_refl:
  forall x, ldov x x.
Proof.
  des x; auto.
Qed.
    

Lemma cast_vptr_ext:
  forall v v' (EXT:forall b i, ldb (v b i) (v' b i)) v1 t1 t2,
    ldov (sem_cast v v1 t1 t2)
         (sem_cast v' v1 t1 t2).
Proof.
  intros. unfold sem_cast.
  destr; try apply ldov_refl; auto.
  des v1; auto. destr. rewrite EXT; auto.
Qed.

Lemma binarith_vptr_ext:
  forall v v' (EXT:forall b i, ldb (v b i) (v' b i)) sem_int sem_long sem_float sem_single  v1 t1 v2 t2,
    ldov (sem_binarith v sem_int sem_long sem_float sem_single v1 t1 v2 t2)
         (sem_binarith v' sem_int sem_long sem_float sem_single v1 t1 v2 t2).
Proof.
  unfold sem_binarith. intros.
  destr. destr.
  generalize (cast_vptr_ext _ _ EXT v1 t1 (binarith_type (classify_binarith t1 t2))).
  generalize (cast_vptr_ext _ _ EXT v2 t2 (binarith_type (classify_binarith t1 t2))).
  rewrite Heqo, Heqo0; simpl.
  destr. destr_in H0.
  destr; try apply ldov_refl; repeat destr; inv H; inv H0;
  apply ldov_refl.
Qed.

Lemma cmp_vptr_ext:
  forall v v' (EXT:forall b i, ldb (v b i) (v' b i)) cmp v1 t1 v2 t2,
    ldov (sem_cmp cmp v1 t1 v2 t2 v) (sem_cmp cmp v1 t1 v2 t2 v').
Proof.
  unfold sem_cmp.
  repeat destr; try apply ldov_refl; auto.
  - unfold Values.Val.cmpu_bool. repeat destr; try apply ldov_refl; auto.
    apply EXT in Heqb0; congruence. 
    apply orb_true_iff in Heqb2; destruct Heqb2 as [A|A]; apply EXT in A; rewrite A in Heqb3; destr.
    rewrite orb_true_r in Heqb3; destr.
    apply EXT in Heqb2; congruence.
    apply EXT in Heqb0; congruence.
    apply EXT in Heqb0; congruence.
    apply EXT in Heqb0; congruence.
    apply andb_true_iff in Heqb2. destruct Heqb2 as [B Heqb2].
    apply orb_true_iff in Heqb2; destruct Heqb2 as [A|A]; apply EXT in A; rewrite A in Heqb3; destr. 
    rewrite orb_true_r in Heqb3; destr.
    apply andb_true_iff in Heqb2. destruct Heqb2 as [B Heqb2]. subst.
    apply EXT in B. rewrite B in Heqb3.
    simpl in *.
    apply orb_true_iff in Heqb2; destruct Heqb2 as [A|A]; apply EXT in A; rewrite A in Heqb3; destr. 
    rewrite orb_true_r in Heqb3; destr.
  - subst. 
    unfold Values.Val.cmpu_bool. repeat destr; auto. try apply ldov_refl; auto.
    apply EXT in Heqb0; congruence.
  - apply EXT in Heqb0; congruence.
  - apply binarith_vptr_ext; auto.
Qed.

Lemma binary_vptr_ext:
  forall v v' (EXT:forall b i, ldb (v b i) (v' b i)) b v1 t1 v2 t2,
    ldov (sem_binary_operation b v1 t1 v2 t2 v)
    (sem_binary_operation b v1 t1 v2 t2 v').
Proof.
  destruct b; simpl; intros;
  try match goal with
        |- ldov (?f _ _ _ _ _) _ => unfold f; repeat destr; try apply ldov_refl; auto
  end;
  try apply binarith_vptr_ext; auto;
  try apply cmp_vptr_ext; auto.
  apply ldov_refl.
  apply ldov_refl.
Qed.

Lemma match_mem_vptr_ext:
  forall m tm (MM: match_mem m tm) b i,
    ldb (CCClight.vptr m b i) (vptr tm b i).
Proof.
  unfold CCClight.vptr, vptr, CCMemory.Mem.valid_pointer, Mem.valid_pointer.
  intros.
  destruct (CCMemory.Mem.perm_dec m b (Int.unsigned i) Cur Nonempty).
  destruct (Mem.perm_dec tm b (Int.unsigned i) Cur Nonempty). red. intuition. 
  inv MM.
  specialize (match_perm0 _ _ _ _ p). exfalso; apply n; auto.
  red; simpl; auto. congruence.
Qed.

Lemma match_val_trans:
  forall v v0 v1
    (LD : Values.Val.lessdef v v0)
    (MV : match_val v0 v1),
    match_val v v1.
Proof.
  red; red; red; intros.
  specialize ((MV alloc em)). destr.
  inv LD; simpl; auto.
Qed.

Lemma match_mem_valid_ptr_ext:
  forall m tm (MM: match_mem m tm) b i,
    ldb (CCMemory.Mem.valid_pointer m b i) (Mem.valid_pointer tm b i).
Proof.
  unfold CCMemory.Mem.valid_pointer, Mem.valid_pointer.
  intros.
  destruct (CCMemory.Mem.perm_dec m b (i) Cur Nonempty).
  destruct (Mem.perm_dec tm b (i) Cur Nonempty). red. intuition. 
  inv MM.
  specialize (match_perm0 _ _ _ _ p). exfalso; apply n; auto.
  red; simpl; auto. congruence.
Qed.

Lemma iob_psale:
  forall l l'
    (LF2 : list_forall2 (match_memval) l l')
    l0
    (PB : CCMemdata.proj_bytes l = Some l0),
  forall al em (* (COMP: Mem.compat_m tm Mem.M32 al) *),
    Vlong (Int64.repr (CCMemdata.int_of_bytes l0)) =
    eSexpr al em (proj_symbolic_aux_le l').
Proof.
  induction 1.
  - simpl. intros; autoinv.
    simpl. auto. 
  - simpl.
    des a1. destr_in PB. autoinv.
    specialize (IHLF2 _ eq_refl al0 em).
    rewrite <- IHLF2. simpl.
    specialize (H al0 em). simpl in H. inv H.
    replace (Int.ltu _ _ ) with true. simpl.
    f_equal.
    rewrite IntFacts.shl'_shl.
    (* replace (two_p _) with 256 by auto. *)
    rewrite Int64.add_is_or.
    apply Int64.same_bits_eq.
    {
      intros.
      rewrite Int64.testbit_repr; auto.
      rewrite Int64.bits_or; auto.
      rewrite Int64.testbit_repr; auto.
      rewrite Int64.bits_shl; auto.
      change (Int64.unsigned _) with 8.
      rewrite Byte.Z_add_is_or; try lia.
      destr.
      setoid_rewrite (Z.mul_pow2_bits_low (CCMemdata.int_of_bytes l) 8 i0). auto. auto.
      rewrite (Byte.Ztestbit_above 8).
      rewrite Int64.testbit_repr; auto.
      rewrite <- Z.mul_pow2_bits. auto. lia. lia.
      apply Byte.unsigned_range. lia.
      intros.
      destruct (zlt j 8).
      setoid_rewrite (Z.mul_pow2_bits_low (CCMemdata.int_of_bytes l) 8 j). apply andb_false_r. lia. 
      rewrite (Byte.Ztestbit_above 8).
      simpl; auto.
      apply Byte.unsigned_range. lia.
    }
    {
      apply Int64.same_bits_eq.
      intros.
      rewrite Int64.bits_and; auto.
      rewrite Int64.testbit_repr; auto.
      rewrite Int64.bits_zero.
      rewrite Int64.bits_shl; auto.
      change (Int64.unsigned _) with 8.
      destr. apply andb_false_r.
      rewrite (Byte.Ztestbit_above 8).
      simpl; auto.
      apply Byte.unsigned_range. lia.
    } 
    change (Int.unsigned _) with 8. lia.
    auto.
Qed.

Lemma decode_int_proj:
  forall l l'
    (LF2 : list_forall2 (match_memval ) l l')
    l0
    (PB : CCMemdata.proj_bytes l = Some l0),
  forall al em ,
    Vlong (Int64.repr (CCMemdata.decode_int l0)) =
    eSexpr al em (proj_symbolic_le l').
Proof.
  intros.
  unfold CCMemdata.decode_int, proj_symbolic_le.
  unfold CCMemdata.rev_if_be, rev_if_be.
  eapply iob_psale; eauto.
Qed.

Lemma int_eq_loword_int64:
  forall i,
    Int.repr i = Int64.loword (Int64.repr i).
Proof.
  intros.
  apply Int.same_bits_eq.
  intros.
  rewrite Int.testbit_repr; auto.
  unfold Int64.loword. rewrite Int.testbit_repr; auto.
  rewrite Int64.unsigned_repr_eq.
  rewrite Int64.modulus_power.
  rewrite Int.Ztestbit_mod_two_p; try lia.
  revert H; IntFacts.unfsize. destr; lia.
  IntFacts.unfsize. lia.   
Qed.


Lemma val_eq_true:
  forall v v',
    proj_sumbool (Val.eq v v') = true -> v = v'.
Proof.
  intros; destruct (Val.eq v v'); auto.
  inv H.
Qed.

Lemma proj_value_proj:
  forall l l'
    (LF2 : list_forall2 (match_memval ) l l')
    al em 
    (* (COMP : Mem.compat_m tm Mem.M32 al) *)
    i 
    (* (EVAL: eSexpr al em (Eval v) = Vint i) *)
    (EVAL : CCMemdata.proj_value CCMemdata.Q32 l = Vint i),
    Values.Val.lessdef (Vint i)
                       (Values.Val.loword (eSexpr al em (proj_symbolic_le l'))).
Proof.
  intros.
  des l.
  des m.
  destruct (Val.eq v v); try congruence.
  simpl in EVAL.
  destr_in EVAL.
  destruct (CCMemdata.quantity_eq CCMemdata.Q32 q) eqn:?; [|simpl in Heqb; congruence].
  simpl in Heqb.
  apply andb_true_iff in Heqb.
  destruct Heqb as [A B].
  repeat destr_in A.
  des l0. des m. 
  apply andb_true_iff in B. destruct B as [B C].
  apply andb_true_iff in B. destruct B as [B D].
  apply andb_true_iff in B. destruct B as [B E].
  repeat destr_in D.
  destr_in C. destr_in C.
  apply andb_true_iff in C. destruct C as [C F].
  apply andb_true_iff in C. destruct C as [C G].
  apply andb_true_iff in C. destruct C as [C H].
  repeat destr_in G.
  des l0. des m. 
  apply andb_true_iff in F. destruct F as [F I].
  apply andb_true_iff in F. destruct F as [F J].
  apply andb_true_iff in F. destruct F as [F K].
  repeat destr_in J. des l.
  inv LF2. inv H4.  inv H6. inv H7. inv H8.
  apply val_eq_true in B.
  apply val_eq_true in C.
  apply val_eq_true in F. subst.
  destruct (CCMemdata.quantity_eq CCMemdata.Q32 q); try easy.
  destruct (CCMemdata.quantity_eq CCMemdata.Q32 q0); try easy.
  destruct (CCMemdata.quantity_eq CCMemdata.Q32 q1); try easy. subst.
  unfold proj_symbolic_le.
  specialize (H2 al em ).
  specialize (H3 al em ).
  specialize (H4 al em ).
  specialize (H5 al em ).
  clear - H2 H3 H4 H5.
  unfold rev_if_be.
  destr.
  {
    unfold expr_of_fragment in *.
    rewrite be_arch in *. rewrite Heqb in *.
    simpl in *.
    Ltac ltu_tac :=
      change (Int.ltu (Int.repr 8) (Int64.iwordsize')) with true in *; simpl in *.
    repeat ltu_tac.
    inv H2; inv H3; inv H4; inv H5.
    simpl.
    repeat ltu_tac.
    rewrite IntFacts.int32_decomp.
    sext32.
  }
  {
    unfold expr_of_fragment in *.
    rewrite be_arch in *. rewrite Heqb in *.
    simpl in *.
    repeat ltu_tac.
    inv H2; inv H3; inv H4; inv H5.
    simpl.
    repeat ltu_tac.
    rewrite IntFacts.int32_decomp.
    sext32.
  }
Qed.


Lemma proj_value_proj_ptr:
  forall l l'
    (LF2 : list_forall2 (match_memval ) l l')
    al em 
   
    b i 
    (* (EVAL: eSexpr al em (Eval v) = Vint i) *)
    (EVAL : CCMemdata.proj_value CCMemdata.Q32 l = Vptr b i),
    Values.Val.lessdef (Vint (Int.add (al b) i))
                       (Values.Val.loword (eSexpr al em (proj_symbolic_le l'))).
Proof.
  intros.
  des l.
  des m.
  destruct (Val.eq v v); try congruence.
  simpl in EVAL.
  destr_in EVAL.
  destruct (CCMemdata.quantity_eq CCMemdata.Q32 q) eqn:?; [|simpl in Heqb0; congruence].
  simpl in Heqb0.
  apply andb_true_iff in Heqb0.
  destruct Heqb0 as [A B].
  repeat destr_in A.
  des l0. des m. 
  apply andb_true_iff in B. destruct B as [B C].
  apply andb_true_iff in B. destruct B as [B D].
  apply andb_true_iff in B. destruct B as [B E].
  repeat destr_in D.
  destr_in C. destr_in C.
  apply andb_true_iff in C. destruct C as [C F].
  apply andb_true_iff in C. destruct C as [C G].
  apply andb_true_iff in C. destruct C as [C H].
  repeat destr_in G.
  des l0. des m. 
  apply andb_true_iff in F. destruct F as [F I].
  apply andb_true_iff in F. destruct F as [F J].
  apply andb_true_iff in F. destruct F as [F K].
  repeat destr_in J. des l.
  inv LF2. inv H4.  inv H6. inv H7. inv H8.
  apply val_eq_true in B.
  apply val_eq_true in C.
  apply val_eq_true in F. subst.
  destruct (CCMemdata.quantity_eq CCMemdata.Q32 q); try easy.
  destruct (CCMemdata.quantity_eq CCMemdata.Q32 q0); try easy.
  destruct (CCMemdata.quantity_eq CCMemdata.Q32 q1); try easy. subst.
  unfold proj_symbolic_le.
  specialize (H2 al em ).
  specialize (H3 al em ).
  specialize (H4 al em ).
  specialize (H5 al em ).
  clear - H2 H3 H4 H5.
  unfold rev_if_be.
  destr.
  {
    unfold expr_of_fragment in *.
    rewrite be_arch in *. rewrite Heqb4 in *.
    simpl in *.
    repeat ltu_tac.
    inv H2; inv H3; inv H4; inv H5.
    simpl.
    repeat ltu_tac.
    rewrite IntFacts.int32_decomp.
    sext32.
  }
  {
    unfold expr_of_fragment in *.
    rewrite be_arch in *. rewrite Heqb4 in *.
    simpl in *.
    repeat ltu_tac.
    inv H2; inv H3; inv H4; inv H5.
    simpl.
    repeat ltu_tac.
    rewrite IntFacts.int32_decomp.
    sext32.
  }
Qed.


Lemma proj_value_proj32_list:
  forall l
    (EVAL : CCMemdata.proj_value CCMemdata.Q32 l <> Vundef),
  exists v,
    l = (CCMemdata.Fragment v CCMemdata.Q32 3) 
          :: (CCMemdata.Fragment v CCMemdata.Q32 2) 
          :: (CCMemdata.Fragment v CCMemdata.Q32 1) 
          :: (CCMemdata.Fragment v CCMemdata.Q32 0) :: nil.
Proof.
  intros.
  des l.
  des m.
  destruct (Val.eq v v); try congruence.
  simpl in EVAL.
  destr_in EVAL.
  destruct (CCMemdata.quantity_eq CCMemdata.Q32 q) eqn:?; [|simpl in Heqb; congruence].
  simpl in Heqb.
  apply andb_true_iff in Heqb.
  destruct Heqb as [A B].
  repeat destr_in A.
  des l0. des m. 
  apply andb_true_iff in B. destruct B as [B C].
  apply andb_true_iff in B. destruct B as [B D].
  apply andb_true_iff in B. destruct B as [B E].
  repeat destr_in D.
  destr_in C. destr_in C.
  apply andb_true_iff in C. destruct C as [C F].
  apply andb_true_iff in C. destruct C as [C G].
  apply andb_true_iff in C. destruct C as [C H].
  repeat destr_in G.
  des l0. des m. 
  apply andb_true_iff in F. destruct F as [F I].
  apply andb_true_iff in F. destruct F as [F J].
  apply andb_true_iff in F. destruct F as [F K].
  repeat destr_in J. des l.
  apply val_eq_true in B.
  apply val_eq_true in C.
  apply val_eq_true in F. subst. subst. subst.
  
  destruct (CCMemdata.quantity_eq CCMemdata.Q32 q); try easy.
  destruct (CCMemdata.quantity_eq CCMemdata.Q32 q0); try easy.
  destruct (CCMemdata.quantity_eq CCMemdata.Q32 q1); try easy. subst.
  eexists; eauto.
Qed.


Lemma decode_val_match:
  forall chunk (Nany: chunk <> Many32 /\ chunk <> Many64) l l',
    list_forall2 (match_memval) l l' ->
    match_val (CCMemdata.decode_val chunk l) (decode_val chunk l').
Proof.
  intros.
  unfold CCMemdata.decode_val.
  red; red; red; simpl; intros.
  destr.
  -
    generalize (decode_int_proj _ _ H _ Heqo alloc em ).
    des chunk; auto; rewrite <- H2; simpl; auto.
    + rewrite int_eq_loword_int64; auto.
    + rewrite int_eq_loword_int64; auto.
    + rewrite int_eq_loword_int64; auto.
    + rewrite int_eq_loword_int64; auto.
    + rewrite int_eq_loword_int64; auto.
    + rewrite Int64.sign_ext_above. auto.
      IntFacts.unfsize;lia.
    + rewrite int_eq_loword_int64; auto.
  - des chunk; auto.
    destr; auto.
    eapply proj_value_proj; eauto.
    eapply proj_value_proj_ptr; eauto.
Qed.

Lemma load_match:
  forall m tm (MM: match_mem m tm)
    loc ofs v chunk (Nany: chunk <> Many32 /\ chunk <> Many64)
    (LOAD1: CCMemory.Mem.load chunk m loc ofs = Some v),
  exists v',
    Mem.load chunk tm loc ofs = Some v' /\
    match_val v v'.
Proof.
  intros.
  Local Transparent CCMemory.Mem.load Mem.load.
  unfold CCMemory.Mem.load in LOAD1.
  destr_in LOAD1. autoinv.
  red in v0. destruct v0 as [RP AC].
  unfold Mem.load.
  assert (Mem.valid_access tm chunk loc ofs Readable).
  {
    red. split.
    - red. intros. eapply match_perm0; eauto.
    - revert AC. unfold CCMemdata.align_chunk, align_chunk. auto.
  }
  destr.
  eexists; split; eauto.
  assert ( forall n ofs,
             list_forall2
               (match_memval )
               (CCMemory.Mem.getN n ofs (CCMemory.Mem.mem_contents m) !! loc)
               (Mem.getN n ofs (Mem.mem_contents tm) !! loc)).
  {
    induction n; simpl; intros; eauto.
    constructor.
    constructor; auto.
  }
  specialize (H2 (CCMemdata.size_chunk_nat chunk) ofs).
  revert H2. replace (size_chunk_nat chunk) with (CCMemdata.size_chunk_nat chunk) by (des chunk).
  match goal with
    |- list_forall2 _ ?a ?b -> _ => generalize a; generalize b
  end.
  intros. eapply decode_val_match. auto. auto.
Qed.

Lemma size_chunks:
  forall chunk,
    CCMemdata.size_chunk_nat chunk =
    size_chunk_nat chunk.
Proof.
  des chunk.
Qed.

Lemma list_repeat_undef_rev:
  forall n,
    rev (list_repeat n CCMemdata.Undef) =
    list_repeat n CCMemdata.Undef.
Proof.
  induction n; simpl; intros; eauto.
  rewrite IHn.
  clear.
  induction n; simpl; intros; eauto.
  rewrite IHn. auto.
Qed.


Lemma list_repeat_undef_rev_rib:
  forall n,
    list_repeat n CCMemdata.Undef =
    rev (rev_if_be (list_repeat n CCMemdata.Undef)).
Proof.
  unfold rev_if_be; destr;
  rewrite ! list_repeat_undef_rev; auto.
Qed.

Lemma lf2_rev:
  forall {A B} (P : A -> B -> Prop) l l',
    list_forall2 P l l' ->
    list_forall2 P (rev l) (rev l').
Proof.
  induction 1; simpl; intros.
  constructor.
  apply list_forall2_app; auto.
  constructor; [|constructor]. auto.
Qed.

Lemma lf2_rib:
  forall {A B} (P : A -> B -> Prop) l l',
    list_forall2 P l l' ->
    list_forall2 P (rev_if_be l) (rev_if_be l').
Proof.
  unfold rev_if_be.
  intros. destr.
  apply lf2_rev; auto.
Qed.

Lemma map_rib:
  forall f l,
    map f (CCMemdata.rev_if_be l) = CCMemdata.rev_if_be (map f l).
Proof.
  induction l; simpl; intros; auto.
Qed.

Fixpoint rev_inj_symbolic' n e t  :=
  match n with
    O => nil
  | S m => rev_inj_symbolic' m e t ++ Symbolic e t m :: nil
  end.

Lemma rev_inj_symbolic'_ok:
  forall n e t,
    rev_inj_symbolic' n e t = rev (inj_symbolic' n e t).
Proof.
  induction n; simpl; intros; auto.
  rewrite IHn; auto.
Qed.


Ltac encode_eq_setup MV :=
  repeat red; 
  let al := fresh "al" in
  let em := fresh "em" in
  intros al em;
  specialize (MV al em); simpl in *; inv MV;
  unfold convert_t; simpl; apply Values.Val.lessdef_same; f_equal; auto;
  repeat ltu_tac; f_equal;
  apply Int64.same_bits_eq;
  intros.


Lemma bit_shiftr:
  forall i i0,
    0 <= i0 < Int64.zwordsize - 8 ->
    Z.testbit (Z.shiftr (Int64.unsigned (Int64.repr i)) 8) i0 =
    Z.testbit i (i0 + 8).
Proof.
  intros.
  rewrite Z.shiftr_spec; auto.
  rewrite <- (Int64.testbit_repr (Int64.unsigned _)).
  rewrite Int64.repr_unsigned.
  rewrite Int64.testbit_repr. auto. lia. lia. lia.
Qed.


Ltac encode_eq_first :=
  rewrite Int64.testbit_repr; auto;
  rewrite Int64.bits_and; auto;
  rewrite ! Int64.testbit_repr; auto;
  rewrite (Int.Ztestbit_two_p_m1 8) by lia;
  destr; [|rewrite (Byte.Ztestbit_above 8); 
            [rewrite andb_false_r; auto|
             apply Byte.unsigned_range| lia]];
  rewrite <- Byte.testbit_repr; auto;
  rewrite Byte.repr_unsigned;
  rewrite Byte.testbit_repr; auto; rewrite andb_true_r; auto;
  rewrite <- ! (Byte.Zshiftr_div_two_p _ 8) by lia;
  rewrite ! Z.shiftr_spec by lia; auto;
  unfold Int64.shru';
  rewrite ! Int64.testbit_repr; auto;
  repeat rewrite bit_shiftr by
      (IntFacts.unfsize; change (Int.unsigned (Int.repr 8)) with 8; lia).


Lemma bytes_match_memval:
  forall n (N: (n = 1 \/ n = 2 \/ n = 4 \/ n = 8)%nat) i e
    (MV : match_val (Vint i) e)
    ,
    list_forall2
      (match_memval )
      (map CCMemdata.Byte (CCMemdata.bytes_of_int n (Int.unsigned i)))
      (rev
         (inj_symbolic'
            n
            (Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint e) None)).
Proof.
  intros. rewrite <- rev_inj_symbolic'_ok.
  revert i e MV.
  destr; subst.
  - simpl. repeat constructor.
    encode_eq_setup MV. encode_eq_first.
  - simpl. repeat constructor;
      encode_eq_setup MV; encode_eq_first; auto.
  - simpl. repeat constructor;
      encode_eq_setup MV; encode_eq_first; auto.
  - simpl. repeat constructor;
      encode_eq_setup MV; encode_eq_first; auto.
Qed.


Lemma bytes_match_memval_long:
  forall n (N: (n = 1 \/ n = 2 \/ n = 4 \/ n = 8)%nat) i e
    (MV : match_val (Vlong i) e)
    ,
    list_forall2
      (match_memval)
      (map CCMemdata.Byte (CCMemdata.bytes_of_int n (Int64.unsigned i)))
      (rev
         (inj_symbolic'
            n
            e None)).
Proof.
  intros. rewrite <- rev_inj_symbolic'_ok.
  revert i e MV.
  destr; subst.
  - simpl. repeat constructor.
    encode_eq_setup MV.
    encode_eq_first.
  - simpl.
    repeat constructor;
      encode_eq_setup MV;
      encode_eq_first.
    change (Int.unsigned (Int.repr 8)) with 8.
    rewrite Z.shiftr_spec; auto.
  - simpl.
    repeat constructor;
      encode_eq_setup MV;
      encode_eq_first;
    rewrite Z.shiftr_spec; auto; lia.
  - simpl.
    repeat constructor;
      encode_eq_setup MV;
      encode_eq_first;
    rewrite Z.shiftr_spec; auto; lia.
Qed.

Lemma bytes_match_memval_float:
  forall n (N: (n = 1 \/ n = 2 \/ n = 4 \/ n = 8)%nat) f e
    (MV : match_val (Vfloat f) e)
  ,
    
   list_forall2 (match_memval )
     (CCMemdata.inj_bytes
        (CCMemdata.encode_int n (Int64.unsigned (Float.to_bits f))))
     (rev (inj_symbolic' n
        (Eunop OpBitsofdouble Tfloat e) None)).
Proof.
  intros. rewrite <- rev_inj_symbolic'_ok.
  revert f e MV.
  destr; subst.
  - simpl. repeat constructor.
    encode_eq_setup MV.
    encode_eq_first.
  - simpl.
    repeat constructor;
      encode_eq_setup MV;
      encode_eq_first.
    change (Int.unsigned (Int.repr 8)) with 8.
    rewrite Z.shiftr_spec; auto.
  - simpl.
    repeat constructor;
      encode_eq_setup MV;
      encode_eq_first;
    rewrite Z.shiftr_spec; auto; lia.
  - simpl.
    repeat constructor;
      encode_eq_setup MV;
      encode_eq_first;
    rewrite Z.shiftr_spec; auto; lia.
Qed.


Lemma bytes_match_memval_single:
  forall n (N: (n = 1 \/ n = 2 \/ n = 4 \/ n = 8)%nat) f e
    (MV : match_val (Vsingle f) e),
   list_forall2 (match_memval )
     (CCMemdata.inj_bytes
        (CCMemdata.encode_int n (Int.unsigned (Float32.to_bits f))))
     (rev (inj_symbolic' n
        (Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint
           (Eunop OpBitsofsingle Tsingle e)) None)).
Proof.
  intros. rewrite <- rev_inj_symbolic'_ok.
  revert f e MV.
  destr; subst.
  - simpl. repeat constructor.
    encode_eq_setup MV.
    encode_eq_first.
  - simpl.
    repeat constructor;
      encode_eq_setup MV;
      encode_eq_first.
    change (Int.unsigned (Int.repr 8)) with 8. auto.
  - simpl.
    repeat constructor;
      encode_eq_setup MV;
      encode_eq_first; auto.
  - simpl.
    repeat constructor;
      encode_eq_setup MV;
      encode_eq_first; auto.
Qed.




Lemma bytes_match_memval_ptr:
  forall b i e
    (MV : match_val (Vptr b i) e),
    list_forall2 (match_memval )
                 (CCMemdata.inj_value CCMemdata.Q32 (Vptr b i))
                 (inj_symbolic
                    4
                    (Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint e) None).
Proof.
  intros. setoid_rewrite <- rev_inj_symbolic'_ok.
  simpl. repeat constructor; encode_eq_setup MV.
Qed.

Lemma lf2_repeat_undef:
  forall n e t,
    list_forall2 (match_memval )
                 (list_repeat n CCMemdata.Undef)
                 (inj_symbolic n e t).
Proof.
  induction n; simpl; intros; eauto.
  - unfold inj_symbolic; simpl; try constructor.
  - unfold inj_symbolic; simpl; try constructor.
    setoid_rewrite (list_repeat_undef_rev_rib (S n)).
    apply lf2_rev.
    apply lf2_rib. simpl. constructor. constructor.
    unfold inj_symbolic in IHn.
    eapply lf2_rib in IHn.
    apply lf2_rev in IHn. rewrite rev_rev_if_be_involutive in IHn.
    rewrite <- list_repeat_undef_rev_rib in IHn. eauto.
Qed.

Lemma match_val_lf2_match_memval:
  forall v e chunk (N: chunk <> Many32 /\ chunk <> Many64),
    match_val v e ->
    list_forall2
      (match_memval)
      (CCMemdata.encode_val chunk v)
      (encode_val chunk e).
Proof.
  unfold encode_val, CCMemdata.encode_val.
  intros.
  rewrite size_chunks.
  assert (LF2U := lf2_repeat_undef (size_chunk_nat chunk) (to_bits chunk e)).
  des v.
  - des chunk; auto.
  - des chunk; auto; unfold size_chunk_nat; simpl;
    unfold Pos.to_nat; simpl.
    + apply bytes_match_memval; auto.
    + apply bytes_match_memval; auto.
    + apply bytes_match_memval; auto.
    + apply bytes_match_memval; auto.
    + apply bytes_match_memval; auto.
  -  des chunk; auto.
     apply bytes_match_memval_long; auto.
  -  des chunk; auto.
     apply bytes_match_memval_float; auto.
  -  des chunk; auto. 
     apply bytes_match_memval_single; auto.
  - des chunk; auto.
    apply bytes_match_memval_ptr; auto.
Qed.

Lemma memval_rel:
  forall l l0
    (LF2: list_forall2 (match_memval) l0 l)
    t t0 o ofs
    (IN: ofs <= o < ofs + Z.of_nat (length l)),
     match_memval (ZMap.get o (CCMemory.Mem.setN l0 ofs t0))
                  (ZMap.get o (Mem.setN l ofs t)).
Proof.
  induction 1; simpl; intros; eauto. 
  lia.
  assert (ofs = o \/ ofs+1 <= o < ofs + Z.pos (Pos.of_succ_nat (length bl))).
  lia.
  destruct H0; subst.
  - rewrite CCMemory.Mem.setN_outside by lia.
    rewrite Mem.setN_outside by lia.
    rewrite ! ZMap.gss; auto.
  - apply IHLF2.  lia. 
Qed.

Lemma store_match:
  forall m tm (MM: match_mem m tm)
    loc ofs v chunk (Nany: chunk <> Many32 /\ chunk <> Many64)
    e
    (MV: match_val v e) m'
    (STORE: CCMemory.Mem.store chunk m loc ofs v = Some m'),
  exists tm',
     Mem.store chunk tm loc ofs (try_norm tm e) = Some tm' /\
    match_mem m' tm'.
Proof.
  intros.
  Local Transparent CCMemory.Mem.store Mem.store.
  unfold CCMemory.Mem.store in STORE.
  destr_in STORE. autoinv. 
  red in v0. destruct v0 as [RP AC].
  unfold Mem.store.
  assert (Mem.valid_access tm chunk loc ofs Writable).
  {
    red. split.
    - red. intros. eapply match_perm0; eauto.
    - revert AC. unfold CCMemdata.align_chunk, align_chunk. auto.
  }
  destr.
  eexists; split; eauto.
  constructor; simpl; auto.
  intros.
  rewrite ! PMap.gsspec.
  destr; eauto. subst.
  assert (Decidable.decidable (o < ofs \/ o >= ofs + Z.of_nat (length (encode_val chunk (try_norm tm e))))).
  red; lia.
  destruct H2.
  rewrite CCMemory.Mem.setN_outside; auto.
  rewrite Mem.setN_outside; auto.
  - rewrite CCMemdata.encode_val_length.
    rewrite encode_val_length in H2.
    des chunk; lia.
  -
    generalize (match_val_lf2_match_memval  v (try_norm tm e) chunk (conj H H0) (match_val_tn _ _ _ MV)).

    assert (ofs <= o < ofs + Z.of_nat (length (encode_val chunk (try_norm tm e)))).
    lia.
    revert H3.
    generalize (CCMemdata.encode_val chunk v).
    generalize (encode_val chunk (try_norm tm e)).
    generalize (CCMemory.Mem.mem_contents m) !! loc.
    generalize (Mem.mem_contents tm) !! loc.
    intros; eapply memval_rel; eauto.
Qed.

Lemma loadv_match:
  forall m tm (MM: match_mem m tm)
    loc ofs se
    (MV : match_val (Vptr loc ofs) se)
    chunk (Nany: chunk <> Many32 /\ chunk <> Many64) v
    (LOAD: CCMemory.Mem.loadv chunk m (Vptr loc ofs) = Some v),
  exists e, 
    Mem.loadv chunk tm se = Some e /\
    match_val v e.
Proof.
  intros.
  simpl in LOAD.
  unfold Mem.loadv.
  replace (Mem.mem_norm tm se) with (Vptr loc ofs).
  - eapply load_match; eauto.
  - symmetry.
    eapply Mem.eq_norm.
    constructor; red; simpl; auto. 
    intros; apply MV.
    congruence.
Qed.

Lemma storev_match:
  forall m tm (MM: match_mem m tm)
    loc ofs se
    (MV : match_val (Vptr loc ofs) se)
    v e
    (MV1: match_val v e)
    chunk (Nany: chunk <> Many32 /\ chunk <> Many64) m'
    (LOAD: CCMemory.Mem.storev chunk m (Vptr loc ofs) v = Some m'),
  exists tm', 
    Mem.storev chunk tm se (try_norm tm e) = Some tm' /\
    match_mem m' tm'.
Proof.
  intros.
  simpl in LOAD.
  unfold Mem.storev.
  replace (Mem.mem_norm tm se) with (Vptr loc ofs).
  - eapply store_match; eauto.
  - symmetry.
    eapply Mem.eq_norm.
    constructor.
    red; intros. apply MV.
    congruence.
Qed.

Lemma deref_loc_match:
  forall m tm (MM: match_mem m tm)
    loc ofs se
    (MV : match_val (Vptr loc ofs) se)
    t v
    (DL : deref_loc t m loc ofs v),
  exists e, 
    Clight2.deref_loc t tm se e /\
    match_val v e.
Proof.
  intros.
  inv DL.
  - eapply loadv_match in H0; eauto.
    dex; destr.
    eexists; split. econstructor; eauto.
    apply match_val_tn; auto.
    des t. des i; des s. des i; des s. des f. des f.
  - eexists; split; [econstructor 2; simpl; eauto| eauto].
    apply match_val_tn; auto.
  - eexists; split; [econstructor 3; simpl; eauto| eauto].
    apply match_val_tn; auto.
Qed.

Lemma loadbytes_match:
  forall m tm (MM: match_mem m tm) n b ofs vl
    (LB: CCMemory.Mem.loadbytes m b ofs (Z.of_nat n) = Some vl),
  exists vl',
    Mem.loadbytes tm b ofs (Z.of_nat n) = Some vl' /\
    list_forall2 (match_memval) vl vl'.
Proof.
  induction n; simpl; intros; eauto.
  - Transparent CCMemory.Mem.loadbytes Mem.loadbytes.
    unfold CCMemory.Mem.loadbytes, Mem.loadbytes in *.
    destr_in LB.
    inv LB.
    destr. 
    eexists; split; eauto. constructor.
    exfalso; apply n.
    red; intros.
    apply match_perm0. auto.
  - unfold CCMemory.Mem.loadbytes, Mem.loadbytes in *.
    destr_in LB.
    inv LB. 
    destr. 
    + eexists; split; eauto. rewrite SuccNat2Pos.id_succ. simpl.
      constructor; auto.
      specialize (IHn b (ofs+1)).
      destr_in IHn.
      specialize (IHn _ eq_refl).
      dex; destr.
      destr_in H.
      * inv H.
        rewrite nat_of_Z_of_nat in H0.
        auto.
      * clear - n0 r.
        exfalso; apply n0. red; intros. apply r. lia.
    + 
      exfalso;  apply n0.
      red; intros.
      apply match_perm0. auto.
Qed.

Require Import PP.PpsimplZ.

Lemma storebytes_match:
  forall m tm (MM: match_mem m tm)  vl el 
    (LF: list_forall2 (match_memval) vl el)
    b ofs m'
    (LB: CCMemory.Mem.storebytes m b ofs vl = Some m'),
  exists tm',
    Mem.storebytes tm b ofs el = Some tm' /\
    match_mem m' tm'.
Proof.
  induction 2; simpl; intros; eauto.
  - Transparent CCMemory.Mem.storebytes Mem.storebytes.
    unfold CCMemory.Mem.storebytes, Mem.storebytes in *.
    destr_in LB.
    inv LB. 
    destr. 
    eexists; split; eauto.
    + constructor; simpl; auto.
      intros.
      rewrite ! PMap.gsspec.
      destr; subst; eauto.
    + exfalso;  apply n.
      red; intros.
      apply match_perm0. auto.
  - unfold CCMemory.Mem.storebytes, Mem.storebytes in *.
    destr_in LB.
    inv LB. 
    destr. 
    + eexists; split; eauto.
      constructor; auto. simpl.
      intros. rewrite ! PMap.gsspec.
      destr; eauto.
      clear IHLF.
      assert (Decidable.decidable ( ofs + 1 <= o < ofs + 1 + Z.of_nat (length bl))).
      red; lia.
      destruct H0.
      eapply memval_rel.
      subst.
      clear - LF. auto.
      auto.
      rewrite CCMemory.Mem.setN_outside.
      rewrite Mem.setN_outside.
      destruct (zeq o ofs).
      subst.
      rewrite ! ZMap.gss.
      eauto. 
      rewrite ! ZMap.gso by auto. eauto.
      lia.
      erewrite list_forall2_length; eauto. lia.

    + exfalso. apply n.
      red; intros.
      apply match_perm0.
      apply r.
      erewrite list_forall2_length; eauto. Qed.


Lemma tnorm_se:
  forall m cm (COMP: Mem.compat_m m Mem.M32 cm) em e,
    eSexpr cm em (try_norm m e) = eSexpr cm em e.
Proof.
  intros.
  generalize (Mem.norm_ld m e _ eq_refl _ em COMP). intro LD.
  destruct (is_val_dec e).
  des e.
  rewrite try_norm_val; auto.
  rewrite try_norm_eq; auto.
  destr;
  match goal with
    |- context [Mem.mem_norm ?m ?e] => generalize (LD); intro LD'; simpl in LD'; inv LD';
                                      des (Mem.mem_norm m e)
  end;
  generalize (LD); intro LD'; simpl in LD'; des (Mem.mem_norm m e); inv LD'; try congruence.
Qed.

Lemma storev_tn:
  forall chunk m addr v,
    Mem.storev chunk m addr v = Mem.storev chunk m (try_norm m addr) v.
Proof.
  unfold Mem.storev. intros.
  rewrite try_norm_eq.
  des (Mem.mem_norm m addr); try rewrite Heqv0; repeat rewrite Mem.norm_val in *;
  auto.
Qed.

Lemma assign_loc_match:
  forall m tm (MM: match_mem m tm)
    loc ofs se
    (MV : match_val (Vptr loc ofs) se)
    t v e
    (MV': match_val v e)
    m'
    (DL : assign_loc t m loc ofs v m'),
  exists tm', 
    Clight2.assign_loc t tm se e tm' /\
    match_mem m' tm'.
Proof.
  intros.
  inv DL.
  - eapply storev_match in H0; eauto.
    dex.
    eexists; split; eauto.
    econstructor; eauto. destr; eauto. destr.
    des t. des i; des s. des i; des s. des f. des f.
  -
    replace (Ctypes.sizeof t) with (Z.of_nat (nat_of_Z (Ctypes.sizeof t))) in H3.
    eapply loadbytes_match in H3; eauto.
    destruct H3 as [vl' [LB' LF2]].
    eapply storebytes_match in H4; eauto.
    destruct H4 as [tm' [SB MM']].
    rewrite nat_of_Z_eq in LB'.
    eexists; split; eauto.
    econstructor 2; simpl. auto.
    eexact H0. eexact H1. eauto. eauto. eauto.
    + intros;  apply Mem.eq_norm.
      constructor; simpl; auto.
      red; intros. eapply MV'; eauto.
      congruence.
    + intros;  apply Mem.eq_norm.
      constructor.
      red; simpl; intros. eapply MV; eauto.
      congruence.
    + apply Ctypes.sizeof_pos.
    + apply nat_of_Z_eq. generalize (Ctypes.sizeof_pos t). lia.
Qed.


Section EXPR_EVAL.
  Variable ge : genv.
  Let tge := genv_of_ccgenv ge.
  Variable m : CCMemory.mem.
  Variable tm : Memory.mem.
  Hypothesis MEMeq: match_mem m tm.
  Variable e : env.
  Variable le: temp_env.
  Variable tle: Clight2.temp_env.
  Hypothesis TEMPeq: match_temp_env le tle.

  Lemma find_symbol_translated:
    forall id l,
      CCGlobalenvs.Genv.find_symbol ge id = Some l ->
      Globalenvs.Genv.find_symbol tge id = Some l.
  Proof.
    unfold CCGlobalenvs.Genv.find_symbol, Globalenvs.Genv.find_symbol.

    unfold tge, genv_of_ccgenv. intros; simpl.
    destr.
  Qed.
  
  Lemma eval_simpl_expr:
    forall a v,
      eval_expr ge e le m a v ->
      exists tv, Clight2.eval_expr tge e tle tm a tv /\ match_val v tv
  with
  eval_simpl_lvalue:
    forall a b ofs,
      eval_lvalue ge e le m a b ofs ->
      exists se, Clight2.eval_lvalue tge e tle tm a se
            /\ match_val (Vptr b ofs) se.
  Proof.
    - destruct 1; simpl; intros.
      + eexists; split. econstructor; simpl. red. red.  simpl; auto.
      + eexists; split. econstructor; simpl. red. red. simpl; auto.
      + eexists; split. econstructor; simpl. red. red.  simpl; auto.
      + eexists; split. econstructor; simpl. red.  red. simpl; auto.
      + apply TEMPeq in H.  dex; destr. eexists; split. econstructor; simpl. eauto.
        auto.
      + apply eval_simpl_lvalue in H.
        destruct H as [se [EL MV]].
        eexists; split. econstructor; simpl; eauto. auto.
      + apply eval_simpl_expr in H.
        destruct H as [tv [EE MV]].
        eexists; split.
        econstructor; simpl; eauto.
        generalize (unary_vptr_ext _ _ (match_mem_vptr_ext _ _ MEMeq) op v1 (ClightSyntax.typeof a)).
        rewrite H0. simpl. destr_cond_match; try easy.
        intro LD.
        eapply eval_unary in Heqo; eauto.
        eapply match_val_trans; eauto.
      + apply eval_simpl_expr in H.
        apply eval_simpl_expr in H0.
        destruct H as [tv1 [EE1 MV1]].
        destruct H0 as [tv2 [EE2 MV2]].
        generalize (binary_vptr_ext _ _ (match_mem_valid_ptr_ext _ _ MEMeq) op v1 (ClightSyntax.typeof a1)
                                    v2 (ClightSyntax.typeof a2)).
        rewrite H1. simpl.
        intro LD. destr_in LD.
        eapply eval_binary in Heqo; eauto.
        destruct Heqo as [res' [SBO MV]].
        eexists; split.
        econstructor; simpl; eauto.
        eapply match_val_trans; eauto.
      + apply eval_simpl_expr in H.
        destruct H as [tv [EE MV]].
        generalize (cast_vptr_ext _ _ (match_mem_vptr_ext _ _ MEMeq) v1 (ClightSyntax.typeof a) ty).
        rewrite H0; simpl. destr_cond_match; try easy.
        intro LD.
        eapply sem_cast_preserved in Heqo; eauto.
        destruct Heqo as [res' [SBO MV']].
        eexists; split.
        econstructor; simpl; eauto.
        eapply match_val_trans; eauto.
      + apply eval_simpl_lvalue in H. destruct H as [se [ELV MV]].
        eapply deref_loc_match in H0; eauto. dex; destr.
        eexists; split. econstructor; simpl.  eauto. eauto. auto.
    - destruct 1; simpl; intros.
      + eexists; split. econstructor; eauto.
        repeat red; intros; auto.
      + eexists; split. econstructor 2; eauto.
        erewrite find_symbol_translated; eauto.
        repeat red; intros; auto.
      + apply eval_simpl_expr in H.
        dex; destr.
        eexists; split. econstructor. eauto. auto.
      + apply eval_simpl_expr in H.
        dex; destr.
        eexists; split. econstructor. eauto. eauto. eauto.
        eapply match_val_tn.
        repeat red; intros; auto.
        specialize (H3 alloc em). destr.
        inv H3. rewrite <- Int.add_assoc. simpl; auto.
      + apply eval_simpl_expr in H.
        dex; destr.
        eexists; split. eapply Clight2.eval_Efield_union; eauto.
        apply match_val_tn; auto. 
  Qed.

End EXPR_EVAL.

Lemma cast_preserved:
  forall m tm (MEMeq: match_mem m tm)
    v2 t2 t1 v tv
    (MV: match_val v2 tv)
    (SC: sem_cast (CCClight.vptr m) v2 t2 t1 = Some v),
  exists e,
    sem_cast_expr tv t2 t1 = Some e /\
    match_val v (try_norm tm e).
Proof.
  intros.
  generalize (cast_vptr_ext _ _ (match_mem_vptr_ext _ _ MEMeq) v2 t2 t1). rewrite SC.
  simpl. destr_cond_match; try easy.
  exploit sem_cast_preserved; eauto.
  intros [res' [SCE MVO]].
  eexists; split; eauto.
  eapply match_val_trans; eauto.
Qed.

Lemma eval_simpl_exprlist:
  forall ge m tm (MM: match_mem m tm)
    e le tle (MTE: match_temp_env le tle)
    al vargs tyargs
    (EEL: eval_exprlist ge e le m al tyargs vargs),
  exists tvl,
    Clight2.eval_exprlist (genv_of_ccgenv ge) e tle tm al tyargs tvl /\
    list_forall2 (match_val) vargs tvl.
Proof.
  induction 3; simpl; intros.
  - eexists; split. econstructor; eauto. constructor.
  - destruct IHEEL as [tvl [EEL' LF2]].
    eapply eval_simpl_expr in H; eauto.
    destruct H as [tv [EE MV]].
    eapply cast_preserved in H0; eauto.
    destruct H0 as [e0 [SCE MV']].
    eexists; split.
    econstructor. eauto. eauto. eauto.
    constructor; auto.
Qed.

Lemma match_temp_env_set:
  forall le tle
    (TEMPeq : match_temp_env le tle)
    v tv
    (MV : match_val v tv) id,
    match_temp_env (PTree.set id v le) (PTree.set id tv tle).
Proof.
  red; intros.
  rewrite PTree.gsspec in *.
  destr.
  - eexists; split; eauto. autoinv; auto.
  - apply TEMPeq; auto.
Qed.


Definition genv_valid {F V} (ge: CCGlobalenvs.Genv.t F V) tm :=
  forall b (fd:F),
    CCGlobalenvs.Genv.find_funct_ptr ge b = Some fd ->
    Mem.in_bound_m 0 tm b /\ ~ Mem.is_dynamic_block tm b.

Lemma find_funct_translated:
  forall ge m tm (MM: match_mem m tm) vf fd tvf
    (GenvValid: genv_valid ge tm)
    (MV: match_val vf tvf)    
    (FF : CCGlobalenvs.Genv.find_funct ge vf = Some fd),
    Globalenvs.Genv.find_funct tm (genv_of_ccgenv ge) tvf = Some (cfundef_of_fundef fd).
Proof.
  intros.
  unfold CCGlobalenvs.Genv.find_funct in FF.
  destruct vf eqn:?; try easy.
  destruct (Int.eq_dec i Int.zero); try easy.
  subst.
  unfold Globalenvs.Genv.find_funct. 
  erewrite match_val_norm; eauto.
  destruct (Int.eq_dec); try congruence.
  clear - FF.
  unfold CCGlobalenvs.Genv.find_funct_ptr in FF.
  unfold Globalenvs.Genv.find_funct_ptr.
  unfold genv_of_ccgenv; simpl.
  des ge.
  unfold tree_of_tree. rewrite PTree.gmap.
  rewrite FF. auto.
Qed.

Lemma boe_eq:
  forall e,
    blocks_of_env e = Clight2.blocks_of_env e.
Proof.
  unfold Clight2.blocks_of_env, blocks_of_env.
  unfold Clight2.block_of_binding, block_of_binding. auto.
Qed.

Lemma free_contents:
  forall m b lo hi m'
    (F : CCMemory.Mem.free m b lo hi = Some m'),
    CCMemory.Mem.mem_contents m' = CCMemory.Mem.mem_contents m.
Proof.
  Transparent CCMemory.Mem.free.
  unfold CCMemory.Mem.free.
  destr. destr_in F.
  autoinv. simpl. auto.
Qed.

Lemma free_match:
  forall m tm
    (MM: match_mem m tm)
    m' b lo hi
    (F: CCMemory.Mem.free m b lo hi = Some m')
    (Bnds: Mem.bounds_of_block tm b = (lo, hi)),
  exists tm',
    Mem.free tm b lo hi = Some tm' /\
    match_mem m' tm'.
Proof.
  intros.
  destruct (Mem.range_perm_free tm b lo hi) as [tm' F'].
  red; intros.
  eapply match_perm; eauto.
  eapply CCMemory.Mem.free_range_perm; eauto.
  unfold Mem.has_bounds; rewrite Bnds. repeat destruct zeq; destr.
  exists tm'; split; auto.
  constructor; simpl; intros; eauto.
  - erewrite free_contents;eauto.
    erewrite Mem.free_contents; eauto.
    generalize (match_contents _ _ MM b0 o). auto.
  - erewrite CCMemory.Mem.nextblock_free; eauto.
    erewrite Mem.nextblock_free; eauto. inv MM; auto.
  -
    assert (Decidable.decidable (b = b0 /\ lo <= o < hi)).
    red. destruct (peq b b0); subst.
    destruct (NormaliseSpec.in_bound_dec (lo,hi) o). red in H0; simpl in H0. auto.
    unfold NormaliseSpec.in_bound in H0; right; simpl in H0. lia.
    right; destr.
    destruct H0.
    destr; subst.
    eapply CCMemory.Mem.perm_free_2 in F; eauto. apply F in H; easy.
    eapply CCMemory.Mem.perm_free_3 in H; eauto.
    eapply match_perm in H. 2: eauto.
    eapply Mem.perm_free_1; eauto.
    destruct (peq b b0); destr. subst. 
    lia.
Qed.

Lemma free_list_match:
  forall m tm (MM: match_mem m tm)
    m' e
    (lnr: list_norepet (map fst (map fst (blocks_of_env e))))
    (FL : CCMemory.Mem.free_list m (blocks_of_env e) = Some m')
    (Bnds: forall b lo hi,
        In (b,lo,hi) (blocks_of_env e) ->
        Mem.bounds_of_block tm b = (lo,hi)),
  exists tm',
    Mem.free_list tm (Clight2.blocks_of_env e) = Some tm' /\
    match_mem m' tm'.
Proof.
  intros.
  rewrite <- boe_eq.
  revert FL Bnds.
  generalize (blocks_of_env e) m tm MM m' lnr .
  
  clear. induction l; simpl; intros; eauto.
  eexists; split; eauto. inv FL; auto.
  des a; des p.
  destr_in FL.
  eapply free_match in Heqo; eauto.
  2: constructor; auto.
  destruct Heqo as [tm' [A B]]; rewrite A.
  eapply IHl; eauto. inv lnr; auto.
  intros.
  erewrite <- Bnds; eauto.
  eapply Mem.bounds_free; eauto.
  inv lnr.
  rewrite map_map in H2. rewrite in_map_iff in H2.
  intro; subst. apply H2.
  exists (b0,lo,hi); split; simpl; auto.
Qed.



Lemma volatile_cc:
  forall ge b,
    CCEvents.block_is_volatile ge b =
    Events.block_is_volatile (genv_of_ccgenv ge) b.
Proof.
  unfold CCEvents.block_is_volatile, Events.block_is_volatile in *.
  unfold CCGlobalenvs.Genv.find_var_info, Globalenvs.Genv.find_var_info in *.
  unfold genv_of_ccgenv; simpl. intro; des ge.
Qed.

Lemma vol_load_match:
  forall ge chunk m b ofs t vres
    (VLOAD: CCEvents.volatile_load ge chunk m b ofs t vres)
    tm (MM : match_mem m tm)
    b1 (MV : match_val (Vptr b ofs) b1),
  exists vres',
    Events.volatile_load (genv_of_ccgenv ge) chunk tm (try_norm tm b1) t vres' /\
    match_val vres vres'.
Proof.
  intros.
  assert (VB: Mem.in_bound_m (Int.unsigned ofs) tm b).
  {
    inv VLOAD.
    red; intros. eapply Mem.perm_bounds; eauto.
    eapply match_perm; eauto. apply H1. des chunk; lia.
    red; intros. eapply Mem.perm_bounds; eauto.
    eapply match_perm; eauto.
    eapply CCMemory.Mem.load_valid_access in H0. apply H0.
    des chunk; lia.
  }
  inv VLOAD.
  - eapply find_symbol_translated in H0.
    exists (Val.load_result chunk (Eval v)).
    split. 
    econstructor.
    erewrite try_norm_rew_ptr.
    apply Mem.norm_val. 
    eapply match_val_norm; eauto.
    auto.
    rewrite <- volatile_cc; auto.
    auto.
    inv H2; constructor.
    eapply find_symbol_translated in H5; auto.
    assert (chunk <> Many32 /\ chunk <> Many64).
    des chunk; inv H2.
    eauto.
    clear - H2.
    repeat red; simpl; intros.
    des chunk; des v; auto.
    sext32. sext32.
    rewrite Int64.sign_ext_above. auto. IntFacts.unfsize;lia.
    eauto.
  - eapply load_match in H0; eauto.
    destruct H0 as [v' [LOAD MV']].
    eexists; split.
    econstructor; simpl; eauto.
    apply match_val_norm; auto.
    apply match_val_tn; auto.
    rewrite <- volatile_cc; auto.    
    auto.
Qed.

Lemma vol_store_match:
  forall ge chunk m b ofs v t m'
    (VSTORE : CCEvents.volatile_store ge chunk m b ofs v t m')
    b1 tm
    (MM: match_mem m tm)
    (MV : match_val (Vptr b ofs) b1)
    b0
    (MV' : match_val v b0),
  exists tm',
     Events.volatile_store (genv_of_ccgenv ge) chunk tm (try_norm tm b1) (try_norm tm b0) t tm' /\
     match_mem m' tm'.
Proof.
  intros.
  inv VSTORE.
  - rewrite volatile_cc in H.
    eapply find_symbol_translated in H0; eauto.
    eexists; split; eauto.
    econstructor; eauto. erewrite try_norm_rew_ptr.
    apply Mem.norm_val.
    apply match_val_norm; auto.
    eapply Mem.perm_bounds; eauto.
    eapply match_perm; eauto.
    apply H1. des chunk; lia.
    assert (Decidable.decidable (exists b i, v = Vptr b i)).
    red; des v; try now (right; intro; dex; destr).
    left; eexists; eexists; eauto.
    destruct H3.
    + dex; destr. subst.
      des chunk; inv H2.
      rewrite try_norm_eq.
      rewrite (Mem.same_eval_eqm) with (v1:=b0) (v2:=Eval (Vptr b2 i)).
      rewrite Mem.norm_val. simpl.
      rewrite (Mem.same_eval_eqm) with (v2:=Eval (Vptr b2 i)).
      rewrite Mem.norm_val. constructor. eapply find_symbol_translated; eauto.
      econstructor; eauto.
      red; intros; simpl; sext32.
      red; intros. specialize (MV' cm em); inv MV'; auto.
    + 
      rewrite Mem.eq_norm with (v:=Values.Val.load_result chunk v); simpl; intros; auto.
      * des chunk; inv H2; constructor; auto;
        des v. exfalso; apply H3; repeat eexists; eauto.
      * constructor; simpl; auto.
        red; intros. specialize (MV' cm em).
        revert MV'.
        simpl.
        rewrite <- (tnorm_se _ _ Pcm em b0).
        des chunk; des v; inv MV'; simpl; mauto.
        rewrite Int64.sign_ext_above. auto. IntFacts.unfsize;lia.
      * inv H2; congruence.
  - rewrite volatile_cc in H.
    eapply store_match in H0; eauto.
    destruct H0 as [tm' [STORE MM']].
    eexists; split.
    econstructor; eauto. apply match_val_norm; eauto. apply match_val_tn. auto.
    auto. 
Qed.

Lemma loadbytes_match':
  forall m tm
    (MM: match_mem m tm)
    n b ofs vl
    (Pos: n >= 0)
    (lb: CCMemory.Mem.loadbytes m b ofs n = Some vl),
  exists vl',
    Mem.loadbytes tm b ofs n = Some vl' /\
    list_forall2 (match_memval) vl vl'.
Proof.
  intros.
  generalize (nat_of_Z_eq _ Pos). intro A; rewrite <- A in *.
  eapply loadbytes_match; eauto.
Qed.




Lemma norm_match_val:
  forall m v x,
    v <> Vundef ->
    match_val v x ->
    Mem.mem_norm m x = v.
Proof.
  intros.
  apply Mem.eq_norm; simpl; auto.
  constructor. red; simpl; intros.
  apply H0.
Qed.

Lemma eventval_match_match:
  forall ge args targs vargs,
    CCEvents.eventval_match ge args targs vargs ->
    forall eargs,
      match_val vargs eargs ->
      forall m tm,
        match_mem m tm ->
        Events.eventval_match (genv_of_ccgenv ge) args targs (Mem.mem_norm tm eargs).
Proof.
  intros.
  generalize (fun pf => norm_match_val tm _ _ pf H0). intro A.
  inv H; rewrite A by destr; constructor.
  eapply find_symbol_translated; eauto.
Qed.

Lemma eventval_list_match_match:
  forall ge args targs vargs,
    CCEvents.eventval_list_match ge args targs vargs ->
    forall eargs,
      list_forall2 match_val vargs eargs ->
      forall m tm,
        match_mem m tm ->
        Events.eventval_list_match (genv_of_ccgenv ge) args targs (map (Mem.mem_norm tm) eargs).
Proof.
  induction 1; simpl; intros; eauto.
  inv H.  constructor.
  inv H1.
  simpl; constructor; eauto.
  eapply eventval_match_match; eauto.
Qed.

Lemma norm_try_norm:
  forall m v,
    Mem.mem_norm m (try_norm m v) = Mem.mem_norm m v.
Proof.
  intros.
  erewrite try_norm_eq.
  des (Mem.mem_norm m v);  apply Mem.norm_val.
Qed.

Lemma map_norm_try_norm:
  forall m v,
    map (Mem.mem_norm m) (map (try_norm m) v) = map (Mem.mem_norm m) v.
Proof.
  induction v; simpl; intros. auto.
  f_equal; eauto using norm_try_norm.
Qed.

Lemma extcall_match:
  forall ef ge vargs m t vres m'
    tm eargs 
    (MM: match_mem m tm)
    (EC : CCEvents.external_call ef ge vargs m t vres m')
    (EVL: list_forall2 (match_val) vargs eargs),
  exists eres tm',
    Events.external_call ef (genv_of_ccgenv ge) (map (try_norm tm) eargs) tm t eres tm' /\
    match_val vres eres /\
    match_mem m' tm'.
Proof.
  intros.
  destruct ef; simpl in *.
  - eapply external_functions_sem_match; eauto.
  - eapply external_functions_sem_match; eauto.
  - inv EC. inv EVL. inv H4.
    eapply vol_load_match in H; eauto.
    destruct H as [vres' [VL MV]].
    eexists; eexists; split.
    econstructor.  eauto. auto.
  - inv EC. inv EVL. inv H4. inv H6.
    eapply vol_store_match in H; eauto.
    destruct H as [tm' [VS MM']].
    eexists; eexists; repSplit.
    econstructor. eauto.
    repeat red; auto. auto.
  - inv EC. inv EVL.
    exploit vol_load_match; eauto.
    repeat red; intros. apply Values.Val.lessdef_same. reflexivity.
    intros [vres' [VL MV]].
    eexists; eexists; repSplit; eauto.
    econstructor. eapply find_symbol_translated; eauto.
    rewrite try_norm_val in VL. auto. simpl; auto.
  - inv EC. inv EVL. inv H5.
    eapply vol_store_match in H0; eauto.
    destruct H0 as [tm' [VS MM']].
    eexists; eexists; split. simpl. 
    econstructor. eapply find_symbol_translated; eauto. rewrite try_norm_val in VS.  eauto. simpl; auto.
    split; auto.
    repeat red; simpl; auto.    repeat red; simpl; auto.
  - eapply malloc_match; eauto.
  - eapply mfree_match; eauto.
  - inv EC.
    destruct (zlt 0 sz).
    + assert (sz > 0) by lia.
      inv EVL. inv H12. inv H14.
      eapply loadbytes_match' in H5; eauto.
      destruct H5 as [vl' [LB LF2]].
      eapply storebytes_match in H6; eauto.
      destruct H6 as [tm' [SB MM']].
      exists (Eval Vundef), tm'.
      repSplit.
      * econstructor. auto. auto. auto. eapply H2; auto. eapply H3; auto. eauto. eauto.
        eauto.
        apply match_val_norm; auto.
        apply match_val_tn; auto.
        apply match_val_norm; auto.
        apply match_val_tn; auto.
      * repeat red; auto.
      * auto.
    + assert (sz = 0) by lia. subst.
      inv EVL. inv H11. inv H13.
      eexists; eexists; repSplit.
      * econstructor 2; eauto.
      * repeat red; auto.
      * rewrite CCMemory.Mem.loadbytes_empty in H5 by lia. inv H5.
        constructor; inv MM; intros; eauto with mem.
        erewrite CCMemory.Mem.storebytes_mem_contents; eauto.
        simpl.
        rewrite ! PMap.gsspec.
        destr_cond_match; subst; eauto.
        erewrite CCMemory.Mem.nextblock_storebytes; eauto.
  - inv EC.
    exploit eventval_list_match_match; eauto. intros.
    eexists; eexists; repSplit.
    econstructor. 
    rewrite map_norm_try_norm. eauto.
    constructor.
    auto.
  - inv EC. inv EVL. inv H4.
    simpl.
    assert (Events.eventval_match  (genv_of_ccgenv ge) arg targ vres).
    inv H; try constructor. eapply find_symbol_translated; eauto.
    assert (same_eval (Eval vres) b1).
    red; intros. specialize (H2 cm em). simpl in *. inv H2. auto. des vres. inv H0.
    assert (try_norm tm b1 = Eval vres).
    erewrite try_norm_rew. 3: symmetry; eauto. auto. intro; subst; inv H0.
    eexists; eexists; repSplit.
    + econstructor.
      rewrite H3, Mem.norm_val. auto.
    + rewrite H3.  apply match_val_eval.
    + auto.
  - eapply inline_assembly_match; eauto.
Qed.

Ltac transf_eval :=
  repeat match goal with
           H : eval_expr ?ge ?e ?le ?m ?a ?v |- _ =>
           eapply eval_simpl_expr in H; eauto;
           let tv := fresh "tv" in
           let EE := fresh "EE" in
           let MV := fresh "MV" in
           destruct H as [tv [EE MV]]
         | H : eval_lvalue ?ge ?e ?le ?m ?a ?loc ?ofs |- _ =>
           eapply eval_simpl_lvalue in H; eauto;
           let tv := fresh "se" in
           let EE := fresh "EL" in
           let MV := fresh "MV" in
           destruct H as [tv [EE MV]]
         | H : eval_exprlist ?ge ?e ?le ?m ?al ?tyargs ?vargs |- _ =>
           eapply eval_simpl_exprlist in H; eauto;
           let tv := fresh "tvl" in
           let EE := fresh "EEL" in
           let MV := fresh "MVL" in
           destruct H as [tv [EE MV]]
         | H : sem_cast ?vptr ?v2 ?t2 ?t1 = Some ?v |- _ =>
           (eapply cast_preserved in H; eauto); [idtac];
           let tv := fresh "se" in
           let EE := fresh "SC" in
           let MV := fresh "MV" in
           destruct H as [tv [EE MV]]
         | H : assign_loc ?t ?m ?loc ?ofs ?v ?m' |- _ =>
           (eapply assign_loc_match in H; eauto); [idtac];
           let tv := fresh "tm'" in
           let EE := fresh "AL" in
           let MV := fresh "MM" in
           destruct H as [tv [EE MV]]
         | H : CCEvents.external_call ?ef ?ge ?vargs ?m ?t ?vres ?m' |- _ =>
           (eapply extcall_match in H; eauto); [idtac];
           let eres := fresh "eres" in
           let tm := fresh "tm" in
           let EC := fresh "EC" in
           let MV := fresh "MV" in
           let MM := fresh "MM" in
           destruct H as [eres [tm [EC [MV MM]]]]
         end.

Lemma mte_set_opttemp:
  forall vres eres le tle optid
    (MV: match_val vres eres)
    (MTE: match_temp_env le tle),
    match_temp_env (set_opttemp optid vres le)
                   (Clight2.set_opttemp optid eres tle).
Proof.
  intros.
  des optid.
  apply match_temp_env_set; auto.
Qed.

Lemma bool_val_preserved:
  forall m tm (MM: match_mem m tm) v1 t b
    (BV : bool_val (CCClight.vptr m) v1 t = Some b)
    tv
    (MV : match_val v1 tv),
    Mem.mem_norm tm (bool_expr tv t) = Values.Val.of_bool b.
Proof.
  intros.
  unfold bool_val, bool_expr in *.
  apply Mem.eq_norm; auto.
  - constructor; red; simpl; intros; auto.
    specialize (MV cm em);  destr; des v1; autoinv; inv MV;
    simpl; destr; mauto.
    rewrite Float.cmp_ne_eq in Heqb. rewrite Heqb. simpl; auto.
    rewrite Float.cmp_ne_eq in Heqb. rewrite Heqb. simpl; auto.
    rewrite Float32.cmp_ne_eq in Heqb. rewrite Heqb. simpl; auto.
    rewrite Float32.cmp_ne_eq in Heqb. rewrite Heqb. simpl; auto.
    destr_in BV; autoinv. simpl; auto.
    destr_in BV; autoinv.
    apply negb_false_iff in Heqb1.
    apply int_eq_true in Heqb1.
    inv Pcm.
    unfold CCClight.vptr in Heqb0.
    unfold CCMemory.Mem.valid_pointer in Heqb0.
    destruct (CCMemory.Mem.perm_dec m b0 (Int.unsigned i) Cur Nonempty); try now destr.
    clear Heqb0.    apply match_perm0 in p.
    apply Mem.perm_bounds in p.
    apply addr_space  in p.
    rewrite Heqb1 in p.
    rewrite Int.unsigned_zero in p. lia.
  - des b; inv H.
Qed.

Lemma bool_val_preserved':
  forall m tm (MM: match_mem m tm) v1 t b
    (BV : bool_val (CCClight.vptr m) v1 t = Some b)
    tv
    (MV : match_val v1 tv),
    Mem.mem_norm tm (bool_expr tv t) = Vint (if b then Int.one else Int.zero).
Proof.
  intros.
  eapply bool_val_preserved in BV; eauto.
  des b.
Qed.

Definition zerons := fun _:ident => O.


Lemma sem_switch_arg_preserved:
  forall v t z tm e
    (MV: match_val v e)
    (SSA: CopGeneric.sem_switch_arg v t = Some z),
    sem_switch_arg_expr tm e t = Some z.
Proof.
  unfold CopGeneric.sem_switch_arg, sem_switch_arg_expr.
  destr.
  destr; des v; autoinv.
  rewrite Mem.eq_norm with (v:=Vint i) ; destr; constructor; destr; eauto. red; intros; apply MV.
  rewrite Mem.eq_norm with (v:=Vlong i) ; destr; constructor; destr; eauto. red; intros; apply MV.
Qed.

Lemma assign_loc_bounds:
  forall t m a v m'
    (AL: Clight2.assign_loc t m a v m') b,
    Mem.bounds_of_block m b = Mem.bounds_of_block m' b.
Proof.
  intros.
  inv AL.
  eapply Mem.storev_bounds; eauto. 
  eapply Mem.bounds_of_block_storebytes; eauto.
Qed.


Section PRES.

  Variable ge : CCGlobalenvs.Genv.t CCClight.fundef Ctypes.type.
  Inductive match_cont tm : CCClight.cont -> Clight2.cont -> block -> block -> Prop :=
  | mc_stop : forall lo hi, Ple lo hi ->
                       Ple hi (Mem.nextblock tm) ->
                       match_cont tm Kstop Clight2.Kstop lo hi
  | mc_seq: forall k tk s lo hi (PLE: Ple lo hi)
              (PLE: Ple hi (Mem.nextblock tm))
              (MC: match_cont tm k tk lo hi),
      match_cont tm (Kseq s k) (Clight2.Kseq s tk) lo hi
            | mc_loop1:forall k tk s s' lo hi (PLE: Ple lo hi)
                         (PLE: Ple hi (Mem.nextblock tm))
                         (MC: match_cont tm k tk lo hi),
      match_cont tm (Kloop1 s s' k) (Clight2.Kloop1 s s' tk) lo hi
            | mc_loop2:forall k tk s s' lo hi (PLE: Ple lo hi)
                         (PLE: Ple hi (Mem.nextblock tm))
                         (MC: match_cont tm k tk lo hi),
      match_cont tm (Kloop2 s s' k) (Clight2.Kloop2 s s' tk) lo hi
            | mc_switch: forall k tk lo hi (PLE: Ple lo hi)
                           (PLE: Ple hi (Mem.nextblock tm))
                           (MC: match_cont tm k tk lo hi),
      match_cont tm (Kswitch k) (Clight2.Kswitch tk) lo hi
  | mc_call :
      forall oi f e le tle k tk lo hi
        (MC: match_cont tm k tk lo hi)
        (MTE: match_temp_env le tle)
        (LNR: list_norepet (map fst (map fst (blocks_of_env e))))
        (Bnds: forall (b : block) (lo hi : Z),
            In (b, lo, hi) (blocks_of_env e) ->
            Mem.bounds_of_block tm b = (lo, hi))
        hi' (PLE: Ple hi hi')
        (PLE: Ple hi' (Mem.nextblock tm))
        (BoundsStack: forall b : block,
            In b (map fst (map fst (blocks_of_env e))) ->
            Ple hi b /\ Plt b hi' /\
            CCGlobalenvs.Genv.find_funct_ptr ge b = None /\
            ~ Mem.is_dynamic_block tm b),
        match_cont tm (Kcall oi f e le k)
                   (Clight2.Kcall oi (cfunction_of_function f) e tle tk) hi hi'.

  Lemma match_call_cont:
    forall tm k tk lo hi,
      match_cont tm k tk lo hi ->
      match_cont tm (call_cont k) (Clight2.call_cont tk) lo hi.
  Proof.
    induction 1; simpl; intros; eauto.
    constructor; auto.
    econstructor; eauto.
  Qed.

  Lemma call_cont_match_cont:
    forall tm k tk lo hi,
      match_cont tm k tk lo hi ->
      is_call_cont k ->
      Clight2.is_call_cont tk.
  Proof.
    induction 1; simpl; intros; eauto.
  Qed.

  Lemma match_cont_same_bounds:
    forall tm tm' k tk lo hi
      (SB: forall b, Plt b hi -> ~ Mem.is_dynamic_block tm b ->
                Mem.bounds_of_block tm b = Mem.bounds_of_block tm' b)
      (SNB: Ple (Mem.nextblock tm) (Mem.nextblock tm'))
      (FYN: forall b, Mem.valid_block tm b -> ~ Mem.is_dynamic_block tm b -> ~ Mem.is_dynamic_block tm' b)
      (MC: match_cont tm k tk lo hi),
      match_cont tm' k tk lo hi.
  Proof.
    induction 4; intros; econstructor; eauto; try xomega.
    - apply IHMC. intros; eapply SB; eauto. xomega.
    - intros.
      exploit Bnds; eauto. intro A; rewrite <- A. symmetry.
      trim (BoundsStack b). 
      + rewrite map_map, in_map_iff; simpl.
        eexists; split; eauto. destr.
      + apply SB; auto. xomega.
        destr.
    - intros.
      exploit BoundsStack. eauto. destr.
      eapply FYN in H4; eauto.
      red; xomega.
  Qed.

  Lemma match_cont_ple:
    forall tm k tk lo hi (MC : match_cont tm k tk lo hi),
      Ple lo hi.
  Proof.
    intros. inv MC; auto.
  Qed.


  Lemma match_cont_ple':
    forall tm k tk lo hi (MC : match_cont tm k tk lo hi),
      Ple hi (Mem.nextblock tm).
  Proof.
    intros. inv MC; auto.
  Qed.

  
  Section FIND_LABEL.

    Variable lbl: ident.
    Variable tm: Memory.mem.

    Definition same_label
               (sk: option (ClightSyntax.statement * cont))
               (stk: option (ClightSyntax.statement * Clight2.cont)) lo hi : Prop :=
      match sk, stk with
        None, None => True
      | Some (s,k), Some (s', tk) => s = s' /\ match_cont tm k tk lo hi
      | _, _ => False
      end.
    
    Lemma match_find_label:
      forall s k tk lo hi,
        match_cont tm k tk lo hi ->
        same_label (find_label lbl s k) (Clight2.find_label lbl s tk) lo hi
    with match_find_label_ls:
           forall ls k tk lo hi,
             match_cont tm k tk lo hi ->
             same_label (find_label_ls lbl ls k) (Clight2.find_label_ls lbl ls tk) lo hi.
    Proof.
      - clear match_find_label.
        induction s; simpl; intros until hi; intros MC; auto.
        +
          exploit (IHs1 (Kseq s2 k) (Clight2.Kseq s2 tk) ).
          constructor; eauto. eapply match_cont_ple; eauto.
          eapply match_cont_ple'; eauto. 
          destr. des p. destr_in H.
          destr_in H. eapply IHs2; eauto.
        + 
          generalize (IHs1 k tk _ _ MC).
          destr.
          * des p. destr_in H.
          * destr. eapply IHs2; eauto.
        +
          exploit (IHs1 (Kloop1 s1 s2 k) (Clight2.Kloop1 s1 s2 tk)).
          econstructor; eauto. eapply match_cont_ple; eauto.
          eapply match_cont_ple'; eauto. 
          destr.
          * des p. destr_in H. 
          * destr_in H. eapply IHs2; eauto.
            econstructor; eauto. eapply match_cont_ple; eauto.
            eapply match_cont_ple'; eauto. 
        +
          eapply match_find_label_ls. econstructor; eauto.
          eapply match_cont_ple; eauto.
          eapply match_cont_ple'; eauto. 
        +
          destruct (ident_eq lbl l).
          red; auto. 
          eapply IHs; eauto.
      - clear match_find_label_ls.
        induction ls; simpl; intros.
        auto.
        exploit (match_find_label s  (Kseq (seq_of_labeled_statement ls) k)
                                  (Clight2.Kseq (Clight2.seq_of_labeled_statement ls) tk)).
        econstructor; eauto. eapply match_cont_ple; eauto.
        eapply match_cont_ple'; eauto. 
        destr.
        * des p. destr_in H0. 
        * destr_in H0. eapply IHls; eauto. 
    Qed.

  End FIND_LABEL.


  Inductive match_states : CCClight.state -> Clight2.state -> Prop :=
    ms_states :
      forall f s k tk e le tle m tm lo hi hi'
        (TEMPeq: match_temp_env le tle)
        (MEMeq: match_mem m tm)
        (MC: match_cont tm k tk lo hi)
        (GV: genv_valid ge tm)
        (lnr: list_norepet (map fst (map fst (blocks_of_env e))))
        (Bnds: forall b lo hi,
            In (b,lo,hi) (blocks_of_env e) ->
            Mem.bounds_of_block tm b = (lo,hi))
        (PLE: Ple hi hi')
        (PLE': Ple hi' (Mem.nextblock tm))
        (BlocksStack:
           forall b,
             In b (map fst (map fst (blocks_of_env e))) ->
             Ple hi b /\ Plt b hi' /\
             CCGlobalenvs.Genv.find_funct_ptr ge b = None /\ ~ Mem.is_dynamic_block tm b)
      ,
        match_states
          (State f s k e le m)
          (Clight2.State (cfunction_of_function f) s tk e tle tm)
  | ms_callstates:
      forall fd vl el k tk m tm
        (MEMeq: match_mem m tm)
        (GV: genv_valid ge tm)
        (LVeq: list_forall2 (match_val) vl el)
        lo hi
        (MC: match_cont tm k tk lo hi),
        match_states
          (Callstate fd vl k m)
          (Clight2.Callstate (cfundef_of_fundef fd) el tk tm)
  | ms_returnstates:
      forall v e k tk m tm
        (MV: match_val v e)
        lo hi
        (MC: match_cont tm k tk lo hi)
        (MM: match_mem m tm)
        (GV: genv_valid ge tm),
        match_states (Returnstate v k m)
                     (Clight2.Returnstate e tk tm).

  (* Lemma match_cont_same_bounds_ple: *)
  (*   forall tm tm' k tk lo hi *)
  (*     (SB: forall b, Plt b hi -> Mem.bounds_of_block tm b = Mem.bounds_of_block tm' b) *)
  (*     (SNB: Ple (Mem.nextblock tm) (Mem.nextblock tm')) *)
  (*     (MC: match_cont tm k tk lo hi), *)
  (*     match_cont tm' k tk lo hi. *)
  (* Proof. *)
  (*   induction 3; intros; econstructor; eauto; try xomega. *)
  (*   eapply IHMC; eauto. intros; apply SB; eauto. xomega.  *)
  (*   intros. *)

  (*   specialize (Bnds _ _ _ H). *)
  (*   rewrite SB in Bnds; auto. *)
  (*   destruct (BoundsStack b). *)
  (*   rewrite map_map, in_map_iff. eexists; split; eauto. simpl; auto. *)
  (*   destr.  *)
  (* Qed. *)

  Lemma tnorm_mult:
    forall m e,
      try_norm m (try_norm m e) = try_norm m e.
  Proof.
    intros.
    rewrite ! try_norm_eq.
    des (Mem.mem_norm m e); try rewrite Heqv; auto;
    rewrite Mem.norm_val; auto.
  Qed.
  
  Lemma assign_loc_match':
    forall tm se t e tm',
      Clight2.assign_loc t tm se e tm' ->
      Clight2.assign_loc t tm se (try_norm tm e) tm'.
  Proof.
    intros.
    inv H.
    - econstructor 1; eauto. rewrite tnorm_mult; auto.
    - econstructor 2. auto. eexact AL'. eexact AL. eexact NOOV.
      eauto. eauto. 
      intros; erewrite try_norm_rew_ptr; eauto.
      apply Mem.norm_val. 
      auto. 
  Qed.
  
  Lemma try_norm_sc:
    forall m m'
      (SB: forall b, Mem.bounds_of_block m b = Mem.bounds_of_block m' b)
      (SM: forall b, Mem.nat_mask m b = Mem.nat_mask m' b)
      e,
      try_norm m e = try_norm m' e.
  Proof.
    intros.
    destruct (is_val_dec e).
    rewrite ! try_norm_val; auto.
    rewrite ! try_norm_eq; auto.
    rewrite ! (Mem.norm_same_compat _ _ _ SB SM). auto.
  Qed.

  Lemma try_norm_sc_list:
    forall m m'
      (SB: forall b, Mem.bounds_of_block m b = Mem.bounds_of_block m' b)
      (SM: forall b, Mem.nat_mask m b = Mem.nat_mask m' b)
      e,
      map (try_norm m) e = map (try_norm m') e.
  Proof.
    induction e; auto.
    simpl.
    rewrite IHe.
    erewrite try_norm_sc; eauto.
  Qed.
  
  
  Lemma assign_loc_mask:
    forall t m a v m'
      (AL: Clight2.assign_loc t m a v m') b,
      Mem.nat_mask m b = Mem.nat_mask m' b.
  Proof.
    intros.
    inv AL.
    unfold Mem.storev in STORE; destr_in STORE. eapply Mem.nat_mask_store; eauto. 
    eapply Mem.nat_mask_storebytes; eauto.
  Qed.

  Lemma bind_parameters_match:
    forall vargs el 
      (LVeq : list_forall2 match_val vargs el)
      e m0 p m1 m0'
      (BP : bind_parameters e m0 p vargs m1)
      (MM : match_mem m0 m0'),
    exists m1',
      Clight2.bind_parameters e m0' p (map (try_norm m0') el) m1' /\
      match_mem m1 m1'.
  Proof.
    induction 1; simpl; intros; eauto.
    - inv BP. eexists; split; eauto. constructor.
    - inv BP.
      eapply assign_loc_match in H5; eauto.
      2: apply match_val_eval.
      destruct H5 as [tm' [AL MM']].
      specialize (IHLVeq _ _ _ _ _ H7 MM').
      destruct IHLVeq as [m1' [BP MM'']].
      eexists; split; eauto.
      econstructor; eauto. apply assign_loc_match'. eauto.
      erewrite try_norm_sc_list; eauto.
      eapply assign_loc_bounds; eauto.
      eapply assign_loc_mask; eauto.
  Qed.


  Lemma assign_loc_nb:
    forall t m a e m',
      Clight2.assign_loc t m a e m' ->
      Ple (Mem.nextblock m) (Mem.nextblock m').
  Proof.
    destruct 1; simpl; intros.
    erewrite <- Mem.nextblock_storev; eauto. xomega.
    erewrite <- Mem.nextblock_storebytes; eauto. xomega.
  Qed.

  Lemma bind_parameters_bound:
    forall e m f l m'
      (BP: Clight2.bind_parameters e m f l m')
      b,
      Mem.bounds_of_block m b = Mem.bounds_of_block m' b.
  Proof.
    induction 1; simpl; intros. auto.
    rewrite <- IHBP.
    eapply assign_loc_bounds; eauto.
  Qed.
  Lemma bind_parameters_nextblock:
    forall e m f l m'
      (BP: Clight2.bind_parameters e m f l m'),
      Ple (Mem.nextblock m) (Mem.nextblock  m').
  Proof.
    induction 1; simpl; intros. auto.
    xomega.
    eapply assign_loc_nb in AL. xomega. 
  Qed.
  Lemma alloc_variables_nextblock:
    forall e m vars e' m',
      Clight2.alloc_variables e m vars e' m' ->
      Ple (Mem.nextblock m) (Mem.nextblock m').
  Proof.
    induction 1.
    apply Ple_refl.
    eapply Ple_trans; eauto. exploit Mem.nextblock_alloc; eauto. intros EQ; rewrite EQ. apply Ple_succ. 
  Qed.
  Lemma match_cont_higher:
    forall tm k tk lo hi
      (MC : match_cont tm k tk lo hi),
      match_cont tm k tk lo (Mem.nextblock tm).
  Proof.
    induction 1; simpl; intros; econstructor; eauto; try xomega.
    intros.
    apply BoundsStack in H.
    destr. xomega.
  Qed.

  Lemma alloc_variables_in_not_in_vars:
    forall e m1 vars e2 m2
      (AV: Clight2.alloc_variables e m1 vars e2 m2)
      id0 (N: ~ In id0 (var_names vars)),
      e2 ! id0 = e ! id0.
  Proof.
    induction 1; simpl; intros; auto.
    rewrite IHAV; auto.
    rewrite PTree.gso; auto.
  Qed.

  Lemma alloc_variables_bounds_other:
    forall e m1 vars e2 m2
      (AV : Clight2.alloc_variables e m1 vars e2 m2)
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
    destr. subst. inv H.
    eapply Mem.valid_new_block; eauto.
    eapply Mem.valid_block_alloc; eauto.
  Qed.

  Lemma alloc_variables_bounds:
    forall e m vars m' e' 
      (AV: Clight2.alloc_variables e m vars e' m')
      (Valid: forall id b ty, e!id = Some (b,ty) -> Mem.valid_block m b)
      id b ty
      (I: In id (var_names vars))
      (E: e' ! id = Some (b,ty)),
      Mem.bounds_of_block m' b = (0, Ctypes.sizeof ty).
  Proof.
    induction 1; simpl; intros; auto. easy.
    destruct (in_dec peq id0 (var_names vars)).
    - eapply IHAV; eauto.
      intros id1 b0 ty1.
      rewrite PTree.gsspec. clear I.  destr; subst.
      inv H.
      eapply Mem.valid_new_block; eauto.
      eapply Mem.valid_block_alloc; eauto.
    - destr. subst.
      erewrite alloc_variables_bounds_other; eauto.
      exploit alloc_variables_in_not_in_vars; eauto.
      rewrite PTree.gss. 
      rewrite E; intro A; inv A.
      erewrite Mem.bounds_of_block_alloc; eauto. f_equal.
      apply Zmax_r. apply Zge_le, Ctypes.sizeof_pos.
      intros id b0 ty1. rewrite PTree.gsspec.
      destr. inv H. eapply Mem.valid_new_block; eauto.
      eapply Mem.valid_block_alloc; eauto.
  Qed.


  Require Import Permutation.

  Lemma blocks_set_elements_permut:
    forall e id b1 ty
      (nex: e ! id = None)
      (nex': ~ exists id t, e ! id = Some (b1,t))
      (injective: forall id1 id2 b1 b2 ty1 ty2,
          (e ! id1 = Some (b1, ty1) ->
           e ! id2 = Some (b2, ty2) -> id1 <> id2 -> b1 <> b2)),
      Permutation (blocks_of_env (PTree.set id (b1, ty) e))
                  ((b1,0,Ctypes.sizeof ty) :: blocks_of_env e ).
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
      inv H.
      des (peq i i0).
      apply B in IN.
      apply B in IN'.
      rewrite PTree.gsspec in IN, IN'.
      des (peq i0 id). 
      generalize (B _ _ IN) (B _ _ IN'). 
      rewrite ! PTree.gsspec.
      des (peq i0 id). des (peq i id).
      inv H0.
      apply nex'; exists i, t; auto.
      des (peq i id).
      inv H.
      apply nex'; exists i0, t0; auto.
      exploit injective. eexact H. eexact H0. auto. auto. auto.
    - constructor.
      + intro IN.
        apply in_map_iff in IN. dex; destr.
        des x. des p. inv H.
        generalize (D _ _ H0).
        intro. apply nex'; exists i, t; auto.
      + eapply list_map_norepet. eapply PTree_Properties.list_norepet_map; eauto.
        intros x y IN IN' DIFF. des x; des y. des p; des p0.
        inv H.
        des (peq i i0).
        apply D in IN.
        apply D in IN'.
        congruence.
        generalize (D _ _ IN) (D _ _ IN'). intros.
        exploit injective. eexact H. eexact H0. auto. auto. auto.
    - split; intros IN.
      + rewrite in_map_iff in IN. dex; destr. des x0. des p.
        apply B in H0. rewrite PTree.gsspec in H0.
        des (peq i id).
        right.
        apply C in H0.
        apply in_map_iff. exists (i, (b,t)); auto.
      + destruct IN.
        * subst.
          apply in_map_iff. exists (id, (b1,ty)); split; auto.
          apply (A _ _ (PTree.gss _ _ _)).
        * apply in_map_iff in H.
          apply in_map_iff.
          dex; destr.
          exists x0; split; auto.
          des x0.
          apply D in H1.
          apply A.
          rewrite PTree.gso; auto.
          congruence.
  Qed.

  
  Lemma alloc_variables_lnr:
    forall l 
      (lnr : list_norepet (map fst l))
      ei m e m0
      (Espec: forall i b t, ei ! i = Some (b,t) ->
                       Plt b (Mem.nextblock m))
      (NotAlready: forall i, In i (map fst l) -> ei ! i = None)
      (lnr': list_norepet (map fst (map fst (blocks_of_env ei))))
      (EI_inj:    forall (id1 id2 : positive) (b1 b2 : block) (ty1 ty2 : Ctypes.type),
          ei ! id1 = Some (b1, ty1) ->
          ei ! id2 = Some (b2, ty2) -> id1 <> id2 -> b1 <> b2)
      (AV : Clight2.alloc_variables ei m l e m0),
      list_norepet (map fst (map fst (blocks_of_env e))).
  Proof.
    induction l; simpl; intros.
    inv AV. auto. 
    inv AV. simpl in *.
    trim IHl. inv lnr; auto.
    eapply IHl in AV0.
    - auto.
    - intros i b t. rewrite PTree.gsspec.
      destr; autoinv; eauto.
      eapply Mem.valid_new_block in ALLOC. auto.
      apply Espec in H.
      apply Mem.nextblock_alloc in ALLOC. rewrite ALLOC. xomega.
    - intros.
      rewrite PTree.gsspec. destr; subst; eauto.
      inv lnr; congruence.
    - eapply Mem.alloc_result in ALLOC. subst.
      eapply permutation_norepet with
      (l:=(Mem.nextblock m)::(map fst (map fst (blocks_of_env ei)))).
      Focus 2.
      + constructor; auto.
        intro IN. unfold blocks_of_env in IN.
        rewrite ! map_map in IN. rewrite in_map_iff in IN.
        destruct IN as [x [EQ IN]].
        destruct x. apply PTree.elements_complete in IN.
        des p.
        eapply Espec in IN. subst. xomega.
      + generalize (blocks_set_elements_permut ei id (Mem.nextblock m) ty). intro P.
        trim P. apply NotAlready. auto.
        trim P. intro NEX; dex. apply Espec in NEX. xomega.
        trim P. intros. eapply EI_inj; eauto.
        eapply Permutation_map with (f:= fst) in P.
        eapply Permutation_map with (f:= fst) in P.
        simpl in P.
        apply Permutation_sym; auto.
    - intros.
      rewrite PTree.gsspec in H, H0.
      destr_in H; destr_in H0; autoinv.
      apply Espec in H0. apply Mem.alloc_result in ALLOC. subst; xomega.
      apply Espec in H. apply Mem.alloc_result in ALLOC. subst; xomega.
      eapply EI_inj; eauto.
  Qed.

  Lemma alloc_variables_lnr':
    forall l 
      (lnr : list_norepet (map fst l))
      m e m0
      (AV : Clight2.alloc_variables empty_env m l e m0),
      list_norepet (map fst (map fst (blocks_of_env e))).
  Proof.
    intros; eapply alloc_variables_lnr; eauto.
    intros i b t. rewrite PTree.gempty; congruence.
    intros i. rewrite PTree.gempty; congruence.
    simpl; constructor.
    intros id1 id2 b1 b2 ty1 ty2; rewrite PTree.gempty; congruence.
  Qed.

  Lemma in_blocks_of_env:
    forall x e, In x (blocks_of_env e) ->
           exists i t, Ctypes.sizeof t = snd x /\
                  snd (fst x) = 0 /\
                  e ! i = Some (fst (fst x), t).
  Proof.
    intros.
    unfold blocks_of_env, block_of_binding in H.
    rewrite in_map_iff in H.
    dex; destr. des x0.
    des p.
    exists i, t.
    apply PTree.elements_complete in H1; auto.
  Qed.
  Lemma alloc_variables_in:
    forall ei m l e m'
      (AV: Clight2.alloc_variables ei m l e m')
      i b t
      (EI: e ! i = Some (b, t)),
      ei ! i = Some (b, t) \/ In i (map fst l).
  Proof.
    induction 1; simpl; intros; eauto.
    eapply IHAV in EI.
    rewrite PTree.gsspec in EI.
    destr_in EI; auto.
  Qed.
  Lemma alloc_variables_range:
    forall id b ty e m vars e' m',
      Clight2.alloc_variables e m vars e' m' ->
      e'!id = Some(b, ty) -> e!id = Some(b, ty) \/ Ple (Mem.nextblock m) b /\ Plt b (Mem.nextblock m').
  Proof.
    induction 1; intros.
    auto.
    exploit IHalloc_variables; eauto. rewrite PTree.gsspec. intros [A|A].
    destruct (peq id id0). inv A. 
    right. exploit Mem.alloc_result; eauto. exploit Mem.nextblock_alloc; eauto.
    generalize (alloc_variables_nextblock _ _ _ _ _ H). intros A B C. 
    subst b. split. apply Ple_refl. eapply Plt_le_trans; eauto. rewrite B. apply Plt_succ. 
    auto.
    right. exploit Mem.nextblock_alloc; eauto. intros B. rewrite B in A. xomega. 
  Qed.

  Require Import Tactics.
  Lemma alloc_match:
    forall m tm (MM: match_mem m tm)
      hi m' b
      (ALLOC: CCMemory.Mem.alloc m 0 hi = (m',b)) al,
    exists tm',
      Mem.low_alloc tm 0 hi al Normal = Some (tm',b) /\
      match_mem m' tm'.
  Proof.
    intros.
    destruct (alloc_succeeds tm 0 hi al Normal) as [tm' [tb ALLOC']].
    assert (tb = b).
    apply CCMemory.Mem.alloc_result in ALLOC.
    apply Globalenvs.Genv.low_alloc_result in ALLOC'.
    inv MM; congruence.
    subst.
    rewrite ALLOC'; repeat refine (ex_intro _ _ _);  split; eauto.
    constructor; inv MM; auto.
    - intros.
      Transparent CCMemory.Mem.alloc.
      unfold CCMemory.Mem.alloc in ALLOC. inv ALLOC. simpl.
      Lemma low_alloc_mem_contents:
        forall m1 sz al m2 sp bt,
          Mem.low_alloc m1 0 sz al bt = Some (m2,sp) ->
          Mem.mem_contents m2 = PMap.set sp (Mem.init_block 0 sz sp)
                                         (Mem.mem_contents m1).
      Proof.
        intros.
        unfold Mem.low_alloc in H; destr_in H; inv H. reflexivity.
      Qed.
      erewrite low_alloc_mem_contents; eauto.
      rewrite ! PMap.gsspec.
      eapply Globalenvs.Genv.low_alloc_result in ALLOC'.
      subst. rewrite match_next0.
      destr; eauto.
      rewrite ZMap.gi. simpl; auto.
    - apply CCMemory.Mem.nextblock_alloc in ALLOC.
      apply Globalenvs.Genv.low_alloc_nextblock in ALLOC'. congruence.
    - intros b0 o k p P.
      eapply CCMemory.Mem.perm_alloc_inv in P; eauto.
      destr_in P.
      + red.
        unfold Mem.low_alloc in ALLOC'; destr_in ALLOC'; inv ALLOC'; simpl.
        red. rewrite PMap.gss. des (zle 0 o); des (zlt o hi).
        constructor.
      + erewrite <- Globalenvs.Genv.low_alloc_perm; eauto.
        eapply CCMemory.Mem.perm_valid_block in P.
        red in P; red. congruence.
  Qed.
  

Transparent Mem.alloc.
  Lemma alloc_variables_match:
    forall m  ei l e m0
      (AV: alloc_variables ei m l e m0)
      tm (MM: match_mem m tm),
    exists m0',
      Clight2.alloc_variables ei tm l e m0' /\
      match_mem m0 m0' /\
      (forall b, Plt b (Mem.nextblock tm) ->
            Mem.bounds_of_block tm b = Mem.bounds_of_block m0' b).
  Proof.
    induction 1; simpl; intros.
    - eexists; split; eauto. constructor.
    - eapply alloc_match in H; eauto.
      destruct H as [tm' [ALLOC MM']].
      destruct (IHAV _ MM') as [m0' [AV' [MM2 SB]]].
      eexists; repSplit. 
      econstructor; eauto.
      unfold Mem.alloc.
      auto.
      intros. rewrite <- SB; auto.
      eapply Mem.bounds_of_block_alloc_other; eauto.
      intro; subst.
      eapply Mem.alloc_result in ALLOC; subst; xomega.
      erewrite Mem.nextblock_alloc; eauto; xomega.
  Qed.


  Lemma assign_loc_dyn:
    forall t m e f m'
      (AL: Clight2.assign_loc t m e f m')
      b,
      (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b).
  Proof.
    intros; inv AL.
    unfold Mem.storev, Mem.store in STORE; repeat destr_in STORE; inv STORE;
    unfold Mem.is_dynamic_block; destr.
    eapply Mem.is_block_dynamic_storebytes; eauto.
  Qed.

  Lemma reserve_0:
    forall m,
      MemReserve.reserve_boxes m O = Some m.
  Proof.
    unfold MemReserve.reserve_boxes. intros.
    destr.
    f_equal. destruct m. apply Mem.mkmem_ext; try reflexivity.
    simpl. apply plus_0_r.
    generalize (Mem.wfm_alloc m). lia.
  Qed.


  Lemma release_0:
    forall m,
      MemReserve.release_boxes m O = Some m.
  Proof.
    unfold MemReserve.release_boxes. intros.
    destr.
    f_equal. destruct m. apply Mem.mkmem_ext; try reflexivity.
    simpl. symmetry. apply minus_n_O. 
    generalize (Mem.wfm_alloc m). lia.
  Qed.

  Theorem clight_eq:
    forall s1 t s1',
      CCClight.step1 ge s1 t s1' ->
      forall s2
        (MS: match_states  s1 s2),
      exists s2',
        Clight2.step1 (genv_of_ccgenv ge) zerons s2 t s2' /\
        match_states s1' s2'.
  Proof.
    induction 1; simpl; intros; inv MS.
    - transf_eval.
      econstructor; split.
      + econstructor; eauto. 
      + econstructor. auto. auto. 
        * eapply match_cont_same_bounds. 4: eauto.
          intros; eapply assign_loc_bounds; eauto.
          eapply assign_loc_nb; eauto.
          intros; erewrite <- assign_loc_dyn; eauto.
        * red; intros.
          apply GV in H.
          split. des H. red; erewrite <-  assign_loc_bounds; eauto.
          des H. erewrite <- assign_loc_dyn; eauto.
        * auto.
        * intros.
          erewrite <-  assign_loc_bounds; eauto.
        * eauto.
        * eapply  assign_loc_nb in AL; eauto. xomega.
        * intros; destr. apply BlocksStack in H; destr.
          repSplit; destr.
          erewrite <- assign_loc_dyn; eauto. destr.
          
    - transf_eval.
      eexists; split.
      + econstructor; eauto.
      + econstructor; eauto.
        apply match_temp_env_set; auto.
        apply match_val_tn; auto.

    - transf_eval.
      econstructor; split.
      + econstructor; simpl; eauto.
        * erewrite find_funct_translated; eauto.
        * unfold Clight2.type_of_fundef.
          des fd.
      + econstructor; eauto.
        econstructor; eauto.
        

    - transf_eval.
      econstructor; split.
      + econstructor; simpl; eauto.
      + econstructor; auto.
        * eapply mte_set_opttemp; eauto.
          apply match_val_tn; auto.
        * eapply match_cont_same_bounds. 4: eauto.
          symmetry; eapply Events.extcall_bounds; eauto.
          red; xomega.
          eapply Events.external_call_nextblock; eauto.
          intros; erewrite <- Events.external_call_dyn; eauto.
        * red; intros.
          apply GV in H.
          des H; split. red; erewrite Events.extcall_bounds; eauto.
          eapply Mem.in_bound_valid; eauto.
          erewrite <- Events.external_call_dyn; eauto.
          eapply Mem.in_bound_valid; eauto.
        * intros.
          erewrite Events.extcall_bounds; eauto.
          trim (BlocksStack b); [|red; xomega].
          rewrite map_map, in_map_iff; simpl.
          eexists; split; eauto. destr.
          apply BlocksStack.
          rewrite map_map, in_map_iff; simpl.
          eexists; split; eauto. destr.
        * eauto.
        * eapply Events.external_call_nextblock in EC; eauto. xomega.
        * intros. exploit BlocksStack; eauto. intros; repSplit; destr.
          erewrite <- Events.external_call_dyn; eauto. destr.
          trim (BlocksStack b); [|red; xomega]. auto.          
          
    - econstructor; split.
      econstructor; simpl; eauto.
      econstructor; auto.
      econstructor; auto. 3: eauto.
      eapply match_cont_ple; eauto.
      eapply match_cont_ple'; eauto.
      auto. auto.
    - inv MC.
      econstructor; split.
      eapply Clight2.step_skip_seq. 
      econstructor; auto. eauto. auto. xomega.

    - inv MC.
      econstructor; split.
      eapply Clight2.step_continue_seq.
      econstructor; auto. eauto. auto. xomega.
      
    - inv MC.
      econstructor; split.
      eapply Clight2.step_break_seq.
      econstructor; auto. eauto. auto. xomega.

    - transf_eval.
      eapply bool_val_preserved' in H0; eauto.
      econstructor; split.
      econstructor. eauto. eauto.
      destruct b; econstructor; eauto.
    - econstructor; split.
      econstructor. 
      econstructor; auto.
      econstructor; auto.
      3: eauto.
      eapply match_cont_ple; eauto.
      eapply match_cont_ple'; eauto. auto. auto.
      
    - inv MC.
      econstructor; split.
      econstructor.  auto.
      econstructor; auto.
      econstructor; auto.
      2: eauto.
      eapply match_cont_ple; eauto. auto. auto.
      
    - inv MC.
      econstructor; split.
      eapply Clight2.step_break_loop1.
      econstructor; auto. eauto. auto. auto.
    - inv MC.
      econstructor; split.
      econstructor.  
      econstructor; auto. eauto. auto. auto.
    - inv MC.
      econstructor; split.
      eapply Clight2.step_break_loop2.
      econstructor; auto. eauto. auto. auto.

    - 
      eapply free_list_match in H; eauto.
      destruct H as [tm' [FL MM']].
      eexists; split.
      + econstructor. eauto. simpl. unfold zerons. apply release_0.
      + econstructor.
        * repeat red; auto.
        * apply match_call_cont; auto.
          eapply match_cont_same_bounds. 4: eauto.
          {
            intros. 
            symmetry.
            eapply Mem.bounds_freelist; eauto.
            intro IN.
            rewrite <- map_map in IN.
            apply BlocksStack in IN. xomega.
          }

          exploit Mem.nextblock_freelist; eauto. intro A; rewrite A. xomega. 
          {
            intros.
            rewrite Mem.is_block_dynamic_freelist; eauto.
          }
        * auto.
        * red; intros.
          specialize (GV _ _ H). des GV.
          split.
          
          red.
          erewrite Mem.bounds_freelist; eauto.
          intro IN.
          rewrite <- map_map in IN.
          apply BlocksStack in IN. destr.
          rewrite Mem.is_block_dynamic_freelist; eauto.
      
    - eapply free_list_match in H1; eauto.
      destruct H1 as [tm' [FL MM']].
      transf_eval.
      eexists; split.
      + econstructor; eauto. apply release_0.
      + simpl. econstructor; auto.
        * apply match_call_cont; auto.
          eapply match_cont_same_bounds. 4: eauto.
          {
            intros. 
            symmetry.
            eapply Mem.bounds_freelist; eauto.
            intro IN.
            rewrite <- map_map in IN.
            apply BlocksStack in IN. xomega.
          }

          exploit Mem.nextblock_freelist; eauto. intros A; rewrite A. xomega.
          {
            intros.
            rewrite Mem.is_block_dynamic_freelist; eauto.
          }
        * red; intros.
          specialize (GV _ _ H). des GV.
          split.
          
          red.
          erewrite Mem.bounds_freelist; eauto.
          intro IN.
          rewrite <- map_map in IN.
          apply BlocksStack in IN. destr.
          rewrite Mem.is_block_dynamic_freelist; eauto.

     
    - eapply free_list_match in H0; eauto.
      destruct H0 as [tm' [FL MM']].
      eexists; split.
      + eapply Clight2.step_skip_call; eauto.
        eapply call_cont_match_cont; eauto.
        apply release_0.
      + simpl. econstructor; auto.
        * repeat red; auto.
        *           eapply match_cont_same_bounds. 4: eauto.
          {
            intros. 
            symmetry.
            eapply Mem.bounds_freelist; eauto.
            intro IN.
            rewrite <- map_map in IN.
            apply BlocksStack in IN. xomega.
          }

          exploit Mem.nextblock_freelist; eauto. intros A; rewrite A. xomega.
          {
            intros.
            rewrite Mem.is_block_dynamic_freelist; eauto.
          }
        * red; intros.
          specialize (GV _ _ H0). des GV.
          split.
          red.
          erewrite Mem.bounds_freelist; eauto.
          intro IN.
          rewrite <- map_map in IN.
          apply BlocksStack in IN. destr.
          rewrite Mem.is_block_dynamic_freelist; eauto.

    - transf_eval.
      eapply sem_switch_arg_preserved in H0; eauto.
      eexists; split.
      econstructor; simpl; eauto.
      econstructor; auto.
      constructor; auto. 3: eauto.
      eapply match_cont_ple; eauto. xomega. auto. auto.

    - inv MC.
      eexists; split.
      econstructor; simpl; eauto.
      econstructor; auto. eauto. auto. xomega. 
    - inv MC.
      eexists; split.
      eapply Clight2.step_continue_switch; eauto.
      econstructor; auto. eauto. auto. xomega.
      
    - eexists; split.
      econstructor; simpl; eauto.
      econstructor; auto. eauto. auto. xomega. 

    - generalize (match_find_label lbl tm (fn_body f) (call_cont k)
                                   (Clight2.call_cont tk)
                                   _ _ (match_call_cont _ _ _ _ _ MC)).
      rewrite H. simpl.
      destr_cond_match; try easy. destruct p.
      intros [A B]; subst.
      eexists; split.
      econstructor; simpl; eauto.
      econstructor; auto. eauto. auto. xomega. 
      
    - inv H.
      

      eapply alloc_variables_match in H1; eauto.
      destruct H1 as [m0' [AV [MM' SB]]].
      eapply bind_parameters_match in H2; eauto.
      destruct H2 as [m1' [BP MM2]].

      eexists; split.
      + econstructor. econstructor.
        auto. eauto. eauto. apply reserve_0. simpl. eauto.

      + econstructor; eauto.
        * red. intros. simpl.
          generalize dependent (fn_temps f). clear; induction l; simpl; intros.
          rewrite PTree.gempty in H; inv H.
          des a.
          rewrite PTree.gsspec in *.
          destr; eauto. autoinv.
          eexists; split; eauto.
          repeat red; auto.
        * eapply match_cont_same_bounds. 4: eapply match_cont_higher. 4: eauto.
          intros. rewrite SB.
          erewrite MemReserve.reserve_bounds_of_block.
          eapply bind_parameters_bound. eauto.
          apply reserve_0. eauto. 
          apply alloc_variables_nextblock in AV.
          apply bind_parameters_nextblock in BP. xomega.
          intros.

          Lemma bind_parameters_dyn:
            forall e m p el m'
              (BP: Clight2.bind_parameters e m p el m') b,
              (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b).
          Proof.
            induction 1; simpl; intros; eauto. tauto.
            rewrite <- IHBP.
            eapply assign_loc_dyn; eauto.
          Qed.

          Lemma alloc_variables_dyn:
            forall e m v e' m'
              (AV: Clight2.alloc_variables e m v e' m') b,
              (Mem.is_dynamic_block m b <-> Mem.is_dynamic_block m' b).
          Proof.
            induction 1; simpl; intros; eauto. tauto.
            rewrite <- IHAV.
            eapply Mem.is_block_dynamic_alloc; eauto.
          Qed.
          rewrite <- bind_parameters_dyn. 2: eauto.
          rewrite <- alloc_variables_dyn; eauto.

        * red; intros.
          specialize (GV _ _ H).
          des GV; split. red.
          erewrite <- bind_parameters_bound. 2: eauto.
          rewrite <- SB; auto.
          eapply Mem.in_bound_valid; eauto.
          rewrite <- bind_parameters_dyn. 2: eauto.
          rewrite <- alloc_variables_dyn; eauto.
        * clear - AV H0.
          eapply alloc_variables_lnr'; eauto.
          unfold var_names in H0. rewrite <- list_append_map in H0. auto.

        * intros.
          erewrite <- bind_parameters_bound. 2:eauto.
          apply in_blocks_of_env in H. dex.  destruct H as (SZ & LO & EI).
          simpl in *. subst.
          eapply alloc_variables_bounds; eauto.
          intros id b0 ty; rewrite PTree.gempty; congruence.


          eapply alloc_variables_in in EI; eauto.
          rewrite PTree.gempty in EI. destr.
          
        * instantiate (1:=Mem.nextblock m0').
          eapply alloc_variables_nextblock; eauto.
        * eapply bind_parameters_nextblock; eauto.
        * intros.
          rewrite map_map, in_map_iff in H.
          destruct H as [[[bb lo0] hi0] [EQ IN]].
          simpl in *. subst.
          apply in_blocks_of_env in IN.
          destruct IN as [i [t [SZ [LO EI]]]]; simpl in *. subst.
          eapply alloc_variables_range in EI; eauto.
          rewrite PTree.gempty in EI.
          destruct EI. congruence.
          destruct H.
          repSplit; auto.
          destruct (CCGlobalenvs.Genv.find_funct_ptr ge b) as [ff|] eqn:E; auto.
          apply GV in E.
          des E. apply Mem.in_bound_valid in i0.
          red in i0. xomega.

          Lemma Ple_Plt_succ_or_eq:
            forall a b,
              Ple a b ->
              Plt a b \/ a = b.
          Proof.
            intros. xomega.
          Qed.
          
          Lemma alloc_variables_in_range_normal:
            forall e m v e' m'
              (AV: Clight2.alloc_variables e m v e' m') b,
              Ple (Mem.nextblock m) b -> Plt b (Mem.nextblock m') ->
              ~ Mem.is_dynamic_block m' b.
          Proof.
            induction 1; simpl; intros; eauto. xomega.
            des (peq b b1).
            rewrite <- alloc_variables_dyn. 2: eauto.
            rewrite <- Mem.is_block_dynamic_alloc. 2: eauto.
            unfold Mem.is_dynamic_block; rewrite Mem.blocktype_valid. destr. xomega.
            apply IHAV; auto.
            erewrite Mem.nextblock_alloc. 2: eauto.
            exploit Mem.alloc_result; eauto. intro; subst.
            apply Ple_Plt_succ_or_eq in H. des H. xomega.
          Qed.
          rewrite <- bind_parameters_dyn. 2: eauto.
          eapply alloc_variables_in_range_normal; eauto.

    - transf_eval.
      econstructor; split.
      econstructor; simpl; eauto.
      econstructor; eauto.
      * eapply match_cont_same_bounds. 4: eauto.
        symmetry; eapply Events.extcall_bounds; eauto. eapply match_cont_ple' in MC; eauto. red; xomega.
        eapply Events.external_call_nextblock. eauto. 
        intros; erewrite <- Events.external_call_dyn; eauto.
      * red; intros.
        apply GV in H. des H; split.
        red; erewrite Events.extcall_bounds; eauto.
        eapply Mem.in_bound_valid; eauto.
        intros; erewrite <- Events.external_call_dyn; eauto.
        eapply Mem.in_bound_valid; eauto.
    - inv MC.
      eexists; split.
      econstructor.
      econstructor; eauto.
      eapply mte_set_opttemp; eauto.
      apply match_val_tn; auto. 
  Qed.

  
  
End PRES.

  Definition transf_program (prog: CCClight.program) : Clight2.program :=
    transform_program cfundef_of_fundef prog.

  Lemma find_funct_ptr_translated:
    forall ge fd b
      (FF : CCGlobalenvs.Genv.find_funct_ptr ge b = Some fd),
      Globalenvs.Genv.find_funct_ptr (genv_of_ccgenv ge) b = Some (cfundef_of_fundef fd).
  Proof.
    intros.
    unfold CCGlobalenvs.Genv.find_funct_ptr in FF.
    unfold Globalenvs.Genv.find_funct_ptr.
    unfold genv_of_ccgenv; simpl.
    des ge. 
    unfold tree_of_tree. rewrite PTree.gmap.
    rewrite FF. auto.
  Qed.

  Lemma alloc_match_wider:
        forall m tm (MM: match_mem m tm)
          hi m' b
          (ALLOC: CCMemory.Mem.alloc m 0 hi = (m',b))
          hi' (Hsup: hi' >= hi) bt,
        exists tm',
          Mem.alloc tm 0 hi' bt = Some (tm',b) /\
          match_mem m' tm'.
      Proof.
        intros.
        Transparent Mem.alloc.
        unfold Mem.alloc.
        destruct (alloc_succeeds tm 0 hi' (alignment_of_size hi') bt) as [tm' [tb ALLOC']].
        assert (tb = b).
        apply CCMemory.Mem.alloc_result in ALLOC.
        apply Mem.alloc_result in ALLOC'.
        inv MM; congruence.
        subst.
        rewrite ALLOC'; repeat refine (ex_intro _ _ _);  split; eauto.
        constructor; inv MM; auto.
        - intros.
          Transparent CCMemory.Mem.alloc.
          unfold CCMemory.Mem.alloc in ALLOC. inv ALLOC. simpl.
          erewrite Mem.a_mem_contents'; eauto.
          rewrite ! PMap.gsspec.
          eapply Mem.alloc_result in ALLOC'. subst. rewrite match_next0.
          destr; eauto.
          rewrite ZMap.gi. simpl; auto.
        - apply CCMemory.Mem.nextblock_alloc in ALLOC.
          apply Mem.nextblock_alloc in ALLOC'. congruence.
        - intros b0 o k p P.
          eapply CCMemory.Mem.perm_alloc_inv in P; eauto.
          destr_in P; eapply Mem.alloc_perm; eauto. right; split; auto. lia.
      Qed.

      Lemma alloc_contents:
        forall m lo hi m' b,
          CCMemory.Mem.alloc m lo hi = (m',b) ->
          CCMemory.Mem.mem_contents m' = PMap.set b (ZMap.init CCMemdata.Undef)
                                                  (CCMemory.Mem.mem_contents m).
      Proof.
        Transparent CCMemory.Mem.alloc.
        intros.
        unfold CCMemory.Mem.alloc in H. inv H.
        simpl. auto.
      Qed.
      
      Lemma store_zeros_match:
        forall m b lo hi m' 
          (SZ: CCGlobalenvs.store_zeros m b lo hi = Some m')
          tm (MM: match_mem m tm),
        exists tm', Globalenvs.store_zeros tm b lo hi = Some tm' /\ match_mem m' tm'.
      Proof.
        intros m b lo hi m' SZ tm MM.
        revert SZ tm MM.
        eapply (CCGlobalenvs.store_zeros_ind).
        - simpl; intros. inv SZ. rewrite Globalenvs.store_zeros_equation. rewrite e.
          eexists; split; eauto.
        - simpl; intros. specialize (H SZ).
          exploit store_match; eauto. destr. apply match_val_eval.
          intros [tm' [S MM']].
          specialize (H _ MM').
          destruct H as [tm'0 [SZ' MM2]].
          rewrite Globalenvs.store_zeros_equation. rewrite e.
          rewrite try_norm_val in S by (simpl; auto).
          setoid_rewrite S. eexists; split; eauto.
        - simpl; intros. congruence.           
      Qed.


        Lemma genv_ext:
          forall F V s s' f f' v v' n n',
            s = s' -> f = f' -> v = v' -> n = n' ->
            forall pf1 pf2 pf3 pf4 pf5
              pf1' pf2' pf3' pf4' pf5',
            @Globalenvs.Genv.mkgenv F V s f v n pf1 pf2 pf3 pf4 pf5 =
            @Globalenvs.Genv.mkgenv F V s' f' v' n' pf1' pf2' pf3' pf4' pf5'. 
        Proof.
          intros.
          subst.
          f_equal; apply Axioms.proof_irr.
        Qed.

        Lemma set_leaf:
          forall {A} (x: A) k,
            PTree.set k x PTree.Leaf =
            match k with
            | (ii~1)%positive =>
              PTree.Node PTree.Leaf None (PTree.set ii x PTree.Leaf)
            | (ii~0)%positive =>
              PTree.Node (PTree.set ii x PTree.Leaf) None PTree.Leaf
            | 1%positive => PTree.Node PTree.Leaf (Some x) PTree.Leaf
            end.
        Proof.
          intros. destr.
        Qed.

        Lemma xmap_noint:
          forall {A B} (f: positive -> A -> B)
            (Ext: forall k1 k2 a, f k1 a = f k2 a) t i1 i2,
            PTree.xmap f t i1 = PTree.xmap f t i2.
        Proof.
          induction t; simpl; intros; eauto.
          erewrite IHt1. erewrite IHt2.
          des o.
          erewrite Ext. reflexivity.
        Qed.

        Lemma map_node:
          forall {A B} (f: positive -> A -> B)
            (Ext: forall k1 k2 a, f k1 a = f k2 a) t1 o t2,
            PTree.map f (PTree.Node t1 o t2) = PTree.Node (PTree.map f t1) (option_map (f xH) o) (PTree.map f t2).
        Proof.
          unfold PTree.map; simpl. intros.
          generalize (xmap_noint _ Ext). intro X.
          des o; f_equal; eauto.
        Qed.
        
        Lemma set_map:
          forall {A B}
            (f: positive -> A -> B) 
            (Ext: forall k1 k2 a, f k1 a = f k2 a)
            x
            (t: PTree.t A)  k,
            PTree.set k (f k x) (PTree.map f t) = PTree.map f (PTree.set k x t).
        Proof.
          induction t; simpl; intros; auto.
          - induction k; simpl; intros; eauto.
            + erewrite Ext with (k2:=k). unfold PTree.map; simpl.
              unfold PTree.map in IHk.
              erewrite xmap_noint with (i2:=1%positive); auto.
              rewrite <- IHk. auto.
            + erewrite Ext with (k2:=k). unfold PTree.map; simpl.
              unfold PTree.map in IHk.
              erewrite xmap_noint with (i2:=1%positive); auto.
              rewrite <- IHk. auto.
          - generalize (xmap_noint _ Ext). intro X.
            destruct k; simpl; auto; rewrite map_node; auto.
            unfold PTree.map in *; des o; f_equal; eauto.
            rewrite (Ext _ k). rewrite <- IHt2; eauto. f_equal; eauto.
            rewrite (Ext _ k). rewrite <- IHt2; eauto. f_equal; eauto.
            unfold PTree.map in *; des o; f_equal; eauto.
            rewrite (Ext _ k). rewrite <- IHt1; eauto. f_equal; eauto.
            rewrite (Ext _ k). rewrite <- IHt1; eauto. f_equal; eauto.
        Qed.
        
        Lemma add_global_translated:
          forall t a,
            Globalenvs.Genv.add_global (genv_of_ccgenv t)
                                       (transform_program_globdef cfundef_of_fundef a) =
            genv_of_ccgenv (CCGlobalenvs.Genv.add_global t a).
        Proof.
          destruct a.
          simpl.
          destruct g.
          simpl.
          unfold Globalenvs.Genv.add_global.
          apply genv_ext; simpl; auto.
          - unfold genv_of_ccgenv; destr.
          - unfold genv_of_ccgenv; destr.
            unfold tree_of_tree.
            generalize (cfundef_of_fundef). clear.
            generalize genv_next.
            generalize genv_funs.
            clear.
            induction genv_funs; simpl; intros.
            rewrite <- set_map; auto.
            rewrite <- set_map; auto.
          - unfold genv_of_ccgenv; destr.
          - unfold genv_of_ccgenv; destr.
          - apply genv_ext; simpl; auto;
            unfold genv_of_ccgenv; destr.
        Qed.
        
        Lemma genv_translated:
          forall prog,
            Globalenvs.Genv.globalenv (transf_program prog) =
            genv_of_ccgenv (CCGlobalenvs.Genv.globalenv prog).
        Proof.
          intros.
          unfold CCGlobalenvs.Genv.globalenv, Globalenvs.Genv.globalenv.
          simpl.
          generalize (prog_defs prog).
          replace (Globalenvs.Genv.empty_genv Clight2.fundef Ctypes.type) with (genv_of_ccgenv (CCGlobalenvs.Genv.empty_genv fundef Ctypes.type)).
          2: simpl.
          2: unfold Globalenvs.Genv.empty_genv.
          2: f_equal; try now apply Axioms.proof_irr.
          generalize (CCGlobalenvs.Genv.empty_genv fundef Ctypes.type).
          intros t l; revert l t.
          induction l; simpl; intros. auto.
          rewrite <- IHl.
          f_equal.
          apply add_global_translated.
        Qed.

      
      Lemma store_init_data_match:
        forall prog idl m b lo m4,
          CCGlobalenvs.Genv.store_init_data
            (CCGlobalenvs.Genv.globalenv  prog) m b lo idl = Some m4 ->
          forall tm (MM: match_mem m tm),
          exists m4',
            Globalenvs.Genv.store_init_data
              (Globalenvs.Genv.globalenv (transf_program prog)) tm b lo
              idl = Some m4' /\ match_mem m4 m4'.
      Proof.
        intros. destruct idl; simpl in *; 
                try eapply store_match in H; eauto; try (now destr);
                try (now apply match_val_eval);
                try (rewrite try_norm_val in * by (simpl; auto)); auto.
        eexists; inv H; split; eauto.
        destr_in H.


        rewrite genv_translated.
        erewrite find_symbol_translated; eauto.
        eapply store_match in H; eauto. 2: econstructor; eauto.
        2: destr. 2: destr.
        2: apply match_val_eval.
        rewrite try_norm_val in H; simpl; auto.
      Qed.

      
      Lemma store_init_data_list_match:
        forall prog idl m b lo m4,
          CCGlobalenvs.Genv.store_init_data_list
            (CCGlobalenvs.Genv.globalenv prog) m b lo idl = Some m4 ->
          forall tm (MM: match_mem m tm) ,
          exists m4',
            Globalenvs.Genv.store_init_data_list
              (Globalenvs.Genv.globalenv (transf_program prog)) tm b lo
              idl = Some m4' /\ match_mem m4 m4'.
      Proof.
        induction idl; simpl; intros.
        - inv H; eexists; split; eauto.
        - revert H; destr_cond_match; try congruence.
          eapply store_init_data_match in Heqo; eauto.
          destruct Heqo as [m4' [SID MM']]. intro.
          eapply IHidl in H.
          destruct H as [m4'0 [SIDL MM2]].
          rewrite SID. rewrite SIDL.
          eexists; split; eauto. auto.
      Qed.
              
      Lemma alloc_global_match:
        forall prog fid sg (SGpos: forall i, sg i > 0) m0 m1 (MM : match_mem m0 m1) a m2
          (AG : CCGlobalenvs.Genv.alloc_global (CCGlobalenvs.Genv.globalenv prog)
                                               m0 a = Some m2),
        exists m' : Memory.mem,
          Globalenvs.Genv.alloc_global
            fid sg
            (Globalenvs.Genv.globalenv (transf_program prog)) m1
            (transform_program_globdef cfundef_of_fundef a) = Some m'
          /\ match_mem m2 m'.
      Proof.
        intros.
        Opaque CCMemory.Mem.alloc.
        destruct a.  simpl in *.
        destruct g; simpl in *.
        - destruct (CCMemory.Mem.alloc m0 0 1) as [m3 b] eqn:A.
          edestruct (alloc_match_wider _ _ MM _ _ _ A (Globalenvs.Genv.size_glob' fid sg (cfundef_of_fundef f))) as [tm' [A' MM']].
          + unfold Globalenvs.Genv.size_glob'.
            unfold Globalenvs.Genv.size_glob.
            destr. generalize (SGpos i0). lia. lia.
          + rewrite A'.
            destruct (Mem.range_perm_drop_2 tm' b 0 (Globalenvs.Genv.size_glob' fid sg (cfundef_of_fundef f)) Nonempty) as [m2' DP].
            * red; intros.
              eapply Mem.perm_alloc_2; eauto.
            * rewrite DP. eexists; split; eauto.
              constructor.
              intros.
              unfold CCMemory.Mem.drop_perm in AG.
              destr_in AG. inv AG. simpl. 
              erewrite <- Mem.drop_perm_contents; [|eauto].
              inv MM'.
              eauto. 
              rewrite (CCMemory.Mem.nextblock_drop _ _ _ _ _ _ AG).
              rewrite (Mem.nextblock_drop _ _ _ _ _ _ DP). inv MM'; auto.
              intros b0 o k p P.
              rewrite Mem.perm_drop_perm. 2: eauto.
              exploit CCMemory.Mem.perm_drop_4. eauto. eauto.
              intros. destr; eauto.
              destr; eauto.
              subst.
              exploit CCMemory.Mem.perm_alloc_3; eauto.
              intro.
              exploit CCMemory.Mem.perm_drop_2; eauto.
              inv MM'; eauto. inv MM'; eauto.
        - 
          repeat destr_in AG.
          destruct (alloc_match _ _  MM _ _ _ Heqp
                                (Globalenvs.Genv.init_data_list_align (gvar_init v)))
            as [tm' [A' MM']].
          +  unfold Mem.alloc in A'.
             Lemma idls_eq:
               forall i,
                 Globalenvs.Genv.init_data_list_size i =
                 CCGlobalenvs.Genv.init_data_list_size i.
             Proof.
               des i.
             Qed.
             rewrite idls_eq.
             rewrite A'.
             exploit store_zeros_match; eauto; try (now econstructor; eauto). intros [tm'0 [SZ MM2]].
            setoid_rewrite SZ.
            exploit store_init_data_list_match; eauto; try (now econstructor; eauto).
            intros [m4' [SIDL MM4]].
            rewrite SIDL.
            destruct (Mem.range_perm_drop_2 m4' b 0 (Globalenvs.Genv.init_data_list_size (gvar_init v)) (Globalenvs.Genv.perm_globvar v)) as [m2' DP].
            * red; intros.
              rewrite <- Globalenvs.Genv.store_init_data_list_perm; [|eauto].
              rewrite <- Globalenvs.Genv.store_zeros_perm; [|eauto].
              unfold Mem.low_alloc in A'; destr_in A'; inv A'. simpl.
              red; simpl. rewrite PMap.gss. clear - H.
              des (zle 0 ofs).
              des (zlt ofs (CCGlobalenvs.Genv.init_data_list_size (gvar_init v))).
              constructor.
              rewrite idls_eq in H; eauto. lia.
            * rewrite <- idls_eq. rewrite DP. eexists; split; eauto.
              constructor.
              intros.
              unfold CCMemory.Mem.drop_perm in AG.
              destr_in AG. inv AG. simpl. 
              erewrite <- Mem.drop_perm_contents; [|eauto].
              inv MM4; eauto. 
              rewrite (CCMemory.Mem.nextblock_drop _ _ _ _ _ _ AG).
              rewrite (Mem.nextblock_drop _ _ _ _ _ _ DP).
              inv MM4; auto.
              intros b0 o k p P.

              rewrite Mem.perm_drop_perm. 2: eauto.
              exploit CCMemory.Mem.perm_drop_4. eauto. eauto.
              inv MM4.              
              destr; eauto.
              destr; eauto.
              subst.
              rewrite <- CCGlobalenvs.Genv.store_init_data_list_perm; [|eauto].
              rewrite <- CCGlobalenvs.Genv.store_zeros_perm; [|eauto].
              intros.
              exploit CCMemory.Mem.perm_alloc_3; eauto.
              intro.
              exploit CCMemory.Mem.perm_drop_2; eauto. 
      Qed.

  Lemma init_mem_match:
    forall prog m fid sg (Pos: forall i, sg i > 0)
      (IM : CCGlobalenvs.Genv.init_mem prog = Some m),
    exists m',
      Globalenvs.Genv.init_mem fid sg (transf_program prog) = Some m'
      /\ match_mem m m'.
  Proof.
    intros. unfold CCGlobalenvs.Genv.init_mem in IM.
    unfold Globalenvs.Genv.init_mem.
    unfold transf_program at 2.
    unfold transform_program; simpl.

    assert (Mempty: match_mem CCMemory.Mem.empty Mem.empty).
    {
      constructor. simpl.
      intros. rewrite PMap.gi. rewrite ZMap.gi. simpl; auto.
      simpl; auto.
      intros b o k p P.
      red in P.
      simpl in P.
      rewrite PMap.gi in P. inv P.
    }
    
    revert Mempty IM.
    generalize (CCMemory.Mem.empty) Mem.empty.
    generalize dependent (prog_defs prog) .
    
    induction l; simpl; intros.
    - eexists; split; eauto. inv IM. auto.
    - revert IM; destr_cond_match; try congruence.
      intros.
      exploit alloc_global_match; eauto.
      intros [m' [AG MM]].
      rewrite AG.
      eapply IHl; eauto. 
  Qed.


  
  Theorem initial_match:
    forall sg (Pos: forall i, sg i > 0) prog S,
      CCClight.initial_state prog S ->
      exists R, Clight2.initial_state (transf_program prog) sg R /\ match_states (CCGlobalenvs.Genv.globalenv prog) S R.
  Proof.
    intros. inv H.
    exploit find_funct_ptr_translated; eauto. intros A. 
    exploit init_mem_match; eauto.
    intros [m' [IM MM]].
    econstructor; split.
    econstructor; eauto.
    rewrite genv_translated.
    eapply find_symbol_translated; eauto.
    rewrite genv_translated.    eauto. 
    des f.

    econstructor. auto.
    2: constructor.
    2: econstructor.
    3: apply Ple_refl.
    2: apply Ple_refl.
    red; intros.
    clear H2.
    exploit find_funct_ptr_translated; eauto. intros.
    clear A.
    exploit (Globalenvs.Genv.init_mem_characterization_2); eauto.
    rewrite genv_translated; eauto. 
    intros [A [B C]].
    split; red; intros.
    rewrite A.
    red; simpl. unfold Globalenvs.Genv.size_glob'.
    unfold Globalenvs.Genv.size_glob.
    destr; try generalize (Pos i); lia.
    destr.
  Qed.


  Lemma final_states_simulation:
  forall ge S R r,
    match_states ge S R -> CCClight.final_state S r -> Clight2.final_state R r.
Proof.
  intros. inv H0. inv H.
  inv MC. 
  constructor.
  apply (Mem.lessdef_eqm tm _ _) in MV.
  rewrite Mem.norm_val in MV.
  inv MV; auto.
Qed.
