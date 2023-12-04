Require Import Coqlib.
Require Import Axioms.
Require Import Bool.
Require Import ZArith.
Require Import Psatz.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Utf8.
Require Import Values_symbolictype.
Require Import ExprEval.
Open Scope Z_scope.
Open Scope list_scope.
Require Import IntFacts.

Ltac destr_and :=
  repeat 
    match goal with
        H: ?A /\ ?B |- _ => destruct H
      | H: exists _, _ |- _ => destruct H
    end.


Definition in_bound (o:Z) (itv: Z * Z) : Prop :=
  fst itv <= o /\ o < snd itv.

Lemma in_bound_dec:
  forall b o,
    in_bound o b \/ ~ in_bound o b.
Proof.
  intros.
  unfold in_bound; destruct b; simpl.
  destruct (zle z o);
    destruct (zlt o z0); try omega.
Qed.


Definition typ_of_result (r:result) : styp :=
  match r with
    | Int   => Tint
    | Long  => Tlong
    | Float => Tfloat
    | Single => Tsingle
    | Ptr   => Tint
  end.


Section Compat.
  (*** Compatibility relation of a CompCert memory w.r.t a concrete allocation of pointers *)

  Variable Size : Z.
  
  (** Bound & Alloc are constructed from a CompCert memory.
     For a non allocated block b, Bound b = (0,0)  and Mask b = 0 
   *)
  Variable Bound : block -> Z * Z.

  Variable Mask : block -> int.

  (** [Alloc b] is the concrete address where b is allocated *)
  Variable Alloc : block -> int.
  
  Infix "∈" := in_bound (at level 80).

  Notation "[ i ]" := (Int.unsigned i).
  Infix "+" := Int.add.
  Infix "&&" := Int.and.

  (** With respect to an axiomatisation of an abstract memory ([Bound], [Mask]),
      the [compat] relation states what a compatible memory [Alloc] must
      satisfy. *)

  Record compat : Prop :=
    {
      addr_space : forall b o,  [o] ∈ (Bound b)  -> 
                                0 < [ (Alloc b) + o ] < Size;
      
      overlap : forall  b b' o o', 
                  b <> b' -> 
                  [o] ∈ (Bound b) -> 
                  [o'] ∈ (Bound b') -> 
                  [(Alloc b) + o] <> [(Alloc b') + o'];
      
      alignment : forall b (* (ib: 0 ∈ (Bound b)) *),
          (Alloc b) && (Mask b) = Alloc b
                                                           
    }.
  
End Compat.


Lemma in_bound_zero:
  forall o bnd (BndSpec: forall b:block, fst (bnd b) = 0) b,
    in_bound o (bnd b) ->
    in_bound (Int.unsigned Int.zero) (bnd b).
Proof.
  unfold in_bound; simpl; intros.
  specialize (BndSpec b).
  rewrite Int.unsigned_zero.
  rewrite BndSpec. split. lia. lia. 
Qed.

Lemma compat_add_unsigned:
  forall bnd (BndSpec: forall b, fst (bnd b) = 0) msk cm (COMP: compat Int.max_unsigned bnd msk cm) b
    o (IB: in_bound (Int.unsigned o) (bnd b)),
    Int.unsigned (Int.add (cm b) o) = Int.unsigned (cm b) + Int.unsigned o.
Proof.
  intros.
  inv COMP.
  clear overlap0 alignment0.
  rename addr_space0 into addr_space.
  specialize (addr_space b).
  generalize (addr_space _ IB).
  generalize (addr_space _ (in_bound_zero _ _ BndSpec _ IB)).
  rewrite Int.add_zero.
  intros. apply Int.unsigned_repr. 

  split.
  generalize (Int.unsigned_range (cm b)) (Int.unsigned_range o); lia.
  destruct (zle (   Int.unsigned (cm b) + Int.unsigned o) (Int.max_unsigned)); auto.
  exfalso.

  set (oo := Int.max_unsigned - Int.unsigned (cm b)).
  trim (addr_space (Int.repr oo)).
  revert IB. unfold oo.
  rewrite Int.unsigned_repr.
  - unfold in_bound. rewrite BndSpec. 
    Opaque Z.sub.
    destr. 2:lia. generalize (Int.unsigned_range_2 (cm b)). lia.
  - destr. 2:lia. generalize (Int.unsigned_range_2 (cm b)). lia.
    
  - revert addr_space.
    unfold oo.
    rewrite Int.add_unsigned.
    rewrite (Int.unsigned_repr (_ - _)).
    rewrite Zplus_minus. simpl; unfsize. rewrite Int.unsigned_repr. lia.
    unfsize. lia.
    split; try lia.
Qed.

Lemma compat_larger:
  forall sz sz' al bnd msk
    (LE: sz <= sz')
    (COMP: compat sz bnd msk al),
    compat sz' bnd msk al.
Proof.
  intros.
  destruct COMP; constructor; auto.
  intros b o IB.
  apply addr_space0 in IB.
  lia.
Qed.

Ltac unfsize :=
  change Int.zwordsize with 32 in *; change Int64.zwordsize with 64 in *;
  change (Int.unsigned (Int.repr Int.half_modulus)) with 2147483648 in *;
  change Int.half_modulus with 2147483648 in *;
  change Int.max_unsigned with 4294967295 in *;
  change Int64.max_unsigned with 18446744073709551615 in *;
  change Int.modulus with 4294967296 in *;
  change Int64.max_unsigned with 18446744073709551616 in *.

Lemma testbit_hm: forall i, Int.testbit (Int.repr Int.half_modulus) i = zeq i 31.
Proof.
  intros.
  destruct (zle 0 i).
  destruct (zlt i Int.zwordsize).
  - rewrite Int.testbit_repr; auto.
    change (Int.half_modulus) with (1 * 2 ^ 31).
    rewrite Z.mul_pow2_bits by lia.
    rewrite Byte.Ztestbit_1.
    destruct (zeq (i - 31) 0), (zeq i 31); auto; lia.      
  - rewrite Int.bits_above. unfsize. destruct (zeq i 31); subst. lia. auto.
    auto.
  - unfold Int.testbit. rewrite Z.testbit_neg_r by lia.
    destruct (zeq i 31); auto; lia.
Qed.

(** Decidability of the existence of a compatible concrete memory. *)
Lemma ex_alloc_dec : forall sz bound align,
                       (exists alloc, compat sz bound align alloc) \/
                       (~exists alloc, compat sz bound align alloc).
Proof.
  intros.
  apply Classical_Prop.classic.
Qed.


Section Depends.
  Variable max: Z.
  Variable sz : block -> (Z*Z).
  Variable msk: block -> int.

  Definition depends (e: expr_sym) (b: block) : Prop :=
    forall cm  (COMP:  compat max sz msk cm)
      cm' (COMP': compat max sz msk cm')
      (SameB: cm b <> cm' b)
      (* (all_eq: forall b', b <> b' -> cm b' = cm' b') *),
    forall em,
      eSexpr cm em e <> eSexpr cm' em e.
  
  Record depends_old (e: expr_sym) (b: block) : Prop :=
    mkDep {
        dep_cm: block -> int;
        dep_cm' : block -> int;
        dep_compat: compat max sz msk dep_cm;
        dep_compat': compat max sz msk dep_cm';
        dep_diff_b: dep_cm b <> dep_cm' b;
        dep_same_other: forall b', b <> b' ->
                              dep_cm b' = dep_cm' b';
        dep_eval_diff: forall em, eSexpr dep_cm em e <> eSexpr dep_cm' em e
      }.


  (* For any two blocks, there exists a pair of concrete memories where one moves and not the other *)
  Hypothesis exists_two_cms:
    forall b,
    exists cm cm', compat max sz msk cm /\
              compat max sz msk cm' /\
              cm b <> cm' b /\
              (forall b', b <> b' -> cm b' = cm' b').

  Lemma dep_old_dep:
    forall e b,
      depends e b -> depends_old e b.
  Proof.
    intros.
    destruct (exists_two_cms b) as (cm & cm' & A & B & C & D).
    eapply mkDep with (dep_cm := cm) (dep_cm' := cm'); auto.
  Qed.
  (* The other way around isn't true: given a pair of concrete memories, we
  can't prove that for any pair of concrete memories, ... *)
  
  Lemma exists_two_cms':
    forall b,
    exists cm cm', compat max sz msk cm /\
              compat max sz msk cm' /\
              cm b <> cm' b.
  Proof.
    intros.
    generalize (exists_two_cms b).
    intros [cm [cm' [COMP [COMP' [DIFF EQ]]]]].
    eauto.               
  Qed.
  
  Example depends_const:
    forall b v (noptr: match v with Vptr _ _ => False | _ => True end),
      ~ depends (Eval v) b.
  Proof.
    red; intros.
    red in H.
    generalize (exists_two_cms b). intro A.
    dex.
    destr_and.
    apply (H _ H0 _ H1 H2 (fun _ _ => Byte.zero)).
    des v.
  Qed.

  Example depends_ptr:
    forall b b' i (dep: depends (Eval (Vptr b i)) b'),
      b = b'.
  Proof.
    intros.
    destruct (peq b' b); auto.
    generalize (exists_two_cms b' ); intro A.
    dex; destr.
    generalize (dep _ H _ H1 H0  (fun _ _ => Byte.zero)). simpl.
    intros.
    assert (cm b <> cm' b).
    intro A; rewrite A in H2; auto. clear H2.
    exfalso; apply H4; apply H3. auto.
  Qed.
 
  
  (** The result of a normalisation is "good" if it is of the correct type, and,
    if it is a pointer, then it must be a valid pointer *)

  Definition good_result (e: expr_sym) (v : val) : Prop :=
    match v with
    | Vptr b i => depends e b
    | _ => True
    end.

End Depends.


  
(** The type of a normalisation function. It takes four parameters:
- a function [bound] that associates with each block [b] a pair [(lo,hi)] of low and high bounds;
- a function [align] that associates with each block [b] its alignment constraints;
- the expression [e] to be normalised;
- the result [t] to which we wish to normalise it.  *)

Definition norm_typ :=   (block -> Z * Z) -> (block -> int) -> expr_sym -> val.


Definition lessdef v1 v2 :=
  forall cm em,
    Val.lessdef (eSexpr cm em v1) (eSexpr cm em v2).

Definition lessdef_on (P: (block -> int) -> Prop) (e1 e2: expr_sym) : Prop :=
  forall cm em (Pcm: P cm),
    Val.lessdef (eSexpr cm em e1) (eSexpr cm em e2).

Definition same_eval_on (P: (block -> int) -> Prop) (e1 e2: expr_sym) : Prop :=
  forall cm em (Pcm: P cm), eSexpr cm em e1 = eSexpr cm em e2.

Definition same_eval (e1 e2: expr_sym) : Prop :=
  forall cm em, eSexpr cm em e1 = eSexpr cm em e2.

Lemma same_eval_lessdef_on:
  forall P a b (SE: same_eval_on P a b), lessdef_on P a b.
Proof.
  red; intros; rewrite SE; auto.
Qed.

(* Definition compat31 := compat (Int.max_unsigned - 8). *)
(* Definition compat32 := compat Int.max_unsigned. *)

Module IsNorm.

  Section NormSpec.

    (** A value [v] is a correct normalisation of the expression [e] if:
      - if [e] is of type [r], then [v] and [e] should evaluate the same;
      - [v] must be a ``good result'' for [e] and [r];
      - if [e] is not of type [r], then [v] is [Vundef];
      - if there does not exists any compatible concrete memory, [v] is [Vundef].
     *)
    
    Record t
           (bound : block -> Z * Z)
           (align : block -> int)
           (e:expr_sym) (v:val) : Prop := 
      Mk
        {
          eval_ok   : 
            lessdef_on (compat Int.max_unsigned bound align) (Eval v) e(* ; *)
          (* no_cm_undef:  *)
          (*   forall (NEX: ~ (exists cm, compat31 bound align cm)), *)
          (*     v = Vundef *)
        }.
  
  End NormSpec.

End IsNorm.

Lemma inj_vint:
  forall i j,
    Vint i = Vint j -> i = j.
Proof.
  congruence.
Qed.


Lemma int_add_eq_l:
  forall a b c,
    Int.add a b = Int.add a c ->
    b = c.
Proof.
  intros.
  generalize (Int.eq_true (Int.add a b)).
  rewrite H at 2.
  rewrite ! (Int.add_commut a). 
  rewrite Int.translate_eq.
  intro A.
  generalize (Int.eq_spec b c). rewrite A; auto.
Qed.


Lemma is_norm_dep:
  forall sz msk e v,
    IsNorm.t sz msk e v ->
    good_result Int.max_unsigned sz msk e v.
Proof.
  intros sz msk e v [LD].
  des v.
  red; intros. intro EQ.
  generalize (LD _ em COMP) (LD _ em COMP').
  rewrite EQ.
  simpl; intros A B; inv A; inv B.
  rewrite <- H1 in H2.
  apply inj_vint in H2.
  rewrite ! (Int.add_commut _ i) in H2.
  apply int_add_eq_l in H2. auto.
Qed.


(* Lemma compat31_32: *)
(*   forall cm bnd al, *)
(*     compat31 cm bnd al -> compat32 cm bnd al. *)
(* Proof. *)
(*   intros cm bnd al. *)
(*   apply compat_larger. *)
(*   unfsize; lia. *)
(* Qed. *)

Lemma norm_unforgeable:
  forall bound align e b o
    (IN: IsNorm.t bound align e (Vptr b o)),
    depends Int.max_unsigned bound align e b.
Proof.
  intros.
  apply is_norm_dep in IN; auto.
Qed.

Section BlocksOfExpr.
  Variable max : Z.
  Variable bound: block -> Z*Z.
  Variable align: block -> int.
  Hypothesis exists_two_cms:
    forall b,
    exists cm cm', compat Int.max_unsigned bound align cm /\
              compat Int.max_unsigned bound align cm' /\
              cm b <> cm' b /\
              (forall b', b <> b' -> cm b' = cm' b').

  (* Hypothesis exists_cm31: *)
  (*   exists cm, compat31 bound align cm. *)
  
  Fixpoint blocks_of (e: expr_sym) :=
    match e with
      Eval (Vptr b i) => b::nil
    | Eval v => nil
    | Eundef _ _ => nil
    | Eunop u t e => blocks_of e
    | Ebinop b t t' e e' => blocks_of e ++ blocks_of e'
    end.

  Definition cm_of_blocks cm bl :=
    fun b =>
      if in_dec peq b bl
      then cm b
      else Int.zero.

  Definition bound_only bl :=
    fun b =>
      if in_dec peq b bl
      then bound b
      else (0,0).

  Definition align_only bl :=
    fun b =>
      if in_dec peq b bl
      then align b
      else Int.mone.

  Lemma compat_blocks_of_e:
    forall sz cm e
      (Pcm : compat sz bound align cm),
      compat sz (bound_only (blocks_of e)) (align_only (blocks_of e)) cm.
  Proof.
    intros.
    inv Pcm; constructor; auto.
    + intros b o IB.
      unfold bound_only in IB.
      destruct (in_dec peq b (blocks_of e)); eauto.
      red in IB; destr; lia.
    + intros b b' o o' diff IB IB'.
      unfold bound_only in IB, IB'.
      destruct (in_dec peq b (blocks_of e)); eauto.
      destruct (in_dec peq b' (blocks_of e)); eauto.
      red in IB'; destr; lia.
      red in IB; destr; lia.
    + intros b.
      unfold align_only.
      destruct (in_dec peq b (blocks_of e)); eauto.
      apply Int.and_mone.
  Qed.

  Lemma isnorm_blocks_of_e:
    forall e v,
      IsNorm.t (bound_only (blocks_of e)) (align_only (blocks_of e)) e v ->
      IsNorm.t bound align e v.
  Proof.
    intros e v [LD].
    constructor; auto.
    red; intros.
    apply LD.
    apply compat_blocks_of_e; auto.
  Qed.

End BlocksOfExpr.


Section NormSpec.

  (** A normalisation function [normalise] is correct if it computes values that
  are correct normalisations. *)
  
  Definition normalise_correct (normalise : norm_typ) : Prop :=
    forall bound align e,
      IsNorm.t bound align e (normalise bound align e).

  (** [Vundef] is always a correct normalisation. *)
  Lemma undef_is_correct_norm :
    forall sz msk e,
      IsNorm.t sz msk e Vundef.
  Proof. 
    intros.
    constructor; auto; try red; auto.
  Qed.

  Section Complete.

    (** A given expression [e] may have two correct normalisations (in the sense
    of [IsNorm.t]). However, when there are two different such values, at least
    one of them is [Vundef]. *)

    Variable env_mem : block -> int -> byte.


    
    (* Axiom bound_dep_ex: *)
    (*   forall bound align e, exists bound', bound_dep bound align e bound'. *)

    Lemma lessdef_nu_eq:
      forall v (NU: v <> Vundef)
        v'
        (LD: Val.lessdef v v'),
        v = v'.
    Proof.
      intros. inv LD; auto. congruence.
    Qed.

    Section Conflict.
      Variable max : Z.
      Variable bound: block -> Z*Z.
      Variable align: block -> int.
      Hypothesis exists_two_cms:
        forall b,
        exists cm cm', compat Int.max_unsigned bound align cm /\
                  compat Int.max_unsigned bound align cm' /\
                  cm b <> cm' b /\
                  (forall b', b <> b' -> cm b' = cm' b').

    
    Lemma conflict_cases:
      forall e v1 v2
             (N1:IsNorm.t bound align e v1)
             (N2:IsNorm.t bound align e v2)
             (diff: v1 <> v2),
        match v1, v2 with
          Vundef, _ => True
        | _, Vundef => True
        | _, _ => False
        end.
    Proof. 
      intros.
      generalize (is_norm_dep _ _ _ _ N1) (is_norm_dep _ _ _ _ N2).
      intros D2 D1.
      inv N1; inv N2.
      
      destruct (exists_two_cms xH) as [cm [_ [Hcm _]]].
      pose proof eval_ok as EOK.
      pose proof eval_ok0 as EOK0.
      specialize (eval_ok _ (fun _ _ => Byte.zero) Hcm).
      specialize (eval_ok0 _ (fun _ _ => Byte.zero) Hcm).
      simpl in *.
      
      destruct (Val.eq v1 Vundef). subst; auto.
      apply lessdef_nu_eq in eval_ok; [|now des v1].
      destruct (Val.eq v2 Vundef). subst; des v1; auto.
      apply lessdef_nu_eq in eval_ok0; [|now des v2].
      rewrite <- eval_ok in eval_ok0.
      des v1; des v2. 
      + apply inj_vint in eval_ok0; auto.
        subst.
        destruct (exists_two_cms b) as (cm0 & cm' & A & B & C & D).
        generalize (EOK _ (fun _ _ => Byte.zero) A).
        generalize (EOK0 _ (fun _ _ => Byte.zero) A).
        simpl.
        intros E F; inv E; inv F.
        rewrite <- H2 in H3.
        apply inj_vint in H3. rewrite ! (Int.add_commut _ i0) in H3.
        apply int_add_eq_l in H3.
        generalize (EOK _ (fun _ _ => Byte.zero) B).
        generalize (EOK0 _ (fun _ _ => Byte.zero) B).
        simpl.
        intros E F; inv E; inv F.
        rewrite <- H4 in H5.
        apply inj_vint in H5. rewrite ! (Int.add_commut _ i0) in H5.
        apply int_add_eq_l in H5. 
        congruence.
      + apply inj_vint in eval_ok0; auto.
        subst.
        destruct (exists_two_cms b) as (cm0 & cm' & A & B & C & D).
        generalize (EOK _ (fun _ _ => Byte.zero) A).
        generalize (EOK0 _ (fun _ _ => Byte.zero) A).
        simpl.
        intros E F; inv E; inv F.
        rewrite <- H2 in H3.
        apply inj_vint in H3. rewrite ! (Int.add_commut _ i) in H3.
        apply int_add_eq_l in H3.
        generalize (EOK _ (fun _ _ => Byte.zero) B).
        generalize (EOK0 _ (fun _ _ => Byte.zero) B).
        simpl.
        intros E F; inv E; inv F.
        rewrite <- H4 in H5.
        apply inj_vint in H5. rewrite ! (Int.add_commut _ i) in H5.
        apply int_add_eq_l in H5. 
        congruence.
      + apply inj_vint in eval_ok0; auto.
        clear n n0.
        destruct (peq b b0).
        *
          subst.
          cut (i = i0).
          intro; subst. congruence.
          generalize (Int.eq_true (Int.add (cm b0) i)).
          rewrite <- eval_ok0 at 1.
          rewrite ! (Int.add_commut (cm b0)).
          rewrite Int.translate_eq.
          intro.
          generalize (Int.eq_spec i0 i). rewrite H; auto.
        * clear diff.
          destruct (exists_two_cms b0) as (cm2 & cm2' & COMP2 & COMP2' & DIFF2 & EQ2).
          specialize (D1 _ COMP2 _ COMP2' DIFF2 (fun _ _ => Byte.zero)).
          apply D1.
          clear - COMP2 COMP2' EOK EQ2 n.
          generalize (EOK _ (fun _ _ => Byte.zero) COMP2).
          generalize (EOK _ (fun _ _ => Byte.zero) COMP2').
          simpl.
          rewrite EQ2; auto.
          intros A B.
          inv A.  inv B.
          congruence.
    Qed.
    
    (** An immediate corollary is that if two values [v] and [v'] are correct 
     * normalisations of an expression [e], and none of them is [Vundef], then 
     * [v] = [v']. *)
    
    Lemma is_norm_unique:
      forall e v v',
        IsNorm.t bound align e v ->
        IsNorm.t bound align e v' ->
        v <> Vundef -> v' <> Vundef ->
        v = v'.
    Proof.
      intros.
      destruct (Val.eq_val_dec v v'); auto.
      generalize (conflict_cases e v v' H H0 n).
      des v; des v'.
    Qed.

    End Conflict.
    (** To rule out this non-determinism, we state that whenever we have a
        choice between [Vundef] and another value [v], we will prefer [v]. *)

    Definition normalise_complete (normalise : norm_typ) : Prop :=
      forall bound align e v,
        IsNorm.t bound align e v ->
        Val.lessdef v (normalise bound align e).

  End Complete.

  Section Normalise.

    Variable norm : norm_typ.
    Variable norm_correct : normalise_correct norm.
    Variable norm_complete : normalise_complete  norm.

    (** Properties of a correct and complete normalisation function. *)
    
    Lemma normalise_undef_cases:
      forall sz msk e
        (Nundef: norm sz msk e = Vundef),
        ~ (exists v, v <> Vundef /\ IsNorm.t sz msk e v).
    Proof.
      intros.
      intros [v [NU IN]].
      generalize (norm_complete sz msk e v IN).
      rewrite Nundef.
      intro A; inv A;
      congruence.
    Qed.

    Lemma deps_same_eval_on:
      forall bound align e e'
        (SE : same_eval_on (compat Int.max_unsigned bound align) e e')
        b
        (DEP: depends Int.max_unsigned bound align e b),
        depends Int.max_unsigned bound align e' b.
    Proof.
      intros.
      red; intros.
      specialize (DEP _ COMP _ COMP' SameB em).
      rewrite <- (SE _ em COMP); auto.
      rewrite <- (SE _ em COMP'); auto.
    Qed.

    Lemma good_result_same_eval_on:
      forall bound align e e'
        (SE : same_eval_on (compat Int.max_unsigned bound align) e e')
        v 
        (GR: good_result Int.max_unsigned bound align e v),
        good_result Int.max_unsigned bound align e' v.
    Proof.
      des v.
      eapply deps_same_eval_on; eauto.
    Qed.
        
    Lemma is_norm_eq :
      forall e e' bound align
        (SE: same_eval_on (compat Int.max_unsigned bound align) e e')
        v
        (IN: IsNorm.t bound align e v),
        IsNorm.t bound align e' v.
    Proof.
      intros.
      destruct IN ; econstructor ; eauto.
      red; intros.
      erewrite <- SE; eauto.
    Qed.

    Lemma lessdef_antisym:
      forall v1 v2,
        Val.lessdef v1 v2 ->
        Val.lessdef v2 v1 ->
        v1 = v2.
    Proof.
      intros.
      inv H; inv H0; auto.
    Qed.
    
    Lemma normalise_eq : 
      forall e e'  bound align
        (SE: same_eval_on (compat Int.max_unsigned bound align) e e'),
        norm bound align e = norm bound align e'.
    Proof.
      intros.
      apply lessdef_antisym.
      {
        eapply norm_complete ; eauto.
        eapply is_norm_eq; eauto. 
      }
      {
        eapply norm_complete ; eauto.
        apply is_norm_eq with (e:=e'); eauto.
        red; intros; symmetry; eauto.
      }
    Qed.
    
    Lemma normalise_ld : 
      forall e e'  bound align
        (LD: lessdef_on (compat Int.max_unsigned bound align) e e'),
        Val.lessdef (norm bound align e) (norm bound align e').
    Proof.
      intros.
      generalize (norm_correct bound align e )
                 (norm_correct bound align e').
      intros A B; inv A; inv B.
      destruct (Val.eq_val_dec (norm bound align e) Vundef) as [A|A].
      rewrite A; auto.
      eapply norm_complete.
      eapply is_norm_eq.
      2: apply norm_correct.
      red; intros.
      specialize (LD cm em Pcm).
      specialize (eval_ok _ em Pcm).
      specialize (eval_ok0 _ em Pcm).
      inv LD; auto. rewrite <- H0 in *.
      inv eval_ok; auto.
      des (norm bound align e).
      des (norm bound align e).
    Qed.
    
  End Normalise.    


End NormSpec.

Ltac clear_useless :=
  repeat
    match goal with
        H: True |- _ => clear H
      | H: ?a = ?a |- _ => clear H
      | H: ?a, H1: ?a |- _ => clear H
    end.









