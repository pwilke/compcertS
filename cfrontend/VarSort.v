Require Import Coqlib.
Require Import List.

Section S.
  Variable  A : Type.
  Variable le : A -> A -> bool.

  Fixpoint insert (e :A) (l : list A) : list A :=
    match l with
      | nil => e ::l
      | e' ::l => if le e e' then e :: e' :: l
                 else  e' :: (insert e l)
    end.

  Lemma In_insert :
    forall l e a,
      In e (insert a l) <->
      (e = a \/ In e l).
  Proof.
    induction l ; simpl ; intros.
    intuition.
    destr. rewrite IHl in H0. firstorder.
    right. rewrite IHl. auto.
    right. rewrite IHl. auto.
  Qed.


  Fixpoint sort (l : list A) :=
    match l with
      | nil => nil
      | e :: l => insert e (sort l)
    end.

  Lemma In_sort :
    forall l e,
      In e l <-> In e (sort l).
  Proof.
    induction l ; simpl.
    - tauto.
    -
      intros.
      rewrite IHl.
      rewrite In_insert.
      intuition.
  Qed.


  Inductive Sorted: list A -> Prop :=
  | Sorted_nil:
      Sorted nil
  | Sorted_cons: forall hd tl,
      (forall x, In x tl -> le hd x = true) ->
      Sorted tl ->
      Sorted (hd :: tl).

  Hypothesis le_trans: forall a b c, le a b = true -> le b c = true -> le a c = true.
  Hypothesis le_false: forall a b, le a b = false -> le b a = true.
  
  Lemma insert_sorted:
    forall l (s: Sorted l) a,
      Sorted (insert a l).
  Proof.
    induction 1; simpl; intros.
    - constructor. easy. constructor.
    - destr.
      + constructor; auto.
        * simpl; destr. apply H in H1.
          eapply le_trans; eauto.
        * constructor; auto.
      + constructor; auto.
        simpl; intros.
        rewrite In_insert in H0. destr.
        subst. apply le_false; auto.
        apply H; auto.
  Qed.

  Lemma sort_sorted:
    forall l, Sorted (sort l).
  Proof.
    induction l; simpl; intros.
    - constructor.
    - apply insert_sorted; auto.
  Qed.

  Lemma insert_split:
    forall a l,
    exists l1 l2, insert a l = l1 ++ a::l2 /\ l = l1 ++ l2.
  Proof.
    induction l; simpl; intros.
    - exists nil, nil. split; reflexivity.
    - destruct IHl as [l1 [l2 [B C]]].
      destr.
      exists nil, (a0::l); split; reflexivity.
      rewrite B.
      exists (a0::l1), l2; split. reflexivity. rewrite C; reflexivity.
  Qed.
  
  Require Import Permutation.
  
  Lemma sort_permut:
    forall l, Permutation l (sort l).
  Proof.
    induction l; simpl; intros.
    auto.
    destruct (insert_split a (sort l)) as [l1 [l2 [B C]]].
    rewrite B.
    rewrite <- Permutation_middle.
    constructor. rewrite <- C. auto.
  Qed.

  Lemma filter_if:
    forall A (f: A -> bool) (a:bool) b c,
      filter f (if a then b else c) = if a then filter f b else filter f c.
  Proof.
    intros; destr.
  Qed.

  Lemma insert_le:
    forall l a0 a, 
      le a0 a = true -> 
      (forall x : A, In x l -> le a x = true) ->
      insert a0 l = a0::l.
  Proof.
    induction l; simpl; intros; auto.
    destr.
    erewrite le_trans in Heqb. congruence.
    eauto. apply H0. auto.
  Qed.
  
  Lemma filter_insert:
    forall f l a, Sorted l -> filter f (insert a l) =
             (if f a then insert a (filter f l) else filter f l).
  Proof.
    induction l; simpl; intros; auto.
    rewrite filter_if.
    simpl. rewrite IHl by (inv H; auto).
    repeat destr.
    inv H.
    erewrite insert_le. auto. eauto.
    intros. apply  H2.
    rewrite filter_In in H. destr.
  Qed.
  
  Lemma filter_sort:
    forall f l,
      filter f (sort l) = sort (filter f l).
  Proof.
    induction l; simpl; intros.
    - auto.
    - transitivity (if f a then sort (a::filter f l) else sort (filter f l)); [|now destr].
      simpl.
      rewrite <- IHl.
      intros; apply filter_insert.
      apply sort_sorted.
  Qed.
  
End S.


Require Import Ctypes.
Require Import PpsimplZ.
Require Import Psatz.

Definition le1 (a b : (AST.ident * type)) : bool :=
  proj_sumbool (zle (sizeof (snd a)) (sizeof (snd b))).

Lemma le1_trans: forall a b c, le1 a b = true -> le1 b c = true -> le1 a c = true.
Proof.
  unfold le1.
  intros.
  repeat match goal with
           H: proj_sumbool (zle ?a ?b) = true |- _ => destruct (zle a b)
         | |- proj_sumbool (zle ?a ?b) = true => destruct (zle a b)
         end; auto; try lia.
Qed.

Lemma le1_false: forall a b, le1 a b = false -> le1 b a = true.
Proof.
  unfold le1; intros.
  repeat match goal with
           H: proj_sumbool (zle ?a ?b) = _ |- _ => destruct (zle a b)
         | |- proj_sumbool (zle ?a ?b) = true => destruct (zle a b)
         end; auto; try lia.
Qed.

Definition varsort := sort _ le1.

Definition varsort_sorted := sort_sorted _ _ le1_trans le1_false.
Definition varsort_permut := sort_permut _ le1.
Definition varsort_filter := filter_sort _ _ le1_trans le1_false.


Definition le2 (a b : (AST.ident * Z)) : bool :=
  proj_sumbool (zle ((snd a)) (snd b)).

Lemma le2_trans: forall a b c, le2 a b = true -> le2 b c = true -> le2 a c = true.
Proof.
  unfold le2.
  intros.
  repeat match goal with
           H: proj_sumbool (zle ?a ?b) = true |- _ => destruct (zle a b)
         | |- proj_sumbool (zle ?a ?b) = true => destruct (zle a b)
         end; auto; try lia.
Qed.

Lemma le2_false: forall a b, le2 a b = false -> le2 b a = true.
Proof.
  unfold le2; intros.
  repeat match goal with
           H: proj_sumbool (zle ?a ?b) = _ |- _ => destruct (zle a b)
         | |- proj_sumbool (zle ?a ?b) = true => destruct (zle a b)
         end; auto; try lia.
Qed.

Definition varsort' := sort _ le2.

Definition varsort'_sorted := sort_sorted _ _ le2_trans le2_false.
Definition varsort'_permut := sort_permut _ le2.
Definition varsort'_filter := filter_sort _ _ le2_trans le2_false.