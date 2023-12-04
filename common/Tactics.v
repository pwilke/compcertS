Require Import Coqlib.
Ltac des t :=
  destruct t eqn:?; try subst; simpl in *;
  try intuition congruence;
  repeat
    match goal with
    | H:_ = left _ |- _ => clear H
    | H:_ = right _ |- _ => clear H
    end.

Ltac destr' := try destr_cond_match; simpl in *; try intuition congruence.

Ltac destr :=
  destr';
  repeat
    match goal with
    | H:_ = left _ |- _ => clear H
    | H:_ = right _ |- _ => clear H
    end.

Ltac destr_in H :=
  match type of H with
  | context [match ?f with
             | _ => _
             end] => des f
  end;
  repeat
    match goal with
    | H:_ = left _ |- _ => clear H
    | H:_ = right _ |- _ => clear H
    end.

Ltac inv H := inversion H; clear H; try subst.
Ltac ami := repeat match goal with
                   | H : context [if ?a then _ else _ ] |- _ => destr_in H
                   | |- _ => destr
                   end.

Definition omap {A B: Type} (f: A -> B) (o: option A): option B :=
  match o with None => None | Some a => Some (f a) end.

Fixpoint filter_map {A B: Type} (f: A -> option B) (l: list A) : list B :=
  match l with
    nil => nil
  | a::r => match f a with
             Some b => b :: filter_map f r
           | None => filter_map f r
           end
  end.


Definition update {A B: Type} (eq: forall (a b: A), {a=b}+{a<>b}) (f: A -> B) (k: A) (b: B) :=
  fun a => if eq a k then b else f a.

    
Ltac rtrim H :=
  repeat (trim H; [clear H; solve [auto; destr]|]).

Ltac unf t H :=
  unfold t in H; repeat destr_in H; try inv H.


Lemma and_impl:
  forall (a b c: Prop),
    (a /\ b -> c) <-> (a -> b -> c).
Proof. destr.
Qed.


Ltac go := solve [repeat (econstructor; destr)].
Ltac autotrim H :=
  repeat match type of H with
           ?a /\ ?b -> ?c => rewrite and_impl in H
         | _ -> ?b =>
           trim H; [
               solve
                 [try match goal with
                        |- ?f _ => unfold f in *; simpl in *
                      | |- ?f _ _ => unfold f in *; simpl in *
                      end;
                   try refine (conj _ _);
                   match goal with
                   | H': ?a |- ?a => exact (H')
                   | H': ?a /\ _ |- ?a => exact ((proj1 H'))
                   | H': _ /\ ?a |- ?a => exact ((proj2 H'))
                   | |- _ => solve [repeat (econstructor; destr)]
                   end]|]
         end.

Ltac ereplace t :=
  let x := fresh in
  let tt := type of t in
  (evar (x: tt);
    replace t with x; unfold x); [|clear x].