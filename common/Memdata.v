(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** In-memory representation of values. *)

Require Import Coqlib.
Require Import Axioms.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import Maps.
Require Import Floats.
Require Import Values.
Require Import Psatz.
Require Import Values_symbolictype.
Require Import Values_symbolic.
Require Import Normalise.
Require Import NormaliseSpec.
Require Import IntFacts.
Require Import ExprEval.

(** * Properties of memory chunks *)

(** Memory reads and writes are performed by quantities called memory chunks,
  encoding the type, size and signedness of the chunk being addressed.
  The following functions extract the size information from a chunk. *)

Definition big_endian : bool := Archi.big_endian.
Lemma be_arch: big_endian = Archi.big_endian.
  Proof. reflexivity. Qed.
Global Opaque big_endian.

Lemma be_rew:
  big_endian = Archi.big_endian.
Proof.
  rewrite be_arch; auto.
Qed.

Definition size_chunk (chunk: memory_chunk) : Z :=
  match chunk with
  | Mint8signed => 1
  | Mint8unsigned => 1
  | Mint16signed => 2
  | Mint16unsigned => 2
  | Mint32 => 4
  | Mint64 => 8
  | Mfloat32 => 4
  | Mfloat64 => 8
  | Many32 => 4
  | Many64 => 8
  end.

Lemma size_chunk_pos:
  forall chunk, size_chunk chunk > 0.
Proof.
  intros. destruct chunk; simpl; omega.
Qed.

Definition size_chunk_nat (chunk: memory_chunk) : nat :=
  nat_of_Z(size_chunk chunk).
  
Lemma size_chunk_nat_sup_0:
  forall chunk, (size_chunk_nat chunk > 0)%nat.
Proof.
  destruct chunk; unfold size_chunk_nat; simpl; unfold Pos.to_nat; simpl; omega.
Qed.

Lemma size_chunk_conv:
  forall chunk, size_chunk chunk = Z_of_nat (size_chunk_nat chunk).
Proof.
  intros. destruct chunk; reflexivity.
Qed.

Lemma size_chunk_nat_pos:
  forall chunk, exists n, size_chunk_nat chunk = S n.
Proof.
  intros. 
  generalize (size_chunk_pos chunk). rewrite size_chunk_conv. 
  destruct (size_chunk_nat chunk).
  simpl; intros; omegaContradiction.
  intros; exists n; auto.
Qed.

(** Memory reads and writes must respect alignment constraints:
  the byte offset of the location being addressed should be an exact
  multiple of the natural alignment for the chunk being addressed.
  This natural alignment is defined by the following 
  [align_chunk] function.  Some target architectures
  (e.g. PowerPC and x86) have no alignment constraints, which we could
  reflect by taking [align_chunk chunk = 1].  However, other architectures
  have stronger alignment requirements.  The following definition is
  appropriate for PowerPC, ARM and x86. *)

Definition align_chunk (chunk: memory_chunk) : Z := 
  match chunk with
  | Mint8signed => 1
  | Mint8unsigned => 1
  | Mint16signed => 2
  | Mint16unsigned => 2
  | Mint32 => 4
  | Mint64 => 8
  | Mfloat32 => 4
  | Mfloat64 => 4
  | Many32 => 4
  | Many64 => 4
  end.

Lemma align_chunk_pos:
  forall chunk, align_chunk chunk > 0.
Proof.
  intro. destruct chunk; simpl; omega.
Qed.

Lemma align_size_chunk_divides:
  forall chunk, (align_chunk chunk | size_chunk chunk).
Proof.
  intros. destruct chunk; simpl; try apply Zdivide_refl; exists 2; auto. 
Qed.

Lemma align_le_divides:
  forall chunk1 chunk2,
  align_chunk chunk1 <= align_chunk chunk2 -> (align_chunk chunk1 | align_chunk chunk2).
Proof.
  intros. destruct chunk1; destruct chunk2; simpl in *;
  solve [ omegaContradiction
        | apply Zdivide_refl
        | exists 2; reflexivity
        | exists 4; reflexivity
        | exists 8; reflexivity ].
Qed.

Inductive quantity : Type := Q32 | Q64.

Definition quantity_eq (q1 q2: quantity) : {q1 = q2} + {q1 <> q2}.
Proof. decide equality. Defined.
Global Opaque quantity_eq.

Definition size_quantity_nat (q: quantity) :=
  match q with Q32 => 4%nat | Q64 => 8%nat end.

Lemma size_quantity_nat_pos:
  forall q, exists n, size_quantity_nat q = S n.
Proof.
  intros. destruct q; [exists 3%nat | exists 7%nat]; auto.
Qed.

(** * Memory values *)

(** A ``memory value'' is a byte-sized quantity that describes the current
  content of a memory cell.  With our new model, a [memval] can only be a
  byte-sized fragment of an opaque symbolic expression; *)

(** Values stored in memory cells. *)

Inductive memval: Type :=
  | Symbolic : expr_sym -> option styp -> nat -> memval.

(** We lift this equivalence to [memval]s.  *)

(* Definition tcheck_memval (mv : memval) : option styp := *)
(*   match mv with *)
(*       Symbolic e n => tcheck_expr e *)
(*   end. *)



(** * Encoding and decoding integers *)

(** We define functions to convert between integers and lists of bytes
  of a given length *)

Fixpoint bytes_of_int (n: nat) (x: Z) {struct n}: list byte :=
  match n with
  | O => nil
  | S m => Byte.repr x :: bytes_of_int m (x / 256)
  end.

Fixpoint int_of_bytes (l: list byte): Z :=
  match l with
  | nil => 0
  | b :: l' => Byte.unsigned b + int_of_bytes l' * 256
  end.

Definition rev_if_be {A:Type} (l: list A) : list A :=
  if big_endian then List.rev l else l.

Lemma rev_if_be_nil:
  forall A, rev_if_be (nil (A:=A)) = (nil (A:=A)).
Proof.
  unfold rev_if_be; destr.
Qed.

Lemma rev_if_be_one:
  forall {A} (a:A),
    rev_if_be (a::nil) = a::nil.
Proof.
  unfold rev_if_be; destr.
Qed.

Lemma in_rib:
  forall {A} (a:A) l,
  In a l ->
  In a (rev_if_be l).
Proof.
  intros; unfold rev_if_be; destr.
  apply in_rev in H; auto.
Qed.

Lemma rev_rev_if_be_involutive:
  forall {A} (l: list A),
    rev (rev_if_be (rev (rev_if_be l))) = l.
Proof.
  unfold rev_if_be; destr; repeat rewrite rev_involutive; auto.
Qed.
Lemma revi_rev_revi:
  forall A (l:list A),
    rev_if_be (rev (rev_if_be l)) = rev l.
Proof.
  unfold rev_if_be; destr; repeat rewrite rev_involutive; auto.
Qed.

Lemma list_forall2_rib:
forall {A} (P:A -> A -> Prop) (l l': list A),
    list_forall2 P l l' ->
    list_forall2 P (rev_if_be l) (rev_if_be l').
Proof.  
  intros.
  unfold rev_if_be; destr.
  apply list_forall2_rev; auto.
Qed.

Lemma list_forall2_rib_inv:
forall {A} (P:A -> A -> Prop) (l l': list A),
  list_forall2 P (rev_if_be l) (rev_if_be l') ->
  list_forall2 P l l'.
Proof.  
  unfold rev_if_be; destr.
  apply list_forall2_rev in H; auto.
  rewrite ! rev_involutive in H; auto.
Qed.

Lemma Exists_rev:
  forall {A} (P:A-> Prop) (l: list A),
    Exists P l -> Exists P (rev l).
Proof.
  intros.
  apply Exists_exists in H.
  apply Exists_exists.
  destruct H as [x [C B]].
  exists x.
  split; auto.
  apply in_rev.
  rewrite rev_involutive; auto.
Qed.

Lemma Exists_rib:
  forall {A} (P:A-> Prop) (l: list A),
    Exists P l -> Exists P (rev_if_be l).
Proof.
  intros.
  unfold rev_if_be; destr.
  apply Exists_rev in H; auto.
Qed.

Lemma Exists_rib_inv:
  forall {A} (P:A-> Prop) (l: list A),
    Exists P (rev_if_be l) -> Exists P l.
Proof.
  intros.
  unfold rev_if_be in H; revert H; destr.
  apply Exists_rev in H; auto.
  rewrite rev_involutive in H; auto.
Qed.

Lemma Forall_rib:
  forall {A} (P: A -> Prop) (l: list A),
    Forall P l ->
    Forall P (rev_if_be l).
Proof.
  unfold rev_if_be; destr.
  apply Forall_rev.
  rewrite rev_involutive; auto.
Qed.

Lemma map_rev_if_be:
  forall {A B} (f: A -> B) (l: list A),
    map f (rev_if_be l) =
    rev_if_be (map f l).
Proof.
  induction l; simpl; unfold rev_if_be in *; destr.
  rewrite map_app.
  simpl.
  rewrite IHl; reflexivity.
Qed.

Lemma rev_rev_if_be:
  forall {A} (l: list A),
    rev (rev_if_be l) = rev_if_be (rev l).
Proof.
  induction l; simpl in *; unfold rev_if_be in *; destr.
Qed.

Definition encode_int (sz: nat) (x: Z) : list byte :=
  rev_if_be (bytes_of_int sz x).

Definition decode_int (b: list byte) : Z :=
  int_of_bytes (rev_if_be b).

(** Length properties *)

Lemma length_bytes_of_int:
  forall n x, length (bytes_of_int n x) = n.
Proof.
  induction n; simpl; intros. auto. decEq. auto.
Qed.

Lemma rev_if_be_length:
  forall (A:Type) (l:list A), length (rev_if_be l) = length l.
Proof.
  intros; unfold rev_if_be; destruct big_endian.
  apply List.rev_length.
  auto.
Qed.

Lemma rev_if_be_involutive:
  forall A (l:list A), rev_if_be (rev_if_be l) = l.
Proof.
  intros; unfold rev_if_be; destruct big_endian. 
  apply List.rev_involutive. 
  auto.
Qed.

(** A length-[n] encoding depends only on the low [8*n] bits of the integer. *)

Lemma bytes_of_int_mod:
  forall n x y,
  Int.eqmod (two_p (Z_of_nat n * 8)) x y ->
  bytes_of_int n x = bytes_of_int n y.
Proof.
  induction n.
  intros; simpl; auto.
  intros until y.
  rewrite inj_S. 
  replace (Zsucc (Z_of_nat n) * 8) with (Z_of_nat n * 8 + 8) by omega.
  rewrite two_p_is_exp; try omega. 
  intro EQM.
  simpl; decEq. 
  apply Byte.eqm_samerepr. red. 
  eapply Int.eqmod_divides; eauto. apply Zdivide_factor_l.
  apply IHn.
  destruct EQM as [k EQ]. exists k. rewrite EQ. 
  rewrite <- Z_div_plus_full_l. decEq. change (two_p 8) with 256. ring. omega.
Qed.

Lemma encode_int_8_mod:
  forall x y,
  Int.eqmod (two_p 8) x y ->
  encode_int 1%nat x = encode_int 1%nat y.
Proof.
  intros. unfold encode_int. decEq. apply bytes_of_int_mod. auto.
Qed.

Lemma encode_int_16_mod:
  forall x y,
  Int.eqmod (two_p 16) x y ->
  encode_int 2%nat x = encode_int 2%nat y.
Proof.
  intros. unfold encode_int. decEq. apply bytes_of_int_mod. auto.
Qed.

(** * Encoding and decoding values *)

Fixpoint inj_symbolic' (n: nat) (e:expr_sym) t {struct n}: list memval :=
  match n with
  | O => nil
  | S m => Symbolic e t m :: inj_symbolic' m e t
  end.

Definition get_type (e: expr_sym) : styp :=
  if wt_expr_dec e Tint
  then Tint
  else if wt_expr_dec e Tfloat
       then Tfloat
       else if wt_expr_dec e Tsingle
            then Tsingle
            else if wt_expr_dec e Tlong
                 then Tlong
                 else Tint.

Lemma get_type_correct:
  forall e,
    wt_expr e (get_type e) \/ ~ exists t, wt_expr e t.
Proof.
  unfold get_type; repeat destr.
  right; intro; dex. des t.
Qed.

Definition inj_symbolic (n:nat) (e:expr_sym) (t:option styp) : list memval :=
  rev (rev_if_be (inj_symbolic' n e t)).

Lemma inj_symbolic_length:
  forall e t n,
    length (inj_symbolic n e t) = n.
Proof.
  induction n; simpl; intros; auto.
  revert IHn.
  unfold inj_symbolic in *.
  unfold rev_if_be.
  destr_cond_match.
  rewrite ! rev_involutive; simpl; auto.
  rewrite ! rev_length.
  simpl. auto.
Qed.

Definition to_bits (c: memory_chunk) (v: expr_sym) : expr_sym :=
  match c with
    | Mfloat32          => Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint
                                 (Eunop OpBitsofsingle Tsingle v)
    | Mfloat64          => Eunop OpBitsofdouble Tfloat v
    | Mint8signed
    | Mint8unsigned
    | Mint16signed
    | Mint16unsigned
    | Mint32            => Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint v
    | Mint64            => v
    | Many32            => match get_type v with
                            Tsingle => 
                            Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned))
                                  Tint (Eunop OpBitsofsingle Tsingle v)
                          | Tint => Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned))
                                         Tint v
                          | _ => Eval Vundef
                          end
    | Many64            => match get_type v with
                            Tfloat => Eunop OpBitsofdouble Tfloat v
                          | Tsingle => Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned))
                                            Tint (Eunop OpBitsofsingle Tsingle v)
                          | Tint => Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint v
                          | Tlong => v
                          end
  end. 

Lemma same_eval_nwt_vundef:
  forall v1 v2 t
    (WT: wt_expr v1 t)
    (NWT: ~ wt_expr v2 t)
    (SE: same_eval v1 v2)
    alloc em,
    eSexpr alloc em v1 = Vundef /\ eSexpr alloc em v2 = Vundef.
Proof.
  intros.
  cut (eSexpr alloc em v2 = Vundef).
  split; auto. rewrite SE; auto.
  eapply expr_type'; eauto.
  rewrite <- SE.
  apply expr_type; auto.
Qed.

Lemma get_type_correct_not_int:
  forall e,
    get_type e <> Tint ->
    wt_expr e Tint -> False.
Proof.
  intros.
  unfold get_type in *; repeat (revert H; destr).
Qed.

Lemma to_bits_same_eval:
  forall v v' chunk,
    same_eval v v' ->
    same_eval (to_bits chunk v) (to_bits chunk v').
Proof.
  intros.
  unfold to_bits.
  destruct chunk; auto;
  repeat apply unop_same_eval; auto.
  - generalize (get_type_correct_not_int v').
    destruct (get_type_correct v), (get_type_correct v').
    destruct (wt_expr_dec v' (get_type v)).
    repeat destr; repeat apply unop_same_eval; auto;
    try (red; intros; simpl; rewrite (wt_expr_2_is_undef v' _ _ H1 w); [reflexivity| congruence]).
    red; intros; simpl; generalize (wt_expr_2_is_undef v' _ _ H1 w). intro A; trim A; try congruence.
    subst. rewrite H. destr.
    red; intros; simpl; generalize (wt_expr_2_is_undef v' _ _ H1 w). intro A; trim A; try congruence.
    subst.
    destr.
    red; intros; simpl; generalize (wt_expr_2_is_undef v' _ _ H1 w). intro A; trim A; try congruence.
    subst. rewrite H. destr.

    red; intros. generalize (same_eval_nwt_vundef _ _ _ H0 n H cm em). intros [A1 A2].
    repeat destr; try rewrite A1; try rewrite A2; destr.

    assert (n : ~ wt_expr v' (get_type v)).
    intro A; apply H1; exists (get_type v); auto.
    red; intros. generalize (same_eval_nwt_vundef _ _ _ H0 n H cm em). intros [A1 A2].
    repeat destr; try rewrite A1; try rewrite A2; destr.

    assert (n : ~ wt_expr v (get_type v')).
    intro A; apply H0; exists (get_type v'); auto.
    red; intros. generalize (same_eval_nwt_vundef _ _ _ H1 n (same_eval_sym _ _ H) cm em). intros [A1 A2].
    repeat destr; try rewrite A1; try rewrite A2; destr.

    red; intros.
    generalize (nwt_expr_undef cm em _ H0).
    generalize (nwt_expr_undef cm em _ H1).
    intros A1 A2.
    repeat destr; try rewrite A1; try rewrite A2; destr.

  - generalize (get_type_correct_not_int v').
    destruct (get_type_correct v), (get_type_correct v').
    destruct (wt_expr_dec v' (get_type v)).
    + generalize (wt_expr_2_is_undef _ _ _ H1 w).
      repeat destr; repeat apply unop_same_eval; auto;
      try (red; intros; simpl; rewrite (wt_expr_2_is_undef v' _ _ H1 w); [reflexivity| congruence]);
      subst; destr;
      red; intros; destr; rewrite H; destr.
    + red; intros. generalize (same_eval_nwt_vundef _ _ _ H0 n H cm em). intros [A1 A2].
      repeat destr; try rewrite A1; try rewrite A2; destr.
    + assert (n : ~ wt_expr v' (get_type v)).
      intro A; apply H1; exists (get_type v); auto.
      red; intros. generalize (same_eval_nwt_vundef _ _ _ H0 n H cm em). intros [A1 A2].
      repeat destr; try rewrite A1; try rewrite A2; destr.
    + assert (n : ~ wt_expr v (get_type v')).
      intro A; apply H0; exists (get_type v'); auto.
      red; intros. generalize (same_eval_nwt_vundef _ _ _ H1 n (same_eval_sym _ _ H) cm em). intros [A1 A2].
      repeat destr; try rewrite A1; try rewrite A2; destr.
    + red; intros.
      generalize (nwt_expr_undef cm em _ H0).
      generalize (nwt_expr_undef cm em _ H1).
      intros A1 A2.
      repeat destr; try rewrite A1; try rewrite A2; destr.
Qed.

Definition encode_val (chunk: memory_chunk) (v: expr_sym) : list memval :=
  inj_symbolic (size_chunk_nat chunk) (to_bits chunk v)
               (match chunk with Many32|Many64 => Some (get_type v)
                                 | _ => None end).

Lemma encode_val_length:
  forall chunk v ,
    length (encode_val chunk v) = size_chunk_nat chunk.
Proof.
  intros.
  unfold encode_val.
  rewrite inj_symbolic_length. auto.
Qed.

(** [get_nth_part e n t] extracts the [n]th byte of expression [e] of type [t]  *)
Fixpoint get_nth_part (e:expr_sym) (n:nat) :=
  match n with
      O   => Ebinop OpAnd Tlong Tlong e (Eval (Vlong (Int64.repr 255)))
    | S m => get_nth_part (Ebinop (OpShr SEUnsigned) Tlong Tint e (Eval (Vint (Int.repr 8)))) m
  end.

Lemma gnp_eSexpr:
  forall n e f,
    same_eval e f ->
    same_eval (get_nth_part e n) (get_nth_part f n).
Proof.
  induction n; red; simpl; intros.
  rewrite H; auto.
  apply IHn; auto.
  red; simpl; intros. 
  rewrite H; auto.
Qed.

Fixpoint get_nth_part_val (v:val) (n:nat) : val :=
  match v with
      Vlong i =>
      match n with
          O => Vlong (Int64.and i (Int64.repr 255))
        | S m => get_nth_part_val (Vlong (Int64.shru i (Int64.repr 8))) m
      end
    | _ => Vundef
  end.

Lemma gnp_rew:
  forall alloc em  n e,
    eSexpr alloc em  (get_nth_part e n) = get_nth_part_val (eSexpr alloc em  e) n.
Proof.
  induction n; simpl; intros.
  - destr. 
  - rewrite IHn; simpl; auto.  destr; des n.
Qed.

Lemma get_nth_part_bnds:
  forall n i j l,
    j >= 8 ->
    get_nth_part_val i n = Vlong l ->
    Int64.testbit l j = false.
Proof.
  induction n; simpl; intuition try omega.
  - des i. inv H0.
    destruct (zlt j Int64.zwordsize).
    rewrite Int64.bits_and; auto; try omega.
    rewrite Int64.testbit_repr; try omega.
    rewrite Int64.Ztestbit_above with (n:=8%nat); auto; try omega.
    ring.
    unfold two_power_nat, shift_nat; simpl; omega.
    eapply Int64.Ztestbit_above; eauto.
    apply Int64.unsigned_range.
  - des i . eapply IHn in H0; eauto.
Qed.

Lemma get_nth_part_val_le:
  forall n i l,
    get_nth_part_val i n = Vlong l ->
    0 <= Int64.unsigned l <= 255.
Proof.
  induction n; simpl; intros.
  - destruct i; inv H.
    change 255 with (Int64.unsigned (Int64.repr 255)) at 3.
    split.
    generalize (Int64.unsigned_range (Int64.and i (Int64.repr 255))); intros; omega.
    apply Int64.bits_le.
    intros.
    rewrite Int64.bits_and in H0; auto.
    apply andb_true_iff in H0; intuition.
  - destruct i; inv H. eapply IHn; eauto.
Qed.

  (** [expr_of_memval] transforms a [memval] into the corresponding [expr_sym]. *)
Definition expr_of_memval (m:memval) : expr_sym :=
  match m with
    | Symbolic e t n => get_nth_part e n
  end.

Lemma expr_of_memval_bound:
  forall alloc em  mv l,
    eSexpr alloc em  (expr_of_memval mv) = Vlong l ->
    Int64.unsigned l < 256.
Proof.
  intros.
  des mv.
  revert H. rewrite gnp_rew.
  des (get_nth_part_val (eSexpr alloc em  e) n); inv H. 
  generalize (get_nth_part_val_le _ _ _ Heqv).
  intros. omega.
Qed.


Lemma nth_error_property:
  forall {A: Type} {P: A -> A -> Prop} l l'
         (LF: list_forall2 P l l') n a b,
    nth_error l  n = Some a ->
    nth_error l' n = Some b ->
    P a b.
Proof.
  induction 1; simpl; intros.
  destruct n; simpl in H; discriminate.
  destruct n; simpl in *.
  - inv H0; inv H1; auto.
  - apply IHLF with (n:=n); auto.
Qed.


(** [proj_symbolic_aux_le] transforms a list of [memval] into the
  corresponding symbolic expression, interpreting [vl] as a little-endian sorted
  list.  *)
  
Fixpoint proj_symbolic_aux_le (vl: list memval) : expr_sym :=
  match vl with
      nil => Eval (Vlong Int64.zero)
    | a :: r =>
      Ebinop OpAdd Tlong Tlong
             (expr_of_memval a)
             (Ebinop OpShl Tlong Tint
                     (proj_symbolic_aux_le r)
                     (Eval (Vint (Int.repr 8))))
  end.


  Lemma psa_wt_expr:
    forall alloc em  l,
      wt_val (eSexpr alloc em  (proj_symbolic_aux_le l)) Tlong.
  Proof.
    induction l; simpl; intros; auto.
    seval.
  Qed.

  Lemma psa_le_app_rew:
    forall l1 l2,
      same_eval (proj_symbolic_aux_le (l1 ++ l2))
                (Val.addl
                   (proj_symbolic_aux_le l1)
                   (Val.mull
                      (proj_symbolic_aux_le l2)
                      (Eval (Vlong (Int64.repr (256^Z.of_nat (length l1))))))).
  Proof.
    induction l1; simpl; intros.
    - red; intros.  generalize (psa_wt_expr cm em  l2).  seval.
      rewrite Int64.mul_one. rewrite Int64.add_zero_l; auto.
    - red; simpl; intros. rewrite IHl1. clear IHl1. simpl.
      seval.
      assert_val true. vm_compute; auto. simpl.
      f_equal.
      repeat rewrite shl'_shl by
          (rewrite Int.unsigned_repr; try omega; unfold Int.max_unsigned; simpl; omega).
      repeat rewrite Int.unsigned_repr by (unfold Int.max_unsigned; simpl; omega).
      rewrite Int64.add_assoc. f_equal.
      rewrite Int64.shl_mul_two_p.
      rewrite Int64.mul_add_distr_l.
      rewrite <- Int64.shl_mul_two_p.
      f_equal.
      rewrite Int64.mul_assoc.
      f_equal.
      rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; simpl; omega).
      unfold two_p.
      unfold two_power_pos; simpl.
      unfold shift_pos; simpl.
      unfold Z.of_nat.
      destr. 
      rewrite Z.pow_pos_fold.
      zify.
      rewrite <- Zpos_P_of_succ_nat.
      generalize (Pos.of_succ_nat n); clear; intros.
      simpl.
      repeat rewrite Z.pow_pos_fold.
      replace (256 ^ Z.pos (Pos.succ p)) with (256 ^ Z.pos p * 256). 
      * generalize (256 ^ Z.pos p); intro.
        change 256 with (two_p (Int64.unsigned (Int64.repr 8))).
        rewrite <- Int64.shl_mul_two_p.
        change (Int64.unsigned (Int64.repr 8)) with 8.
        rewrite <- Int64.Zshiftl_mul_two_p by omega.
        apply Int64.same_bits_eq; intros.
        rewrite Int64.bits_shl by omega.
        change (Int64.unsigned (Int64.repr 8)) with 8.
        destruct (zlt i 8).
        rewrite Int64.testbit_repr; auto.
        rewrite Z.shiftl_spec_low; auto; omega.
        repeat rewrite Int64.testbit_repr; auto; try lia.
        rewrite Z.shiftl_spec_high; auto; try lia.
      * replace (Z.pos (Pos.succ p)) with (Z.pos p + 1).
        rewrite Z.pow_add_r.
        f_equal.
        zify; lia.
        lia.
        zify. lia.
  Qed.

Lemma psa_le_n_bnds:
  forall l n,
    (length l <= n)%nat ->
    forall alloc em  i,
      eSexpr alloc em  (proj_symbolic_aux_le l) = Vlong i ->
      Int64.unsigned i < 256 ^ (Z.of_nat n).
Proof.
  induction l; simpl in *; intuition try congruence.
  - inv H0. 
    change (Int64.unsigned Int64.zero) with 0.
    clear.
    apply Z.pow_pos_nonneg; try lia.
  - repeat (revert H0; seval).
    assert_val true. vm_compute; auto.
    intro A; inv A.
    eapply IHl in Heqv0; eauto.
    des n. lia.
    des a. rewrite gnp_rew in Heqv. apply get_nth_part_val_le in Heqv. 
    rewrite shl'_shl by (vm_compute; intuition congruence).
    change (Int.unsigned (Int.repr 8)) with 8.
    rewrite Int64.add_is_or. 
    + generalize (Int64.or_interval i0 (Int64.shl i1 (Int64.repr 8))).
      simpl.
      intros. 
      change 256 with (two_p 8) in *.
      assert (8 >= Int64.size i0).
      { apply Int64.size_interval_2; auto; try lia.
        split. lia. change (two_p 8) with 256. lia.
      }
      rewrite two_p_equiv in Heqv0.
      rewrite <- Z.pow_mul_r in Heqv0; try lia.
      rewrite <- two_p_equiv in Heqv0.
      assert (8*Z.of_nat n0 >= Int64.size i1).
      { apply Int64.size_interval_2; auto; try lia. 
        generalize (Int64.unsigned_range i1); split; try lia.
        eapply Z.lt_le_trans; eauto.
        apply two_p_monotone.
        split; lia.
      }
      cut ( two_p
              (Z.max (Int64.size i0) (Int64.size (Int64.shl i1 (Int64.repr 8)))) <=
            two_p 8 ^ (Z.pos (Pos.of_succ_nat n0))).
      revert H0.
      generalize (   two_p (Z.max (Int64.size i0) (Int64.size (Int64.shl i1 (Int64.repr 8))))); intro.
      intros.  simpl in H3. simpl. lia.
      rewrite (two_p_equiv 8).
      rewrite <- Z.pow_mul_r ; try lia.
      rewrite <- two_p_equiv . 
      apply two_p_monotone.
      split.
      generalize (Int64.size_range i0).
      generalize (Int64.size_range (Int64.shl i1 (Int64.repr 8))).
      unfold Z.max; destr; lia.
      assert (Z.max (Int64.size i0) (Int64.size (Int64.shl i1 (Int64.repr 8))) =
              Int64.size i0 \/
              Z.max (Int64.size i0) (Int64.size (Int64.shl i1 (Int64.repr 8))) =
              Int64.size (Int64.shl i1 (Int64.repr 8))).
      unfold Z.max; destr.
      destruct H3 as [H3|H3]; rewrite H3.
      cut ( 8 <= 8* Z.pos (Pos.of_succ_nat n0)).
      intro; lia.
      change (8*1 <= 8*Z.pos (Pos.of_succ_nat n0)).
      apply Zmult_le_compat; try lia.
      apply Int64.bits_size_3.
      lia. 
      intros.
      rewrite Int64.bits_shl; try (split) ; try lia;  auto.
      change (Int64.unsigned (Int64.repr 8)) with 8.
      destruct (zlt i 8); auto.
      rewrite <- (Int64.repr_unsigned i1).
      rewrite Int64.testbit_repr; auto; try lia.
      apply Int64.Ztestbit_above with (n:=mult 8 n0); try lia.
      split.
      generalize (Int64.unsigned_range i1); lia.
      rewrite two_power_nat_two_p.
      replace (Z.of_nat (8*n0)) with (8*Z.of_nat n0); auto.
      destruct (eq_nat_dec (length l) n0); subst; auto.
      transitivity (two_p (8*Z.of_nat (length l))); auto.
      apply two_p_monotone_strict. split; lia.
      rewrite Nat2Z.inj_mul; auto.
    + solve_long.
      cut (Int64.testbit i0 i = false).
      intro A; rewrite A; ring.
      rewrite <- (Int64.repr_unsigned i0).
      rewrite Int64.testbit_repr; auto.
      rewrite Int64.Ztestbit_above with (n:=8%nat); auto.
      unfold two_power_nat, shift_nat; simpl.
      generalize (Int64.unsigned_range i0); intro.
      split; try lia.
Qed.

Lemma psa_le_app:
  forall l1 l2,    
    length l1 = 4%nat ->
    length l2 = 4%nat ->
    same_eval (proj_symbolic_aux_le (l1 ++ l2))
              (Val.longofwords
                 (Val.loword (proj_symbolic_aux_le l2)) 
                 (Val.loword (proj_symbolic_aux_le l1))).
Proof.
  red; intros.
  rewrite psa_le_app_rew.
  simpl.
  rewrite H.
  seval.
  eapply psa_le_n_bnds in Heqv; eauto.
  eapply psa_le_n_bnds in Heqv0; eauto.
  rewrite H in Heqv.
  rewrite H0 in Heqv0.
  f_equal. 
  assert (forall i i1, Int64.unsigned i < 256 ^ Z.of_nat 4 ->
                       32 <= i1 < 64 -> Int64.testbit i i1 = false). 
  {
    clear; intros.
    rewrite <- (Int64.repr_unsigned i).
    rewrite Int64.testbit_repr; auto; try rewrite int64_zwordsize; try lia.
    rewrite Int64.Ztestbit_above with (n:=32%nat); auto; simpl; try lia.
    generalize (Int64.unsigned_range i); split; try lia.
    change (two_power_nat 32) with (Z.pow_pos 256 4); auto.
  }
  solve_long.
  rewrite Int64.bits_ofwords; auto.
  rewrite Int64.add_is_or.
  - rewrite Int64.bits_or; auto.
    destr; rewrite Int64.bits_loword; try lia.
    + rewrite int_zwordsize, int64_zwordsize in *.
      change (Z.pow_pos 256 4) with (two_p (Int64.unsigned (Int64.repr 32))).
      rewrite <- Int64.shl_mul_two_p. 
      rewrite Int64.bits_shl.
      change (Int64.unsigned (Int64.repr 32)) with 32.
      destr; try lia.
      apply orb_false_r.
      rewrite int64_zwordsize; auto.
    + rewrite int_zwordsize, int64_zwordsize in *.
      change (Z.pow_pos 256 4) with (two_p (Int64.unsigned (Int64.repr 32))).
      rewrite <- Int64.shl_mul_two_p. 
      rewrite Int64.bits_shl.
      change (Int64.unsigned (Int64.repr 32)) with 32.
      destr; try lia.
      rewrite (H1 i i1); auto. lia.
      rewrite int64_zwordsize; auto.
    + rewrite int_zwordsize, int64_zwordsize in *.
      lia. 
  - solve_long.
    rewrite int64_zwordsize in *.
    change (Z.pow_pos 256 4) with (two_p (Int64.unsigned (Int64.repr 32))).
    rewrite <- Int64.shl_mul_two_p. 
    rewrite Int64.bits_shl.
    change (Int64.unsigned (Int64.repr 32)) with 32.
    destr; try ring.
    rewrite (H1 i i2); auto. lia.
    rewrite int64_zwordsize; auto.
Qed.

(** [proj_symbolic_le] transforms a list of memval [vl] into the corresponding
symbolic expression, reversing the list if we are on big-endian architecture.
*)

Definition proj_symbolic_le (vl: list memval) : expr_sym :=
  proj_symbolic_aux_le (rev_if_be vl).


Definition type_of_list_memval (vl: list memval) : option styp :=
  match vl with
  | (Symbolic e (Some t) n)::r => Some t
  | _ => None
  end.

(** [decode_val] adds a cast around the result of [proj_symbolic_le], and
finalizes the decoding of a list of [memval].  *)

Definition from_bits chunk e vl :=
  match chunk with
  | Mint8signed => Eunop (OpSignext 8) Tint (Val.loword e)
  | Mint8unsigned => Eunop (OpZeroext 8) Tint (Val.loword e)
  | Mint16signed => Eunop (OpSignext 16) Tint (Val.loword e)
  | Mint16unsigned => Eunop (OpZeroext 16) Tint (Val.loword e)
  | Mint32   => (Val.loword e)
  | Mint64   => Eunop (OpSignext 64) Tlong e
  | Mfloat32 => Eunop OpSingleofbits Tint (Val.loword e)
  | Mfloat64 => Eunop OpDoubleofbits Tlong e
  | Many64   =>
    match type_of_list_memval vl with
      Some Tint => Eunop (OpConvert SEUnsigned (Tint, SEUnsigned)) Tlong e
    | Some Tfloat => Eunop OpDoubleofbits Tlong e
    | Some Tsingle => Eunop OpSingleofbits Tint
                           (Eunop (OpConvert SEUnsigned (Tint, SEUnsigned)) Tlong e)
    | Some Tlong => e
    | None => Eval Vundef
    end
  | Many32   =>
    match type_of_list_memval vl with
      Some Tint => Eunop (OpConvert SEUnsigned (Tint, SEUnsigned)) Tlong e
    | Some Tsingle => Eunop OpSingleofbits Tint
                           (Eunop (OpConvert SEUnsigned (Tint, SEUnsigned)) Tlong e)
    | _ => Eval Vundef
    end
  end.
  
Definition decode_val (chunk: memory_chunk) (vl: list memval) : expr_sym :=
  from_bits chunk (proj_symbolic_le vl) vl.

Lemma gnp_wt:
  forall n e,
    weak_wt (get_nth_part e n) Tlong.
Proof.
  induction n; simpl; intros; auto.
  destruct (wt_expr_dec e Tlong); simpl; auto.
  left; repeat split; auto; constructor.
  right.
  intro.
  destruct H as [t [A B]]. congruence.
Qed.
     
Lemma eom_wt:
  forall l,
    weak_wt (expr_of_memval l) Tlong.
Proof.
  des l.
  apply gnp_wt.
Qed.

Lemma psa_wt:
  forall l,
    weak_wt (proj_symbolic_aux_le l) Tlong.
Proof.
  induction l; simpl; intros; auto.
  red; simpl; auto.
  destruct (eom_wt a).
  - destruct IHl.
    + left; repeat split; auto; constructor.
    + right; intro A; destruct A as [t [A [[B D] C]]].
      elim H0; exists Tlong; auto.
  - right; intro A; destruct A as [t [A [[B D] C]]].
    elim H; exists Tlong; auto.
Qed.

Lemma ps_wt:
  forall l,
    weak_wt (proj_symbolic_le l) Tlong.
Proof.
  unfold proj_symbolic_le.
  apply psa_wt.
Qed.

Definition wt e t := (exists t', wt_expr e (styp_of_ast t') /\ subtype t' t = true)
                     \/ ~ exists t, wt_expr e t.


Lemma subtype_refl:
  forall t, subtype t t = true.
Proof.
  intros. des t.
Qed.


Lemma weak_wt_wt':
  forall e t,
    weak_wt e (styp_of_ast t) -> wt e t.
Proof.
  intros e t [A|A].
  left; eexists; split; eauto; try apply subtype_refl.
  red; auto.
Qed.

Lemma gnp_wt':
  forall n e,
    wt (get_nth_part e n) AST.Tlong.
Proof.
  intros.
  apply weak_wt_wt'.
  apply gnp_wt. 
Qed.
     
Lemma eom_wt':
  forall l,
    wt (expr_of_memval l) AST.Tlong.
Proof.
  intros.
  apply weak_wt_wt'.
  apply eom_wt.
Qed.

Lemma psa_wt':
  forall l,
    wt (proj_symbolic_aux_le l) AST.Tlong.
Proof.
  intros.
  apply weak_wt_wt'.
  apply psa_wt.
Qed.

Lemma ps_wt':
  forall l,
    wt (proj_symbolic_le l) AST.Tlong.
Proof.
  intros.
  apply weak_wt_wt'.
  apply ps_wt. 
Qed.

Lemma decode_val_type:
  forall l chunk,
    wt (decode_val chunk l) (type_of_chunk chunk).
Proof.
  intros.
  destruct (ps_wt' l) as [[t [A B]]|A].
  - des t.
    des chunk;
    try (red; left; eexists; split; try apply subtype_refl; simpl; destr; try constructor; fail).
    + destr.
      * red; simpl; left.
        destr.
        exists AST.Tint; destr.
        exists AST.Tint; destr.
        exists AST.Tint; destr.
        exists AST.Tsingle; destr.
      * red; left; eexists; split; eauto; try apply subtype_refl; simpl; auto.
    + destr.
      2: red; left; eexists; split; eauto; try apply subtype_refl; destr.
      red; simpl; left.
      destr.
      exists AST.Tint; destr.
      exists AST.Tlong; destr.
      exists AST.Tfloat; destr.
      exists AST.Tsingle; destr.
  - des chunk; repeat destr;
    try (right; intro;dex; destr; apply A; eexists; eauto; fail);
    left; eexists; split; eauto; try apply subtype_refl; simpl; auto.
Qed.


Definition is_se_or_ld R :=
  R = same_eval \/ R = Val.lessdef.

Record wf_mr (mr: expr_sym -> expr_sym -> Prop) :=
  {
    mr_refl: forall x, mr x x;
    mr_unop: forall u t a b
                    (MR: mr a b),
               mr (Eunop u t a) (Eunop u t b);
    mr_binop: forall bi t t' a b c d
                     (MR1: mr a b)
                     (MR2: mr c d),
                mr (Ebinop bi t t' a c) (Ebinop bi t t' b d);
    mr_val_refl: forall v1 v2
                        (REL: mr (Eval v1) (Eval v2))
                        (NU: v1 <> Vundef),
                   v1 = v2;
    mr_same_eval: forall v1 v2, same_eval v1 v2 -> 
                           mr v1 v2;
    mr_closed_se: forall v1 v2 v3 v4,
        same_eval v1 v2 -> same_eval v3 v4 ->
        mr v1 v3 -> mr v2 v4;
    mr_se_or_ld:
      is_se_or_ld mr
  }.

Lemma add_one_zero_diff:
  forall i i0,
    i = Int.add Int.one i0 ->
    i = Int.add Int.zero i0 ->
    False.
Proof.
  intros; subst.
  apply f_equal with (f:= fun x => Int.sub x i0) in H0.
  revert H0.
  rewrite ! Int.sub_add_opp.
  sint. rewrite ! Int.add_neg_zero.
  rewrite Int.add_zero. discriminate.
Qed.


Lemma wf_mr_se:
  wf_mr same_eval.
Proof.
  constructor; simpl; intros; eauto.
  reflexivity.
  apply unop_same_eval;auto.
  apply binop_same_eval;auto.
  generalize (REL (fun _ => Int.zero) (fun _ _ => Byte.zero)); simpl.
  generalize (REL (fun _ => Int.one) (fun _ _ => Byte.zero)); simpl.
  des v1; des v2;
  repeat match goal with
             H: Vint _ = Vint _ |- _ => apply inj_vint in H
           | H1: ?i = _, H2: ?i = _ |- _ => exfalso; apply (add_one_zero_diff _ _ H1 H2)
           | H: Int.add _ _ = ?i, H1: Int.add _ _ = ?i|- _ => symmetry in H; symmetry in H1
         end.
  rewrite ! Int.add_zero_l in H0. subst.
  destruct (peq b b0); subst; auto.
  generalize (REL (fun bb => if peq bb b then Int.zero else Int.one) (fun _ _ => Byte.zero)); simpl.
  intro A; apply inj_vint in A.
  apply f_equal with (f:= fun x => Int.sub x i0) in A.
  revert A.
  rewrite ! Int.sub_add_opp.
  sint. rewrite ! Int.add_neg_zero.
  rewrite ! Int.add_zero. rewrite pred_dec_true; auto. rewrite pred_dec_false; auto. discriminate.
  congruence.
  red; auto.
Qed.



Lemma wf_mr_ld:
  wf_mr Val.lessdef.
Proof.
  constructor; simpl; intros; eauto.
  apply Val.lessdef_unop; auto.
  apply Val.lessdef_binop; auto.
  generalize (REL (fun _ => Int.zero) (fun _ _ => Byte.zero)); simpl.
  generalize (REL (fun _ => Int.one) (fun _ _ => Byte.zero)); simpl.
  des v1; des v2;
  repeat match goal with
             H: Values.Val.lessdef (Vint _) (Vint _) |- _ => apply lessdef_vint in H
           | H: Values.Val.lessdef _ _ |- _ => solve [inv H; subst; auto]
           | H1: ?i = _, H2: ?i = _ |- _ => exfalso; apply (add_one_zero_diff _ _ H1 H2)
           | H: Int.add _ _ = ?i, H1: Int.add _ _ = ?i|- _ => symmetry in H; symmetry in H1
         end; subst; auto.
  rewrite ! Int.add_zero_l in H0. subst.
  destruct (peq b b0); subst; auto.
  generalize (REL (fun bb => if peq bb b then Int.zero else Int.one) (fun _ _ => Byte.zero)); simpl.
  intro A; apply lessdef_vint in A.
  apply f_equal with (f:= fun x => Int.sub x i0) in A.
  revert A.
  rewrite ! Int.sub_add_opp.
  sint. rewrite ! Int.add_neg_zero.
  rewrite ! Int.add_zero. rewrite pred_dec_true; auto. rewrite pred_dec_false; auto. discriminate.
  red; intros; rewrite H; auto.
  red; intros.
  rewrite <- H, <- H0.
  apply H1.
  red; auto.
Qed.


Section MemvalRel.

  Variable mr: expr_sym -> expr_sym -> Prop.


  Hypothesis WF: wf_mr mr.

  Definition same_type_memval m1 m2 :=
    match m1, m2 with
      Symbolic e t n, Symbolic e' t' n' => t = t'
    end.
  
  Definition memval_rel : memval -> memval -> Prop :=
    fun m1 m2 => mr (expr_of_memval m1) (expr_of_memval m2)
              /\ (same_type_memval m1 m2
                 \/ same_eval (Eval Vundef) (expr_of_memval m1))
  .


  Lemma memval_equiv_expr_of_memval:
    forall a b,
      memval_rel a b ->
      mr (expr_of_memval a) (expr_of_memval b).
  Proof.
    intros. 
    apply H. 
  Qed.
  
  Lemma psa_eSexpr:
    forall v v',
      list_forall2 memval_rel v v' ->
      mr (proj_symbolic_aux_le v)
         (proj_symbolic_aux_le v').
  Proof.
    inv WF. 
    induction 1; simpl; intros; auto.
    destruct H; auto.
  Qed.

  Lemma psa_le_spec:
    forall l l',
      list_forall2 memval_rel l l' ->
      mr (proj_symbolic_aux_le l)
         (proj_symbolic_aux_le l').
  Proof.
    inv WF.
    induction 1; simpl; intros; auto.
    destruct H; auto.
  Qed.


Lemma ps_eSexpr:
  forall v v',
    list_forall2 memval_rel v v' ->
    mr (proj_symbolic_le v) (proj_symbolic_le v').
Proof.
  unfold proj_symbolic_le.
  intros.
  eapply psa_eSexpr; eauto.
Qed.


Lemma memval_rel_type_of_ml:
  forall v v',
    list_forall2 memval_rel v v' ->
    type_of_list_memval v = type_of_list_memval v'
    \/
    (exists h, Some h = head v /\
          same_eval (Eval Vundef) (expr_of_memval h)
    ).
Proof.
  induction 1.
  - destr.
  - destr; dex; destr.
    + des H.
      repeat destr.  right; exists (Symbolic e o n); destr.
    + subst. inv H. des H4.
      repeat destr. right; exists (Symbolic e o n); destr. 
Qed.

Lemma in_same_undef_psa_undef:
  forall vl m,
    In m vl ->
    same_eval (Eval Vundef) (expr_of_memval m) ->
    same_eval (Eval Vundef) (proj_symbolic_aux_le vl).
Proof.
  induction vl; simpl; intros. easy.
  red; intros; destr. subst. rewrite <- H0. destr.
  rewrite <- (IHvl _ H1 H0). destr. seval.
Qed.

Lemma hd_error_in:
  forall A l (x:A),
    hd_error l = Some x -> In x l.
Proof.
  induction l; simpl; intros; inv H; auto.
Qed.

 

Lemma lessdef_vundef:
  forall v,
    Val.lessdef (Eval Vundef) v.
Proof.
  red; intros; auto.
Qed.

Lemma decode_val_spec:
  forall l l',
    list_forall2 memval_rel l l' ->
    forall c,
      mr (decode_val c l) (decode_val c l').
Proof.
  inv WF; simpl; intros.
  generalize (ps_eSexpr _ _ H). intro EVAL.
  des c; eauto.
  - destruct (memval_rel_type_of_ml _ _ H) as [A | [h [A B]]].
    +
      rewrite A; repeat destr; eauto.
    +
      generalize (in_same_undef_psa_undef _ _ (hd_error_in _ _ _ (eq_sym A))
                                          B); intro C.
      generalize (mr_closed_se0 _ _ _ _ (same_eval_sym _ _ C) (same_eval_refl _) EVAL).
      clear H A B.
      repeat destr; eauto;
      apply (fun pf => mr_closed_se0 (Eval Vundef) _ _ _ pf (same_eval_refl _)); eauto;
      try red; simpl;intros;  try rewrite <- C; destr;
      (destruct mr_se_or_ld0; subst; [|try apply lessdef_vundef]);
      try (red; intros; simpl; try rewrite <- H; seval);
      unfold convert_t in *; destr.
- destruct (memval_rel_type_of_ml _ _ H) as [A | [h [A B]]].
    +
      rewrite A; repeat destr; eauto.
    +
      generalize (in_same_undef_psa_undef _ _ (hd_error_in _ _ _ (eq_sym A))
                                          B); intro C.
      generalize (mr_closed_se0 _ _ _ _ (same_eval_sym _ _ C) (same_eval_refl _) EVAL).
      clear H A B.
      repeat destr; eauto;
      apply (fun pf => mr_closed_se0 (Eval Vundef) _ _ _ pf (same_eval_refl _)); eauto;
      try red; simpl;intros;  try rewrite <- C; destr;
      (destruct mr_se_or_ld0; subst; [|try apply lessdef_vundef]);
      try (red; intros; simpl; try rewrite <- H; seval);
      unfold convert_t in *; destr.      
Qed.

Lemma decode_val_eSexpr:
  forall chunk v v',
    list_forall2 memval_rel v v' ->
    mr (decode_val chunk v) (decode_val chunk v').
Proof.
  intros.
  apply decode_val_spec.
  apply list_forall2_rib; auto.
Qed.

End MemvalRel.

Definition decode_encode_expr_sym (v1: expr_sym) (chunk1 chunk2: memory_chunk) (v2: expr_sym) :Prop :=
  match chunk1, chunk2 with
    | (Mint8signed|Mint8unsigned), Mint8signed => same_eval v2 (Eunop (OpSignext 8) Tint v1)
    | (Mint8signed|Mint8unsigned), Mint8unsigned => same_eval v2 (Eunop (OpZeroext 8) Tint v1)
    | (Mint16signed|Mint16unsigned), Mint16signed => same_eval v2 (Eunop (OpSignext 16) Tint v1)
    | (Mint16signed|Mint16unsigned), Mint16unsigned => same_eval v2 (Eunop (OpZeroext 16) Tint v1)
    | Mint32, Mint32 => same_eval v2 (Eunop (OpSignext 32) Tint v1)
    | Mint32, Mfloat32 => same_eval v2  (Eunop OpSingleofbits Tint v1)
    | Mfloat32, Mint32 => same_eval v2  (Eunop OpBitsofsingle Tsingle v1)
    | Mfloat32, Mfloat32 => same_eval v2  (Eunop (OpConvert SESigned (Tsingle, SESigned)) Tsingle v1)
    | Mint64, Mint64 => same_eval v2  (Eunop (OpSignext 64) Tlong v1)
    | Mint64, Mfloat64 => same_eval v2  (Eunop OpDoubleofbits Tlong v1)
    | Mfloat64, Mint64 => same_eval v2  (Eunop OpBitsofdouble Tfloat v1)
    | Mfloat64, Mfloat64 => same_eval v2  (Eunop (OpConvert SESigned (Tfloat, SESigned)) Tfloat v1)
    | Many32, Many32 => match get_type v1 with
                         Tint =>  same_eval v2 v1
                       | Tsingle => same_eval v2 v1
                       | _ => same_eval v2 (Eval Vundef)
                       end
    | Many32, Mint32 => match get_type v1 with
                       | Tint => same_eval v2 (Eunop (OpSignext 32) Tint v1)
                       | _ => True
                       end
    | Many64, Many64 => same_eval v2 v1
    | _, _ => True
  end.

Ltac simpl_int :=
  match goal with
    | |- context [Int.eq ?a ?a] => rewrite Int.eq_true; simpl; simpl_int
    | |- context [Int.eq ?a ?b] => replace (Int.eq a b) with false by reflexivity; simpl; simpl_int
    | |- context [Int.ltu ?a ?b] => try replace (Int.ltu a b) with true by reflexivity; simpl; simpl_int
    | _ => progress simpl; simpl_int
    | _ => idtac
  end.

Ltac rew_shru_64:=
  repeat match goal with
             |- context[Int64.shru 
                          (Int64.shru ?a ?i) (Int64.repr ?i')] =>
             rewrite Int64.shru_shru; auto
         end. 

Lemma decode_encode_val_general:
  forall v chunk1 chunk2,
    decode_encode_expr_sym v chunk1 chunk2 (decode_val chunk2 (encode_val chunk1 v)).
Proof.
  intros.
  unfold encode_val.
  unfold decode_val.
  unfold inj_symbolic. unfold proj_symbolic_le.
  rewrite revi_rev_revi. 
  destruct chunk1 eqn:?; destruct chunk2 eqn:?; simpl; auto;
  try (red; simpl; intros; seval; simpl_int; unfold convert_t; progress f_equal).
  + rewrite <- (sign_ext_8_id i).  solve_int. rewrite Int64.bits_loword; auto. rewrite Int64.add_zero.
    rewrite Int64.bits_and; auto. rewrite bits64_255_below; auto. rewrite bits_255_below; auto.
    rewrite Int64.testbit_repr.
    rewrite <- (Int.repr_unsigned i) at 2.
    rewrite Int.testbit_repr; auto.
    unfsize; lia.    unfsize; lia.
  + rewrite <- (zero_ext_8_id i).  solve_int. rewrite Int64.bits_loword; auto. rewrite Int64.add_zero.
    rewrite Int64.bits_and; auto. rewrite bits64_255_below; auto. rewrite bits_255_below; auto.
    rewrite Int64.testbit_repr.
    rewrite <- (Int.repr_unsigned i) at 2.
    rewrite Int.testbit_repr; auto.
    unfsize; lia.    unfsize; lia.
  + rewrite <- (sign_ext_8_id i).  solve_int. rewrite Int64.bits_loword; auto. rewrite Int64.add_zero.
    rewrite Int64.bits_and; auto. rewrite bits64_255_below; auto. rewrite bits_255_below; auto.
    rewrite Int64.testbit_repr.
    rewrite <- (Int.repr_unsigned i) at 2.
    rewrite Int.testbit_repr; auto.
    unfsize; lia.    unfsize; lia.
  + rewrite <- (zero_ext_8_id i).  solve_int. rewrite Int64.bits_loword; auto. rewrite Int64.add_zero.
    rewrite Int64.bits_and; auto. rewrite bits64_255_below; auto. rewrite bits_255_below; auto.
    rewrite Int64.testbit_repr.
    rewrite <- (Int.repr_unsigned i) at 2.
    rewrite Int.testbit_repr; auto.
    unfsize; lia.    unfsize; lia.
  + rewrite  (sign_ext_16_id_long i). auto. 
  + rewrite  (zero_ext_16_id_long i). auto. 
  + rewrite  (sign_ext_16_id_long i). auto. 
  + rewrite  (zero_ext_16_id_long i). auto. 
  + rewrite int32_decomp; auto.
  + rewrite int32_decomp; auto.
    rewrite Int.sign_ext_above; sl. 
  + repeat rewrite shl'_shl by (vm_compute; intuition congruence).
    repeat rewrite shru'_shru by (vm_compute; intuition congruence).
    progress rew_shru_64. sl.
    rewrite int64_decomp. auto.
  + repeat rewrite shl'_shl by (vm_compute; intuition congruence).
    repeat rewrite shru'_shru by (vm_compute; intuition congruence).
    progress rew_shru_64. sl.
    rewrite int64_decomp. auto.
  + rewrite int32_decomp.
    rewrite Int.sign_ext_above; sl.
  + rewrite int32_decomp.
    rewrite Int.sign_ext_above; sl.
    apply Float32.of_to_bits.
  + repeat rewrite shl'_shl by (vm_compute; intuition congruence).
    repeat rewrite shru'_shru by (vm_compute; intuition congruence).
    progress rew_shru_64.
    rewrite int64_decomp. apply Int64.sign_ext_above; auto.
    sl.
  + repeat rewrite shl'_shl by (vm_compute; intuition congruence).
    repeat rewrite shru'_shru by (vm_compute; intuition congruence).
    progress rew_shru_64.
    rewrite int64_decomp. apply Float.of_to_bits; auto.
  + repeat destr. 
    * red; simpl; intros; seval. simpl_int.
      rewrite int32_decomp. auto.

  +  replace (type_of_list_memval (rev (rev_if_be _))) with (Some (get_type v))
      by (repeat destr). 
    destruct (get_type_correct v) as [A|A].
    * repeat destr; try solve [constructor]; try red; simpl; intros;
    try now (exploit (get_type_correct_not_int v); eauto; try congruence; easy).
    simpl_int. unfold convert_t; simpl.
    generalize (expr_type _ _ A cm em). seval; simpl_int.
    rewrite int32_decomp.
    rewrite Int.sign_ext_above by (vm_compute; destr); auto.
    generalize (expr_type _ _ A cm em). seval; simpl_int.
    rewrite int32_decomp.
    rewrite Int.sign_ext_above by (vm_compute; destr); auto.
    rewrite Float32.of_to_bits; auto.
    * repeat destr; red; intros; simpl;
      rewrite (nwt_expr_undef cm em _  A); simpl; auto.

  +  replace (type_of_list_memval (rev (rev_if_be _))) with (Some (get_type v))
      by (repeat destr). 
    destruct (get_type_correct v) as [A|A].
     * red; intros; simpl.
       destr; simpl_int.
      generalize (expr_type _ _ A cm em);
        seval; simpl_int.
      repeat rewrite shl'_shl by (vm_compute; intuition congruence).
      repeat rewrite shru'_shru by (vm_compute; intuition congruence).
      progress rew_shru_64.
      rewrite int64_decomp.
      unfold convert_t. simpl. unfold Int64.loword.
      rewrite Int64.unsigned_repr.
      rewrite Int.repr_unsigned. auto.
      generalize (Int.unsigned_range i).
      unf_modulus. unfold Int64.max_unsigned, Int64.modulus; simpl. lia.

      generalize (expr_type _ _ A cm em);
      seval; simpl_int.
      repeat rewrite shl'_shl by (vm_compute; intuition congruence).
      repeat rewrite shru'_shru by (vm_compute; intuition congruence).
      progress rew_shru_64.
      rewrite int64_decomp. auto.

      generalize (expr_type _ _ A cm em);
      seval; simpl_int.
      repeat rewrite shl'_shl by (vm_compute; intuition congruence).
      repeat rewrite shru'_shru by (vm_compute; intuition congruence).
      progress rew_shru_64.
      rewrite int64_decomp.
      unfold Int64.loword.
      rewrite Float.of_to_bits; auto.

      
      generalize (expr_type _ _ A cm em);
      seval; simpl_int.
      repeat rewrite shl'_shl by (vm_compute; intuition congruence).
      repeat rewrite shru'_shru by (vm_compute; intuition congruence).
      progress rew_shru_64.
      rewrite int64_decomp.
      unfold Int64.loword.
      rewrite Int64.unsigned_repr.
      rewrite Int.repr_unsigned.
      rewrite Float32.of_to_bits; auto.
      generalize (Int.unsigned_range (Float32.to_bits f)).
      unf_modulus. unfold Int64.max_unsigned, Int64.modulus; simpl. lia.

    * red; intros; generalize (nwt_expr_undef cm em v A).
      unfold get_type.
      intro B; repeat destr; try rewrite B in *; try rewrite ! convert_undef in *; auto.
      destr. destr. destr. destr.
Qed.

Lemma encode_val_int8_signed_unsigned:
  forall v, encode_val Mint8signed v = encode_val Mint8unsigned v.
Proof.
  intros. 
  destruct v; simpl; auto.
Qed.

Lemma encode_val_int16_signed_unsigned:
  forall v, encode_val Mint16signed v = encode_val Mint16unsigned v.
Proof.
  intros. destruct v; simpl; auto.
Qed.

Definition memval_equiv := memval_rel same_eval.

Lemma encode_val_int8_zero_ext:
  forall mr (wf: wf_mr mr) n,
    list_forall2
      (memval_rel mr)
      (encode_val Mint8unsigned (Eval (Vint (Int.zero_ext 8 n))))
      (encode_val Mint8unsigned (Eval (Vint n))).
Proof.
  intros; unfold encode_val. simpl. unfold inj_symbolic.
  repeat destr.
  apply list_forall2_rev.
  apply list_forall2_rib.
  simpl.
  repeat constructor.
  repeat red; intros; simpl; seval.
  inv wf. apply mr_same_eval0; auto.
  red; intros; simpl.
  change 255 with (two_p 8 - 1).
  rewrite <- ! Int64.zero_ext_and by lia.
  f_equal. sl.
  repeat rewrite Int64.testbit_repr; auto.
  rewrite <- ! Int.testbit_repr; unfsize; try lia.
  rewrite ! Int.repr_unsigned.
  rewrite Int.bits_zero_ext; auto.
  destr.
Qed.


Lemma encode_val_int8_sign_ext:
  forall mr (wf: wf_mr mr) n,
    list_forall2
      (memval_rel mr)
      (encode_val Mint8unsigned (Eval (Vint (Int.sign_ext 8 n))))
      (encode_val Mint8unsigned (Eval (Vint n))).
Proof.
   intros; unfold encode_val. simpl. unfold inj_symbolic.
  repeat destr.
  apply list_forall2_rev.
  apply list_forall2_rib.
  simpl.
  repeat constructor.
  repeat red; intros; simpl; seval.
  inv wf. apply mr_same_eval0; auto.
  red; intros; simpl.
  change 255 with (two_p 8 - 1).
  rewrite <- ! Int64.zero_ext_and by lia.
  f_equal. sl.
  repeat rewrite Int64.testbit_repr; auto.
  rewrite <- ! Int.testbit_repr; unfsize; try lia.
  rewrite ! Int.repr_unsigned.
  rewrite Int.bits_sign_ext; unfsize; try lia. destr. 
Qed.

Lemma encode_val_int16_zero_ext:
  forall mr (wf: wf_mr mr) n,
    list_forall2
      (memval_rel mr)
      (encode_val Mint16unsigned (Eval (Vint (Int.zero_ext 16 n))))
      (encode_val Mint16unsigned (Eval (Vint n))).
Proof.
   intros; unfold encode_val. simpl. unfold inj_symbolic.
  repeat destr.
  apply list_forall2_rev.
  apply list_forall2_rib.
  simpl.
  repeat constructor.
  -  inv wf. apply mr_same_eval0; auto.
     repeat red; intros; simpl; seval. sl.
     change 255 with (two_p 8 - 1). 
     rewrite <- ! Int64.zero_ext_and by lia.
     f_equal. rewrite ! shru'_shru; sl.
     rewrite ! Int64.testbit_repr; unfsize; try lia.
     rewrite <- ! Int.testbit_repr; unfsize; try lia.
     rewrite ! Int.repr_unsigned.
     rewrite Int.bits_zero_ext; try lia. 
     destr; lia.
  -  inv wf. apply mr_same_eval0; auto.
     repeat red; intros; simpl; seval. 
     change 255 with (two_p 8 - 1). 
     rewrite <- ! Int64.zero_ext_and by lia.
     f_equal. sl.
     rewrite ! Int64.testbit_repr; unfsize; try lia.
     rewrite <- ! Int.testbit_repr; unfsize; try lia.
     rewrite ! Int.repr_unsigned.
     rewrite Int.bits_zero_ext; try lia. 
     destr; lia.
Qed.


Lemma encode_val_int16_sign_ext:
  forall mr (wf: wf_mr mr) n,
    list_forall2
      (memval_rel mr)
      (encode_val Mint16unsigned (Eval (Vint (Int.sign_ext 16 n))))
      (encode_val Mint16unsigned (Eval (Vint n))).
Proof.
  intros; unfold encode_val. simpl. unfold inj_symbolic.
  repeat destr.
  apply list_forall2_rev.
  apply list_forall2_rib.
  simpl.
  repeat constructor.
  -  inv wf. apply mr_same_eval0; auto.
     repeat red; intros; simpl; seval. sl.
     change 255 with (two_p 8 - 1). 
     rewrite <- ! Int64.zero_ext_and by lia.
     f_equal. rewrite ! shru'_shru; sl.
     rewrite ! Int64.testbit_repr; unfsize; try lia.
     rewrite <- ! Int.testbit_repr; unfsize; try lia.
     rewrite ! Int.repr_unsigned.
     rewrite Int.bits_sign_ext; unfsize; try lia. 
     destr; lia. 
  - inv wf. apply mr_same_eval0; auto.
    repeat red; intros; simpl; seval. 
    change 255 with (two_p 8 - 1). 
    rewrite <- ! Int64.zero_ext_and by lia.
    f_equal. sl.
    rewrite ! Int64.testbit_repr; unfsize; try lia.
    rewrite <- ! Int.testbit_repr; unfsize; try lia.
    rewrite ! Int.repr_unsigned.
    rewrite Int.bits_sign_ext; unfsize; try lia. 
    destr; lia.
Qed.

Definition memval_lessdef : memval -> memval -> Prop :=
  memval_rel Val.lessdef.

Lemma decode_val_cast:
  forall chunk l,
    length l = size_chunk_nat chunk ->
    let v:= decode_val chunk l in
    match chunk with
      | Mint8signed => same_eval v (Val.sign_ext 8 v)
      | Mint8unsigned => same_eval v (Val.zero_ext 8 v)
      | Mint16signed => same_eval v (Val.sign_ext 16 v)
      | Mint16unsigned => same_eval v (Val.zero_ext 16 v)
      | _ => True
    end.
Proof.
  intros chunk l.
  rewrite <- (rev_if_be_involutive) with (l:=l).
  generalize (rev_if_be l). clear l. intros l H.
  unfold decode_val.
  des chunk; red; simpl; intros; 
    unfold proj_symbolic_le; rewrite rev_if_be_involutive; simpl; seval.
  rewrite Int.sign_ext_widen; auto; lia.
  rewrite Int.zero_ext_widen; auto; lia.
  rewrite Int.sign_ext_widen; auto; lia.
  rewrite Int.zero_ext_widen; auto; lia.
Qed.

(** * Compatibility with memory injections *)

(** Relating two memory values according to a memory injection. *)

Lemma decode_val_info:
  forall c n,
    let v2 := proj_symbolic_aux_le (rev_if_be n) in
    same_eval
      (decode_val c n)
      match c with
        | Mint32 => Val.loword v2
        | Mint64 => Eunop (OpSignext 64) Tlong v2
        | _ => decode_val c n
      end.
Proof.
  unfold decode_val.
  des c; try reflexivity.
Qed.



(** * Breaking 64-bit memory accesses into two 32-bit accesses *)
    
Lemma decode_val_int64:
  forall l1 l2,
    length l1 = 4%nat -> 
    length l2 = 4%nat ->
    same_eval (decode_val Mint64 (l1 ++ l2))
              (Val.longofwords 
                 (decode_val Mint32 (if big_endian then l1 else l2))
                 (decode_val Mint32 (if big_endian then l2 else l1))).
Proof.
  intros.  red; intros.
  rewrite (decode_val_info Mint64).
  unfold Val.longofwords.
  Local Opaque decode_val. simpl.
  repeat rewrite (decode_val_info Mint32). 
  replace (rev_if_be (l1 ++ l2))
  with ((if big_endian then rev l2 else l1)
          ++ (if big_endian then rev l1 else l2)) by
      (unfold rev_if_be; destr; rewrite rev_app_distr; auto).
  replace (rev_if_be (if big_endian then l1 else l2))
  with (if big_endian then rev l1 else l2) by (unfold rev_if_be; destr).
  replace (rev_if_be (if big_endian then l2 else l1)) 
  with (if big_endian then rev l2 else l1) by (unfold rev_if_be; destr).
  rewrite psa_le_app.
  generalize (if big_endian then rev l2 else l1).
  generalize (if big_endian then rev l1 else l2).
  intros; simpl.
  seval.
  rewrite Int64.sign_ext_above with (n:=64) by (vm_compute; congruence).
  auto.
  destr. rewrite rev_length; auto.
  destr. rewrite rev_length; auto.
Qed.

Lemma gnpv_hi:
  forall n i,
    get_nth_part_val (Vlong (Int64.repr (Int.unsigned (Int64.hiword i)))) n =
    get_nth_part_val (Vlong i) (n + 4).
Proof.
  induction n; simpl; intros.
  - f_equal. sl.
    + rewrite Int64.testbit_repr; auto.
      rewrite <- Int.testbit_repr; unfsize; try lia.
      rewrite Int.repr_unsigned.
      rewrite Int64.bits_hiword; unfsize; try lia.
      f_equal. f_equal. lia.
    + rewrite bits64_255_above; unfsize; try lia. ring.
    + rewrite bits64_255_above; unfsize; try lia. ring.
    + rewrite bits64_255_above; unfsize; try lia. ring.
    + rewrite bits64_255_above; unfsize; try lia. ring.
  - rewrite <- IHn. f_equal. f_equal.
    sl.
    + rewrite ! Int64.testbit_repr; unfsize; try lia.
      destruct (zlt (i0+8) 32).
      * rewrite <- Int.testbit_repr; (unfsize; try lia).
        rewrite Int.repr_unsigned.
        rewrite Int64.bits_hiword; unfsize; try lia.
        rewrite <- Int.testbit_repr; (unfsize; try lia).
        rewrite Int.repr_unsigned.
        rewrite Int64.bits_hiword; unfsize; try lia.
        rewrite Int64.bits_shru; unfsize; try lia.
        sl.
      * rewrite Int.Ztestbit_above with (n:=32%nat)
          by (unfsize; lia || apply Int.unsigned_range).
        destruct (zlt i0 32).
        rewrite <- Int.testbit_repr; unfsize; try lia.
        rewrite Int.repr_unsigned.
        rewrite Int64.bits_hiword; unfsize; try lia.
        rewrite Int64.bits_shru; unfsize; try lia. sl.
        rewrite Int.Ztestbit_above with (n:=32%nat)
          by (unfsize; lia || apply Int.unsigned_range).
        auto.
    + rewrite ! Int64.testbit_repr; unfsize; try lia.
      destruct (zlt (i0+8) 32).
      * rewrite <- Int.testbit_repr; (unfsize; try lia).
      * rewrite Int.Ztestbit_above with (n:=32%nat)
          by (unfsize; lia || apply Int.unsigned_range).
        auto.
Qed.        

Lemma gnpv_lo:
  forall n i,
    (n <= 3)%nat ->
    get_nth_part_val (Vlong (Int64.repr (Int.unsigned (Int64.loword i)))) n =
    get_nth_part_val (Vlong i) n.
Proof.
  repeat ((des n || des n0); try lia).
  - f_equal. sl.
    rewrite Int64.testbit_repr; auto.
    destruct (zlt i0 32).
    + rewrite <- Int.testbit_repr; unfsize; try lia.
      rewrite Int.repr_unsigned.
      rewrite Int64.bits_loword; unfsize; try lia.
      reflexivity.
    + rewrite bits64_255_above; unfsize; try lia. ring.
  - f_equal. sl.
    rewrite Int64.testbit_repr; unfsize; try lia. 
    destruct (zlt (i0+8) 32).
    + rewrite <- Int.testbit_repr; unfsize; try lia.
      rewrite Int.repr_unsigned.
      rewrite Int64.bits_loword; unfsize; try lia.
      reflexivity.
    + rewrite bits64_255_above; unfsize; try lia. ring.
  - f_equal. sl.
    rewrite Int64.testbit_repr; unfsize; try lia. 
    destruct (zlt (i0+8+8) 32).
    + rewrite <- Int.testbit_repr; unfsize; try lia.
      rewrite Int.repr_unsigned.
      rewrite Int64.bits_loword; unfsize; try lia.
      reflexivity.
    + rewrite bits64_255_above; unfsize; try lia. ring.
  - f_equal. sl.
    rewrite Int64.testbit_repr; unfsize; try lia. 
    destruct (zlt (i0+8+8+8) 32).
    + rewrite <- Int.testbit_repr; unfsize; try lia.
      rewrite Int.repr_unsigned.
      rewrite Int64.bits_loword; unfsize; try lia.
      reflexivity.
    + rewrite bits64_255_above; unfsize; try lia. ring.
Qed.

Lemma memval_equiv_hiword:
  forall n v t,
    memval_equiv
      (Symbolic
         (Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint (Val.hiword v))
         t n) (Symbolic v t (plus n 4)).
Proof.
  intros.
  repeat red.
  simpl. split; auto. red; simpl; intros.
  rewrite ! gnp_rew.
  simpl. seval; try (des n; fail).
  unfold convert_t.
  unfold Values.Val.longofintu.
  apply gnpv_hi.
Qed.

Lemma memval_equiv_loword:
  forall n (n_bounds: (n <= 3)%nat) v,
   memval_equiv
     (Symbolic
        (Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint (Val.loword v))
        None n) (Symbolic v None n).
Proof.
  intros.
  repeat red; intros.
  split; simpl; auto.
  red; simpl; intros.
  rewrite ! gnp_rew. simpl. unfold convert_t.
  unfold Values.Val.longofintu.
  seval ; try (des n; fail).
  apply gnpv_lo. auto.
Qed.

Lemma rib_app:
  forall A B (l1 l2:  A) (f : A -> list B),
    rev_if_be (f (if big_endian then l1 else l2))
              ++ rev_if_be (f (if big_endian then l2 else l1)) =
    rev_if_be ((f l2) ++ (f l1)).
Proof.
  unfold rev_if_be; destr.
  rewrite rev_app_distr; auto.
Qed.



Definition same_type a1 a2 : Prop :=
  forall t, wt_expr a2 t -> wt_expr a1 t.

(* Record same_teval (a1 a2: expr_sym) : Prop := *)
(*   { rel_eval: same_eval a1 a2; *)
(*     rel_type: same_type a1 a2 }. *)

(* Lemma wf_ste: *)
(*   wf_mr same_teval. *)
(* Proof. *)
(*   constructor; simpl; intros; try constructor; try solve [red; auto]. *)
(*   apply unop_same_eval. inv MR. eauto. *)
(*   red; simpl; intros; intuition. *)
(*   apply binop_same_eval; inv MR1; inv MR2; eauto. *)
(*   red; simpl; intros; intuition. *)
(*   inv REL. destruct (wf_mr_se); auto. *)
(* Qed. *)


Lemma encode_val_int64:
  forall v,
    same_eval (decode_val Mint64 (encode_val Mint64 v))
              (decode_val
                 Mint64
                 ((encode_val
                     Mint32
                     (if big_endian then Val.hiword v else Val.loword v))
                    ++
                    (encode_val
                       Mint32
                       (if big_endian then Val.loword v else Val.hiword v)))).
Proof.
  intros.
  unfold encode_val; simpl.
  (* eapply (decode_val_spec) with (mr:=same_eval) (c:=Mint64). *)
  (* exact wf_mr_se. *)
  (* apply list_forall2_rib. *)
  unfold inj_symbolic.
  rewrite <- rev_app_distr.
  (* apply list_forall2_rev. *)
  (* destruct (wt_expr_dec v Tlong). *)
  (* -  *)
  (*   assert (get_type v = Tlong \/ forall alloc em, eSexpr alloc em v = Vundef). *)
  (*   { *)
  (*     unfold get_type; repeat destr; right; *)
  (*     erewrite (wt_expr_2_is_undef v _ _ w0 w) by congruence; reflexivity. *)
  (*   } *)
  (*   destruct H. *)
  (*   +  *)
  Transparent decode_val. unfold decode_val.
  unfold proj_symbolic_le.
  rewrite ! revi_rev_revi.
  set (f:= (fun x =>
              inj_symbolic'
                (size_chunk_nat Mint32)
                (Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint x)
                None)).
  apply unop_same_eval.
  change (same_eval (proj_symbolic_aux_le (rev (inj_symbolic' 8 v None)))
                    (proj_symbolic_aux_le (rev_if_be (rev
                                                        (rev_if_be (f (if big_endian then Val.loword v else Val.hiword v)) ++
                                                                   rev_if_be (f (if big_endian then Val.hiword v else Val.loword v))))))).
  rewrite rib_app.
  rewrite revi_rev_revi.

  simpl.
  red; intros.
  destruct (wt_expr_dec v Tlong).
  generalize (expr_type _ _ w cm em); seval. 
  simpl_int.
  inv Heqv0.
  sl.
  repeat rewrite shl'_shl by (vm_compute; intuition congruence).
  repeat rewrite shru'_shru by (vm_compute; intuition congruence).
  progress rew_shru_64.
  rewrite ! int64_decomp.
  repeat sl.

  {
    f_equal; sl.
    rewrite <- (Int64.ofwords_recompose i) at 1.
    rewrite Int64.bits_ofwords.
    replace Int.zwordsize with 32 by (vm_compute; destr).
    destr.
    repeat (rewrite add_and_shl_rew; destr); try lia.
    rewrite Int64.testbit_repr; auto.
    rewrite Int64.bits_shru; auto. sl.
    rewrite Int64.testbit_repr; auto.
    sl.
    rewrite Int64.bits_shru; sl.
    replace (i0 - 8 - 8 + 16) with i0 by lia.
    rewrite Int64.testbit_repr; sl.
    rewrite Int64.bits_shru; sl.
    replace (i0 - 8 - 8 -8 + 24) with i0 by lia.
    rewrite Int64.testbit_repr; sl.
    sl. sl. sl.
    repeat (rewrite add_and_shl_rew; destr); try lia.
    replace (i0 - 8 - 8 - 8 - 8) with (i0 - 32) by lia.
    rewrite Int64.testbit_repr; auto. sl.
    rewrite Int64.bits_shru; sl.
    replace (i0 - 8 - 8 - 8 - 8) with (i0 - 32) by lia.
    rewrite Int64.testbit_repr; sl.
    rewrite Int64.bits_shru; sl.
    replace (i0 - 8 - 8 - 8 - 8 - 8 -8 + 16) with (i0 - 32) by lia.
    rewrite Int64.testbit_repr; sl.
    rewrite Int64.add_zero.
    rewrite Int64.bits_and.
    rewrite bits64_255_below by sl.
    rewrite andb_true_r.
    rewrite Int64.bits_shru; sl.
    replace (i0 - 8 - 8 - 8 - 8 -8 - 8 - 8 + 24) with (i0 - 32) by lia.
    rewrite Int64.testbit_repr; sl.
    sl. sl.
    sl. sl.
    sl. sl.
    sl. sl. 
  }
  
  rewrite ! nwt_expr_undef; auto.
  intro E; dex; destr.
  intro E; dex; destr.
Qed.

Lemma expr_inject_unop:
  forall f e e' u t,
    Val.expr_inject f e e' ->
    Val.expr_inject f (Eunop u t e) (Eunop u t e').
Proof.
  intros; apply Val.expr_inject_unop; auto.
Qed.

Lemma expr_inject_binop:
  forall f e e' e1 e1' b t1 t2,
    Val.expr_inject f e e' ->
    Val.expr_inject f e1 e1' ->
    Val.expr_inject f (Ebinop b t1 t2 e e1) (Ebinop b t1 t2 e' e1').
Proof.
  intros.
  apply Val.expr_inject_binop; auto.
Qed.

Definition impl_vi (ei: meminj -> expr_sym -> expr_sym -> Prop) :=
  forall f v1 v2,
    ei f (Eval v1) (Eval v2) ->
    val_inject f v1 v2.

Lemma impl_vi_ei:
  impl_vi Val.expr_inject.
Proof.
  red; intros.
  inv H.
  des v1; auto; inv inj_ok; auto.
  simp H0. des p; inv H1. econstructor; eauto.
Qed.

Fixpoint block_appears (e: expr_sym) (b: block) : Prop :=
  match e with
      Eval (Vptr bb i) => b = bb
    | Eval _ => False
    | Eundef _ _ => False
    | Eunop _ _ e => block_appears e b
    | Ebinop _ _ _ e1 e2 => block_appears e1 b \/ block_appears e2 b
  end.

Lemma nba_se:
  forall a b,
    ~ block_appears a b ->
    forall cm cm' em,
      (forall bb, bb <> b -> cm bb = cm' bb) ->
      eSexpr cm em a = eSexpr cm' em a.
Proof.
  induction a; simpl; intros; eauto.
  - des v.
    rewrite H0; auto.
  - erewrite IHa; eauto.
  - erewrite IHa1; eauto.
    erewrite IHa2; eauto.
Qed.

Lemma block_appears_dec: forall b a, {block_appears a b} + {~ block_appears a b}.
Proof.
  induction a; simpl; intros; eauto.
  - des v. des (peq b b0); auto.
  - destruct IHa1; destruct IHa2; auto.
    right; auto. intros [A | A ]; congruence.
Qed.

Lemma ptr_se_block_appears:
  forall a b i
         (SE: same_eval (Eval (Vptr b i)) a),
    block_appears a b.
Proof.
  intros.
  destruct (block_appears_dec b a); auto.
  generalize (nba_se _ _ n (fun bb => Int.zero)
                     (fun bb => if peq b bb then Int.one else Int.zero)
                     Normalise.dummy_em).
  intro A. trim A.
  intros. rewrite pred_dec_false; auto.
  rewrite <- ! SE in A.
  simpl in A.

  rewrite pred_dec_true in A; auto.
  apply inj_vint in A.
  exploit add_one_zero_diff; eauto.
  intuition.
Qed.
    
Lemma apply_inj_none:
  forall f a b,
    block_appears a b ->
    f b = None ->
    Val.apply_inj f a = None.
Proof.
  induction a; simpl; intros; eauto.
  - des v. unfold Val.inj_ptr; rewrite H0; auto.
  - intuition.
  - erewrite IHa; eauto.
  - destruct H; [erewrite IHa1|erewrite IHa2]; eauto.
    des (Val.apply_inj f a1).
Qed.


Lemma impl_vi_ei':
  impl_vi expr_inject'.
Proof.
  red; intros. inv H.
  inv ei_ei.
  
  generalize (fun al em => Val.apply_inj_eSexpr f al em _ _ inj_ok). intro EVAL.


  red in ei_ld_1, ei_ld_2.

  assert (forall cm em,
            Values.Val.lessdef (eSexpr (Val.inj_alloc cm f) (Val.inj_em em f) (Eval v1))
                               (eSexpr cm em (Eval v2))).
  {
    intros.
    eapply Values.Val.lessdef_trans; eauto.
    rewrite EVAL. auto.
  } 


  generalize (H (fun _ => Int.zero) (fun _ _ => Byte.zero)). simpl.
  generalize (H (fun _ => Int.one) (fun _ _ => Byte.zero)). simpl.

  intros D E.
  des v1; des v2; auto; try solve [inv D; inv E; auto].

  - apply lessdef_vint in D.
    apply lessdef_vint in E.
    exploit add_one_zero_diff; eauto. intuition.
  -
    unfold Val.inj_alloc in *.
    des (f b). des p.
    + apply lessdef_vint in D.
      apply lessdef_vint in E.
      subst.
      revert E; sint. generalize (Int.add (Int.repr z) i). intros.
      apply f_equal with (f:= fun x => Int.sub x i0) in E.
      rewrite ! Int.sub_add_opp in E.
      revert E; sint. rewrite ! Int.add_neg_zero.
      rewrite Int.add_zero. discriminate.
    + erewrite apply_inj_none in inj_ok; eauto.
      congruence.
      eapply ptr_se_block_appears.
      red; intros.
      specialize (ei_ld_1 cm em).
      inv ei_ld_1. simpl; eauto.
  - unfold Val.inj_alloc in *.
    generalize (H (fun bb => if peq bb b then Int.zero else
                               if peq bb b0 then Int.repr 2 else
                               Int.one) Normalise.dummy_em).
    intro X; apply lessdef_vint in X.
    des (f b). des p.
    + destruct (peq b1 b); 
      destruct (peq b0 b); subst; auto.
      * econstructor; eauto.
        rewrite ! Int.add_zero_l in X; subst. apply Int.add_commut.
      * rewrite pred_dec_true in X; auto. 
        rewrite ! Int.add_zero_l in X; subst.
        apply lessdef_vint in E.
        rewrite Int.add_zero_l in E.
        rewrite E in X.
        apply f_equal with (f:= fun x => Int.sub x i0) in X.
        rewrite ! Int.sub_add_opp in X. revert X; sint.
        rewrite Int.add_neg_zero.
        rewrite ! Int.add_zero. discriminate.
      * rewrite pred_dec_false in X; auto.
        rewrite Int.add_zero_l in X. subst.
        apply lessdef_vint in D. contradict D.
        generalize (Int.add (Int.add Int.one (Int.repr z)) i).
        red; intros.
        apply f_equal with (f:= fun x => Int.sub x i0) in H0.
        revert H0; sint.
        rewrite Int.sub_idem.
        rewrite Int.sub_add_opp; sint. rewrite Int.add_neg_zero.
        rewrite Int.add_zero. discriminate.
      * rewrite peq_true in X. 
        apply f_equal with (f:= fun x => Int.sub x (Int.repr 2)) in X.
        revert X.
        rewrite ! (Int.add_commut (Int.repr 2)).
        rewrite ! Int.sub_add_opp.
        sint.
        rewrite ! Int.add_neg_zero. rewrite Int.add_zero. intro; subst.
        apply lessdef_vint in D.
        apply lessdef_vint in E.
        destruct (peq b1 b0); subst; auto.
        econstructor; eauto.
        rewrite Int.add_permut. rewrite ! (Int.add_commut i).
        f_equal.
        rewrite Int.add_permut. rewrite <- Int.add_assoc.
        rewrite (Int.add_commut (Int.neg _)). rewrite Int.add_neg_zero.
        apply Int.add_zero_l.
        rewrite ! Int.add_zero_l in E.
        exfalso; clear - E.
        revert E.
        rewrite Int.add_permut.  intro X; apply int_add_eq_l in X.
        revert X.
        replace i with (Int.add i Int.zero) at 1.
        rewrite Int.add_permut.
        intro X.
        apply int_add_eq_l in X.
        discriminate.
        apply Int.add_zero.
    + apply lessdef_vint in D.
      apply lessdef_vint in E.
      subst.
      revert E; sint. rewrite ! Int.add_zero_l; intro; subst.
      rewrite <- ! (Int.add_commut i0) in D.
      apply int_add_eq_l in D. discriminate.
Qed.



Definition ei_ld (ei: meminj -> expr_sym -> expr_sym -> Prop) : Prop :=
  forall f cm em e1 e1',
    ei f e1 e1' ->
    Values.Val.lessdef (eSexpr (Val.inj_alloc cm f) (Val.inj_em em f) e1)
                       (eSexpr cm em e1').

Lemma ei_ld_ei:
  ei_ld Val.expr_inject.
Proof.
  red; intros.
  destruct H.
  erewrite <-  (Val.apply_inj_eSexpr _ _ _ _ _ inj_ok); eauto.
Qed.

Lemma ei_ld_ei':
  ei_ld expr_inject'.
Proof.
  red; intros. inv H.
  exploit ei_ld_ei; eauto.
  intro D.
  eapply Values.Val.lessdef_trans.
  apply ei_ld_1.
  eapply Values.Val.lessdef_trans.
  apply D.
  apply ei_ld_2.
Qed.


Definition cm_inj (al: mem) (f: meminj) (al': mem) :=
  forall b b' delta
    (FB: f b = Some (b', delta)),
    al' b = Int.add (al b') (Int.repr delta).

Example cm_inj_inj_alloc:
  forall f al,
    cm_inj al f (Val.inj_alloc al f).
Proof.
  red; intros.
  unfold Val.inj_alloc. rewrite FB. auto.
Qed.

Definition em_inj (em: block -> int -> byte) (f: meminj) (em': block -> int -> byte) :=
  forall b b' delta
    (FB: f b = Some (b', delta)) i,
    em' b i = em b' (Int.add i (Int.repr delta)).

Example em_inj_inj_em:
  forall f em,
    em_inj em f (Val.inj_em em f).
Proof.
  red; intros.
  unfold Val.inj_em. rewrite FB. auto.
Qed.

Definition same_eval_inj (f: meminj) (e1 e2: expr_sym) :=
  forall al em al' em' 
    (IA: cm_inj al f al')
    (IE: em_inj em f em'),
    (eSexpr al' em' e1) = (eSexpr al' em' e2).


  Definition wf_ei_typ ei :=
    forall (f:meminj) a b,
      ei f a b ->
      same_eval_inj f a (Eval Vundef) \/ (forall t, wt_expr a t <-> wt_expr b t).

    Definition ei_ld' ei :=
    forall f e1 e1'
      (EI: ei f e1 e1')
      cm em cm' em'
      (ai: cm_inj cm f cm')
      (ie: em_inj em f em'),
      Values.Val.lessdef (eSexpr cm' em' e1) (eSexpr cm em e1').


Definition wf_inj_refl ei :=
  forall f sv v,  same_eval sv (Eval v) ->
             match v with
               Vptr b _ => f b = Some (b,0)
             | _ => True
             end ->
             ei f sv sv.


Record wf_inj (ei : meminj -> expr_sym -> expr_sym -> Prop) : Prop :=
  {
    ei_inj_incr: Val.inj_incr_compat ei;
    ei_unop: forall f u t a b
                    (EI: ei f a b),
               ei f (Eunop u t a) (Eunop u t b);
    ei_binop: forall f bi t t' a b c d
                     (EI1: ei f a b)
                     (EI2: ei f c d),
                ei f (Ebinop bi t t' a c) (Ebinop bi t t' b d);
    ei_val: forall f v
                   (VINJ: val_inject f v v),
              ei f (Eval v) (Eval v);
    vi_ei: forall f v v', Val.apply_inj f v = Some v' -> ei f v v';
    ei_ld'_expr: ei_ld' ei;
    wf_inj_undef: forall f v v', same_eval_inj f v (Eval Vundef) -> ei f v v'
    ;
    wf_typ: wf_ei_typ ei;
    wf_ir: wf_inj_refl ei

  }.

Lemma ei_ld_expr:
  forall ei (WF: wf_inj ei), ei_ld ei.
Proof.
  red; intros.
  eapply ei_ld'_expr; eauto.
  apply cm_inj_inj_alloc.
  apply em_inj_inj_em.
Qed.


Inductive expr_inj (f: meminj) : expr_sym -> expr_sym -> Prop :=
| expr_inj_vundef: forall v, expr_inj f (Eval Vundef) v
| expr_inj_val: forall v1 v2 (VI: val_inject f v1 v2), expr_inj f (Eval v1) (Eval v2)
| expr_inj_undef: forall b b0 i z (FB: f b = Some (b0,z)),
                              expr_inj f (Eundef b i) (Eundef b0 (Int.add i (Int.repr z)))
| expr_inj_unop: forall e1 e2 u t (EI: expr_inj f e1 e2), expr_inj f (Eunop u t e1) (Eunop u t e2)
| expr_inj_binop: forall e1 e2 f1 f2 b t1 t2 (EI1: expr_inj f e1 e2) (EI2: expr_inj f f1 f2),
    expr_inj f (Ebinop b t1 t2 e1 f1) (Ebinop b t1 t2 e2 f2).

Lemma expr_inj_incr:
  Val.inj_incr_compat expr_inj.
Proof.
  red; intros.
  revert e1 e2 EI.
  induction 1; constructor; auto.
  eapply val_inject_incr; eauto.
Qed.



Lemma expr_inj_ld:
   forall (f : meminj) (e1 e1' : expr_sym)
     (ei: expr_inj f e1 e1')
     (cm : block -> int) (em : block -> int -> byte),
     Values.Val.lessdef
       (eSexpr (Val.inj_alloc cm f) (Val.inj_em em f) e1)
       (eSexpr cm em e1').
Proof.
  induction 1; simpl; intros; auto.
  - inv VI; simpl; auto.
    unfold Val.inj_alloc. rewrite FB. sint. rewrite (Int.add_commut ofs1); auto.
  - unfold Val.inj_em. rewrite FB. auto.
  - apply ld_unop; auto.
  - apply ld_binop; auto.
Qed.

Definition binrelexpr := expr_sym -> expr_sym -> Prop.

Definition close (R:binrelexpr) (P Q: binrelexpr) : binrelexpr :=
  fun a b =>
    exists a' b', P a a' /\ Q b b' /\ R a' b'.

Definition expr_inj_se f := close (expr_inj f) (same_eval_inj f) same_eval.

Lemma wf_inj_refl_expr_inj_se:
  wf_inj_refl expr_inj_se.
Proof.
  red; intros.
  exists (Eval v), (Eval v); repSplit; auto.
  red; intros; rewrite H; auto.
  constructor.
  des v; econstructor; eauto. rewrite Int.add_zero; auto. 
Qed.


Lemma cm_inj_incr:
  forall al f f' al'
    (IA: cm_inj al f' al')
    (INCR: inject_incr f f'),
    cm_inj al f al'.
Proof.
  red; intros.
  apply IA.
  apply INCR. auto.
Qed.



Lemma em_inj_incr:
  forall al f f' al'
    (EI: em_inj al f' al')
    (INCR: inject_incr f f'),
    em_inj al f al'.
Proof.
  red; intros.
  apply EI.
  apply INCR. auto.
Qed.


Lemma same_eval_inj_incr:
  forall f f' (INCR: inject_incr f f')
    a b (SEI: same_eval_inj f a b),
    same_eval_inj f' a b.
Proof.
  red; intros.
  eapply SEI.
  eapply cm_inj_incr; eauto.
  eapply em_inj_incr; eauto.
Qed.

Lemma unop_same_eval_inj:
  forall f u t e1 e2,
    same_eval_inj f e1 e2 ->
    same_eval_inj f (Eunop u t e1) (Eunop u t e2).
Proof.
  red; intros.
  generalize (H _ _ _ _ IA IE).
  simpl.
  intro A; inv A. auto.
Qed.



Lemma binop_same_eval_inj:
  forall f b t1 t2 e1 e2 e3 e4,
    same_eval_inj f e1 e2 ->
    same_eval_inj f e3 e4 ->
    same_eval_inj f (Ebinop b t1 t2 e1 e3) (Ebinop b t1 t2 e2 e4).
Proof.
  red; intros; simpl.
  f_equal.
  generalize (H _ _ _ _ IA IE).
  generalize (H0 _ _ _ _ IA IE).
  intros A B.
  inv A. inv B.
  auto.
  eapply H0; eauto.
Qed.

Lemma sei_sym:
  forall f a b,
    same_eval_inj f a b ->
    same_eval_inj f b a.
Proof.
  red; intros.
  symmetry; eapply H; eauto.
Qed.

Instance same_eval_inj_equi :
  forall f, RelationClasses.PreOrder (same_eval_inj f).
Proof.
  constructor.
  red; red; intros; auto.
  (* red; apply sei_sym. *)
  red; red; intros.
  erewrite H; eauto. 
Qed.

  Lemma expr_inj_type:
    forall f a b,
      expr_inj f a b ->
      same_eval a (Eval Vundef) \/ (forall t, wt_expr a t <-> wt_expr b t).
  Proof.
    induction 1; simpl; intros; auto.
    - left; reflexivity.
    - inv VI; auto; try (right; intros; des (t:styp); fail).
      left; reflexivity.
    - destr.
    - destr; subst.
      left; red; intros; simpl; rewrite H0; destr.
      rewrite fun_of_unop_undef; auto.
      right; intros. rewrite H0. tauto.
    - destruct IHexpr_inj1.
      left; red; intros; simpl; rewrite H1.
      apply fun_of_binop_undef_l.
      destruct IHexpr_inj2.
      left; red; intros; simpl; rewrite H2.
      apply fun_of_binop_undef_r.
      right; intros. rewrite H1,H2. tauto.
  Qed.

  Lemma expr_inj_type':
    forall f a b,
      expr_inj f a b ->
      same_eval_inj f a (Eval Vundef) \/ (forall t, wt_expr a t <-> wt_expr b t).
  Proof.
    induction 1; simpl; intros; auto.
    - left; reflexivity.
    - inv VI; auto; try (right; intros; des (t:styp); fail).
      left; reflexivity.
    - destr.
    - destr; subst.
      left; red; intros; simpl.
      exploit H0; eauto. intros A; inv A; auto;
                         try rewrite H2; rewrite fun_of_unop_undef; auto.
      right; intros. rewrite H0. tauto.
    - destruct IHexpr_inj1.
      left; red; intros; simpl; exploit H1; eauto.
      intros A; inv A; auto; try rewrite H3;
      rewrite fun_of_binop_undef_l; auto.
      destruct IHexpr_inj2.
      left; red; intros; simpl; exploit H2; eauto.
      intros A; inv A; auto; try rewrite H4;
      rewrite fun_of_binop_undef_r; auto.
      right; intros. rewrite H1,H2. tauto.
  Qed.

  
  Lemma get_type_same_type:
    forall a b,
      (forall t, wt_expr a t <-> wt_expr b t) ->
      get_type a = get_type b.
  Proof.
    unfold get_type; repeat destr_no_dep; rewrite H in *; destr.    
  Qed.
  
  Lemma expr_inj_get_type:
    forall f a b,
      expr_inj f a b ->
      same_eval a (Eval Vundef) \/ get_type a = get_type b.
  Proof.
    intros.
    destruct (expr_inj_type _ _ _ H); auto.
    right; apply get_type_same_type; auto.
  Qed.

  Lemma nu_se_st:
    forall v v',
      ~ same_eval (Eval Vundef) v ->
      same_eval v v' ->
      (forall t, wt_expr v t <-> wt_expr v' t).
  Proof.
    split; intros.
    destruct (wt_expr_dec v' t); auto.
    exfalso; apply H; red; intros; rewrite (proj1 (same_eval_nwt_vundef _ _ _ H1 n H0 cm em)); auto.
    destruct (wt_expr_dec v t); auto.
    symmetry in H0. rewrite <- H0 in H.
    exfalso; apply H; red; intros; rewrite (proj1 (same_eval_nwt_vundef _ _ _ H1 n H0 cm em)); auto.
  Qed.


  Lemma nu_sei_st:
    forall f v v',
      ~ same_eval_inj f v (Eval Vundef) ->
      same_eval_inj f v v' ->
      (forall t, wt_expr v t <-> wt_expr v' t).
  Proof.
    split; intros.
    destruct (wt_expr_dec v' t); auto.
    exfalso; apply H. red; intros.
    generalize (expr_type _ _ H1 al' em'), (fun pf => expr_type' al' em' _ _ pf n).
    intros A B.
    rewrite <- B.
    erewrite H0; eauto. simpl.
    seval; auto. erewrite <- H0; eauto.
    
    destruct (wt_expr_dec v t); auto.
    exfalso; apply H. red; intros.
    generalize (expr_type _ _ H1 al' em'), (fun pf => expr_type' al' em' _ _ pf n).
    intros A B. exploit H0; eauto.
    intro C; rewrite C in *. eauto.
  Qed.

  
  Lemma ei_vundef:
    forall f a b (EI: expr_inj f a b)
      al em (U: eSexpr al em b = Vundef),
      eSexpr (Val.inj_alloc al f) (Val.inj_em em f) a = Vundef.
  Proof.
    intros.
    generalize (expr_inj_ld _ _ _ EI al em).
    intro A; inv A; congruence.
  Qed.

  
  Lemma expr_inj_ld':
    ei_ld' expr_inj.
  Proof.
    induction 1; simpl; intros; auto.
    - inv VI; simpl; auto.
      rewrite (ai _ _ _ FB). sint. rewrite (Int.add_commut ofs1); auto.
    - rewrite (ie _ _ _ FB). auto. 
    - apply ld_unop; auto.
    - apply ld_binop; auto.
  Qed.

  Lemma  expr_inj_se_ld':
    ei_ld' expr_inj_se.
  Proof.
    red; intros.
    destruct EI as (a & b & A & B & C).
    rewrite B.
    erewrite A; eauto.
    eapply expr_inj_ld'; eauto.
  Qed.
  
  Lemma expr_inj_nundef:
    forall f a b
      (EI: expr_inj f a b)
      (NU: ~ same_eval_inj f a (Eval Vundef)),
      ~ same_eval b (Eval Vundef).
  Proof.
    intros.
    cut (exists al al' em em', cm_inj al f al' /\ em_inj em f em' /\
                          eSexpr al' em' a <> Vundef).
    intros; dex; destr_and.
    intro SEU.
    generalize (expr_inj_ld' _ _ _ EI al em al' em' H H0).
    rewrite SEU.
    simpl. intro D; inv D; congruence.
    repeat (apply Classical_Pred_Type.not_all_ex_not in NU; dex).
    exists n, n1, n0, n2; repSplit; auto.
  Qed.

  Lemma nse_sym:
    forall a b,
      ~ same_eval a b -> ~ same_eval b a.
  Proof.
    red; intros.
    symmetry in H0; apply H; auto.
  Qed.


  (* Lemma nsei_sym: *)
  (*   forall f a b, *)
  (*     ~ same_eval_inj f a b -> ~ same_eval_inj f b a. *)
  (* Proof. *)
  (*   red; intros. *)
  (*   symmetry in H0; apply H; auto. *)
  (* Qed. *)


Lemma expr_inj_se_get_type:
    forall f a b
      (EI: expr_inj_se f a b),
      same_eval_inj f a (Eval Vundef) \/ (forall t, wt_expr a t <-> wt_expr b t).
  Proof.
    intros f a b [c [d [A [B C]]]].
    destruct (Classical_Prop.classic (same_eval_inj f a (Eval Vundef))); auto.
    rewrite A. 
    destruct (Classical_Prop.classic (same_eval_inj f c (Eval Vundef))); auto.
    destruct (expr_inj_type' _ _ _ C); auto.
    right. intro.
    generalize (expr_inj_nundef _ _ _ C H0). intro NU.
    rewrite <- (nu_se_st _ _ (nse_sym _ _ NU) (same_eval_sym _ _ B)).
    rewrite <- H1.
    rewrite (nu_sei_st _ _ _ H A).
    tauto.
  Qed.

  
  (* Lemma expr_inj_nundef': *)
  (*   forall f a b *)
  (*     (EI: expr_inj f a b) *)
  (*     (NU: ~ same_eval  a (Eval Vundef)), *)
  (*     ~ same_eval b (Eval Vundef). *)
  (* Proof. *)
  (*   intros. *)
  (*   red; intros. *)
  (*   apply NU. clear NU. *)
  (*   red; intros. *)
  (*   specialize (H cm em). simpl in *. *)
  (*   revert a b EI H. induction 1. *)
  (*   - simpl; auto. *)
  (*   - simpl. *)
  (*     inv VI; simpl; auto. congruence. *)
  (*   - simpl; congruence. *)
  (*   - simpl. *)
  (*     cut (exists al al' em em', cm_inj al f al' /\ em_inj em f em' /\ *)
  (*                           eSexpr al' em' a <> Vundef). *)
  (*   intros; dex; destr_and. *)
  (*   intro SEU. *)
  (*   generalize (expr_inj_ld' _ _ _ EI al em al' em' H H0). *)
  (*   rewrite SEU. *)
  (*   simpl. intro D; inv D; congruence. *)
  (*   repeat (apply Classical_Pred_Type.not_all_ex_not in NU; dex). *)
  (*   exists n, n1, n0, n2; repSplit; auto. *)
  (* Qed. *)

  

  (* Lemma expr_inj_se_get_type_eq: *)
  (*   forall f a b *)
  (*     (EI: expr_inj_se f a b), *)
  (*     same_eval_inj f a (Eval Vundef) \/ get_type a = get_type b. *)
  (* Proof. *)
  (*   intros. *)
  (*   edestruct expr_inj_se_get_type; eauto. *)
  (*   right; apply get_type_same_type; auto. *)
  (* Qed. *)

  (* Lemma expr_inj_se_get_type: *)
  (*           forall f a b *)
  (*             (EI: expr_inj_se f a b), *)
  (*             same_eval a (Eval Vundef) \/ (forall t, wt_expr a t <-> wt_expr b t). *)
  (*         Proof. *)
  (*           intros f a b [c [d [A [B C]]]]. *)
  (*           destruct (Classical_Prop.classic (same_eval a (Eval Vundef))); auto. *)
  (*           rewrite A.  *)
  (*           destruct (Classical_Prop.classic (same_eval c (Eval Vundef))); auto. *)
  (*           destruct (expr_inj_type' _ _ _ C); auto. *)
  (*           right. intro. *)
  (*           generalize (expr_inj_nundef _ _ _ C H0). intro NU. *)
  (*           rewrite <- (nu_se_st _ _ (nse_sym _ _ NU) (same_eval_sym _ _ B)). *)
  (*           rewrite <- H1. *)
  (*           rewrite (nu_sei_st _ _ _ H A). *)
  (*           tauto. *)
  (*         Qed. *)
  
Lemma wf_inj_expr_inj_se: wf_inj expr_inj_se.
Proof.
  constructor.
  - red; simpl; intros.
    destruct EI as (a' & b' & A & B & C).
    eexists; eexists; repSplit; eauto.
    eapply same_eval_inj_incr; eauto.
    eapply expr_inj_incr; eauto.
  - unfold expr_inj_se, close; simpl; intros.
    dex; repeat destr_and.
    eexists; eexists; repSplit.
    apply unop_same_eval_inj; eauto.
    apply unop_same_eval; eauto.
    apply expr_inj_unop; auto.
  - unfold expr_inj_se, close; simpl; intros.
    dex; repeat destr_and.
    eexists; eexists; repSplit.
    apply binop_same_eval_inj; eauto.
    apply binop_same_eval; eauto.
    apply expr_inj_binop; auto.
  - unfold expr_inj_se, close; intros.
    eexists; eexists; repSplit.
    reflexivity. reflexivity.
    apply expr_inj_val; auto.
  - red; red; intros. exists v, v'; repSplit; try reflexivity.
    revert v v' H; induction v; simpl; intros.
    unfold Val.inj_ptr in H.
    des v; try (des (f b); des p); inv H; try repeat econstructor; eauto.
    unfold Val.inj_undef in H. des (f b); des p; inv H.
    constructor; auto.
    des (Val.apply_inj f v); inv H.
    constructor; auto.
    des (Val.apply_inj f v1); des (Val.apply_inj f v2); inv H.
    constructor; auto.
  - apply expr_inj_se_ld'.
  - red; red;intros.
    exists (Eval Vundef), v'; repSplit; auto.
    reflexivity.
    constructor.
  - red; intros.
    apply expr_inj_se_get_type; auto.
  - apply wf_inj_refl_expr_inj_se.
Qed.

Hint Resolve wf_inj_expr_inj_se.


Section INJ.

  Variable ei : meminj -> expr_sym -> expr_sym -> Prop.
  Hypothesis WF: wf_inj ei.
 
  Inductive memval_inject (f: meminj) : memval -> memval -> Prop :=
  | memval_inject_symb:
      forall e1 e2 n m t t'
        (Hmeminj: ei f (get_nth_part e1 n) (get_nth_part e2 m))
        (TYPorUNDEF: t = t' \/ same_eval_inj f (get_nth_part e1 n) (Eval Vundef)),
        memval_inject f (Symbolic e1 t n) (Symbolic e2 t' m).

  Lemma memval_inject_incr:
    forall f f' v1 v2,
      memval_inject f v1 v2 ->
      inject_incr f f' ->
      memval_inject f' v1 v2.
  Proof.
    intros. inv WF. inv H. econstructor; eauto.
    destruct TYPorUNDEF; auto.
    right; eapply same_eval_inj_incr; eauto.
  Qed.

  Theorem gnp_inject:
    forall n (f: meminj) vl1 vl2
           (EI: ei f vl1 vl2),
      ei f (get_nth_part vl1 n) (get_nth_part vl2 n).
  Proof.
    inv WF.
    induction n; simpl; intros; eauto.
  Qed.

  Theorem eom_inject:
    forall f a b
           (MI : memval_inject f a b),
      ei f (expr_of_memval a) (expr_of_memval b).
  Proof.
    intros.
    inv MI.   
    unfold expr_of_memval. auto.
  Qed.

  Theorem psa_inject:
    forall f vl1 vl2,
      list_forall2 (memval_inject f) vl1 vl2 ->
      ei f (proj_symbolic_aux_le vl1) (proj_symbolic_aux_le vl2).
  Proof.
    inv WF.
    induction 1; simpl; eauto.
    apply ei_binop0; auto.
    apply eom_inject; auto.
  Qed.

  Theorem ps_inject:
    forall f vl1 vl2 ,
      list_forall2 (memval_inject f) vl1 vl2 ->
      ei f (proj_symbolic_le vl1) (proj_symbolic_le vl2).
  Proof.
    intros.
    unfold proj_symbolic_le.
    apply psa_inject.
    apply list_forall2_rib; auto.
  Qed.
  
     
  Lemma mvinj_type:
    forall f vl1 vl2,
      list_forall2 (memval_inject f) vl1 vl2 ->
      type_of_list_memval vl1 = type_of_list_memval vl2 \/
      exists h, head vl1 = Some h /\ same_eval_inj f (expr_of_memval h) (Eval Vundef).
  Proof.
    intros.
    destruct H; simpl; auto. 
    inv H.
    destruct TYPorUNDEF; subst; auto.
    right; exists (Symbolic e1 t n); split; auto.
  Qed.

  Lemma in_psale_undef:
    forall v e,
      In e v ->
      forall f,
      same_eval_inj f (expr_of_memval e) (Eval Vundef) ->
      same_eval_inj f (proj_symbolic_aux_le v) (Eval Vundef).
  Proof.
    induction v; simpl; intros. destr.
    destr; subst.
    - red; intros; simpl. erewrite H0; eauto.
    - red; intros; simpl.
      erewrite  IHv; eauto.
      seval; auto.
  Qed.
      
  Lemma in_decode_undef:
    forall v c e,
      In e v ->
      forall f, 
      same_eval_inj f (expr_of_memval e) (Eval Vundef) ->
      same_eval_inj f (decode_val c v) (Eval Vundef) .
  Proof.
    intros.
    assert (In e (rev_if_be v)).
    apply in_rib; auto. clear H.
    unfold decode_val, proj_symbolic_le.
    generalize (in_psale_undef _ _ H1 _ H0). clear.
    red; intros.
    des c; repeat destr; try erewrite H in *; eauto; destr;
    try rewrite convert_undef in *; destr.
  Qed.
 



Lemma in_psale_undef':
  forall l x,
    In x l ->
    same_eval (expr_of_memval x) (Eval Vundef) ->
    same_eval (proj_symbolic_aux_le l) (Eval Vundef).
Proof.
  induction l; simpl; intros; eauto. easy.
  destr; subst.
  red; intros; simpl.
  rewrite H0. simpl; auto.
  red; intros; simpl; erewrite IHl; simpl; eauto.
  seval.
Qed.

Lemma in_decode_undef':
  forall chunk l x,
    In x l ->
    same_eval (expr_of_memval x) (Eval Vundef) ->
    same_eval (decode_val chunk l) (Eval Vundef).
Proof.
  intros.
  unfold decode_val.
  unfold proj_symbolic_le.
  generalize (fun pf => in_psale_undef' (rev_if_be l) x pf H0).
  intro G; trim G. apply in_rib; auto.
  red; intros; des chunk; repeat destr; try rewrite G in *; seval; destr.
  rewrite convert_undef in Heqv; congruence.
  rewrite convert_undef in Heqv; congruence.
Qed.

  Theorem decode_val_inject:
    forall f vl1 vl2 chunk,
      (* chunk <> Many32 -> chunk <> Many64 -> *)
      list_forall2 (memval_inject f) vl1 vl2 ->
      ei f (decode_val chunk vl1) (decode_val chunk vl2).
  Proof.
    intros.
    Transparent decode_val.
    destruct (mvinj_type _ _ _ H).
    - unfold decode_val, from_bits.
      rewrite H0.
      destruct WF.
      des chunk; repeat destr; repeat apply ei_unop0; auto; try apply ps_inject; auto.
    - dex; destr.
      inv WF. apply wf_inj_undef0.
      eapply in_decode_undef; eauto.
      apply hd_error_in; eauto.
  Qed.  

  
  Lemma same_eval_inj_undef:
    forall f v,
      same_eval_inj f v (Eval Vundef) <->
      (forall al em al' em' (IA: cm_inj al f al') (IE: em_inj em f em'),
          eSexpr al' em' v = Vundef).
  Proof.
    red; split; intros; eauto.
  Qed.

  Lemma encode_val_inject:
    forall f v1 v2 chunk
      (EI: ei f v1 v2),
      list_forall2 (memval_inject f) (encode_val chunk v1) (encode_val chunk v2).
  Proof.
    intros.
    unfold encode_val.
    unfold inj_symbolic; simpl.
    apply list_forall2_rev.
    apply list_forall2_rib.
    generalize (size_chunk_nat chunk).
    induction n; simpl; intros; auto.
    - constructor.
    - constructor; auto.
      clear IHn.
      assert ((chunk <> Many32 /\ chunk <> Many64) \/ chunk = Many32 \/ chunk = Many64) by des chunk.
      destruct H.
      + generalize (gnp_inject); intro GI.
        des chunk; try rewrite H1; destr; constructor; destruct WF; eauto.
      + des chunk.
        * destruct (wf_typ _ WF _ _ _ EI).
          rewrite same_eval_inj_undef in H.
          assert (same_eval_inj
                    f
                    (get_nth_part
                       match get_type v1 with
                       | Tint => Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint v1
                       | Tlong => Eval Vundef
                       | Tfloat => Eval Vundef
                       | Tsingle =>
                         Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint
                               (Eunop OpBitsofsingle Tsingle v1)
                       end n) (Eval Vundef)).
          red; intros.
          specialize (H _ _ _ _ IA IE).
          rewrite gnp_rew; destr; simpl; auto; try rewrite H; try rewrite convert_undef; des n; auto.
          constructor; auto. apply wf_inj_undef; auto.
          rewrite (get_type_same_type _ _ H).
          constructor; auto; inversion WF; destr; apply gnp_inject; eauto.
        * destruct (wf_typ _ WF _ _ _ EI).
          assert (same_eval_inj
                    f
                    (get_nth_part
                       match get_type v1 with
                       | Tint => Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint v1
                       | Tlong => v1
                       | Tfloat => Eunop OpBitsofdouble Tfloat v1
                       | Tsingle =>
                         Eunop (OpConvert SEUnsigned (Tlong, SEUnsigned)) Tint
                               (Eunop OpBitsofsingle Tsingle v1)
                       end n) (Eval Vundef)).
          red; intros.
          rewrite same_eval_inj_undef in H.
          specialize (H _ _ _ _ IA IE).
          rewrite gnp_rew; destr; simpl; auto; try rewrite H; try rewrite convert_undef; des n; auto.
          constructor; auto. apply wf_inj_undef; auto.
          rewrite (get_type_same_type _ _ H).
          constructor; auto; inversion WF; destr; apply gnp_inject; eauto.
  Qed.
  
End INJ.

  
  Lemma encode_val_inject':
    forall f v1 v2 chunk
      (EI: expr_inj_se f v1 v2),
      list_forall2 (memval_inject expr_inj_se f) (encode_val chunk v1) (encode_val chunk v2).
  Proof.
    intros.
    apply encode_val_inject; auto.
  Qed.
  
  (** [memval_inject] and compositions *)


Definition expr_list_inject (f: meminj) (a b: list expr_sym) : Prop :=
  list_forall2 (expr_inj_se f) a b.

Inductive list_ei (ei: meminj -> expr_sym -> expr_sym -> Prop) (f: meminj): list expr_sym -> list expr_sym -> Prop :=
| list_ei_nil: list_ei ei f nil nil
| list_ei_cons: forall a b al bl
                  (EI: ei f a b)
                  (LEI: list_ei ei f al bl),
                  list_ei ei f (a::al) (b::bl).


Lemma expr_list_inject_list_ei:
forall f vl1 vl2,
  expr_list_inject f vl1 vl2 ->
  list_ei expr_inj_se f vl1 vl2.
Proof.
  induction 1; simpl; intros.
  constructor.
  constructor; auto.
Qed.

Lemma list_ei_expr_list_inject:
forall f vl1 vl2,
  list_ei expr_inj_se f vl1 vl2 ->
  expr_list_inject f vl1 vl2.
Proof.
  induction 1; simpl; intros.
  constructor.
  constructor; auto.
Qed.


Lemma memval_inject_undef:
  forall j n a t,
    memval_inject expr_inj_se j (Symbolic (Eval Vundef) t n) a.
Proof.
  intros.
  destruct a.
  constructor.
  repeat red.
  exists (Eval Vundef), (get_nth_part e n0); repSplit; auto.
  red; intros; simpl; auto.
  rewrite gnp_rew. simpl. des n; auto.
  reflexivity.
  constructor.
  right. red; intros.
  rewrite gnp_rew. des n; auto.
Qed.


Lemma expr_inj_se_vundef:
  forall j v,
    expr_inj_se j (Eval Vundef) v.
Proof.
  intros; repeat eexists; constructor.
Qed.

Definition decode_encode chunk v := decode_val chunk (encode_val chunk v).


Definition tolm_eq:
  forall  chunk b,
    type_of_list_memval
      (encode_val chunk b)
    =
    match chunk with
      Many32 | Many64 => Some (get_type b)
    | _ => None
    end.
Proof.
  des chunk. 
Qed.

Lemma same_eval_wt:
  forall v' (NU: ~ exists al em, eSexpr al em v' = Vundef)
    v (SE: same_eval v v')
    t (WT: wt_expr v' t),
    wt_expr v t.
Proof.
  intros.
  destruct (wt_expr_dec v t); auto.
  set (al := fun _:block => Int.zero).
  set (em := fun (_:block) (_:int) => Byte.zero).
  generalize (expr_type _ _ WT al em).
  generalize (fun H => expr_type' al em _ _ H n).
  generalize (expr_nu_type al em v t _ eq_refl).
  intros A1 A2 A3.
  eapply A1. rewrite SE. intro EU; apply NU; eexists; eauto.
  rewrite SE. apply A3.
Qed.



Lemma expr_inj_wt:
  forall f e1 e2, expr_inj f e1 e2 ->
             forall t, wt_expr e2 t -> wt_expr e1 t.
Proof.
  induction 1; simpl; auto.
  inv VI; intros; simpl; auto.
  destr.
  apply IHexpr_inj; auto.
  destr.
  apply IHexpr_inj1; auto.
  apply IHexpr_inj2; auto.
Qed.

Lemma expr_inj_se_to_bits:
  forall f v v' chunk,
    get_type v = get_type v' ->
    expr_inj_se f v v' ->
    expr_inj_se f (to_bits chunk v) (to_bits chunk v').
Proof.
  intros.
  destruct wf_inj_expr_inj_se.
  des chunk; eauto;
  rewrite H.
  destr; eauto.
  destr; eauto.
Qed.

Lemma decode_encode_inj:
  forall f a b
    (EQT: get_type a = get_type b)
    (EI: expr_inj_se f a b)
    chunk,
    expr_inj_se f (decode_encode chunk a) (decode_encode chunk b).
Proof.
  clear. intros.
  destruct wf_inj_expr_inj_se.
  des chunk;
    repeat (apply ei_unop0 || apply ei_binop0 || auto);
  rewrite ! tolm_eq; rewrite EQT;
  destr;
  repeat (apply ei_unop0 || apply ei_binop0 || apply expr_inj_se_to_bits || auto);
  congruence.
Qed.


Lemma expr_inj_se_se:
  forall f a b c,
    expr_inj_se f a b ->
    same_eval b c ->
    expr_inj_se f a c.
Proof.
  intros.
  destruct H as (x & y & A & B & C).
  exists x, y; repSplit; auto. congruence.
Qed.


Lemma expr_inj_se_l:
  forall f a b c,
    expr_inj_se f a b ->
    same_eval a c ->
    expr_inj_se f c b.
Proof.
  intros.
  destruct H as (x & y & A & B & C).
  exists x, y; repSplit; auto.
  rewrite <- A.
  red; intros; rewrite H0; auto.
Qed.

Lemma get_type_correct_not_int_2:
  forall v t,
    get_type v = Tint ->
    wt_expr v t ->
    t <> Tint ->
    wt_expr v Tint.
Proof.
  unfold get_type.
  intros.
  repeat (revert H; destr).
  des t.
Qed.

Ltac exp_get_type H :=
  match type of H with
    get_type ?v = ?t => unfold get_type in H;
      destruct (wt_expr_dec v Tint);
      destruct (wt_expr_dec v Tfloat);
      destruct (wt_expr_dec v Tsingle);
      destruct (wt_expr_dec v Tlong); destr
  end.

Ltac egt :=
  repeat match goal with
    H: get_type ?v = ?t |- _ => exp_get_type H
  end.

Lemma decode_encode_eSexpr :
  forall v chunk,
    same_eval (decode_encode chunk v) (Val.load_result chunk v).
Proof.
  clear.
  red. intros v chunk cm em.
  unfold decode_encode.
  generalize (decode_encode_val_general v chunk chunk); intro DE.
  pose (n:=chunk). 
  des chunk; try (specialize (DE cm em); simpl in *; rewrite DE; now auto).
  rewrite tolm_eq in *.
  destr; auto.
  - destr; try now egt. rewrite <- DE; destr.
  - destr; destr; try now (egt;
                            match goal with
                              H: wt_expr ?v ?t,
                                 H0: wt_expr ?v ?t' |-
                              context [eSexpr ?al ?em ?v] =>
                              let x := fresh in
                              assert (t <> t') as x by congruence;
                                rewrite (wt_expr_2_is_undef v t t' H H0 x); destr
                            end).
    setoid_rewrite (DE cm em); auto.
    setoid_rewrite (DE cm em); auto.
    egt.
    rewrite nwt_expr_undef; auto.
    intro; dex. des t.
Qed.

Lemma weak_wt_wt:
  forall e t t',
    weak_wt e t ->
    wt_expr e t' ->
    e <> Eval Vundef ->
    t = t'.
Proof.
  intros e t t' A B C.
  des A.
  des (styp_eq t t').
  generalize (wt_expr_2_is_undef _ _ _ w B n). congruence.
  exfalso; apply n. eauto.
Qed.

Tactic Notation "Trim" constr(L) "as" ident(H) :=
  let x := fresh H in
  assert (x:=L); trim x; [clear x|].

Lemma ei_vi:
  forall ei (wf: wf_inj ei) f v1 v2
    (ptr: match v1 with
            Vptr b o => f b <> None
          | _ => True
    end)
  ,
    
    ei f (Eval v1) (Eval v2) ->
    val_inject f v1 v2.
Proof.
  intros ei wf f v1 v2 ptr EI.
  generalize (fun al =>  ei_ld_expr  _ wf f al (fun _ _ => Byte.zero) _ _ EI); simpl.
  intro A; generalize (A (fun _ => Int.zero)); simpl.

  des v1; des v2; try solve [inv H; auto].
  - inv H. assert (forall al, al b = Int.zero).
    {
      intros.
      specialize (A al).
      apply lessdef_vint in A.
      rewrite <- ! (Int.add_commut i0) in A.
      apply int_add_eq_l in A. auto.
    }
    specialize (H (fun _ => Int.one)). discriminate.
  - inv H. unfold Val.inj_alloc in *.
    des (f b).
    des p.
    assert (forall al, al b0 = Int.zero).
    intros.
    specialize (A al).
    apply lessdef_vint in A.
    rewrite <- ! (Int.add_commut i) in A.
    apply int_add_eq_l in A. 
    rewrite <- ! (Int.add_commut (Int.repr z)) in A.
    apply int_add_eq_l in A.
    auto.
    specialize (H (fun _ => Int.one)). discriminate.
  - apply lessdef_vint in H.
    unfold Val.inj_alloc in H. des (f b); des p. revert H; sint. intro.
    apply int_add_eq_l in H.
    subst.
    econstructor.
    rewrite Heqo; repeat f_equal.
    generalize (A (fun bb => if peq bb b1 then Int.zero else Int.one)); clear -Heqo.
    unfold Val.inj_alloc. rewrite Heqo.
    rewrite peq_true. destr.
    apply lessdef_vint in H. revert H; sint. rewrite <- ! (Int.add_commut (Int.add _ _)).
    intro H; apply int_add_eq_l in H. discriminate.
    apply Int.add_commut.
Qed.
