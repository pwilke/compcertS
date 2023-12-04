(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the interface for the memory model that
  is used in the dynamic semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memdata.
Require Import Values_symbolic.
Require Import Values_symbolictype.
Require Import Normalise.
Require Import NormaliseSpec.

Require Export Memperm Alloc.



Inductive block_type : Type :=
  Normal | Dynamic.


Module Type MEM.

(** The abstract type of memory states. *)
Parameter mem: Type.


Parameter has_bounds : mem -> block -> Z -> Z -> bool.


(** * Operations on memory states *)

(** [empty] is the initial memory state. *)
Parameter empty: mem.

(** [alloc m lo hi] allocates a fresh block of size [hi - lo] bytes.
  Valid offsets in this block are between [lo] included and [hi] excluded.
  These offsets are writable in the returned memory state.
  This block is not initialized: its contents are initially undefined.
  Returns a pair [(m', b)] of the updated memory state [m'] and
  the identifier [b] of the newly-allocated block.
  Note that [alloc] never fails: we are modeling an infinite memory. *)
Parameter alloc: forall (m: mem) (lo hi: Z) (bt: block_type), option (mem * block).

(** [free m b lo hi] frees (deallocates) the range of offsets from [lo]
  included to [hi] excluded in block [b].  Returns the updated memory
  state, or [None] if the freed addresses are not writable. *)
Parameter free: forall (m: mem) (b: block) (lo hi: Z), option mem.

(** [load chunk m b ofs] reads a memory quantity [chunk] from
  addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the value read, or [None] if the accessed addresses
  are not readable. *)
Parameter load: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z), option expr_sym.

(** [store chunk m b ofs v] writes value [v] as memory quantity [chunk]
  from addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the updated memory state, or [None] if the accessed addresses
  are not writable. *)
Parameter store: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: expr_sym), option mem.

(** [loadv] and [storev] are variants of [load] and [store] where
  the address being accessed is passed as a value (of the [Vptr] kind). *)

Parameter loadv : memory_chunk -> mem -> expr_sym -> option expr_sym.

Parameter storev : memory_chunk -> mem -> expr_sym -> expr_sym -> option mem.

(** [loadbytes m b ofs n] reads and returns the byte-level representation of
  the values contained at offsets [ofs] to [ofs + n - 1] within block [b]
  in memory state [m].
  [None] is returned if the accessed addresses are not readable. *)
Parameter loadbytes: forall (m: mem) (b: block) (ofs n: Z), option (list memval).

(** [storebytes m b ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)
Parameter storebytes: forall (m: mem) (b: block) (ofs: Z) (bytes: list memval), option mem.

(** [free_list] frees all the given (block, lo, hi) triples. *)
Fixpoint free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

(** [drop_perm m b lo hi p] sets the permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have [Freeable] permissions
    in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

Parameter drop_perm: forall (m: mem) (b: block) (lo hi: Z) (p: permission), option mem.

(** * Permissions, block validity, access validity, and bounds *)

(** The next block of a memory state is the block identifier for the
  next allocation.  It increases by one at each allocation.
  Block identifiers below [nextblock] are said to be valid, meaning
  that they have been allocated previously.  Block identifiers above
  [nextblock] are fresh or invalid, i.e. not yet allocated.  Note that
  a block identifier remains valid after a [free] operation over this
  block. *)

Parameter nextblock: mem -> block.

Definition valid_block (m: mem) (b: block) := Plt b (nextblock m).

Axiom valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.

(** [perm m b ofs k p] holds if the address [b, ofs] in memory state [m]
  has permission [p]: one of freeable, writable, readable, and nonempty.
  If the address is empty, [perm m b ofs p] is false for all values of [p].
  [k] is the kind of permission we are interested in: either the current
  permissions or the maximal permissions. *)
Parameter perm: forall (m: mem) (b: block) (ofs: Z) (k: perm_kind) (p: permission), Prop.

(** Logical implications between permissions *)

Axiom perm_implies:
  forall m b ofs k p1 p2, perm m b ofs k p1 -> perm_order p1 p2 -> perm m b ofs k p2.

(** The current permission is always less than or equal to the maximal permission. *)

Axiom perm_cur_max:
  forall m b ofs p, perm m b ofs Cur p -> perm m b ofs Max p.
Axiom perm_cur:
  forall m b ofs k p, perm m b ofs Cur p -> perm m b ofs k p.
Axiom perm_max:
  forall m b ofs k p, perm m b ofs k p -> perm m b ofs Max p.

(** Having a (nonempty) permission implies that the block is valid.
  In other words, invalid blocks, not yet allocated, are all empty. *)
Axiom perm_valid_block:
  forall m b ofs k p, perm m b ofs k p -> valid_block m b.

(* Unused?
(** The [Mem.perm] predicate is decidable. *)
Axiom perm_dec:
  forall m b ofs k p, {perm m b ofs k p} + {~ perm m b ofs k p}.
*)

(** [range_perm m b lo hi p] holds iff the addresses [b, lo] to [b, hi-1]
  all have permission [p] of kind [k]. *)
Definition range_perm (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs k p.

Axiom range_perm_implies:
  forall m b lo hi k p1 p2,
  range_perm m b lo hi k p1 -> perm_order p1 p2 -> range_perm m b lo hi k p2.

(** An access to a memory quantity [chunk] at address [b, ofs] with
  permission [p] is valid in [m] if the accessed addresses all have
  current permission [p] and moreover the offset is properly aligned. *)
Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) Cur p
  /\ (align_chunk chunk | ofs).

Axiom valid_access_implies:
  forall m chunk b ofs p1 p2,
  valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2.

Axiom valid_access_valid_block:
  forall m chunk b ofs,
  valid_access m chunk b ofs Nonempty ->
  valid_block m b.

Axiom valid_access_perm:
  forall m chunk b ofs k p,
  valid_access m chunk b ofs p ->
  perm m b ofs k p.

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)

Parameter valid_pointer: forall (m: mem) (b: block) (ofs: Z), bool.

Axiom valid_pointer_nonempty_perm:
  forall m b ofs,
  valid_pointer m b ofs = true <-> perm m b ofs Cur Nonempty.
Axiom valid_pointer_valid_access:
  forall m b ofs,
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty.

(** C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)

Definition weak_valid_pointer (m: mem) (b: block) (ofs: Z) :=
  valid_pointer m b ofs || valid_pointer m b (ofs - 1).

Axiom weak_valid_pointer_spec:
  forall m b ofs,
  weak_valid_pointer m b ofs = true <->
    valid_pointer m b ofs = true \/ valid_pointer m b (ofs - 1) = true.
Axiom valid_pointer_implies:
  forall m b ofs,
  valid_pointer m b ofs = true -> weak_valid_pointer m b ofs = true.

(** * Properties of the memory operations *)

(** ** Properties of the initial memory state. *)

Axiom nextblock_empty: nextblock empty = 1%positive.
Axiom perm_empty: forall b ofs k p, ~perm empty b ofs k p.
Axiom valid_access_empty:
  forall chunk b ofs p, ~valid_access empty chunk b ofs p.

(** ** Properties of [load]. *)

(** A load succeeds if and only if the access is valid for reading *)
Axiom valid_access_load:
  forall m chunk b ofs,
  valid_access m chunk b ofs Readable ->
  exists v, load chunk m b ofs = Some v.
Axiom load_valid_access:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs Readable.

(** The value returned by [load] belongs to the type of the memory quantity
  accessed: [Vundef], [Vint] or [Vptr] for an integer quantity,
  [Vundef] or [Vfloat] for a float quantity. *)
Axiom load_type:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  wt v (type_of_chunk chunk).

(** For a small integer or float type, the value returned by [load]
  is invariant under the corresponding cast. *)
Axiom load_cast:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  match chunk with
  | Mint8signed => same_eval v (Val.sign_ext 8 v)
  | Mint8unsigned => same_eval v (Val.zero_ext 8 v)
  | Mint16signed => same_eval v (Val.sign_ext 16 v)
  | Mint16unsigned => same_eval v (Val.zero_ext 16 v)
  | Mint32 => same_eval v (Val.sign_ext 32 v)
  | _ => True
  end.

Axiom load_int8_signed_unsigned:
  forall m b ofs v1 v2,
  load Mint8signed m b ofs = Some v1 ->
  option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs) = Some v2 ->
  same_eval v1 v2.

Axiom load_int16_signed_unsigned:
  forall m b ofs v1 v2,
  load Mint16signed m b ofs = Some v1 ->
  option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs) = Some v2 ->
  same_eval v1 v2.

(** ** Properties of [loadbytes]. *)

(** [loadbytes] succeeds if and only if we have read permissions on the accessed
    memory area. *)

Axiom range_perm_loadbytes:
  forall m b ofs len,
  range_perm m b ofs (ofs + len) Cur Readable ->
  exists bytes, loadbytes m b ofs len = Some bytes.
Axiom loadbytes_range_perm:
  forall m b ofs len bytes,
  loadbytes m b ofs len = Some bytes ->
  range_perm m b ofs (ofs + len) Cur Readable.

(** If [loadbytes] succeeds, the corresponding [load] succeeds and
  returns a value that is determined by the
  bytes read by [loadbytes]. *)
Axiom loadbytes_load:
  forall chunk m b ofs bytes,
  loadbytes m b ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs = Some (decode_val chunk bytes).

(** Conversely, if [load] returns a value, the corresponding
  [loadbytes] succeeds and returns a list of bytes which decodes into the
  result of [load]. *)
Axiom load_loadbytes:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes
             /\ v = decode_val chunk bytes.

(** [loadbytes] returns a list of length [n] (the number of bytes read). *)
Axiom loadbytes_length:
  forall m b ofs n bytes,
  loadbytes m b ofs n = Some bytes ->
  length bytes = nat_of_Z n.

Axiom loadbytes_empty:
  forall m b ofs n,
  n <= 0 -> loadbytes m b ofs n = Some nil.

(** Composing or decomposing [loadbytes] operations at adjacent addresses. *)
Axiom loadbytes_concat:
  forall m b ofs n1 n2 bytes1 bytes2,
  loadbytes m b ofs n1 = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) = Some(bytes1 ++ bytes2).
Axiom loadbytes_split:
  forall m b ofs n1 n2 bytes,
  loadbytes m b ofs (n1 + n2) = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 = Some bytes1 
  /\ loadbytes m b (ofs + n1) n2 = Some bytes2
  /\ bytes = bytes1 ++ bytes2.

(** ** Properties of [store]. *)

(** [store] preserves block validity, permissions, access validity, and bounds.
  Moreover, a [store] succeeds if and only if the corresponding access
  is valid for writing. *)

Axiom nextblock_store:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  nextblock m2 = nextblock m1.
Axiom store_valid_block_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b', valid_block m1 b' -> valid_block m2 b'.
Axiom store_valid_block_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b', valid_block m2 b' -> valid_block m1 b'.

Axiom perm_store_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Axiom perm_store_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.

Axiom valid_access_store:
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  { m2: mem | store chunk m1 b ofs v = Some m2 }.
Axiom store_valid_access_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Axiom store_valid_access_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Axiom store_valid_access_3:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  valid_access m1 chunk b ofs Writable.

(** Load-store properties. *)

Axiom load_store_similar:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_expr_sym v chunk chunk' v'.

Axiom load_store_same:
  forall chunk m1 b ofs v m2,
    store chunk m1 b ofs v = Some m2 ->
    exists v1,
      load chunk m2 b ofs = Some v1 /\
      same_eval v1 (Val.load_result chunk v).

Axiom load_store_other:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs'.

(** Integrity of pointer values. *)

(* These two theorems do not hold anymore, because of the new memory model *)
(*Axiom load_store_pointer_overlap:
  forall chunk m1 b ofs v_b v_o m2 chunk' ofs' v v_sz v_msk,
  store chunk m1 b ofs (Eval (Vptr v_b v_sz v_msk v_o)) = Some m2 ->
  load chunk' m2 b ofs' = Some v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = Eval Vundef.
Axiom load_store_pointer_mismatch:
  forall chunk m1 b ofs v_b v_o m2 chunk' v v_sz v_msk,
  store chunk m1 b ofs (Eval (Vptr v_b v_sz v_msk v_o)) = Some m2 ->
  load chunk' m2 b ofs = Some v ->
  chunk <> Mint32 \/ chunk' <> Mint32 ->
  v = Eval Vundef.*)

Axiom load_pointer_store:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs' v_b v_o,
  load chunk' m2 b' ofs' = Some(Eval (Vptr v_b  v_o)) ->
  (chunk = Mint32 /\ v = Eval (Vptr v_b v_o) /\ chunk' = Mint32 /\ b' = b /\ ofs' = ofs)
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').

(** Load-store properties for [loadbytes]. *)

Axiom loadbytes_store_same:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  loadbytes m2 b ofs (size_chunk chunk) = Some (encode_val chunk v).
Axiom loadbytes_store_other:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' n,
  b' <> b \/ n <= 0 \/ ofs' + n <= ofs \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n.

(** [store] is insensitive to the signedness or the high bits of
  small integer quantities. *)

Axiom store_signed_unsigned_8:
  forall m b ofs v,
  store Mint8signed m b ofs v = store Mint8unsigned m b ofs v.
Axiom store_signed_unsigned_16:
  forall m b ofs v,
  store Mint16signed m b ofs v = store Mint16unsigned m b ofs v.



(* Parameter opt_mem_rel : (expr_sym -> expr_sym -> Prop) -> option mem -> option mem -> Prop. *)

(* Axiom store_int8_zero_ext: *)
(*   forall mr (wf: wf_mr mr) m b ofs n, *)
(*     opt_mem_rel mr *)
(*                 (store Mint8unsigned m b ofs (Eval (Vint (Int.zero_ext 8 n)))) *)
(*                 (store Mint8unsigned m b ofs (Eval (Vint n))). *)

(* Axiom store_int8_sign_ext: *)
(*    forall mr (wf: wf_mr mr) m b ofs n, *)
(*     opt_mem_rel mr *)
(*       (store Mint8signed m b ofs (Eval (Vint (Int.sign_ext 8 n)))) *)
(*       (store Mint8signed m b ofs (Eval (Vint n))). *)

(* Axiom store_int16_zero_ext: *)
(*   forall mr (wf: wf_mr mr) m b ofs n, *)
(*     opt_mem_rel mr *)
(*                 (store Mint16unsigned m b ofs (Eval (Vint (Int.zero_ext 16 n)))) *)
(*                 (store Mint16unsigned m b ofs (Eval (Vint n))). *)

(* Axiom store_int16_sign_ext: *)
(*   forall mr (wf: wf_mr mr) m b ofs n, *)
(*     opt_mem_rel mr *)
(*                 (store Mint16signed m b ofs (Eval (Vint (Int.sign_ext 16 n)))) *)
(*                 (store Mint16signed m b ofs (Eval (Vint n))). *)

(** ** Properties of [storebytes]. *)

(** [storebytes] preserves block validity, permissions, access validity, and bounds.
  Moreover, a [storebytes] succeeds if and only if we have write permissions
  on the addressed memory area. *)


Axiom range_perm_storebytes:
  forall m1 b ofs bytes,
  range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable ->
  (* check_bytes bytes = true -> *)
  { m2 : mem | storebytes m1 b ofs bytes = Some m2 }.
Axiom storebytes_range_perm:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable.
Axiom perm_storebytes_1:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Axiom perm_storebytes_2:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Axiom storebytes_valid_access_1:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Axiom storebytes_valid_access_2:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Axiom nextblock_storebytes:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  nextblock m2 = nextblock m1.
Axiom storebytes_valid_block_1:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b', valid_block m1 b' -> valid_block m2 b'.
Axiom storebytes_valid_block_2:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b', valid_block m2 b' -> valid_block m1 b'.

(** Connections between [store] and [storebytes]. *)

Axiom storebytes_store:
  forall m1 b ofs chunk v m2,
    storebytes m1 b ofs (encode_val chunk v) = Some m2 ->
    (align_chunk chunk | ofs) ->
    store chunk m1 b ofs v = Some m2.

Axiom store_storebytes:
  forall m1 b ofs chunk v m2,
  store chunk m1 b ofs v = Some m2 ->
  storebytes m1 b ofs (encode_val chunk v) = Some m2.

(** Load-store properties. *)

Axiom loadbytes_storebytes_same:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  loadbytes m2 b ofs (Z_of_nat (length bytes)) = Some bytes.
Axiom loadbytes_storebytes_other:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' len,
  len >= 0 ->
  b' <> b
  \/ ofs' + len <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len.
Axiom load_storebytes_other:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall chunk b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  load chunk m2 b' ofs' = load chunk m1 b' ofs'.

(** Composing or decomposing [storebytes] operations at adjacent addresses. *)

Axiom storebytes_concat:
  forall m b ofs bytes1 m1 bytes2 m2,
  storebytes m b ofs bytes1 = Some m1 ->
  storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2 ->
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2.
Axiom storebytes_split:
  forall m b ofs bytes1 bytes2 m2,
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2 ->
  exists m1,
     storebytes m b ofs bytes1 = Some m1
  /\ storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2.

(** ** Properties of [alloc]. *)

(** The identifier of the freshly allocated block is the next block
  of the initial memory state. *)

Axiom alloc_result:
  forall m1 lo hi m2 b bt, alloc m1 lo hi bt = Some (m2, b) ->
  b = nextblock m1.

(** Effect of [alloc] on block validity. *)

Axiom nextblock_alloc:
  forall m1 lo hi m2 b bt, alloc m1 lo hi bt = Some (m2, b) ->
  nextblock m2 = Psucc (nextblock m1).

Axiom valid_block_alloc:
  forall m1 lo hi m2 b bt, alloc m1 lo hi bt = Some (m2, b) ->
  forall b', valid_block m1 b' -> valid_block m2 b'.
Axiom fresh_block_alloc:
  forall m1 lo hi m2 b bt, alloc m1 lo hi bt = Some (m2, b) ->
  ~(valid_block m1 b).
Axiom valid_new_block:
  forall m1 lo hi m2 b bt, alloc m1 lo hi bt = Some (m2, b) ->
  valid_block m2 b.
Axiom valid_block_alloc_inv:
  forall m1 lo hi m2 b bt, alloc m1 lo hi bt = Some (m2, b) ->
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.

(** Effect of [alloc] on permissions. *)

Axiom perm_alloc_1:
  forall m1 lo hi m2 b bt, alloc m1 lo hi bt = Some (m2, b) ->
  forall b' ofs k p, perm m1 b' ofs k p -> perm m2 b' ofs k p.
Axiom perm_alloc_2:
  forall m1 lo hi m2 b bt, alloc m1 lo hi bt = Some (m2, b) ->
  forall ofs k, 0 <= ofs < hi -> perm m2 b ofs k Freeable.
Axiom perm_alloc_3:
  forall m1 lo hi m2 b bt, alloc m1 lo hi bt = Some (m2, b) ->
  forall ofs k p, perm m2 b ofs k p -> 0 <= ofs < hi.
Axiom perm_alloc_4:
  forall m1 lo hi m2 b bt, alloc m1 lo hi bt = Some (m2, b) ->
  forall b' ofs k p, perm m2 b' ofs k p -> b' <> b -> perm m1 b' ofs k p.
Axiom perm_alloc_inv:
  forall m1 lo hi m2 b bt, alloc m1 lo hi bt = Some (m2, b) ->
  forall b' ofs k p, 
  perm m2 b' ofs k p ->
  if eq_block b' b then 0 <= ofs < hi else perm m1 b' ofs k p.

(** Effect of [alloc] on access validity. *)

Axiom valid_access_alloc_other:
  forall m1 lo hi m2 b bt, alloc m1 lo hi bt = Some (m2, b) ->
  forall chunk b' ofs p,
  valid_access m1 chunk b' ofs p ->
  valid_access m2 chunk b' ofs p.
Axiom valid_access_alloc_same:
  forall m1 lo hi m2 b bt, alloc m1 lo hi  bt= Some (m2, b) ->
  forall chunk ofs,
    0 <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable.
Axiom valid_access_alloc_inv:
  forall m1 lo hi m2 b bt, alloc m1 lo hi bt = Some (m2, b) ->
  forall chunk b' ofs p,
  valid_access m2 chunk b' ofs p ->
  if eq_block b' b
  then 0 <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p.

(** Load-alloc properties. *)

Axiom load_alloc_unchanged:
  forall m1 lo hi m2 b bt, alloc m1 lo hi bt = Some (m2, b) ->
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs.
Axiom load_alloc_other:
  forall m1 lo hi m2 b bt, alloc m1 lo hi  bt= Some (m2, b) ->
  forall chunk b' ofs v,
  load chunk m1 b' ofs = Some v ->
  load chunk m2 b' ofs = Some v.

(* Axiom load_alloc_same: *)
(*   forall m1 lo hi m2 b, alloc m1 lo hi = Some (m2, b) -> *)
(*   forall chunk ofs v, *)
(*   load chunk m2 b ofs = Some v -> *)
(*   is_undef v. *)

(* Axiom load_alloc_same': *)
(*   forall m1 lo hi m2 b, alloc m1 lo hi = Some (m2, b) -> *)
(*   forall chunk ofs, *)
(*     0 <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) -> *)
(*   exists v,  *)
(*     load chunk m2 b ofs = Some v /\ *)
(*     is_undef v. *)

(** ** Properties of [free]. *)

(** [free] succeeds if and only if the correspond range of addresses
  has [Freeable] current permission. *)

Axiom range_perm_free:
  forall m1 b lo hi,
    range_perm m1 b lo hi Cur Freeable ->
    has_bounds m1 b lo hi = true ->
  { m2: mem | free m1 b lo hi = Some m2 }.
Axiom free_range_perm:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  range_perm m1 bf lo hi Cur Freeable.

(** Block validity is preserved by [free]. *)

Axiom nextblock_free:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  nextblock m2 = nextblock m1.
Axiom valid_block_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b, valid_block m1 b -> valid_block m2 b.
Axiom valid_block_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b, valid_block m2 b -> valid_block m1 b.

(** Effect of [free] on permissions. *)

Axiom perm_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs k p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs k p ->
  perm m2 b ofs k p.
Axiom perm_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall ofs k p, lo <= ofs < hi -> ~ perm m2 bf ofs k p.
Axiom perm_free_3:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs k p,
  perm m2 b ofs k p -> perm m1 b ofs k p.

(** Effect of [free] on access validity. *)

Axiom valid_access_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p -> 
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p.
Axiom valid_access_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p).
Axiom valid_access_free_inv_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs p,
  valid_access m2 chunk b ofs p ->
  valid_access m1 chunk b ofs p.
Axiom valid_access_free_inv_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk ofs p,
  valid_access m2 chunk bf ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.

(** Load-free properties *)

Axiom load_free:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs,
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs = load chunk m1 b ofs.

(** ** Properties of [drop_perm]. *)

Axiom nextblock_drop:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  nextblock m' = nextblock m.
Axiom drop_perm_valid_block_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b', valid_block m b' -> valid_block m' b'.
Axiom drop_perm_valid_block_2:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b', valid_block m' b' -> valid_block m b'.

Axiom range_perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  range_perm m b lo hi Cur Freeable.
Axiom range_perm_drop_2:
  forall m b lo hi p,
  range_perm m b lo hi Cur Freeable -> { m' | drop_perm m b lo hi p = Some m' }.

Axiom perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall ofs k, lo <= ofs < hi -> perm m' b ofs k p.
Axiom perm_drop_2:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall ofs k p', lo <= ofs < hi -> perm m' b ofs k p' -> perm_order p p'.
Axiom perm_drop_3:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs k p' -> perm m' b' ofs k p'.
Axiom perm_drop_4:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b' ofs k p', perm m' b' ofs k p' -> perm m b' ofs k p'.

Axiom load_drop:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall chunk b' ofs, 
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs = load chunk m b' ofs.

(** * Relating two memory states. *)

(*
(** ** Memory extensions *)

(**  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by relaxing the permissions of [m1] (for instance, allocating larger
  blocks) and replacing some of the [Vundef] values stored in [m1] by
  more defined values stored in [m2] at the same addresses. *)

Parameter extends: mem -> mem -> Prop.

Axiom extends_refl:
  forall m, extends m m.

Axiom load_extends:
  forall chunk m1 m2 b ofs v1,
  extends m1 m2 ->
  load chunk m1 b ofs = Some v1 ->
  exists v2, load chunk m2 b ofs = Some v2 /\ Val.lessdef v1 v2.

Axiom loadv_extends:
  forall chunk m1 m2 addr1 addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2.

Axiom loadbytes_extends:
  forall m1 m2 b ofs len bytes1,
  extends m1 m2 ->
  loadbytes m1 b ofs len = Some bytes1 ->
  exists bytes2, loadbytes m2 b ofs len = Some bytes2
              /\ list_forall2 (memval_lessdef) bytes1 bytes2.

Axiom store_within_extends:
  forall chunk m1 m2 b ofs v1 m1' v2,
  extends m1 m2 ->
  store chunk m1 b ofs v1 = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 b ofs v2 = Some m2'
  /\ extends m1' m2'.

Axiom store_outside_extends:
  forall chunk m1 m2 b ofs v m2',
  extends m1 m2 ->
  store chunk m2 b ofs v = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + size_chunk chunk -> False) ->
  extends m1 m2'.

(* Axiom storev_extends: *)
(*   forall chunk m1 m2 addr1 v1 m1' addr2 v2, *)
(*   extends m1 m2 -> *)
(*   storev chunk m1 addr1 v1 = Some m1' -> *)
(*   Val.lessdef addr1 addr2 -> *)
(*   Val.lessdef v1 v2 -> *)
(*   exists m2', *)
(*      storev chunk m2 addr2 v2 = Some m2' *)
(*   /\ extends m1' m2'. *)

Axiom storebytes_within_extends:
  forall m1 m2 b ofs bytes1 m1' bytes2,
  extends m1 m2 ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  list_forall2 (memval_lessdef) bytes1 bytes2 ->
  exists m2',
     storebytes m2 b ofs bytes2 = Some m2'
  /\ extends m1' m2'.

Axiom storebytes_outside_extends:
  forall m1 m2 b ofs bytes2 m2',
  extends m1 m2 ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + Z_of_nat (length bytes2) -> False) ->
  extends m1 m2'.

Axiom alloc_extends:
  forall m1 m2 lo hi b m1'
    (Hmwf: forall b i, Ple (nextblock m1) b -> p b i = None),
  extends m1 m2 ->
  alloc m1 lo hi = (m1', b) ->
  exists m2',
     alloc m2 lo hi = (m2', b)
  /\ extends m1' m2'.

(* Axiom free_left_extends: *)
(*   forall m1 m2 b lo hi m1', *)
(*   extends m1 m2 -> *)
(*   free m1 b lo hi = Some m1' -> *)
(*   extends m1' m2. *)

(* Axiom free_right_extends: *)
(*   forall m1 m2 b lo hi m2', *)
(*   extends m1 m2 -> *)
(*   free m2 b lo hi = Some m2' -> *)
(*   (forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) -> *)
(*   extends m1 m2'. *)

(* Axiom free_parallel_extends: *)
(*   forall m1 m2 b lo hi m1', *)
(*   extends m1 m2 -> *)
(*   free m1 b lo hi = Some m1' -> *)
(*   exists m2', *)
(*      free m2 b lo hi = Some m2' *)
(*   /\ extends m1' m2'. *)

(* Axiom valid_block_extends: *)
(*   forall m1 m2 b, *)
(*   extends m1 m2 -> *)
(*   (valid_block m1 b <-> valid_block m2 b). *)
(* Axiom perm_extends: *)
(*   forall m1 m2 b ofs k p, *)
(*   extends m m1 m2 -> perm m1 b ofs k p -> perm m2 b ofs k p. *)
(* Axiom valid_access_extends: *)
(*   forall m1 m2 chunk b ofs p, *)
(*   extends m m1 m2 -> valid_access m1 chunk b ofs p -> valid_access m2 chunk b ofs p. *)
(* Axiom valid_pointer_extends: *)
(*   forall m1 m2 b ofs, *)
(*   extends m1 m2 -> valid_pointer m1 b ofs = true -> valid_pointer m2 b ofs = true. *)
(* Axiom weak_valid_pointer_extends: *)
(*   forall m1 m2 b ofs, *)
(*   extends m1 m2 -> *)
(*   weak_valid_pointer m1 b ofs = true -> weak_valid_pointer m2 b ofs = true. *)
 *)

(** * Memory injections *)

(** A memory injection [f] is a function from addresses to either [None] *)
(*   or [Some] of an address and an offset.  It defines a correspondence *)
(*   between the blocks of two memory states [m1] and [m2]: *)
(* - if [f b = None], the block [b] of [m1] has no equivalent in [m2]; *)
(* - if [f b = Some(b', ofs)], the block [b] of [m2] corresponds to *)
(*   a sub-block at offset [ofs] of the block [b'] in [m2]. *)

(* A memory injection [f] defines a relation [val_inject] between values *)
(* that is the identity for integer and float values, and relocates pointer  *)
(* values as prescribed by [f].  (See module [Values].) *)

(* Likewise, a memory injection [f] defines a relation between memory states  *)
(* that we now axiomatize. *)

Parameter inject: bool -> (meminj -> expr_sym -> expr_sym -> Prop) -> meminj -> mem -> mem -> Prop.

Axiom valid_block_inject_1:
  forall sm p f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject sm p f m1 m2 ->
  valid_block m1 b1.

Axiom valid_block_inject_2:
  forall sm p f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject sm p f m1 m2 ->
  valid_block m2 b2.

Axiom perm_inject:
  forall sm m f m1 m2 b1 b2 delta ofs k p,
  f b1 = Some(b2, delta) ->
  inject sm m f m1 m2 ->
  perm m1 b1 ofs k p -> perm m2 b2 (ofs + delta) k p.

Axiom valid_access_inject:
  forall sm m  f m1 m2 chunk b1 ofs b2 delta p,
  f b1 = Some(b2, delta) ->
  inject sm m f m1 m2 ->
  valid_access m1 chunk b1 ofs p ->
  valid_access m2 chunk b2 (ofs + delta) p.

Axiom valid_pointer_inject:
  forall sm p f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject sm p f m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true.

Axiom weak_valid_pointer_inject:
  forall sm  p f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject sm p f m1 m2 ->
  weak_valid_pointer m1 b1 ofs = true ->
  weak_valid_pointer m2 b2 (ofs + delta) = true.

Axiom address_inject:
  forall sm  m f m1 m2 b1 ofs1 b2 delta p,
  inject sm m f m1 m2 ->
  perm m1 b1 (Int.unsigned ofs1) Cur p ->
  f b1 = Some (b2, delta) ->
  Int.unsigned (Int.add ofs1 (Int.repr delta)) = Int.unsigned ofs1 + delta.

Axiom valid_pointer_inject_no_overflow:
  forall sm  p f m1 m2 b ofs b' delta,
  inject sm p f m1 m2 ->
  valid_pointer m1 b (Int.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Int.unsigned ofs + Int.unsigned (Int.repr delta) <= Int.max_unsigned.

Axiom weak_valid_pointer_inject_no_overflow:
  forall sm  p f m1 m2 b ofs b' delta,
  inject sm p f m1 m2 ->
  weak_valid_pointer m1 b (Int.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Int.unsigned ofs + Int.unsigned (Int.repr delta) <= Int.max_unsigned.

Axiom valid_pointer_inject_val:
  forall sm  p (wf: wf_inj p) f m1 m2 b ofs b' ofs',
  inject sm p f m1 m2 ->
  valid_pointer m1 b (Int.unsigned ofs) = true ->
  p f (Eval (Vptr b ofs)) (Eval (Vptr b' ofs')) ->
  valid_pointer m2 b' (Int.unsigned ofs') = true.

Axiom weak_valid_pointer_inject_val:
  forall sm  p (wf: wf_inj p) f m1 m2 b ofs b' ofs',
  inject sm p f m1 m2 ->
  weak_valid_pointer m1 b (Int.unsigned ofs) = true ->
  p f (Eval (Vptr b ofs)) (Eval (Vptr b' ofs')) ->
  weak_valid_pointer m2 b' (Int.unsigned ofs') = true.

Axiom inject_no_overlap:
  forall sm  p f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject sm p f m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Max Nonempty ->
  perm m1 b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

Axiom different_pointers_inject:
  forall sm  p f m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  inject sm p f m m' ->
  b1 <> b2 ->
  valid_pointer m b1 (Int.unsigned ofs1) = true ->
  valid_pointer m b2 (Int.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Int.unsigned (Int.add ofs1 (Int.repr delta1)) <>
  Int.unsigned (Int.add ofs2 (Int.repr delta2)).

Variable all_blocks_injected : meminj -> mem -> Prop.

Axiom load_inject:
  forall sm  m (wf: wf_inj m) f m1 m2 chunk b1 ofs b2 delta v1,
    inject sm m f m1 m2 ->

  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ m f v1 v2.

Axiom loadv_inject:
  forall sm  m (wf: wf_inj m ) f m1 m2 chunk a1 a2 v1
         (ABI: all_blocks_injected f m1),
  inject sm m f m1 m2 ->

  loadv chunk m1 a1 = Some v1 ->
  m f a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ m f v1 v2.

Axiom loadbytes_inject:
  forall sm  m f m1 m2 b1 ofs len b2 delta bytes1,
  inject sm m f m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject m f) bytes1 bytes2.

Axiom store_mapped_inject:
  forall sm  m (wf: wf_inj m) f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
     (* (chunk = Many32 \/ chunk = Many64 -> get_type v1 = get_type v2) -> *)
  inject sm m f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  m f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ inject sm m f n1 n2.

Axiom store_unmapped_inject:
  forall sm  m f chunk m1 b1 ofs v1 n1 m2,
  inject sm m f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  inject sm m f n1 m2.

Axiom store_outside_inject:
  forall sm  m f m1 m2 chunk b ofs v m2',
  inject sm m f m1 m2 ->
  (forall  b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v = Some m2' ->
  inject sm m f m1 m2'.

Axiom storev_mapped_inject:
  forall sm  m (wf: wf_inj m) f chunk m1 a1 v1 n1 m2 a2 v2         
    (ABI: all_blocks_injected f m1),
    (* (chunk = Many32 \/ chunk = Many64 -> get_type v1 = get_type v2) -> *)
  inject sm m f m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  m f a1 a2 ->
  m f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ inject sm m f n1 n2.

Axiom storebytes_mapped_inject:
  forall sm  m f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  inject sm m f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject m f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ inject sm m f n1 n2.

Axiom storebytes_unmapped_inject:
  forall sm  m f m1 b1 ofs bytes1 n1 m2,
  inject sm m f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  inject sm m f n1 m2.

Axiom storebytes_outside_inject:
  forall sm  m f m1 m2 b ofs bytes2 m2',
  inject sm m f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z_of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  inject sm m f m1 m2'.

(* Axiom alloc_right_inject: *)
(*   forall m f m1 m2 lo hi b2 m2', *)
(*   inject sm m f m1 m2 -> *)
(*   alloc m2 lo hi = (m2', b2) -> *)
(*   inject sm m f m1 m2'. *)

Axiom alloc_left_unmapped_inject:
  forall sm  m (wf: wf_inj m) f m1 m2 lo hi m1' b1 bt,
  inject sm m f m1 m2 ->
  alloc m1 lo hi  bt= Some (m1', b1) ->
  exists f',
     inject sm m f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b).

Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  (two_power_nat (alignment_of_size size) | delta).
  
Parameter block_undefs : Z -> Z -> Z -> mem -> block -> Prop.

Axiom alloc_parallel_inject:
  forall sm  m (wf: wf_inj m) f m1 m2 lo1 hi1 m1' b1  (* lo2 hi2 *),
    lo1 <= hi1 ->
forall bt,
  inject sm m f m1 m2 ->
  alloc m1 lo1 hi1  bt= Some (m1', b1) ->
  hi1 >= 0 ->
  sm = true ->
  exists f', exists m2', exists b2,
  alloc m2 lo1 hi1  bt= Some (m2', b2)
  /\ inject sm m f' m1' m2'
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, 0)
  /\ (forall b, b <> b1 -> f' b = f b).

Axiom drop_outside_inject:
  forall sm  m f m1 m2 b lo hi p m2',
  inject sm m f m1 m2 ->
  drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  inject sm m f m1 m2'.

(* (** Memory states that inject sm into themselves. *) *)

Definition flat_inj (thr: block) : meminj :=
  fun (b: block) => if plt b thr then Some(b, 0) else None.

Parameter inject_neutral: forall (sm:bool)  (ei: meminj -> expr_sym -> expr_sym -> Prop) (thr: block) (m: mem), Prop.

Axiom neutral_inject:
  forall sm  ei m,
    inject_neutral sm ei (nextblock m) m ->
    inject sm ei (flat_inj (nextblock m)) m m.

Axiom empty_inject_neutral:
  forall sm  ei thr, inject_neutral sm ei thr empty.

Axiom alloc_inject_neutral:
  forall sm  ei (wf: wf_inj ei) thr m lo hi b m' bt,
  alloc m lo hi  bt= Some (m', b) ->
  lo <= 0 ->
  inject_neutral sm ei thr m ->
  Plt (nextblock m) thr ->
  inject_neutral sm ei thr m'.

Axiom store_inject_neutral:
  forall sm  ei (WF: wf_inj ei) chunk m b ofs v m' thr ,
  store chunk m b ofs v = Some m' ->
  inject_neutral sm ei thr m ->
  Plt b thr ->
  ei (flat_inj thr) v v ->
  inject_neutral sm ei thr m'.

Axiom drop_inject_neutral:
  forall sm  ei m b lo hi p m' thr,
  drop_perm m b lo hi p = Some m' ->
  inject_neutral sm ei thr m ->
  Plt b thr ->
  inject_neutral sm ei thr m'.

End MEM.
