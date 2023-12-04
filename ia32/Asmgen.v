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

(** Translation from Mach to IA32 Asm. *)

Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Memdata.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Asm.

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

(** The code generation functions take advantage of several characteristics of the [Mach] code generated by earlier passes of the compiler:
- Argument and result registers are of the correct type.
- For two-address instructions, the result and the first argument
  are in the same register.  (True by construction in [RTLgen], and preserved by [Reload].)
- The top of the floating-point stack ([ST0], a.k.a. [FP0]) can only
  appear in [mov] instructions, but never in arithmetic instructions.

All these properties are true by construction, but it is painful to track them statically.  Instead, we recheck them during code generation and fail if they do not hold.
*)

(** Extracting integer or float registers. *)

Definition ireg_of (r: mreg) : res ireg :=
  match preg_of r with IR mr => OK mr | _ => Error(msg "Asmgen.ireg_of") end.

Definition freg_of (r: mreg) : res freg :=
  match preg_of r with FR mr => OK mr | _ => Error(msg "Asmgen.freg_of") end.

(** Smart constructors for various operations. *)

Definition mk_mov (rd rs: preg) (k: code) : res code :=
  match rd, rs with
  | IR rd, IR rs => OK (Pmov_rr rd rs :: k)
  | FR rd, FR rs => OK (Pmovsd_ff rd rs :: k)
  | _, _ => Error(msg "Asmgen.mk_mov")
  end.

Definition mk_shrximm (n: int) (k: code) : res code :=
  let p := Int.sub (Int.shl Int.one n) Int.one in
  OK (Ptest_rr EAX EAX ::
      Plea ECX (Addrmode (Some EAX) None (inl _ p)) ::
      Pcmov Cond_l EAX ECX ::
      Psar_ri EAX n :: k).

Definition low_ireg (r: ireg) : bool :=
  match r with
  | EAX | EBX | ECX | EDX => true
  | ESI | EDI | EBP | ESP => false
  end.

Definition mk_intconv (mk: ireg -> ireg -> instruction) (rd rs: ireg) (k: code) :=
  if low_ireg rs then
    OK (mk rd rs :: k)
  else
    OK (Pmov_rr EAX rs :: mk rd EAX :: k).

Definition addressing_mentions (addr: addrmode) (r: ireg) : bool :=
  match addr with Addrmode base displ const =>
      match base with Some r' => ireg_eq r r' | None => false end
   || match displ with Some(r', sc) => ireg_eq r r' | None => false end
  end.

Definition mk_smallstore (sto: addrmode -> ireg ->instruction) 
                         (addr: addrmode) (rs: ireg) (k: code) :=
  if low_ireg rs then
    OK (sto addr rs :: k)
  else if addressing_mentions addr EAX then
    OK (Plea ECX addr :: Pmov_rr EAX rs ::
        sto (Addrmode (Some ECX) None (inl _ Int.zero)) EAX :: k)
  else
    OK (Pmov_rr EAX rs :: sto addr EAX :: k).

(** Accessing slots in the stack frame. *)

Definition loadind (base: ireg) (ofs: int) (ty: typ) (dst: mreg) (k: code) :=
  match ty, preg_of dst with
  | Tint, IR r => OK (Pmov_rm r (Addrmode (Some base) None (inl _ ofs)) :: k)
  | Tsingle, FR r => OK (Pmovss_fm r (Addrmode (Some base) None (inl _ ofs)) :: k)
  | Tsingle, ST0  => OK (Pflds_m (Addrmode (Some base) None (inl _ ofs)) :: k)
  | Tfloat, FR r => OK (Pmovsd_fm r (Addrmode (Some base) None (inl _ ofs)) :: k)
  | Tfloat, ST0  => OK (Pfldl_m (Addrmode (Some base) None (inl _ ofs)) :: k)
  | Tany32, IR r => OK (Pmov_rm_a r (Addrmode (Some base) None (inl _ ofs)) :: k)
  | Tany64, FR r => OK (Pmovsd_fm_a r (Addrmode (Some base) None (inl _ ofs)) :: k)
  | _, _ => Error (msg "Asmgen.loadind")
  end.

Definition storeind (src: mreg) (base: ireg) (ofs: int) (ty: typ) (k: code) :=
  match ty, preg_of src with
  | Tint, IR r => OK (Pmov_mr (Addrmode (Some base) None (inl _ ofs)) r :: k)
  | Tsingle, FR r => OK (Pmovss_mf (Addrmode (Some base) None (inl _ ofs)) r :: k)
  | Tsingle, ST0 => OK (Pfstps_m (Addrmode (Some base) None (inl _ ofs)) :: k)
  | Tfloat, FR r => OK (Pmovsd_mf (Addrmode (Some base) None (inl _ ofs)) r :: k)
  | Tfloat, ST0  => OK (Pfstpl_m (Addrmode (Some base) None (inl _ ofs)) :: k)
  | Tany32, IR r => OK (Pmov_mr_a (Addrmode (Some base) None (inl _ ofs)) r :: k)
  | Tany64, FR r => OK (Pmovsd_mf_a (Addrmode (Some base) None (inl _ ofs)) r :: k)
  | _, _ => Error (msg "Asmgen.storeind")
  end.

(** Translation of addressing modes *)

Definition transl_addressing (a: addressing) (args: list mreg): res addrmode :=
  match a, args with
  | Aindexed n, a1 :: nil =>
      do r1 <- ireg_of a1; OK(Addrmode (Some r1) None (inl _ n))
  | Aindexed2 n, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK(Addrmode (Some r1) (Some(r2, Int.one)) (inl _ n))
  | Ascaled sc n, a1 :: nil =>
      do r1 <- ireg_of a1; OK(Addrmode None (Some(r1, sc)) (inl _ n))
  | Aindexed2scaled sc n, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK(Addrmode (Some r1) (Some(r2, sc)) (inl _ n))
  | Aglobal id ofs, nil =>
      OK(Addrmode None None (inr _ (id, ofs)))
  | Abased id ofs, a1 :: nil =>
      do r1 <- ireg_of a1; OK(Addrmode (Some r1) None (inr _ (id, ofs)))
  | Abasedscaled sc id ofs, a1 :: nil =>
      do r1 <- ireg_of a1; OK(Addrmode None (Some(r1, sc)) (inr _ (id, ofs)))
  | Ainstack n, nil =>
      OK(Addrmode (Some ESP) None (inl _ n))
  | _, _ =>
      Error(msg "Asmgen.transl_addressing")
  end.

(** Floating-point comparison.  We swap the operands in some cases
   to simplify the handling of the unordered case. *)

Definition floatcomp (cmp: comparison) (r1 r2: freg) : instruction :=
  match cmp with
  | Clt | Cle => Pcomisd_ff r2 r1
  | Ceq | Cne | Cgt | Cge => Pcomisd_ff r1 r2
  end.

Definition floatcomp32 (cmp: comparison) (r1 r2: freg) : instruction :=
  match cmp with
  | Clt | Cle => Pcomiss_ff r2 r1
  | Ceq | Cne | Cgt | Cge => Pcomiss_ff r1 r2
  end.

(** Translation of a condition.  Prepends to [k] the instructions
  that evaluate the condition and leave its boolean result in bits
  of the condition register. *)

Definition transl_cond
              (cond: condition) (args: list mreg) (k: code) : res code :=
  match cond, args with
  | Ccomp c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2; OK (Pcmp_rr r1 r2 :: k)
  | Ccompu c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2; OK (Pcmp_rr r1 r2 :: k)
  | Ccompimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if Int.eq_dec n Int.zero then Ptest_rr r1 r1 :: k else Pcmp_ri r1 n :: k)
  | Ccompuimm c n, a1 :: nil =>
      do r1 <- ireg_of a1; OK (Pcmp_ri r1 n :: k)
  | Ccompf cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2; OK (floatcomp cmp r1 r2 :: k)
  | Cnotcompf cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2; OK (floatcomp cmp r1 r2 :: k)
  | Ccompfs cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2; OK (floatcomp32 cmp r1 r2 :: k)
  | Cnotcompfs cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2; OK (floatcomp32 cmp r1 r2 :: k)
  | Cmaskzero n, a1 :: nil =>
      do r1 <- ireg_of a1; OK (Ptest_ri r1 n :: k)
  | Cmasknotzero n, a1 :: nil =>
      do r1 <- ireg_of a1; OK (Ptest_ri r1 n :: k)
  | _, _ =>
     Error(msg "Asmgen.transl_cond")
  end.

(** What processor condition to test for a given Mach condition. *)

Definition testcond_for_signed_comparison (cmp: comparison) :=
  match cmp with
  | Ceq => Cond_e
  | Cne => Cond_ne
  | Clt => Cond_l
  | Cle => Cond_le
  | Cgt => Cond_g
  | Cge => Cond_ge
  end.

Definition testcond_for_unsigned_comparison (cmp: comparison) :=
  match cmp with
  | Ceq => Cond_e
  | Cne => Cond_ne
  | Clt => Cond_b
  | Cle => Cond_be
  | Cgt => Cond_a
  | Cge => Cond_ae
  end.

Inductive extcond: Type :=
  | Cond_base (c: testcond)
  | Cond_or (c1 c2: testcond)
  | Cond_and (c1 c2: testcond).

Definition testcond_for_condition (cond: condition) : extcond :=
  match cond with
  | Ccomp c => Cond_base(testcond_for_signed_comparison c)
  | Ccompu c => Cond_base(testcond_for_unsigned_comparison c)
  | Ccompimm c n => Cond_base(testcond_for_signed_comparison c)
  | Ccompuimm c n => Cond_base(testcond_for_unsigned_comparison c)
  | Ccompf c | Ccompfs c =>
      match c with
      | Ceq => Cond_and Cond_np Cond_e
      | Cne => Cond_or Cond_p Cond_ne
      | Clt => Cond_base Cond_a
      | Cle => Cond_base Cond_ae
      | Cgt => Cond_base Cond_a
      | Cge => Cond_base Cond_ae
      end
  | Cnotcompf c | Cnotcompfs c =>
      match c with
      | Ceq => Cond_or Cond_p Cond_ne
      | Cne => Cond_and Cond_np Cond_e
      | Clt => Cond_base Cond_be
      | Cle => Cond_base Cond_b
      | Cgt => Cond_base Cond_be
      | Cge => Cond_base Cond_b
      end
  | Cmaskzero n => Cond_base Cond_e
  | Cmasknotzero n => Cond_base Cond_ne
  end.

(** Acting upon extended conditions. *)

Definition mk_setcc_base (cond: extcond) (rd: ireg) (k: code) :=
  match cond with
  | Cond_base c =>
      Psetcc c rd :: k
  | Cond_and c1 c2 =>
      if ireg_eq rd EAX
      then Psetcc c1 EAX :: Psetcc c2 ECX :: Pand_rr EAX ECX :: k
      else Psetcc c1 EAX :: Psetcc c2 rd  :: Pand_rr rd EAX :: k
  | Cond_or c1 c2 => 
      if ireg_eq rd EAX
      then Psetcc c1 EAX :: Psetcc c2 ECX :: Por_rr EAX ECX :: k
      else Psetcc c1 EAX :: Psetcc c2 rd  :: Por_rr rd EAX :: k
  end.

Definition mk_setcc (cond: extcond) (rd: ireg) (k: code) :=
  if low_ireg rd
  then mk_setcc_base cond rd k
  else mk_setcc_base cond EAX (Pmov_rr rd EAX :: k).

Definition mk_jcc (cond: extcond) (lbl: label) (k: code) :=
  match cond with
  | Cond_base c => Pjcc c lbl :: k
  | Cond_and c1 c2 => Pjcc2 c1 c2 lbl :: k
  | Cond_or c1 c2 => PjccOr c1 c2 lbl :: k
  end.

(** Translation of the arithmetic operation [r <- op(args)].
  The corresponding instructions are prepended to [k]. *)

Definition transl_op
             (op: operation) (args: list mreg) (res: mreg) (k: code) : Errors.res code :=
  match op, args with
  | Omove, a1 :: nil =>
      mk_mov (preg_of res) (preg_of a1) k
  | Ointconst n, nil =>
      do r <- ireg_of res;
      OK ((if Int.eq_dec n Int.zero then Pxor_r r else Pmov_ri r n) :: k)
  | Ofloatconst f, nil =>
      do r <- freg_of res; 
      OK ((if Float.eq_dec f Float.zero then Pxorpd_f r else Pmovsd_fi r f) :: k)
  | Osingleconst f, nil =>
      do r <- freg_of res; 
      OK ((if Float32.eq_dec f Float32.zero then Pxorps_f r else Pmovss_fi r f) :: k)
  | Oindirectsymbol id, nil =>
      do r <- ireg_of res;
      OK (Pmov_ra r id :: k)
  | Ocast8signed, a1 :: nil =>
      do r1 <- ireg_of a1; do r <- ireg_of res; mk_intconv Pmovsb_rr r r1 k
  | Ocast8unsigned, a1 :: nil =>
      do r1 <- ireg_of a1; do r <- ireg_of res; mk_intconv Pmovzb_rr r r1 k
  | Ocast16signed, a1 :: nil =>
      do r1 <- ireg_of a1; do r <- ireg_of res; mk_intconv Pmovsw_rr r r1 k
  | Ocast16unsigned, a1 :: nil =>
      do r1 <- ireg_of a1; do r <- ireg_of res; mk_intconv Pmovzw_rr r r1 k
  | Oneg, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pneg r :: k)
  | Osub, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Psub_rr r r2 :: k)
  | Omul, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Pimul_rr r r2 :: k)
  | Omulimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pimul_ri r n :: k)
  | Omulhs, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq res DX);
      do r2 <- ireg_of a2; OK (Pimul_r r2 :: k)
  | Omulhu, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq res DX);
      do r2 <- ireg_of a2; OK (Pmul_r r2 :: k)
  | Odiv, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq a2 CX);
      assertion (mreg_eq res AX);
      OK(Pidiv ECX :: k)
  | Odivu, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq a2 CX);
      assertion (mreg_eq res AX);
      OK(Pdiv ECX :: k)
  | Omod, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq a2 CX);
      assertion (mreg_eq res DX);
      OK(Pidiv ECX :: k)
  | Omodu, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq a2 CX);
      assertion (mreg_eq res DX);
      OK(Pdiv ECX :: k)
  | Oand, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Pand_rr r r2 :: k)
  | Oandimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pand_ri r n :: k)
  | Oor, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Por_rr r r2 :: k)
  | Oorimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Por_ri r n :: k)
  | Oxor, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Pxor_rr r r2 :: k)
  | Oxorimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pxor_ri r n :: k)
  | Onot, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pnot r :: k)
  | Oshl, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      assertion (mreg_eq a2 CX);
      do r <- ireg_of res; OK (Psal_rcl r :: k)
  | Oshlimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Psal_ri r n :: k)
  | Oshr, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      assertion (mreg_eq a2 CX);
      do r <- ireg_of res; OK (Psar_rcl r :: k)
  | Oshrimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Psar_ri r n :: k)
  | Oshru, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      assertion (mreg_eq a2 CX);
      do r <- ireg_of res; OK (Pshr_rcl r :: k)
  | Oshruimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pshr_ri r n :: k)
  | Oshrximm n, a1 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq res AX);
      mk_shrximm n k
  | Ororimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pror_ri r n :: k)
  | Oshldimm n, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Pshld_ri r r2 n :: k)
  | Olea addr, _ =>
      do am <- transl_addressing addr args; do r <- ireg_of res;
      OK (Plea r am :: k)
  | Onegf, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; OK (Pnegd r :: k)
  | Oabsf, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; OK (Pabsd r :: k)
  | Oaddf, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Paddd_ff r r2 :: k)
  | Osubf, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Psubd_ff r r2 :: k)
  | Omulf, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Pmuld_ff r r2 :: k)
  | Odivf, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Pdivd_ff r r2 :: k)
  | Onegfs, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; OK (Pnegs r :: k)
  | Oabsfs, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; OK (Pabss r :: k)
  | Oaddfs, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Padds_ff r r2 :: k)
  | Osubfs, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Psubs_ff r r2 :: k)
  | Omulfs, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Pmuls_ff r r2 :: k)
  | Odivfs, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Pdivs_ff r r2 :: k)
  | Osingleoffloat, a1 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1; OK (Pcvtsd2ss_ff r r1 :: k)
  | Ofloatofsingle, a1 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1; OK (Pcvtss2sd_ff r r1 :: k)
  | Ointoffloat, a1 :: nil =>
      do r <- ireg_of res; do r1 <- freg_of a1; OK (Pcvttsd2si_rf r r1 :: k)
  | Ofloatofint, a1 :: nil =>
      do r <- freg_of res; do r1 <- ireg_of a1; OK (Pcvtsi2sd_fr r r1 :: k)
  | Ointofsingle, a1 :: nil =>
      do r <- ireg_of res; do r1 <- freg_of a1; OK (Pcvttss2si_rf r r1 :: k)
  | Osingleofint, a1 :: nil =>
      do r <- freg_of res; do r1 <- ireg_of a1; OK (Pcvtsi2ss_fr r r1 :: k)
  | Ocmp c, args =>
      do r <- ireg_of res;
      transl_cond c args (mk_setcc (testcond_for_condition c) r k)
  | _, _ =>
      Error(msg "Asmgen.transl_op")
  end.

(** Translation of memory loads and stores *)

Definition transl_load (chunk: memory_chunk)
                       (addr: addressing) (args: list mreg) (dest: mreg)
                       (k: code) : res code :=
  do am <- transl_addressing addr args;
  match chunk with
  | Mint8unsigned =>
      do r <- ireg_of dest; OK(Pmovzb_rm r am :: k)
  | Mint8signed =>
      do r <- ireg_of dest; OK(Pmovsb_rm r am :: k)
  | Mint16unsigned =>
      do r <- ireg_of dest; OK(Pmovzw_rm r am :: k)
  | Mint16signed =>
      do r <- ireg_of dest; OK(Pmovsw_rm r am :: k)
  | Mint32 =>
      do r <- ireg_of dest; OK(Pmov_rm r am :: k)
  | Mfloat32 =>
      do r <- freg_of dest; OK(Pmovss_fm r am :: k)
  | Mfloat64 =>
      do r <- freg_of dest; OK(Pmovsd_fm r am :: k)
  | _ =>
      Error (msg "Asmgen.transl_load")
  end.

Definition transl_store (chunk: memory_chunk)
                        (addr: addressing) (args: list mreg) (src: mreg)
                        (k: code) : res code :=
  do am <- transl_addressing addr args;
  match chunk with
  | Mint8unsigned | Mint8signed =>
      do r <- ireg_of src; mk_smallstore Pmovb_mr am r k
  | Mint16unsigned | Mint16signed =>
      do r <- ireg_of src; OK(Pmovw_mr am r :: k)
  | Mint32 =>
      do r <- ireg_of src; OK(Pmov_mr am r :: k)
  | Mfloat32 =>
      do r <- freg_of src; OK(Pmovss_mf am r :: k)
  | Mfloat64 =>
      do r <- freg_of src; OK(Pmovsd_mf am r :: k)
  | _ =>
      Error (msg "Asmgen.transl_store")
  end.

(** Translation of arguments to annotations *)

Definition transl_annot_param (p: Mach.annot_param) : Asm.annot_param :=
  match p with
  | Mach.APreg r => APreg (preg_of r)
  | Mach.APstack chunk ofs => APstack chunk ofs
  end.

(** Translation of a Mach instruction. *)

Definition transl_instr (f: Mach.function) (i: Mach.instruction)
                        (edx_is_parent: bool) (k: code) :=
  match i with
  | Mgetstack ofs ty dst =>
      loadind ESP ofs ty dst k
  | Msetstack src ofs ty =>
      storeind src ESP ofs ty k
  | Mgetparam ofs ty dst =>
      if edx_is_parent then
        loadind EDX ofs ty dst k
      else
        (do k1 <- loadind EDX ofs ty dst k;
         loadind ESP f.(fn_link_ofs) Tint DX k1)
  | Mop op args res =>
      transl_op op args res k
  | Mload chunk addr args dst =>
      transl_load chunk addr args dst k
  | Mstore chunk addr args src =>
      transl_store chunk addr args src k
  | Mcall sig (inl reg) =>
      do r <- ireg_of reg; OK (Pcall_r r sig :: k)
  | Mcall sig (inr symb) =>
      OK (Pcall_s symb sig :: k)
  | Mtailcall sig (inl reg) =>
      do r <- ireg_of reg; 
      OK (Pfreeframe f.(Mach.fn_stacksize) f.(fn_retaddr_ofs) f.(fn_link_ofs) :: 
          Pjmp_r r sig :: k)
  | Mtailcall sig (inr symb) =>
      OK (Pfreeframe f.(Mach.fn_stacksize) f.(fn_retaddr_ofs) f.(fn_link_ofs) :: 
          Pjmp_s symb sig :: k)
  | Mlabel lbl =>
      OK(Plabel lbl :: k)
  | Mgoto lbl =>
      OK(Pjmp_l lbl :: k)
  | Mcond cond args lbl =>
    transl_cond cond args (mk_jcc (testcond_for_condition cond) lbl k)
  | Mjumptable arg tbl =>
    do r <- ireg_of arg; OK (Pjmptbl r tbl :: k)
  | Mreturn =>
    OK (Pfreeframe f.(Mach.fn_stacksize) f.(fn_retaddr_ofs) f.(fn_link_ofs)
                                                           :: Pret :: k)
  | Mbuiltin ef args res =>
    OK (Pbuiltin ef (List.map preg_of args) (List.map preg_of res) :: k)
       (* | Mannot ef args => *)
       (*     OK (Pannot ef (map transl_annot_param args) :: k) *)
  end.

(** Translation of a code sequence *)

Definition it1_is_parent (before: bool) (i: Mach.instruction) : bool :=
  match i with
  | Msetstack src ofs ty => before
  | Mgetparam ofs ty dst => negb (mreg_eq dst DX)
  | _ => false
  end.

(** This is the naive definition that we no longer use because it
  is not tail-recursive.  It is kept as specification. *)

Fixpoint transl_code (f: Mach.function) (il: list Mach.instruction) (it1p: bool) :=
  match il with
  | nil => OK nil
  | i1 :: il' =>
      do k <- transl_code f il' (it1_is_parent it1p i1);
      transl_instr f i1 it1p k
  end.

(** This is an equivalent definition in continuation-passing style
  that runs in constant stack space. *)

Fixpoint transl_code_rec (f: Mach.function) (il: list Mach.instruction)
                         (it1p: bool) (k: code -> res code) :=
  match il with
  | nil => k nil
  | i1 :: il' =>
      transl_code_rec f il' (it1_is_parent it1p i1)
        (fun c1 => do c2 <- transl_instr f i1 it1p c1; k c2)
  end.

Definition transl_code' (f: Mach.function) (il: list Mach.instruction) (it1p: bool) :=
  transl_code_rec f il it1p (fun c => OK c).

(** Translation of a whole function.  Note that we must check
  that the generated code contains less than [2^32] instructions,
  otherwise the offset part of the [PC] code pointer could wrap
  around, leading to incorrect executions. *)

Definition transl_function (f: Mach.function) :=
  do c <- transl_code' f f.(Mach.fn_code) true;
  OK (mkfunction
        (Mach.fn_id f)
        (Mach.fn_sig f)
        (Pallocframe f.(Mach.fn_stacksize) f.(fn_retaddr_ofs) f.(fn_link_ofs) :: c)
        (Mach.fn_stacksize f)
        (Mach.fn_nbextra f)).

Definition transf_function (f: Mach.function) : res Asm.function :=
  do tf <- transl_function f;
  if zlt Int.max_unsigned (list_length_z tf.(fn_code))
  then Error (msg "code size exceeded")
  else OK tf.

Definition transf_fundef (f: Mach.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Mach.program) : res Asm.program :=
  transform_partial_program transf_fundef p.