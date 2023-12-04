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

(** Abstract syntax and semantics for IA32 assembly language *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Import Stacklayout.
Require Import Conventions.

Require Import Values_symbolictype.
Require Import Values_symbolic.

(** * Abstract syntax *)

(** ** Registers. *)

(** Integer registers. *)

Inductive ireg: Type :=
  | EAX: ireg  | EBX: ireg  | ECX: ireg  | EDX: ireg
  | ESI: ireg  | EDI: ireg  | EBP: ireg  | ESP: ireg.

(** Floating-point registers, i.e. SSE2 registers *)

Inductive freg: Type :=
  | XMM0: freg  | XMM1: freg  | XMM2: freg  | XMM3: freg
  | XMM4: freg  | XMM5: freg  | XMM6: freg  | XMM7: freg.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(** Bits of the flags register. *)

Inductive crbit: Type := 
  | ZF | CF | PF | SF | OF.

(** All registers modeled here. *)

Inductive preg: Type :=
  | PC: preg                            (**r program counter *)
  | IR: ireg -> preg                    (**r integer register *)
  | FR: freg -> preg                    (**r XMM register *)
  | ST0: preg                           (**r top of FP stack *)
  | CR: crbit -> preg                   (**r bit of the flags register *)
  | RA: preg.                   (**r pseudo-reg representing return address *)

Coercion IR: ireg >-> preg.
Coercion FR: freg >-> preg.
Coercion CR: crbit >-> preg.

(** Conventional names for stack pointer ([SP]) and return address ([RA]) *)

Notation SP := ESP (only parsing).

(** ** Instruction set. *)

Definition label := positive.

(** General form of an addressing mode. *)

Inductive addrmode: Type :=
  | Addrmode (base: option ireg)
             (ofs: option (ireg * int))
             (const: int + ident * int).

(** Testable conditions (for conditional jumps and more). *)

Inductive testcond: Type :=
  | Cond_e | Cond_ne
  | Cond_b | Cond_be | Cond_ae | Cond_a
  | Cond_l | Cond_le | Cond_ge | Cond_g
  | Cond_p | Cond_np.

(** Instructions.  IA32 instructions accept many combinations of
  registers, memory references and immediate constants as arguments.
  Here, we list only the combinations that we actually use.

  Naming conventions:
- [r]: integer register operand
- [f]: XMM register operand
- [m]: memory operand
- [i]: immediate integer operand
- [s]: immediate symbol operand
- [l]: immediate label operand
- [cl]: the [CL] register

  For two-operand instructions, the first suffix describes the result
  (and first argument), the second suffix describes the second argument.
*)

Inductive instruction: Type :=
  (** Moves *)
  | Pmov_rr (rd: ireg) (r1: ireg)       (**r [mov] (32-bit int) *)
  | Pmov_ri (rd: ireg) (n: int)
  | Pmov_ra (rd: ireg) (id: ident)
  | Pmov_rm (rd: ireg) (a: addrmode)
  | Pmov_mr (a: addrmode) (rs: ireg)
  | Pmovsd_ff (rd: freg) (r1: freg)     (**r [movsd] (single 64-bit float) *)
  | Pmovsd_fi (rd: freg) (n: float)     (**r (pseudo-instruction) *)
  | Pmovsd_fm (rd: freg) (a: addrmode)
  | Pmovsd_mf (a: addrmode) (r1: freg)
  | Pmovss_fi (rd: freg) (n: float32)   (**r [movss] (single 32-bit float) *)
  | Pmovss_fm (rd: freg) (a: addrmode)
  | Pmovss_mf (a: addrmode) (r1: freg)
  | Pfldl_m (a: addrmode)               (**r [fld] double precision *)
  | Pfstpl_m (a: addrmode)              (**r [fstp] double precision *)
  | Pflds_m (a: addrmode)               (**r [fld] simple precision *)
  | Pfstps_m (a: addrmode)              (**r [fstp] simple precision *)
  | Pxchg_rr (r1: ireg) (r2: ireg)      (**r register-register exchange *)
  (** Moves with conversion *)
  | Pmovb_mr (a: addrmode) (rs: ireg)   (**r [mov] (8-bit int) *)
  | Pmovw_mr (a: addrmode) (rs: ireg)   (**r [mov] (16-bit int) *)
  | Pmovzb_rr (rd: ireg) (rs: ireg)     (**r [movzb] (8-bit zero-extension) *)
  | Pmovzb_rm (rd: ireg) (a: addrmode)
  | Pmovsb_rr (rd: ireg) (rs: ireg)     (**r [movsb] (8-bit sign-extension) *)
  | Pmovsb_rm (rd: ireg) (a: addrmode)
  | Pmovzw_rr (rd: ireg) (rs: ireg)     (**r [movzw] (16-bit zero-extension) *)
  | Pmovzw_rm (rd: ireg) (a: addrmode)
  | Pmovsw_rr (rd: ireg) (rs: ireg)     (**r [movsw] (16-bit sign-extension) *)
  | Pmovsw_rm (rd: ireg) (a: addrmode)
  | Pcvtsd2ss_ff (rd: freg) (r1: freg)  (**r conversion to single float *)
  | Pcvtss2sd_ff (rd: freg) (r1: freg)  (**r conversion to double float *)
  | Pcvttsd2si_rf (rd: ireg) (r1: freg) (**r double to signed int *)
  | Pcvtsi2sd_fr (rd: freg) (r1: ireg)  (**r signed int to double *)
  | Pcvttss2si_rf (rd: ireg) (r1: freg) (**r single to signed int *)
  | Pcvtsi2ss_fr (rd: freg) (r1: ireg)  (**r signed int to single *)
  (** Integer arithmetic *)
  | Plea (rd: ireg) (a: addrmode)
  | Pneg (rd: ireg)
  | Psub_rr (rd: ireg) (r1: ireg)
  | Pimul_rr (rd: ireg) (r1: ireg)
  | Pimul_ri (rd: ireg) (n: int)
  | Pimul_r (r1: ireg)
  | Pmul_r (r1: ireg)
  | Pdiv (r1: ireg)
  | Pidiv (r1: ireg)
  | Pand_rr (rd: ireg) (r1: ireg)
  | Pand_ri (rd: ireg) (n: int)
  | Por_rr (rd: ireg) (r1: ireg)
  | Por_ri (rd: ireg) (n: int)
  | Pxor_r (rd: ireg)                  (**r [xor] with self = set to zero *)
  | Pxor_rr (rd: ireg) (r1: ireg)
  | Pxor_ri (rd: ireg) (n: int)
  | Pnot (rd: ireg)
  | Psal_rcl (rd: ireg)
  | Psal_ri (rd: ireg) (n: int)
  | Pshr_rcl (rd: ireg)
  | Pshr_ri (rd: ireg) (n: int)
  | Psar_rcl (rd: ireg)
  | Psar_ri (rd: ireg) (n: int)
  | Pshld_ri (rd: ireg) (r1: ireg) (n: int)
  | Pror_ri (rd: ireg) (n: int)
  | Pcmp_rr (r1 r2: ireg) 
  | Pcmp_ri (r1: ireg) (n: int)
  | Ptest_rr (r1 r2: ireg)
  | Ptest_ri (r1: ireg) (n: int)
  | Pcmov (c: testcond) (rd: ireg) (r1: ireg)
  | Psetcc (c: testcond) (rd: ireg)
  (** Floating-point arithmetic *)
  | Paddd_ff (rd: freg) (r1: freg)
  | Psubd_ff (rd: freg) (r1: freg)
  | Pmuld_ff (rd: freg) (r1: freg)
  | Pdivd_ff (rd: freg) (r1: freg)
  | Pnegd (rd: freg)
  | Pabsd (rd: freg)
  | Pcomisd_ff (r1 r2: freg)
  | Pxorpd_f (rd: freg)	              (**r [xor] with self = set to zero *)
  | Padds_ff (rd: freg) (r1: freg)
  | Psubs_ff (rd: freg) (r1: freg)
  | Pmuls_ff (rd: freg) (r1: freg)
  | Pdivs_ff (rd: freg) (r1: freg)
  | Pnegs (rd: freg)
  | Pabss (rd: freg)
  | Pcomiss_ff (r1 r2: freg)
  | Pxorps_f (rd: freg)	              (**r [xor] with self = set to zero *)
  (** Branches and calls *)
  | Pjmp_l (l: label)
  | Pjmp_s (symb: ident) (sg: signature)
  | Pjmp_r (r: ireg) (sg: signature)
  | Pjcc (c: testcond)(l: label)
  | Pjcc2 (c1 c2: testcond)(l: label)   (**r pseudo *)
  | PjccOr (c1 c2: testcond)(l: label)   (**r pseudo *)
  | Pjmptbl (r: ireg) (tbl: list label) (**r pseudo *)
  | Pcall_s (symb: ident) (sg: signature)
  | Pcall_r (r: ireg) (sg: signature)
  | Pret
  (** Saving and restoring registers *)
  | Pmov_rm_a (rd: ireg) (a: addrmode)  (**r like [Pmov_rm], using [Many32] chunk *)
  | Pmov_mr_a (a: addrmode) (rs: ireg)  (**r like [Pmov_mr], using [Many32] chunk *)
  | Pmovsd_fm_a (rd: freg) (a: addrmode) (**r like [Pmovsd_fm], using [Many64] chunk *)
  | Pmovsd_mf_a (a: addrmode) (r1: freg) (**r like [Pmovsd_mf], using [Many64] chunk *)
  (** Pseudo-instructions *)
  | Plabel(l: label)
  | Pallocframe(sz: Z)(ofs_ra ofs_link: int)
  | Pfreeframe(sz: Z)(ofs_ra ofs_link: int)
  | Pbuiltin(ef: external_function)(args: list preg)(res: list preg)
  | Pannot(ef: external_function)(args: list annot_param)

with annot_param : Type :=
  | APreg: preg -> annot_param
  | APstack: memory_chunk -> Z -> annot_param.

Definition code := list instruction.
Record function : Type := mkfunction {
                              fn_id: ident;
                              fn_sig: signature;
                              fn_code: code;
                              fn_stacksize: Z (* just to compute the oracles
                                                 easily from the assembly
                                                 program *);
                              fn_nbextra: nat
                            }.

Definition fundef := AST.fundef function.

Definition fid f :=
  match f with
    Internal f => Some (fn_id f)
  | _ => None
  end.

Definition program := AST.program fundef unit.

(** * Operational semantics *)

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. apply freg_eq. decide equality. Defined.

Module PregEq.
  Definition t := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

Definition regset := Pregmap.t expr_sym.
Definition genv := Genv.t fundef unit.

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level).

(** Undefining some registers *)

Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- (Eval Vundef))
  end.

(** Assigning multiple registers *)

Fixpoint set_regs (rl: list preg) (vl: list expr_sym) (rs: regset) : regset :=
  match rl, vl with
  | r1 :: rl', v1 :: vl' => set_regs rl' vl' (rs#r1 <- v1)
  | _, _ => rs
  end.

Section RELSEM.

(** Looking up instructions in a code sequence by position. *)

Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.

Variable ge: genv.

(** Evaluating an addressing mode *)

Definition eval_addrmode (a: addrmode) (rs: regset) : expr_sym :=
  match a with
      Addrmode base ofs const =>
      let bb :=
          match base with
            | None => Eval (Vint Int.zero)
            | Some r => rs r
          end in
      let oo :=
          match ofs with
            | None => Eval (Vint Int.zero)
            | Some(r, sc) =>
              if Int.eq sc Int.one then rs r else Val.mul (rs r) (Eval (Vint sc))              
          end in
      let cc :=
          match const with
            | inl ofs => Eval (Vint ofs)
            | inr(id, ofs) =>
              match Genv.symbol_address' ge id ofs with
                None => Eval Vundef
              | Some v => v
              end
          end in
      Val.add bb (Val.add oo cc)
  end.

(** Performing a comparison *)

(** Integer comparison between x and y:
-       ZF = 1 if x = y, 0 if x != y
-       CF = 1 if x <u y, 0 if x >=u y
-       SF = 1 if x - y is negative, 0 if x - y is positive
-       OF = 1 if x - y overflows (signed), 0 if not
-       PF is undefined
*)

Definition compare_ints (x y: expr_sym) (rs: regset) (m: mem): regset :=
  rs #ZF  <- ( (Val.cmpu Ceq x y))
     #CF  <- ( (Val.cmpu Clt x y))
     #SF  <- ( (Ebinop (OpCmp SESigned Clt) Tint Tint (Val.sub x y) (Eval (Vint Int.zero))))
     #OF  <- ( (Ebinop OpSubOverflow Tint Tint x y))
     #PF  <- (Eval Vundef).

(** Floating-point comparison between x and y:
-       ZF = 1 if x=y or unordered, 0 if x<>y
-       CF = 1 if x<y or unordered, 0 if x>=y
-       PF = 1 if unordered, 0 if ordered.
-       SF and 0F are undefined
*)

Definition compare_floats (x y: expr_sym) (rs: regset) : regset :=
      rs #ZF  <- ( (Val.cmpf Ceq x y))
         #CF  <- ( Val.notbool (Val.cmpf Cge x y))
         #PF  <- ( (Eunop OpNotbool Tint
                              (Ebinop OpOr Tint Tint
                                      (Val.cmpf Ceq x y)
                                      (Ebinop OpOr Tint Tint
                                              (Val.cmpf Clt x y)
                                              (Val.cmpf Cgt x y)))))
         #SF  <- (Eval Vundef)
         #OF  <- (Eval Vundef).

Definition compare_floats32 (x y: expr_sym) (rs: regset) : regset :=
    rs #ZF  <- ( (Val.cmpfs Ceq x y))
         #CF  <- ( Val.notbool (Val.cmpfs Cge x y))
         #PF  <- ( (Eunop OpNotbool Tint
                              (Ebinop OpOr Tint Tint
                                      (Val.cmpfs Ceq x y)
                                      (Ebinop OpOr Tint Tint
                                              (Val.cmpfs Clt x y)
                                              (Val.cmpfs Cgt x y)))))
         #SF  <- (Eval Vundef)
         #OF  <- (Eval Vundef).

(** Testing a condition *)

Definition test_one (x: expr_sym) : expr_sym :=
  Val.cmp Ceq x (Eval (Vint Int.one)).

Definition test_zero (x: expr_sym) : expr_sym :=
  Val.cmp Ceq x (Eval (Vint Int.zero)).

Definition eval_testcond (c: testcond) (rs: regset) : expr_sym :=
  match c with
    | Cond_e => test_one (rs ZF)
    | Cond_ne => test_zero (rs ZF)
    | Cond_b =>  test_one (rs CF)
    | Cond_be => Val.or (test_one (rs CF)) (test_one (rs ZF))
    | Cond_ae => test_zero (rs CF)
    | Cond_a => Val.and (test_zero (rs CF)) (test_zero (rs ZF))
    | Cond_l => test_one (Val.xor (rs OF) (rs SF))
    | Cond_le => Val.or (test_one (Val.xor (rs OF) (rs SF))) (test_one (rs ZF))
    | Cond_ge => test_zero (Val.xor (rs OF) (rs SF))
    | Cond_g => Val.and (test_zero (Val.xor (rs OF) (rs SF))) (test_zero (rs ZF))
    | Cond_p => test_one (rs PF)
    | Cond_np => test_zero (rs PF)
  end.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome: Type :=
  | Next: regset -> mem -> outcome
  | Stuck: outcome.

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]).
  [nextinstr_nf] is a variant of [nextinstr] that sets condition flags
  to [Vundef] in addition to incrementing the [PC]. *)


Definition incr o := Int.add o Int.one.

Definition nextinstr (rs: regset) :=
  match rs#PC with
      Eval (Vptr b o) => rs#PC <- (Eval (Vptr b (incr o)))
    | _ => rs
  end.
  (* rs#PC <- (Val.add (rs#PC) (Eval (Vint Int.one))). *)

Definition nextinstr_nf (rs: regset) : regset :=
  nextinstr (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs).


Ltac repSplit :=
  repeat match goal with
           | |- _ /\ _ => split; auto
         end.




Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
    | None => Stuck
    | Some pos =>
      match rs#PC with
          Eval (Vptr b ofs) =>
          Next (rs#PC <- (Eval (Vptr b (Int.repr pos)))) m
        | _ => Stuck
      end
  end.

(** Auxiliaries for memory accesses. *)

Definition exec_load (chunk: memory_chunk) (m: mem)
           (a: addrmode) (rs: regset) (rd: preg) :=
  match Mem.loadv chunk m (eval_addrmode a rs)  with
    | Some v => Next (nextinstr_nf (rs#rd <- v)) m
    | None => Stuck
  end.

Definition exec_store (chunk: memory_chunk) (m: mem)
                      (a: addrmode) (rs: regset) (r1: preg)
                      (destroyed: list preg) :=
  match Mem.storev chunk m (eval_addrmode a rs) (rs r1) with
    | Some m' => Next (nextinstr_nf (undef_regs destroyed rs)) m'
    | None => Stuck
  end.

(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual IA32 instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the IA32 reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above.  

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the IA32 code
    we generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction.

    Concerning condition flags, the comparison instructions set them
    accurately; other instructions (moves, [lea]) preserve them;
    and all other instruction set those flags to [Vundef], to reflect
    the fact that the processor updates some or all of those flags,
    but we do not need to model this precisely.
*)

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  (** Moves *)
  | Pmov_rr rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) m
  | Pmov_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Eval (Vint n)))) m
  | Pmov_ra rd id =>
    match Genv.symbol_address ge id Int.zero with
        Vptr b o =>
        Next (nextinstr_nf (rs#rd <- (Eval (Vptr b o)))) m
      | _ => Stuck
    end
  | Pmov_rm rd a =>
      exec_load Mint32 m a rs rd
  | Pmov_mr a r1 =>
      exec_store Mint32 m a rs r1 nil
  | Pmovsd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) m
  | Pmovsd_fi rd n =>
      Next (nextinstr (rs#rd <- (Eval (Vfloat n)))) m
  | Pmovsd_fm rd a =>
      exec_load Mfloat64 m a rs rd
  | Pmovsd_mf a r1 =>
      exec_store Mfloat64 m a rs r1 nil
  | Pmovss_fi rd n =>
      Next (nextinstr (rs#rd <- (Eval (Vsingle n)))) m
  | Pmovss_fm rd a =>
      exec_load Mfloat32 m a rs rd
  | Pmovss_mf a r1 =>
      exec_store Mfloat32 m a rs r1 nil
  | Pfldl_m a =>
      exec_load Mfloat64 m a rs ST0
  | Pfstpl_m a =>
      exec_store Mfloat64 m a rs ST0 (ST0 :: nil)
  | Pflds_m a =>
      exec_load Mfloat32 m a rs ST0
  | Pfstps_m a =>
      exec_store Mfloat32 m a rs ST0 (ST0 :: nil)
  | Pxchg_rr r1 r2 =>
      Next (nextinstr (rs#r1 <- (rs r2) #r2 <- (rs r1))) m
  (** Moves with conversion *)
  | Pmovb_mr a r1 =>
      exec_store Mint8unsigned m a rs r1 nil
  | Pmovw_mr a r1 =>
      exec_store Mint16unsigned m a rs r1 nil
  | Pmovzb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 8 rs#r1))) m
  | Pmovzb_rm rd a =>
      exec_load Mint8unsigned m a rs rd
  | Pmovsb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1))) m
  | Pmovsb_rm rd a =>
      exec_load Mint8signed m a rs rd
  | Pmovzw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 16 rs#r1))) m
  | Pmovzw_rm rd a =>
      exec_load Mint16unsigned m a rs rd
  | Pmovsw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1))) m
  | Pmovsw_rm rd a =>
      exec_load Mint16signed m a rs rd
  | Pcvtsd2ss_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.singleoffloat rs#r1))) m
  | Pcvtss2sd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.floatofsingle rs#r1))) m
  | Pcvttsd2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- ((Val.intoffloat rs#r1)))) m
  | Pcvtsi2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- ((Val.floatofint rs#r1)))) m
  | Pcvttss2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- ((Val.intofsingle rs#r1)))) m
  | Pcvtsi2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- ( (Val.singleofint rs#r1)))) m
  (** Integer arithmetic *)
  | Plea rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode a rs))) m
  | Pneg rd =>
      Next (nextinstr_nf (rs#rd <- (Val.neg rs#rd))) m
  | Psub_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd rs#r1))) m
  | Pimul_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd rs#r1))) m
  | Pimul_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd (Eval (Vint n))))) m
  | Pimul_r r1 =>
      Next (nextinstr_nf (rs#EAX <- (Val.mul rs#EAX rs#r1)
                            #EDX <- (Val.mulhs rs#EAX rs#r1))) m
  | Pmul_r r1 =>
      Next (nextinstr_nf (rs#EAX <- (Val.mul rs#EAX rs#r1)
                            #EDX <- (Val.mulhu rs#EAX rs#r1))) m
  | Pdiv r1 =>
      let vn := rs#EAX in let vd := (rs#EDX <- (Eval Vundef))#r1 in
      match Val.divu vn vd, Val.modu vn vd with
      | vq, vr => Next (nextinstr_nf (rs#EAX <- vq #EDX <- vr)) m
      end
  | Pidiv r1 =>
      let vn := rs#EAX in let vd := (rs#EDX <- (Eval Vundef))#r1 in
      match Val.divs vn vd, Val.mods vn vd with
      | vq, vr => Next (nextinstr_nf (rs#EAX <- vq #EDX <- vr)) m
      end
  | Pand_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd rs#r1))) m
  | Pand_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd (Eval (Vint n))))) m
  | Por_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd rs#r1))) m
  | Por_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd (Eval (Vint n))))) m
  | Pxor_r rd =>
      Next (nextinstr_nf (rs#rd <- (Eval Vzero))) m
  | Pxor_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd rs#r1))) m
  | Pxor_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd (Eval (Vint n))))) m
  | Pnot rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notint rs#rd))) m
  | Psal_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd rs#ECX))) m
  | Psal_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd (Eval (Vint n))))) m
  | Pshr_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd rs#ECX))) m
  | Pshr_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd (Eval (Vint n))))) m
  | Psar_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd rs#ECX))) m
  | Psar_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd (Eval (Vint n))))) m
  | Pshld_ri rd r1 n =>
      Next (nextinstr_nf
              (rs#rd <- (Val.or (Val.shl rs#rd (Eval (Vint n)))
                                (Val.shru rs#r1 (Eval (Vint (Int.sub Int.iwordsize n))))))) m
  | Pror_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.ror rs#rd (Eval (Vint n))))) m
  | Pcmp_rr r1 r2 =>
      Next (nextinstr (compare_ints (rs r1) (rs r2) rs m)) m
  | Pcmp_ri r1 n =>
      Next (nextinstr (compare_ints (rs r1) (Eval (Vint n)) rs m)) m
  | Ptest_rr r1 r2 =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (rs r2)) (Eval Vzero) rs m)) m
  | Ptest_ri r1 n =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (Eval (Vint n))) (Eval Vzero) rs m)) m
  | Pcmov c rd r1 =>
    let res := Val.add (Val.mul (eval_testcond c rs) rs#r1)
                       (Val.mul (Val.notbool (eval_testcond c rs)) rs#rd) in
    Next (nextinstr (rs#rd <- res)) m
     (* match Mem.mem_norm m (eval_testcond c rs) Int with *)
     (*        Vint i => if Int.eq i Int.zero *)
     (*                  then Next (nextinstr rs) m *)
     (*                  else Next (nextinstr (rs#rd <- (rs#r1))) m *)
     (*      | _ => Next (nextinstr (rs#rd <- (Eval Vundef))) m *)
     (* end *)
  | Psetcc c rd =>
      Next (nextinstr (rs#rd <- (eval_testcond c rs))) m
  (** Arithmetic operations over double-precision floats *)
  | Paddd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addf rs#rd rs#r1))) m
  | Psubd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subf rs#rd rs#r1))) m
  | Pmuld_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulf rs#rd rs#r1))) m
  | Pdivd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divf rs#rd rs#r1))) m
  | Pnegd rd =>
      Next (nextinstr (rs#rd <- (Val.negf rs#rd))) m
  | Pabsd rd =>
      Next (nextinstr (rs#rd <- (Val.absf rs#rd))) m
  | Pcomisd_ff r1 r2 =>
      Next (nextinstr (compare_floats (rs r1) (rs r2) rs)) m
  | Pxorpd_f rd =>
      Next (nextinstr_nf (rs#rd <- (Eval (Vfloat Float.zero)))) m
  (** Arithmetic operations over single-precision floats *)
  | Padds_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addfs rs#rd rs#r1))) m
  | Psubs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subfs rs#rd rs#r1))) m
  | Pmuls_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulfs rs#rd rs#r1))) m
  | Pdivs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divfs rs#rd rs#r1))) m
  | Pnegs rd =>
      Next (nextinstr (rs#rd <- (Val.negfs rs#rd))) m
  | Pabss rd =>
      Next (nextinstr (rs#rd <- (Val.absfs rs#rd))) m
  | Pcomiss_ff r1 r2 =>
      Next (nextinstr (compare_floats32 (rs r1) (rs r2) rs)) m
  | Pxorps_f rd =>
      Next (nextinstr_nf (rs#rd <- (Eval (Vsingle Float32.zero)))) m
  (** Branches and calls *)
  | Pjmp_l lbl =>
      goto_label f lbl rs m
  | Pjmp_s id sg =>
    match Genv.symbol_address ge id Int.zero with
        Vptr b o =>    
        Next (rs#PC <- (Eval (Vptr b o))) m
      | _ => Stuck
    end
  | Pjmp_r r sg =>
    match Mem.mem_norm m (rs r) with
        Vptr b o =>
        Next (rs#PC <- (Eval (Vptr b o))) m
      | _ => Stuck
    end
  | Pjcc cond lbl =>
    match Mem.mem_norm m (eval_testcond cond rs) with
        Vint i => if negb (Int.eq i Int.zero)
                  then goto_label f lbl rs m
                  else Next (nextinstr rs) m
      | _ => Stuck
    end
  | Pjcc2 cond1 cond2 lbl =>
    match Mem.mem_norm m (Val.and (eval_testcond cond1 rs) (eval_testcond cond2 rs)) with
      | Vint i =>
        if negb (Int.eq i Int.zero)
        then goto_label f lbl rs m
        else Next (nextinstr rs) m
      | _ => Stuck
    end
  | PjccOr cond1 cond2 lbl =>
    match Mem.mem_norm m (Val.or (eval_testcond cond1 rs) (eval_testcond cond2 rs)) with
      | Vint i =>
        if negb (Int.eq i Int.zero)
        then goto_label f lbl rs m
        else Next (nextinstr rs) m
      | _ => Stuck
    end
  | Pjmptbl r tbl =>
      match Mem.mem_norm m rs#r with
      | Vint n => 
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl rs m
          end
      | _ => Stuck
      end
  | Pcall_s id sg =>
     match rs#PC with
         Eval (Vptr bpc opc) =>
         match Genv.symbol_address ge id Int.zero with
             Vptr ba oa => 
             Next (rs#RA <- (Eval (Vptr bpc (Int.add opc Int.one)))
                     #PC <- (Eval (Vptr ba oa))
                  ) m
           | _ => Stuck
         end
       | _ => Stuck
     end
      (* Next (rs#RA <- (Val.add rs#PC (Eval Vone)) #PC <- (Eval (Genv.symbol_address ge id Int.zero))) m *)
  | Pcall_r r sg =>
    match rs#PC, Mem.mem_norm m rs#r with
        Eval (Vptr bpc opc), (Vptr br or) =>
        Next (rs#RA <- (Eval (Vptr bpc (Int.add opc Int.one)))
                #PC <- (Eval (Vptr br or))) m
      | _, _ => Stuck
    end
  | Pret =>
      Next (rs#PC <- (rs#RA)) m
  (** Saving and restoring registers *)
  | Pmov_rm_a rd a =>
      exec_load Many32 m a rs rd
  | Pmov_mr_a a r1 =>
      exec_store Many32 m a rs r1 nil
  | Pmovsd_fm_a rd a =>
      exec_load Many64 m a rs rd
  | Pmovsd_mf_a a r1 =>
      exec_store Many64 m a rs r1 nil
  (** Pseudo-instructions *)
  | Plabel lbl =>
    Next (nextinstr rs) m
         
  | Pallocframe sz ofs_ra ofs_link =>
    match Mem.alloc m 0 sz Normal with
      Some (m1, stk) =>
      (* let n := needed_stackspace f.(fn_id) - sz in *)
      (* if Z_ge_dec n 0 then *)
      (*   match Mem.alloc_bytes m1 (Z.to_nat n) with *)
      (*     Some (m1,l) => *)
          let sp := Eval (Vptr stk Int.zero) in
          match Mem.storev Mint32 m1 (Val.add sp (Eval (Vint ofs_link))) rs#ESP with
          | None => Stuck
          | Some m2 =>
            match Mem.storev Mint32 m2 (Val.add sp (Eval (Vint ofs_ra))) rs#RA with
            | None => Stuck
            | Some m3 => Next (nextinstr (rs #EDX <- (rs#ESP) #ESP <- sp)) m3
            end
          end
      (*   | None => Stuck *)
      (*   end *)
      (* else Stuck *)
    | _ => Stuck
    end

  | Pfreeframe sz ofs_ra ofs_link =>
      match Mem.loadv Mint32 m (Val.add rs#ESP (Eval (Vint ofs_ra))) with
      | None => Stuck
      | Some ra =>
          match Mem.loadv Mint32 m (Val.add rs#ESP (Eval (Vint ofs_link))) with
          | None => Stuck
          | Some sp =>
              match Mem.mem_norm m rs#ESP with
              | Vptr stk ofs =>
                  match Mem.free m stk 0 sz with
                  | None => Stuck
                  | Some m' =>
                    match Mem.mem_norm m ra with
                    | Vptr bra ora =>
                      Next (nextinstr (rs#ESP <- sp #RA <- (Eval (Vptr bra ora)))) m'
                    | Vint i =>
                      if Int.eq_dec i Int.zero
                      then 
                        Next (nextinstr (rs#ESP <- sp #RA <- (Eval (Vint Int.zero)))) m'
                      else Stuck
                    | _ => Stuck
                    end
                  end
              | _ => Stuck
              end
          end
      end
  | Pbuiltin ef args res =>
      Stuck                             (**r treated specially below *)
  | Pannot ef args =>
      Stuck                             (**r treated specially below *)
  end.

(** Translation of the LTL/Linear/Mach view of machine registers
  to the Asm view.  *)

Definition preg_of (r: mreg) : preg :=
  match r with
  | AX => IR EAX
  | BX => IR EBX
  | CX => IR ECX
  | DX => IR EDX
  | SI => IR ESI
  | DI => IR EDI
  | BP => IR EBP
  | X0 => FR XMM0
  | X1 => FR XMM1
  | X2 => FR XMM2
  | X3 => FR XMM3
  | X4 => FR XMM4
  | X5 => FR XMM5
  | X6 => FR XMM6
  | X7 => FR XMM7
  | FP0 => ST0
  end.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use machine registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> expr_sym -> Prop :=
| extcall_arg_reg:
    forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
| extcall_arg_stack:
    forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.add (rs (IR ESP)) (Eval (Vint (Int.repr bofs)))) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list expr_sym) : Prop :=
  list_forall2 (extcall_arg rs m) (loc_arguments sg) args.

Definition loc_external_result (sg: signature) : list preg :=
  map preg_of (loc_result sg).

(** Extract the values of the arguments of an annotation. *)

Inductive annot_arg (rs: regset) (m: mem): annot_param -> expr_sym -> Prop :=
| annot_arg_reg:
    forall r,
      annot_arg rs m (APreg r) (rs r)
| annot_arg_stack:
    forall chunk ofs stk base v,
      Mem.mem_norm m (rs (IR ESP)) = Vptr stk base ->
      Mem.load chunk m stk (Int.unsigned base + ofs) = Some v ->
      annot_arg rs m (APstack chunk ofs) v.

Definition annot_arguments
    (rs: regset) (m: mem) (params: list annot_param) (args: list expr_sym) : Prop :=
  list_forall2 (annot_arg rs m) params args.

(** Execution of the instruction at [rs#PC]. *)

Inductive state: Type :=
| State: regset -> mem -> state.

Inductive step: state -> trace -> state -> Prop :=
| exec_step_internal:
    forall b ofs f i rs m rs' m',
      rs PC = Eval (Vptr b ofs) ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) f.(fn_code) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
| exec_step_builtin:
    forall b ofs f ef args res rs m t vl rs' m',
      rs PC = Eval (Vptr b ofs) ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      external_call' ef ge (map rs args) m t vl m' ->
      rs' = nextinstr_nf 
              (set_regs res vl
                        (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      step (State rs m) t (State rs' m')
| exec_step_annot:
    forall b ofs f ef args rs m vargs t v m',
      rs PC = Eval (Vptr b ofs) ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) f.(fn_code) = Some (Pannot ef args) ->
      annot_arguments rs m args vargs ->
      external_call' ef ge vargs m t v m' ->
      step (State rs m) t
           (State (nextinstr rs) m')
| exec_step_external:
    forall b ef args res rs m t rs' m',
      rs PC = Eval (Vptr b Int.zero) ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      external_call' ef ge args m t res m' ->
      rs' = (set_regs (loc_external_result (ef_sig ef)) res rs) #PC <- (rs RA) ->
      step (State rs m) t (State rs' m').

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program) sg: state -> Prop :=
| initial_state_intro:
    forall m0 b o,
      Genv.init_mem fid sg p = Some m0 ->
      let ge := Genv.globalenv p in
      Genv.symbol_address ge p.(prog_main) Int.zero = Vptr b o ->
      let rs0 :=
          (Pregmap.init (Eval Vundef))
            # PC <- ( (Eval (Vptr b o)))
            # RA <- ( (Eval (Vint Int.zero)))
            # ESP <- ( (Eval (Vint Int.zero))) in
      initial_state p sg (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
| final_state_intro:
    forall (rs: regset) m r,
      rs#PC = Eval (Vint Int.zero) ->
      Mem.mem_norm m rs#EAX = Vint r ->
      final_state (State rs m) r.

Definition semantics (p: program) sg :=
  Semantics step (initial_state p sg) final_state (Genv.globalenv p).

(** Determinacy of the [Asm] semantics. *)

Remark extcall_arguments_determ:
  forall rs m sg args1 args2,
  extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (forall ll vl1, list_forall2 (extcall_arg rs m) ll vl1 ->
          forall vl2, list_forall2 (extcall_arg rs m) ll vl2 -> vl1 = vl2).
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; auto. 
    inv H; inv H3; congruence.
  intros. red in H0; red in H1. eauto. 
Qed.

Remark annot_arguments_determ:
  forall rs m params args1 args2,
  annot_arguments rs m params args1 -> annot_arguments rs m params args2 -> args1 = args2.
Proof.
  unfold annot_arguments. intros. revert params args1 H args2 H0. 
  induction 1; intros. 
  - inv H0; auto.
  - inv H1. decEq; eauto.
    inv H; inv H4; congruence.
Qed.

Lemma semantics_determinate: forall p sg, determinate (semantics p sg).
Proof.
  Ltac Equalities :=
    match goal with
      | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
        rewrite H1 in H2; inv H2; Equalities
      | _ => idtac
    end.
  intros; constructor; simpl; intros.
  - (* determ *)
    inv H; inv H0; Equalities.
    + split. constructor. auto.
    + discriminate.
    + discriminate.
    + inv H11. 
    + exploit external_call_determ'. eexact H4. eexact H9. intros [A B].
      split. auto. intros. destruct B; auto. subst. auto.
    + inv H12.
    + assert (vargs0 = vargs) by (eapply annot_arguments_determ; eauto). subst vargs0.
      exploit external_call_determ'. eexact H5. eexact H13. intros [A B].
      split. auto. intros. destruct B; auto. subst. auto.
    + assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
      exploit external_call_determ'. eexact H4. eexact H9. intros [A B].
      split. auto. intros. destruct B; auto. subst. auto.
  - (* trace length *)
    red; intros; inv H; simpl.
    omega.
    inv H3. eapply external_call_trace_length; eauto.
    inv H4. eapply external_call_trace_length; eauto.
    inv H3. eapply external_call_trace_length; eauto.
  - (* initial states *)
    inv H; inv H0.
    rewrite H1 in H; inv H.
    unfold ge, ge0 in *.
    rewrite H3 in H2. inversion H2. f_equal.
    unfold rs0, rs1. repeat f_equal; auto.
  - (* final no step *)
    inv H. red; intros; red; intros.
    inv H; try congruence. 
  - (* final states *)
    inv H; inv H0. congruence.
Qed.

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | PC => false
  | IR _ => true
  | FR _ => true
  | ST0 => true
  | CR _ => false
  | RA => false
  end.

