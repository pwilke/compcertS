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

(** Abstract syntax and semantics for the Cminor language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Events.
Require Import Values.
Require Import Memory MemReserve.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Switch.
Require Import Values_symbolictype.
Require Import Values_symbolic.
Require Import Normalise.

(** * Abstract syntax *)

(** Cminor is a low-level imperative language structured in expressions,
  statements, functions and programs.  We first define the constants
  and operators that occur within expressions. *)

Inductive constant : Type :=
  | Ointconst: int -> constant     (**r integer constant *)
  | Ofloatconst: float -> constant (**r double-precision floating-point constant *)
  | Osingleconst: float32 -> constant (**r single-precision floating-point constant *)
  | Olongconst: int64 -> constant  (**r long integer constant *)
  | Oaddrsymbol: ident -> int -> constant (**r address of the symbol plus the offset *)
  | Oaddrstack: int -> constant.   (**r stack pointer plus the given offset *)

Inductive unary_operation : Type :=
  | Ocast8unsigned: unary_operation        (**r 8-bit zero extension  *)
  | Ocast8signed: unary_operation          (**r 8-bit sign extension  *)
  | Ocast16unsigned: unary_operation       (**r 16-bit zero extension  *)
  | Ocast16signed: unary_operation         (**r 16-bit sign extension *)
  | Onegint: unary_operation               (**r integer opposite *)
  | Onotint: unary_operation               (**r bitwise complement  *)
  | Onegf: unary_operation                 (**r float64 opposite *)
  | Oabsf: unary_operation                 (**r float64 absolute value *)
  | Onegfs: unary_operation                (**r float32 opposite *)
  | Oabsfs: unary_operation                (**r float32 absolute value *)
  | Osingleoffloat: unary_operation        (**r float truncation to float32 *)
  | Ofloatofsingle: unary_operation        (**r float extension to float64 *)
  | Ointoffloat: unary_operation           (**r signed integer to float64 *)
  | Ointuoffloat: unary_operation          (**r unsigned integer to float64 *)
  | Ofloatofint: unary_operation           (**r float64 to signed integer *)
  | Ofloatofintu: unary_operation          (**r float64 to unsigned integer *)
  | Ointofsingle: unary_operation          (**r signed integer to float32 *)
  | Ointuofsingle: unary_operation         (**r unsigned integer to float32 *)
  | Osingleofint: unary_operation          (**r float32 to signed integer *)
  | Osingleofintu: unary_operation        (**r float32 to unsigned integer *)
  | Onegl: unary_operation                 (**r long integer opposite *)
  | Onotl: unary_operation                 (**r long bitwise complement *)
  | Ointoflong: unary_operation            (**r long to int *)
  | Olongofint: unary_operation            (**r signed int to long *)
  | Olongofintu: unary_operation           (**r unsigned int to long *)
  | Olongoffloat: unary_operation          (**r float64 to signed long *)
  | Olonguoffloat: unary_operation         (**r float64 to unsigned long *)
  | Ofloatoflong: unary_operation          (**r signed long to float64 *)
  | Ofloatoflongu: unary_operation         (**r unsigned long to float64 *)
  | Olongofsingle: unary_operation         (**r float32 to signed long *)
  | Olonguofsingle: unary_operation        (**r float32 to unsigned long *)
  | Osingleoflong: unary_operation         (**r signed long to float32 *)
  | Osingleoflongu: unary_operation        (**r unsigned long to float32 *)
  (** Should better be builtins ? 
      This is just a reinterpret-cast which shall have no runtime meaning i.e it shall be implemented by a nop
   *)      
(*  | Obitsofsingle                          (**r float32 to unsigned int   (bit encoding) *)
  | Obitsoffloat                           (**r float   to unsigned long  (bit encoding) *)
  | Osingleofbits                          (**r unsigned int to float32   (bit encoding) *)
  | Ofloatofbits                           (**r unsigned long to float    (bit encoding) *)
*)
.
                      
Inductive binary_operation : Type :=
  | Oadd: binary_operation                 (**r integer addition *)
  | Osub: binary_operation                 (**r integer subtraction *)
  | Omul: binary_operation                 (**r integer multiplication *)
  | Odiv: binary_operation                 (**r integer signed division *)
  | Odivu: binary_operation                (**r integer unsigned division *)
  | Omod: binary_operation                 (**r integer signed modulus *)
  | Omodu: binary_operation                (**r integer unsigned modulus *)
  | Oand: binary_operation                 (**r integer bitwise ``and'' *)
  | Oor: binary_operation                  (**r integer bitwise ``or'' *)
  | Oxor: binary_operation                 (**r integer bitwise ``xor'' *)
  | Oshl: binary_operation                 (**r integer left shift *)
  | Oshr: binary_operation                 (**r integer right signed shift *)
  | Oshru: binary_operation                (**r integer right unsigned shift *)
  | Oaddf: binary_operation                (**r float64 addition *)
  | Osubf: binary_operation                (**r float64 subtraction *)
  | Omulf: binary_operation                (**r float64 multiplication *)
  | Odivf: binary_operation                (**r float64 division *)
  | Oaddfs: binary_operation               (**r float32 addition *)
  | Osubfs: binary_operation               (**r float32 subtraction *)
  | Omulfs: binary_operation               (**r float32 multiplication *)
  | Odivfs: binary_operation               (**r float32 division *)
  | Oaddl: binary_operation                (**r long addition *)
  | Osubl: binary_operation                (**r long subtraction *)
  | Omull: binary_operation                (**r long multiplication *)
  | Odivl: binary_operation                (**r long signed division *)
  | Odivlu: binary_operation               (**r long unsigned division *)
  | Omodl: binary_operation                (**r long signed modulus *)
  | Omodlu: binary_operation               (**r long unsigned modulus *)
  | Oandl: binary_operation                (**r long bitwise ``and'' *)
  | Oorl: binary_operation                 (**r long bitwise ``or'' *)
  | Oxorl: binary_operation                (**r long bitwise ``xor'' *)
  | Oshll: binary_operation                (**r long left shift *)
  | Oshrl: binary_operation                (**r long right signed shift *)
  | Oshrlu: binary_operation               (**r long right unsigned shift *)
  | Ocmp: comparison -> binary_operation   (**r integer signed comparison *)
  | Ocmpu: comparison -> binary_operation  (**r integer unsigned comparison *)
  | Ocmpf: comparison -> binary_operation  (**r float64 comparison *)
  | Ocmpfs: comparison -> binary_operation (**r float32 comparison *)
  | Ocmpl: comparison -> binary_operation  (**r long signed comparison *)
  | Ocmplu: comparison -> binary_operation (**r long unsigned comparison *)

.
(** Expressions include reading local variables, constants,
  arithmetic operations, and memory loads. *)

Inductive expr : Type :=
  | Evar : ident -> expr
  | Econst : constant -> expr
  | Eunop : unary_operation -> expr -> expr
  | Ebinop : binary_operation -> expr -> expr -> expr
  | Eload : memory_chunk -> expr -> expr.

(** Statements include expression evaluation, assignment to local variables,
  memory stores, function calls, an if/then/else conditional, infinite
  loops, blocks and early block exits, and early function returns.
  [Sexit n] terminates prematurely the execution of the [n+1]
  enclosing [Sblock] statements. *)

Definition label := ident.

Inductive stmt : Type :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt
  | Sstore : memory_chunk -> expr -> expr -> stmt
  | Scall : option ident -> signature -> expr -> list expr -> stmt
  | Stailcall: signature -> expr -> list expr -> stmt
  | Sbuiltin : option ident -> external_function -> list expr -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: expr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: bool -> expr -> list (Z * nat) -> nat -> stmt
  | Sreturn: option expr -> stmt
  | Slabel: label -> stmt -> stmt
  | Sgoto: label -> stmt.

(** Functions are composed of a signature, a list of parameter names,
  a list of local variables, and a  statement representing
  the function body.  Each function can allocate a memory block of
  size [fn_stackspace] on entrance.  This block will be deallocated
  automatically before the function returns.  Pointers into this block
  can be taken with the [Oaddrstack] operator. *)

Record function : Type := mkfunction {
  fn_id: ident;
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list ident;
  fn_stackspace: Z;
  fn_body: stmt;
  fn_stackspace_pos: 0 <= fn_stackspace
}.

Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

(** * Operational semantics (small-step) *)

(** Two kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [env]: local environments, map local variables to values.
*)

Definition genv := Genv.t fundef unit.
Definition env := PTree.t expr_sym.

(** The following functions build the initial local environment at
  function entry, binding parameters to the provided arguments and
  initializing local variables to [Vundef]. *)

Fixpoint set_params (vl: list expr_sym) (il: list ident) {struct il} : env :=
  match il, vl with
  | i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is)
  | i1 :: is, nil => PTree.set i1 (Eval Vundef) (set_params nil is)
  | _, _ => PTree.empty expr_sym
  end.

Fixpoint set_locals (il: list ident) (e: env) {struct il} : env :=
  match il with
  | nil => e
  | i1 :: is => PTree.set i1 (Eval Vundef)  (set_locals is e)
  end.

Definition set_optvar (optid: option ident) (v: expr_sym) (e: env) : env :=
  match optid with
  | None => e
  | Some id => PTree.set id v e
  end.

(** Continuations *)

Inductive cont: Type :=
  | Kstop: cont                         (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kblock: cont -> cont                (**r exit a block, then do cont *)
  | Kcall: option ident -> function -> block -> env -> cont -> cont.
                                        (**r return to caller *)

(** States *)

Inductive state: Type :=
  | State:                      (**r Execution within a function *)
      forall (f: function)              (**r currently executing function  *)
             (s: stmt)                  (**r statement under consideration *)
             (k: cont)                  (**r its continuation -- what to do next *)
             (sp: block)                  (**r current stack pointer *)
             (e: env)                   (**r current local environment *)
             (m: mem),                  (**r current memory state *)
      state
  | Callstate:                  (**r Invocation of a function *)
      forall (f: fundef)                (**r function to invoke *)
             (args: list expr_sym)           (**r arguments provided by caller *)
             (k: cont)                  (**r what to do next  *)
             (m: mem),                  (**r memory state *)
      state
  | Returnstate:                (**r Return from a function *)
      forall (v: expr_sym)                   (**r Return value *)
             (k: cont)                  (**r what to do next *)
             (m: mem),                  (**r memory state *)
      state.
             
Section RELSEM.

  Variable ge: genv.

  Variable needed_stackspace : ident -> nat.


(** Evaluation of constants and operator applications.
    [None] is returned when the computation is undefined, e.g.
    if arguments are of the wrong types, or in case of an integer division
    by zero. *)

Definition eval_constant (sp: block) (cst: constant) : option expr_sym :=
  match cst with
  | Ointconst n => Some (Eval (Vint n))
  | Ofloatconst n => Some (Eval (Vfloat n))
  | Osingleconst n => Some (Eval (Vsingle n))
  | Olongconst n => Some (Eval (Vlong n))
  | Oaddrsymbol s ofs =>
    match Genv.find_symbol ge s with
      | None => None
      | Some b => Some (Eval (Vptr b ofs))
    end
  | Oaddrstack ofs => Some (Eval (Vptr sp ofs))
  end.


Definition eval_unop (op: unary_operation) (arg: expr_sym) : option expr_sym :=
  match op with
  | Ocast8unsigned => Some (Val.zero_ext 8 arg)
  | Ocast8signed => Some (Val.sign_ext 8 arg)
  | Ocast16unsigned => Some (Val.zero_ext 16 arg)
  | Ocast16signed => Some (Val.sign_ext 16 arg)
  | Onegint => Some (Val.negint arg)
  | Onotint => Some (Val.notint arg)
  | Onegf => Some (Val.negf arg)
  | Oabsf => Some (Val.absf arg)
  | Onegfs => Some (Val.negfs arg)
  | Oabsfs => Some (Val.absfs arg)
  | Osingleoffloat => Some (Val.singleoffloat arg)
  | Ofloatofsingle => Some (Val.floatofsingle arg)
  | Ointoffloat => Some (Val.intoffloat arg)
  | Ointuoffloat => Some (Val.intuoffloat arg)
  | Ofloatofint => Some (Val.floatofint arg)
  | Ofloatofintu => Some (Val.floatofintu arg)
  | Ointofsingle => Some (Val.intofsingle arg)
  | Ointuofsingle => Some (Val.intuofsingle arg)
  | Osingleofint => Some (Val.singleofint arg)
  | Osingleofintu => Some (Val.singleofintu arg)
  | Onegl => Some (Val.negl arg)
  | Onotl => Some (Val.notl arg)
  | Ointoflong => Some (Val.loword arg)
  | Olongofint => Some (Val.longofint arg)
  | Olongofintu => Some (Val.longofintu arg)
  | Olongoffloat => Some (Val.longoffloat arg)
  | Olonguoffloat => Some (Val.longuoffloat arg)
  | Ofloatoflong => Some (Val.floatoflong arg)
  | Ofloatoflongu => Some (Val.floatoflongu arg)
  | Olongofsingle => Some (Val.longofsingle arg)
  | Olonguofsingle => Some (Val.longuofsingle arg)
  | Osingleoflong => Some (Val.singleoflong arg)
  | Osingleoflongu => Some (Val.singleoflongu arg)
  (** FB: Adding cast between integers and floating points.
          This is used to inspect the binary representation of floating point numbers.
          At the C level, this could be done by a union type... *)          
(*  | Obitsofsingle  => Some (Val.bitsofsingle arg)
  | Obitsofdouble  => Some (Val.bitsofdouble arg) *)
  end.

Definition eval_binop
            (op: binary_operation) (arg1 arg2: expr_sym) (m: mem): option expr_sym :=
  match op with
  | Oadd => Some (Val.add arg1 arg2)
  | Osub => Some (Val.sub arg1 arg2)
  | Omul => Some (Val.mul arg1 arg2)
  | Odiv => Some (Val.divs arg1 arg2)
  | Odivu => Some (Val.divu arg1 arg2)
  | Omod => Some (Val.mods arg1 arg2)
  | Omodu => Some (Val.modu arg1 arg2)
  | Oand => Some (Val.and arg1 arg2)
  | Oor => Some (Val.or arg1 arg2)
  | Oxor => Some (Val.xor arg1 arg2)
  | Oshl => Some (Val.shl arg1 arg2)
  | Oshr => Some (Val.shr arg1 arg2)
  | Oshru => Some (Val.shru arg1 arg2)
  | Oaddf => Some (Val.addf arg1 arg2)
  | Osubf => Some (Val.subf arg1 arg2)
  | Omulf => Some (Val.mulf arg1 arg2)
  | Odivf => Some (Val.divf arg1 arg2)
  | Oaddfs => Some (Val.addfs arg1 arg2)
  | Osubfs => Some (Val.subfs arg1 arg2)
  | Omulfs => Some (Val.mulfs arg1 arg2)
  | Odivfs => Some (Val.divfs arg1 arg2)
  | Oaddl => Some (Val.addl arg1 arg2)
  | Osubl => Some (Val.subl arg1 arg2)
  | Omull => Some (Val.mull arg1 arg2)
  | Odivl => Some (Val.divls arg1 arg2)
  | Odivlu => Some (Val.divlu arg1 arg2)
  | Omodl => Some (Val.modls arg1 arg2)
  | Omodlu => Some (Val.modlu arg1 arg2)
  | Oandl => Some (Val.andl arg1 arg2)
  | Oorl => Some (Val.orl arg1 arg2)
  | Oxorl => Some (Val.xorl arg1 arg2)
  | Oshll => Some (Val.shll arg1 arg2)
  | Oshrl => Some (Val.shrl arg1 arg2)
  | Oshrlu => Some (Val.shrlu arg1 arg2)
  | Ocmp c => Some (Val.cmp c arg1 arg2)
  | Ocmpu c => Some (Val.cmpu c arg1 arg2)
  | Ocmpf c => Some (Val.cmpf c arg1 arg2)
  | Ocmpfs c => Some (Val.cmpfs c arg1 arg2)
  | Ocmpl c => Some (Val.cmpl c arg1 arg2)
  | Ocmplu c => Some (Val.cmplu c arg1 arg2)
  end.

(** Evaluation of an expression: [eval_expr ge sp e m a v]
  states that expression [a] evaluates to value [v].
  [ge] is the global environment, [e] the local environment,
  and [m] the current memory state.  They are unchanged during evaluation.
  [sp] is the pointer to the memory block allocated for this function
  (stack frame).
*)

Section EVAL_EXPR.

Variable sp: block.
Variable e: env.
Variable m: mem.

Inductive eval_expr: expr -> expr_sym -> Prop :=
  | eval_Evar: forall id v,
      PTree.get id e = Some v ->
      eval_expr (Evar id) v
  | eval_Econst: forall cst v,
      eval_constant sp cst = Some v ->
      eval_expr (Econst cst) v
  | eval_Eunop: forall op a1 v1 v,
      eval_expr a1 v1 ->
      eval_unop op v1 = Some v ->
      eval_expr (Eunop op a1) v
  | eval_Ebinop: forall op a1 a2 v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      eval_binop op v1 v2 m = Some v ->
      eval_expr (Ebinop op a1 a2) v
  | eval_Eload: forall chunk addr vaddr v,
      eval_expr addr vaddr ->
      Mem.loadv chunk m vaddr = Some v ->     
      eval_expr (Eload chunk addr) v.

Inductive eval_exprlist: list expr -> list expr_sym -> Prop :=
  | eval_Enil:
      eval_exprlist nil nil
  | eval_Econs: forall a1 al v1 vl,
      eval_expr a1 v1 -> eval_exprlist al vl ->
      eval_exprlist (a1 :: al) (v1 :: vl).

End EVAL_EXPR.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kblock k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

(** Find the statement and manufacture the continuation 
  corresponding to a label *)

Fixpoint find_label (lbl: label) (s: stmt) (k: cont) 
                    {struct s}: option (stmt * cont) :=
  match s with
  | Sseq s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse a s1 s2 =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sloop s1 =>
      find_label lbl s1 (Kseq (Sloop s1) k)
  | Sblock s1 =>
      find_label lbl s1 (Kblock k)
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end.

(** One step of execution *)

Inductive step: state -> trace -> state -> Prop :=

  | step_skip_seq: forall f s k sp e m,
      step (State f Sskip (Kseq s k) sp e m)
        E0 (State f s k sp e m)
  | step_skip_block: forall f k sp e m,
      step (State f Sskip (Kblock k) sp e m)
        E0 (State f Sskip k sp e m)
  | step_skip_call: forall f k sp e m m' m'',
      is_call_cont k ->
      Mem.free m sp 0 (f.(fn_stackspace)) = Some m' ->
      release_boxes m' (needed_stackspace (fn_id f)) = Some m'' ->
      step (State f Sskip k sp e m)
        E0 (Returnstate (Eval Vundef) k m'')

  | step_assign: forall f id a k sp e m v,
      eval_expr sp e m a v ->
      step (State f (Sassign id a) k sp e m)
        E0 (State f Sskip k sp (PTree.set id v e) m)

  | step_store: forall f chunk addr a k sp e m vaddr v m',
      eval_expr sp e m addr vaddr ->
      eval_expr sp e m a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      step (State f (Sstore chunk addr a) k sp e m)
        E0 (State f Sskip k sp e m')

  | step_call: forall f optid sig a bl k sp e m vf vargs fd,
      eval_expr sp e m a vf ->
      eval_exprlist sp e m bl vargs ->
      Genv.find_funct m ge vf = Some fd ->
      funsig fd = sig ->
      step (State f (Scall optid sig a bl) k sp e m)
        E0 (Callstate fd vargs (Kcall optid f sp e k) m)

  | step_tailcall: forall f sig a bl k sp e m vf vargs fd m' m'',
      eval_expr sp e m a vf ->
      eval_exprlist sp e m bl vargs ->
      Genv.find_funct m'' ge vf = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 ( f.(fn_stackspace) ) = Some m' ->
      release_boxes m' (needed_stackspace (fn_id f)) = Some m'' ->
      step (State f (Stailcall sig a bl) k sp e m)
        E0 (Callstate fd vargs (call_cont k) m'')

  | step_builtin: forall f optid ef bl k sp e m vargs t vres m',
      eval_exprlist sp e m bl vargs ->
      external_call ef ge vargs m t vres m' ->
      step (State f (Sbuiltin optid ef bl) k sp e m)
         t (State f Sskip k sp (set_optvar optid vres e)  m')

  | step_seq: forall f s1 s2 k sp e m,
      step (State f (Sseq s1 s2) k sp e m)
        E0 (State f s1 (Kseq s2 k) sp e m)

  | step_ifthenelse: forall f a s1 s2 k sp e m v b,
                       eval_expr sp e m a v ->
                       Mem.mem_norm m v = Vint b ->
                       step (State f (Sifthenelse a s1 s2) k sp e m)
                            E0 (State f (if negb (Int.eq b Int.zero) then s1 else s2) k sp e m)

  | step_loop: forall f s k sp e m,
      step (State f (Sloop s) k sp e m)
        E0 (State f s (Kseq (Sloop s) k) sp e m)

  | step_block: forall f s k sp e m,
      step (State f (Sblock s) k sp e m)
        E0 (State f s (Kblock k) sp e m)

  | step_exit_seq: forall f n s k sp e m,
      step (State f (Sexit n) (Kseq s k) sp e m)
        E0 (State f (Sexit n) k sp e m)
  | step_exit_block_0: forall f k sp e m,
      step (State f (Sexit O) (Kblock k) sp e m)
        E0 (State f Sskip k sp e m)
  | step_exit_block_S: forall f n k sp e m,
      step (State f (Sexit (S n)) (Kblock k) sp e m)
        E0 (State f (Sexit n) k sp e m)

  | step_switch: forall f islong a cases default k sp e m v n,
      eval_expr sp e m a v ->
      switch_argument m islong v n ->
      step (State f (Sswitch islong a cases default) k sp e m)
        E0 (State f (Sexit (switch_target n default cases)) k sp e m)

  | step_return_0: forall f k sp e m m' m'',
      Mem.free m sp 0 ( f.(fn_stackspace) ) = Some m' ->
      release_boxes m' (needed_stackspace (fn_id f)) = Some m'' ->
      step (State f (Sreturn None) k sp e m)
        E0 (Returnstate (Eval Vundef) (call_cont k) m'')
  | step_return_1: forall f a k sp e m v m' m'',
      eval_expr sp e m a v ->
      Mem.free m sp 0 ( f.(fn_stackspace)) = Some m' ->
      release_boxes m' (needed_stackspace (fn_id f)) = Some m'' ->
      step (State f (Sreturn (Some a)) k sp e m)
        E0 (Returnstate v (call_cont k) m'')

  | step_label: forall f lbl s k sp e m,
      step (State f (Slabel lbl s) k sp e m)
        E0 (State f s k sp e m)

  | step_goto: forall f lbl k sp e m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
      step (State f (Sgoto lbl) k sp e m)
        E0 (State f s' k' sp e m)

  | step_internal_function: forall f vargs k m m' sp e m1 ,
      Mem.alloc m 0 ( f.(fn_stackspace)) Normal = Some (m1, sp) ->
      reserve_boxes m1 (needed_stackspace f.(fn_id)) = Some m' ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params))  = e ->
      step (Callstate (Internal f) vargs k m)
        E0 (State f f.(fn_body) k sp e m')
  | step_external_function: forall ef vargs k m t vres m',
      external_call ef ge vargs m t vres m' ->
      step (Callstate (External ef) vargs k m)
         t (Returnstate vres k m')        

  | step_return: forall v optid f sp e k m,
      step (Returnstate v (Kcall optid f sp e k) m)
        E0 (State f Sskip k sp (set_optvar optid v e) m).

End RELSEM.

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty continuation. *)

Definition fid f :=
  match f with
    Internal f => Some (fn_id f)
  | _ => None
  end.

Inductive initial_state (p: program) sg: state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem fid sg p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      initial_state p sg (Callstate f nil Kstop m0).

(** A final state is a [Returnstate] with an empty continuation. *)

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: 
      forall e r m,
        Mem.mem_norm m e = Vint r ->
        final_state (Returnstate e Kstop m) r.

(** The corresponding small-step semantics. *)

Definition semantics (p: program) ns sg  :=
  Semantics (fun ge => step ge ns) (initial_state p sg) final_state (Genv.globalenv p).

(** This semantics is receptive to changes in events. *)

Lemma semantics_receptive:
  forall (p: program) ns sg, receptive (semantics p ns sg).
Proof.
  intros. constructor; simpl; intros.
(* receptiveness *)
  assert (t1 = E0 -> exists s2, step (Genv.globalenv p) ns s t2 s2).
    intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]]. 
  exists (State f Sskip k sp (set_optvar optid vres2 e) m2). econstructor; eauto. 
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]]. 
  exists (Returnstate vres2 k m2). econstructor; eauto.
(* trace length *)
  red; intros; inv H; simpl; try omega; eapply external_call_trace_length; eauto.
Qed.

(** * Alternate operational semantics (big-step) *)

(** We now define another semantics for Cminor without [goto] that follows
  the ``big-step'' style of semantics, also known as natural semantics.
  In this style, just like expressions evaluate to values, 
  statements evaluate to``outcomes'' indicating how execution should
  proceed afterwards. *)

Inductive outcome: Type :=
  | Out_normal: outcome                (**r continue in sequence *)
  | Out_exit: nat -> outcome           (**r terminate [n+1] enclosing blocks *)
  | Out_return: option expr_sym -> outcome  (**r return immediately to caller *)
  | Out_tailcall_return: expr_sym -> outcome. (**r already returned to caller via a tailcall *)

Definition outcome_block (out: outcome) : outcome :=
  match out with
  | Out_exit O => Out_normal
  | Out_exit (S n) => Out_exit n
  | out => out
  end.

Definition outcome_result_value
    (out: outcome) (retsig: option typ) (vres: expr_sym) : Prop :=
  match out with
  | Out_normal => vres = Eval Vundef
  | Out_return None => vres = Eval Vundef
  | Out_return (Some v) => retsig <> None /\ vres = v
  | Out_tailcall_return v => vres = v
  | _ => False
  end.

Definition outcome_free_mem
    (out: outcome) (m: mem) (sp: block) (sz: Z) (m': mem) :=
  match out with
  | Out_tailcall_return _ => m' = m
  | _ => Mem.free m sp 0 sz = Some m'
  end.

Definition outcome_free_mem_extra
    (out: outcome) (m: mem) (n: nat) (m': mem) :=
  match out with
  | Out_tailcall_return _ => m' = m
  | _ => release_boxes m n = Some m'
  end.

Section NATURALSEM.

Variable ge: genv.

Variable needed_stackspace : ident -> nat .

(** Evaluation of a function invocation: [eval_funcall ge m f args t m' res]
  means that the function [f], applied to the arguments [args] in
  memory state [m], returns the value [res] in modified memory state [m'].
  [t] is the trace of observable events generated during the invocation.
*)

Inductive eval_funcall:
        mem -> fundef -> list expr_sym -> trace ->
        mem -> expr_sym -> Prop :=
  | eval_funcall_internal:
      forall m f vargs m1 sp e t e2 m2 out vres m3 m4 m',
        Mem.alloc m 0 ( f.(fn_stackspace)) Normal = Some (m1, sp) ->
        reserve_boxes m1 (needed_stackspace f.(fn_id)) = Some m' ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      exec_stmt f sp e m' f.(fn_body) t e2 m2 out ->
      outcome_result_value out f.(fn_sig).(sig_res) vres ->
      outcome_free_mem out m2 sp ( f.(fn_stackspace) ) m3 ->
      outcome_free_mem_extra out m3 (needed_stackspace (fn_id f)) m4 ->
      eval_funcall m (Internal f) vargs t m4 vres
  | eval_funcall_external:
      forall ef m args t res m',
      external_call ef ge args m t res m' ->
      eval_funcall m (External ef) args t m' res

(** Execution of a statement: [exec_stmt ge f sp e m s t e' m' out]
  means that statement [s] executes with outcome [out].
  [e] is the initial environment and [m] is the initial memory state.
  [e'] is the final environment, reflecting variable assignments performed
  by [s].  [m'] is the final memory state, reflecting memory stores
  performed by [s].  [t] is the trace of I/O events performed during
  the execution.  The other parameters are as in [eval_expr]. *)

with exec_stmt:
       function -> 
       block ->
         env -> mem -> stmt -> trace ->
         env -> mem -> outcome -> Prop :=
  | exec_Sskip:
      forall f sp e m,
      exec_stmt f sp e m Sskip E0 e m Out_normal
  | exec_Sassign:
      forall f sp e m id a v,
      eval_expr ge sp e m a v ->
      exec_stmt f sp e m (Sassign id a) E0 (PTree.set id v e) m Out_normal
  | exec_Sstore:
      forall f sp e m chunk addr a vaddr v m',
      eval_expr ge sp e m addr vaddr ->
      eval_expr ge sp e m a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      exec_stmt f sp e m (Sstore chunk addr a) E0 e m' Out_normal
  | exec_Scall:
      forall f sp e m optid sig a bl vf vargs fd t m' vres e',
      eval_expr ge sp e m a vf ->
      eval_exprlist ge sp e m bl vargs ->
      Genv.find_funct m ge vf = Some fd ->
      funsig fd = sig ->
      eval_funcall m fd vargs t m' vres ->
      e' = set_optvar optid vres e ->
      exec_stmt f sp e m (Scall optid sig a bl) t e' m' Out_normal
  | exec_Sbuiltin:
      forall f sp e m optid ef bl t m' vargs vres e',
      eval_exprlist ge sp e m bl vargs ->
      external_call ef ge vargs m t vres m' ->
      e' = set_optvar optid vres e ->
      exec_stmt f sp e m (Sbuiltin optid ef bl) t e' m' Out_normal
  | exec_Sifthenelse:
      forall f sp e m a s1 s2 v b t e' m' out,
      eval_expr ge sp e m a v ->
      Mem.mem_norm m v = Vint b ->
      exec_stmt f sp e m (if negb (Int.eq b Int.zero) then s1 else s2) t e' m' out ->
      exec_stmt f sp e m (Sifthenelse a s1 s2) t e' m' out
  | exec_Sseq_continue:
      forall f sp e m t s1 t1 e1 m1 s2 t2 e2 m2 out,
      exec_stmt f sp e m s1 t1 e1 m1 Out_normal ->
      exec_stmt f sp e1 m1 s2 t2 e2 m2 out ->
      t = t1 ** t2 ->
      exec_stmt f sp e m (Sseq s1 s2) t e2 m2 out
  | exec_Sseq_stop:
      forall f sp e m t s1 s2 e1 m1 out,
      exec_stmt f sp e m s1 t e1 m1 out ->
      out <> Out_normal ->
      exec_stmt f sp e m (Sseq s1 s2) t e1 m1 out
  | exec_Sloop_loop:
      forall f sp e m s t t1 e1 m1 t2 e2 m2 out,
      exec_stmt f sp e m s t1 e1 m1 Out_normal ->
      exec_stmt f sp e1 m1 (Sloop s) t2 e2 m2 out ->
      t = t1 ** t2 ->
      exec_stmt f sp e m (Sloop s) t e2 m2 out
  | exec_Sloop_stop:
      forall f sp e m t s e1 m1 out,
      exec_stmt f sp e m s t e1 m1 out ->
      out <> Out_normal ->
      exec_stmt f sp e m (Sloop s) t e1 m1 out
  | exec_Sblock:
      forall f sp e m s t e1 m1 out,
      exec_stmt f sp e m s t e1 m1 out ->
      exec_stmt f sp e m (Sblock s) t e1 m1 (outcome_block out)
  | exec_Sexit:
      forall f sp e m n,
      exec_stmt f sp e m (Sexit n) E0 e m (Out_exit n)
  | exec_Sswitch:
      forall f sp e m islong a cases default v n,
      eval_expr ge sp e m a v ->
      switch_argument m islong v n ->
      exec_stmt f sp e m (Sswitch islong a cases default)
                E0 e m (Out_exit (switch_target n default cases))
  | exec_Sreturn_none:
      forall f sp e m,
      exec_stmt f sp e m (Sreturn None) E0 e m (Out_return None)
  | exec_Sreturn_some:
      forall f sp e m a v,
      eval_expr ge sp e m a v ->
      exec_stmt f sp e m (Sreturn (Some a)) E0 e m (Out_return (Some v))
  | exec_Stailcall:
      forall f sp e m sig a bl vf vargs fd t m' m'' vres m''',
      eval_expr ge sp e m a vf ->
      eval_exprlist ge sp e m bl vargs ->
      Genv.find_funct m'' ge vf = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 ( f.(fn_stackspace)) = Some m' ->
      release_boxes m' (needed_stackspace (fn_id f)) = Some m'' ->
      eval_funcall m'' fd vargs t m''' vres ->
      exec_stmt f sp e m (Stailcall sig a bl) t e m''' (Out_tailcall_return vres).

Scheme eval_funcall_ind2 := Minimality for eval_funcall Sort Prop
  with exec_stmt_ind2 := Minimality for exec_stmt Sort Prop.
Combined Scheme eval_funcall_exec_stmt_ind2 
  from eval_funcall_ind2, exec_stmt_ind2.

(** Coinductive semantics for divergence.
  [evalinf_funcall ge m f args t]
  means that the function [f] diverges when applied to the arguments [args] in
  memory state [m].  The infinite trace [t] is the trace of
  observable events generated during the invocation.
*)

CoInductive evalinf_funcall:
        mem -> fundef -> list expr_sym -> traceinf -> Prop :=
  | evalinf_funcall_internal:
      forall m f vargs m1 sp e t m',
        Mem.alloc m 0 (f.(fn_stackspace)) Normal = Some (m1, sp) ->
        reserve_boxes m1 (needed_stackspace f.(fn_id)) = Some m' ->
        set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
        execinf_stmt f sp e m' f.(fn_body) t ->
        evalinf_funcall m (Internal f) vargs t

(** [execinf_stmt ge sp e m s t] means that statement [s] diverges.
  [e] is the initial environment, [m] is the initial memory state,
  and [t] the trace of observable events performed during the execution. *)

with execinf_stmt:
         function -> block -> env -> mem -> stmt -> traceinf -> Prop :=
  | execinf_Scall:
      forall f sp e m optid sig a bl vf vargs fd t,
      eval_expr ge sp e m a vf ->
      eval_exprlist ge sp e m bl vargs ->
      Genv.find_funct m ge vf = Some fd ->
      funsig fd = sig ->
      evalinf_funcall m fd vargs t ->
      execinf_stmt f sp e m (Scall optid sig a bl) t
  | execinf_Sifthenelse:
      forall f sp e m a s1 s2 v b t,
      eval_expr ge sp e m a v ->
      Mem.mem_norm m v = Vint b ->
      execinf_stmt f sp e m (if negb (Int.eq b Int.zero) then s1 else s2) t ->
      execinf_stmt f sp e m (Sifthenelse a s1 s2) t
  | execinf_Sseq_1:
      forall f sp e m t s1 s2,
      execinf_stmt f sp e m s1 t ->
      execinf_stmt f sp e m (Sseq s1 s2) t
  | execinf_Sseq_2:
      forall f sp e m t s1 t1 e1 m1 s2 t2,
      exec_stmt f sp e m s1 t1 e1 m1 Out_normal ->
      execinf_stmt f sp e1 m1 s2 t2 ->
      t = t1 *** t2 ->
      execinf_stmt f sp e m (Sseq s1 s2) t
  | execinf_Sloop_body:
      forall f sp e m s t,
      execinf_stmt f sp e m s t ->
      execinf_stmt f sp e m (Sloop s) t
  | execinf_Sloop_loop:
      forall f sp e m s t t1 e1 m1 t2,
      exec_stmt f sp e m s t1 e1 m1 Out_normal ->
      execinf_stmt f sp e1 m1 (Sloop s) t2 ->
      t = t1 *** t2 ->
      execinf_stmt f sp e m (Sloop s) t
  | execinf_Sblock:
      forall f sp e m s t,
      execinf_stmt f sp e m s t ->
      execinf_stmt f sp e m (Sblock s) t
  | execinf_Stailcall:
      forall f sp e m sig a bl vf vargs fd m' t m'',
      eval_expr ge sp e m a vf ->
      eval_exprlist ge sp e m bl vargs ->
      Genv.find_funct m'' ge vf = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 (f.(fn_stackspace)) = Some m' ->
      release_boxes m' (needed_stackspace (fn_id f)) = Some m'' ->
      evalinf_funcall m'' fd vargs t ->
      execinf_stmt f sp e m (Stailcall sig a bl) t.

End NATURALSEM.

(** Big-step execution of a whole program *)

Inductive bigstep_program_terminates (p: program) ns sg : trace -> int -> Prop :=
  | bigstep_program_terminates_intro:
      forall b f m0 t m r e,
      let ge := Genv.globalenv p in
      Genv.init_mem fid sg p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      Mem.mem_norm m e = Vint r ->
      eval_funcall ge ns m0 f nil t m e ->
      bigstep_program_terminates p ns sg  t r.

Inductive bigstep_program_diverges (p: program) ns sg: traceinf -> Prop :=
  | bigstep_program_diverges_intro:
      forall b f m0 t,
      let ge := Genv.globalenv p in
      Genv.init_mem fid sg p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      evalinf_funcall ge ns m0 f nil t ->
      bigstep_program_diverges p ns sg t.

Definition bigstep_semantics (p: program) ns sg :=
  Bigstep_semantics (bigstep_program_terminates p ns sg)
                    (bigstep_program_diverges p ns sg).

(** ** Correctness of the big-step semantics with respect to the transition semantics *)

Section BIGSTEP_TO_TRANSITION.
 
Variable prog: program.
Let ge := Genv.globalenv prog.

Variable needed_stackspace : ident -> nat .


Inductive outcome_state_match
        (sp: block) (e: env) (m: mem) (f: function) (k: cont):
        outcome -> state -> Prop :=
  | osm_normal:
      outcome_state_match sp e m f k 
                          Out_normal
                          (State f Sskip k sp e m)
  | osm_exit: forall n,
      outcome_state_match sp e m f k 
                          (Out_exit n)
                          (State f (Sexit n) k sp e m)
  | osm_return_none: forall k',
      call_cont k' = call_cont k ->
      outcome_state_match sp e m f k 
                          (Out_return None)
                          (State f (Sreturn None) k' sp e m)
  | osm_return_some: forall k' a v,
      call_cont k' = call_cont k ->
      eval_expr ge sp e m a v ->
      outcome_state_match sp e m f k 
                          (Out_return (Some v))
                          (State f (Sreturn (Some a)) k' sp e m)
  | osm_tail: forall v,
      outcome_state_match sp e m f k
                          (Out_tailcall_return v)
                          (Returnstate v (call_cont k) m).

Remark is_call_cont_call_cont:
  forall k, is_call_cont (call_cont k).
Proof.
  induction k; simpl; auto.
Qed.

Remark call_cont_is_call_cont:
  forall k, is_call_cont k -> call_cont k = k.
Proof.
  destruct k; simpl; intros; auto || contradiction.
Qed.

Lemma eval_funcall_exec_stmt_steps:
  (forall m fd args t m' res,
   eval_funcall ge needed_stackspace m fd args t m' res ->
   forall k,
   is_call_cont k ->
   star (fun ge => step ge needed_stackspace) ge (Callstate fd args k m)
              t (Returnstate res k m'))
/\(forall f sp e m s t e' m' out,
   exec_stmt ge needed_stackspace f sp e m s t e' m' out ->
   forall k,
   exists S,
   star (fun ge => step ge needed_stackspace) ge (State f s k sp e m) t S
   /\ outcome_state_match sp e' m' f k out S).
Proof.
  apply eval_funcall_exec_stmt_ind2; intros.

- (* funcall internal *)
  destruct (H3 k) as [S [A B]]. 
  assert (call_cont k = k) by (apply call_cont_is_call_cont; auto).
  eapply star_left. econstructor; eauto. 
  eapply star_trans. eexact A.
  inversion B; clear B; subst out; simpl in *; simpl; try contradiction.
  + (* Out normal *)
    subst vres. apply star_one. eapply step_skip_call; eauto. 
  + (* Out_return None *)
    subst vres. replace k with (call_cont k') by congruence.
    apply star_one. eapply step_return_0; eauto.
  + (* Out_return Some *)
    destruct H4. subst vres.
    replace k with (call_cont k') by congruence.
    apply star_one. eapply step_return_1; eauto.
  + (* Out_tailcall_return *)
    subst vres. subst m3. rewrite H10. rewrite H8 in *. clear H8. subst. apply star_refl. 
  + reflexivity.
  + traceEq.

- (* funcall external *)
  apply star_one. constructor; auto. 

- (* skip *)
  econstructor; split.
  apply star_refl. 
  constructor.

- (* assign *)
  exists (State f Sskip k sp (PTree.set id v e) m); split.
  apply star_one. econstructor. auto.
  constructor.

- (* store *)
  econstructor; split.
  apply star_one. econstructor; eauto.
  constructor.

- (* call *)
  econstructor; split.
  eapply star_left. econstructor; eauto. 
  eapply star_right. apply H4. red; auto. 
  constructor. reflexivity. traceEq.
  subst e'. constructor.

- (* builtin *)
  econstructor; split.
  apply star_one. econstructor; eauto. 
  subst e'. constructor.

- (* ifthenelse *)
  destruct (H2 k) as [S [A B]].
  exists S; split.
  apply star_left with E0 (State f (if negb (Int.eq b Int.zero) then s1 else s2) k sp e m) t.
  econstructor; eauto. exact A.
  traceEq.
  auto.

- (* seq continue *)
  destruct (H0 (Kseq s2 k)) as [S1 [A1 B1]].
  destruct (H2 k) as [S2 [A2 B2]].
  inv B1.
  exists S2; split.
  eapply star_left. constructor. 
  eapply star_trans. eexact A1. 
  eapply star_left. constructor. eexact A2.
  reflexivity. reflexivity. traceEq.
  auto.

- (* seq stop *)
  destruct (H0 (Kseq s2 k)) as [S1 [A1 B1]].
  set (S2 :=
    match out with
    | Out_exit n => State f (Sexit n) k sp e1 m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. constructor. eapply star_trans. eexact A1.
  unfold S2; destruct out; try (apply star_refl).
  inv B1. apply star_one. constructor.
  reflexivity. traceEq.
  unfold S2; inv B1; congruence || simpl; constructor; auto.

- (* loop loop *)
  destruct (H0 (Kseq (Sloop s) k)) as [S1 [A1 B1]].
  destruct (H2 k) as [S2 [A2 B2]].
  inv B1.
  exists S2; split.
  eapply star_left. constructor. 
  eapply star_trans. eexact A1. 
  eapply star_left. constructor. eexact A2.
  reflexivity. reflexivity. traceEq.
  auto.

- (* loop stop *)
  destruct (H0 (Kseq (Sloop s) k)) as [S1 [A1 B1]].
  set (S2 :=
    match out with
    | Out_exit n => State f (Sexit n) k sp e1 m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. constructor. eapply star_trans. eexact A1.
  unfold S2; destruct out; try (apply star_refl).
  inv B1. apply star_one. constructor.
  reflexivity. traceEq.
  unfold S2; inv B1; congruence || simpl; constructor; auto.

- (* block *)
  destruct (H0 (Kblock k)) as [S1 [A1 B1]].
  set (S2 :=
    match out with
    | Out_normal => State f Sskip k sp e1 m1
    | Out_exit O => State f Sskip k sp e1 m1
    | Out_exit (S m) => State f (Sexit m) k sp e1 m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. constructor. eapply star_trans. eexact A1.
  unfold S2; destruct out; try (apply star_refl).
  inv B1. apply star_one. constructor.
  inv B1. apply star_one. destruct n; constructor.
  reflexivity. traceEq.
  unfold S2; inv B1; simpl; try constructor; auto.
  destruct n; constructor.

- (* exit *)
  econstructor; split. apply star_refl. constructor.

- (* switch *)
  econstructor; split.
  apply star_one. econstructor; eauto. constructor.

- (* return none *)
  econstructor; split. apply star_refl. constructor; auto.

- (* return some *)
  econstructor; split. apply star_refl. constructor; auto.

- (* tailcall *)
  econstructor; split.
  + eapply star_left. econstructor; eauto. 
  apply H6. apply is_call_cont_call_cont. traceEq.
  + econstructor. 
Qed.

Lemma eval_funcall_steps:
   forall m fd args t m' res,
   eval_funcall ge needed_stackspace m fd args t m' res ->
   forall k,
   is_call_cont k ->
   star (fun ge => step ge needed_stackspace) ge (Callstate fd args k m)
              t (Returnstate res k m').
Proof (proj1 eval_funcall_exec_stmt_steps).

Lemma exec_stmt_steps:
   forall f sp e m s t e' m' out,
   exec_stmt ge needed_stackspace f sp e m s t e' m' out ->
   forall k,
   exists S,
   star (fun ge => step ge needed_stackspace) ge (State f s k sp e m) t S
   /\ outcome_state_match sp e' m' f k out S.
Proof (proj2 eval_funcall_exec_stmt_steps).

Lemma evalinf_funcall_forever:
  forall m fd args T k,
  evalinf_funcall ge needed_stackspace m fd args T ->
  forever_plus (fun ge => step ge needed_stackspace) ge (Callstate fd args k m) T.
Proof.
  cofix CIH_FUN.
  assert (forall sp e m s T f k,
          execinf_stmt ge needed_stackspace f sp e m s T ->
          forever_plus (fun ge => step ge needed_stackspace) ge (State f s k sp e m) T).
  cofix CIH_STMT.
  intros. inv H.

- (* call *)
  eapply forever_plus_intro.
  apply plus_one. econstructor; eauto. 
  apply CIH_FUN. eauto. traceEq.

- (* ifthenelse *)
  eapply forever_plus_intro with (s2 := State f (if negb (Int.eq b Int.zero)  then s1 else s2) k sp e m).
  apply plus_one. econstructor; eauto. 
  apply CIH_STMT. eauto. traceEq.

- (* seq 1 *)
  eapply forever_plus_intro.
  apply plus_one. constructor.
  apply CIH_STMT. eauto. traceEq.

- (* seq 2 *)
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ _ H0 (Kseq s2 k))
  as [S [A B]]. inv B.
  eapply forever_plus_intro.
  eapply plus_left. constructor.
  eapply star_right. eexact A. constructor. 
  reflexivity. reflexivity.
  apply CIH_STMT. eauto. traceEq. 

- (* loop body *)
  eapply forever_plus_intro.
  apply plus_one. econstructor; eauto.
  apply CIH_STMT. eauto. traceEq.

- (* loop loop *)
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ _ H0 (Kseq (Sloop s0) k))
  as [S [A B]]. inv B.
  eapply forever_plus_intro.
  eapply plus_left. constructor.
  eapply star_right. eexact A. constructor. 
  reflexivity. reflexivity.
  apply CIH_STMT. eauto. traceEq.

- (* block *)
  eapply forever_plus_intro.
  apply plus_one. econstructor; eauto.
  apply CIH_STMT. eauto. traceEq.

- (* tailcall *)
  eapply forever_plus_intro.
  apply plus_one. econstructor; eauto. 
  apply CIH_FUN. eauto. traceEq.

- (* function call *)
  intros. inv H0.
  eapply forever_plus_intro.
  apply plus_one. econstructor; eauto.
  apply H. eauto. 
  traceEq.
Qed.

Theorem bigstep_semantics_sound:
  forall sg, 
    bigstep_sound
      (bigstep_semantics prog needed_stackspace sg)
      (semantics prog needed_stackspace sg).
Proof.
  constructor; intros.
- (* termination *)
  inv H. econstructor; econstructor.
  split. econstructor; eauto. 
  split. apply eval_funcall_steps. eauto. red; auto. 
  econstructor. auto.
- (* divergence *)
  inv H. econstructor.
  split. econstructor; eauto. 
  eapply forever_plus_forever.
  eapply evalinf_funcall_forever; eauto.
Qed.

End BIGSTEP_TO_TRANSITION.

