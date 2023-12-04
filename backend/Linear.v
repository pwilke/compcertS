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

(** The Linear intermediate language: abstract syntax and semantcs *)

(** The Linear language is a variant of LTL where control-flow is not
    expressed as a graph of basic blocks, but as a linear list of
    instructions with explicit labels and ``goto'' instructions. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory MemReserve.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import Conventions.
Require Import Values_symbolic.
Require Import Values_symbolictype.
Require Import MemRel.

(** * Abstract syntax *)

Definition label := positive.

Inductive instruction: Type :=
  | Lgetstack: slot -> Z -> typ -> mreg -> instruction
  | Lsetstack: mreg -> slot -> Z -> typ -> instruction
  | Lop: operation -> list mreg -> mreg -> instruction
  | Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Lcall: signature -> mreg + ident -> instruction
  | Ltailcall: signature -> mreg + ident -> instruction
  | Lbuiltin: external_function -> list mreg -> list mreg -> instruction
  (* | Lannot: external_function -> list loc -> instruction *)
  | Llabel: label -> instruction
  | Lgoto: label -> instruction
  | Lcond: condition -> list mreg -> label -> instruction
  | Ljumptable: mreg -> list label -> instruction
  | Lreturn: instruction.

Definition code: Type := list instruction.

Record function: Type := mkfunction {
  fn_id: ident;
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: code;
  fn_stacksize_pos: 0 <= fn_stacksize;
  fn_stacksize_aligned: align fn_stacksize 8 = fn_stacksize
}.

Definition fundef := AST.fundef function.

Definition fid f :=
  match f with
    Internal f => Some (fn_id f)
  | _ => None
  end.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Definition genv := Genv.t fundef unit.
Definition locset := Locmap.t.

(** * Operational semantics *)

(** Looking up labels in the instruction list.  *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Llabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Llabel lbl else instr <> Llabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

(** [find_label lbl c] returns a list of instruction, suffix of the
  code [c], that immediately follows the [Llabel lbl] pseudo-instruction.
  If the label [lbl] is multiply-defined, the first occurrence is
  retained.  If the label [lbl] is not defined, [None] is returned. *)

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label lbl i1 then Some il else find_label lbl il
  end.

Section RELSEM.

  Variable ge: genv.
  Variable needed_stackspace : ident -> nat .

Definition find_function (m:mem) (ros: mreg + ident) (rs: locset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct m ge (rs (R r))
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.


Lemma find_function_lessdef:
  forall m m' ros' ls1 tfd,
    mem_lessdef m m' ->
    find_function m ros' ls1 = Some tfd ->
    find_function m' ros' ls1 = Some tfd.
Proof.
  intros m m' ros' ls1 tfd MLD FF.
  revert FF; unfold find_function.
  des ros'.
  revert FF.
  unfold Genv.find_funct.
  generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ MLD (Val.lessdef_refl (ls1 (R m0)))).
  rewrite lessdef_val.
  intro A; inv A; destr.
Qed.


(** Linear execution states. *)

Inductive stackframe: Type :=
  | Stackframe:
      forall (f: function)         (**r calling function *)
        (sp: expr_sym)             (**r stack pointer in calling function *)
             (rs: locset)          (**r location state in calling function *)
             (c: code),            (**r program point in calling function *)
      stackframe.

Inductive state: Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r function currently executing *)
             (sp: expr_sym)                (**r stack pointer *)
             (c: code)                (**r current program point *)
             (rs: locset)             (**r location state *)
             (m: mem),                (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (rs: locset)             (**r location state at point of call *)
             (m: mem),                (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (rs: locset)             (**r location state at point of return *)
             (m: mem),                (**r memory state *)
      state.

(** [parent_locset cs] returns the mapping of values for locations
  of the caller function. *)
Definition parent_locset (stack: list stackframe) : locset :=
  match stack with
  | nil => Locmap.init 
  | Stackframe f sp ls c :: stack' => ls
  end.

Inductive step: state -> trace -> state -> Prop :=
  | exec_Lgetstack:
      forall s f sp sl ofs ty dst b rs m rs' v,
        (rs (S sl ofs ty)) = v ->
      rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_getstack sl) rs) ->
      step (State s f sp (Lgetstack sl ofs ty dst :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Lsetstack:
      forall s f sp src sl ofs ty b rs m rs' v,
        (rs (R src)) = v ->
      rs' = Locmap.set (S sl ofs ty) v (undef_regs (destroyed_by_setstack ty) rs) ->
      step (State s f sp (Lsetstack src sl ofs ty :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Lop:
      forall s f sp op args res b rs m v rs' args',
        (reglist rs args) = args' ->
      eval_operation ge sp op args' = Some v ->
      rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
      step (State s f sp (Lop op args res :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Lload:
      forall s f sp chunk addr args dst b rs m a v rs' args',
        reglist rs args = args' ->
      eval_addressing ge sp addr args' = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
      step (State s f sp (Lload chunk addr args dst :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Lstore:
      forall s f sp chunk addr args src b rs m m' a rs' args' v,
        reglist rs args =  args' ->
      eval_addressing ge sp addr args' = Some a ->
      (rs (R src)) = v ->
      Mem.storev chunk m a v = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step (State s f sp (Lstore chunk addr args src :: b) rs m)
        E0 (State s f sp b rs' m')
  | exec_Lcall:
      forall s f sp sig ros b rs m f',
      find_function m ros rs = Some f' ->
      sig = funsig f' ->
      step (State s f sp (Lcall sig ros :: b) rs m)
        E0 (Callstate (Stackframe f sp rs b:: s) f' rs m)
  | exec_Ltailcall:
      forall s f stk sig ros b rs m rs' f' m' m'',
      rs' = return_regs (parent_locset s) rs ->
      find_function m'' ros rs' = Some f' ->
      sig = funsig f' ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      release_boxes m' (needed_stackspace (fn_id f)) = Some m'' -> 
      step (State s f (Eval (Vptr stk Int.zero)) (Ltailcall sig ros :: b) rs m)
        E0 (Callstate s f' rs' m'')
  | exec_Lbuiltin:
      forall s f sp rs m ef args res b t vl rs' m' args',
        reglist rs args = args' ->
      external_call' ef ge args' m t vl m' ->
      rs' = Locmap.setlist (map R res) vl (undef_regs (destroyed_by_builtin ef) rs) ->
      step (State s f sp (Lbuiltin ef args res :: b) rs m)
         t (State s f sp b rs' m')
  (* | exec_Lannot: *)
  (*     forall s f sp rs m ef args b t v m' args', *)
  (*       map rs args = args' -> *)
  (*     external_call' ef ge args' m t v m' -> *)
  (*     step (State s f sp (Lannot ef args :: b) rs m) *)
  (*        t (State s f sp b rs m') *)
  | exec_Llabel:
      forall s f sp lbl b rs m,
      step (State s f sp (Llabel lbl :: b) rs m)
        E0 (State s f sp b rs m)
  | exec_Lgoto:
      forall s f sp lbl b rs m b',
      find_label lbl f.(fn_code) = Some b' ->
      step (State s f sp (Lgoto lbl :: b) rs m)
        E0 (State s f sp b' rs m)
  | exec_Lcond_true:
      forall s f sp cond args lbl b rs m rs' b' bcond args',
        reglist rs args = args' ->
      eval_condition cond args' = Some bcond ->
      Mem.mem_norm m  bcond  = Vtrue ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      find_label lbl f.(fn_code) = Some b' ->
      step (State s f sp (Lcond cond args lbl :: b) rs m)
        E0 (State s f sp b' rs' m)
  | exec_Lcond_false:
      forall s f sp cond args lbl b rs m rs' bcond args',
        reglist rs args = args' ->
      eval_condition cond args' = Some bcond ->
      Mem.mem_norm m bcond = Vfalse ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (State s f sp (Lcond cond args lbl :: b) rs m)
        E0 (State s f sp b rs' m)
  | exec_Ljumptable:
      forall s f sp arg tbl b rs m n lbl b' rs' v,
        rs (R arg) = v ->
      Mem.mem_norm m v = (Vint n) ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      find_label lbl f.(fn_code) = Some b' ->
      rs' = undef_regs (destroyed_by_jumptable) rs ->
      step (State s f sp (Ljumptable arg tbl :: b) rs m)
        E0 (State s f sp b' rs' m)
  | exec_Lreturn:
      forall s f stk b rs m m' m'',
        Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      release_boxes m' (needed_stackspace (fn_id f)) = Some m'' -> 
      step (State s f (Eval (Vptr stk Int.zero)) (Lreturn :: b) rs m)
        E0 (Returnstate s (return_regs (parent_locset s) rs) m'')
  | exec_function_internal:
      forall s f rs m rs' m' stk m1,
        Mem.alloc m 0 f.(fn_stacksize) Normal = Some (m1, stk) ->
        reserve_boxes m1 (needed_stackspace f.(fn_id)) = Some m' ->
      rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
      step (Callstate s (Internal f) rs m)
        E0 (State s f (Eval (Vptr stk Int.zero)) f.(fn_code) rs' m')
  | exec_function_external:
      forall s ef args res rs1 rs2 m t m',
        args = map rs1 (loc_arguments (ef_sig ef)) ->
      external_call' ef ge args m t res m' ->
      rs2 = Locmap.setlist (map R (loc_result (ef_sig ef))) res rs1 ->
      step (Callstate s (External ef) rs1 m)
         t (Returnstate s rs2 m')
  | exec_return:
      forall s f sp rs0 c rs m,
      step (Returnstate (Stackframe f sp rs0 c :: s) rs m)
        E0 (State s f sp c rs m).

End RELSEM.

Inductive initial_state (p: program) sg: state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem fid sg p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      initial_state p sg (Callstate nil f (Locmap.init ) m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r retcode v,
      loc_result signature_main = r :: nil ->
      (rs (R r)) = v ->
      Mem.mem_norm m v = Vint retcode ->
      final_state (Returnstate nil rs m) retcode.

Definition semantics (p: program) ns sg :=
  Semantics (fun ge => step ge ns) (initial_state p sg) final_state (Genv.globalenv p).
