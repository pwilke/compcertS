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

(** The RTL intermediate language: abstract syntax and semantics.

  RTL stands for "Register Transfer Language". This is the first
  intermediate language after Cminor and CminorSel.
*)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory MemReserve.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.

Require Import Values_symbolictype.
Require Import Values_symbolic.
Require Import MemRel.
(** * Abstract syntax *)

(** RTL is organized as instructions, functions and programs.
  Instructions correspond roughly to elementary instructions of the
  target processor, but take their arguments and leave their results
  in pseudo-registers (also called temporaries in textbooks).
  Infinitely many pseudo-registers are available, and each function
  has its own set of pseudo-registers, unaffected by function calls.

  Instructions are organized as a control-flow graph: a function is
  a finite map from ``nodes'' (abstract program points) to instructions,
  and each instruction lists explicitly the nodes of its successors.
*)

Definition node := positive.

Inductive instruction: Type :=
  | Inop: node -> instruction
      (** No operation -- just branch to the successor. *)
  | Iop: operation -> list reg -> reg -> node -> instruction
      (** [Iop op args dest succ] performs the arithmetic operation [op]
          over the values of registers [args], stores the result in [dest],
          and branches to [succ]. *)
  | Iload: memory_chunk -> addressing -> list reg -> reg -> node -> instruction
      (** [Iload chunk addr args dest succ] loads a [chunk] quantity from
          the address determined by the addressing mode [addr] and the
          values of the [args] registers, stores the quantity just read
          into [dest], and branches to [succ]. *)
  | Istore: memory_chunk -> addressing -> list reg -> reg -> node -> instruction
      (** [Istore chunk addr args src succ] stores the value of register
          [src] in the [chunk] quantity at the
          the address determined by the addressing mode [addr] and the
          values of the [args] registers, then branches to [succ]. *)
  | Icall: signature -> reg + ident -> list reg -> reg -> node -> instruction
      (** [Icall sig fn args dest succ] invokes the function determined by
          [fn] (either a function pointer found in a register or a
          function name), giving it the values of registers [args] 
          as arguments.  It stores the return value in [dest] and branches
          to [succ]. *)
  | Itailcall: signature -> reg + ident -> list reg -> instruction
      (** [Itailcall sig fn args] performs a function invocation
          in tail-call position.  *)
  | Ibuiltin: external_function -> list reg -> reg -> node -> instruction
      (** [Ibuiltin ef args dest succ] calls the built-in function
          identified by [ef], giving it the values of [args] as arguments.
          It stores the return value in [dest] and branches to [succ]. *)
  | Icond: condition -> list reg -> node -> node -> instruction
      (** [Icond cond args ifso ifnot] evaluates the boolean condition
          [cond] over the values of registers [args].  If the condition
          is true, it transitions to [ifso].  If the condition is false,
          it transitions to [ifnot]. *)
  | Ijumptable: reg -> list node -> instruction
      (** [Ijumptable arg tbl] transitions to the node that is the [n]-th
          element of the list [tbl], where [n] is the signed integer
          value of register [arg]. *)
  | Ireturn: option reg -> instruction.
      (** [Ireturn] terminates the execution of the current function
          (it has no successor).  It returns the value of the given
          register, or [Vundef] if none is given. *)

Definition code: Type := PTree.t instruction.

Record function: Type := mkfunction {
  fn_id: ident;
  fn_sig: signature;
  fn_params: list reg;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node;
  fn_stacksize_pos: 0 <= fn_stacksize(* ; *)
  (* fn_stacksize_aligned: align fn_stacksize 8 = fn_stacksize  *)
}.

(** A function description comprises a control-flow graph (CFG) [fn_code]
    (a partial finite mapping from nodes to instructions).  As in Cminor,
    [fn_sig] is the function signature and [fn_stacksize] the number of bytes
    for its stack-allocated activation record.  [fn_params] is the list
    of registers that are bound to the values of arguments at call time.
    [fn_entrypoint] is the node of the first instruction of the function
    in the CFG.  [fn_code_wf] asserts that all instructions of the function
    have nodes no greater than [fn_nextpc]. *)

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

(** * Operational semantics *)

Definition genv := Genv.t fundef unit.
Definition regset := Regmap.t expr_sym.

Fixpoint init_regs (vl: list expr_sym) (rl: list reg) {struct rl} : regset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => Regmap.set r1 v1 (init_regs vs rs)
  | _, _ => Regmap.init (Eval Vundef)
  end.

(** The dynamic semantics of RTL is given in small-step style, as a 
  set of transitions between states.  A state captures the current
  point in the execution.  Three kinds of states appear in the transitions:

- [State cs f sp pc rs m] describes an execution point within a function.
  [f] is the current function.
  [sp] is the pointer to the stack block for its current activation
     (as in Cminor).
  [pc] is the current program point (CFG node) within the code [c].
  [rs] gives the current values for the pseudo-registers.
  [m] is the current memory state.
- [Callstate cs f args m] is an intermediate state that appears during
  function calls.
  [f] is the function definition that we are calling.
  [args] (a list of values) are the arguments for this call.
  [m] is the current memory state.
- [Returnstate cs v m] is an intermediate state that appears when a
  function terminates and returns to its caller.
  [v] is the return value and [m] the current memory state.

In all three kinds of states, the [cs] parameter represents the call stack.
It is a list of frames [Stackframe res f sp pc rs].  Each frame represents
a function call in progress.  
[res] is the pseudo-register that will receive the result of the call.
[f] is the calling function.
[sp] is its stack pointer.
[pc] is the program point for the instruction that follows the call.
[rs] is the state of registers in the calling function.
*)

Inductive stackframe : Type :=
  | Stackframe:
      forall (res: reg)            (**r where to store the result *)
             (f: function)         (**r calling function *)
             (sp: block)             (**r stack pointer in calling function *)
             (pc: node)            (**r program point in calling function *)
             (rs: regset),         (**r register state in calling function *)
      stackframe.

Inductive state : Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r current function *)
             (sp: block)                (**r stack pointer *)
             (pc: node)               (**r current program point in [c] *)
             (rs: regset)             (**r register state *)
             (m: mem),                (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (args: list expr_sym)         (**r arguments to the call *)
             (m: mem),                (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (v: expr_sym)                 (**r return value for the call *)
             (m: mem),                (**r memory state *)
      state.

Section RELSEM.

  Variable ge: genv.

  Variable needed_stackspace : ident -> nat .


Definition find_function (m:mem)
      (ros: reg + ident) (rs: regset) : option fundef :=
  match ros with
    | inl r => Genv.find_funct m ge rs#r
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
  generalize (rel_norm _ wf_mr_ld wf_mr_norm_ld _ _ _ _ MLD (Val.lessdef_refl (ls1 # r))).
  rewrite lessdef_val.
  unfold Mem.mem_norm; intro A; inv A; destr.
Qed.


(** The transitions are presented as an inductive predicate
  [step ge st1 t st2], where [ge] is the global environment,
  [st1] the initial state, [st2] the final state, and [t] the trace
  of system calls performed during this transition. *)

Inductive step: state -> trace -> state -> Prop :=
  | exec_Inop:
      forall s f sp pc rs m pc',
      (fn_code f)!pc = Some(Inop pc') ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m)
  | exec_Iop:
      forall s f sp pc rs m op args res pc' v,
        (fn_code f)!pc = Some(Iop op args res pc') ->
        eval_operation ge (Eval (Vptr sp Int.zero)) op rs##args = Some v ->
        step (State s f sp pc rs m)
             E0 (State s f sp pc' (rs#res <- v) m)
  | exec_Iload:
      forall s f sp pc rs m chunk addr args dst pc' a v ,
        (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
      eval_addressing ge (Eval (Vptr sp Int.zero)) addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (rs#dst <- v) m)
  | exec_Istore:
      forall s f sp pc rs m chunk addr args src pc' a m',
        (fn_code f)!pc = Some(Istore chunk addr args src pc') ->
        eval_addressing ge (Eval (Vptr sp Int.zero)) addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m')
  | exec_Icall:
      forall s f sp pc rs m sig ros args res pc' fd,
      (fn_code f)!pc = Some(Icall sig ros args res pc') ->
      find_function m ros rs = Some fd ->
      funsig fd = sig ->
      step (State s f sp pc rs m)
        E0 (Callstate (Stackframe res f sp pc' rs :: s) fd rs##args m)
  | exec_Itailcall:
      forall s f stk pc rs m sig ros args fd m' m'',
      (fn_code f)!pc = Some(Itailcall sig ros args) ->
      find_function m'' ros rs = Some fd ->
      funsig fd = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      release_boxes m' (needed_stackspace (fn_id f)) = Some m'' -> 
      step (State s f stk pc rs m)
        E0 (Callstate s fd rs##args m'')
  | exec_Ibuiltin:
      forall s f sp pc rs m ef args res pc' t v m',
        (fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
      external_call ef ge rs##args m t v m' ->
      step (State s f sp pc rs m)
         t (State s f sp pc' (rs#res <- v) m')
  | exec_Icond:
      forall s f sp pc rs m cond args ifso ifnot b pc' vb,
        (fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
        eval_condition cond rs##args = Some b ->
        Mem.mem_norm m b = Vint vb ->
        pc' = (if negb (Int.eq vb Int.zero) then ifso else ifnot) ->
        step (State s f sp pc rs m)
             E0 (State s f sp pc' rs m)
  | exec_Ijumptable:
      forall s f sp pc rs m arg tbl n pc',
        (fn_code f)!pc = Some(Ijumptable arg tbl) ->
      Mem.mem_norm m rs#arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc' ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m)
  | exec_Ireturn:
      forall s f stk pc rs m or m' res m'',
      (fn_code f)!pc = Some(Ireturn or) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      release_boxes m' (needed_stackspace (fn_id f)) = Some m'' -> 
      regmap_optget or (Eval Vundef) rs = res ->
      step (State s f stk pc rs m)
        E0 (Returnstate s res m'')
  | exec_function_internal:
      forall s f args m m1 m' stk,
        Mem.alloc m 0 f.(fn_stacksize) Normal  = Some (m1, stk) ->
        reserve_boxes m1 (needed_stackspace f.(fn_id)) = Some m' ->
      step (Callstate s (Internal f) args m)
        E0 (State s
                  f
                  stk
                  f.(fn_entrypoint)
                  (init_regs args f.(fn_params))
                  m')
  | exec_function_external:
      forall s ef args res t m m',
      external_call ef ge args m t res m' ->
      step (Callstate s (External ef) args m)
         t (Returnstate s res m')
  | exec_return:
      forall res f sp pc rs s vres m,
      step (Returnstate (Stackframe res f sp pc rs :: s) vres m)
        E0 (State s f sp pc (rs#res <- vres) m).

Lemma exec_Iop':
  forall s f sp pc rs m op args res pc' rs' v ,
    (fn_code f)!pc = Some(Iop op args res pc') ->
  eval_operation ge (Eval (Vptr sp Int.zero)) op rs##args = Some v ->
  rs' = (rs#res <- v) ->
  step (State s f sp pc rs m)
    E0 (State s f sp pc' rs' m).
Proof.
  intros. subst rs'. eapply exec_Iop; eauto.
Qed.

Lemma exec_Iload':
  forall s f sp pc rs m chunk addr args dst pc' rs' a v,
    (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
  eval_addressing ge (Eval (Vptr sp Int.zero)) addr rs##args = Some a ->
  Mem.loadv chunk m a = Some v ->
  rs' = (rs#dst <- v) ->
  step (State s f sp pc rs m)
    E0 (State s f sp pc' rs' m).
Proof.
  intros. subst rs'. eapply exec_Iload; eauto.
Qed.

End RELSEM.

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty call stack. *)

Inductive initial_state (p: program) sg: state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem fid sg p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      initial_state p sg (Callstate nil f nil m0).

(** A final state is a [Returnstate] with an empty call stack. *)

Inductive final_state: state -> int -> Prop :=
| final_state_intro: forall r m b,
                       Mem.mem_norm m r = Vint b ->
                       final_state (Returnstate nil r m) b.

(** The small-step semantics for a program. *)

Definition semantics (p: program) ns sg  :=
  Semantics (fun ge => step ge ns ) (initial_state p sg) final_state (Genv.globalenv p).

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
  exists (State s0 f sp pc' (rs#res <- vres2) m2). eapply exec_Ibuiltin; eauto.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]]. 
  exists (Returnstate s0 vres2 m2). econstructor; eauto.
(* trace length *)
  red; intros; inv H; simpl; try omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
Qed.

(** * Operations on RTL abstract syntax *)

(** Transformation of a RTL function instruction by instruction.
  This applies a given transformation function to all instructions
  of a function and constructs a transformed function from that. *)

Section TRANSF.

Variable transf: node -> instruction -> instruction.

Definition transf_function (f: function) : function :=
  mkfunction
    f.(fn_id)
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (PTree.map transf f.(fn_code))
    f.(fn_entrypoint)
        f.(fn_stacksize_pos).

End TRANSF.

(** Computation of the possible successors of an instruction.
  This is used in particular for dataflow analyses. *)

Definition successors_instr (i: instruction) : list node :=
  match i with
  | Inop s => s :: nil
  | Iop op args res s => s :: nil
  | Iload chunk addr args dst s => s :: nil
  | Istore chunk addr args src s => s :: nil
  | Icall sig ros args res s => s :: nil
  | Itailcall sig ros args => nil
  | Ibuiltin ef args res s => s :: nil
  | Icond cond args ifso ifnot => ifso :: ifnot :: nil
  | Ijumptable arg tbl => tbl
  | Ireturn optarg => nil
  end.

Definition successors_map (f: function) : PTree.t (list node) :=
  PTree.map1 successors_instr f.(fn_code).

(** The registers used by an instruction *)

Definition instr_uses (i: instruction) : list reg :=
  match i with
  | Inop s => nil
  | Iop op args res s => args
  | Iload chunk addr args dst s => args
  | Istore chunk addr args src s => src :: args
  | Icall sig (inl r) args res s => r :: args
  | Icall sig (inr id) args res s => args
  | Itailcall sig (inl r) args => r :: args
  | Itailcall sig (inr id) args => args
  | Ibuiltin ef args res s => args
  | Icond cond args ifso ifnot => args
  | Ijumptable arg tbl => arg :: nil
  | Ireturn None => nil
  | Ireturn (Some arg) => arg :: nil
  end.

(** The register defined by an instruction, if any *)

Definition instr_defs (i: instruction) : option reg :=
  match i with
  | Inop s => None
  | Iop op args res s => Some res
  | Iload chunk addr args dst s => Some dst
  | Istore chunk addr args src s => None
  | Icall sig ros args res s => Some res
  | Itailcall sig ros args => None
  | Ibuiltin ef args res s => Some res
  | Icond cond args ifso ifnot => None
  | Ijumptable arg tbl => None
  | Ireturn optarg => None
  end.

(** Maximum PC (node number) in the CFG of a function.  All nodes of
  the CFG of [f] are between 1 and [max_pc_function f] (inclusive). *)

Definition max_pc_function (f: function) :=
  PTree.fold (fun m pc i => Pmax m pc) f.(fn_code) 1%positive.

Lemma max_pc_function_sound:
  forall f pc i, f.(fn_code)!pc = Some i -> Ple pc (max_pc_function f).
Proof.
  intros until i. unfold max_pc_function. 
  apply PTree_Properties.fold_rec with (P := fun c m => c!pc = Some i -> Ple pc m).
  (* extensionality *)
  intros. apply H0. rewrite H; auto. 
  (* base case *)
  rewrite PTree.gempty. congruence.
  (* inductive case *)
  intros. rewrite PTree.gsspec in H2. destruct (peq pc k). 
  inv H2. xomega. 
  apply Ple_trans with a. auto. xomega.
Qed.

(** Maximum pseudo-register mentioned in a function.  All results or arguments
  of an instruction of [f], as well as all parameters of [f], are between
  1 and [max_reg_function] (inclusive). *)

Definition max_reg_instr (m: positive) (pc: node) (i: instruction) :=
  match i with
  | Inop s => m
  | Iop op args res s => fold_left Pmax args (Pmax res m)
  | Iload chunk addr args dst s => fold_left Pmax args (Pmax dst m)
  | Istore chunk addr args src s => fold_left Pmax args (Pmax src m)
  | Icall sig (inl r) args res s => fold_left Pmax args (Pmax r (Pmax res m))
  | Icall sig (inr id) args res s => fold_left Pmax args (Pmax res m)
  | Itailcall sig (inl r) args => fold_left Pmax args (Pmax r m)
  | Itailcall sig (inr id) args => fold_left Pmax args m
  | Ibuiltin ef args res s => fold_left Pmax args (Pmax res m)
  | Icond cond args ifso ifnot => fold_left Pmax args m
  | Ijumptable arg tbl => Pmax arg m
  | Ireturn None => m
  | Ireturn (Some arg) => Pmax arg m
  end.

Definition max_reg_function (f: function) :=
  Pmax
    (PTree.fold max_reg_instr f.(fn_code) 1%positive)
    (fold_left Pmax f.(fn_params) 1%positive).

Remark max_reg_instr_ge:
  forall m pc i, Ple m (max_reg_instr m pc i).
Proof.
  intros. 
  assert (X: forall l n, Ple m n -> Ple m (fold_left Pmax l n)).
  { induction l; simpl; intros. 
    auto.
    apply IHl. xomega. }
  destruct i; simpl; try (destruct s0); try (apply X); try xomega.
  destruct o; xomega.
Qed.

Remark max_reg_instr_def:
  forall m pc i r, instr_defs i = Some r -> Ple r (max_reg_instr m pc i).
Proof.
  intros.
  assert (X: forall l n, Ple r n -> Ple r (fold_left Pmax l n)).
  { induction l; simpl; intros. xomega. apply IHl. xomega. }
  destruct i; simpl in *; inv H.
- apply X. xomega.
- apply X. xomega.
- destruct s0; apply X; xomega.
- apply X. xomega.
Qed.

Remark max_reg_instr_uses:
  forall m pc i r, In r (instr_uses i) -> Ple r (max_reg_instr m pc i).
Proof.
  intros. 
  assert (X: forall l n, In r l \/ Ple r n -> Ple r (fold_left Pmax l n)).
  { induction l; simpl; intros. 
    tauto.
    apply IHl. destruct H0 as [[A|A]|A]. right; subst; xomega. auto. right; xomega. }
  destruct i; simpl in *; try (destruct s0); try (apply X; auto).
- contradiction.
- destruct H. right; subst; xomega. auto.
- destruct H. right; subst; xomega. auto.
- destruct H. right; subst; xomega. auto.
- intuition. subst; xomega.
- destruct o; simpl in H; intuition. subst; xomega.
Qed.

Lemma max_reg_function_def:
  forall f pc i r,
  f.(fn_code)!pc = Some i -> instr_defs i = Some r -> Ple r (max_reg_function f).
Proof.
  intros. 
  assert (Ple r (PTree.fold max_reg_instr f.(fn_code) 1%positive)).
  {  revert H. 
     apply PTree_Properties.fold_rec with
       (P := fun c m => c!pc = Some i -> Ple r m).
   - intros. rewrite H in H1; auto.
   - rewrite PTree.gempty; congruence.
   - intros. rewrite PTree.gsspec in H3. destruct (peq pc k). 
     + inv H3. eapply max_reg_instr_def; eauto. 
     + apply Ple_trans with a. auto. apply max_reg_instr_ge.
  }
  unfold max_reg_function. xomega. 
Qed.

Lemma max_reg_function_use:
  forall f pc i r,
  f.(fn_code)!pc = Some i -> In r (instr_uses i) -> Ple r (max_reg_function f).
Proof.
  intros. 
  assert (Ple r (PTree.fold max_reg_instr f.(fn_code) 1%positive)).
  {  revert H. 
     apply PTree_Properties.fold_rec with
       (P := fun c m => c!pc = Some i -> Ple r m).
   - intros. rewrite H in H1; auto.
   - rewrite PTree.gempty; congruence.
   - intros. rewrite PTree.gsspec in H3. destruct (peq pc k). 
     + inv H3. eapply max_reg_instr_uses; eauto. 
     + apply Ple_trans with a. auto. apply max_reg_instr_ge.
  }
  unfold max_reg_function. xomega. 
Qed.

Lemma max_reg_function_params:
  forall f r, In r f.(fn_params) -> Ple r (max_reg_function f).
Proof.
  intros.
  assert (X: forall l n, In r l \/ Ple r n -> Ple r (fold_left Pmax l n)).
  { induction l; simpl; intros. 
    tauto.
    apply IHl. destruct H0 as [[A|A]|A]. right; subst; xomega. auto. right; xomega. }
  assert (Y: Ple r (fold_left Pmax f.(fn_params) 1%positive)).
  { apply X; auto. }
  unfold max_reg_function. xomega.
Qed.
