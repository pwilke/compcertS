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

(** The Clight language: a simplified version of Compcert C where all
  expressions are pure and assignments and function calls are
  statements, not expressions. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory MemReserve.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import CopGeneric.
Require Import Cop.
Require Import Values_symbolictype.
Require Import Values_symbolic.
Require Import VarSort.
Require Export ClightSyntax.



(** ** Functions *)

(** A function definition is composed of its return type ([fn_return]),
  the names and types of its parameters ([fn_params]), the names
  and types of its local variables ([fn_vars]), and the body of the
  function (a statement, [fn_body]). *)

Record function : Type :=
  mkfunction {
  fn_id: ident;                            
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_temps: list (ident * type);
  fn_body: statement;
  fn_sl_save : nat
}.

Definition var_names (vars: list(ident * type)) : list ident :=
  List.map (@fst ident type) vars.

(** Functions can either be defined ([Internal]) or declared as
  external functions ([External]). *)

Inductive fundef : Type :=
  | Internal: function -> fundef
  | External: external_function -> typelist -> type -> calling_convention -> fundef.

(** The type of a function definition. *)

Definition type_of_function (f: function) : type :=
  Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External id args res cc => Tfunction args res cc
  end.

(** ** Programs *)

(** A program is a collection of named functions, plus a collection
  of named global variables, carrying their types and optional initialization 
  data.  See module [AST] for more details. *)

Definition program : Type := AST.program fundef type.

(** * Operational semantics *)

(** The semantics uses two environments.  The global environment
  maps names of functions and global variables to memory block references,
  and function pointers to their definitions.  (See module [Globalenvs].) *)

Definition genv := Genv.t fundef type.

(** The local environment maps local variables to block references and
  types.  The current value of the variable is stored in the
  associated memory block. *)

Definition env := PTree.t (block * type). (* map variable -> location & type *)

Definition empty_env: env := (PTree.empty (block * type)).

(** The temporary environment maps local temporaries to values. *)

Definition temp_env := PTree.t expr_sym.

(** [deref_loc ty m b ofs v] computes the value of a datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  If the type [ty] indicates an access by value, the corresponding
  memory load is performed.  If the type [ty] indicates an access by
  reference or by copy, the pointer [Vptr b ofs] is returned. *)

Inductive deref_loc (ty: type) (m: mem) (ptr: expr_sym) : expr_sym -> Prop :=
  | deref_loc_value: forall chunk v,
      access_mode ty = By_value chunk ->
      Mem.loadv chunk m ptr = Some v ->
      deref_loc ty m ptr v
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m ptr ptr
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ty m ptr ptr. 

(** Symmetrically, [assign_loc ty m b ofs v m'] returns the
  memory state after storing the value [v] in the datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  This is allowed only if [ty] indicates an access by value or by copy.
  [m'] is the updated memory state. *)

Inductive assign_loc (ty: type) (m: mem) (* (b: block) (ofs: int) *) (addr: expr_sym):
  expr_sym -> mem -> Prop :=
  | assign_loc_value: forall v chunk m'
                        (AM: access_mode ty = By_value chunk)
                        (STOREV: Mem.storev chunk m addr v = Some m'),
      assign_loc ty m addr v m'
  | assign_loc_copy: forall b ofs b' ofs' bytes m' v
                       (AM: access_mode ty = By_copy)
                       (Spos: sizeof ty > 0)
                       (AL: (alignof_blockcopy ty | Int.unsigned ofs'))
                       (AL': (alignof_blockcopy ty | Int.unsigned ofs))
                       (NOOV: b' <> b \/ Int.unsigned ofs' = Int.unsigned ofs
                              \/ Int.unsigned ofs' + sizeof ty <= Int.unsigned ofs
                              \/ Int.unsigned ofs + sizeof ty <= Int.unsigned ofs')
                       (LB: Mem.loadbytes m b' (Int.unsigned ofs') (sizeof ty) = Some bytes)
                       (SB: Mem.storebytes m b (Int.unsigned ofs) bytes = Some m')
                       (MNv: Mem.mem_norm m v = Vptr b' ofs')
                       (MNaddr: Mem.mem_norm m addr = Vptr b ofs),
      assign_loc ty m addr v m'
  | assign_loc_copy_0: forall v
                         (AM: access_mode ty = By_copy)
                         (SZnull: sizeof ty = 0),
      assign_loc ty m addr v m.


(** Allocation of function-local variables.
  [alloc_variables e1 m1 vars e2 m2] allocates one memory block
  for each variable declared in [vars], and associates the variable
  name with this block.  [e1] and [m1] are the initial local environment
  and memory state.  [e2] and [m2] are the final local environment
  and memory state. *)

Inductive alloc_variables: env -> mem ->
                           list (ident * type) ->
                           env -> mem -> Prop :=
  | alloc_variables_nil:
      forall e m,
      alloc_variables e m nil e m
  | alloc_variables_cons:
      forall e m id ty vars m1 b1 m2 e2,
      Mem.alloc m 0 (sizeof ty) Normal = Some (m1, b1) ->
      alloc_variables (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
      alloc_variables e m ((id, ty) :: vars) e2 m2.

Definition size_vars (l: list (ident * type)) : Z :=
  List.fold_left
    (fun acc var => acc + align (sizeof (snd var)) 8) l 0.


(** Initialization of local variables that are parameters to a function.
  [bind_parameters e m1 params args m2] stores the values [args]
  in the memory blocks corresponding to the variables [params].
  [m1] is the initial memory state and [m2] the final memory state. *)

Inductive bind_parameters (e: env):
                           mem -> list (ident * type) -> list expr_sym ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall m,
      bind_parameters e m nil nil m
  | bind_parameters_cons:
      forall m id ty params v1 vl b m1 m2,
      PTree.get id e = Some(b, ty) ->
      assign_loc ty m (Eval (Vptr b Int.zero)) v1 m1 ->
      bind_parameters e m1 params vl m2 ->
      bind_parameters e m ((id, ty) :: params) (v1 :: vl) m2.

(** Initialization of temporary variables *)

Fixpoint create_undef_temps (temps: list (ident * type)) : temp_env :=
  match temps with
    | nil => PTree.empty expr_sym
    | (id, t) :: temps' => PTree.set id (Eval Vundef)
                                     (create_undef_temps temps')
 end.

(** Initialization of temporary variables that are parameters to a function. *)

Fixpoint bind_parameter_temps (formals: list (ident * type)) (args: list expr_sym)
                              (le: temp_env) : option temp_env :=
 match formals, args with
 | nil, nil => Some le
 | (id, t) :: xl, v :: vl => bind_parameter_temps xl vl (PTree.set id v le)
 | _, _ => None
 end. 

(** Return the list of blocks in the codomain of [e], with low and high bounds. *)

Definition block_of_binding (id_b_ty: ident * (block * type)) :=
  match id_b_ty with (id, (b, ty)) => (b, 0, sizeof ty) end.

Definition blocks_of_env (e: env) : list (block * Z * Z) :=
  List.map block_of_binding (PTree.elements e).

(** Optional assignment to a temporary *)

Definition set_opttemp (optid: option ident) (v: expr_sym) (le: temp_env) :=
  match optid with
  | None => le
  | Some id => PTree.set id v le
  end.

(** Selection of the appropriate case of a [switch], given the value [n]
  of the selector expression. *)

Fixpoint select_switch_default (sl: labeled_statements): labeled_statements :=
  match sl with
  | LSnil => sl
  | LScons None s sl' => sl
  | LScons (Some i) s sl' => select_switch_default sl'
  end.

Fixpoint select_switch_case (n: Z) (sl: labeled_statements): option labeled_statements :=
  match sl with
  | LSnil => None
  | LScons None s sl' => select_switch_case n sl'
  | LScons (Some c) s sl' => if zeq c n then Some sl else select_switch_case n sl'
  end.

Definition select_switch (n: Z) (sl: labeled_statements): labeled_statements :=
  match select_switch_case n sl with
  | Some sl' => sl'
  | None => select_switch_default sl
  end.

(** Turn a labeled statement into a sequence *)

Fixpoint seq_of_labeled_statement (sl: labeled_statements) : statement :=
  match sl with
  | LSnil => Sskip
  | LScons _ s sl' => Ssequence s (seq_of_labeled_statement sl')
  end.

Section SEMANTICS.

Variable ge: genv.

Variable needed_stackspace : ident -> nat.

(** ** Evaluation of expressions *)

Section EXPR.

Variable e: env.
Variable le: temp_env.
Variable m: mem.

(** [eval_expr ge e m a v] defines the evaluation of expression [a]
  in r-value position.  [v] is the value of the expression.
  [e] is the current environment and [m] is the current memory state. *)

Inductive eval_expr: expr -> expr_sym -> Prop :=
  | eval_Econst_int:   forall i ty,
      eval_expr (Econst_int i ty) (Eval (Vint i))
  | eval_Econst_float:   forall f ty,
      eval_expr (Econst_float f ty) (Eval (Vfloat f))
  | eval_Econst_single:   forall f ty,
      eval_expr (Econst_single f ty) (Eval (Vsingle f))
  | eval_Econst_long:   forall i ty,
      eval_expr (Econst_long i ty) (Eval (Vlong i))
  | eval_Etempvar:  forall id ty v,
      le!id = Some v ->
      eval_expr (Etempvar id ty) v
  | eval_Eaddrof: forall a ty v,
      eval_lvalue a v ->
      eval_expr (Eaddrof a ty) v
  | eval_Eunop:  forall op a ty v1 v,
      eval_expr a v1 ->
      sem_unary_operation_expr op v1 (typeof a) = v ->
      eval_expr (Eunop op a ty) v
  | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      sem_binary_operation_expr op v1 (typeof a1) v2 (typeof a2) = Some v ->
      eval_expr (Ebinop op a1 a2 ty) v
  | eval_Ecast:   forall a ty v1 v,
      eval_expr a v1 ->
      sem_cast_expr v1 (typeof a) ty = Some v ->
      eval_expr (Ecast a ty) v
  | eval_Elvalue: forall a v vptr,
                    eval_lvalue a vptr ->
                    deref_loc (typeof a) m vptr v ->
                    eval_expr a v

(** [eval_lvalue ge e m a b ofs] defines the evaluation of expression [a]
  in l-value position.  The result is the memory location [b, ofs]
  that contains the value of the expression [a]. *)

with eval_lvalue: expr -> expr_sym  -> Prop :=
     | eval_Evar_local:
         forall id l ty,
           e!id = Some(l, ty) ->
           eval_lvalue (Evar id ty) (Eval (Vptr l Int.zero))
     | eval_Evar_global:
         forall id l ty,
           e!id = None ->
           Genv.find_symbol ge id = Some l ->
           eval_lvalue (Evar id ty) (Eval (Vptr l Int.zero))
     | eval_Ederef:
         forall a ty v,
           eval_expr a v ->
           eval_lvalue (Ederef a ty) v
     | eval_Efield_struct:
         forall a i ty id fList att delta v,
           eval_expr a v ->
           typeof a = Tstruct id fList att ->
           field_offset i fList = OK delta ->
           eval_lvalue (Efield a i ty) (Val.add v (Eval (Vint (Int.repr delta))))
     | eval_Efield_union:
         forall a i ty id fList att v,
           eval_expr a v ->
           typeof a = Tunion id fList att ->
           eval_lvalue (Efield a i ty) v.

Scheme eval_expr_ind2 := Minimality for eval_expr Sort Prop
  with eval_lvalue_ind2 := Minimality for eval_lvalue Sort Prop.
Combined Scheme eval_expr_lvalue_ind from eval_expr_ind2, eval_lvalue_ind2.



(** [eval_exprlist ge e m al tyl vl] evaluates a list of r-value
  expressions [al], cast their values to the types given in [tyl],
  and produces the list of cast values [vl].  It is used to
  evaluate the arguments of function calls. *)

Inductive eval_exprlist: list expr -> typelist -> list expr_sym -> Prop :=
  | eval_Enil:
      eval_exprlist nil Tnil nil
  | eval_Econs:   forall a bl ty tyl v1 v2 vl,
      eval_expr a v1 ->
      sem_cast_expr v1 (typeof a) ty = Some v2 ->
      eval_exprlist bl tyl vl ->
      eval_exprlist (a :: bl) (Tcons ty tyl) (v2 :: vl).

End EXPR.


(** ** Transition semantics for statements and functions *)

(** Continuations *)

Inductive cont: Type :=
  | Kstop: cont
  | Kseq: statement -> cont -> cont       (**r [Kseq s2 k] = after [s1] in [s1;s2] *)
  | Kloop1: statement -> statement -> cont -> cont (**r [Kloop1 s1 s2 k] = after [s1] in [Sloop s1 s2] *)
  | Kloop2: statement -> statement -> cont -> cont (**r [Kloop1 s1 s2 k] = after [s2] in [Sloop s1 s2] *)
  | Kswitch: cont -> cont       (**r catches [break] statements arising out of [switch] *)
  | Kcall: option ident ->                  (**r where to store result *)
           function ->                      (**r calling function *)
           env ->                           (**r local env of calling function *)
           temp_env ->                      (**r temporary env of calling function *)
           cont -> cont.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kloop1 s1 s2 k => call_cont k
  | Kloop2 s1 s2 k => call_cont k
  | Kswitch k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

(** States *)

Inductive state: Type :=
  | State
      (f: function)
      (s: statement)
      (k: cont)
      (e: env)
      (le: temp_env)
      (m: mem) : state
  | Callstate
      (fd: fundef)
      (args: list expr_sym)
      (k: cont)
      (m: mem) : state
  | Returnstate
      (res: expr_sym)
      (k: cont)
      (m: mem) : state.
                 
(** Find the statement and manufacture the continuation 
  corresponding to a label *)

Fixpoint find_label (lbl: label) (s: statement) (k: cont) 
                    {struct s}: option (statement * cont) :=
  match s with
  | Ssequence s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse a s1 s2 =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sloop s1 s2 =>
      match find_label lbl s1 (Kloop1 s1 s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 (Kloop2 s1 s2 k)
      end
  | Sswitch e sl =>
      find_label_ls lbl sl (Kswitch k)
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end

with find_label_ls (lbl: label) (sl: labeled_statements) (k: cont) 
                    {struct sl}: option (statement * cont) :=
  match sl with
  | LSnil => None
  | LScons _ s sl' =>
      match find_label lbl s (Kseq (seq_of_labeled_statement sl') k) with
      | Some sk => Some sk
      | None => find_label_ls lbl sl' k
      end
  end.

(** Semantics for allocation of variables and binding of parameters at
  function entry.  Two semantics are supported: one where
  parameters are local variables, reside in memory, and can have their address
  taken; the other where parameters are temporary variables and do not reside
  in memory.  We parameterize the [step] transition relation over the
  parameter binding semantics, then instantiate it later to give the two
  semantics described above. *)

Variable function_entry: (ident -> nat) -> function -> list expr_sym -> mem -> env -> temp_env -> mem -> Prop.

(** Transition relation *)

Inductive step: state -> trace -> state -> Prop :=

  | step_assign:   forall f a1 a2 k e le m v2 v m' vptr,
      eval_lvalue e le m a1 vptr ->
      eval_expr e le m a2 v2 ->
      sem_cast_expr v2 (typeof a2) (typeof a1) = Some v ->
      assign_loc (typeof a1) m vptr v m' ->
      step (State f (Sassign a1 a2) k e le m)
        E0 (State f Sskip k e le m')

  | step_set:   forall f id a k e le m v,
      eval_expr e le m a v ->
      step (State f (Sset id a) k e le m)
        E0 (State f Sskip k e (PTree.set id v le) m)

  | step_call:   forall f optid a al k e le m tyargs tyres cconv vf vargs fd,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr e le m a vf ->
      eval_exprlist e le m al tyargs vargs ->
      Genv.find_funct m ge vf = Some fd ->
      type_of_fundef fd = Tfunction tyargs tyres cconv ->
      step (State f (Scall optid a al) k e le m)
        E0 (Callstate fd vargs (Kcall optid f e le k) m)

  | step_builtin:   forall f optid ef tyargs al k e le m vargs t vres m',
      eval_exprlist e le m al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      step (State f (Sbuiltin optid ef tyargs al) k e le m)
         t (State f Sskip k e (set_opttemp optid vres le) m')

  | step_seq:  forall f s1 s2 k e le m,
      step (State f (Ssequence s1 s2) k e le m)
        E0 (State f s1 (Kseq s2 k) e le m)
  | step_skip_seq: forall f s k e le m,
      step (State f Sskip (Kseq s k) e le m)
        E0 (State f s k e le m)
  | step_continue_seq: forall f s k e le m,
      step (State f Scontinue (Kseq s k) e le m)
        E0 (State f Scontinue k e le m)
  | step_break_seq: forall f s k e le m,
      step (State f Sbreak (Kseq s k) e le m)
        E0 (State f Sbreak k e le m)

  | step_ifthenelse:  forall f a s1 s2 k e le m v1 b,
      eval_expr e le m a v1 ->
      Mem.mem_norm m (bool_expr v1 (typeof a)) = Vint b ->
      step (State f (Sifthenelse a s1 s2) k e le m)
        E0 (State f (if negb (Int.eq b Int.zero) then s1 else s2) k e le m)
  | step_loop: forall f s1 s2 k e le m,
      step (State f (Sloop s1 s2) k e le m)
        E0 (State f s1 (Kloop1 s1 s2 k) e le m)
  | step_skip_or_continue_loop1:  forall f s1 s2 k e le m x,
      x = Sskip \/ x = Scontinue ->
      step (State f x (Kloop1 s1 s2 k) e le m)
        E0 (State f s2 (Kloop2 s1 s2 k) e le m)
  | step_break_loop1:  forall f s1 s2 k e le m,
      step (State f Sbreak (Kloop1 s1 s2 k) e le m)
        E0 (State f Sskip k e le m)
  | step_skip_loop2: forall f s1 s2 k e le m,
      step (State f Sskip (Kloop2 s1 s2 k) e le m)
        E0 (State f (Sloop s1 s2) k e le m)
  | step_break_loop2: forall f s1 s2 k e le m,
      step (State f Sbreak (Kloop2 s1 s2 k) e le m)
        E0 (State f Sskip k e le m)

  | step_return_0: forall f k e le m m' m'',
      Mem.free_list m (blocks_of_env e) = Some m' ->
      release_boxes m' (needed_stackspace (fn_id f)) = Some m'' ->
      step (State f (Sreturn None) k e le m)
        E0 (Returnstate (Eval Vundef) (call_cont k) m'')
  | step_return_1: forall f a k e le m v v' m' m'',
      eval_expr e le m a v -> 
      sem_cast_expr v (typeof a) f.(fn_return) = Some v' ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      release_boxes m' (needed_stackspace (fn_id f)) = Some m'' ->
      step (State f (Sreturn (Some a)) k e le m)
        E0 (Returnstate v' (call_cont k) m'')
  | step_skip_call: forall f k e le m m' m'',
      is_call_cont k ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      release_boxes m' (needed_stackspace (fn_id f)) = Some m'' ->
      step (State f Sskip k e le m)
        E0 (Returnstate (Eval Vundef) k m'')

  | step_switch: forall f a sl k e le m v n,
                   eval_expr e le m a v ->
                   sem_switch_arg_expr m v (typeof a) = Some n ->
                   step (State f (Sswitch a sl) k e le m)
        E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m)
  | step_skip_break_switch: forall f x k e le m,
      x = Sskip \/ x = Sbreak ->
      step (State f x (Kswitch k) e le m)
        E0 (State f Sskip k e le m)
  | step_continue_switch: forall f k e le m,
      step (State f Scontinue (Kswitch k) e le m)
        E0 (State f Scontinue k e le m)

  | step_label: forall f lbl s k e le m,
      step (State f (Slabel lbl s) k e le m)
        E0 (State f s k e le m)

  | step_goto: forall f lbl k e le m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
      step (State f (Sgoto lbl) k e le m)
        E0 (State f s' k' e le m)

  | step_internal_function: forall f vargs k m e le m1,
      function_entry needed_stackspace f vargs m e le m1 ->
      step (Callstate (Internal f) vargs k m)
        E0 (State f f.(fn_body) k e le m1)

  | step_external_function: forall ef targs tres cconv vargs k m vres t m',
      external_call ef ge vargs m t vres m' ->
      step (Callstate (External ef targs tres cconv) vargs k m)
         t (Returnstate vres k m')

  | step_returnstate: forall v optid f e le k m,
      step (Returnstate v (Kcall optid f e le k) m)
        E0 (State f Sskip k e (set_opttemp optid v le) m).

(** ** Whole-program semantics *)

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
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      initial_state p sg (Callstate f nil Kstop m0).

(** A final state is a [Returnstate] with an empty continuation. *)

Inductive final_state: state -> int -> Prop :=
| final_state_intro:
    forall r e m,
      Mem.mem_norm m e = Vint r -> 
      final_state (Returnstate e Kstop m) r.

End SEMANTICS.






(** The two semantics for function parameters.  First, parameters as local variables. *)

Inductive function_entry1 needed_stackspace  (f: function) (vargs: list expr_sym) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
  | function_entry1_intro: forall m1 m2,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      alloc_variables empty_env m (VarSort.varsort (f.(fn_params) ++ f.(fn_vars))) e m1 ->
      le = create_undef_temps f.(fn_temps) ->
      reserve_boxes m1 (needed_stackspace f.(fn_id)) = Some (m2) ->
      bind_parameters e m2 f.(fn_params) vargs m' ->
      function_entry1 needed_stackspace  f vargs m e le m'.

Definition step1 (ge: genv) ns := step ge ns function_entry1.

(** Second, parameters as temporaries. *)


Inductive function_entry2 needed_stackspace (f: function) (vargs: list expr_sym) (m: mem) (e: env)  (le: temp_env) (m': mem) : Prop :=
| function_entry2_intro:
    forall m2,
      list_norepet (var_names f.(fn_vars)) ->
      list_norepet (var_names f.(fn_params)) ->
      list_disjoint (var_names f.(fn_params)) (var_names f.(fn_temps)) ->
      alloc_variables empty_env m (VarSort.varsort f.(fn_vars)) e m2 ->
      bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
      reserve_boxes m2 (needed_stackspace f.(fn_id)) = Some m' ->
      function_entry2 needed_stackspace f vargs m e le m'.

Definition step2 (ge: genv) ns := step ge ns function_entry2.

(** Wrapping up these definitions in two small-step semantics. *)

Definition semantics1 (p: program) ns sg :=
  Semantics (fun ge => step1 ge ns) (initial_state p sg) final_state (Genv.globalenv p).

Definition semantics2 (p: program) ns sg :=
  Semantics (fun ge => step2 ge ns) (initial_state p sg) final_state (Genv.globalenv p).

(** This semantics is receptive to changes in events. *)

Lemma semantics_receptive:
  forall (p: program) ns sg, receptive (semantics1 p ns sg).
Proof.
  intros. constructor; simpl; intros.
(* receptiveness *)
  assert (t1 = E0 -> exists s2, step1 (Genv.globalenv p) ns s t2 s2).
    intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto.
  (* builtin *)
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]]. 
  econstructor; econstructor; eauto.
  (* external *)
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]]. 
  exists (Returnstate vres2 k m2). econstructor; eauto.
(* trace length *)
  red; intros. inv H; simpl; try omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
Qed.

