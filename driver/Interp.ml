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

(* Interpreting CompCert C sources *)

open Format
open Camlcoq
open Datatypes
open AST
open Integers
open Values
open Memory
open Globalenvs
open Events
open EventsGeneric
open Ctypes
open Cop
open Csyntax
open Csem
open Clflags
open Values_symbolic_aux
open Values_symbolictype

(* Configuration *)

let trace = ref 1   (* 0 if quiet, 1 if normally verbose, 2 if full trace *)
let time_trace = ref 0
let mem_debug = ref false
let dummy_blocks = ref 0
let dummy_size = ref 0

type mode = First | Random | All

let mode = ref First

(* Printing events *)

let print_id_ofs p (id, ofs) =
  let id = extern_atom id and ofs = camlint_of_coqint ofs in
  if ofs = 0l
  then fprintf p " %s" id
  else fprintf p " %s%+ld" id ofs

let print_eventval p = function
  | EVint n -> fprintf p "%ld" (camlint_of_coqint n)
  | EVfloat f -> fprintf p "%F" (camlfloat_of_coqfloat f)
  | EVsingle f -> fprintf p "%F" (camlfloat_of_coqfloat32 f)
  | EVlong n -> fprintf p "%LdLL" (camlint64_of_coqint n)
  | EVptr_global(id, ofs) -> fprintf p "&%a" print_id_ofs (id, ofs)

let print_eventval_list p = function
  | [] -> ()
  | v1 :: vl ->
      print_eventval p v1;
      List.iter (fun v -> fprintf p ",@ %a" print_eventval v) vl

let print_event p = function
  | Event_syscall(id, args, res) ->
      fprintf p "extcall %s(%a) -> %a"
                (extern_atom id)
                print_eventval_list args
                print_eventval res
  | Event_vload(chunk, id, ofs, res) ->
      fprintf p "volatile load %s[&%s%+ld] -> %a"
                (PrintAST.name_of_chunk chunk)
                (extern_atom id) (camlint_of_coqint ofs)
                print_eventval res
  | Event_vstore(chunk, id, ofs, arg) ->
      fprintf p "volatile store %s[&%s%+ld] <- %a"
                (PrintAST.name_of_chunk chunk)
                (extern_atom id) (camlint_of_coqint ofs)
                print_eventval arg
  | Event_annot(text, args) ->
      fprintf p "annotation \"%s\" %a"
                (extern_atom text)
                print_eventval_list args

(* Printing states *)

let name_of_fundef prog fd =
  let rec find_name = function
  | [] -> "<unknown function>"
  | (id, Gfun fd') :: rem ->
      if fd == fd' then extern_atom id else find_name rem
  | (id, Gvar v) :: rem ->
      find_name rem
  in find_name prog.prog_defs

let name_of_function prog fn =
  let rec find_name = function
  | [] -> "<unknown function>"
  | (id, Gfun(Internal fn')) :: rem ->
      if fn == fn' then extern_atom id else find_name rem
  | (id, _) :: rem ->
      find_name rem
  in find_name prog.prog_defs

let invert_local_variable e b =
  Maps.PTree.fold 
    (fun res id (b', _) -> if b = b' then Some id else res)
    e None

let print_pointer ge e p (bofs) =
  match bofs with
    Eval (Vptr(b,ofs)) ->
      begin match invert_local_variable e b with
      | Some id -> print_id_ofs p (id, ofs)
      | None ->
	match Genv.invert_symbol ge b with
	| Some id -> print_id_ofs p (id, ofs)
	| None -> ()
      end
  | _ -> fprintf p "%s" (PrintValues.print_expr_symb bofs)

let print_val = PrintCsyntax.print_value

let print_val_list p vl =
  match vl with
  | [] -> ()
  | v1 :: vl ->
    PrintCsyntax.print_expr_symb p v1;
    List.iter (fun v -> fprintf p ",@ %a" (PrintCsyntax.print_expr_symb) v) vl

let print_state p (prog, ge, s) =
  match s with
  | State(f, s, k, e, m) ->
      PrintCsyntax.print_pointer_hook := print_pointer ge e;
      fprintf p "in function %s, statement@ @[<hv 0>%a@]"
              (name_of_function prog f)
              PrintCsyntax.print_stmt s
  | ExprState(f, r, k, e, m) ->
      PrintCsyntax.print_pointer_hook := print_pointer ge e;
      fprintf p "in function %s, expression@ @[<hv 0>%a@]"
              (name_of_function prog f)
              PrintCsyntax.print_expr r
  | Callstate(fd, args, k, m) ->
      PrintCsyntax.print_pointer_hook := print_pointer ge Maps.PTree.empty;
      fprintf p "calling@ @[<hov 2>%s(%a)@]"
              (name_of_fundef prog fd)
              print_val_list args
  | Returnstate(res, k, m) ->
    PrintCsyntax.print_pointer_hook := print_pointer ge Maps.PTree.empty;
    fprintf p "returning@ %a"
      PrintCsyntax.print_expr_symb res
  | Stuckstate ->
      fprintf p "stuck after an undefined expression"

(* Comparing memory states *)

let compare_mem m1 m2 =
  (* assumes nextblocks were already compared equal *)
  (* should permissions be taken into account? *)
  Pervasives.compare m1.Mem.mem_contents m2.Mem.mem_contents

(* Comparing continuations *)

let some_expr = Csyntax.Eval(Eval (Vint Integers.Int.zero), Tvoid)

let rank_cont = function
  | Kstop -> 0
  | Kdo _ -> 1
  | Kseq _ -> 2
  | Kifthenelse _ -> 3
  | Kwhile1 _ -> 4
  | Kwhile2 _ -> 5
  | Kdowhile1 _ -> 6
  | Kdowhile2 _ -> 7
  | Kfor2 _ -> 8
  | Kfor3 _ -> 9
  | Kfor4 _ -> 10
  | Kswitch1 _ -> 11
  | Kswitch2 _ -> 12
  | Kreturn _ -> 13
  | Kcall _ -> 14

let rec compare_cont k1 k2 =
  if k1 == k2 then 0 else
  match k1, k2 with
  | Kstop, Kstop -> 0
  | Kdo k1, Kdo k2 -> compare_cont k1 k2
  | Kseq(s1, k1), Kseq(s2, k2) ->  
      let c = compare s1 s2 in if c <> 0 then c else compare_cont k1 k2
  | Kifthenelse(s1, s1', k1), Kifthenelse(s2, s2', k2) ->
      let c = compare (s1,s1') (s2,s2') in
      if c <> 0 then c else compare_cont k1 k2
  | Kwhile1(e1, s1, k1), Kwhile1(e2, s2, k2) ->
      let c = compare (e1,s1) (e2,s2) in
      if c <> 0 then c else compare_cont k1 k2
  | Kwhile2(e1, s1, k1), Kwhile2(e2, s2, k2) ->
      let c = compare (e1,s1) (e2,s2) in
      if c <> 0 then c else compare_cont k1 k2
  | Kdowhile1(e1, s1, k1), Kdowhile1(e2, s2, k2) ->
      let c = compare (e1,s1) (e2,s2) in
      if c <> 0 then c else compare_cont k1 k2
  | Kdowhile2(e1, s1, k1), Kdowhile2(e2, s2, k2) ->
      let c = compare (e1,s1) (e2,s2) in
      if c <> 0 then c else compare_cont k1 k2
  | Kfor2(e1, s1, s1', k1), Kfor2(e2, s2, s2', k2) ->
      let c = compare (e1,s1,s1') (e2,s2,s2') in
      if c <> 0 then c else compare_cont k1 k2
  | Kfor3(e1, s1, s1', k1), Kfor3(e2, s2, s2', k2) ->
      let c = compare (e1,s1,s1') (e2,s2,s2') in
      if c <> 0 then c else compare_cont k1 k2
  | Kfor4(e1, s1, s1', k1), Kfor4(e2, s2, s2', k2) ->
      let c = compare (e1,s1,s1') (e2,s2,s2') in
      if c <> 0 then c else compare_cont k1 k2
  | Kswitch1(sl1, k1), Kswitch1(sl2, k2) ->
      let c = compare sl1 sl2 in
      if c <> 0 then c else compare_cont k1 k2
  | Kreturn k1, Kreturn k2 ->
      compare_cont k1 k2
  | Kcall(f1, e1, c1, ty1,  k1), Kcall(f2, e2, c2, ty2, k2) ->
      let c = compare (f1, e1, c1 some_expr, ty1) (f2, e2, c2 some_expr, ty2) in
      if c <> 0 then c else compare_cont k1 k2
  | _, _ ->
      compare (rank_cont k1) (rank_cont k2)

(* Comparing states *)

let rank_state = function
  | State _ -> 0
  | ExprState _ -> 1
  | Callstate _ -> 2
  | Returnstate _ -> 3
  | Stuckstate -> assert false

let mem_state = function
  | State(f, s, k, e, m) -> m
  | ExprState(f, r, k, e, m) -> m
  | Callstate(fd, args, k, m) -> m
  | Returnstate(res, k, m) -> m
  | Stuckstate -> assert false

let compare_state s1 s2 =
  if s1 == s2 then 0 else
  let c = P.compare (mem_state s1).Mem.nextblock (mem_state s2).Mem.nextblock in
  if c <> 0 then c else begin
  match s1, s2 with
  | State(f1,s1,k1,e1,m1), State(f2,s2,k2,e2,m2) ->
      let c = compare (f1,s1,e1) (f2,s2,e2) in if c <> 0 then c else
      let c = compare_cont k1 k2 in if c <> 0 then c else
      compare_mem m1 m2
  | ExprState(f1,r1,k1,e1,m1), ExprState(f2,r2,k2,e2,m2) ->
      let c = compare (f1,r1,e1) (f2,r2,e2) in if c <> 0 then c else
      let c = compare_cont k1 k2 in if c <> 0 then c else
      compare_mem m1 m2
  | Callstate(fd1,args1,k1,m1), Callstate(fd2,args2,k2,m2) ->
      let c = compare (fd1,args1) (fd2,args2) in if c <> 0 then c else
      let c = compare_cont k1 k2 in if c <> 0 then c else
      compare_mem m1 m2
  | Returnstate(res1,k1,m1), Returnstate(res2,k2,m2) ->
      let c = compare res1 res2 in if c <> 0 then c else
      let c = compare_cont k1 k2 in if c <> 0 then c else
      compare_mem m1 m2
  | _, _ ->
      compare (rank_state s1) (rank_state s2)
  end

(* Sets of states already explored *)

module StateSet =
  Set.Make(struct
             type t = state * Determinism.world
             let compare (s1,w1) (s2,w2) = compare_state s1 s2
           end)

(* Purging states that will never be reached again based on their memory
   next block.  All states with nextblock <= the given nextblock are
   removed.  We take advantage of the fact that StateSets are sorted
   by increasing nextblock, cf. the definition of compare_state above. *)

let rec purge_seen nextblock seen =
  let min = try Some(StateSet.min_elt seen) with Not_found -> None in
  match min with
  | None -> seen
  | Some((s, w) as sw) ->
      if P.le (mem_state s).Mem.nextblock nextblock
      then purge_seen nextblock (StateSet.remove sw seen)
      else seen

(* Extract a string from a global pointer *)

let extract_string m blk ofs =
  let b = Buffer.create 80 in
  let rec extract blk ofs =
    match Mem.load Mint8unsigned m blk ofs with
    | Some v ->
       begin match Mem.mem_norm m v with
	       Values.Vint n -> 
	       let c = Char.chr (Z.to_int n) in
	       if c = '\000' then begin
		   Some(Buffer.contents b)
		 end else begin
		   Buffer.add_char b c; 
		   extract blk (Z.succ ofs)
		 end
	     | _ -> None
       end
    | _ -> None
  in extract blk ofs


(* let extract_c_string m blk ofs n = *)
(*   let b = Buffer.create n in *)
(*   let rec extract blk ofs n = *)
(*     match Mem.load Mint8unsigned m blk ofs with *)
(*     | Some(Values_symbolictype.Eval (Vint n)) -> *)
(*       let c = Char.chr (Z.to_int n) in *)
(*       if n = 0 then begin *)
(*         Some(Buffer.contents b) *)
(*       end else begin *)
(*         Buffer.add_char b c;  *)
(*         extract blk (Z.succ ofs) (n-1) *)
(*       end *)
(*     | _ -> *)
(*       None in *)
(*   extract blk ofs n *)

(* Emulation of printf *)

(* All ISO C 99 formats *)

let re_conversion = Str.regexp (
  "\\(%[-+0# ]*[0-9]*\\(\\.[0-9]*\\)?\\)" (* group 1: flags, width, precision *)
^ "\\(\\|[lhjztL]\\|hh\\|ll\\)"            (* group 3: length modifier *)
^ "\\([aAcdeEfgGinopsuxX%]\\)"            (* group 4: conversion specifier *)
)

external format_float: string -> float -> string
  = "caml_format_float"
external format_int32: string -> int32 -> string
  = "caml_int32_format"
external format_int64: string -> int64 -> string
  = "caml_int64_format"

let format_value m flags length conv (arg: Values_symbolictype.expr_sym)  =
  match conv.[0], length, arg with
  | ('d'|'i'|'u'|'o'|'x'|'X'|'c'), (""|"h"|"hh"|"l"|"z"|"t"), arg ->
     begin match Mem.mem_norm m arg with
	     Vint i -> 
	     format_int32 (flags ^ conv) (camlint_of_coqint i)
	   | _ -> "<int argument expected>"
     end
  | ('d'|'i'|'u'|'o'|'x'|'X'), ("ll"|"j"), i ->
     begin match Mem.mem_norm m i with
	     Vlong i -> 
	     format_int64 (flags ^ conv) (camlint64_of_coqint i)
	   | _ ->       "<long long argument expected>"
     end
  | ('f'|'e'|'E'|'g'|'G'|'a'), "", i ->
     begin match Mem.mem_norm m i with
	     Vfloat f -> 
	     format_float (flags ^ conv) (camlfloat_of_coqfloat f)
	   | _ ->
	      begin match Mem.mem_norm m i with
		      Vsingle i ->
		      format_float (flags ^ conv) (camlfloat_of_coqfloat32 i)
		    | _ -> "<float argument expected>"
	      end
     end
  | 's', "", ptr ->
     begin match Mem.mem_norm m ptr with
	     Vptr (blk,ofs) ->
	     begin match extract_string m blk ofs with
		   | Some s -> s
		   | None -> "<bad string>"
	     end
	   | _ -> "<pointer argument expected>"
     end
  | 'p', "", ptr ->
     begin match Mem.mem_norm m ptr with
	     Vptr (blk,ofs) ->
	     Printf.sprintf "<%ld%+ld>" (P.to_int32 blk) (camlint_of_coqint ofs)
	   | _ -> begin match Mem.mem_norm m ptr with
			  Vint i ->
			  format_int32 (flags ^ "x") (camlint_of_coqint i)
			| _ ->   "<int or pointer argument expected>"
		  end
     end
  | _, _, _ ->
      "<unrecognized format>"      

let do_printf m fmt args =

  let b = Buffer.create 80 in
  let len = String.length fmt in

  let opt_search_forward pos =
    try Some(Str.search_forward re_conversion fmt pos)
    with Not_found -> None in

  let rec scan pos args =
    if pos < len then begin
    match opt_search_forward pos with
    | None ->
        Buffer.add_substring b fmt pos (len - pos)
    | Some pos1 ->
        Buffer.add_substring b fmt pos (pos1 - pos);
        let flags = Str.matched_group 1 fmt
        and length = Str.matched_group 3 fmt
        and conv = Str.matched_group 4 fmt
        and pos' = Str.match_end() in
        if conv = "%" then begin
          Buffer.add_char b '%';
          scan pos' args
        end else begin
          match args with
          | [] ->
            Buffer.add_string b "<missing argument>";
            scan pos' []
          | arg :: args' ->
            Buffer.add_string b (format_value m flags length conv arg);
            scan pos' args'
	  (* | _ -> failwith "did not expect a symbolic value as printf argument" *)
        end
    end
  in scan 0 args; Buffer.contents b

(* Implementation of external functions *)

let (>>=) opt f = match opt with None -> None | Some arg -> f arg

let next_handle = ref 3
let file_handles = ref [(0,Unix.stdin);(1,Unix.stdout);(2,Unix.stderr)]

let convertFlags (flags:BinNums.coq_Z) : (Unix.open_flag list) = 
  let f = Z.to_int flags in
  let rec opt_flags ofl = match ofl with
      [] -> []
    | (o,fl)::r -> if f land o <> 0 then fl::(opt_flags r) else (opt_flags r)
  in
  (if f lor 0o0 = 0 then [Unix.O_RDONLY] else []) @
    opt_flags [
      (   0o1,  Unix.O_WRONLY);
      (   0o2,  Unix.O_RDWR);
      ( 0o100,  Unix.O_CREAT);
      (0o1000,  Unix.O_TRUNC);
      (0o2000,  Unix.O_APPEND)]
    

let flag_name = function
  | Unix.O_RDONLY -> "rd_only"
  | Unix.O_WRONLY -> "wr_only"
  | Unix.O_RDWR -> "rd_wr"
  | Unix.O_CREAT -> "creat"
  | Unix.O_TRUNC -> "trunc"
  | Unix.O_APPEND -> "append"
  | _ -> "other; should not appear..."

let copen fname flags perms =
  try
    let unix_flags = convertFlags flags in
    let new_handle = Unix.openfile fname unix_flags perms in
    let new_handle_int = !next_handle in
    file_handles := ((new_handle_int,new_handle)::(!file_handles));
    next_handle := !next_handle + 1;
    new_handle_int
  with _ -> failwith (Printf.sprintf "Could not open file '%s'." fname)

let rec get_file_handle id =
  let rec gfh fhl =
    match fhl with
    | [] -> None
    | (i,fh)::r -> if i = id then Some fh else gfh r
  in
  gfh !file_handles

let remove_file_handle id =
  let rec rfh fhl id =
    match fhl with
    | [] -> []
    | (i,fh)::r -> if i = id then r else (i,fh)::(rfh r id)
  in file_handles := rfh (!file_handles) id


let explode s n =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (n - 1) [];;

let string_to_list_memval s n = List.map
  (fun c -> Memdata.Symbolic (Eval (Vint (Z.of_uint (int_of_char c))), None, O))
  (explode s n)

let exec_open id w m args = 
  match args with 
    Values_symbolictype.Eval(Vptr(b,ofs)) :: Values_symbolictype.Eval(Vint flags) :: oargs ->
      extract_string m b ofs >>= fun fname ->
      let perms = (match oargs with (Values_symbolictype.Eval (Vint a))::r -> Z.to_int a | _ -> 0) in
      let open_handle = try copen fname flags perms with _ -> -1 in
      Some(((w, [Event_syscall(id, [], EVint (Z.of_uint open_handle))]), Values_symbolictype.Eval(Vint (Z.of_uint open_handle))), m)
  | _ -> None

let encode_mode_prot kind prot = 
  (match kind with
    Unix.S_REG -> 0o0100000
  | Unix.S_DIR -> 0o0040000
  | Unix.S_CHR -> 0o0020000
  | Unix.S_BLK -> 0o0060000
  | Unix.S_LNK -> 0o0120000
  | Unix.S_FIFO -> 0o0010000
  | Unix.S_SOCK -> 0o0140000) lor prot

let rec nat_of_int = function
  | 0 -> O
  | n when n < 0-> failwith "negative nat impossible"
  | n -> S (nat_of_int (n-1))

let memval_of_int =
  (fun c -> Memdata.Symbolic (Eval (Vint c), None, O))
    
let  encode_int i =
  (Memdata.inj_symbolic (S (S (S (S O)))) (Eval (Vint (Z.of_uint i)))) None

let  encode_long i =
  (Memdata.inj_symbolic (S (S (S (S (S (S (S (S O)))))))) (Eval (Vlong (Z.of_uint i)))) None
    
let encode_time t = 
  (encode_int  (int_of_float (floor t))) @
    (encode_int (int_of_float ((t-.(floor t)) *. 1.0e9)))





let caml_stats_to_list_memval (s:Unix.stats) = 
  (encode_long (s.Unix.st_dev)) @
    (encode_int 0) @		       (* unsigned short int padding*)
    (encode_int (s.Unix.st_ino)) @   (* unsigned long int*)
    (encode_int (encode_mode_prot s.Unix.st_kind s.Unix.st_perm)(* (s.Unix.st_kind) *)) @  (* unsigned int *)
    (encode_int (s.Unix.st_nlink)) @ (* unsigned int *)
    (encode_int (s.Unix.st_uid)) @
    (encode_int (s.Unix.st_gid)) @
    (encode_long (s.Unix.st_rdev)) @
    (encode_int 0) @		      (* unsigned short int padding *)
    (encode_int (s.Unix.st_size)) @ (* unsigned long int *)
    (encode_int 1024) @	      (* blksize: long int *)
    (encode_int 1) @	      (* blksize: long int *)
    (encode_time (s.Unix.st_atime)) @
    (encode_time (s.Unix.st_mtime)) @
    (encode_time (s.Unix.st_ctime))


let exec_stat id w m args = 
  match args with 
    Values_symbolictype.Eval(Vptr(b,ofs)) :: Values_symbolictype.Eval(Vptr(b2,ofs2)) :: oargs ->
      extract_string m b ofs >>= fun fname ->
      let ret, m' =
	try 0,
	  Mem.storebytes m b2 ofs2 (caml_stats_to_list_memval (Unix.stat fname)) 
	with e -> -1, Some m
      in
      (match m' with
	Some m2 ->
	  Some(((w, [Event_syscall(id, [], EVint (Z.of_uint ret))]), Values_symbolictype.Eval(Vint (Z.of_uint ret))), m2)
      | _ -> None)
  | _ -> None


let my_c_exit n = 
  Printf.printf "Program exits with code %d\n" n; exit n

let c_cmd_to_caml_cmd = function
  | 0 -> Unix.SEEK_SET
  | 1 -> Unix.SEEK_CUR
  | 2 -> Unix.SEEK_END
  | _ -> failwith "Invalid lseek argument"
    

let exec_seek handle n cmd = 
  Unix.lseek handle n (c_cmd_to_caml_cmd cmd)

let do_external_function id sg ge w args m =
  match extern_atom id, args with
  | "printk", Values_symbolictype.Eval (Vptr(b,  ofs)) :: args' ->
    extract_string m b ofs >>= fun fmt ->
    Printf.printf "Kernel message: %s" (do_printf m fmt args');
    flush stdout;
    Some(((w, [Event_syscall(id, [], EVint Integers.Int.zero)]), Values_symbolictype.Eval(Vint Integers.Int.zero)), m)
  | "printf", ptr :: args' ->
     begin match Mem.mem_norm m ptr with
	     Vptr (b,ofs) ->
	     begin match extract_string m b ofs with
		     Some fmt ->
		     Printf.printf "%s" (do_printf m fmt args');
		     flush stdout;
		     Some(((w, [Event_syscall(id, [], EVint Integers.Int.zero)]), Values_symbolictype.Eval(Vint Integers.Int.zero)), m)
		   | None -> Printf.printf "printf failed: \n"; None
	     end
	   | _ -> Printf.printf "norming printf args failed\n"; None
     end
  | "error", Values_symbolictype.Eval (Vptr(b, ofs)) :: args' ->
    extract_string m b ofs >>= fun fmt ->
    print_string ("Error: " ^ (do_printf m fmt args'));
    flush stdout;
    failwith "Program called error()";
  | "srand", Values_symbolictype.Eval v :: nil ->
    (match v with
      Vint n | Vlong n ->
	Random.init (Z.to_int n);
	Some(((w, [Event_syscall(id, [], EVint Integers.Int.zero)]), Values_symbolictype.Eval(Vint Integers.Int.zero)), m)
    | _ -> None)
  | "rand", nil ->
    let random_number = Z.of_sint (Random.bits ()) in
    Some(((w, [Event_syscall(id, [], EVint (Integers.Int.repr random_number))]), Values_symbolictype.Eval(Vint (Integers.Int.repr random_number))), m)
  | "stat", _ -> exec_stat id w m args
  | "open", _ -> exec_open id w m args
  | "__libc_open",_ -> exec_open id w m args
  | "exit", Values_symbolictype.Eval(Vint ret)::nil -> my_c_exit (Z.to_int ret)
  | "_exit", Values_symbolictype.Eval(Vint ret)::nil -> my_c_exit (Z.to_int ret)
  | "raise", Values_symbolictype.Eval(Vint sign)::bil -> failwith (Printf.sprintf "Error raise(%d)" (Z.to_int sign))
  | "lseek", Values_symbolictype.Eval(Vint handle) :: Values_symbolictype.Eval(Vint n) :: Values_symbolictype.Eval(Vint cmd) :: nil ->
    get_file_handle (Z.to_int handle) >>= fun file_handle ->
    let resulting_offset = exec_seek file_handle (Z.to_int n) (Z.to_int cmd) in
    Some(((w, [Event_syscall(id, [], EVint (Z.of_uint resulting_offset))]), Values_symbolictype.Eval(Vint (Z.of_uint resulting_offset))), m)
  | "read", Values_symbolictype.Eval(Vint handle) :: Values_symbolictype.Eval (Vptr(b,ofs)) :: Values_symbolictype.Eval (Vint len) :: nil ->
    get_file_handle (Z.to_int handle) >>= fun file_handle ->
    let length = Z.to_int len in
    let str = String.make length ' ' in
    let n = Unix.read file_handle str 0 length in
  (* copy n first characters of str in memory *)
    Mem.storebytes m b ofs (string_to_list_memval str n) >>= fun m' ->
    Some(((w, [Event_syscall(id, [], EVint (Z.of_uint n))]), Values_symbolictype.Eval(Vint (Z.of_uint n))), m')
  | "write", Values_symbolictype.Eval(Vint handle) :: Values_symbolictype.Eval (Vptr(b,ofs)) :: Values_symbolictype.Eval (Vint len) :: nil ->
    get_file_handle (Z.to_int handle) >>= fun file_handle ->
    let length = Z.to_int len in
    extract_string m b ofs >>= fun str ->
    (try 
       let n = Unix.write file_handle str 0 length in
	 Some(((w, [Event_syscall(id, [], EVint (Z.of_uint n))]), Values_symbolictype.Eval(Vint (Z.of_uint n))), m)
     with Unix.Unix_error (e,s,s2) ->
       Printf.printf "Erreur write: %s" (Unix.error_message e); None)
  | "close", Values_symbolictype.Eval(Vint handle)::nil ->
    get_file_handle (Z.to_int handle) >>= fun file_handle ->
    (if (Z.to_int handle) < 3 then
	(Printf.printf "Warning: tried to close file descriptor %d, ignored\n" (Z.to_int handle);
	 flush stdout)
     else
	(Unix.close file_handle;
	 remove_file_handle (Z.to_int handle)));

    Cexec.list_eventval_of_val ge (List.map (Mem.mem_norm m) args) sg.sig_args >>= fun eargs ->
    Some(((w, [Event_syscall(id, eargs, EVint Integers.Int.zero)]), Values_symbolictype.Eval(Vint Integers.Int.zero)), m)
  | "time", args' ->
    Cexec.list_eventval_of_val ge (List.map (Mem.mem_norm m) args) sg.sig_args >>= fun eargs ->
    let time = int_of_float (Unix.time ()) in
    Some(((w, [Event_syscall(id, eargs, EVint Integers.Int.zero)]), Values_symbolictype.Eval(Vint (Z.of_uint time))), m)
  | "mmap", file:: len :: prot :: flags :: fd :: fofs :: args' ->
     let expect_int e v =
       let n = (Mem.mem_norm m e) in
       if Val.eq n (Vint (Integers.Int.repr (Z.of_uint v)))
       then Some v
       else None in
     expect_int file 0 >>= fun _ ->
       expect_int prot 3 >>= fun _ -> 
       expect_int flags 34 >>= fun _ ->
       expect_int fd (-1) >>= fun _ ->
       expect_int fofs 0 >>= fun _ ->
       begin match Mem.mem_norm m len with
	 Vint len ->
	 begin match Mem.low_alloc m Integers.Int.zero len (Nat.of_int 12) (* (Z.of_uint (1 lsl 12)) *) Memtype.Dynamic with
	   Some (m',b') ->
           let mkint i =
             (Vint (Integers.Int.repr (Z.of_uint i))) in
           Cexec.list_eventval_of_val
             ge
             [mkint 0; (Vint len); mkint 3; mkint 34; mkint (-1); mkint 0]
             sg.sig_args >>= fun eargs ->
	   Some(((w, [Event_syscall(id, eargs, EVptr_global (b', Integers.Int.zero))]),
		 Eval(Vptr (b',Integers.Int.zero))), m')
	 | _ -> None
	 end
       | _ -> None
       end
  | "malloc", len :: nil ->
     begin match Mem.mem_norm m len with
       Vint len ->
       begin match Mem.low_alloc m Integers.Int.zero len (Nat.of_int 4) Memtype.Dynamic with
	   Some (m',b') ->
           Cexec.list_eventval_of_val
             ge [ (Vint len)] sg.sig_args >>= fun eargs ->
	   Some(((w, [Event_syscall(id, eargs, EVptr_global (b', Integers.Int.zero))]),
		 Eval(Vptr (b',Integers.Int.zero))), m')
	 | _ -> None
	 end
       | _ -> None
       end
  | "unlink", Values_symbolictype.Eval (Vptr (b, ofs)) :: nil ->
     extract_string m b ofs >>= fun str ->
     let ret = try Unix.unlink str;0 with _ -> -1 in
     Some(((w, [Event_syscall(id, [], EVint( Integers.Int.repr (Z.of_sint ret)))]),
	   Eval(Vint( Integers.Int.repr (Z.of_sint ret)))), m)
  | "link", Values_symbolictype.Eval (Vptr (b, ofs)) :: Values_symbolictype.Eval (Vptr (b2, ofs2)) :: nil ->
     extract_string m b ofs >>= fun path1 ->
     extract_string m b2 ofs2 >>= fun path2 ->
     let ret = try Unix.link path1 path2; 0 with _ -> -1 in 
     Some(((w, [Event_syscall(id, [], EVint( Integers.Int.repr (Z.of_sint ret)))]),
	   Eval(Vint( Integers.Int.repr (Z.of_sint ret)))), m)
  | func,_ -> Printf.printf "Undefined external %s\n" func;
              None


let do_inline_assembly txt ge w args m = None

(* Implementing external functions producing observable events *)

let rec world ge m =
  Determinism.World(world_io ge m, world_vload ge m, world_vstore ge m)

and world_io ge m id args =
  None

and world_vload ge m chunk id ofs =
  Genv.find_symbol ge id >>= fun b ->
  Mem.load chunk m b ofs >>= fun v ->
  Cexec.eventval_of_val ge (Mem.mem_norm m v) (type_of_chunk chunk) >>= fun ev ->
  Some(ev, world ge m)

and world_vstore ge m chunk id ofs ev =
  Genv.find_symbol ge id >>= fun b ->
  Cexec.val_of_eventval ge ev (type_of_chunk chunk) >>= fun v ->
  Mem.store chunk m b ofs (Eval v) >>= fun m' ->
  Some(world ge m')

let do_event p ge time w ev =
  if !trace >= 1 then
    fprintf p "@[<hov 2>Time %d: observable event:@ @[<hov 2>%a@]@]@."
              time print_event ev;
  (* Return new world after external action *)
  match ev with
  | Event_vstore(chunk, id, ofs, v) ->
      begin match Determinism.nextworld_vstore w chunk id ofs v with
      | None -> assert false
      | Some w' -> w'
      end
  | _ -> w

let rec do_events p ge time w t =
  match t with
  | [] -> w
  | ev :: t' -> do_events p ge time (do_event p ge time w ev) t'

(* Debugging stuck expressions *)

let (|||) a b = a || b (* strict boolean or *)

let diagnose_stuck_expr p ge w f a kont e m =
  let rec diagnose k a =
  (* diagnose subexpressions first *)
    let found =
      match k, a with
      | LV, Ederef(r, ty) -> diagnose RV r
      | LV, Efield(r, f, ty) -> diagnose RV r
      | RV, Evalof(l, ty) -> diagnose LV l
      | RV, Eaddrof(l, ty) -> diagnose LV l
      | RV, Csyntax.Eunop(op, r1, ty) -> diagnose RV r1
      | RV, Csyntax.Ebinop(op, r1, r2, ty) -> diagnose RV r1 ||| diagnose RV r2
      | RV, Ecast(r1, ty) -> diagnose RV r1
      | RV, Econdition(r1, r2, r3, ty) -> diagnose RV r1
      | RV, Eassign(l1, r2, ty) -> diagnose LV l1 ||| diagnose RV r2
      | RV, Eassignop(op, l1, r2, tyres, ty) -> diagnose LV l1 ||| diagnose RV r2
      | RV, Epostincr(id, l, ty) -> diagnose LV l
      | RV, Ecomma(r1, r2, ty) -> diagnose RV r1
      | RV, Eparen(r1, ty) -> diagnose RV r1
      | RV, Ecall(r1, rargs, ty) -> diagnose RV r1 ||| diagnose_list rargs
      | RV, Ebuiltin(ef, tyargs, rargs, ty) -> diagnose_list rargs
      | _, _ -> false in
    if found then true else begin
      let l = Cexec.step_expr ge (fun _ -> Nat.of_int 100) do_external_function do_inline_assembly e w k a m in
      if List.exists (fun (ctx,red) -> red = Cexec.Stuckred) l then begin
	PrintCsyntax.print_pointer_hook := print_pointer ge e;
	fprintf p "@[<hov 2>Stuck subexpression:@ %a@]@."
          PrintCsyntax.print_expr a;
	true
      end else false
    end

  and diagnose_list al =
    match al with
    | Enil -> false
    | Econs(a1, al') -> diagnose RV a1 ||| diagnose_list al'

  in diagnose RV a

let diagnose_stuck_state p ge w = function
  | ExprState(f,a,k,e,m) -> ignore(diagnose_stuck_expr p ge w f a k e m)
  | _ -> ()

(* Exploration *)

let do_step p ns prog ge time (s, w) =
  if !trace >= 2 && time >= !time_trace then
    fprintf p "@[<hov 2>Time %d: %a@]@." time print_state (prog, ge, s);
  match Cexec.at_final_state s with
  | Some r ->   
    if !trace >= 1 then
      fprintf p "Time %d: program terminated (exit code = %ld)@."
        time (camlint_of_coqint r);
    (* Printf.printf "Program performed %d normalisations.\n" (!Values_symbolic_aux.num_simpl); *)

    begin match !mode with
    | All -> []
    | First | Random -> exit (Int32.to_int (camlint_of_coqint r))
    end
  | None ->
    let l = Cexec.do_step ge ns do_external_function do_inline_assembly w s in
    if l = [] || List.exists (fun (t,s) -> s = Stuckstate) l then begin
      pp_set_max_boxes p 1000;
      fprintf p "@[<hov 2>Stuck state: %a@]@." print_state (prog, ge, s);
      diagnose_stuck_state p ge w s;
      fprintf p "ERROR: Undefined behavior@.";
      exit 126
    end else begin
      List.map (fun (t, s') -> (s', do_events p ge time w t)) l
    end


let rec explore_one p ns prog ge time sw =
  let succs = do_step p ns prog ge time sw in
  if succs <> [] then begin
    let sw' =
      match !mode with
      | First -> List.hd succs
      | Random -> List.nth succs (Random.int (List.length succs))
      | All -> assert false in
    explore_one p ns prog ge (time + 1) sw'
  end

(* A priority queue structure where the priority is inversely proportional
   to the memory nextblock. *)

module PrioQueue = struct

  type elt = int * StateSet.elt

  type queue = Empty | Node of elt * queue * queue

  let empty = Empty

  let singleton elt = Node(elt, Empty, Empty)

  let higher_prio (time1, (s1, w1)) (time2, (s2, w2)) =
    P.lt (mem_state s1).Mem.nextblock (mem_state s2).Mem.nextblock

  let rec insert queue elt =
    match queue with
    | Empty -> Node(elt, Empty, Empty)
    | Node(e, left, right) ->
        if higher_prio elt e
        then Node(elt, insert right e, left)
        else Node(e, insert right elt, left)

  let rec remove_top = function
  | Empty -> assert false
  | Node(elt, left, Empty) -> left
  | Node(elt, Empty, right) -> right
  | Node(elt, (Node(lelt, _, _) as left),
              (Node(relt, _, _) as right)) ->
      if higher_prio lelt relt
      then Node(lelt, remove_top left, right)
      else Node(relt, left, remove_top right)

  let extract = function
  | Empty -> None
  | Node(elt, _, _) as queue -> Some(elt, remove_top queue)

  (* Return true if all elements of queue have strictly lower priority
     than elt. *)
  let dominate elt queue =
    match queue with
    | Empty -> true
    | Node(e, _, _) -> higher_prio elt e
end

let rec explore_all p ns prog ge seen queue =
  match PrioQueue.extract queue with
  | None -> ()
  | Some((time, sw) as tsw, queue') ->
      if StateSet.mem sw seen then
        explore_all p ns prog ge seen queue'
      else
        let succs = 
          List.rev_map (fun sw -> (time + 1, sw)) (do_step p ns prog ge time sw) in
        let queue'' = List.fold_left PrioQueue.insert queue' succs in
        let seen' = StateSet.add sw seen in
        let seen'' = 
          if PrioQueue.dominate tsw queue''
          then purge_seen (mem_state (fst sw)).Mem.nextblock seen'
          else seen' in
        explore_all p ns prog ge seen'' queue''

(* The variant of the source program used to build the world for
   executing events.  
   Volatile variables are turned into non-volatile ones, so that
     reads and writes can be performed.
   Other variables are turned into empty vars, so that
     reads and writes just fail.
   Functions are preserved, although they are not used. *)

let world_program prog =
  let change_def (id, gd) =
    match gd with
    | Gvar gv ->
        let gv' =
          if gv.gvar_volatile then
            {gv with gvar_readonly = false; gvar_volatile = false}
          else
            {gv with gvar_init = []} in
        (id, Gvar gv')
    | Gfun fd ->
        (id, gd) in
 {prog with prog_defs = List.map change_def prog.prog_defs}

(* Massaging the program to get a suitable "main" function *)

let change_main_function p old_main old_main_ty =
  let old_main = Evalof(Evar(old_main, old_main_ty), old_main_ty) in
  let arg1 = Csyntax.Eval(Eval(Vint(coqint_of_camlint 0l)), type_int32s) in
  let arg2 = arg1 in
  let body =
    Sreturn(Some(Ecall(old_main, Econs(arg1, Econs(arg2, Enil)), type_int32s))) in
  let new_main_fn =
    { fn_id = Camlcoq.P.of_int 1; fn_return = type_int32s; fn_callconv = cc_default;
      fn_params = []; fn_vars = []; fn_body = body } in
  let new_main_id = intern_string "___main" in
  { prog_main = new_main_id;
    prog_defs = (new_main_id, Gfun(Internal new_main_fn)) :: p.prog_defs }

let rec find_main_function name = function
  | [] -> None
  | (id, Gfun fd) :: gdl -> if id = name then Some fd else find_main_function name gdl
  | (id, Gvar v) :: gdl -> find_main_function name gdl

let fixup_main p =
  match find_main_function p.prog_main p.prog_defs with
  | None ->
    fprintf err_formatter "ERROR: no main() function";
    None
  | Some main_fd ->
    match type_of_fundef main_fd with
    | Tfunction(Tnil, Tint(I32, Signed, _), _) ->
      Some p
    | Tfunction(Tcons(Tint _, Tcons(Tpointer(Tpointer(Tint(I8,_,_),_),_), Tnil)),
                Tint _, _) as ty ->
      Some (change_main_function p p.prog_main ty)
    | _ ->
      fprintf err_formatter "ERROR: wrong type for main() function";
      None
  
(* Execution of a whole program *)

let execute prog =
  Mem.debug := !mem_debug;
  (* Values_symbolic_aux.dummy_number := !dummy_blocks; *)
  (* Values_symbolic_aux.dummy_size := !dummy_size; *)
  Random.self_init();
  let p = std_formatter in
  pp_set_max_indent p 30;
  pp_set_max_boxes p 10;
  match fixup_main prog with
  | None -> ()
  | Some prog1 ->
      let wprog = world_program prog1 in
      let wge = Genv.globalenv wprog in
      match Genv.init_mem Csem.fid (fun _ -> Z.of_sint 100) wprog with
      | None ->
          fprintf p "ERROR: World memory state undefined@."
      | Some wm ->
      match Cexec.do_initial_state prog1 (fun _ -> Z.of_sint 100) with
      | None ->
          fprintf p "ERROR: Initial state undefined@."
      | Some(ge, s) ->
         match Compiler.do_oracles prog with
         | None ->
            fprintf p "ERROR: Couldn't compute oracles@."
         | Some ((_,ns),_) ->
           match !mode with
           | First | Random ->
              explore_one p ns prog1 ge 0 (s, world wge wm)
           | All ->
              explore_all p ns prog1 ge StateSet.empty 
                          (PrioQueue.singleton (0, (s, world wge wm)))

                                
