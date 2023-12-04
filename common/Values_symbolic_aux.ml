open AST
open Camlcoq
open Values
open Values_symbolictype
open PrintValues

let undef_count = ref 0			(* undefined expression counter, to give a name to each unedfined expression *)
let num_simpl = ref 0			(* simplification counter: used for stats printing at the end of execution *)

type z3expr =
| Z3undef of int * int
| Z3val of int
| Z3longval of int64
| Z3var of string*expr_sym
| Z3unop of unop_t * styp * z3expr
| Z3binop of binop_t * styp * styp * z3expr * z3expr
| Z3bot

type z3constraint = 
  Eq of z3expr * z3expr
| Neq of z3expr * z3expr
| Distinct of  z3expr list
| Not of z3constraint

(* To process a symbolic expression, we define three sets, from which we will build the Z3 model:
 * - a variable set, which consists of variable names (strings) of three forms: b_i, o_j, b_i_o_j, where i and j are integers.
 * - a block set, which holds the set of all blocks appearing in the pointers in the expression. This set holds triplets (block_name, size of block, alignment of block)
 * - a constraint set, which holds the constraints that link variables together:
 *   § b_i_o_j = b_i + o_j
 *   § o_j = j
 *   § b_i & align(b_i) = b_i
 * *)


module StringSet = Set.Make( 
  struct
    let compare = Pervasives.compare
    type t = string*string
  end )

module BlockSet = Set.Make( 
  struct
    let compare = Pervasives.compare
    type t = string*int*int
  end )

module ConstraintSet = Set.Make( 
  struct
    let compare = Pervasives.compare
    type t = z3constraint
  end )

let undef_name = function
Eundef (b,ofs) -> ((Camlcoq.P.to_int b),(Camlcoq.Z.to_int ofs))
  | _ -> failwith "Undefined undef_name for non-undef"
  
let var_name = function
Vptr (b,ofs) -> (Printf.sprintf "b_%d_o_%d" (Camlcoq.P.to_int b) (Camlcoq.Z.to_int ofs))
  | _ -> failwith "Undefined var_name for non-pointer"

let block_name =  function
Vptr (b,ofs) -> (Printf.sprintf "b_%d" (Camlcoq.P.to_int b))
  | _ -> failwith "Undefined block_name for non-pointer"

let offset_name = function
Vptr (b,ofs) -> (Printf.sprintf "o_%d" (Camlcoq.Z.to_int ofs))
  | _ -> failwith "Undefined offset_name for non-pointer"

let rec expr_symb_to_z3expr expr =
  match expr with
  | Eval v -> 
    begin match v with 
    | Vptr (b,ofs) -> Z3var ((var_name v),Eval v)
    | Vint n  -> Z3val (Camlcoq.Z.to_int n)
    | Vlong n -> Z3longval (Camlcoq.Z.to_int64 n)
    | Vundef -> Z3bot
    | Vfloat f -> failwith "No floats in simplifications"
    | Vsingle f -> failwith "No floats in simplifications"
    end
  | Eundef(b,ofs) -> let (x,y) = (undef_name expr) in
		     Z3undef(x,y)
  | Eunop (u,t,e) -> Z3unop (u,t,(expr_symb_to_z3expr e))
  | Ebinop (u,t,t',e1,e2) -> Z3binop (u,t,t',
				   (expr_symb_to_z3expr e1),
				   (expr_symb_to_z3expr e2))

let size_of_block bnds b = 
  let (lo,hi) = bnds b in
  Camlcoq.Z.to_int hi - Camlcoq.Z.to_int lo

let mask_of_block align b = 
  let msk = align b in 
  Camlcoq.Z.to_int (Integers.Int.unsigned msk)

let gen_vars_val v =
  match v with
    Eval (Vptr (b,ofs)) ->
      StringSet.add (var_name (Vptr (b,ofs)),"Word") 
	(StringSet.add (block_name (Vptr (b,ofs)),"Word") 
	   (StringSet.add (offset_name (Vptr (b,ofs)),"Word") 
	      StringSet.empty))
  | _ -> StringSet.empty

let gen_block_list bnds align v =
  match v with
    Eval (Vptr (b,_) as vv) -> 
      BlockSet.add ( (block_name vv),
		     (size_of_block bnds b),
		     (mask_of_block align b)) BlockSet.empty
  | _ -> BlockSet.empty

let gen_constraint_val align v =
  match v with
    Eval (Vptr (b,ofs') as vv) -> 
      let ofs = (Camlcoq.Z.to_int ofs') in
      let msk = (mask_of_block align b) in
      let bname = block_name vv in
      let oname = offset_name vv in
      let bvar = Z3var (bname,v) in
      let ovar = Z3var (oname,v) in
      ConstraintSet.add (
	Eq ((Z3var ((var_name vv),v)), (Z3binop (OpAdd,Tint,Tint,bvar,ovar))))	(* b_i_o_j = b_i + o_j *)
	(ConstraintSet.add (Eq (ovar, (Z3val ofs)))		(* o_j = j *)
	   (ConstraintSet.add (Eq (bvar,(Z3binop (OpAnd,Tint,Tint,bvar,(Z3val msk)))))	(* b & msk = b *)
	      ConstraintSet.empty ))
  | _ -> ConstraintSet.empty

let append_z3_sets v b c (vl,bl,cl) = 
  (StringSet.union v vl),
  (BlockSet.union b bl),
  (ConstraintSet.union c cl)

let rec create_z3_sets_rec bnds align expr (vl,bl,cl) = 
  let myrec = create_z3_sets_rec bnds align in
  match expr with
  | Z3undef(x,y) -> (StringSet.add (Printf.sprintf "undef_%d_%d" x y, "Dword") vl,bl,cl)
  | Z3val v -> (vl,bl,cl)
  | Z3longval v -> (vl,bl,cl)
  | Z3var (vname,v) -> append_z3_sets (gen_vars_val v) (gen_block_list bnds align v) (gen_constraint_val align v) (vl,bl,cl)
  | Z3unop (u,t,e) -> myrec e (vl,bl,cl)
  | Z3binop (b,t,t',e1,e2) -> myrec e1 (myrec e2 (vl,bl,cl))
  | Z3bot -> (vl,bl,cl)

let create_z3_sets bnds align expr = 
  create_z3_sets_rec bnds align expr (
                       (StringSet.add ("r","Word") (StringSet.add ("ro","Word") StringSet.empty)),
    BlockSet.empty,
    (ConstraintSet.add
       (Eq
	  (expr,
	   Z3binop(OpAdd,Tint,Tint,
		   Z3var("r",Eundef(BinNums.Coq_xH,BinNums.Z0)),
		   Z3var("ro",Eundef(BinNums.Coq_xH,BinNums.Z0))))) ConstraintSet.empty))

(*** BEGIN Printing function ***)

type result = Int | Long | Float | Single | Ptr
		     
let print_bv res (n:int64) =
  Printf.sprintf "((_ int2bv %d) %Ld)" (if res = Long then 64 else 32) n

let print_var v =
  Printf.sprintf "%s" v

let print_comp_function c sg = 
  match c, sg with
    Integers.Ceq,_ -> "="
  | Integers.Cne,_ -> "distinct"
  | Integers.Clt,SESigned -> "bvslt"
  | Integers.Cgt,SESigned -> "bvsgt"
  | Integers.Cle,SESigned -> "bvsle"
  | Integers.Cge,SESigned -> "bvsge"
  | Integers.Clt,SEUnsigned -> "bvult"
  | Integers.Cgt,SEUnsigned -> "bvugt"
  | Integers.Cle,SEUnsigned -> "bvule"
  | Integers.Cge,SEUnsigned -> "bvuge"

let print_z3_comp c sg a b = 
  Printf.sprintf "(%s %s %s)" (print_comp_function c sg) a b


(* http://stackoverflow.com/questions/13683563/whats-the-difference-between-mod-and-remainder
   -21 mod 4 is 3 because -21 + 4 x 6 is 3.
   But -21 divided by 4 gives -5 with a remainder of -1.
   __________  mod      remainder
   signed      bvsmod   bvsrem
   unsigned    bvurem   bvurem
*)

let print_otsg (ot,sg) =
  (match sg with
    SEUnsigned -> "u"
  | SESigned -> "s") ^
    (match ot with
      Tint -> "int"
    | Tlong -> "long"
    | Tsingle -> "single"
    | Tfloat -> "float"
    )

let res_of_typ ot = 
  match ot with
    Tint -> Int
  | Tlong -> Long
  | Tfloat -> Float
  | Tsingle -> Single

let print_cmp c sg e1 e2 =
  Printf.sprintf "(ite %s %s %s)" 
    (print_z3_comp c sg e1 e2) 
    (print_bv Int Int64.one) (print_bv Int Int64.zero)

let print_unop_z3 u t e =
  match u with
  | OpBoolval -> Printf.sprintf "(ite (= %s %s) #x00000000 #x00000001)" e (print_bv Int Int64.zero)
  | OpNotbool -> Printf.sprintf "(ite (= %s %s) #x00000001 #x00000000)" e (print_bv Int Int64.zero)    
  | OpNeg -> Printf.sprintf "(bvneg %s)" e
  | OpNot -> Printf.sprintf "(bvnot %s)" e
  | OpRolm (i,j) -> failwith (Printf.sprintf "rolm(%s,%d,%d)" e (Camlcoq.Z.to_int i) (Camlcoq.Z.to_int j))
  | OpLoword -> Printf.sprintf "((_ extract 31 0) %s)" e
  | OpHiword -> Printf.sprintf "((_ extract 63 32) %s)" e
  | OpZeroext z ->
    let zi = (Camlcoq.Z.to_int z) in
    Printf.sprintf "((_ zero_extend %d) ((_ extract %d 0) %s))" 
      ((match t with
	Tint -> 32
      | Tlong -> 64
      | Tsingle -> 32
      | Tfloat -> 64) - zi)
      (zi-1)
      e
  | OpSignext z ->
    let zi = (Camlcoq.Z.to_int z) in
    Printf.sprintf "((_ sign_extend %d) ((_ extract %d 0) %s))" 
      ((match t with
	Tint -> 32
      | Tlong -> 64
      | Tsingle -> 32
      | Tfloat -> 64) - zi)
      (zi-1)
      e
  | OpAbsf -> failwith (Printf.sprintf "absf(%s)" e)
  | OpConvert (sg,otsg2) -> 
    begin match (t,sg), otsg2 with
      (Tlong, SEUnsigned),(Tint, SEUnsigned) -> Printf.sprintf "((_ extract 31 0) %s)" e
    | (Tint, SEUnsigned),(Tlong, SEUnsigned) -> Printf.sprintf "((_ zero_extend 32) %s)" e
    | (Tint, SESigned),(Tlong, SESigned) -> Printf.sprintf "((_ sign_extend 32) %s)" e
    | _,_ -> failwith (Printf.sprintf "convert(%s,%s,%s)" (print_otsg (t,sg)) (print_otsg otsg2) e)
    end
  | OpSingleofbits -> failwith (Printf.sprintf "OpSingleofbits(%s)" e)
  | OpDoubleofbits -> failwith (Printf.sprintf "OpDoubleofbits(%s)" e)
  | OpBitsofsingle -> failwith (Printf.sprintf "OpBitsofsingle(%s)" e)
  | OpBitsofdouble -> failwith (Printf.sprintf "OpBitsofdouble(%s)" e)

let print_binop_z3 b t1 t2 e1 e2 =
  match b with
    OpAnd -> Printf.sprintf "(bvand %s %s)" e1 e2
| OpOr -> Printf.sprintf "(bvor %s %s)" (e1) (e2)
| OpXor -> Printf.sprintf "(bvxor %s %s)" (e1) (e2)
| OpAdd -> Printf.sprintf "(bvadd %s %s)" (e1) (e2)
| OpSub -> Printf.sprintf "(bvsub %s %s)" (e1) (e2)
| OpMul -> Printf.sprintf "(bvmul %s %s)" (e1) (e2)
| OpMulh sg -> failwith "high multiply not handled"
| OpDiv sg -> Printf.sprintf "(%s %s %s)" 
  (match sg with SESigned -> "bvsdiv" | SEUnsigned -> "bvudiv")
  (e1) (e2)
| OpMod sg -> Printf.sprintf "(%s %s %s)" 
  (match sg with SESigned -> "bvsmod" | SEUnsigned -> "bvumod")
  (e1) (e2)
| OpShrx -> Printf.sprintf "(bvashr %s %s)" e1 e2
| OpShr_carry -> 
  let one = (print_bv Int Int64.one) in
  let zero = (print_bv Int Int64.zero) in
  Printf.sprintf "(ite (and (bvslt %s %s) (distinct (bvand %s (bvsub (bvshl %s %s) %s)) %s)) %s %s)" e1 zero e1 one e2 one zero one zero
| OpRor -> failwith (Printf.sprintf "ror(%s,%s)" e1 e2)
| OpCmp (sg,c) -> print_cmp c sg e1 e2
| OpMull' -> failwith(Printf.sprintf "(bvmul %s %s)" e1 e2)
| OpFloatofwords  -> failwith (Printf.sprintf "floatofwords(%s,%s)" e1 e2)
| OpLongofwords -> failwith (Printf.sprintf "longofwords(%s,%s)" e1 e2)
| OpSubOverflow -> failwith (Printf.sprintf "suboverflow(%s,%s)" e1 e2)
| OpShr sg -> Printf.sprintf "(%s %s %s)" 
			     (match sg with SESigned -> "bvashr" | SEUnsigned -> "bvlshr") 
  (e1) (match t1 with Tint -> e2 | Tlong -> Printf.sprintf "((_ zero_extend 32) %s)" e2 | _ -> failwith "cant shr floats")
| OpShl -> Printf.sprintf "(bvshl %s %s)" (e1)
			  (match t1 with Tint -> e2 | Tlong -> Printf.sprintf "((_ zero_extend 32) %s)" e2 | _ -> failwith "cant shr floats")


let rec print_z3_expr res exp =
  match exp with
  | Z3undef(x,y) -> Printf.sprintf "undef_%d_%d" x y
  | Z3val v -> print_bv Int (Int64.of_int v)
  | Z3longval v -> print_bv Long v 
  | Z3var (v,_) -> print_var v
  | Z3unop (u,t,e) -> print_unop_z3 u t (print_z3_expr (res_of_typ t) e)
  | Z3binop (b,t,t',e1,e2) -> print_binop_z3 b t t'
    (print_z3_expr (res_of_typ t) e1)
    (print_z3_expr (res_of_typ t') e2)
  | Z3bot -> "bot"


(* http://stackoverflow.com/questions/3703000/logical-arithmetical-bitwise-shifts
   int y = (signed)x >> 1;    // arithmetic shift.
   int z = (unsigned)x >> 1;  // logical shift. *)
(* from Integers.v: shr_carry x y = 
  if lt x zero && negb (eq (and x (sub (shl one y) one)) zero)
  then one else zero. *)




let rec print_constraint res c =
  match c with
  | Eq (e1,e2) -> Printf.sprintf "(= %s %s)" (print_z3_expr res e1) (print_z3_expr res e2)
  | Neq (e1,e2) -> Printf.sprintf "(not (= %s %s))" (print_z3_expr res e1) (print_z3_expr res e2)
  | Distinct l -> Printf.sprintf "(distinct %s)" (List.fold_left (fun x y -> x ^ (print_z3_expr res y) ^ " ") "" l)
  | Not e -> Printf.sprintf "(not %s)" (print_constraint res e)

let print_blocksize_function list = 
  Printf.sprintf "(define-fun size ((b Word)) Word %s)\n" 
    (BlockSet.fold 
       (fun (v,s,_) x -> Printf.sprintf "(ite (= b %s) %s %s)" v (print_bv Int (Int64.of_int s)) x) 
       list "#x00000000")

let print_distinct_blocks res list =
  Printf.sprintf "(assert (distinct %s %s))\n" (print_bv res Int64.zero)
    (BlockSet.fold (fun (v,s,msk) x -> x ^ v ^ " ") list "")

let print_value_list res b = 
  (match res with 
  | Single | Float | Int | Long -> "ro "
  | Ptr -> "r ro " ) ^ (BlockSet.fold (fun  (y,_,_) x -> x ^ y ^ " ") b "")

let print_var_decl v =
  (StringSet.fold (fun (y,t) x -> x ^ (Printf.sprintf "(declare-const %s %s)\n" y t)) v "")

let print_word_decl res =
  (Printf.sprintf "(define-sort Word () (_ BitVec %d))\n" (if res = Long then 64 else 32)) ^
    (Printf.sprintf "(define-sort Dword () (_ BitVec 64))\n")

let print_non_overlap_assertion res =
  (if res = Ptr then "(assert (bvult ro (size r)))\n"
   else "") ^
    "(assert (forall ((b Word) (b1 Word) (o Word) (o1 Word))
    		(=> (and (not (= b b1))
    			 (bvult o (size b))
    			 (bvult o1 (size b1)))
    		    (distinct (bvadd b o) (bvadd b1 o1)))))\n" ^
"(assert (forall ((b Word) (o Word))
		(=> (bvult o (size b))
		    (distinct (bvadd b o) #x00000000))))\n"

let print_constraints res cset = 
  (ConstraintSet.fold (fun y x -> x ^ (Printf.sprintf "(assert %s)\n" (print_constraint res y))) cset "")

let print_get_model res b = 
    "(check-sat)\n"^
    (Printf.sprintf "(get-value (%s))\n" (print_value_list res b))

let rec print_pair_list l = 
  match l with
    [] -> ""
  | (s,v)::r -> Printf.sprintf "%s = %s\n%s" s v (print_pair_list r)


let rec print_smt l = 
  match l with
    [] -> ""
  | l'::r' -> "("^(print_pair_list l')  ^")\n"^ (print_smt r')

let print_val v =
  match v with
  | Vint n -> Printf.sprintf "%ld" (Camlcoq.camlint_of_coqint n)
  | Vfloat f -> Printf.sprintf "%F" (Camlcoq.camlfloat_of_coqfloat f)
  | Vsingle f -> Printf.sprintf "%F" (Camlcoq.camlfloat_of_coqfloat32 f)
  | Vlong n -> Printf.sprintf "%Ld" (Camlcoq.camlint64_of_coqint n)
  | Vptr(b,ofs) -> Printf.sprintf "<ptr(%d,%d)>" (Camlcoq.P.to_int b) (Camlcoq.Z.to_int ofs)
  | Vundef -> "<undef>"
    
(* let print_expr v = *)
(*   match v with *)
(*   | Eval v -> print_val v *)
(*   | Eundef(b,ofs) -> Printf.sprintf "<undef(%d,%d)>" (Camlcoq.P.to_int b) (Camlcoq.Z.to_int ofs) *)
(*   | Eunop (u,t,e) -> Printf *)
		
(*** END Printing functions ***)

let is_a_block r blist = Not (Distinct (r::blist))

let is_a_block_var str bset = is_a_block (Z3var(str,Eundef(BinNums.Coq_xH,BinNums.Z0))) 
  (List.map (fun (x,y,z) -> Z3var (x,Eundef(BinNums.Coq_xH,BinNums.Z0))) (BlockSet.elements bset))

let var_is_null str = Eq ((Z3var (str,Eundef(BinNums.Coq_xH,BinNums.Z0))),(Z3val 0))



let expr_to_lists bnds align z3expr res opt_constraint =
  let v,b,c' = create_z3_sets bnds align z3expr in
  (
  v,b,(ConstraintSet.add
	 (match res with
	 | Single | Float | Int | Long -> var_is_null "r"
	 | Ptr -> is_a_block_var "r" b
	 ) (match opt_constraint with
	   Some s -> ConstraintSet.add s c'
	 | None -> c')))

let create_z3_program bnds align expr res opt_constraint = 
  let z3expr = expr_symb_to_z3expr expr in
  let v,b,c = expr_to_lists bnds align z3expr res opt_constraint in
  (print_word_decl res ^
     print_var_decl v ^ 
     print_blocksize_function b ^
     print_non_overlap_assertion res ^
     print_distinct_blocks res b ^
     print_constraints res c^
     print_get_model res b, (v,b,c))
(* with *)
  (*   _ ->  *)
  (*     failwith (Printf.sprintf "error while parsing expr") *)


let load_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = String.create n in
  really_input ic s 0 n;
  close_in ic;
  (s)




let get_block_value_from_ident i l = 
  try List.assoc i l
  with Not_found -> failwith ("Ident "^i^" not found in model ???")

let rec get_block_ident_from_value l v = 
  let bv = (*blocks with value v*)
    List.filter (fun (i,j) -> v=j && i.[0] = 'b') l
  in
  try fst (List.hd bv)
  with _ -> (v^": Not found!")
 

let intval_from_string_rep s = Scanf.sscanf s "%x" (fun x -> x)

let lookup_block blockset blockid = 
  BlockSet.fold (fun (str,sz,msk) x -> if str = blockid then (match x with None -> Some (str,sz,msk) | Some v -> Some v) else x) blockset None

let mk_pointer blockset b ofs = 
  let bid = Scanf.sscanf b "b_%d" (fun x -> x) in
  let b' = P.of_int bid in
  let ofs' = Z.of_sint (intval_from_string_rep ofs) in
  match lookup_block blockset b with
    Some (str,sz,msk) ->
      Vptr (b',ofs')
  | _ -> failwith (Printf.sprintf "Failed to find pointer %s in blockset." b)



let smtfilename = Printf.sprintf "smtfile.%d.smt2" (Unix.getpid ())
let smtoutfile =  Printf.sprintf "smtout.%d" (Unix.getpid ())
let smtfilename2 = Printf.sprintf "smtfile2.%d.smt2" (Unix.getpid ())
let smtoutfile2 =  Printf.sprintf "smtout2.%d" (Unix.getpid ())

let getModel bnds align expr res =
  let smtfile = open_out smtfilename in
  let (prog,(v,b,c)) = create_z3_program bnds align expr res None in
  Printf.fprintf smtfile "%s" prog;
  close_out smtfile;
  ignore (Unix.system (Printf.sprintf "z3 -smt2 %s > %s" smtfilename smtoutfile));
  let smtout_chan = open_in smtoutfile in
  let lexbuf = Lexing.from_channel smtout_chan in 
  let result = SMTParser.main SMTLexer.token lexbuf in
  let model = 
    try List.hd result with _ -> Printf.printf "Could not find model!\n"; [] in
  close_in smtout_chan;
  (model,b)

let getSat bnds align expr res opt =
  let smtfile2 = open_out smtfilename2 in
  let (prog,(v,b,c)) = create_z3_program bnds align expr res opt in
  Printf.fprintf smtfile2 "%s" prog;
  close_out smtfile2;
  ignore (Unix.system (Printf.sprintf "z3 -smt2 %s > %s" smtfilename2 smtoutfile2));
  let smtout2 = open_in smtoutfile2 in
  let sat = input_line smtout2 in
  close_in smtout2;
  sat = "unsat"

let make_unicity_constraint model expr res =
  if res = Ptr then
    let res_bval = get_block_value_from_ident "r" model in
    let block_id = get_block_ident_from_value model res_bval in 
    Some(Neq(Z3var("r",Eundef(BinNums.Coq_xH,BinNums.Z0)),Z3var(block_id,Eundef(BinNums.Coq_xH,BinNums.Z0))))
  else
    let res_bval = get_block_value_from_ident "ro" model in
    let int_bval = intval_from_string_rep res_bval in
    Some(Neq(Z3var("ro",Eundef(BinNums.Coq_xH,BinNums.Z0)),Z3val(int_bval)))

(* let rec show_alignments align expr = *)
(*   match expr with *)
(*     Eval (Eptr(b,_)) -> Printf.printf "al %d \t= 0x%8x\n" (Camlcoq.P.to_int b) *)
(*       (Camlcoq.Z.to_int (align b)) *)
(*   | Eunop (_,_,e) -> show_alignments align e *)
(*   | Ebinop (_,_,_,e,f) -> show_alignments align e; *)
(*     show_alignments align f *)
(*   | _ -> () *)
  

  let norm (bnds:BinNums.positive -> BinNums.coq_Z * BinNums.coq_Z) (align: BinNums.positive -> Integers.Int.int) expr res =
    (* Printf.printf "normalising with alignments:\n"; *)
    (* show_alignments align expr; *)
  let log_file = 
    (* stdout *)
    open_out_gen [Open_creat; Open_text; Open_append] 0o640 "log.txt"
  in
  output_string log_file (Printf.sprintf "===============\n%s\n" (print_expr_symb expr));
  undef_count := 0;
  num_simpl := !num_simpl + 1;
  let z3expr = expr_symb_to_z3expr expr in
  ignore(z3expr);
  let ret =
    let model,b = getModel bnds align expr res in
    if model = [] then begin
      output_string log_file "Vundef\n";
    (* Printf.printf "Simplification returns Vundef because no solution was found.\n"; *) Vundef
    end else
      let unicity_constraint = make_unicity_constraint model expr res in
      if getSat bnds align expr res unicity_constraint then
	let ro = get_block_value_from_ident "ro" model in
	let int_bval = intval_from_string_rep ro in
	let result = 
	  match res with 
	    Int -> Vint (Camlcoq.Z.of_sint int_bval)
	  | Long -> Vlong (Camlcoq.Z.of_sint int_bval)
	  | Float -> failwith "floats not implemented"
	  | Single -> failwith "floats not implemented"
	  | Ptr -> mk_pointer b (get_block_ident_from_value model (get_block_value_from_ident "r" model)) ro in
	output_string log_file (Printf.sprintf "%s\n" (print_val result));
	result
      else
	(output_string log_file "Vundef\n";
	 Vundef)
  in (if log_file = stdout then () else close_out log_file); ret

						       
  let normalise bnds align e =
    match Memdata.get_type e with
      Tint ->
      begin match norm bnds align e Int with
	      Vint i -> Vint i
	    | _ -> norm bnds align e Ptr
      end
    | Tlong -> norm bnds align e Long
    | Tsingle -> norm bnds align e Single
    | Tfloat -> norm bnds align e Float
