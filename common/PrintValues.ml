
open Values
(* open Values_symbolic *)
open Values_symbolictype
open Integers
(* open Memdata *)
(* open Memtype *)
(* open Memory.Mem *)
(* open Maps *)


(* let print_value v = *)
(*   match v with *)
(*   | Vint n -> Printf.sprintf "int(%ld)" (Camlcoq.camlint_of_coqint n) *)
(*   | Vfloat f -> Printf.sprintf "float(%F)" (Camlcoq.camlfloat_of_coqfloat f) *)
(*   | Vsingle f -> Printf.sprintf "single(%F)" (Camlcoq.camlfloat_of_coqfloat32 f) *)
(*   | Vlong n -> Printf.sprintf "long(%Ld)" (Camlcoq.camlint64_of_coqint n) *)
(*   | Vptr(b,ofs) -> Printf.sprintf "<ptr(%d,%d)>" (Camlcoq.P.to_int b) (Camlcoq.Z.to_int ofs); *)
(*   | Vundef -> "<undef>" *)

let print_value v ty =
  let open Ctypes in
  match v, ty with
  | Vundef, _ -> "<vundef>"
  | Vint n, Ctypes.Tint(I32, Unsigned, _) -> Printf.sprintf "%ldU" (Camlcoq.camlint_of_coqint n)
  | Vint n , _-> Printf.sprintf "%ld" (Camlcoq.camlint_of_coqint n)
  | Vfloat f , _-> Printf.sprintf "%F" (Camlcoq.camlfloat_of_coqfloat f)
  | Vsingle f , _-> Printf.sprintf "%Ff" (Camlcoq.camlfloat_of_coqfloat32 f)
  | Vlong n , Ctypes.Tlong(Unsigned, _) -> Printf.sprintf "%LdLLU" (Camlcoq.camlint64_of_coqint n)
  | Vlong n , _-> Printf.sprintf "%LdLL" (Camlcoq.camlint64_of_coqint n)
  | Vptr(b,ofs), _ -> Printf.sprintf "<ptr(%d,%d)>" (Camlcoq.P.to_int b) (Camlcoq.Z.to_int ofs)
    
    
let print_int i = Camlcoq.camlint_of_coqint i
let print_nat n = Camlcoq.Nat.to_int n

let print_cmp_op c = 
  match c with
    Ceq -> "ceq"
  | Cne -> "cne"
  | Clt -> "clt"
  | Cle -> "cle"
  | Cgt -> "cgt"
  | Cge -> "cge"



let print_otsg (ot,sg) =
  (match sg with
    SEUnsigned -> "u"
  | SESigned -> "s") ^
    (match ot with
      Tint  -> "int"
    | Tlong -> "long"
    | Tsingle -> "single"
    | Tfloat -> "float"
    )

let print_unop u t e =
  match u with
  | OpBoolval -> Printf.sprintf "boolval(%s)" e
| OpNotbool -> Printf.sprintf "notbool(%s)" e
| OpNeg -> Printf.sprintf "neg(%s)" e
| OpNot -> Printf.sprintf "not(%s)" e
| OpRolm(i,j) -> Printf.sprintf "rolm(%s,%ld,%ld)" e (print_int i) (print_int j)
| OpZeroext(z) -> Printf.sprintf "zeroext(%s,%d)" e (Camlcoq.Z.to_int z)
| OpSignext(z) -> Printf.sprintf "signext(%s,%d)" e (Camlcoq.Z.to_int z)
| OpAbsf -> Printf.sprintf "absf(%s)" e
| OpConvert (sg,otsg2) -> Printf.sprintf "convert(%s,%s,%s)" (print_otsg (t,sg)) (print_otsg otsg2) e
| OpLoword -> Printf.sprintf "loword(%s)" e
| OpHiword -> Printf.sprintf "hiword(%s)" e
| OpSingleofbits -> Printf.sprintf "singleofbits(%s)" e
| OpDoubleofbits -> Printf.sprintf "doubleofbits(%s)" e
| OpBitsofsingle -> Printf.sprintf "singletobits(%s)" e
| OpBitsofdouble -> Printf.sprintf "doubletobits(%s)" e

let print_binop b e1 e2 =
  match b with
| OpAnd  -> Printf.sprintf "and(%s,%s)" e1 e2
| OpOr -> Printf.sprintf "or(%s,%s)" e1 e2
| OpXor -> Printf.sprintf "xor(%s,%s)" e1 e2
| OpAdd -> Printf.sprintf "add(%s,%s)" e1 e2
| OpSub -> Printf.sprintf "sub(%s,%s)" e1 e2
| OpMul -> Printf.sprintf "mul(%s,%s)" e1 e2
| OpMulh sg -> Printf.sprintf "mulh(%s,%s)" e1 e2
| OpDiv sg -> Printf.sprintf "divs(%s,%s)" e1 e2
| OpMod sg -> Printf.sprintf "modu(%s,%s)" e1 e2
| OpShr sg -> Printf.sprintf "shr(%s,%s)" e1 e2
| OpShl -> Printf.sprintf "shl(%s,%s)" e1 e2
| OpShrx -> Printf.sprintf "shrx(%s,%s)" e1 e2
| OpShr_carry  -> Printf.sprintf "shr_carry(%s,%s)" e1 e2
| OpRor -> Printf.sprintf "ror(%s,%s)" e1 e2
| OpCmp(sg,c) -> Printf.sprintf "cmp(%s,%s,%s)" (print_cmp_op c) e1 e2
| OpMull'  -> Printf.sprintf "mull'(%s,%s)" e1 e2
| OpFloatofwords -> Printf.sprintf "floatofwords(%s,%s)" e1 e2
| OpLongofwords -> Printf.sprintf "longofwords(%s,%s)" e1 e2
| OpSubOverflow -> Printf.sprintf "suboverflow(%s,%s)" e1 e2

                                  
let rec print_expr_symb_typed exp ty =
  match exp with
  | Eval v -> print_value v ty
  | Eundef(b,ofs) -> Printf.sprintf "<undef(%d,%d)>" (Camlcoq.P.to_int b) (Camlcoq.Z.to_int ofs)
  | Eunop (u,t,e) -> print_unop u t (print_expr_symb_typed e ty)
  | Ebinop (b,t,t',e1,e2) -> print_binop b (print_expr_symb_typed e1 ty) (print_expr_symb_typed e2 ty)
  (* | Eite (c,t,e1,e2) -> Printf.sprintf "ite(%s,%s,%s)" *)
  (*   (print_expr_symb c) (print_expr_symb e1) (print_expr_symb e2) *)


let print_expr_symb exp =
  print_expr_symb_typed exp Ctypes.Tvoid


let print_opt_value_symb v =
  let ty = Ctypes.Tvoid in
  match v with
    Some (Values_symbolictype.Eval v') -> print_value v' ty
  | Some e -> Printf.sprintf "<symbolic[%s]>" (print_expr_symb_typed e ty )
  | None -> "<none>"



