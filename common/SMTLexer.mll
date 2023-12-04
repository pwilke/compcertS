{
  open Parser
  open SMTParser
  exception Eof
}

let digit = ['0'-'9''a'-'f']
let id = ['a'-'z'] ['a'-'z' '_' '0'-'9']*


rule token = parse
| "sat" { SAT }
| "unsat" { UNSAT}
| '(' { LPAREN}
| ')' { RPAREN}
| "error" {ERROR}
| "\"line " digit+ " column " digit+": model is not available\"" {ERROR_MSG}
| id as ident { IDENT(ident)}
| "#x" (digit+ as num) { NUM(num)}
| [' ' '\n' '\t'] { token lexbuf }
| eof { EOF }
| _ as c { Printf.printf "Unexpected symbol : '%c'\n" c; token lexbuf }


{

}
