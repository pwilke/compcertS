%token SAT UNSAT LPAREN RPAREN EOF ERROR ERROR_MSG
%token <string> IDENT
%token <string> NUM


%start main
%type <(((string*string) list) list)> main
%%

main:
  SAT main { $2}
 |UNSAT main { $2}
 |LPAREN ERROR ERROR_MSG RPAREN main { $5 }
 |LPAREN vallist RPAREN main { $2::$4 }
 |EOF { []}
 | error { Printf.printf "Unexpected token in main\n"; [] }
;

vallist:
 |LPAREN IDENT NUM RPAREN vallist {   ($2,$3)::$5 }
 |LPAREN IDENT NUM RPAREN {  [($2,$3)] }
 | error {Printf.printf "Unexpected token in vallist\n";[]}
;
