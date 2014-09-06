{
open Parser

}
let z = ['0']
let identifiers = ['a'-'z']['_' ''' '0'-'9' 'a'-'z' 'A'-'Z']*	
let whitespace = [' ' '\t']
let nonzero = ['1'-'9']
let zerodigit = ['0'-'9']
let capitalvariables = ['A'-'Z']
let variables = capitalvariables ['_' ''' '0'-'9' 'a'-'z' 'A'-'Z']*
let int = z | ['-']? ((nonzero) zerodigit*) 
let enter = ['\n']	
let comma = [',']
let dot = ['.'] 
let float = zerodigit ['.'] zerodigit
| ((int '.') zerodigit*) nonzero ['e'] int
| ((int '.') zerodigit*) nonzero "e-" int
| int ['e'] int
| int "e-" int
| ((int '.') zerodigit*) nonzero


rule token = parse
| int  as num	{INTEGER(int_of_string num)}
| float  as reals	{FLOAT(float_of_string (reals))}
| variables  as identifiers	{VARIABLE(identifiers)}
| '(' {LPAREN}
| ')' {RPAREN}
| ',' {COMMA}
| ' ' {token lexbuf}
| '\t' {token lexbuf}
| '\n' {NEWLINE}
| '.' {DOT}
| ":-" {IF}
| identifiers  as id_nvar	{ID(id_nvar)}
  | _ as c	{token lexbuf}
  | eof	{raise End_of_file}
