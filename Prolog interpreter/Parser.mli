type token =
  | ID of (string)
  | VARIABLE of (string)
  | LPAREN
  | RPAREN
  | INTEGER of (int)
  | FLOAT of (float)
  | COMMA
  | NEWLINE
  | IF
  | DOT

val input :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> unit
