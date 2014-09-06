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

open Parsing;;
# 2 "Parser.mly"
open Printf;;

type node = Node of string*int;;
type preterm = Empty|Var of string|Const of string|Op of (node*(preterm list));;
type signature = (string*int) list;;
type subs = (string*preterm) list;;

let lineno = ref (0);;

let rec member value signa = match signa with 
|  []-> false
| (x,y)::xs -> if x = value then true else member value xs;;

let rec ar value signa = match signa with 
|  []-> -1
| (x,y)::xs -> if x = value then y else ar value xs;;

let rec sigok signa = match signa with 
| [] ->true
| (x,y)::xs -> if member x xs = true then false else if y<0 then false else sigok xs;; 

let rec wellformed signa pret = match pret with
| Empty -> true
| Var(x) -> member x signa
| Const(x) -> member x signa
| Op(Node(s,i),pretl) -> (member s signa)&&(ar s signa = i)&&(i = List.length pretl)&&(applyallwellformed signa pretl)

and applyallwellformed signa pretl = match pretl with
| [] -> true
| x::xs -> (wellformed signa x)&&(applyallwellformed signa xs);;

let rec getsub value signa = match signa with 
|  []-> Empty
| (x,y)::xs -> if x = value then y else getsub value xs;;

let rec subst pret subs = match pret with
| Empty -> Empty
| Const(x) -> Const(x)
| Var (x) -> let replace = getsub x subs in if (replace = Empty) then Var(x) else replace
| Op(x, pretl) -> Op(x, applyallsubst pretl subs)

and applyallsubst pretl subs = match pretl with
| []->[]
| x::xs -> (subst x subs)::(applyallsubst xs subs) 

let rec present pret y = match pret with
| Empty -> false
| Const(x) -> if(x=y) then true else false
| Var (x) -> if(x=y) then true else false
| Op(Node(x,i), pretl) -> (x = y)||(applyallpresent pretl y)

and applyallpresent pretl y = match pretl with
| []->false
| x::xs -> (present x y)||(applyallpresent xs y) 

let rec join subs1 subs2 = match subs1 with
| []->subs2
| (x,y)::xs -> if (getsub x subs2 = Empty) then (x,y)::(join xs subs2) else (join xs subs2)

let rec mgu pret1 pret2 = match (pret1, pret2) with 
| (Empty, Empty) -> []
| (Const(x), Const(y)) -> if x=y then [] else [("false",(Const("false")))]
| (Var(x), y) -> if (y = Var(x)) then [(x,y)] else if (present y x) then [("false",(Const("false")))] else [(x,y)]
| (x, Var(y)) -> if (x = Var(y)) then [(y,x)] else if (present x y) then [("false",(Const("false")))] else [(y,x)]
| ((Op(Node(x,i), pretl1)), (Op(Node(y,j), pretl2))) -> if ((x = y)&&(i = j)) then applyallmgu pretl1 pretl2 else [("false",(Const("false")))]
| _ -> [("false",(Const("false")))]

and applyallmgu pret1 pret2 =  match (pret1, pret2) with 
| ([], []) -> []
| (x::xs,y::ys) -> let z = (mgu x y) in z@(applyallmgu (applyallsubst xs z)  (applyallsubst ys z) )
| (_,_) -> [("false",(Const("false")))]

let rec detect_fail subs = match subs with
	|[] -> false
	| ((x,y)::xs) -> if ((x = "false")&&y = Const("false")) then true else detect_fail xs

let stack = ref [];;
let statestack = ref [];;

let rec remqueue n oldstack newstack = match newstack with
	|[] -> []
	| x::xs -> if n = 0 then remqueue (-1) xs (newstack) else remqueue (n-1) xs (x::newstack)

let remo n = statestack := List.rev (remqueue n !statestack []);;

let rec applysubst sub1 sub2 = 
	match sub2 with
	| [] -> []
	| ((x,pret)::xs) -> (x,(subst pret sub1))::(applysubst sub1 xs)


let rec printt t = match t with
| Empty -> printf " Empty "
|Const(token) -> printf " constant ";print_string token
| Var(token) -> printf " var ";print_string token
| Op(Node(token,i),x) -> print_string token;printf "( ";
match x with
| [] -> printf " "
| y::ys -> printt y;List.iter(fun z ->printf " , ";printt z;) ys;printf " )";;

let rec printsub subs = match subs with
| [] -> ()
| x::xs -> let (s,b) = x in printf "  "; print_string s; printf "->"; printt b; printsub xs; flush stdout

let rec dfvar term = match term with
| Empty -> Empty
|Const(token) -> Const(token)
| Var(token) -> Var((String.sub token 1 ((String.length token) - 1)))
| Op(Node(token,i),x) -> let l = List.map(fun z -> dfvar z) x in Op(Node(token,i) , l);;

let rec union l1 l2 = match l1 with
| [] -> l2
| x::xs -> if (List.mem x l2 = true) then union xs l2 else union xs (x::l2)

let rec printqueue l = match l with
| [] -> ()
| x::xs ->  printf "\n"; let (pret, subs, a, b, c) = x in printt pret; printsub !subs; print_int !a; print_int !b; print_int !c; flush stdout; printqueue xs


let rec convert subs upind downind tlist  = match tlist with
| [] -> []
| x::xs -> ((x) , ref(subs) , ref(-1) , ref(upind) , ref(downind))::(convert subs upind downind xs);;

let rec hasvarspret pret = match pret with
| Empty -> []
|Const(token) -> []
| Var(token) -> [token]
| Op(Node(token,i),x) -> hasvarspretl x 

and hasvarspretl pretl = match pretl with
| [] -> []
| x::xs -> ( hasvarspret x )@( hasvarspretl xs )

let rec interpret row col = 
	let rowref = ref(row) in let colref = ref(col) in let curq = List.nth !statestack !rowref in
		let final = ref([]) in 
			while(!colref < (List.length curq)) do
				(let b2 = ref(true) in let b1 = ref(false) in 
					 let (curtree, cursub, curpos, upind, downind) = List.nth curq !colref in 
				while(!b2) do ( 
					let curline = List.nth !stack (!curpos+1) in 
					let unif = mgu (subst curtree !cursub) (List.hd curline) in  
					if ( detect_fail unif = true ) then (curpos := !curpos+1)
					else(
						if((List.length curline) > 1) then (
							b1 := true; b2 := false; curpos := !curpos+1; rowref := List.length !statestack;
							statestack := !statestack @ [convert unif 0 row (List.tl curline)];
							let retanswer = backtrack ((List.length !statestack) -1) 0 in 
								if (detect_fail retanswer = true) then 
									(b1 := false ; b2 := true; remo (List.length !statestack); upind :=0)
								else(
									if(!colref = ((List.length curq) -1)) then ( final := union (applysubst retanswer unif) !cursub )
									else( 
										let (nextree, nexsub, nexpos, nexupind, nexdownind) = List.nth curq (!colref+1) in 
										nexsub := union !cursub (applysubst retanswer !cursub) 
										)
									)
							)
					else (b1 := true; b2 := false; curpos := !curpos+1;
							if(!colref = ((List.length curq) -1)) then (final := union unif !cursub; printsub unif; printsub !cursub; flush stdout )
							else( 
									let (nextree, nexsub, nexpos, nexupind, nexdownind) = List.nth curq (!colref+1) in 
									nexsub := union !cursub unif ; 
								)
							)
					)
				); if(!curpos >= List.length !stack -1) then b2 := false
				done
			; if(!b1 = true) then colref := !colref +1
			else (final := backtrack row !colref; colref := 1000000) )
			done; !final 
			
and backtrack row col = 
	let rowref = ref(row) in let colref = ref(col) in let curq = List.nth !statestack !rowref in
		let final = ref([]) in let (curtree, cursub, curpos, upind, downind) = List.nth curq !colref in
		if(!curpos < ((List.length !stack) -1)) then 
			( if(!upind !=0) then 
				(let newcol = (List.length (List.nth !statestack !upind) -1) in 
				let ans = backtrack !upind newcol in 
				if (detect_fail ans = true) then (upind := 0; backtrack !upind !colref)
				else (
					let curline = List.nth !stack (!curpos) in let unif = mgu (subst curtree !cursub) (List.hd curline) in
					if(!colref = ((List.length curq) -1)) then (union (applysubst ans unif) !cursub)
					else (let (nextree, nexsub, nexpos, nexupind, nexdownind) = List.nth curq (!colref+1) in 
								nexsub := union (applysubst ans unif) !cursub ; backtrack !rowref (!colref+1))
							)
						)
				else	( backtrack !rowref !colref)
				)
				else(
					if( !colref != 0) then (
						if (!upind = 0) then (curpos := -1; cursub := []; backtrack !rowref (!colref-1))
						else(
							let newcol = (List.length (List.nth !statestack !upind) -1) in 
							let ans = backtrack !upind newcol in
							if (detect_fail ans = true) then (curpos := -1; cursub := []; backtrack !rowref (!colref-1))
							else(
								let curline = List.nth !stack (!curpos) in let unif = mgu (subst curtree !cursub) (List.hd curline) in
								if(!colref = ((List.length curq) -1)) then union (applysubst ans unif) !cursub
								else (let (nextree, nexsub, nexpos, nexupind, nexdownind) = List.nth curq (!colref+1) in 
									nexsub := union (applysubst ans unif) !cursub ; backtrack !rowref (!colref+1))
								)
							) 
						)
						else (
								if(!upind = 0) then (remo row;["false",Const("false")])
								else(
							let newcol = (List.length (List.nth !statestack !upind) -1) in 
							let ans = backtrack !upind newcol in
							if (detect_fail ans = true) then (remo row;["false",Const("false")])
							else(
								let curline = List.nth !stack (!curpos) in let unif = mgu (subst curtree !cursub) (List.hd curline) in
								if(!colref = ((List.length curq) -1)) then union (applysubst ans unif) !cursub
								else (let (nextree, nexsub, nexpos, nexupind, nexdownind) = List.nth curq (!colref+1) in 
									nexsub := union (applysubst ans unif) !cursub ; backtrack !rowref (!colref+1))
								)
							)
						)
					);;		
	
				
										 
exception Fail of string;;				
	

let rec printm sub q = let t = hasvarspretl q in 
match sub with 
| [] -> printf "True";flush stdout;
| (x , y)::xs -> if (List.exists (fun z -> (x = (String.sub z 1 (String.length z - 1)))) t) then (print_string x;printf " -> ";printt y;printf ";";) else ();printm xs q;printf "\n";flush stdout
								;;	
	
let result query =    statestack := !statestack @ [(convert ([])  0 0 query)];
											let answer = backtrack 0 0 in											
											match answer with
											| ("false",Const("false"))::xs -> raise (Fail "False")
											| _ -> (printsub answer;
											 				let b = ref (true) in
																while (!b) do
																	let tanswer = backtrack 0 (List.length query - 1) in
																	match tanswer  with
																	| ("false",Const("false"))::xs -> b := false
																	| _ ->  (printsub tanswer;) 
																						done);;
					

# 261 "Parser.ml"
let yytransl_const = [|
  259 (* LPAREN *);
  260 (* RPAREN *);
  263 (* COMMA *);
  264 (* NEWLINE *);
  265 (* IF *);
  266 (* DOT *);
    0|]

let yytransl_block = [|
  257 (* ID *);
  258 (* VARIABLE *);
  261 (* INTEGER *);
  262 (* FLOAT *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\002\000\002\000\004\000\004\000\005\000\007\000\
\008\000\008\000\006\000\010\000\010\000\009\000\009\000\009\000\
\009\000\009\000\003\000\000\000"

let yylen = "\002\000\
\000\000\002\000\002\000\003\000\001\000\001\000\002\000\004\000\
\001\000\003\000\004\000\001\000\003\000\001\000\001\000\001\000\
\001\000\001\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\020\000\000\000\000\000\005\000\006\000\
\000\000\000\000\002\000\000\000\000\000\000\000\003\000\000\000\
\007\000\000\000\015\000\016\000\017\000\018\000\000\000\009\000\
\004\000\000\000\019\000\012\000\000\000\008\000\000\000\013\000\
\011\000\010\000"

let yydgoto = "\002\000\
\004\000\005\000\011\000\006\000\007\000\008\000\022\000\023\000\
\024\000\014\000"

let yysindex = "\002\000\
\019\255\000\000\018\255\000\000\019\255\014\255\000\000\000\000\
\004\255\000\255\000\000\015\255\004\255\009\255\000\000\019\255\
\000\000\018\255\000\000\000\000\000\000\000\000\003\255\000\000\
\000\000\019\255\000\000\000\000\001\255\000\000\000\255\000\000\
\000\000\000\000"

let yyrindex = "\000\000\
\024\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\011\255\000\000\000\000\000\000\
\000\000\005\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\000\000\021\000\000\000\000\000\255\255\000\000\
\252\255\012\000"

let yytablesize = 28
let yytable = "\009\000\
\018\000\019\000\001\000\013\000\020\000\021\000\030\000\026\000\
\014\000\031\000\033\000\014\000\016\000\017\000\028\000\026\000\
\027\000\012\000\012\000\003\000\010\000\015\000\025\000\001\000\
\032\000\012\000\034\000\029\000"

let yycheck = "\001\000\
\001\001\002\001\001\000\005\000\005\001\006\001\004\001\007\001\
\004\001\007\001\010\001\007\001\009\001\010\001\016\000\007\001\
\008\001\007\001\008\001\001\001\003\001\008\001\008\001\000\000\
\026\000\005\000\031\000\016\000"

let yynames_const = "\
  LPAREN\000\
  RPAREN\000\
  COMMA\000\
  NEWLINE\000\
  IF\000\
  DOT\000\
  "

let yynames_block = "\
  ID\000\
  VARIABLE\000\
  INTEGER\000\
  FLOAT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    Obj.repr(
# 263 "Parser.mly"
            ()
# 352 "Parser.ml"
               : unit))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'code) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'query) in
    Obj.repr(
# 264 "Parser.mly"
             ( result _2;stack := [];statestack := [];lineno := 0 )
# 360 "Parser.ml"
               : unit))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'clause) in
    Obj.repr(
# 268 "Parser.mly"
              ()
# 367 "Parser.ml"
               : 'code))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'code) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'clause) in
    Obj.repr(
# 269 "Parser.mly"
                     ()
# 375 "Parser.ml"
               : 'code))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'fact) in
    Obj.repr(
# 273 "Parser.mly"
     (lineno := !lineno+1; stack := !stack @ [[_1]])
# 382 "Parser.ml"
               : 'clause))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'rule) in
    Obj.repr(
# 274 "Parser.mly"
      (lineno := !lineno+1;  stack := !stack @ [_1] )
# 389 "Parser.ml"
               : 'clause))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'atomic_predicate) in
    Obj.repr(
# 278 "Parser.mly"
                     (_1)
# 396 "Parser.ml"
               : 'fact))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'tlist) in
    Obj.repr(
# 282 "Parser.mly"
                       (Op(Node(_1,List.length(_3)), _3))
# 404 "Parser.ml"
               : 'atomic_predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 286 "Parser.mly"
     ([_1])
# 411 "Parser.ml"
               : 'tlist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'tlist) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 287 "Parser.mly"
                   (_1 @ [_3])
# 419 "Parser.ml"
               : 'tlist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'atomic_predicate) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'body) in
    Obj.repr(
# 291 "Parser.mly"
                             ([_1] @ _3)
# 427 "Parser.ml"
               : 'rule))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atomic_predicate) in
    Obj.repr(
# 295 "Parser.mly"
                 ([_1])
# 434 "Parser.ml"
               : 'body))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'body) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'atomic_predicate) in
    Obj.repr(
# 296 "Parser.mly"
                              (_1 @ [_3])
# 442 "Parser.ml"
               : 'body))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 300 "Parser.mly"
   (Const(_1))
# 449 "Parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 301 "Parser.mly"
           (Var( (string_of_int !lineno)^"$"^_1))
# 456 "Parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 302 "Parser.mly"
          (Const(string_of_int _1))
# 463 "Parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 303 "Parser.mly"
        (Const(string_of_float _1))
# 470 "Parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atomic_predicate) in
    Obj.repr(
# 304 "Parser.mly"
                   (_1)
# 477 "Parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'body) in
    Obj.repr(
# 307 "Parser.mly"
            (_1)
# 484 "Parser.ml"
               : 'query))
(* Entry input *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let input (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : unit)
;;
# 309 "Parser.mly"
  
# 511 "Parser.ml"
