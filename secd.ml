type opcode = CONST of int | BCONST of bool
                 |PLUS|MULT
                 |TUPLE of int| PROJ of int*int
                 |LOOKUP of string
                 |OR|AND|NOT
                 |APP|COND of opcode list*opcode list
                 |RET
                 |CLOS of string* opcode list
                 |BIND of string
                 |SIMPLE |SEQ |PARA of opcode list*opcode list;;

type exp =  ConstInt of int|ConstBool of bool 
               |Var of string  
               |Plus of exp*exp|Mul of exp*exp
               |Or of exp*exp|And of exp*exp|Not of exp
               |Tuple of exp list
               |Proj of exp *int
               |IfThenElse of exp*exp*exp
               |Lambda of string*exp
               |Apply of exp*exp
               |Cl of string*opcode list;;

type def = Simple of string*exp
              |Seq of def*def
              |Para of def*def;;

type table = Table of (string * exp * table) list;;

type closure = Clos of exp*table;;

type dump = Dump of closure list*table*opcode list;;

exception VarNotFound;;

type secd = Secd of closure list*table*opcode list*dump list;;

exception IntersectionNotNull;;

let rec compile(x) = match x with 
ConstInt(x) -> [CONST(x)];
|ConstBool(x) -> [BCONST(x)];
   |Var(s) -> LOOKUP(s)::[];
   |Plus(e1,e2)  -> compile(e1)@compile(e2)@[PLUS]
   |Mul(e1,e2)  -> compile(e1)@compile(e2)@[MULT]
   |Or(e1,e2) -> compile(e1)@compile(e2)@[OR]
   |And(e1,e2)  -> compile(e1)@compile(e2)@[AND]
   |Not(e1)  -> compile(e1)@[NOT] 
   |Tuple(h::t) -> let
                              len = List.length (h::t);
                             in 
                             (let rec sep(x) = match x with 
                             	[] -> []
                                |(h::t) -> compile(h)@sep(t);
                             in
                              (sep(h::t)@[TUPLE(len)]));
  |Proj(Tuple(h::t),i) -> 
                              compile(Tuple(h::t))@[PROJ(List.length (h::t),i)];
  |IfThenElse(e1,e2,e3) -> compile(e1)@[COND(compile(e2),compile(e3))]    
   |Lambda(s,e) -> [CLOS(s,compile(e))]
   |Apply(e1,e2) -> compile(e1)@compile(e2)@[APP]@[RET];;

let not(x) = match x with 
true -> false
   |false -> true;;


let rec lookup(x) = match x with 
(s,Table([])) -> raise VarNotFound
   |(s,Table(h::t)) -> let
                               (s1,o1,ta) = h
                            in 
                              if s=s1 then Clos(o1,ta)
                              else lookup(s,Table(t));;  
                             
let rec valu(a) = match a with 
 Plus(ConstInt(x),ConstInt(y)) -> ConstInt(x+y)
   |Plus(e1,e2) -> valu(Plus(valu(e1),valu(e2)))
   |ConstInt(x) -> ConstInt(x)  
   |ConstBool(x) -> ConstBool(x)  
      |Mul(ConstInt(x),ConstInt(y)) -> ConstInt(x*y)
      |Mul(e1,e2) -> valu(Mul(valu(e1),valu(e2)))
      |Or(ConstBool(x),ConstBool(y)) -> ConstBool(x || y)
      |Or(e1,e2) -> valu(Or(valu(e1),valu(e2)))

      |And(ConstBool(x),ConstBool(y)) -> ConstBool(x && y)
      |And(e1,e2) -> valu(And(valu(e1),valu(e2))) 

      |Not(ConstBool(x)) -> ConstBool(not(x))
      |Not(e1) -> valu(Not(valu(e1)));;

exception IntersectionNotNull;;

let rec extract(r)=match r with 
                   [] -> []
                      |(BIND(x)::t) -> x::extract(t)
                      
                      |(h::t) -> extract(t);;


let rec contains(q)= match q with 

                   (x,[]) -> false 
                      |(x,h::t) -> if x=h then true else contains(x,t);;
    let rec checkCommon(s)=match s with 
                   ([],t2) -> true
                      |(h1::t1,t2) -> if contains(h1,t2) then false    
                                                else checkCommon(t1,t2) ;;
                  

let  check(a,b) = 
                    checkCommon(extract(a),extract(b));;

let rec compileDef(q)= match q with 
 (Simple(x,e)) -> compile(Lambda(x,e))@[BIND(x)]
   |(Seq(a,b)) -> compileDef(a)@compileDef(b)
   |(Para(a,b)) -> if check(compileDef(a),compileDef(b)) = true then [PARA(compileDef(a),compileDef(b))]
                            else raise IntersectionNotNull;;









(*val t2 = Table([("s",constInt(3),Table([])),("f",constBool(false),Table([]))]);*)
exception NumberExceedsTupleCount;;

let rec extrac(q) = match q with 
 (s,res,0) -> res
 |(h::s,res,n) -> let
                                                     Clos(a,b) = h  
                                                    in 
                                                     extrac(s,[a]@res,n-1);;

let rec extract2(q)=match q with 
 ([],h) -> raise NumberExceedsTupleCount 
                                                |(h::t,n) -> if n=1 then h else extract2(t,n-1) ;;    
                                            
                                                    
let rec pop(q)=match q with 
(t,0) -> t
   |(h::t,n) -> pop(t,n-1);;
let rec execute(q)= match q with 
 (Secd(s,e,[],d)) -> (s,e)
   |(Secd(s,e,CONST(x)::c,d)) -> execute(Secd(Clos(ConstInt(x),e)::s,e,c,d))
   |(Secd(s,e,BCONST(x)::c,d)) -> execute(Secd(Clos(ConstBool(x),e)::s,e,c,d))
   |(Secd(h1::h2::s,e,PLUS::c,d)) -> let
                                             Clos(ConstInt(x),e1) = h1 
                                         in
                                            (  let Clos(ConstInt(y),e2) = h2

                                           in
                                             (
                                             	execute(Secd(Clos(ConstInt(x+y),e)::s,e,c,d))
                                             )


                                            )
                                           
   |(Secd(h1::h2::s,e,MULT::c,d)) -> let
                                             Clos(ConstInt(x),e1) = h1 
                                           in let  Clos(ConstInt(y),e2) = h2

                                           in
                                             execute(Secd(Clos(ConstInt(x*y),e)::s,e,c,d))
                                           
   |(Secd(h1::h2::s,e,OR::c,d)) -> let
                                             Clos(ConstBool(x),e1) = h1 
                                            in let  Clos(ConstBool(y),e2) = h2

                                           in
                                             execute(Secd(Clos(ConstBool(x || y),e)::s,e,c,d))
                                           
   |(Secd(h1::h2::s,e,AND::c,d)) -> let
                                             Clos(ConstBool(x),e1) = h1 
                                         in let   Clos(ConstBool(y),e2) = h2

                                           in
                                             execute(Secd(Clos(ConstBool(x && y),e)::s,e,c,d))
                                           
   |(Secd(h1::s,e,NOT::c,d)) -> let
                                             Clos(ConstBool(x),e1) = h1 
                                            
                                           in
                                             execute(Secd(Clos(ConstBool(not(x)),e)::s,e,c,d))
                                           
   |(Secd(s,e,LOOKUP(x)::c,d)) -> execute(Secd(lookup(x,e)::s,e,c,d))
   |(Secd(s,e,TUPLE(n)::c,d)) -> let
                                                  
                                          res = Tuple(extrac(s,[],n))
                                        in let  snew = pop(s,n) 
                                        in
                                         execute(Secd(Clos(res,e)::pop(s,n),e,c,d))  
                                        
   |(Secd(h1::s,e,PROJ(n,i)::c,d)) -> let
                                             
                                              Clos(Tuple(h::t),e) = h1
                                             in let res = Clos(extract2(h::t,i),e) 
                                              in
                                               execute(Secd(res::s,e,c,d))
                                              
   

   |(Secd(h::s,e,COND(c1,c2)::c,d)) -> let
                                                Clos(ConstBool(x),r) = h;
                                             in
                                              if x=true then execute(Secd(s,e,c1@c,d))
                                              else execute(Secd(s,e,c2@c,d))   
                                              
   |(Secd(s,e,CLOS(x,c1)::c,d)) -> execute(Secd(Clos(Cl(x,c1),e)::s,e,c,d))
   |(Secd(h1::h2::s,e,APP::c,d)) -> let
                                             Clos(x,r) = h1
                                            in let Clos(Cl(g,c1),e1) = h2
                                            in let cL = valu(x)
                                            in let Table(t) = e
                                          in
                                           execute(Secd(s,Table((g,cL,e)::t),c1,Dump(s,e,c)::d))
                                          
   |(Secd(h::s2,e2,RET::c2,Dump(s,e,c)::d)) -> execute(Secd(h::s,e,c,d))     
   |(Secd(h::s,e,BIND(x)::c,d)) -> let
                                            Clos(Cl(x,c1),e1) = h
                                           in let ([Clos(a,b)],l) = execute(Secd([],e,c1,d))
                                          in let Table(t) = e 
                                         in
                                           execute(Secd(s,Table((x,a,e)::t),c,d))                                           
                                         
   |(Secd(s,e,PARA(c1,c2)::c,d)) -> let
                                             (a,b) = execute(Secd(s,e,c1,d))
                                            in let (f,l) = execute(Secd(s,e,c2,d))
                                            in let Table(t1) = b
                                            in let Table(t2) = l
                                            in let Table(t) = e
                                          in
                                           execute(Secd(s,Table(t1@t2@t),c,d));;
let run(q)= match q with 
 (e,t) -> let
                    c  = compile(e)
                    in let (a,b) =  execute(Secd([],t,c,[]))                   
                   in                     
                    a ;;
                   
                  

let runDef(q)=match q with
 (d,t) -> let
                        g = compileDef(d)
                      in let (a,b)  = execute(Secd([],t,g,[]))
                      in let rec extract(q)=match q with 
                      (Table([])) -> []
                         |(Table((a,b,c)::t)) -> (a,b)::extract(Table(t))
                      in
                       b;;
                        

(*
run(ConstInt(5),Table([]));     
run(ConstBool(true),Table([]));
run(Plus(ConstInt(6),ConstInt(10)),Table([]));
run(Var("s"),Table([("s",ConstInt(24),Table([]))]));
run(Tuple([ConstBool(true),Plus(ConstInt(23),ConstInt(56))]),Table([]));
run(Proj(Tuple([ConstInt(2),And(ConstBool(true),ConstBool(false)),Plus(ConstInt(3),ConstInt(15))]),2),Table([]));
run(IfThenElse(Not(ConstBool(false)),ConstInt(2),Plus(ConstInt(4),ConstInt(3))),Table([]));
run(Lambda("r",Plus(ConstInt(3),Var("r"))),Table([]));
run(Apply(Lambda("x",Plus(ConstInt(4),Var("x"))),ConstInt(7)),Table([]));

definitions

runDef(Simple("x",Plus(ConstInt(3),ConstInt(4))),Table([]));
runDef(Seq(Simple("x",ConstInt(5)),Simple("y",Plus(ConstInt(3),Var("x")))),Table([]));
runDef(Para(Simple("x",ConstBool(true)),Seq(Simple("y",Or(ConstBool(true),ConstBool(true))),Simple("z",Var("y")))),Table([]));  // when intersection is null
runDef(Para(Simple("x",ConstBool(true)),Seq(Simple("y",Or(ConstBool(true),Var("x"))),Simple("z",Var("y")))),Table([]));         // when intersection is not null









*)





                  
                             
  







  