
type exp = V of string
              |ConstInt of int|ConstBool of bool
              |Appl of exp*exp
              |Plus of exp*exp|Mul of exp*exp
              |Or of exp*exp|And of exp*exp|Not of exp
              |Lessthan_equal of exp*exp|Equal of exp*exp
              |Tuple of exp_list
              |Proj of exp *int
              |Let of def list*exp
              |Parl of def list*exp
              |Seq of def* def *exp
              |Local of def *def
              |Lambda of string * exp
              |Proj1 of exp*exp
                            |Proj2 of exp*exp

              |Call of exp*exp
              |If_then_else of exp* exp* exp
              and def = Def of string*exp 
              and exp_list = Exp1 of exp| Exp2 of exp*exp_list;; 


type closure = Closure of exp*((string * closure) list)|Closure_tuple of exp_list*((string*closure) list);;


(* val t = Table([("d",Table([]),lambda("s",var("s"))),("d",Table([]),var("n")),("f",Table([]),var("d"))]); *)

exception NotInTable;;

(* let rec lookup =function
          (s,Table([])) -> raise NotInTable;
          |(s,Table(h::t)) -> (let (s1,t1,e1) = h
                                   in
                                    (if s=s1 then Closure(t1,e1)
                                    else lookup(s,Table(t))));; 
 *)
  
(* (Closure(gamma,Lambda(s,e)),Closure(t,e1)::s1) ->let
                                               Table(t1) = gamma
                                             in
                                               let 
                                               tnew = Table((s,t,e1)::t1) 
                                              in 
                                                execute(Closure(tnew,e),s1);
  |(Closure(gamma,Appl(e1,e2)),s) -> execute(Closure(gamma,e1),Closure(gamma,e2)::s)  
  |(Closure(gamma,Var(x)),s) -> try
                              execute(lookup(x,gamma),s) 
                            with NotInTable -> Closure(gamma,Var(x));
  |(Closure(gamma,ConstInt(x)),s) ->Closure(gamma,ConstInt(x));
  |(Closure(gamma,Plus(e1,e2)),s)-> execute(Closure(gamma,e1),s),execute(Closure(gamma,e2),s) *)

let  rec gamma_new(x)=match x with 

  ([],gamma) -> gamma
|(d::xs,gamma) -> let Def(v,e)=d in [(v,Closure(e,gamma))]@gamma_new(xs,gamma);;

   let rec execute(x)= match x with 
  |(Closure(ConstInt(x),gamma),stack)->ConstInt(x)
  |(Closure(ConstBool(x),gamma),stack)->ConstBool(x)
  |(Closure(Plus(ConstInt(n1),ConstInt(n2)),gamma),stack)->ConstInt(n1+n2)
  |(Closure(Mul(ConstInt(n1),ConstInt(n2)),gamma),stack)->ConstInt(n1*n2)
  |(Closure(Not(ConstBool(true)),gamma),stack)->ConstBool(false)
  |(Closure(And(ConstBool(n1),ConstBool(n2)),gamma),stack)->ConstBool(n1&&n2)
  |(Closure(Or(ConstBool(n1),ConstBool(n2)),gamma),stack)->ConstBool(n1||n2)
  |(Closure(And(ConstBool(n1),ConstBool(n2)),gamma),stack)->ConstBool(n1&&n2)
  |(Closure(Lessthan_equal(ConstInt(n1),ConstInt(n2)),gamma),stack) -> (if n1<=n2 then ConstBool(true) else ConstBool(false))
  |(Closure(Equal(ConstInt(n1),ConstInt(n2)),gamma),stack) -> (if n1=n2 then ConstBool(true) else ConstBool(false))

  |(Closure(Plus(e1,e2),gamma),stack) -> execute (Closure(Plus(execute(Closure(e1,gamma),stack),execute(Closure(e2,gamma),stack)),gamma),stack)
  |(Closure(Mul(e1,e2),gamma),stack) -> execute (Closure(Mul(execute(Closure(e1,gamma),stack),execute(Closure(e2,gamma),stack)),gamma),stack)
  |(Closure(Or(e1,e2),gamma),stack) -> execute (Closure(Or(execute(Closure(e1,gamma),stack),execute(Closure(e2,gamma),stack)),gamma),stack)
  |(Closure(And(e1,e2),gamma),stack) -> execute (Closure(And(execute(Closure(e1,gamma),stack),execute(Closure(e2,gamma),stack)),gamma),stack)
  |(Closure(Lessthan_equal(e1,e2),gamma),stack) -> execute (Closure(Lessthan_equal(execute(Closure(e1,gamma),stack),execute(Closure(e2,gamma),stack)),gamma),stack)
  |(Closure(Equal(e1,e2),gamma),stack) -> execute (Closure(Equal(execute(Closure(e1,gamma),stack),execute(Closure(e2,gamma),stack)),gamma),stack)
  |(Closure(Not(e),gamma),stack)->execute(Closure(Not(execute(Closure(e,gamma),stack)),gamma),stack)
  |(Closure(V(v),x::xs),stack) ->(let (a,b)= x
                              in
                              (if a=v then execute(b,stack) else execute(Closure(V(v),xs),stack)
                              ))
  | (Closure(V(v),[]),stack) -> (raise NotInTable)
  |(Closure(Tuple(e),gamma),stack) -> Tuple(t_execute(Closure_tuple(e,gamma),stack))
  |(Closure(Let(l,e),gamma),stack) -> execute(Closure(e,gamma_new(l,gamma)),stack)
  |(Closure(Parl(l,e),gamma),stack) -> execute(Closure(e,gamma_new(l,gamma)),stack)
    |(Closure(Seq(l1,l2,e),gamma),stack) -> execute(Closure(e,gamma_new_seq(l1,l2,gamma)),stack)

  |(Closure(If_then_else(e1,e2,e3),gamma),stack) -> if (execute(Closure(e1,gamma),stack)=ConstBool(true)) then execute(Closure(e2,gamma),stack) else execute(Closure(e3,gamma),stack)
(* |(Closure(Local(l1,l2),gamma),stack) -> execute(Closure(),stack)
 *)
|(Closure(Lambda(v,e),gamma),stack) -> execute(Closure(e,[(v,Closure(e,gamma))]@gamma),stack)
|(Closure(Call(e1,e2),gamma),stack) -> execute(Closure(e1,gamma),Closure(e2,gamma)::stack)
|(Closure(Proj1(e1,e2),gamma),stack) -> execute(Closure(e1,gamma),stack)
|(Closure(Proj2(e1,e2),gamma),stack) -> execute(Closure(e2,gamma),stack)

  and gamma_new_seq(Def(v,e),Def(v1,e1),gamma)= let gamma2=[(v,Closure(e,gamma))]@gamma in [(v1,Closure(e1,gamma2))]

 and t_execute(Closure_tuple(Exp2(e,e1),gamma),stack) = Exp2(execute(Closure(e,gamma),stack),t_execute(Closure_tuple(e1,gamma),stack));;
