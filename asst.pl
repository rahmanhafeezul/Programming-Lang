%constants define

const(X) :- X==tt.
const(X) :- X==ff.
const(X) :- atom(X),!.
const(X) :- number(X), !.
val(X):- number(X).
list([]).
list([X|Y]).

size([],0).
size([_|T],N):-size(T,M),N is M+1.
tuple([],0).
tuple(A,N):- list(A),size(A,N).

%variable define

variable(X).

%
const_type(X, bool) :- X==tt.
const_type(X, bool) :- X==ff.
const_type(X,string) :- atom(X),!.
const_type(X, int) :- number(X), !.
execute(lambda(variable(X),E),M,_,closure(lambda(variable(X),E),M)).


evalarith(A+B,M,C):-evalarith(A,M,AV),evalarith(B,M,BV),C is AV+BV.
evalarith(A-B,M,C):-evalarith(A,M,AV),evalarith(B,M,BV),C is AV-BV.
evalarith(A*B,M,C):-evalarith(A,M,AV),evalarith(B,M,BV),C is AV*BV.
evalarith(variable(X),M,Y):- lookup(M,variable(X),Y).

evalarith(X,_,X).
lookup(M,X,Y) :- append(_,[(X,Y)|_],M).

evalbool(true,_,tt).
evalbool(false,_,ff).

not_b(tt,ff).
not_b(ff,tt).

and_b(tt,tt,tt).
and_b(ff,tt,ff).
and_b(tt,ff,ff).
and_b(ff,ff,ff).

or_b(tt,tt,tt).
or_b(ff,tt,tt).
or_b(tt,ff,tt).
or_b(ff,ff,ff).


eq(V1,V2,tt) :- V1 == V2.
eq(V1,V2,ff) :- \+ V1 == V2.

lte(V1,V2,tt) :- V1 =&lt; V2.
lte(V1,V2,ff) :- \+ V1 =&lt; V2.
evalbool(not(B),M,V) :- evalbool(B,M,V1), not_b(V1,V).
evalbool(and(B1,B2),M,V) :- evalbool(B1,M,V1), evalbool(B2,M,V2), and_b(V1,V2,V).
evalbool(or(B1,B2),M,V) :- evalbool(B1,M,V1), evalbool(B2,M,V2), or_b(V1,V2,V).
evalbool(eq(A1,A2),M,V) :-  evalarith(A1,M,V1),  evalarith(A2,M,V2),  eq(V1,V2,V).
evalbool(lte(A1,A2),M,V) :-  evalarith(A1,M,V1),  evalarith(A2,M,V2),  lte(V1,V2,V).
execute(true,_,_,tt).
execute(false,_,_,ff).


execute(A+B,M1,M1,C):-evalarith(A+B,M1,C).
execute(A-B,M1,M1,C):-evalarith(A-B,M1,C).
execute(A*B,M1,M1,C):-evalarith(A*B,M1,C).
execute(and(A,B),M1,M1,C):-evalbool(and(A,B),M1,C).
execute(or(A,B),M1,M1,C):-evalbool(or(A,B),M1,C).
execute(not(A),M1,M1,C):-evalbool(not(A),M1,C).
execute(eq(A,B),M1,M1,C):-evalbool(eq(A,B),M1,C).
execute(lte(A,B),M1,M1,C):-evalbool(lte(A,B),M1,C).
execute(variable(X),G,G,A):- evalarith(variable(X),G,A).



execute(skip,M,M,_).
execute(seq(S1,S2),M1,M3,_) :- execute(S1,M1,M2_), execute(S2,M2,M3_).
execute(par(S1,S2),M1,M2,_) :- execute(S1,M1,M4_),execute(S2,M1,M5_),union(M4,M5,M2).
execute(assign(X,A),M1,M2,_) :- execute(A,M1,M1,Y), update(M1,X,Y,M2).
execute(ifthenelse(B,S1,S2),M1,M2,C) :- execute(B,M1,M1,tt), execute(S1,M1,M2,C),execute(S2,M1,M3,An).
execute(ifthenelse(B,S1,S2),M1,M2,C) :- execute(B,M1,M1,ff), execute(S2,M1,M2,C),execute(S1,M1,M3,An).
execute(let(S1,A),M1,M3,C):- execute(S1,M1,M2,_),execute(A,M2,M3,C).

execute(local(S1,S2),M1,M4,_) :- execute(S1,M1,M2,_), execute(S2,M2,M3,_),remove2nd(M3,M4).
execute(e1ofe2(E1,E2),M1,M2,Ans):-execute(E1,M1,_,closure(lambda(X,E),M1)),execute(E2,M1,M3,Ans1),execute(E,[(X,Ans1)|M1],M2,Ans).


update([],X,Y,[(X,Y)]).
update([(X,_)|M],X,Y,[(X,Y)|M]).
update([(X1,Y1)|M1],X2,Y2,[(X1,Y1)|M2]) :- \+ X1 = X2, update(M1,X2,Y2,M2).

projhead(A,X):-list(A),A=[X|Y].
projtail(A,Y):-list(A),A=[X|Y].

tuple_nth(A,N,X) :- tuple_nth(A,0,N,X) .

tuple_nth([X|A],N,N,X) :- !. tuple_nth([_|A],T,N,X) :- T1 is T+1 , tuple_nth(A,T1,N,X).

union([H|T],[],[H|T]).     
union([],[H|T],[H|T]).    
union([H|T], SET2, RESULT) :- member(H,SET2), union(T,SET2,RESULT).    
union([H|T], SET2, [H|RESULT]) :- not(member(H,SET2)), union(T,SET2,RESULT).

extend(Gamma, X, T, [(X, T) | Gamma]).
execute(N,_,_,N).
type_check(Gamma,recursive(F,X),T):- type_check(Gamma,X,T1),extend(Gamma,X,T1,Gamma2),type_check(Gamma2,F,arrow(T1,T)).

type_check(Gamma,unit,unit).
type_check(Gamma, N, int) :- number(N).
type_check(Gamma,[X|Y],list).
type_check(Gamma,tuple(A,N),tupl):-type_check(Gamma,A,list),type_check(Gamma,N,int).

type_check(Gamma, X, T) :- lookUp(X, Gamma, T).
type_check(Gamma, if(M, N1, N2), T) :- type_check(Gamma, M, bool), type_check(Gamma, N1, T), type_check(Gamma, N2, T).
type_check(Gamma, let(S1,A), T) :- type_check(Gamma, S1, Gamma2), type_check(Gamma2, A, T).
type_check(Gamma, lambda(S1,A), T) :- type_check(Gamma, S1, Gamma2), type_check(Gamma2, A, T).

type_check(Gamma,A+B,int):- type_check(Gamma,A,int),type_check(Gamma,B,int).
type_check(Gamma,A-B,int):- type_check(Gamma,A,int),type_check(Gamma,B,int).
type_check(Gamma,A*B,int):- type_check(Gamma,A,int),type_check(Gamma,B,int).
type_check(Gamma,not(A),bool):- type_check(Gamma,A,bool).
type_check(Gamma,and(A,B),bool):- type_check(Gamma,A,bool),type_check(Gamma,B,bool).
type_check(Gamma,or(A,B),bool):- type_check(Gamma,A,bool),type_check(Gamma,B,bool).
type_check(Gamma, e1ofe2(M, N), T) :- type_check(Gamma, N, TN),type_check(Gamma, M, arrow(TN, T)).
type_check(Gamma,equal(A,B),bool):- type_check(Gamma,A,T),type_check(Gamma,B,T).
type_check(Gamma,lt(A,B),bool):- type_check(Gamma,A,int),type_check(Gamma,B,int).
type_check(Gamma,gt(A,B),bool):- type_check(Gamma,A,int),type_check(Gamma,B,int).
type_check(Gamma,assign(X,E),Gamma2):-type_check(Gamma,E,T),extend(Gamma,X,T,Gamma2).
type_check(Gamma,letrec(F,X),T):- type_check(Gamma,X,T1),extend(Gamma,X,T1,Gamma2),type_check(Gamma2,F,arrow(T1,T)).
type_check(Gamma,par(S1,S2),Gamma3):- type_check(Gamma,S1,Gamma4),type_check(Gamma,S2,Gamma5),union(Gamma4,Gamma5,Gamma3).
type_check(Gamma,seq(S1,S2),Gamma2):- type_check(Gamma,S1,Gamma1),type_check(Gamma1,S2,Gamma2).
type_check(Gamma,local(S1,S2),Gamma3):-type_check(Gamma,S1,Gamma1),type_check(Gamma1,S2,Gamma2),remove2nd(Gamma2,Gamma3).
remove2nd([X|[Y|Z]],[X|Z]).

lookUp(X,Gamma,Y) :- append(_,[(X,Y)|_],Gamma).

lazy(closure(variable(X),M),closure(Y,M)):- lookup(M,variable(X),Y).

%closure(E,M,X):- X=(E,M).
%call()
lazy(closure(A,M),closure(A,M)):- number(A).
lazy_bool(closure(tt,M),closure(tt,M)).
lazy_bool(closure(ff,M),closure(ff,M)).
lazy(closure(A+B,M),closure(C,M)):- lazy(closure(A,M),closure(AV,M)),lazy(closure(B,M),closure(BV,M)),C is AV+BV. 
lazy(closure(A-B,M),closure(C,M)):- lazy(closure(A,M),closure(AV,M)),lazy(closure(B,M),closure(BV,M)),C is AV-BV. 
lazy(closure(A*B,M),closure(C,M)):- lazy(closure(A,M),closure(AV,M)),lazy(closure(B,M),closure(BV,M)),C is AV*BV. 
lazy_bool(closure(and(A,B),M),closure(C,M)):-lazy_bool(closure(A,M),closure(AV,M)),lazy_bool(closure(B,M),closure(BV,M)),and_b(AV,BV,C).
lazy_bool(closure(or(A,B)),M,closure(C,M)):-lazy_bool(closure(A,M),closure(AV,M)),lazy_bool(closure(B,M),closure(BV,M)),or_b(AV,BV,C).
lazy_bool(closure(not(A),M),closure(C,M)):-lazy_bool(closure(A,M),closure(AV,M)),not_b(AV,C).
lazy_bool(closure(eq(A,B),M),closure(C,M)):-lazy(closure(A,M),closure(AV,M)),lazy(closure(B,M),closure(BV,M)),eq(AV,BV,C).
lazy_bool(closure(lte(A,B),M),closure(C,M)):-lazy(closure(A,M),closure(AV,M)),lazy(closure(B,M),closure(BV,M)),lte(AV,BV,C).


lazy_execute(closure(N,_),closure(N,_)):-number(N).
lazy_execute(closure(true,_),closure(tt,_)).
lazy_execute(closure(false,_),closure(ff,_)).

lazy_execute(closure(A+B,M1),closure(C,M1)):- lazy(closure(A+B,M1),closure(C,M1)).
lazy_execute(closure(A-B,M1),closure(C,M1)):- lazy(closure(A-B,M1),closure(C,M1)).
lazy_execute(closure(A*B,M1),closure(C,M1)):- lazy(closure(A*B,M1),closure(C,M1)).
lazy_execute(closure(variable(X),G),closure(A,G)):- lazy(closure(variable(X),G),closure(A,G)).
lazy_execute(closure(and(A,B),M1),closure(C,M1)):- lazy_bool(closure(and(A,B),M1),closure(C,M1)).
lazy_execute(closure(or(A,B),M1),closure(C,M1)):- lazy_bool(closure(or(A,B),M1),closure(C,M1)).
lazy_execute(closure(eq(A,B),M1),closure(C,M1)):- lazy_bool(closure(eq(A,B),M1),closure(C,M1)).
lazy_execute(closure(lte(A,B),M1),closure(C,M1)):- lazy_bool(closure(lte(A,B),M1),closure(C,M1)).


lazy_execute(closure(not(A),M1),closure(C,M1)):- lazy_execute(closure(not(A),M1),closure(C,M1)).


lazy_execute(closure(ifthenelse(B,S1,_),M1),closure(C,M2)):-lazy_execute(closure(B,M1),closure(tt,M1)), lazy_execute(closure(S1,M1),closure(C,M2)).
lazy_execute(closure(ifthenelse(B,_,S2),M1),closure(C,M2)):-lazy_execute(closure(B,M1),closure(ff,M1)), lazy_execute(closure(S2,M1),closure(C,M2)).

lazy_execute(closure(assign(X,E),M1),closure(_,M2)):- lazy_execute(closure(E,M1),closure(Y,M1)),update(M1,X,Y,M2).
lazy_execute(closure(seq(S1,S2),M1),closure(_,M3)):-lazy_execute(closure(S1,M1),closure(_,M2)),lazy_execute(closure(S2,M2),closure(_,M3)).
lazy_execute(closure(par(S1,S2),M1),closure(_,M2)):- lazy_execute(closure(S1,M1),closure(_,M4)),lazy_execute(closure(S2,M1),closure(_,M5)),union(M4,M5,M2).
lazy_execute(closure(local(S1,S2),M1),closure(_,M4)):-lazy_execute(closure(S1,M1),closure(_,M2)),lazy_execute(closure(S2,M2),closure(_,M3)),remove2nd(M3,M4).
lazy_execute(closure(let(S1,A),M1),closure(C,M3)):- lazy_execute(closure(S1,M1),closure(_,M2)),lazy_execute(closure(A,M2),closure(C,M3)).




%execute(e1ofe2(lambda(variable(x),variable(x)+10),variable(x)+5),[(variable(x),2)],Y,V).
% type_check([(variable(x),bool),(variable(y),bool)],and(variable(x),variable(y)),R).
% type_check([(F,arrow(string,int)),(variable(x),int)],letrec(F,variable(x)),X).
