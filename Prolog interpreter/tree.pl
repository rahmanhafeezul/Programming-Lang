root(2).
child(2,3).
child(2,5).
child(3,6).
child(3,12).
intree(X):-root(X). 
intree(X):-child(Y,X),intree(Y).
child(X,Y)
