exp2(0,0,'Math Error') :- !.
exp2(X,0,1) :- X =\= 0, !.
exp2(X,Y,Z) :- A is Y -1, exp2(X,A,B), Z is B*X, !.

fact(0,1) :- !. 
fact(X,_):- X<0,!,fail. 
fact(X,R) :- X>0, Z is X-1, fact(Z,R1), R is X*R1,!.

ackermann2(0,N,X) :- X is N+1, !.
ackermann2(M, 0, X) :- M1 is M-1, ackermann2(M1, 1, X), !.
ackermann2(M, N, X) :- M1 is M-1, N1 is N-1, ackermann2(M, N1, X1), ackermann2(M1, X1, X),!.