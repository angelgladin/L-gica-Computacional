% Estado inicial %
inicial(q0).
% Estado Final %
final(q3).

% Autómata finito determinista %
delta(q0,a,q1).
delta(q1,b,q2).
delta(q2,c,q1).
delta(q2,d,q3).
delta(q3,e,q0).

% Autómata finito no determinista %
delta(q0,0,q0).
delta(q0,1,q0).
delta(q0,1,q1).
delta(q1,0,q2).
delta(q2,1,q3).

% Relación que se cumple si y sólo si la lista de caractéres
% es aceptado por el autómata descrito.
afd(XS) :- inicial(Q0),
	   tExt(Q0,XS).

% Relación que se cumple si y sólo si a partir del estado q es
% posible llegar a q3 a través de la cadena.
tExt(Q,[X|XS]) :- delta(Q,X,Qi),
		  tExt(Qi,XS).
tExt(q3,[]) :- final(q3).

% Relación que se cumple si y sólo si la lista de caractéres
% es aceptado por el autómata descrito.
afn(XS) :- inicial(Q0),
	   tExt(Q0,XS).


