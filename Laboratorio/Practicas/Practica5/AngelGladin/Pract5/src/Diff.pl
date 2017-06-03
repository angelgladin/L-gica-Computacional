
% Relación que verifica si la lista dada sea diferenciable.
flattendifl(XS,YS) :- flattendifl_aux(XS, YS-[]).

% Relación auxiliar que hace que una lista que tiene lista ponga los elementos
% de estos en una usando listas diferenciables.
flattendifl_aux([], X-X).
flattendifl_aux([X|XS], Y-Z) :- flattendifl_aux(X, Y-W),
				flattendifl_aux(XS, W-Z).
flattendifl_aux(X, [X|XS]-XS).
