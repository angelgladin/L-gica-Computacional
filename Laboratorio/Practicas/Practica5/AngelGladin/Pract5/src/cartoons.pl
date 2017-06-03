% Hay cinco casas consecutivas, cada una tiene un color diferente y habitada por 
% personajes de distintas caricaturas. Cada una tiene una mascota distinta y 
% manejan un tipo distinto de arma y tienen una bebida favorita.

% Cada casa se puede ver como una tupla de 5 elementos, es decir.
% (_Personaje,_Color,_Bebida,_Arma,_Mascota)

% Relación que contiene una 5-tupla que dice la información de la persona.
% El primer parámetro representa la posición de la casa en la calle.
personas(0, []).
personas(N, [(_Personaje,_Color,_Bebida,_Arma,_Mascota)|XS]) :- N1 is N-1, personas(N1,XS).

% Relación que me da la relación de la i-ésima persona.
persona(1, [P|_], P).
persona(N, [_|XS], R) :- N1 is N-1, persona(N1, XS, R).

%% Hipótesis %%

% 1. Bugs Bunny vive en la casa roja.
pista1([(buggs_bunny,roja,_, _, _)|_]).
pista1([_|XS]) :- pista1(XS).

% 2. Steven tiene un león.
pista2([(steven,_,_,_,leon)|_]).
pista2([_|XS]) :- pista2(XS).

% 3. En la casa verde se bebe whisky.
pista3([(_,verde,whisky,_,_)|_]).
pista3([_|XS]) :- pista3(XS).

% 4. Star bebe chocolate.
pista4([(star,_,chocolate,_,_)|_]).
pista4([_|XS]) :- pista4(XS).

% 5. La casa verde está inmediatamente al lado de la morada.
pista5([(_,verde,_,_,_),(_,morada,_,_,_)|_]).
pista5([(_,morada,_,_,_),(_,verde,_,_,_)|_]).
pista5([_|XS]) :- pista5(XS).

% 6. El dueño de la espada tiene caracoles.
pista6([(_,_,_,espada,caracoles)|_]).
pista6([_|XS]) :- pista6(XS).

% 7. El personaje que ataca con un pistola vive en la casa amarilla.
pista7([(_,amarilla,_,pistola,_)|_]).
pista7([_|XS]) :- pista7(XS).

% 8. En la casa de en medio se bebe leche.
pista8(Personas) :- persona(3, Personas, (_,_,leche,_,_)).

% 9. Mickey Mouse vive en la primera casa (de izquierda a derecha).
pista9(Personas) :- persona(1, Personas, (mickey_mouse,_,_,_,_)).

% 10. El que usa un sable vive en la casa siguiente del que tiene un zorro.
pista10([(_,_,_,sable,_),(_,_,_,_,zorro)|_]).
pista10([(_,_,_,_,zorro),(_,_,_,sable,_)|_]).
pista10([_|XS]) :- pista10(XS).

% 11. La pistola la usa el personaje que vive en la casa siguiente a donde está el caballo.
pista11([(_,_,_,pistola,_),(_,_,_,_,caballo)|_]).
pista11([(_,_,_,_,caballo),(_,_,_,pistola,_)|_]).
pista11([_|XS]) :- pista11(XS).

% 12. El que usa rayos como arma bebe coca cola.
pista12([(_,_,rayos,coca_cola,_)|_]).
pista12([_|XS]) :- pista12(XS).

% 13. Batman usa sus puños como arma.
pista13([(batman,_,_,punos,_)|_]).
pista13([_|XS]) :- pista13(XS).

% 14. Mickey Mouse vive en la casa siguiente a la casa azul.
pista14([(mickey_mouse,_,_,_,_),(_,azul,_,_,_)|_]).
pista14([(_,azul,_,_,_),(mickey_mouse,_,_,_,_)|_]).
pista14([_|XS]) :- pista14(XS).

% ¿Quién es el dueño del perro?
% batman %
pregunta1([(_,_,_,_,perro)|_]).
pregunta1([_|XS]) :- pregunta1(XS).

% ¿Quién bebe agua?
% mickey_mouse %
pregunta2([(_,_,agua,_,_)|_]).
pregunta2([_|XS]) :- pregunta2(XS).

%% Respuestas %%
% X = [(mickey_mouse, amarilla, agua, pistola, zorro),
%        (star, azul, chocolate, sable, caballo),  
%(buggs_bunny, roja, leche, espada, caracoles), 
%(steven, morada, rayos, coca_cola, leon), 
% (batman, verde, whisky, punos, perro)] .

solucion(Personas) :-
    personas(5, Personas),
    pista1(Personas),
    pista2(Personas),
    pista3(Personas),
    pista4(Personas),
    pista5(Personas),
    pista6(Personas),
    pista7(Personas),
    pista8(Personas),
    pista9(Personas),
    pista10(Personas),
    pista11(Personas),
    pista12(Personas),
    pista13(Personas),
    pista14(Personas),
    pregunta1(Personas),
    pregunta2(Personas).
