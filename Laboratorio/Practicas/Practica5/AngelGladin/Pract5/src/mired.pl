% Relaciones con las herencias
esparte(musica,instrumento).
esparte(musica,artista).
esparte(musica,interpretacion).
sedivide(instrumento,cuerdas).
sedivide(instrumento,aire).
sedivide(instrumento,percusion).
ejemplo(cuerdas,guitarra).
ejemplo(cuerdas,violin).
ejemplo(cuerdas,contrabajo).
ejemplo(aire,flauta).
ejemplo(aire,clarinete).
ejemplo(aire,trompeta).
ejemplo(percusion,bateria).
ejemplo(percusion,triangulo).
ejemplo(artista,hombre).
ejemplo(artista,mujer).
ejemplo(hombre,jimmorrison).
ejemplo(hombre,jimmypage).
ejemplo(mujer,justinbiber).
ejemplo(mujer,maluma).
ejemplo(interpretacion,baby).
ejemplo(interpretacion,muevetuculito).
ejemplo(justinbiber,baby).

% Relación que dados X,Y,Z, determina si Z hereda de Y a través de X.
satisface(X,Y,Z) :- call(X,Y,Z).
satisface(X,Y,Z) :- call(X,U,Z), satisface(esparte,Y,U).
satisface(X,Y,Z) :- call(X,U,Z), satisface(ejemplo,Y,U).
satisface(X,Y,Z) :- call(X,U,Z), satisface(sedivide,Y,U).
