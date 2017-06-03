/**
  * Lógica computacional 2017-2
  * Tema : Listas
  * Profesora: Lourdes del Carmen Gonzaléz Huesca
  * Ayudante: Roberto Monroy Argumedo
  * Laboratorio: Fernando A. Galicia Mendoza
  **/

/**
  * @arg nat Término que representa un natural
  * Relación que indica si un término es un número natural.
  **/
natu(0).
natu(s(X)) :- natu(X).

%%Ejemplo: Hacer que prolog cuente hasta 4.

/**
  * @arg nat. Primer parámetro de la suma.
  * @arg nat. Segundo parámetro de la suma.
  * Relación que determina si x+y = z
  * suma 0 y = y
  * suma (S x) y = S (suma x y)
  * Autores: Fernanda y Eduardo
  **/
suma(0,Y,Y).
suma(s(X),Y,s(Z)) :- suma(X,Y,Z).

/**
  * Aqui las listas pueden contener varios tipos de datos, es decir,
  * heterogeneas.
  * Por ejemplo:
  * ¿Qué devuelve [X|Y] = [1 'a' natu(0) suma(s(s(0)),s(s(0)),X)] ?
  * ¿Cómo obtener mas elementos de la lista?
  **/

/**
  * @arg. Elemento a buscar.
  * @arg. Lista en donde se buscará.
  * Relación que determina si un elemento pertenece a una lista.
  **/
elem(X,[X|_]). 
elem(X,[_|XS]) :- elem(X,XS).

/**
  * @arg. Lista que se contará.
  * Relación que determina si un lista es de tamaño X.
  **/
long([],0).
long([_|XS],M) :- long(XS,N),M is N+1.

/**
  * @arg. Primer lista a comparar.
  * @arg. Segunda lista a comparar.
  * Relación que determina si dos listas son iguales.
  * Autores versión 5 min: Andrés y Daniel
  * Autor versión elegante: Leonardo
  **/
igual([],[]).
igual([X|XS],[X|YS]) :- igual(XS,YS).

/**
  * @arg. Primer lista a concatenar.
  * @arg. Segunda lista a concatenar.
  * Relación que determina si X es la concatenación de dos listas.
  * ¿Porqué está definida de esta forma?
  * Autores: Andrés y Daniel
  **/
app([],L,L).
app([H|T],L2,[H|L3])  :-  app(T,L2,L3).

/**
  * Última parte: Tratemos hasta donde lleguemos implementar árboles binarios
  * de búsqueda... les toca comentar.
  **/
istree(nil).
istree(t(I,_,D)) :- istree(I),istree(D).

preord(nil,[]).
preord(t(I,X,D),YS) :- preord(I,Y1),preord(D,Y2),
	app(Y1,[X],Y3),app(Y3,Y2,YS).

maxnum(X,Y,X) :- X >= Y.
maxnum(X,Y,Y) :- Y >= X.

maxi([X],X).
maxi([X|XS],Y) :- maxi(XS,Z),maxnum(Z,X,Y).

maxt(T,X) :- preord(T,L),maxi(L,X).

minnum(X,Y,X) :- X =< Y.
minnum(X,Y,Y) :- Y =< X.

mini([X],X).
mini([X|XS],Y) :- mini(XS,Z),minnum(Z,X,Y).

mint(T,X) :- preord(T,L),mini(L,X).