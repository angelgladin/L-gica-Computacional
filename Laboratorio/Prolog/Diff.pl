/**
  * Lógica computacional 2017-2
  * Tema : Operador de corte y listas diferenciables
  * Profesora: Lourdes del Carmen Gonzaléz Huesca
  * Ayudante: Roberto Monroy Argumedo
  * Laboratorio: Fernando A. Galicia Mendoza
  **/

/**
  * Relación que determina si dados X,Y,Z, Z es el mínimo
  * entre X e Y. Utilizando operador de corte.
  * @arg nat. Primer número natural.
  * @arg nat. Segundo número natural.
  * @arg nat. Natural mínimo
  **/
minimoC(X,Y,X) :- X =< Y,!.
minimoC(X,Y,Y) :- X > Y,!.


/**
  * Relación que determina si las listas diferenciables
  * l1,l2 y l3 cumplen que l3 = l1++l2.
  * @arg list. Primera lista a concatenar.
  * @arg list. Segunda lista a concatenar.
  * @arg list. Lista resultante de la concatenación.
  * Un ejemplo puede ser:
  * app([1,2,3|X]-X,[4,5,6]-X,Z-X).
  **/
app(A-B, B-C, A-C).

/**
  * Relación que determina si un término es un atómo.
  * @arg. Término a analizar.
  **/
constant(X) :- atomic(X).

/**
  * Relación que determina si la lista l2, tiene
  * todos los elementos de la lista de listas l1.
  * @arg list. Lista de listas.
  * @arg list. Lista con todos los elementos del primer argumento.
  **/
flatten(XS,YS) :- flatten(XS,[],YS),!.

/**
  * Relación auxiliar que ejecuta el flatten utilizando
  * un acumulador (pila).
  * @arg list. Lista de listas.
  * @arg list. Pila donde se acumularán los resultados.
  * @arg list. Lista con todos los elementos del primer argumento.
  **/
flatten([X|XS],S,YS) :- list(X),flatten(X,[XS|S],YS).
flatten([X|XS],S,[X|YS]) :- constant(X),X \= [],flatten(XS,S,YS).
flatten([],[X|S],YS) :- flatten(X,S,YS).
flatten([],[],[]).
list([_|_]).

/**
  * Relación que determina si dados dos números naturales X,Y,
  * Y es X+2. Utilizando call.
  * @arg nat. Argumento de la función.
  * @arg nat. Resultado de la suma.
  **/
esSumaDos(X,Y) :- call(plus(2),X,Y).