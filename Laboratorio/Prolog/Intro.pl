/**
  * Lógica computacional 2017-2
  * Tema : Introducción a Prolog, números naturales
  * Profesora: Lourdes del Carmen Gonzaléz Huesca
  * Ayudante: Roberto Monroy Argumedo
  * Laboratorio: Fernando A. Galicia Mendoza
  **/

%%Esto es un comentario de una línea :D

/**
  * Es un comentario de varias
  * varias
  * ...
  * muchas líneas. ^_^
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

%%¿Como se está comportando la suma?

/**
  * @arg nat. Primer parámetro de la producto.
  * @arg nat. Segundo parámetro de la producto.
  * Relación que determina si x*y = z  * prod 0 y = 0
  * prod (S x) y = prod x (suma (S x) y)
  * Autores: Eduardo y Andrés
  **/
prod(0,_,0).
prod(s(X),Y,Z) :- prod(X,Y,W),suma(W,Y,Z).

%%¿Como se está comportando el producto?

/**
  * @arg nat. Primer parámetro de la exponenciación.
  * @arg nat. Segundo parámetro de la exponenciación.
  * Relación que determina si a*b = c
  * exp a 0 = 1
  * exp a (S b) = prod a (exp a b)
  * Autores:Osvaldo y Victor
  **/
exp(_,0,s(0)).
exp(X,s(Y),Z) :- prod(X,W,Z),exp(X,Y,W).

/**
  * @arg nat. Primer parámetro de la exponenciación.
  * @arg nat. Segundo parámetro de la exponenciación.
  * Relación que determina si a*b = c
  * fac 0 = 1
  * fac (S n) = prod (S n) (fact n)
  *Autores: Pedro, Erick
  **/
fac(0,s(0)).
fac(s(X),Y) :- prod(s(X),W,Y),fac(X,W).