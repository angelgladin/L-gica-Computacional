(*
* Lógica computacional 2017-2
* Tema: Introducción a Coq.
* Profesora: Lourdes del Carmen González Huesca
* Ayudante: Roberto Monroy Argumedo
* Laboratorio: Fernando A. Galicia Mendoza
*)

(*Biblioteca para que se vean bonitas algunas cosas.*)
Require Import Utf8.

(*Biblioteca para utilizar algunas funciones sobre el tipo nat.*)
Require Import Arith.

(*Biblioteca para utilizar algunas funciones sobre el tipo bool.*)
Require Import Bool.

(*
*********************************************************
* Programación funcional                                *
*********************************************************
*)


(*Definición de la estructura de datos lista.*)
Inductive lista (A:Type) : Type :=
| Nil : lista A
| Cons : A -> lista A -> lista A.

(*Principio de inducción para listas.*)
Check lista_ind.

(*Ejemplo de función recursiva, recordar que debe ser recursión
primitiva.*)
Fixpoint long {A:Type} (l:lista A) : nat :=
  match l with
  | Nil _ => 0
  | Cons _ x xs => 1 + long xs
  end.

(*Ejemplos.*)
Eval compute in long (Cons nat 1 (Cons nat 2 (Nil nat))).
Eval compute in long (Cons nat 1 (Cons nat 2 (Cons nat 3 (Nil nat)))).
Eval compute in long (Nil nat).

(*El tipo option es el Maybe de Coq.*)
Print option.

(*
***************************
* 1.1. Lista y option
* head_error
* last_error
* nth_elem
***************************
*)

(*Definición que dada una lista devuelve la
  cabeza de la lista `envuelto` con el tipo
  option para evitar errores*)
Definition head_error {A:Type} (l:lista A) : option A :=
  match l with
  | Nil _ => None
  | Cons _ x xs => Some x
  end.

(*Ejemplos.*)
Eval compute in head_error (Cons nat 1 (Cons nat 2 (Nil nat))).
Eval compute in head_error (Cons nat 3 (Cons nat 2 (Cons nat 1 (Nil nat)))).
Eval compute in head_error (Nil nat).

(*Función recursiva que devuelve el último elemento de
  una lista.*)
Fixpoint last_error {A:Type} (l:lista A) : option A :=
  match l with
  | Nil _ => None
  | Cons _ x (Nil _) => Some x
  | Cons _ x xs => last_error xs
  end.

(*Ejemplos.*)
Eval compute in last_error (Cons nat 1 (Nil nat)).
Eval compute in last_error (Cons nat 1 (Cons nat 2 (Cons nat 3 (Nil nat)))).
Eval compute in last_error (Nil nat).

(*Función revursiva que devuelve el n-ésimo elemento
  de la lista.*)
Fixpoint nthElem {A:Type} (l:lista A) (n:nat) : option A :=
  match l,n with
  | Nil _, _ => None
  | Cons _ x xs, 0 => Some x
  | Cons _ x xs, S m => nthElem xs m
  end.

(*Ejemplos.*)
Eval compute in nthElem (Cons nat 1 (Nil nat)) 0.
Eval compute in nthElem (Cons nat 1 (Cons nat 2 (Cons nat 3 (Nil nat)))) (S(S(0))).
Eval compute in nthElem (Nil nat) (S(S(0))).

(*
**************************************
* 1.2. Números naturales con paridad
* PNat
* mist
* norm
**************************************
*)

(*Vernáculo que representa la gramática de los números
  con paridad*)
Inductive pNat : Type :=
| Cero : pNat
| D : pNat -> pNat
| I : pNat -> pNat.

(*Función que normaliza la gramatica ya que se puede
  generar al cero infinitamente y con esta función
  normalizamos las representaciones del cero*)
Fixpoint norm (p:pNat) : pNat :=
  match p with
  | Cero => Cero
  | I pn => (I (norm pn))
  | D pn => match norm pn with
            | Cero => Cero
            | x => (D x)
            end
  end.

(*Ejemplos*)
Eval compute in norm (D (I Cero)).
Eval compute in norm (D (D Cero)).
Eval compute in norm (I (D (D Cero))).
Eval compute in norm (I (I (D Cero))).
Eval compute in norm (D (I Cero)).
Eval compute in norm (I Cero).
Eval compute in norm (I (D Cero)).
Eval compute in norm (D (I (I (D (D (D (D (D (D Cero))))))))).

(*Función recursiva auxiliar que suma dos números de 
 la gramática nPnat, es de utilidad para `mist`*)
Fixpoint suma (n:pNat) (m:pNat) : pNat :=
  match n,m with
  | Cero, x => x
  | x, Cero => x
  | D x, D y => D (suma x y)
  | D x, I y => I (suma x y)
  | I x, D y => I (suma x y)
  | I x, I y => D (I (suma x y))
  end.

(*Ejemplos lo normalizo por que el usuario puede ser tonto.*)
(*Suma  2  2  =  4 => (D (D (I Cero)))*)
Eval compute in norm (suma (D (I Cero)) (D (I Cero))).
(*Suma  6  7  =  13 => (I (I (I (I Cero))))*)
Eval compute in norm (suma (D (D (D (I Cero)))) (I (I (I (Cero))))).
(*Suma  3  4  =  7 => (I (I (I (Cero)))))*)
Eval compute in norm (suma (I (I Cero)) (D (D (I Cero)))).

(*Función recursiva auxiliar que multiplica dos números de 
 la gramática nPnat, es de utilidad para `mist`*)
Fixpoint prod (n:pNat) (m:pNat) : pNat :=
  match n,m with
  | Cero, x => Cero
  | x, Cero => Cero
  | D x, D y => D (D (prod x y))
  | D x, I y => suma (D (D (prod x y))) (D x)
  | I x, D y => suma (D (D (prod x y))) (D y)
  | I x, I y => I (suma (suma (D (prod x y)) x) y)
  end.

(*Ejemplos lo normalizo por que el usuario puede ser tonto.*)
Eval compute in norm (prod (D (I Cero)) (D (I Cero))).
Eval compute in norm (prod (D (I Cero)) (I (I Cero))).
Eval compute in norm (suma (I (I Cero)) (D (D (I Cero)))).

(*Función recursiva que hace una optimización de la
  exponienciación.*)
Fixpoint mist (n:pNat) (m:pNat) : pNat :=
  match n,m with
  | _, Cero => I (Cero)
  | x ,D y => prod (mist x y) (mist x y)
  | x ,I y => prod (prod (mist x y) (mist x y)) (x)
  end.

(*Ejemplos*)
Eval compute in norm (mist (D (I Cero)) (D (I Cero))).
Eval compute in norm (mist (D (I Cero)) (I (I Cero))).
Eval compute in norm (mist (I (I Cero)) (D (D (I Cero)))).

(*
*********************************************************
* Programación lógica                                   *
*********************************************************
*)

(*Definición de la relación menor o igual.*)
Inductive meIg : nat -> nat -> Prop :=
| N_n (n : nat): meIg n n
| N_S_m (n m : nat): meIg n m -> meIg n (S m).

(*Principio de inducción para relaciones.*)
Check meIg_ind.

(*Ejemplos.*)
Goal meIg 2 3.
Proof.
  constructor.
  constructor.
Qed.
Goal meIg 8 8.
Proof.
  constructor.
Qed.
Goal ~meIg 1 0.
Proof.
  unfold not.
  intros.
  inversion H.
Qed.


(*
**************************************
* 2.1. Relaciones sobre N
* npar
* nimpar
**************************************
*)

(*Definición de que un número natural es par.*)
Inductive par : nat -> Prop :=
| par_0 : par 0
| par_s (n:nat): par n -> par (S (S n)).

(*Definición de que un número natural es impar.*)
Inductive impar : nat -> Prop :=
| impar_i (n:nat): par n -> impar (S n).

(*Resultados.*)
Goal par 8.
Proof.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
Qed.
Goal par 10.
Proof.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
Qed.
Goal ~par 5.
Proof.
  unfold not.
  intros.
  inversion H.
  inversion H1.
  inversion H3.
Qed.
Goal impar 5.
Proof.
  constructor.
  constructor.
  constructor.
  constructor.
Qed.
Goal ~impar 6.
Proof.
  unfold not.
  intros.
  inversion H.
  inversion H1.
  inversion H3.
  inversion H5.
Qed.

(*
****************************************
* 2.2. Programación funcional vs lógica
* npar
* nimpar
* elem
* member
****************************************
*)

(*Definición si indica si un número es par*)
Definition nparF (n:nat) : bool :=
  if Nat.modulo n 2 =? 0 then true else false.

(*Definición si indica si un número es impar*)
Definition nimparF (n:nat) : bool :=
  if Nat.modulo n 2 =? 1 then true else false.

(*Ejemplos.*)
Eval compute in nparF (10).
Eval compute in nparF (9).
Eval compute in nimparF (20).
Eval compute in nimparF (21).

(*Función recursica si dice si un elemento de tipo nat
  se encuentra en la lista*)
Fixpoint elemF (n:nat) (l:lista nat) : bool :=
  match n, l with
  | _, Nil _ => false
  | n, Cons _ x xs => if x =? n then true else elemF n xs
  end.

(*Ejemplos.*)
Eval compute in elemF 0 (Cons nat 1 (Cons nat 2 (Nil nat))).
Eval compute in elemF 1 (Cons nat 1 (Cons nat 2 (Nil nat))).
Eval compute in elemF 3 (Cons nat 1 (Cons nat 2 (Cons nat 3 (Nil nat)))).


(*Relación que es cuerta syss un número natural pertenece
  a una lisra de números naturales.*)
Inductive member : nat -> lista nat -> Prop :=
  | is (n:nat) (l:lista nat): member n (Cons _ n l)
  | is2 (n m : nat) (l:lista nat) : member n l -> member n (Cons _ m l).


Goal member 2 (Cons nat 1 (Cons nat 2 (Nil nat))).
Proof.
  constructor.
  constructor.
Qed.
Goal member 3 (Cons nat 1 (Cons nat 2 (Cons nat 3 (Nil nat)))).
Proof.
  constructor.
  constructor.
  constructor.
Qed.
Goal ~member 4 (Cons nat 1 (Cons nat 2 (Cons nat 3 (Nil nat)))).
Proof.
  unfold not.
  intros.
  inversion H.
  inversion H2.
  inversion H6.
  inversion H10.
Qed.