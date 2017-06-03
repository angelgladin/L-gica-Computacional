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
* Programación funcional
*********************************************************
*)

(*Ejemplo de definición de un tipo,
parecido a type de Haskell.
prod A B es lo mismo que (A,B)*)
Definition parNB := prod nat bool.

(*Parecido a la instrucción :t de GHC.*)
Check parNB.

(*Ejemplo de función no recursiva.*)
Definition iZ (n:nat) : bool :=
  match n with
  | 0 => true
  | _ => false
  end.

(*Ejemplos.*)
Eval compute in iZ 0.
Eval compute in iZ 9.
Eval compute in iZ 4.

(*Definición del tipo de datos que representa los números 
naturales.
Se define nats para fines educativos, pero el script
hará uso del tipo nat, nativo del lenguaje.*)
Inductive nats : Type :=
| C : nats
| Su : nats -> nats.

(*Una de las maravillas de Coq, es que define el
prinicipio de inducción de forma automática, cuando
se define un tipo de datos mediante Inductive.*)
Check nats_ind.

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
Primera idea para definir head.
Autor: El niño de los 3 nombres*)
Definition head1 {A:Type} (l:lista A) : lista A :=
  match l with
  | Nil _ => Nil A
  | Cons _ x xs => Cons _ x (Nil A)
  end.

(*Un ejemplo.*)
Eval compute in head1 (Cons nat 1 (Cons nat 2 (Nil nat))).

(*Podemos indicarle a Coq un parámetro de error para head,
esto resulta inconveniente.*)
Definition head_err {A:Type} (error:A)
           (l:lista A) : A :=
  match l with
  | Nil _ => error
  | Cons _ x xs => x
  end.

(*Ejemplos.*)
Eval compute in head_err 0 (Cons nat 1 (Cons nat 2 (Nil nat))).
Eval compute in head_err 0 (Nil nat).

(*Ejemplo de la relación menor que, cuya imagen son booleanos.*)
Eval compute in (3 <? 2).

(*Árbol binario que almacena números naturales.*)
Inductive ab : Type :=
| Vacio : ab
| Nodo : nat -> ab -> ab -> ab.

(*Función que indica si un árbol binario es vacío.*)
Definition esVacio (t:ab) : bool :=
  match t with
  | Vacio => true
  | Nodo x i d => false
  end.

(*Función que obtiene el mínimo de un árbol binario.*)
Fixpoint minimo (t:ab) : option nat :=
  match t with
  | Vacio => None
  | Nodo x Vacio Vacio => Some x
  | Nodo x i d => match minimo i,minimo d with
                  | None,_ => None
                  | _,None => None
                  | Some n,Some m =>
                    if x <? n then
                      Some (min x m)
                    else
                      Some (min n m)
                  end
  end.

(*Ejemplos.*)
Eval compute in minimo (Vacio).
Eval compute in minimo (Nodo 3 (Nodo 1 Vacio Vacio)
                             (Nodo 0 Vacio Vacio)).
Eval compute in minimo (Nodo 3 (Nodo 2 Vacio Vacio)
                             (Nodo 7
                                   (Nodo 4 Vacio Vacio)
                                   (Nodo 1 Vacio Vacio))).

(*Función que obtiene el máximo de un árbol binario.*)
Fixpoint maximo (t:ab) : option nat :=
  match t with
  | Vacio => None
  | Nodo x Vacio Vacio => Some x
  | Nodo x i d => match maximo i,maximo d with
                  | None,_ => None
                  | _,None => None
                  | Some n,Some m =>
                    if negb (x <? n) then
                      Some (max x m)
                    else
                      Some (max n m)
                  end
  end.

(*Ejemplos.*)
Eval compute in maximo (Vacio).
Eval compute in maximo (Nodo 3 (Nodo 1 Vacio Vacio)
                             (Nodo 0 Vacio Vacio)).
Eval compute in maximo (Nodo 3 (Nodo 2 Vacio Vacio)
                             (Nodo 7
                                   (Nodo 4 Vacio Vacio)
                                   (Nodo 1 Vacio Vacio))).

(*
*********************************************************
* Programación lógica
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

(*Definición de que un número natural es par.*)
Inductive par : nat -> Prop := (*Definir*).

(*Definición de que un número natural es impar.*)
Inductive impar : nat -> Prop := (*Definir*).

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

Inductive elem : nat -> lista nat -> Prop := (*Definir*).

Goal elem 2 (Cons nat 1 (Cons nat 2 (Nil nat))).
Proof.
  constructor.
  constructor.
Qed.
Goal elem 3 (Cons nat 1 (Cons nat 2 (Cons nat 3 (Nil nat)))).
Proof.
  constructor.
  constructor.
  constructor.
Qed.
Goal ~elem 4 (Cons nat 1 (Cons nat 2 (Cons nat 3 (Nil nat)))).
Proof.
  unfold not.
  intros.
  inversion H.
  inversion H2.
  inversion H6.
  inversion H10.
Qed.