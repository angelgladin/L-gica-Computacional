(*
* Lógica computacional 2017-2
* Temas:
* Lógica ecuacional: Caso de la inducción.
* Deducción natural.
* Correspondencia Curry-Howard.
* Profesora: Lourdes del Carmen González Huesca
* Ayudante: Roberto Monroy Argumedo
* Laboratorio: Fernando A. Galicia Mendoza
*)

(*************************************************************
* Lógica ecuacional parte 2: Utilizando inducción matemática
*************************************************************)

(*Axiomas que definen la suma de naturales*)
Axiom suma1: forall n, n + 0 = n.
Axiom suma2: forall n m, n + (S m) = S (n + m).

(*Un par de ejemplos*)

Example ej1: 1 + 2 = 3.
Proof.
  rewrite suma2.
  rewrite suma2.
  rewrite suma1.
  trivial.
Qed.

Example ej2: 2 + (1 + 2) = 5.
Proof.
  transitivity (2 + 3).
  -rewrite ej1.
   trivial.
  -rewrite suma2.
   rewrite suma2.
   assert (2 + 1 = 1 + 2).
   +rewrite suma2.
    rewrite suma2.
    rewrite suma2.
    rewrite suma1.
    rewrite suma1.
    trivial.
   +rewrite H.
    rewrite ej1.
    trivial.
Qed.

(* La suma es asociativa.*)
Theorem suma_aso: forall n m r, n + (m + r) = (n + m) + r.
Proof.
  intros n m r.
  induction r.
  -rewrite suma1.
   rewrite suma1.
   trivial.
  -rewrite suma2.
   rewrite suma2.
   rewrite suma2.
   rewrite IHr.
   trivial.
Qed.

(*La suma conmuta*)
Theorem suma_conm: forall n m, n + m = m + n.
Proof.
  intros n m.
  induction m.
  -rewrite suma1.
   induction n.
   +rewrite suma1.
    trivial.
   +rewrite suma2.
    rewrite <- IHn.
    trivial.
  -rewrite suma2.
   rewrite IHm.
   clear IHm (*Ya no es necesaria esta hipótesis.*).
   induction n.
   +rewrite suma1.
    rewrite suma1.
    trivial.
   +rewrite suma2.
    rewrite suma2.
    rewrite <- IHn.
    trivial.
Qed.

(*************************************************************
* Deducción natural: Límites de la lógica constructivista
*************************************************************)

(*Observemos la definición de la negación.*)
Print not.
(*Es decir, not A por definición es A -> False*)

(*Teoremas demostrables de la lógica constructivista*)
Theorem teo1: forall A B C, ((A /\ B) -> C) -> (A -> (B -> C)).
Proof.
  intros A B C (*Regla de introducción del para todo*).
  intro (*Regla de introducción de la implicación*).
  intro.
  intro.
  apply X (*Regla de eliminación de la implicación*).
  split (*Regla de introducción de la conjunción*).
  -assumption (*Regla de hipótesis*).
  -trivial (*Contiene la regla de hipótesis*).
Qed.

Theorem teo2: forall (A:Prop), A -> exists B, A \/ B.
Proof.
  intro A.
  intro.
  exists A (*Regla de introducción del existencial*).
  left (*Regla 1 de introducción de la disyunción*).
  trivial.
Qed.

Theorem dM: forall (A B:Prop), ~(A \/ B) <-> (~A /\ ~B).
Proof.
  intros A B.
  unfold iff (*Definición de la doble condicional o equivalencia*).
  split.
  -intro.
   unfold not in * (*Definición de la negación*).
   split.
   +intro.
    apply H.
    left.
    trivial.
   +intro.
    apply H.
    right (*Regla 2 de introducción de la disyunción*).
    trivial.
  -intro.
   destruct H (*Regla de eliminación de la conjunción*).
   unfold not in *.
   intro.
   destruct H1 (*Regla de eliminación de la disyunción*).
   +apply H.
    trivial.
   +contradiction (*Coq busca sintácticamente expresiones de la forma A y ~A*).
Qed.

(*El siguiente teorema no es demostrable en lógica constructivista*)
Theorem noDemostrable: forall (A:Prop), ~~A -> A.
Proof.
  intro A.
  intro.
  unfold not in H.
  exfalso (*Cambia la meta por False*).
  apply H.
  intro.
  (*De aquí es imposible seguir*)
Admitted. (*Vernáculo para indicar: No chavo, no sale*)

(*Para demostrar lo anterior es necesario demostrar lo siguiente*)
Theorem TerExc: forall (A:Prop), A \/ ~A.
Proof.
  intro A.
  (*De aquí es imposible seguir*)
Admitted. (* TT_TT *)

(*************************************************************
* Deducción natural: Lógica clásica
*************************************************************)

(*Requerimos del siguiente axioma para poder hacer cosas como ~~p -> p*)
Axiom clasica: forall (A:Prop), A \/ ~A.

(*Ahora si podremos demostrar la fórmula p <-> ~~p*)
Theorem NNPP: forall (A:Prop), A <-> ~~A.
Proof.
  intro A.
  unfold iff.
  split.
  -(*Demostrable en lógica constructivista*)
    intro.
    unfold not.
    intro.
    contradiction.
  -unfold not (*Podemos desglozar desde un principio las definiciones*).
   intro.
   assert (A \/ ~A) (*Truco*).
   +apply clasica (*Benditos axiomas*).
   +destruct H0.
    *trivial.
    *contradiction.
Qed.

(*Otro teorema de la lógica clásica*)
Theorem eqImpl: forall (A B:Prop), (A -> B) <-> (~A \/ B).
Proof.
  intros A B.
  unfold iff.
  split.
  -intro.
   apply NNPP (*De esos trucos malvados*).
   unfold not.
   intro.
   exfalso.
   apply H0.
   left.
   intro.
   apply H0.
   right.
   apply H.
   trivial.
  -(*Demostrable en constructivismo*)
    intro.
    intro.
    destruct H.
    +contradiction.
    +trivial.
Qed.

(*************************************************************
* Heurísticas al momento de demsotrar:
* Siempre fijarse en la forma de la fórmula a demostrar.
Por ejemplo: Si quieren demostrar una conjunción, de antemano saben que
tienen que demostrar A y B, buscar en sus hipótesis donde aparecen esas hipótesis.
* En caso de estar en lógica constructivista (o minimal) llevar todo a sus mínimas
definiciones, es decir, cambiar el <-> por /\ y ->, lo mismo para ~ por -> False.
Esto les dará un mejor análisis sobre la sintaxis.
* En caso de estar en lógica clásica (es decir, les indican que la demostración
es en lógica clásica) existen dos viejas confiables: 
** A \/ ~A
** A <-> ~~A
* Y también cambiar las fórmulas a forma normal conjuntiva, a pesar de ser sintácticamente
* mas largas, son mas dóciles de manejar.
De tarea moral intentar deMorgan2: forall (A B:Prop), ~(A /\ B) <-> (~A \/ ~B).
* Por último, sugiero ampliamente que demuestren todas las equivalencias indicadas en
* las notas número 2 antes de realizar sus ejercicios en la tarea examen,
* ya que, el resto de teoremas es muy probable que terminen siendo corolarios de estas o 
* o inclusos estos mismos.
*************************************************************)

(*************************************************************
* Currry Howard
*************************************************************)

Definition suc: nat -> nat.
Proof.
  apply S.
Defined.

Extraction Language Haskell.
Extraction suc.

Definition idN: nat -> nat.
Proof.
  intro n.
  exact n.
Defined.

Extraction idN.

(*La composición de funciones*)

Variables A B C:Type. (*Consideremos a tres tipos cualesquiera*)
Definition comp: (A -> B) -> (B -> C) -> A -> C.
Proof.
  intros H H0 H1.
  apply H0.
  apply H.
  trivial.
Defined.

Extraction comp.

(*Dos casos especiales y que queda solo como chisme:
* Funciones recursivas.
* Programación con tipos dependientes.
*)
Definition suma: nat -> nat -> nat.
Proof.
  refine (fix f (n m:nat) : nat :=
            match n with
            | 0 => m
            | S n' => S (f n' m)
            end
         ).
Defined.

Extraction suma.

Require Import Arith.

Lemma zgtz: ~ 0 > 0.
Proof.
auto with arith.
Defined.

Check 0 >0.

Print False.

Definition pred_strong1 (n:nat)  : n > 0 -> nat :=
 match n with
  | 0 => fun pf: 0>0 => match zgtz pf with end
  | S n' => fun _ => n'
 end.

Extraction pred_strong1.