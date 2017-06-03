(*
 * Lógica computacional 2017-2
 * Práctica 7
 * Deducción natural y lógica ecuacional.
 * Profesora: Lourdes del Carmen González Huesca
 * Ayudante: Roberto Monroy Krgumedo
 * Laboratorio: Fernando A. Galicia Mendoza
 * Ángel Iván Gladín García
 * 313112470
 * María Ximena Lezama Hernández
 * 313040131
 *)

(***************************************************************)
(***************************************************************)
(****************     1.1 Primera defición     *****************)
(***************************************************************)
(***************************************************************)

(* Definición 1 (Álgebra de Bool). Sea K una conjunto no vacío, +, ◦ dos
 * operadores binarios y ¬ un operador unario sobre K y 0, 1 dos elementos de K. *)
Hypotheses (K:Set)
           (o:K)
           (l:K)
           (addition:K -> K -> K)
           (multiplication:K -> K -> K)
           (negation:K -> K).

Notation "¬ x" := (negation x) (at level 40).

(* El vernáculo Infix es para darle una notación infija a alguna función *)
Infix "⊕" := addition (at level 40).
Infix "⊙" := multiplication (at level 40).

(* Se dice que (K, +, ◦, ¬, 0, 1) es un álgebra de Bool si se satisfacen las 
 * siguientes propiedades:*)

(* Para cualquier a∈K, se tiene que a+0=a. *)
Axiom id_aditiv : forall a: K, a ⊕ o = a.

(* Para cualquier a∈K, se tiene que a⊙1=a *)
Axiom id_prod : forall a: K, a ⊙ l = a.

(* Para cualesquiera a,b∈K, se tiene que a+b=b+a *)
Axiom conm_sum : forall a b: K, a ⊕ b = b ⊕ a.

(* Para cualesquiera a,b∈K, se tiene que a⊙b=b⊙a *)
Axiom conm_prod : forall a b: K, a ⊙ b = b ⊙ a.

(* Para cualesquiera a,b,c∈K, se tiene que a+(b⊙c)=(a+b)⊙(a+c) *)
Axiom distr_sum : forall a b c: K, a ⊕ (b ⊙ c) = (a ⊕ b) ⊙ (a ⊕ c).

(* Para cualesquiera a,b,c∈K, se tiene que a⊙(b+c)=(a⊙b)+(a⊙c) *)
Axiom distr_prod : forall a b c: K, a ⊙ (b ⊕ c) = (a ⊙ b) ⊕ (a ⊙ c).

(* Para cualquier a∈K, se tiene que a+¬a=1 *)
Axiom compl_sum : forall a: K, a ⊕ (¬ a) = l.

(* Para cualquier a∈K, se tiene que a◦¬a=0 *)
Axiom compl_prod : forall a: K, a ⊙ (¬ a) = o.

(* 1. Para cualquier a∈K, se tiene que a+a=a *)
Theorem idempotent_law_1: forall a: K, a ⊕ a = a.
Proof.
  intros.
  rewrite <- id_prod with (a ⊕ a).
  rewrite <- compl_sum with a.
  rewrite <- distr_sum.
  rewrite compl_prod.
  rewrite id_aditiv.
  trivial.
Qed.

(* 2. Para cualquier a ∈ K, se tiene que a◦a=a *)
Theorem idempotent_law_2: forall a: K, a ⊙ a = a.
Proof.
  intros.
  rewrite <- id_aditiv with (a ⊙ a).
  rewrite <- conm_sum.
  rewrite <- (compl_prod a).
  rewrite <- distr_prod.
  rewrite <- conm_sum.
  rewrite compl_sum.
  rewrite id_prod.
  trivial.
Qed.

(* 3. Para cualquier a∈K, se tiene que a+1=1 *)
Theorem union_law_1: forall a: K, a ⊕ l = l.
Proof.
  intros.
  rewrite <- id_prod with (a ⊕ l).
  rewrite <- conm_prod.
  rewrite <- compl_sum with a.
  rewrite <- distr_sum.
  rewrite compl_sum with a.
  rewrite id_prod.
  rewrite compl_sum with a.
  trivial.
Qed.

(* 4. Para cualquier a ∈ K, se tiene que a◦0=0 *)
Theorem union_law_2: forall a: K, a ⊙ o = o.
Proof.
  intros.
  rewrite <- id_aditiv with (a ⊙ o).
  rewrite conm_sum.
  rewrite <- compl_prod with a.
  rewrite <- distr_prod.
  rewrite compl_prod.
  rewrite id_aditiv.
  rewrite compl_prod.
  trivial.
Qed.

(* 5. Para cualesquiera a,b ∈ K, se tiene que a+(a◦b)=a *)
Theorem absortion_law_1: forall a b: K, a ⊕ (a ⊙ b) = a.
Proof.
  intros.
  assert (a ⊕ (a ⊙ b) = (a ⊙ l) ⊕ (a ⊙ b)).
  rewrite id_prod.
  reflexivity.
  rewrite H.
  rewrite <- distr_prod.
  rewrite <- conm_sum.
  assert (b ⊕ l = l).
  apply union_law_1.
  rewrite H0.
  rewrite id_prod.
  trivial.
Qed.

(* 6. Para cualesquiera a, b∈K, se tiene que a◦(a+b)=a *)
Theorem absorption_law_2: forall a b: K, a ⊙ (a ⊕ b) = a.
Proof.
  intros.
  assert (a ⊙ (a ⊕ b) = (a ⊕ o) ⊙ (a ⊕ b)).
  rewrite id_aditiv.
  reflexivity.
  rewrite H.
  rewrite <- distr_sum.  
  rewrite <- conm_prod.
  assert (b ⊙ o = o).
  apply union_law_2.  
  rewrite H0.
  rewrite id_aditiv.
  trivial.
Qed.

(*Fernando: Aquí inicia mis sugerencias*)
Theorem dCInvU: forall (x:K), exists! (x': K), x ⊕ x' = l /\ (x ⊙ x') = o.
Proof.
  intros.
  exists (¬ x).
  split.
  -split.
   +rewrite compl_sum.
    trivial.
   +rewrite compl_prod.
    trivial.
  -intros.
   destruct H.
   (*El truco aquí era agregar un 0, es decir,
    x' = x' + 0*)
   rewrite <- id_aditiv with x'.
   rewrite <- compl_prod with x.
   rewrite distr_sum.
   rewrite conm_sum.
   rewrite H.
   rewrite conm_sum.
   assert (l = ¬ x ⊕ x).
   rewrite conm_sum.
   rewrite compl_sum.
   reflexivity.
   rewrite H1.
   rewrite <- distr_sum.
   rewrite H0.
   rewrite id_aditiv.
   trivial.
Qed.

Axiom assic_add: forall x y z, ((x ⊕ y) ⊕ z) = (x ⊕ (y ⊕ z)).
Axiom assoc_mult: forall x y z, ((x ⊙ y) ⊙ z) = (x ⊙ (y ⊙ z)).

Theorem cInvD: forall (x y: K), ¬ (x ⊙ y) = (¬ x ⊕ ¬ y).
Proof.
  intros.
  (*
   * El siguiente argumento es cuando indicas en matemáticas
   * que verás un cassic_add particular de un teorema.
   *)
  destruct dCInvU with (x ⊙ y).
  destruct H.
  destruct H.
  destruct H0 with (¬ x ⊕ ¬ y).
  split.
  +rewrite conm_sum.
   rewrite distr_sum.
   rewrite conm_sum.
   rewrite <- assic_add.
   rewrite compl_sum.
   rewrite <- conm_sum.
   rewrite union_law_1.
   rewrite conm_prod.
   rewrite id_prod.
   rewrite assic_add.
   assert (¬ y ⊕ y = y ⊕ ¬ y).
   rewrite conm_sum.
   reflexivity.
   rewrite H2.
   rewrite compl_sum.
   rewrite union_law_1.
   trivial.
  +rewrite distr_prod.
   rewrite conm_prod.
   rewrite assoc_mult.
   rewrite compl_prod.
   rewrite union_law_2.
   rewrite id_aditiv.
   assert (¬ x ⊙ (x ⊙ y) = (¬ x ⊙ x) ⊙ y).
   symmetry.
   rewrite <- assoc_mult.
   reflexivity.
   rewrite H2.
   assert (¬ x ⊙ x = x ⊙ ¬ x).
   rewrite conm_prod.
   reflexivity.
   rewrite H3.
   rewrite compl_prod.
   rewrite conm_prod.
   rewrite union_law_2.
   trivial.
  +symmetry. (*Truco*)
   apply H0.
   split.
   rewrite compl_sum.
   trivial.
   rewrite compl_prod.
   trivial.
Qed.

Theorem cInvD2: forall (x y: K), ¬ (x ⊕ y) = (¬ x ⊙ ¬ y).
Proof.
  (*La demostración es análoga a la anterior.*)
  intros.
  (*
   * El siguiente argumento es cuando indicas en matemáticas
   * que verás un cassic_add particular de un teorema.
   *)
  destruct dCInvU with (x ⊕ y).
  destruct H.
  destruct H.
  destruct H0 with (¬ x ⊙ ¬ y).
  split.
  +rewrite distr_sum.
   rewrite <- conm_sum.
   rewrite assic_add.
   rewrite compl_sum.
   rewrite union_law_1.
   rewrite id_prod.
   rewrite <- assic_add.
   assert (¬ x ⊕ x = x ⊕ ¬ x).
   rewrite <- conm_sum.
   reflexivity.
   rewrite H2.
   rewrite compl_sum.
   rewrite conm_sum.
   rewrite union_law_1.
   trivial.
  +rewrite conm_prod.
   rewrite distr_prod.
   rewrite conm_prod.
   rewrite assoc_mult.
   assert (¬ y ⊙ y = y ⊙ ¬ y).
   rewrite conm_prod.
   reflexivity.
   rewrite H2.
   rewrite compl_prod.
   rewrite union_law_2.
   rewrite id_aditiv.
   rewrite <- assoc_mult.
   rewrite compl_prod.
   rewrite <- conm_prod.
   rewrite union_law_2.
   trivial.
  +symmetry. (*Truco*)
   apply H0.
   split.
   rewrite compl_sum.
   trivial.
   rewrite compl_prod.
   trivial.    
Qed.

(*Última sugerencia*)
Theorem double_neg: forall a, ¬ (¬ a) = a.
  intros.
  destruct dCInvU with (¬ a).
  destruct H.
  destruct H.
  destruct H0 with (¬ (¬ a)).
  -split.
   +rewrite compl_sum.
    trivial.
   +rewrite compl_prod.
    trivial.
  -apply H0.
   split.
   +rewrite conm_sum.
    rewrite compl_sum.
    trivial.
   +rewrite conm_prod.
    rewrite compl_prod.
    trivial.
Qed.

(* 7. Los elementos 0 y 1 son duales, es decir, ¬1=0 y ¬0=1 *)
Theorem dual: (¬ l) = o /\ (¬ o) = l.
Proof.
  split.
  -rewrite <- compl_sum with o. (*Ojito y después cuentas*)
   rewrite cInvD2.
   rewrite compl_prod.
   trivial.
  -rewrite <- compl_prod with l.
   rewrite cInvD.
   rewrite compl_sum.
   trivial.
Qed.

(* 8. Para cualesquiera a, b∈K, se tiene que a+b=¬(¬a◦¬b) *)
Theorem morgan1: forall a b: K, a ⊕ b = ¬ (¬ a ⊙ ¬ b).
Proof.
  intros.
  rewrite cInvD.
  rewrite double_neg.
  rewrite double_neg.
  trivial.
Qed.

(* 9. Para cualesquiera a, b∈K, se tiene que a◦b=¬(¬a+¬b) *)
Theorem morgan2: forall a b: K, a ⊙ b = ¬ (¬ a ⊕ ¬ b).
Proof.
  intros.
  rewrite cInvD2.
  rewrite double_neg.
  rewrite double_neg.
  trivial.
Qed.


(***************************************************************)
(***************************************************************)
(************     1.2 Álgebras de Bool con orden     ***********)
(***************************************************************)
(***************************************************************)

(* Sea (K,+,◦,¬,0,1) un  álgebra de Bool, dados x,y ∈ K decimos que 
 * x < y syss x + y = y.*)
Definition orderXY (x y: K) := x ⊕ y = y.
Notation "x << y" := (orderXY x y) (at level 80).

Theorem theorem1 : forall (x y: K), x << y -> x ⊙ y = x.
Proof.
  intros.
  unfold orderXY in H.
  rewrite <- H.
  rewrite absorption_law_2.
  trivial.
Qed.

(* 2. Para cuales quiera x, y ∈ K, si x<y entonces ¬x+y=1 *)
Theorem theorem2: forall (x y: K), x << y -> ¬x ⊕ y = l. 
Proof.
  intros.
  unfold orderXY in H.
  rewrite <- H.
  rewrite <- assic_add.
  rewrite conm_sum with (¬ x) x.
  rewrite compl_sum.
  rewrite conm_sum.
  rewrite union_law_1.
  trivial.
Qed.

(* 3. Para cuales quiera x, y ∈ K, si x<y entonces ¬x◦y=0 *)
Theorem theorem3: forall (x y: K), x << y -> ¬ y ⊙ x = o.
Proof.
  intros.
  unfold orderXY in H.
  rewrite <- H.
  rewrite cInvD2.
  rewrite conm_prod with (¬ x) (¬ y).
  rewrite assoc_mult.
  rewrite conm_prod with (¬ x) x.
  rewrite compl_prod.
  rewrite union_law_2.
  trivial.
Qed.


(***************************************************************)
(***************************************************************)
(****************     1.3 Segunda deficinón     ****************)
(***************************************************************)
(***************************************************************)

(* Definición 3 (Álgebra de Bool).
 * Sea K una conjunto no vacío, + un operador binario y ¬ un operador unario
 * sobre K. *)
Hypotheses (A: Set)
           (addition2: A -> A -> A)
           (negation2: A -> A).

Notation "► x" := (negation2 x) (at level 20).

(* El vernáculo Infix es para darle una notación infija a alguna función *)
Infix "⊞" := addition2 (at level 40).

(* Se dice que (K,+,¬) es un álgebra de Bool si se satisfacen las 
 * siguientes propiedades *)

(* Para cualesquiera a,b∈K, se tiene que a+b=b+a *)
Axiom conmutativity_2 : forall x y: A, x ⊞ y = y ⊞ x.

(* Para cualesquiera a,b,c∈K, se tiene que (a+b)+c=a+(b+c) *)
Axiom associativity_add_2 : forall x y z: A, (x ⊞ y) ⊞ z = x ⊞ (y ⊞ z).

(* Para cualesquier a∈K, se tiene que a+a=a *)
Axiom idempotent_2: forall x: A, x ⊞ x = x.

(* Para cualesquiera a,b∈K, se tiene que ¬(¬a+¬b)+¬(¬a+b)=a *)
Axiom foo_bar_baz: forall x y: A, ► (► x ⊞ ► y) ⊞ ► (► x ⊞ y) = x.

(* Definamos los siguientes operadores y constantes sobre un 
 * álgebra de Bool (K, +, ¬) *)

(* Sean a, b ∈ K, definimos a a ◦ b como ¬(¬a + ¬b) *)
Definition multiplication_2_def (x y: A) := ► (► x ⊞ ► y).
Notation "x ⊡ y" := (multiplication_2_def x y) (at level 80).

(*Definición de 1 y 0 dependen de las variables*)
(* Sea a ∈ K, definimos a 1 como a + ¬a *)
Definition one (x: A) := x ⊞ ► x.
(* Sea a ∈ K, definimos a 0 como a ◦ ¬a *)
Definition zero (x: A) := x ⊡ ► x.

(* 2. Para cualquier a ∈ K,se tiene que a+¬a=¬a+¬¬a *)
Theorem theorem_2_2: forall (x: A), (x ⊞ ► x) = (► x ⊞ ► (► x)).
Proof.
  intros.
  assert (► x ⊞ ► (► x) = (► (► (► x) ⊞ ► (► x)) ⊞ ► (► (► x) ⊞ ► x)) 
                            ⊞ (► (► (► (► x)) ⊞ ► (► x)) ⊞ ► (► (► (► x)) ⊞ ► x))).
  +rewrite foo_bar_baz.
   rewrite foo_bar_baz.
   trivial.
  +rewrite H.
   assert ((► (► (► x) ⊞ ► (► x)) ⊞ ► (► (► x) ⊞ ► x))
             ⊞ (► (► (► (► x)) ⊞ ► (► x)) ⊞ ► (► (► (► x)) ⊞ ► x)) 
           = (► (► (► (► x)) ⊞ ► (► x)) ⊞ ► (► (► (► x)) ⊞ ► x)) 
               ⊞ (► (► (► x) ⊞ ► (► x)) ⊞ ► (► (► x) ⊞ ► x))).
   *rewrite conmutativity_2.
    reflexivity.
   *rewrite H0.
    clear.
    assert (► (► (► (► x)) ⊞ ► (► x)) ⊞ ► (► (► (► x)) ⊞ ► x) 
            = ► (► (► (► x)) ⊞ ► x) ⊞ ► (► (► (► x)) ⊞ ► (► x))).
    --rewrite conmutativity_2.
      reflexivity.
    --rewrite H.
      assert (► (► (► x) ⊞ ► (► x)) ⊞ ► (► (► x) ⊞ ► x) 
              = ► (► (► x) ⊞ ► x) ⊞ ► (► (► x) ⊞ ► (► x))).
      ++rewrite conmutativity_2.
        reflexivity.
      ++rewrite H0.
        clear.
        rewrite associativity_add_2.
        assert ((► (► (► (► x)) ⊞ ► (► x))
                   ⊞ (► (► (► x) ⊞ ► x) ⊞ ► (► (► x) ⊞ ► (► x)))) 
                = ((► (► (► (► x)) ⊞ ► (► x))⊞ ► (► (► x) ⊞ ► x))⊞ ► (► (► x) 
                                                                        ⊞ ► (► x)))).
        **rewrite <- associativity_add_2.
          reflexivity.
        **rewrite H.
          clear.
          assert (► (► (► (► x)) ⊞ ► (► x)) ⊞ ► (► (► x) ⊞ ► x)
                  = ► (► (► x) ⊞ ► x) ⊞ ► (► (► (► x)) ⊞ ► (► x))).
          +++rewrite conmutativity_2.
             reflexivity.
          +++rewrite H.
             clear.
             assert ((► (► (► x) ⊞ ► x) ⊞ ► (► (► (► x)) ⊞ ► (► x)))
                       ⊞ ► (► (► x) ⊞ ► (► x)) 
                     = ► (► (► x) ⊞ ► x) ⊞ (► (► (► (► x)) ⊞ ► (► x)) ⊞ ► (► (► x) 
                                                                             ⊞ ► (► x)))).
          ---rewrite <- associativity_add_2.
             reflexivity.
          ---rewrite H.
             clear.
             rewrite <- associativity_add_2.
             assert (► (► (► x)) ⊞ ► x = ► x ⊞ ► (► (► x))).
             rewrite conmutativity_2.
             reflexivity.
             assert (► (► x) ⊞ ► x = ► x ⊞ ► (► x)).
             rewrite conmutativity_2.
             reflexivity.
             assert (► (► (► x)) ⊞ ► (► x) = ► (► x) ⊞ ► (► (► x))).
             rewrite conmutativity_2.
             reflexivity.
             rewrite H.
             rewrite H0.
             rewrite H1.
             assert (x ⊞ ► x = (► (► x ⊞ ► (► (► x))) ⊞ ► (► x ⊞ ► (► x)))
                                 ⊞ (► (► (► x) ⊞ ► (► (► x))) ⊞ ► (► (► x) ⊞ ► (► x)))).
  -rewrite foo_bar_baz.
   rewrite foo_bar_baz.
   trivial.
  -rewrite H2.
   reflexivity.
Qed.

(* 3. Para cualquier a ∈ K, se tiene que ¬¬a = a *)
Theorem theorem_2_3: forall (x: A), ► (► x) = x.
Proof.
  intros.
  assert (► (► x) = ► (► (► (► x)) ⊞ ► (► x)) 
                      ⊞ ► (► (► (► x)) ⊞ ► x)).
  +rewrite foo_bar_baz.
   reflexivity.
  +rewrite H.
   assert (► (► (► x)) ⊞ ► (► x) 
           = ► (► x) ⊞ ► (► (► x))).
   --rewrite conmutativity_2.
     reflexivity.
   --rewrite H0.
     clear.
     assert (► (► x) ⊞ ► (► (► x)) = ► x ⊞ ► (► x)).
  -rewrite <- theorem_2_2.
   reflexivity.
  -rewrite H.
   assert (► (► (► x)) ⊞ ► x = ► x ⊞ ► (► (► x))).
   *rewrite conmutativity_2.
    reflexivity.
   *rewrite H0.
    clear.
    rewrite conmutativity_2.
    rewrite foo_bar_baz.
    reflexivity.
Qed.

(* 1. Para cuales quiera a, b ∈ K, se tiene que (a◦b)+(a◦¬b)=a *)
Theorem theorem_2_1: forall (x y: A), (x ⊡ y) ⊞ (x ⊡ ► y) = x.
Proof.
  intros.
  unfold multiplication_2_def.
  unfold multiplication_2_def.
  rewrite theorem_2_3.
  rewrite foo_bar_baz.
  reflexivity.
Qed.

(* 4. Para cualesquiera a, b ∈ K, se tiene que a+¬a=b+¬b *)
Theorem theorem_2_4: forall (a b: A), (a ⊞ (► a)) = (b ⊞ (► b)).
Proof.
  intros.
  set (x:= a ⊞ ► a).
  set (y:= b ⊞ ► b).
  unfold y.
  rewrite conmutativity_2.
  rewrite <- foo_bar_baz with b b.
  assert (► (► (► b ⊞ ► b) ⊞ ► (► b ⊞ b)) = ► b).
  -rewrite foo_bar_baz.
   reflexivity.
  -rewrite H.
   rewrite idempotent_2.
   assert (► b ⊞ b = b ⊞ ► b).
   +rewrite conmutativity_2.
    reflexivity.
   +rewrite H0.
    fold y.
    rewrite <- associativity_add_2.
    rewrite <- theorem_2_2.
    fold y.
    rewrite <- foo_bar_baz with y (► x).
    assert (► (► (► y ⊞ ► (► x)) ⊞ ► (► y ⊞ ► x)) = ► y).
    *rewrite foo_bar_baz.
     reflexivity.
    *rewrite H1.
     rewrite <- foo_bar_baz with (► y) (► x).
     assert ((►
                ((► (► (► y) ⊞ ► (► x)) ⊞ ► (► (► y) ⊞ ► x))
                   ⊞ ► (► x))
                ⊞ ►
                ((► (► (► y) ⊞ ► (► x)) ⊞ ► (► (► y) ⊞ ► x)) ⊞ ► x))
             = (► (► y ⊞ ► (► x)) ⊞ ► (► y ⊞ ► x))).
     --rewrite foo_bar_baz.
       reflexivity.
     --rewrite H2.
       clear H2.
       clear H1.
       clear H.
       clear H0.
       rewrite associativity_add_2.
       assert ( (► (► y ⊞ ► x)
                   ⊞ (► (► (► y) ⊞ ► (► x)) ⊞ ► (► (► y) ⊞ ► x)))
                = (► (► y ⊞ ► x) ⊞ ► (► (► y) ⊞ ► (► x))) 
                    ⊞ ► (► (► y) ⊞ ► x)).
       ++rewrite <- associativity_add_2.
         reflexivity.
       ++rewrite H.
         clear H.
         assert (► (► y ⊞ ► x) ⊞ ► (► (► y) ⊞ ► (► x))
                 = ► (► (► y) ⊞ ► (► x)) ⊞ ► (► y ⊞ ► x)).
         **rewrite conmutativity_2.
           reflexivity.
         **rewrite H.
           assert (((► (► (► y) ⊞ ► (► x)) ⊞ ► (► y ⊞ ► x))
                      ⊞ ► (► (► y) ⊞ ► x)) = ► (► (► y) ⊞ ► (► x)) 
                                               ⊞ ( ► (► y ⊞ ► x) ⊞ ► (► (► y) ⊞ ► x)) ).
           ---rewrite associativity_add_2.
              reflexivity.
           ---rewrite H0.
              clear H.
              clear H0.
              rewrite <- associativity_add_2.
              assert (► (► y ⊞ ► (► x)) ⊞  ► (► (► y) ⊞ ► (► x))
                      =  ► (► (► y) ⊞ ► (► x)) ⊞ ► (► y ⊞ ► (► x)) ).
              +++rewrite conmutativity_2.
                 reflexivity.
              +++rewrite H.
                 assert (► (► y ⊞ ► x) ⊞ ► (► (► y) ⊞ ► x)
                         = ► (► (► y) ⊞ ► x) ⊞ ► (► y ⊞ ► x)).
                 ***rewrite conmutativity_2.
                    reflexivity.
                 ***rewrite H0.
                    clear H.
                    clear H0.
                    assert (► (► y) ⊞ ► (► x) = ► (► x) ⊞ ► (► y)).
                    rewrite conmutativity_2.
                    reflexivity.
                    rewrite H.
                    assert (► y ⊞ ► (► x) = ► (► x) ⊞ ► y).
                    rewrite conmutativity_2.
                    reflexivity.
                    rewrite H0.
                    assert (► (► y) ⊞ ► x = ► x ⊞ ► (► y)).
                    rewrite conmutativity_2.
                    reflexivity.
                    rewrite H1.
                    assert (► y ⊞ ► x = ► x ⊞ ► y).
                    rewrite conmutativity_2.
                    reflexivity.
                    rewrite H2.
                    rewrite foo_bar_baz.
                    rewrite foo_bar_baz.
                    rewrite conmutativity_2.
                    clear H.
                    clear H0.
                    clear H1.
                    clear H2.
                    unfold x.
                    assert (► (a ⊞ ► a) = ► x).
                    fold x.
                    reflexivity.
                    rewrite H.
                    rewrite theorem_2_2.
                    rewrite associativity_add_2.
                    assert (► (► a) ⊞ ► x = ► (► a ⊞ ► a) ⊞ ► ( ► a ⊞ a ) ).
                    ----rewrite <- idempotent_2 with (► a).
                        assert ( ► ((► a ⊞ ► a) ⊞ (► a ⊞ ► a)) ⊞ ► ((► a ⊞ ► a) ⊞ a)
                                 = ► (► a ⊞ ► a) ⊞ ► ( ► a ⊞ a ) ).
                        ++++rewrite idempotent_2.
                            assert ((► a ⊞ ► a) ⊞ a = ► a ⊞ a).
                            ****rewrite idempotent_2.
                                reflexivity.
                            ****rewrite H0.
                                reflexivity.
                        ++++rewrite H0.
                            unfold x.
                            assert (a ⊞ ► a = ► a ⊞ a).
                            rewrite conmutativity_2.
                            reflexivity.
                            rewrite H1.
                            clear H1.
                            clear H0.
                            clear H.
                            reflexivity.
                    ----rewrite H0.
                        rewrite foo_bar_baz.
                        rewrite <- theorem_2_2.
                        rewrite conmutativity_2.
                        reflexivity.
Qed.

(* 5. Para cualquier a ∈ 0K, ¬a+a=1 *)
Theorem theorem_2_5: forall x:A, ► x ⊞ x = one x.
Proof.
  intros.
  rewrite conmutativity_2.
  unfold one.
  reflexivity.
Qed.

(* 6. Para cualquier a ∈ K, ¬a◦a=0 *)
Theorem theorem_2_6: forall (a: A), ((► a) ⊡ a) = zero a.
Proof.
  intros.
  unfold multiplication_2_def.
  rewrite conmutativity_2.
  unfold multiplication_2_def.
  unfold zero.
  reflexivity.
Qed.

(* 7. Los elementos 0 y 1 son duales, es decir, ¬1=0 y ¬0=1 *)
Theorem theorem_2_7: forall (a: A), (► one a) = zero a /\ (► zero a) = (one a).
Proof.
  intros.
  split.
  symmetry.
  unfold one.
  rewrite theorem_2_2.
  unfold multiplication_2_def.
  unfold zero.
  reflexivity.
  unfold zero.
  unfold multiplication_2_def.
  rewrite <- theorem_2_2.
  rewrite theorem_2_3.
  unfold one.
  reflexivity.
Qed.


(***************************************************************)
(***************************************************************)
(****************     2. Deducción natural     *****************)
(***************************************************************)
(***************************************************************)

(***************************************************************)
(**************************  Axiomas   *************************)
(***************************************************************)
Theorem ded_na_ax_1: forall (P: Prop), (P \/ False) <-> P.
Proof.
  intros P.
  unfold iff.
  split.
  -intros.
   destruct H.
   +assumption.
   +contradiction.
  -intros.
   left. assumption.
Qed.

Theorem ded_na_ax_2: forall (P: Prop), (P /\ True) <-> P.
Proof.
  intros P.
  unfold iff.
  split.
  -intros.
   destruct H.
   assumption.
  -intros.
   split.
   +assumption.
   +trivial.
Qed.

Theorem ded_na_ax_3: forall (P Q: Prop), (P \/ Q) <-> (Q \/ P).
Proof.
  intros P Q.
  unfold iff.
  split.
  -intros.
   destruct H.
   +right. assumption.
   +left. assumption.
  -intros.
   destruct H.
   +right. assumption.
   +left. assumption.
Qed.

Theorem ded_na_ax_4: forall (P Q: Prop), (P /\ Q) <-> (Q /\ P).
Proof.
  intros P Q.
  unfold iff.
  split.
  -intros.
   split.
   +destruct H.
    assumption.
   +destruct H.
    assumption.
  -intros.
   split.
   +destruct H.
    assumption.
   +destruct H.
    assumption.
Qed.

Theorem ded_na_ax_5: forall (P Q R: Prop), (P \/ (Q /\ R)) <-> ((P \/ Q) /\ (P \/ R)).
Proof.
  intros P Q R.
  unfold iff.
  split.
  -intros.
   destruct H.
   +split.
    *left. assumption.
    *left. assumption.
   +destruct H.
    split.
    *right. assumption.
    *right. assumption.
  -intros.
   destruct H.
   destruct H.
   +left. assumption.
   +destruct H0.
    *left. assumption.
    *right.
     split.
     **assumption.
     **assumption.
Qed.

Theorem ded_na_ax_6: forall (P Q R: Prop), (P /\ (Q \/ R)) <-> ((P /\ Q) \/ (P /\ R)).
Proof.
  intros P Q R.
  unfold iff.
  split.
  -intros.
   destruct H.
   destruct H0.
   +left.
    split.
    assumption. assumption.
   +right.
    split.
    assumption. assumption.
  -intros.
   destruct H.
   +destruct H.
    split.
    *assumption.
    *left. assumption.
   +destruct H.
    split.
    *assumption.
    *right. assumption.
Qed.

Axiom classic: forall (P: Prop), P \/ ~P.

Theorem ded_na_ax_7: forall (P: Prop), P \/ ~P <-> True.
  intros P.
  unfold iff.
  split.
  -intros.
   trivial.
  -intros.
   apply classic. (*Tuve que usar clásica*)
Qed.

Theorem ded_na_ax_8: forall (P: Prop), P/\ ~P <-> False.
  intros.
  unfold iff.
  split.
  -intros.
   destruct H.
   contradiction.
  -intros.
   contradiction.
Qed.

(***************************************************************)
(************************  Propiedades   ***********************)
(***************************************************************)
Theorem ded_na_prop_1: forall (P: Prop), P \/ P <-> P.
Proof.
  intros.
  unfold iff.
  split.
  -intros.
   destruct H.
   assumption. assumption.
  -intros.
   left.
   assumption.
Qed.

Theorem ded_na_prop_2: forall (P: Prop), P /\ P <-> P.
Proof.
  intros.
  unfold iff.
  split.
  -intros.
   destruct H.
   assumption.
  -intros.
   split.
   assumption. assumption.
Qed.

Theorem ded_na_prop_3: forall (P: Prop), P \/ True <-> True.
Proof.
  intros.
  unfold iff.
  split.
  -intros.
   destruct H.
   +trivial.
   +trivial.
  -intros.
   right.
   trivial.
Qed.

Theorem ded_na_prop_4: forall (P: Prop), P /\ False  <-> False.
Proof.
  intros.
  unfold iff.
  split.
  -intros.
   destruct H.
   assumption.
  -intros.
   split.
   contradiction.
   assumption.
Qed.

Theorem ded_na_prop_5: forall (P Q: Prop), P \/ (P /\ Q) <-> P.
Proof.
  intros.
  unfold iff.
  split.
  -intros.
   destruct H. assumption.
   destruct H. assumption.
  -intros.
   left. assumption.
Qed.

Theorem ded_na_prop_6: forall (P Q: Prop), P /\ (P \/ Q) <-> P.
Proof.
  intros.
  unfold iff.
  split.
  -intros.
   destruct H. assumption.
  -intros.
   split. assumption.
   left. assumption.
Qed.

Theorem ded_na_prop_7: (~True <-> False) /\ (~False <-> True).
Proof.
  intros.
  unfold iff.
  split.
  -split.
   +intros. contradiction.
   +intro. contradiction.
  -split.
   +intros. trivial.
   +intros.
    unfold not in *.
    trivial.
Qed.

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
   +apply classic. (*Benditos axiomas*)
   +destruct H0.
    *trivial.
    *contradiction.
Qed.

Theorem ded_na_prop_8: forall (P Q: Prop), (P \/ Q) <-> ~ (~P /\ ~Q).
Proof.
  intros.
  unfold iff.
  split.
  -intros.
   unfold not.
   destruct H.
   +intros.
    destruct H0.
    contradiction.
   +intros.
    destruct H0.
    contradiction.
  -intros.
   unfold not in H.
   apply NNPP.
   unfold not.
   intros.
   apply H.
   split.
   +intros.
    apply H0.
    left.
    assumption.
   +intros.
    apply H0.
    right.
    assumption.
Qed.

Theorem ded_na_prop_9: forall (P Q: Prop), (P /\ Q) <-> ~ (~P \/ ~Q).
Proof.
  intro.
  unfold iff.
  intros.
  split.
  -intros.
   unfold not.
   intros.
   destruct H.
   destruct H0.
   contradiction. contradiction.
  -intros.
   assert (P \/ ~P).
   apply classic.
   assert (Q \/ ~Q).
   apply classic.
   unfold not in *.
   destruct H0.
   +split. assumption.
    *destruct H1. assumption.
     destruct H.
     right.
     assumption.
   +destruct H.
    left. assumption.
Qed.