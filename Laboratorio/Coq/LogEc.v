(*
* Lógica computacional 2017-2
* Tema: Lógica ecuacional.
* Profesora: Lourdes del Carmen González Huesca
* Ayudante: Roberto Monroy Argumedo
* Laboratorio: Fernando A. Galicia Mendoza
*)

(*
* Primero comencemos con teoría de grupos.
*)

(*
* El vernáculo Hypothesis es para indicar que proposiciones, variables y tipos
* se supondrán.
*)
Hypotheses (A:Set)
           (e:A)  (* Elemento neutro *)
           (m:A -> A -> A)  (* Operacion del grupo mul x y = x * y *)
           (i:A -> A). (* Inverso i x = x^-1*)

(*El vernáculo Infix es para darle una notación infija a alguna función.*)
Infix "&" := m (at level 40).

(*El vernáculo Axiom es para indicar los axiomas de la teoría en la cual trabajaremos.*)
Axiom asoc : forall x y z : A, x & (y & z) = (x & y) & z. (* x*(y* z)=(x*y)*z *)

Axiom idI : forall x:A, e & x = x.
(* e*x = x *)

Axiom invI : forall x:A, (i x) & x = e.
(* x^-1 * x = e *)

(*Theorem es un vernáculo que indica teorema*)

(*Un ejemplo de asociatividad*)
Theorem ej1: forall x y:A,  (x & y) & (e & x) = x & (y & x).
Proof.
  intros.
  rewrite idI.
  rewrite <- asoc.
  reflexivity.
Qed.

(*Un caso de unicidad.*)
Theorem UnicIdI: forall x:A, x & x = x -> x = e.
Proof.
  (*Prueba del ayudante.
  intros.
  rewrite <- idI with x.
  rewrite <- (invI x).
  rewrite <- asoc.
  rewrite H.
  trivial.
   *)
  (*Prueba de Daniel*)
  rewrite <- (invI x).
  symmetry.
  transitivity (i x & (x & x)).
  rewrite H.
  reflexivity.
  rewrite asoc.
  transitivity ((i x & (x & x)) & x).
  rewrite H.
  reflexivity.
  rewrite asoc.
  rewrite invI.
  rewrite idI.
  rewrite H.
  reflexivity.*)
Qed.

(*Inverso derecho*)
Theorem invD: forall x:A, x & (i x) = e.
Proof.
  intros.
  apply UnicIdI. (*Si tienes q y a parte un teorema indica p -> q, entonces basta demostrar p.*)
  rewrite <- asoc.
  transitivity (x & ((i x & x) & i x)).
  rewrite asoc.
  rewrite asoc.
  rewrite asoc.
  rewrite asoc.
  trivial.
  rewrite invI.
  rewrite idI.
  trivial.
Qed.

(*Elemento neutro derecho*)
Theorem idD: forall x:A, x & e = x.
Proof.
  intros (*Ángel*).
  rewrite <- (invI x) (*Francisco*).
  rewrite asoc.
  rewrite invD.
  rewrite idI (*Ándres*).
  trivial.
Qed.

(*Congruencia izquierda*)
Lemma congI: forall x y z:A, x = y ->
                             x & z = y & z.
Proof.
  intros.
  rewrite H (*Eder*).
  trivial.
Qed.

(*Congruencia derecha*)
Lemma congD: forall x y z:A, x = y ->
                             z & x = z & y.
Proof.
  intros.
  rewrite H.
  trivial.
Qed.

(*Ley de cancelación izquierda.*)
Lemma CanI: forall x y z:A, x & y = x & z ->
                            y = z.
Proof.
  intros.
  (*Ándres*)
  assert (i x & (x & y) = i x & (x & z)).
  apply congD.
  trivial.
  rewrite asoc in H0.
  rewrite asoc in H0.
  rewrite invI in H0.
  rewrite idI in H0.
  rewrite idI in H0.
  trivial.
Qed.

(*Ley de cancelación derecha.*)
Lemma CanD: forall x y z:A, y & x = z & x ->
                            y = z.
Proof.
  intros.
  (*Daniel*)
  assert ((y & x) & i x = (z & x) & i x).
  apply congI.
  trivial.
  rewrite <- asoc in H0.
  rewrite <- asoc in H0.
  rewrite invD in H0.
  rewrite idD in H0.
  rewrite idD in H0.
  trivial.
Qed.

(*Neutro derecho único.*)
Theorem NeuID:  exists! e:A, forall x:A,
      x & e = x.
Proof.
  exists e.
  (*
   * Ándres, Daniel y Francisco
   *)
  unfold unique. (*Cuando tienes que un símbolo es azúcar sintáctica de un conjunto de operaciones, unfold las desglosa.*)
  split.
  -intros.
   rewrite idD.
   trivial.
  -intros.
   rewrite <- H with e.
   rewrite idI.
   trivial.
Qed.

(*Inverso derecho único.*)
Theorem invUniq: forall x:A, exists! x':A,
      x & x' = e.
Proof.
  intros.
  (*
   * Ándres, Daniel y Francisco
   *)
  unfold unique.
  exists (i x). (*Para indicar que existe un elemento.*)
  split. (*Separa la meta en dos submetas.*)
  -rewrite invD.
   trivial.
  -intros.
   rewrite <- invD with x in H.
   apply CanI in H.
   symmetry.
   trivial.
Qed.

(*El inverso es involutivo.*)
Theorem invinv: forall x:A, i (i x) = x.
Proof.
  intros.
  assert (i x & i (i x) = e).
  rewrite invD.
  trivial.
  (*
   * Lo de invUniq no es necesario, pero
   * dio la idea para instanciar.
   * Francisco
   *)
  destruct invUniq with (i x).
  unfold unique in H0.
  destruct H0.
  assert (i x & x = e).
  rewrite invI.
  trivial.
  apply CanI with (i x).
  rewrite H.
  rewrite invI.
  trivial.
Qed.

(*El inverso del producto*)
Theorem invop: forall x y:A, i (x & y) = (i y) & (i x).
Proof.
  intros.
  (*
   * Daniel, Ándres y Eder
   *)
  assert (i (x & y) & (x & y) = e).
  rewrite invI.
  trivial.
  assert ((i y & i x) & (x & y) = e).
  rewrite asoc.
  rewrite <- asoc with (i y) (i x) x.
  rewrite invI.
  rewrite idD.
  rewrite invI.
  trivial.
  assert (i (x & y) & (x & y) = (i y & i x) & (x & y)).
  transitivity e.
  trivial.
  symmetry.
  trivial.
  apply CanD in H1.
  trivial.
Qed.

(*La suma de naturales.*)
Fixpoint suma (n m:nat) : nat :=
  match n with
  | 0 => m
  | S n' => S (suma n' m)
  end.

Proposition suma0 : forall n: nat,
    suma n 0 = n.
Proof.
  intros.
  Print nat_ind.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  trivial.
Qed.

(*La suma conmmuta*)
Theorem sumaCom: forall n m:nat,
    suma n m = suma m n.
Proof.
  intros.
  induction n.
  rewrite suma0.
  reflexivity.
  simpl.
  rewrite IHn.
  clear IHn.
  induction m0.
  reflexivity.
  simpl.
  rewrite IHm0.
  trivial.
Qed.

(*Una segunda definición.*)
Fixpoint suma2 (n m:nat) : nat :=
  match n with
  | 0 => m
  | S n' => suma2 n' (S m)
  end.

(*Las definiciones son equivalentes.*)
Theorem suma_eq_suma2: forall n m:nat,
    suma n m = suma2 n m.
  (*Tarea moral*)
Admitted.

(*Suma2 conmuta*)
Corollary suma2Com: forall n m:nat,
    suma2 n m = suma2 m n.
Proof.
  intros.
  rewrite <- suma_eq_suma2.
  rewrite <- suma_eq_suma2.
  rewrite sumaCom.
  trivial.
Qed.  