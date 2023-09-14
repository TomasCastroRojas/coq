
Section Ejercicio4.
Variable A: Set.

Definition id := fun x:A => x.

Theorem e4_1 : forall x:A, (oGen A A A id id) x = id x.
Proof.
  intro x.
  cbv delta beta.
  reflexivity.
Qed.

Theorem e4_2 : forall x:A, (oGen A A A id id) x = id x.
Proof.
  intro x.
  compute.
  reflexivity.
Qed.

Theorem e4_3 : forall x:A, (oGen A A A id id) x = id x.
Proof.
  intro x.
  cbv delta.
  simpl.
  reflexivity.
Qed.


End Ejercicio4.


Section Ejercicio5.

(* 5.1 *)
Definition opI (A : Set) (x : A) := x.

Definition opK (A B : Set) (x: A) (y:B) := x.

Definition opS (A B C : Set) (f: A->B->C) (g: A -> B) (x:A) := (f x (g x)).

(* 5.2 *)
(* Para formalizar el siguiente lema, determine los tipos ?1 ... ?8 adecuados *)
Lemma e52 : forall A B : Set, opS A (B->A) A (opK A (B->A)) (opK A B) = opI A.
Proof.
  intros A B.
  cbv delta beta.
  reflexivity.
Qed.

End Ejercicio5.


(* Ejercicio8 *)

Section ArrayNat.
Parameter ArrayNat : forall n:nat, Set.
Parameter empty    : ArrayNat 0.
Parameter add      : forall n:nat, nat -> ArrayNat n -> ArrayNat (n + 1).

(* 8.1 *)
Check (add 0 (S 0) empty): ArrayNat (S 0).
(* 8.2 *)
Check (add 1 0 ((add 0 0 empty))): ArrayNat 2.

Check (add 3 1 (add 2 0 (add 1 (S 0) ((add 0 0 empty))))) : ArrayNat 4.
(* 8.3 *)
Parameter Concat : forall n1 n2: nat, ArrayNat n1 -> ArrayNat n2 -> ArrayNat (plus n1 n2).

(* 8.4 *)
Parameter Zip : forall n:nat, ArrayNat n -> ArrayNat n -> (nat->nat->nat) -> ArrayNat n.

(* 8.5 *)
Check ArrayNat.
(* 8.6 *)
Parameter ArrayGen : forall (X:Set) (n:nat), Set.
Parameter emptyGen : forall (X:Set), ArrayGen X 0.
Parameter addGen   : forall (X:Set) (n:nat), X -> ArrayGen X n -> ArrayGen X (n+1).
Parameter ZipGen   : forall (X:Set) (n:nat), ArrayGen X n -> ArrayGen X n -> (X->X->X) -> ArrayGen X n.

(* 8.7 *)
Parameter ArrayBool : forall n:nat, ArrayGen bool n.

End ArrayNat.

Section Ejercicio10.

Parameter Array : Set -> nat -> Set.
Parameter emptyA : forall X : Set, Array X 0.
Parameter addA : forall (X : Set) (n : nat), X -> Array X n -> Array X (S n).

Parameter Matrix : Set -> nat -> Set.
Parameter emptyM : forall X:Set, Matrix X 0.
Parameter addM : forall (X:Set) (n:nat), Array X (n+1) -> Matrix X n -> Matrix X (n+1).

Definition A1 := addA nat 0 1 (emptyA nat).
Definition A2 := addA nat 1 2 (addA nat 0 2 (emptyA nat)).
Definition A3 := addA nat 2 3 (addA nat 1 3 (addA nat 0 3 (emptyA nat))).

Definition M1 := addM nat 0 A1 (emptyM nat). (* matriz de una columna *)
Definition M2 := addM nat 1 A2 M1. (* matriz de dos columnas *) 
Definition M3 := addM nat 2 A3 M2. (* matriz de tres columnas *)

Check M3.

End Ejercicio10.


Section Ejercicio11.
Parameter ABNat : forall n : nat, Set.

Parameter emptyAB : ABNat 0.
Parameter addAB : forall n: nat, nat -> ABNat n -> ABNat n -> ABNat (n+1).

Definition AB7 := addAB 0 7 emptyAB emptyAB.
Definition AB11_3 := addAB 1 3 AB7 AB7.
Check AB11_3.

Parameter ABGen : Set -> nat -> Set.
Parameter emptyABGen : forall (X:Set), ABGen X 0.
Parameter addABGen : forall (X:Set) (n:nat), X -> ABGen X n -> ABGen X n -> ABGen X (n+1).

End Ejercicio11.


Section Ejercicio12.
Parameter AVLNat : forall n : nat, Set.
Parameter emptyAVL : AVLNat 0.
Parameter addAVL1 : forall (n:nat), nat -> AVLNat n -> AVLNat n -> AVLNat (n+1).
Parameter addAVL2 : forall (n:nat), nat -> AVLNat (n+1) -> AVLNat n -> AVLNat (n+2).
Parameter addAVL3 : forall (n:nat), nat -> AVLNat n -> AVLNat (n+1) -> AVLNat (n+2).

Definition AVL1 := addAVL1 0 10 emptyAVL emptyAVL.
Definition AVL2 := addAVL1 0 30 emptyAVL emptyAVL.
Definition AVL3 := addAVL1 1 20 AVL1 AVL2.
Check AVL3.

Parameter AVLGen : forall (X:Set) (n : nat), Set.
Parameter emptyAVLGen : forall (X:Set), AVLGen X 0.
Parameter addAVLGen1 : forall (X:Set) (n:nat), X -> AVLGen X n -> AVLGen X n -> AVLGen X (n+1).
Parameter addAVLGen2 : forall (X:Set) (n:nat), X -> AVLGen X (n+1) -> AVLGen X n -> AVLGen X (n+2).
Parameter addAVLGen3 : forall (X:Set) (n:nat), X -> AVLGen X n -> AVLGen X (n+1) -> AVLGen X (n+2).
End Ejercicio12.


Section Ejercicio14.
Variable A B C: Prop.

Lemma Ej314_1 : (A -> B -> C) -> A -> (A -> C) -> B -> C.
Proof.
  intros f a g b.
  exact (g a).
Qed.

Lemma Ej314_2 : A -> ~ ~ A.
Proof.
  unfold not.
  intros.
  exact (H0 H).
Qed.

Lemma Ej314_3 : (A -> B -> C) -> A -> B -> C.
Proof.
  exact (fun (f:A->B->C) (a:A) (b:B) => f a b).
Qed.

Lemma Ej314_4 : (A -> B) -> ~ (A /\ ~ B).
Proof.
  unfold not.
  intros.
  elim H0; intros.
  exact (H2 (H H1)).
Qed.

End Ejercicio14.



Section Ejercicio15.

Variable U : Set.
Variable e : U.
Variable A B : U -> Prop.
Variable P : Prop.
Variable R : U -> U -> Prop.

Lemma Ej315_1 : (forall x : U, A x -> B x) -> (forall x : U, A x) ->
forall x : U, B x.
Proof.
  intros.
  exact (H x (H0 x)).
Qed.

Lemma Ej315_2 : forall x : U, A x -> ~ (forall x : U, ~ A x).
Proof.
  unfold not.
  intros.
  exact (H0 x H).
Qed.

Lemma Ej315_3 : (forall x : U, P -> A x) -> P -> forall x : U, A x.
Proof.
  exact (fun (f: forall x:U, P -> A x) (p:P) (z:U) => f z p).
Qed.

Lemma Ej315_4 : (forall x y : U, R x y) -> forall x : U, R x x.
Proof.
  exact (fun (f: forall x y:U, R x y) (z:U) => f z z).
Qed.

Lemma Ej315_5 : (forall x y: U, R x y -> R y x) ->
                 forall z : U, R e z -> R z e.
Proof.
  exact (fun (f: forall x y:U, R x y -> R y x) (z:U) => f e z). 
Qed.

End Ejercicio15.

