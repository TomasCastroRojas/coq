Section Ejercicio1.
Variable A B C: Set.

Definition term1_1 : (A->A->A)->A->A := 
  fun f x => f x x.
Check term1_1.

Lemma term1_1_tauto: (A->A->A)->A->A.
Proof.
  tauto.
Qed. 

Lemma term1_1_exact: (A->A->A)->A->A.
Proof.
  exact (fun f x => f x x).
Qed.

Definition term1_2 : (A -> B) -> (B -> C) -> A -> B -> C :=
  fun f g a b => g (f a).
Check term1_2.

Lemma term1_2_tauto: (A -> B) -> (B -> C) -> A -> B -> C.
Proof.
  tauto.
Qed. 

Lemma term1_2_exact: (A -> B) -> (B -> C) -> A -> B -> C.
Proof.
  exact (fun f g a b => g (f a)).
Qed.

Definition term1_3 : (A -> B) -> (A -> B -> C) -> A -> C :=
  fun f g a => g a (f a).
Check term1_2.

Lemma term1_3_tauto: (A -> B) -> (A -> B -> C) -> A -> C.
Proof.
  tauto.
Qed. 

Lemma term1_3_exact: (A -> B) -> (A -> B -> C) -> A -> C.
Proof.
  exact (fun f g a => g a (f a)).
Qed.

Definition term1_4 : (A -> B) -> ((A -> B) -> C)-> C :=
  fun f g => g f.
Check term1_2.

Lemma term1_4_tauto: (A -> B) -> ((A -> B) -> C)-> C.
Proof.
  tauto.
Qed. 

Lemma term1_4_exact: (A -> B) -> ((A -> B) -> C)-> C.
Proof.
  exact (fun f g => g f).
Qed.
 
End Ejercicio1.


Section Ejercicio2.
Variable A B C: Set.

(*[x:A->B->C][y:A][z:B]((x y)z)*)
Definition term2_1: (A->B->C)->A->B->C :=
  fun x y z => (x y) z.
Check term2_1.

(*[x:?][y:?][z:?] (x (y z)*)
Definition term2_2: (B->C) -> (A -> B) -> A -> C :=
  fun x y z => x (y z).
Check term2_2.

(*[z:?] ([x:?][y:?](x y) z)*)
Definition term2_3 : B -> (A -> B -> C) -> A -> C :=
  fun z => fun x y => (x y) z.
Check term2_3.

(*([x:?]x [y:?]y)*) 
Definition term2_4 : ((A -> A) -> B) -> B :=
  fun x => x (fun y => y).
Check term2_4.

End Ejercicio2.


Section Ejercicio3.
Variable A B C: Set.

Definition apply: (A->B)->A->B :=
  fun f a => (f a).
Check apply.

Definition applyGen: forall A B : Set, (A->B)->A->B :=
  fun a b (f:a->b) (x:a) => (f x).
Check applyGen.

Definition o :  (A->B)->(B->C)->(A->C) :=
  fun f g => fun x => g (f x).
Check o.

Definition oGen : forall A B C : Set, (A->B)->(B->C)->(A->C) :=
  fun a b c (f:a -> b) (g:b->c) => fun x:a => g (f x).
Check oGen.

Definition twice : (A -> A) -> A -> A :=
  fun f x => f (f x).
Check twice.

Definition twiceGen : forall A : Set, (A -> A) -> A -> A :=
  fun a (f:a->a) (x:a) => f (f x).
Check twiceGen.

End Ejercicio3.


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


Section Ejercicio6.
Definition N := forall X : Set, X -> (X -> X) -> X.
Definition Zero (X : Set) (o : X) (f : X -> X) := o.
Definition Uno  (X : Set) (o : X) (f : X -> X) := f (Zero X o f).

(* 6.1 *)
Definition Dos (X : Set) (o : X) (f : X -> X) := f (Uno X o f).

(* 6.2 *)
Definition Succ (n: N) : N := fun (X: Set) (o: X) (f : X -> X) => f (n X o f).

Lemma succUno : Succ Uno = Dos.
Proof.
  cbv delta beta.
  reflexivity.
Qed.

(* 6.3 *)
Definition Plus (n m : N) : N
                := fun (X : Set) (o : X) (f : X -> X) => n X (m X o f) f.


Infix "+++" := Plus (left associativity, at level 94).

Lemma suma1: (Uno +++ Zero) = Uno.
Proof.
  compute.
  reflexivity.
Qed.

Lemma suma2: (Uno +++ Uno) = Dos.
Proof.
  compute.
  reflexivity.
Qed.

(* 6.4 *)
Definition Prod (n m : N) : N
                := fun (X:Set) (o:X) (f:X->X) => m X o (fun y:X => n X y f).


Infix "**" := Prod (left associativity, at level 94).

(* 6.5 *)
Lemma prod1 : (Uno ** Zero) = Zero.
Proof.
  compute.
  reflexivity.
Qed.

Lemma prod2: (Uno ** Dos) = Dos.
Proof.
  compute.
  reflexivity.
Qed.

End Ejercicio6.


Section Ejercicio7.
(* 7.1 *)
Definition Bool := forall X:Set, X -> X -> X.
Definition t    (X:Set) (x:X) (y:X) := x. 
Definition f    (X:Set) (x:X) (y:X) := y.

(* 7.2 *)
Definition If (p q r:Bool):Bool := fun (X:Set) (x:X) (y:X) => p X (q X x y) (r X x y).


(* 7.3 *)
Definition Not (p:Bool) : Bool := fun (X:Set) (x:X) (y:X) => p X (f X x y) (t X x y).


Lemma CorrecNot : (Not t) = f /\ (Not f) = t.
Proof.
  split.
  cbv delta beta.
  reflexivity.
  cbv delta beta.
  reflexivity.
Qed.

(* 7.4 *)
Definition And (p q: Bool) : Bool := fun (X:Set) (x:X) (y:X) => p X (q X x y) (f X x y).

Definition And' (p q: Bool) : Bool := fun (X:Set) (x:X) (y:X) => (If p q f X x y).

(* 7.5 *)
Infix "&" := And (left associativity, at level 94).

Lemma CorrecAnd : (t & t) = t /\ (f & t) = f /\ (t & f) = f.
Proof.
  compute.
  split.
  reflexivity.
  split.
  reflexivity.
  reflexivity.
Qed.

End Ejercicio7.



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


Section Ejercicio9.
(* 9.1 *)
Parameter MatrizNat : forall n m : nat, Set.


(* 9.2 *)
Parameter prod : forall n m p : nat, MatrizNat n m -> MatrizNat m p -> MatrizNat n p.

Parameter es_id: forall n : nat, MatrizNat n n -> bool.

Parameter ins_fila : forall n m : nat, MatrizNat n m -> MatrizNat 1 m -> MatrizNat (n+1) m.

Parameter ins_columna : forall n m , MatrizNat n m -> MatrizNat n 1 -> MatrizNat n (m+1).

End Ejercicio9.


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


Section Ejercicio13.
Variable A B C: Set.

Lemma e13_1 : (A -> B -> C) -> B -> A -> C.
Proof.
  ...
Qed.

Lemma e13_2 : (A -> B) -> (B -> C) -> A -> C.
Proof.
  ...
Qed.

Lemma e13_3 : (A -> B -> C) -> (B -> A) -> B -> C.
Proof.
  ...
Qed.

End Ejercicio13.


Section Ejercicio14.
Variable A B C: Prop.

Lemma Ej314_1 : (A -> B -> C) -> A -> (A -> C) -> B -> C.
Proof.
  intros f a g b.
        ...
Qed.

Lemma Ej314_2 : A -> ~ ~ A.
Proof.
  unfold not.
  intros.
     ...
Qed.

Lemma Ej314_3 : (A -> B -> C) -> A -> B -> C.
Proof.
     ...
Qed.

Lemma Ej314_4 : (A -> B) -> ~ (A /\ ~ B).
Proof.
  unfold not.
  intros.
  elim H0; intros.
     ...
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
   ...
Qed.

Lemma Ej315_2 : forall x : U, A x -> ~ (forall x : U, ~ A x).
Proof.
  unfold not.
  intros.
  ...
Qed.

Lemma Ej315_3 : (forall x : U, P -> A x) -> P -> forall x : U, A x.
Proof.
    ...
Qed.

Lemma Ej315_4 : (forall x y : U, R x y) -> forall x : U, R x x.
Proof.
     ...
Qed.

Lemma Ej315_5 : (forall x y: U, R x y -> R y x) ->
                 forall z : U, R e z -> R z e.
Proof.
     ...
Qed.

End Ejercicio15.

