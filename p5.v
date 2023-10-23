Inductive list (A:Set):Set := 
  | nil : list A
  | cons : A -> list A -> list A.

Inductive bintree (A:Set):Set :=
  | empty: bintree A
  | node : A -> bintree A -> bintree A -> bintree A.

Section Ejercicio1.
Inductive LE : nat -> nat -> Prop :=
 | Le_O : forall n : nat, LE 0 n
 | Le_S : forall n m : nat, LE n m -> LE (S n) (S m).

Inductive Mem (A : Set) (a : A) : list A -> Prop :=
 | here : forall x : list A, Mem A a (cons A a x)
 | there : forall x : list A, Mem A a x ->
              forall b : A, Mem A a (cons A b x).
              
(* 5.1 *)
Theorem not_sn_le_o: forall n:nat, ~ LE (S n) O.
Proof.
  intro n.
  unfold not; intro H.
  inversion H.
Qed.

(* 5.2 *)
Theorem nil_empty: forall (A:Set) (a:A), ~ Mem A a (nil A).
Proof.
  intros A a.
  unfold not; intro H.
  inversion H.
Qed.

(* 5.3 *)
Theorem not4lt3: ~ (LE 4 3).
Proof.
  unfold not; intro H.
  inversion_clear H.
  inversion_clear H0.
  inversion_clear H.
  apply (not_sn_le_o 0).
  exact H0.
Qed.

(* 5.4 *)
Theorem not_sn_le_n: forall n:nat, ~ LE (S n) n.
Proof.
  induction n; unfold not.
  apply (not_sn_le_o 0).
  intro H.
  inversion_clear H.
  apply IHn.
  exact H0.
Qed.

(* 5.5 *)
Lemma le_sn1: forall n m:nat, LE n m -> LE n (S m).
Proof.
  intros n m H.
  induction H.
  constructor.
  constructor.
  exact IHLE.
Qed.

Lemma le_sn2: forall n m:nat, LE (S n) m -> LE n m.
Proof.
  intros n m H.
  induction n.
  constructor.
  destruct m.
  inversion H.
  apply (le_sn1 (S n) m).
  inversion H.
  exact H2.
Qed.
Theorem le_transitive: forall n m p:nat, (LE n m) -> (LE m p) -> LE n p.
Proof.
  intros n m p.
  induction n.
  - intros H1 H2; constructor.
  - intros H1 H2.
    
Qed.
End Ejercicio1.












