Section Ejercicio1.

(* 1.1 *)
Inductive list (A:Set):Set := 
  | nil : list A
  | cons : A -> list A -> list A.

Inductive bintree (A:Set):Set :=
  | empty: bintree A
  | node : A -> bintree A -> bintree A -> bintree A.

(* 1.2 *)

Inductive array (A:Set): nat -> Set :=
  | emptyArray : array A 0
  | addArray : forall (n:nat), A -> array A n -> array A (S n).

Inductive matrix (A:Set): nat -> nat -> Set :=
  | one_col : forall (n:nat), array A n -> matrix A 1 n
  | extend_col : forall (m n:nat), array A n -> matrix A m n -> matrix A (S m) n.

(* 1.3 *)

Inductive leq : nat -> nat -> Prop :=
  | leq0 : forall n:nat, leq n n
  | leqS : forall n m:nat, leq n m -> leq n (S m).

(* 1.4*)
Inductive eq_list (A:Set): list A -> list A -> Prop :=
  | eq_nil : eq_list A (nil A) (nil A)
  | eq_cons : forall (a:A) (l l':list A), 
                  (eq_list A l l') -> (eq_list A (cons A a l) (cons A a l')).

(* 1.5 *)
Inductive sorted (A:Set) (R: A -> A -> Prop): list A -> Prop :=
  | sorted_nil : sorted A R (nil A)
  | sorted_singleton : forall (a:A), sorted A R (cons A a (nil A))
  | sorted_cons : forall (a b: A) l,
                  R a b -> sorted A R (cons A b l) ->
                  sorted A R (cons A a (cons A b l)).

(* 1.6 *)
Inductive mirror (A:Set) : bintree A -> bintree A -> Prop :=
  | mirror_empty : mirror A (empty A) (empty A)
  | mirror_node : forall (a:A) (l1 r1 l2 r2:bintree A), 
                    mirror A l1 r2 -> mirror A r1 l2 ->
                    mirror A (node A a l1 r1) (node A a l2 r2). 

End Ejercicio1.