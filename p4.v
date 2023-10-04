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

(* 1.7 *)
Inductive isomorfo (A:Set): bintree A -> bintree A -> Prop :=
  | isomorfo_empty : isomorfo A (empty A) (empty A)
  | isomorfo_node : forall (a b:A) (l1 r1 l2 r2:bintree A),
                      isomorfo A l1 l2 -> isomorfo A r1 r2 ->
                      isomorfo A (node A a l1 r1) (node A b l2 r2).

(* 1.8 *)
Inductive Gtree (A:Set): Set :=
  Gnode : A -> forest A -> Gtree A
with
  forest (A:Set):Set :=
    | empty_forest : forest A
    | add_forest : Gtree A -> forest A -> forest A.

End Ejercicio1.


Section Ejercicio2.

(* 2.1 *)
Definition Or :=
  fun b1 b2:bool => match b1 with
                      true => true
                    | false => b2
                    end.

Definition Or2 :=
  fun b1 b2:bool => match b1 , b2 with
                      true , _ => true
                    | false , b2 => b2
                    end.

Definition And :=
  fun b1 b2:bool => match b1 with
                      false => false
                    | true => b2
                    end.

Definition Not :=
  fun b:bool => match b with
                  true => false
                | false => true
                end.

Definition Xor :=
  fun b1 b2:bool => match b1, b2 with
                      true, false => true
                    | false, true => true
                    | _, _ => false
                    end.
                    
(* 2.2 *)
Definition is_nil :=
  fun (A:Set) (l:list A) => match l with
                              nil _      => true
                            | cons _ _ _ => false
                            end.
End Ejercicio2.

Section Ejercicio3.
(* 3.1 *)
Fixpoint sum (n m:nat) {struct n}:nat :=
  match n with
      0     => m
    | (S k) => S (sum k m)
  end.
  
(* 3.2 *)
Fixpoint prod (n m:nat) {struct n}:nat :=
  match n with
      0     => 0
    | (S k) => sum m (prod k m)
  end.
  
(* 3.3 *)
Fixpoint pot (n m:nat) {struct m}:nat :=
  match m with
      0     => 1
    | (S k) => prod n (pot n k)
  end.
  
(* 3.4 *)
Fixpoint leBool (n m: nat):bool :=
  match n, m with
      0 , _         => true
    | _ , 0         => false
    | (S a) , (S b) => leBool a b
  end.

End Ejercicio3.

Section Ejercicio4.
(* 4.1 *)
Fixpoint length (A:Set) (l:list A): nat :=
  match l with
      nil _         => 0
    | cons _ _ rest => 1 + (length A rest)
  end.

(* 4.2 *) 
Fixpoint append (A:Set) (l1 l2:list A) {struct l1}:list A :=
  match l1 with
      nil _         => l2
    | cons _ a rest => cons _ a (append _ rest l2)
  end.
  
(* 4.3 *) 
Fixpoint reverse (A:Set) (l1:list A) :list A :=
  match l1 with
      nil _         => nil _
    | cons _ a rest => (append _ (reverse _ rest) (cons _ a (nil _)))
  end.
  
(* 4.4 *) 
Fixpoint filter (A:Set) (P: A -> bool) (l1:list A) :list A :=
  match l1 with
      nil _         => nil _
    | cons _ a rest => match (P a) with
                          false => filter _ P rest
                        | true  => cons _ a (filter _ P rest)
                       end
  end.
  
(* 4.5 *) 
Fixpoint map (A B:Set) (f: A -> B) (l1:list A) :list B :=
  match l1 with
      nil _         => nil _
    | cons _ a rest => cons _ (f a) (map _ _ f rest)
  end.

(* 4.6 *) 
Fixpoint exists_ (A:Set) (P: A -> bool)(l1:list A) :bool :=
  match l1 with
      nil _         => false
    | cons _ a rest => match (P a) with
                          false => exists_ _ P rest
                        | true => true
                       end
  end.

End Ejercicio4.





























