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
  fun b1 b2:bool => match b1, b2 with
                      true, _ => true
                    | false, b2 => b2
                    end.

Definition And :=
  fun b1 b2:bool => match b1, b2 with
                      false, _ => false
                    | true, b2 => b2
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
                        | true  => true
                       end
  end.

End Ejercicio4.

Section Ejercicio5.
(* 5.1 *)
Fixpoint inverse (A:Set) (t: bintree A): bintree A :=
  match t with
      empty _      => empty _
    | node _ a l r => node _ a (inverse _ r) (inverse _ l)
  end.
  
(* 5.2 *)
(* TODO: consultar *)

End Ejercicio5.

Section Ejercicio6.
Definition ListN := list nat.

(* 6.1 *)
Fixpoint member (e:nat) (l:ListN) : bool :=
  match l with
      nil _         => false
    | cons _ n rest => match (Nat.eqb n e) with
                        false => member e rest
                      | true  => true
                     end
  end.
  
(* 6.2 *)
Fixpoint delete (e:nat) (l:ListN) : ListN :=
  match l with
      nil _         => nil _
    | cons _ n rest => match (Nat.eqb n e) with
                          false => cons _ n (delete e rest)
                        | true  => rest
                       end
  end.
  
(* 6.3 *)
Fixpoint insert_sorted (n:nat) (l':ListN): ListN :=
      match l' with
          nil _           => cons _ n (nil _)
        | cons _ h' rest' => if (leBool n h') then (cons _ n (cons _ h' rest'))
                                              else (cons _ h' (insert_sorted n rest'))
      end.
Fixpoint insert_sort (l:ListN):ListN :=
  match l with
      nil _         => nil _
    | cons _ h rest => insert_sorted h (insert_sort rest)
  end.
(* TODO: generalizacion de las funciones *)
End Ejercicio6.
                                                
Section Ejercicio7.
(* TODO: Como trabajar Exp *)
End Ejercicio7.

Section Ejercicio8.
(* 8.1 *)
Theorem And_asoc: forall a b: bool, And a b = And b a.
Proof.
  intros p q.
  elim p; elim q; simpl; reflexivity.
Qed.

Theorem Or_asoc: forall a b: bool, Or a b = Or b a.
Proof.
  intros p q.
  elim p; elim q; simpl; reflexivity.
Qed.

Theorem And_comm: forall a b c: bool, And a (And b c) = And (And a b) c.
Proof.
  intros p q r.
  elim p; elim q; elim r; simpl; reflexivity.
Qed.

Theorem Or_comm: forall a b c: bool, Or a (Or b c) = Or (Or a b) c.
Proof.
  intros p q r.
  elim p; elim q; elim r; simpl; reflexivity.
Qed.

(* 8.2 *)
Theorem LAnd : forall a b : bool, And a b = true <-> a = true /\ b = true.
Proof.
  intros p q.
  unfold iff.
  split.
  - elim p; elim q; simpl.
    intro t; split; reflexivity.
    intro ft; split; [reflexivity | exact ft].
    intro ft; split; [exact ft | reflexivity].
    intro ft; split; exact ft.
  - intro and; elim and; intros ptrue qtrue.
    rewrite ptrue; rewrite qtrue.
    simpl; reflexivity.
Qed.

(* 8.3 *)
Theorem LOr1 : forall a b : bool, Or a b = false <-> a = false /\ b = false.
Proof.
  intros p q.
  unfold iff.
  split.
  - elim p; elim q; simpl.
    intro ft; split; exact ft.
    intro ft; split; [exact ft | reflexivity].
    intro ft; split; [reflexivity | exact ft].
    intro t; split; reflexivity.
  - intro and; elim and; intros pfalse qfalse.
    rewrite pfalse; rewrite qfalse.
    simpl; reflexivity.
Qed.

(* 8.4 *)
Theorem LOr2 : forall a b : bool, Or a b = true <-> a = true \/ b = true.
Proof.
  intros p q.
  unfold iff.
  split.
  - elim p; simpl; intro H; [left | right]; exact H.
  - intro or; elim or; intro H; rewrite H; simpl.
    reflexivity.
    elim p; simpl; reflexivity.
Qed.

(* 8.5 *)
(*
Theorem LXor : forall a b : bool, Xor a b = true <-> a <> b.
Proof.     
Qed.
*)
(* 8.6 *)
Theorem LNot : forall b : bool, Not (Not b) = b.
Proof.
  intro p; elim p; simpl; reflexivity.
Qed.
End Ejercicio8.

Section Ejercicio9.
(* 9.1 *)
Theorem SumO : forall n : nat, sum n 0 = n /\ sum 0 n = n.
Proof.
  intro n.
  elim n.
  - split; simpl; reflexivity.
  - intro k.
    intro and; elim and; intros suml sumr; split; simpl; try (rewrite suml); reflexivity.
Qed.

(* 9.2 *)
Theorem SumS : forall n m : nat, sum n (S m) = sum (S n) m.
Proof.
  intros n m.
  elim n.
  simpl; reflexivity.
  intros k H.
  simpl; rewrite H; reflexivity.
Qed.

(* 9.3 *)
Theorem SumAsoc : forall n m p : nat, sum n (sum m p) = sum (sum n m) p.
Proof.
  intros n m p.
  elim n.
  simpl; reflexivity.
  intros k H.
  simpl.
  rewrite H.
  reflexivity.
Qed.

(* 9.4 *)
Theorem SumConm : forall n m : nat, sum n m = sum m n.
Proof.
  intros n m.
  elim n.
  elim (SumO m).
  intros sum0l sum0r.
  simpl.
  rewrite sum0l.
  reflexivity.
  intros k H; simpl.
  rewrite (SumS m k); simpl.
  rewrite H; reflexivity.
Qed.

End Ejercicio9.

Section Ejericio10.
(* 10.1 *)

Theorem ProdConm : forall n m : nat, prod n m = prod m n.
Proof.

  induction n; induction m.
  - reflexivity.
  - simpl; rewrite <- IHm; reflexivity.
  - simpl; rewrite IHn; reflexivity.
  - simpl; rewrite <- IHm.
    rewrite (IHn (S m)).
    simpl. rewrite (IHn m).
    rewrite (SumAsoc m n (prod m n)).
    rewrite (SumAsoc n m (prod m n)).
    rewrite (SumConm m n).
    reflexivity.
Qed.

End Ejericio10.

















