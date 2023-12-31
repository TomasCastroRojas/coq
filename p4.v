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
Fixpoint nodos_internosG (A:Set) (gt: Gtree A) : nat :=
  match gt with
    Gnode _ _ f => 1 + (nodos_internosF _ f)
  end
  with
    nodos_internosF (A:Set) (f: forest A): nat :=
      match f with
          empty_forest _     => 0
        | add_forest _ gt f' => (nodos_internosG _ gt) + (nodos_internosF _ f')
      end.

Fixpoint nodos_externosG (A:Set) (gt: Gtree A) : nat :=
  match gt with
    Gnode _ _ f => (nodos_externosF _ f)
  end
  with
    nodos_externosF (A:Set) (f: forest A): nat :=
      match f with
          empty_forest _ => 1
        | add_forest _ gt f' => (nodos_externosG _ gt) + (nodos_externosF _ f')
      end.

Definition nodos (A:Set) (gt: Gtree A): bool := (leBool (nodos_internosG _ gt) (nodos_externosG _ gt)).

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

(* Generalizacion de las funciones *)
Fixpoint memberGen (A:Set) (elem:A) (l: list A) (eq: A -> A -> bool): bool :=
  match l with
      nil _         => false
    | cons _ a rest => if (eq a elem) then true
                                      else (memberGen _ elem rest eq)
  end.

Fixpoint deleteGen (A:Set) (elem:A) (l: list A) (eq: A -> A -> bool): list A :=
  match l with
      nil _         => nil _
    | cons _ a rest => if (eq a elem) then rest
                                      else (cons _ a (deleteGen _ elem rest eq))
  end.

Fixpoint insert_sortedGen (A:Set) (elem:A) (l:list A) (le: A -> A -> bool): list A :=
  match l with
      nil _ => cons _ elem (nil _)
    | cons _ h rest => if (le elem h) then (cons _ elem (cons _ h rest))
                                      else (cons _ h (insert_sortedGen _ elem rest le))
  end.

Fixpoint insert_sortGen (A:Set) (l: list A) (le: A -> A -> bool): list A :=
  match l with
      nil _ => nil _
    | cons _ h rest => (insert_sortedGen _ h (insert_sortGen _ rest le) le)
  end.
End Ejercicio6.
                                                
Section Ejercicio7.
                                        
Inductive Exp (a: Set): Set :=
  | const: a -> Exp a
  | sum_exp: Exp a -> Exp a -> Exp a
  | prod_exp: Exp a -> Exp a -> Exp a
  | op_exp: Exp a -> Exp a.

Fixpoint eval_nat (e: Exp nat): nat :=
  match e with
    | const _ a => a
    | sum_exp _ a b => (eval_nat a) + (eval_nat b)
    | prod_exp _ a b => (eval_nat a) * (eval_nat b)
    | op_exp _ a => eval_nat a
  end.

Fixpoint eval_bool (e: Exp bool): bool :=
  match e with
    | const _ a => a
    | sum_exp _ a b => bool_or (eval_bool a) (eval_bool b)
    | prod_exp _ a b => bool_and (eval_bool a) (eval_bool b)
    | op_exp _ a => bool_not (eval_bool a)
  end.
                                        
End Ejercicio7.

Section Ejercicio8.
(* 8.1 *)
Lemma And_asoc: forall a b: bool, And a b = And b a.
Proof.
  induction a;induction b; simpl; reflexivity.
Qed.

Lemma Or_asoc: forall a b: bool, Or a b = Or b a.
Proof.
  induction a;induction b; simpl; reflexivity.
Qed.

Lemma And_comm: forall a b c: bool, And a (And b c) = And (And a b) c.
Proof.
  induction a;induction b; induction c; simpl; reflexivity.
Qed.

Lemma Or_comm: forall a b c: bool, Or a (Or b c) = Or (Or a b) c.
Proof.
  induction a;induction b; induction c; simpl; reflexivity.
Qed.

(* 8.2 *)

Lemma LAnd : forall a b : bool, And a b = true <-> a = true /\ b = true.
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
Lemma LOr1 : forall a b : bool, Or a b = false <-> a = false /\ b = false.
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
Lemma LOr2 : forall a b : bool, Or a b = true <-> a = true \/ b = true.
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

Lemma LXor : forall a b : bool, Xor a b = true <-> a <> b.
Proof.
  intros p q.
  unfold iff.
  split.
  - elim p; elim q; simpl; intro; unfold not.
    discriminate.
    intro; discriminate.
    intro; discriminate.
    discriminate.
  - elim p; elim q; intro; simpl; try reflexivity; elim H; reflexivity.
Qed.

(* 8.6 *)
Lemma LNot : forall b : bool, Not (Not b) = b.
Proof.
  induction b; simpl; reflexivity.
Qed.
End Ejercicio8.

Section Ejercicio9.
(* 9.1 *)
Lemma SumO : forall n : nat, sum n 0 = n /\ sum 0 n = n.
Proof.
  induction n.
  - split; simpl; reflexivity.
  - split; elim IHn; intros sum0l sum0r; simpl; try (rewrite sum0l); reflexivity.
Qed.

(* 9.2 *)
Lemma SumS : forall n m : nat, sum n (S m) = sum (S n) m.
Proof.
  induction n.
  - intro m; simpl; reflexivity.
  - intro m; simpl; rewrite (IHn m); reflexivity.
Qed.

(* 9.3 *)
Lemma SumAsoc : forall n m p : nat, sum n (sum m p) = sum (sum n m) p.
Proof.
  induction n.
  - intros m p; simpl; reflexivity.
  - intros m p.
    simpl.
    rewrite (IHn m p).
    reflexivity.
Qed.

(* 9.4 *)
Lemma SumConm : forall n m : nat, sum n m = sum m n.
Proof.
  induction n.
  - intro m.
    elim (SumO m).
    intros sum0l sum0r.
    simpl.
    rewrite sum0l.
    reflexivity.
  - intro m.
    simpl.
    rewrite (SumS m n).
    simpl.
    rewrite (IHn m).
    reflexivity.
Qed.

End Ejercicio9.

Section Ejericio10.

(* 10.1 *)
Lemma ProdConm : forall n m : nat, prod n m = prod m n.
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

(* 10.2 *)
Lemma ProdDisrt_R: forall n m p:nat, prod (sum n m) p = sum (prod n p) (prod m p).
Proof.
  induction n.
  intros m p.
  - simpl.
    reflexivity.
  - intros m p.
    simpl.
    rewrite (IHn m p).
    rewrite (SumAsoc p (prod n p) (prod m p)).
    reflexivity.
Qed.

Lemma ProdAsoc: forall n m p: nat, prod n (prod m p) = prod (prod n m) p.
Proof.
  induction n.
  - intros m p.
    reflexivity.
  - intros m p.
    simpl.
    rewrite (ProdDisrt_R m (prod n m) p).
    rewrite (IHn m p).
    reflexivity.
Qed.

(* 10.3 *)
Lemma ProdDistr: forall n m p: nat, prod n (sum m p) = sum (prod n m) (prod n p).
Proof.
  induction n.
  - intros m p.
    reflexivity.
  - intros m p.
    simpl.
    rewrite (IHn m p).
    rewrite <- (SumAsoc m p (sum (prod n m) (prod n p))).
    rewrite (SumAsoc p (prod n m) (prod n p)).
    rewrite (SumConm p (prod n m)).
    rewrite <- (SumAsoc (prod n m) p (prod n p)).
    rewrite (SumAsoc m (prod n m) (sum p (prod n p))).
    reflexivity.
Qed.

End Ejericio10.

Section Ejercicio11.

(* 11.1 *)
Lemma L1: forall (A:Set) (l: list A), append A l (nil A) = l.
Proof.
  intro A.
  induction l.
  - simpl; reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

(* 11.2 *)
Lemma L2: forall (A : Set) (l : list A) (a : A), ~(cons A a l) = nil A.
Proof.
  intro A.
  induction l.
  - intro a.
    unfold not.
    intro; discriminate.
  - intro a'.
    unfold not.
    intro H.
    discriminate.
Qed.
(* 11.3 *)
Lemma L3 : forall (A : Set) (l m : list A) (a : A),
                            cons A a (append A l m) = append A (cons A a l) m.
Proof.
  intro A.
  induction l.
  - intros m a.
    simpl.
    reflexivity.
  - intros m a'.
    simpl.
    rewrite (IHl m a).
    reflexivity.
Qed.
(* 11.4 *)
Lemma L4 : forall (A : Set) (l m : list A),
                            length A (append A l m) = sum (length A l) (length A m).
Proof.
  intro A.
  induction l.
  - intro m.
    simpl.
    reflexivity.
  - intro m.
    simpl.
    rewrite (IHl m).
    reflexivity.
Qed.
(* 11.5 *)
Lemma L5 : forall (A : Set) (l : list A), length A (reverse A l) = length A l.
Proof.
  intro A.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite (L4 A (reverse A l) (cons A a (nil A))).
    rewrite IHl.
    simpl.
    rewrite (SumConm (length A l) 1).
    simpl.
    reflexivity.
Qed.
End Ejercicio11.

Section Ejercicio12.

(* 12.1 *)
Lemma L7 : forall (A B : Set) (l m : list A) (f : A -> B),
map A B f (append A l m) = append B (map A B f l) (map A B f m).
Proof.
  intros A B.
  induction l.
  - intros m f.
    simpl.
    reflexivity.
  - intros m f.
    simpl.
    rewrite (IHl m f).
    reflexivity.
Qed.
(* 12.2 *)
Lemma L8 : forall (A : Set) (l m : list A) (P : A -> bool),
filter A P (append A l m) = append A (filter A P l) (filter A P m).
Proof.
  intro A.
  induction l.
  - intros m P.
    simpl.
    reflexivity.
  - intros m P.
    simpl.
    rewrite (IHl m P).
    case (P a).
    simpl.
    reflexivity.
    reflexivity.
Qed.

(* 12.3 *)
Lemma L9 : forall (A : Set) (l : list A) (P : A -> bool),
filter A P (filter A P l) = filter A P l.
Proof.
  intro A.
  induction l.
  - intro P.
    simpl.
    reflexivity.
  - intro P.
    simpl.
    case_eq (P a).
    intro Pa.
    simpl.
    rewrite Pa.
    rewrite (IHl P).
    reflexivity.
    intro notPa.
    rewrite (IHl P).
    reflexivity.
Qed.

(* 12.4 *)
Lemma L10 : forall (A : Set) (l m n : list A),
append A l (append A m n) = append A (append A l m) n.
Proof.
  intro A.
  induction l.
  - intros m n.
    simpl.
    reflexivity.
  - intros m n.
    simpl.
    rewrite (IHl m n).
    reflexivity.
Qed.

End Ejercicio12.

Section Ejercicio13.
Fixpoint filterMap (A B : Set) (P : B -> bool) (f : A -> B)
(l : list A) {struct l} : list B :=
  match l with
   | nil _ => nil B
   | cons _ a l1 =>
     match P (f a) with
       | true => cons B (f a) (filterMap A B P f l1)
       | false => filterMap A B P f l1
     end
  end.

Lemma FusionFilterMap : forall (A B : Set) (P : B -> bool) (f : A -> B) (l : list A),
                          filter B P (map A B f l) = filterMap A B P f l.
Proof.
  intros A B P f.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    case (P (f a)); rewrite IHl; reflexivity.
Qed.
End Ejercicio13.


Section Ejercicio14.
Lemma inverse_is_mirror: forall (A:Set) (t:bintree A), mirror A (inverse A t) t.
Proof.
  intro A.
  induction t.
  - simpl.
    constructor.
  - simpl.
    constructor.
    exact IHt2.
    exact IHt1.
Qed.

End Ejercicio14.

Section Ejercicio15.
Lemma iso_tree_id: forall (A:Set) (t: bintree A), isomorfo _ t t.
Proof.
induction t; simpl; constructor; [exact IHt1 | exact IHt2].
Qed.

Lemma iso_tree_sym: forall (A:Set) (t1 t2: bintree A), isomorfo _ t1 t2 -> isomorfo _ t2 t1.
Proof.
  intros.
  induction H.
  - constructor.
  - constructor; [exact IHisomorfo1 | exact IHisomorfo2].
Qed.
End Ejercicio15.

Section Ejercicio16.

Inductive Tree (A:Set): Set :=
  | leaf_t: A -> Tree A
  | node_t: Tree A -> Tree A -> Tree A.

(* 16.1 *)
Fixpoint mapTree (A B:Set) (t: Tree A) (f: A -> B): Tree B :=
  match t with
    | leaf_t _ a => leaf_t B (f a)
    | node_t _ l r => node_t B (mapTree A B l f) (mapTree A B r f)
  end.

(* 16.2 *)
Fixpoint sizeTree (A:Set) (t: Tree A): nat :=
  match t with
    | leaf_t _ _ => 1
    | node_t _ l r => (sizeTree _ l) + (sizeTree _ r)
  end.

(* 16.3 *)
Lemma inv_size_map: forall (A B:Set) (t: Tree A) (f: A -> B), sizeTree A t = sizeTree B (mapTree A B t f).
Proof.
  intros.
  induction t; simpl.
  - reflexivity.
  - rewrite <- IHt1; rewrite <- IHt2.
    reflexivity.
Qed.

Fixpoint tree_to_list (a: Set) (t: Tree a) {struct t}: list a :=
  match t with
    | leaf_t _ e => cons _ e (nil _)
    | node_t _ l r => append _ (tree_to_list _ l) (tree_to_list _ r)
  end.

Lemma tree_to_list_size: forall (a: Set) (t: Tree a), sizeTree _ t = length _ (tree_to_list _ t).
Proof.
induction t; simpl.
- reflexivity.
- rewrite IHt1. rewrite IHt2.
  rewrite (L4 _ (tree_to_list a t1) (tree_to_list a t2)).
  reflexivity.
Qed.

End Ejercicio16.

Section Ejercicio17.
(* 17.1 *)
Inductive posfijo (A:Set) : list A -> list A -> Prop :=
  | posfijo0 : forall l1, posfijo A l1 l1
  | posfijoS : forall (l1 l2: list A) (a:A), posfijo A l1 l2 -> posfijo A l1 (cons A a l2).

(* 17.2 *)
Lemma LPosfijo1: forall (A:Set) (l1 l2 l3:list A), l2 = append A l3 l1 -> posfijo A l1 l2.
Proof.
  intros A l1 l2 l3 H.
  rewrite H; clear H.
  induction l3.
  - simpl.
    constructor.
  - simpl.
    constructor.
    exact IHl3.
Qed.

Lemma LPosfijo2: forall (A:Set) (l1 l2:list A), posfijo A l1 l2 -> exists (l3: list A), l2 = append A l3 l1.
Proof.
  intros A l1 l2 H.
  elim H.
  - intro l.
    exists (nil A).
    reflexivity.
  - intros l3 l4 a.
    intros H1 H2.
    elim H2.
    intro l0.
    intro H3.
    exists (cons A a l0).
    simpl.
    rewrite H3.
    reflexivity.
Qed.

Lemma LPosfijo3: forall (A:Set) (l1 l2:list A), posfijo A l2 (append A l1 l2).
Proof.
  intro A.
  induction l1.
  - intro l2.
    simpl.
    constructor.
  - intro l2.
    simpl.
    constructor.
    exact (IHl1 l2).
Qed.

(* 17.3 *)
Fixpoint ultimo (A:Set) (l:list A): list A :=
  match l with
    | nil _ => nil A
    | cons _ a rest => match rest with
                         | nil _ => cons A a (nil A)
                         | cons _ _ rest' => ultimo A rest
                       end
  end.


Lemma LUltimo_aux: forall (A:Set) (l:list A) (a a':A),
                       ultimo A (cons A a (cons A a' l)) = ultimo A (cons A a' l).
Proof.
  intros.
  induction l.
  - simpl; reflexivity.
  - simpl.
    reflexivity.
Qed.
Lemma LPosfijo4: forall (A:Set) (l:list A), posfijo A (ultimo A l) l.
Proof.
  intro A.
  induction l.
  - simpl.
    constructor.
  - destruct l.
    simpl; constructor.
    rewrite (LUltimo_aux A l a a0).
    constructor.
    exact IHl.
Qed.

End Ejercicio17.

Section Ejercicio18.

Inductive ABin (A B: Set): Set :=
  | leaf_abt: B -> ABin A B
  | add_abtree: A -> ABin A B -> ABin A B -> ABin A B.

Fixpoint count_leafs (A B:Set) (t: ABin A B): nat :=
  match t with
    | leaf_abt _ _ _ => 1
    | add_abtree _ _ _ l r => (plus (count_leafs _ _ l) (count_leafs _ _ r))
  end.

Fixpoint count_interns (A B:Set) (t:ABin A B): nat :=
  match t with
    | leaf_abt _ _ _ => 0
    | add_abtree _ _ _ l r => S (plus (count_interns _ _ l) (count_interns _ _ r))
  end.

Lemma count_nodes_abt: forall (A B:Set) (t: ABin A B), count_leafs A B t = S (count_interns A B t).
Proof.
  intros.
  induction t; simpl; auto.
  rewrite IHt1.
  rewrite IHt2.
  simpl.
  auto.
Qed.

End Ejercicio18.

Section Ejercicio19.
Variable A : Set.

Inductive Tree_ : Set :=
  | nullT : Tree_
  | consT : A -> Tree_ -> Tree_ -> Tree_.

Inductive isSubTree: Tree_ -> Tree_ -> Prop :=
  | subtree_id: forall (t: Tree_), isSubTree t t
  | subtree_left: forall (t t1 t2: Tree_) (a: A), isSubTree t t1 -> isSubTree t (consT a t1 t2)
  | subtree_right: forall (t t1 t2: Tree_) (a: A), isSubTree t t2 -> isSubTree t (consT a t1 t2).

Lemma subtree_refl: forall (t: Tree_), isSubTree t t.
Proof.
  constructor.
Qed.

Lemma subtree_trans: forall (t1 t2 t3: Tree_), isSubTree t1 t2 -> isSubTree t2 t3 -> isSubTree t1 t3.
Proof.
  intros.
  induction H0.
  - exact H.
  - apply subtree_left.
    apply IHisSubTree.
    exact H.
  - apply subtree_right.
    apply IHisSubTree.
    exact H.
Qed.

End Ejercicio19.

Section Ejercicio20.
(* 20.1 *)
Inductive ACom (A:Set):nat -> Set :=
  | leaf : A -> ACom A 0
  | addACom : forall (n:nat), A -> ACom A n -> ACom A n -> ACom A (S n).

(* 20.2 *)  
Fixpoint h (A:Set) (n:nat) (t:ACom A n): nat :=
  match t with
    | leaf _ _ => 1
    | addACom _ m _ l r => sum (h A m l) (h A m r)
  end.

(* 20.3 *)
Axiom potO : forall n : nat, pot (S n) 0 = 1.
Axiom potS : forall m: nat, pot 2 (S m) = sum (pot 2 m) (pot 2 m).

Lemma nodesACom : forall (A:Set) (n: nat) (t: ACom A n), h A n t = pot 2 n.
Proof.
  intros A n.
  induction t.
  - simpl; reflexivity.
  - simpl.
    rewrite (SumConm (pot 2 n) 0).
    simpl.
    rewrite IHt1; rewrite IHt2.
    reflexivity.
Qed.
(* TODO: deberia ser con induccion en la altura. No encuentro la manera de reemplazar
         ACom A 0 -> leaf A a para algun a y asi simplificar la funcion h
*)

End Ejercicio20.


Section Ejercicio21.
Require Import Arith.PeanoNat.
Require Import Arith.Compare_dec.
Require Import Lia.

Inductive AB (A:Set) : nat -> Set :=
  | emptyAB : AB A 0
  | forkAB  : forall (h1 h2:nat), A -> AB A h1 -> AB A h2 -> AB A (S (max h1 h2)).
  
Fixpoint camino (A:Set) (n:nat) (t: AB A n): list A :=
  match t with
    | emptyAB _ => nil A
    | forkAB _ h1 h2 a l r => if (h2 <=? h1) then cons A a (camino A h1 l)
                                             else cons A a (camino A h2 r)
  end.

Lemma LCamino: forall (A:Set) (n:nat) (t: AB A n), (length A (camino A n t)) = n.
Proof.
  intros A n t.
  induction t.
  - simpl; reflexivity.
  - simpl.
    case_eq (Nat.leb h2 h1).
    (* h2 <= h1 *)
      rewrite (Nat.leb_le h2 h1).
      intro H1.
      simpl.
      rewrite IHt1.
      rewrite (Nat.max_l h1 h2).
      reflexivity.
      exact H1.
    (* h1 <= h2 *)
      rewrite (leb_iff_conv h1 h2).
      intro H1.
      simpl.
      rewrite IHt2.
      rewrite (Nat.max_r h1 h2).
      reflexivity.
      lia.
Qed.
End Ejercicio21.


















