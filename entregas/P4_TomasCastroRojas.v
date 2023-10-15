Section Ejercicio1.

(* 1.1 *)
Inductive list (A:Set):Set := 
  | nil : list A
  | cons : A -> list A -> list A.

Inductive bintree (A:Set):Set :=
  | empty: bintree A
  | node : A -> bintree A -> bintree A -> bintree A.
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
    (* h1 <= h2 *)
      rewrite (Nat.leb_le h2 h1).
      intro H1.
      simpl.
      rewrite IHt1.
      rewrite (Nat.max_l h1 h2).
      reflexivity.
      exact H1.
    (* h2 <= h1 *)
      rewrite (leb_iff_conv h1 h2).
      intro H1.
      simpl.
      rewrite IHt2.
      rewrite (Nat.max_r h1 h2).
      reflexivity.
      lia.
Qed.
End Ejercicio21.


















