Inductive list (A:Set):Set := 
  | nil : list A
  | cons : A -> list A -> list A.

Inductive bintree (A:Set):Set :=
  | empty: bintree A
  | node : A -> bintree A -> bintree A -> bintree A.

Inductive isomorfo (A:Set): bintree A -> bintree A -> Prop :=
  | isomorfo_empty : isomorfo A (empty A) (empty A)
  | isomorfo_node : forall (a b:A) (l1 r1 l2 r2:bintree A),
                      isomorfo A l1 l2 -> isomorfo A r1 r2 ->
                      isomorfo A (node A a l1 r1) (node A b l2 r2).

Inductive mirror (A:Set) : bintree A -> bintree A -> Prop :=
  | mirror_empty : mirror A (empty A) (empty A)
  | mirror_node : forall (a:A) (l1 r1 l2 r2:bintree A), 
                    mirror A l1 r2 -> mirror A r1 l2 ->
                    mirror A (node A a l1 r1) (node A a l2 r2). 

Fixpoint append (A:Set) (l1 l2:list A) {struct l1}:list A :=
  match l1 with
      nil _         => l2
    | cons _ a rest => cons _ a (append _ rest l2)
  end.

Fixpoint inverse (A:Set) (t: bintree A): bintree A :=
  match t with
      empty _      => empty _
    | node _ a l r => node _ a (inverse _ r) (inverse _ l)
  end.
Section Ejercicio1.
Inductive LE : nat -> nat -> Prop :=
 | Le_O : forall n : nat, LE 0 n
 | Le_S : forall n m : nat, LE n m -> LE (S n) (S m).

Inductive Mem (A : Set) (a : A) : list A -> Prop :=
 | here : forall x : list A, Mem A a (cons A a x)
 | there : forall x : list A, Mem A a x ->
              forall b : A, Mem A a (cons A b x).
              
(* 1.1 *)
Theorem not_sn_le_o: forall n:nat, ~ LE (S n) O.
Proof.
  intro n.
  unfold not; intro H.
  inversion H.
Qed.

(* 1.2 *)
Theorem nil_empty: forall (A:Set) (a:A), ~ Mem A a (nil A).
Proof.
  intros A a.
  unfold not; intro H.
  inversion H.
Qed.

(* 1.3 *)
Theorem not4lt3: ~ (LE 4 3).
Proof.
  unfold not; intro H.
  inversion_clear H.
  inversion_clear H0.
  inversion_clear H.
  apply (not_sn_le_o 0).
  exact H0.
Qed.

(* 1.4 *)
Theorem not_sn_le_n: forall n:nat, ~ LE (S n) n.
Proof.
  induction n; unfold not.
  apply (not_sn_le_o 0).
  intro H.
  inversion_clear H.
  apply IHn.
  exact H0.
Qed.

(* 1.5 *)
Theorem le_transitive: forall n m p:nat, (LE n m) -> (LE m p) -> LE n p.
Proof.
  induction n.
  - intros m p H1 H2.
    constructor.
  - intros.
    destruct m; destruct p.
    -- inversion H.
    -- inversion H.
    -- inversion H0.
    -- constructor.
       inversion_clear H.
       inversion_clear H0.
       apply (IHn m p).
       exact H1.
       exact H.
Qed.

(* 1.6 *)
Theorem mel_append: forall (A:Set) (a:A) (l1 l2:list A), Mem A a l1 -> Mem A a (append A l1 l2).
Proof.
  intros A a l1 l2.
  induction l1.
  - intro H.
    inversion H.
  - intro H.
    inversion_clear H.
    constructor.
    simpl.
    constructor.
    apply IHl1.
    exact H0.
Qed.
End Ejercicio1.

Section Ejercicio2.

(* 2.1 *)
Theorem not_iso_emptyBin1: forall (A:Set) (a:A) (l r: bintree A), ~(isomorfo A (empty A) (node A a l r)).
Proof.
  intros A a l r.
  unfold not; intro H.
  inversion H.
Qed.

Theorem not_iso_emptyBin12: forall (A:Set) (a:A) (l r: bintree A), ~(isomorfo A (node A a l r) (empty A)).
Proof.
  intros A a l r.
  unfold not; intro H.
  inversion H.
Qed.

(* 2.2 *)
Theorem iso_nodes: forall (A:Set) (a1 a2:A) (l1 r1 l2 r2: bintree A), 
                      (isomorfo A (node A a1 l1 r1) (node A a2 l2 r2)) -> (isomorfo A l1 l2) /\ (isomorfo A r1 r2).
Proof.
  intros.
  inversion_clear H.
  split.
  exact H0.
  exact H1.
Qed.

(* 2.3 *)
Theorem iso_transitive: forall (A:Set) (t1 t2 t3: bintree A), 
                            (isomorfo _ t1 t2) -> (isomorfo _ t2 t3) -> (isomorfo _ t1 t3).
Proof.
  intro A.
  induction t1.
  - intros.
    inversion H.
    rewrite <- H2 in H0.
    assumption.
  - intros.
    inversion H.
    rewrite <- H3 in H0; rewrite <- H3 in H.
    inversion_clear H0; inversion_clear H.
    constructor.
    apply (IHt1_1 l2 l3); assumption.
    apply (IHt1_2 r2 r3); assumption.
Qed.

(* 2.4 *)
Theorem iso_mirror: forall (A:Set) (t1 t2: bintree A), isomorfo A t1 t2 -> isomorfo A (inverse A t1) (inverse A t2).
Proof.
  intro A.
  induction t1.
  - intros.
    inversion H.
    rewrite <- H1 in H.
    simpl.
    exact H.
  - intros.
    inversion H.
    simpl.
    constructor.
    apply (IHt1_2 r2); assumption.
    apply (IHt1_1 l2); assumption.
Qed.
End Ejercicio2.


Section Ejercicio3.
Variable A : Set.
Parameter equal : A -> A -> bool.
Axiom equal1 : forall x y : A, equal x y = true -> x = y.
Axiom equal2 : forall x : A, equal x x <> false.
Inductive List : Set :=
 | nullL : List
 | consL : A -> List -> List.
Inductive MemL (a : A) : List -> Prop :=
 | hereL : forall x : List, MemL a (consL a x)
 | thereL : forall x : List, MemL a x -> forall b : A, MemL a (consL b x).

(* 3.1 *)
Inductive isSet : List -> Prop :=
  | emptySet : isSet nullL
  | consSet : forall (a:A) (l:List), isSet l -> ~ (MemL a l) -> isSet (consL a l).
  
(* 3.2 *)
Fixpoint deleteAll (x: A) (l:List) : List :=
  match l with
    | nullL => nullL
    | consL h rest => if equal x h then deleteAll x rest
                                   else consL h (deleteAll x rest)
  end.

(* 3.3 *)
Lemma DeleteAllNotMember : forall (l : List) (x : A), ~ MemL x (deleteAll x l).
Proof.
  intros.
  unfold not.
  induction l.
  - simpl.
    intro H.
    inversion H.
  - simpl.
    case_eq (equal x a).
    -- intro.
       exact IHl.
    -- intros.
       inversion H0.
       rewrite H2 in H.
       apply (equal2 a).
       exact H.
       apply IHl.
       exact H2.
Qed.

(* 3.4 *)
Fixpoint delete (x: A) (l:List) : List :=
  match l with
    | nullL => nullL
    | consL h rest => if equal x h then rest
                                   else consL h (delete x rest)
  end.

(* 3.5 *)
Lemma DeleteNotMember : forall (l : List) (x : A), isSet l -> ~ MemL x (delete x l).
Proof.
  intros.
  induction l; unfold not; simpl.
  - intro H1.
    inversion H1.
  - case_eq (equal x a).
    -- intros EQ H1.
       apply IHl.
       inversion H.
       assumption.
       apply (equal1 x a) in EQ.
       rewrite <- EQ in H.
       inversion H.
       absurd (MemL x l); assumption.
    -- intros NEQ H1.
       inversion H.
       inversion H1.
       rewrite H6 in NEQ.
       apply (equal2 a); assumption.
       apply IHl.
       exact H3.
       exact H6.
Qed.
End Ejercicio3.

Section Ejercicio4.
Variable A : Set.

Inductive AB: Set :=
   nullAB : AB
 | consAB : A -> AB-> AB -> AB.

(* 4.1 *)
Inductive Pertenece (a:A): AB -> Prop :=
  | rootAB : forall (t1 t2: AB), Pertenece a (consAB a t1 t2)
  | treeAB : forall (t1 t2: AB) (b:A), Pertenece a t1 \/ Pertenece a t2 -> Pertenece a (consAB b t1 t2).
  
(* 4.2 *)
Parameter eqGen: A->A->bool.
Fixpoint Borrar (x:A) (t:AB): AB :=
  match t with
    | nullAB       => nullAB
    | consAB a l r => if eqGen x a then nullAB
                                   else consAB a (Borrar x l) (Borrar x r)
  end.

(* 4.3 *)
Axiom eqGen1: forall (x:A), ~(eqGen x x) = false.
Lemma BorrarNoPertenece: forall (x:AB) (a:A), ~(Pertenece a (Borrar a x)).
Proof.
  induction x; intro; simpl; unfold not.
  - intro H.
    inversion H.
  - case_eq (eqGen a0 a).
    -- intros EQ H.
       inversion H.
    -- intros NEQ H.
       inversion H.
       rewrite H1 in NEQ.
       apply (eqGen1 a); assumption.
       elim H1.
       --- apply (IHx1 a0).
       --- apply (IHx2 a0).
Qed.

(* 4.4 *)
Inductive SinRepetidos: AB -> Prop :=
 | emptyAB: SinRepetidos nullAB
 | nodeAB: forall (t1 t2:AB) (a:A), SinRepetidos t1 -> SinRepetidos t2 
                                      -> SinRepetidos (consAB a t1 t2).
End Ejercicio4.

Section Ejercicio5.
(* 5.1 *)
Definition Var := nat.

Inductive BoolExpr:Set :=
  | BEVar: Var -> BoolExpr
  | BEBool: bool -> BoolExpr
  | BEAnd: BoolExpr -> BoolExpr -> BoolExpr
  | BENeg: BoolExpr -> BoolExpr.
  
(* 5.2 *)
Definition Valor := bool.
Definition Memoria := nat -> Valor.
Definition lookup (m:Memoria) (v:Var) := m v.

Inductive BEval : BoolExpr -> Memoria -> Valor -> Prop :=
  | EVar : forall (v:Var) (mem:Memoria), BEval (BEVar v) mem (lookup mem v)
  | Eboolt: forall (mem:Memoria), BEval (BEBool true) mem true
  | Eboolf: forall (mem:Memoria), BEval (BEBool false) mem false
  | Eandl: forall (e1 e2: BoolExpr) (mem:Memoria), BEval e1 mem false -> BEval (BEAnd e1 e2) mem false
  | Eandr: forall (e1 e2: BoolExpr) (mem:Memoria), BEval e2 mem false -> BEval (BEAnd e1 e2) mem false
  | Eandrl: forall (e1 e2: BoolExpr) (mem:Memoria), BEval e1 mem true -> BEval e2 mem true -> BEval (BEAnd e1 e2) mem true
  | Enott: forall (e: BoolExpr) (mem:Memoria), BEval e mem true -> BEval (BENeg e) mem false
  | Enotf: forall (e: BoolExpr) (mem:Memoria), BEval e mem false -> BEval (BENeg e) mem true.

(* 5.3 *)
(* TODO: 5.3.a *)
Lemma LEand1: forall (mem:Memoria) (e1 e2: BoolExpr) (w: Valor),
                 BEval e1 mem true -> BEval e2 mem w -> BEval (BEAnd e1 e2) mem w.
Proof.
  intros.
  case_eq w.
  - intro wtrue.
    rewrite wtrue in H0.
    apply (Eandrl e1 e2 mem); assumption.
  - intro wfalse.
    rewrite wfalse in H0.
    apply (Eandr e1 e2 mem); assumption.
Qed.
End Ejercicio5.
















