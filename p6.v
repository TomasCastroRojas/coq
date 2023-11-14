Require Import Coq.extraction.ExtrHaskellBasic.
Require Import FunInd.

(* 1.1 *)
Lemma predspec : forall n : nat, {m : nat | n = 0 /\ m = 0 \/ n = S m}.
Proof.
  destruct n.
  - exists 0.
    left.
    split; reflexivity.
  - exists n.
    right; reflexivity.
Qed.

(* 1.2 *)
Extraction Language Haskell.

Extraction "predecesor" predspec.

(* 2.1 *)
Inductive bintree (A:Set):Set :=
  | empty: bintree A
  | node : A -> bintree A -> bintree A -> bintree A.

Inductive mirror (A:Set) : bintree A -> bintree A -> Prop :=
  | mirror_empty : mirror A (empty A) (empty A)
  | mirror_node : forall (a:A) (l1 r1 l2 r2:bintree A), 
                    mirror A l1 r2 -> mirror A r1 l2 ->
                    mirror A (node A a l1 r1) (node A a l2 r2).

Fixpoint inverse (A:Set) (t: bintree A): bintree A :=
  match t with
      empty _      => empty _
    | node _ a l r => node _ a (inverse _ r) (inverse _ l)
  end.
  
(* 2.1 *)
Lemma MirrorC: forall (A:Set) (t:bintree A),
{t':bintree A|(mirror A t t')}.
Proof.
  intros.
  induction t.
  - exists (empty A).
    constructor.
  - elim IHt1.
    intros t1' H1.
    elim IHt2.
    intros t2' H2. 
    exists (node A a t2' t1').
    constructor; assumption.
Qed.

(* 2.2 *)
Functional Scheme inverse_ind := Induction for inverse Sort Prop.
#[local] Hint Constructors mirror : core.
Lemma MirrorCInverse: forall (A:Set) (t:bintree A),
{t':bintree A|(mirror A t t')}.
Proof.
  intros.
  exists (inverse A t).
  functional induction inverse A t; auto.
Qed.

(* 2.3 *)
Extraction "mirror_function" MirrorC.
Extraction "mirror_inverse_function" MirrorCInverse.

(* 3.1 *)
Definition Value := bool.
Inductive BoolExpr : Set :=
| bbool : bool -> BoolExpr
| band : BoolExpr -> BoolExpr -> BoolExpr
| bnot : BoolExpr -> BoolExpr.
Inductive BEval : BoolExpr -> Value -> Prop :=
| ebool : forall b : bool, BEval (bbool b) (b:Value)
| eandl : forall e1 e2 : BoolExpr, BEval e1 false -> BEval (band e1 e2) false
| eandr : forall e1 e2 : BoolExpr, BEval e2 false -> BEval (band e1 e2) false
| eandrl : forall e1 e2 : BoolExpr,
  BEval e1 true -> BEval e2 true -> BEval (band e1 e2) true
| enott : forall e : BoolExpr, BEval e true -> BEval (bnot e) false
| enotf : forall e : BoolExpr, BEval e false -> BEval (bnot e) true.


Fixpoint beval1 (e : BoolExpr) : Value :=
  match e with
    | bbool b => b
    | band e1 e2 => match beval1 e1, beval1 e2 with
                      | true, true => true
                      | _, _ => false
                    end
    | bnot e1 => if beval1 e1 then false else true
  end.
Fixpoint beval2 (e : BoolExpr) : Value :=
  match e with
    | bbool b => b
    | band e1 e2 => match beval2 e1 with
                      | false => false
                      | _ => beval2 e2
                    end
    | bnot e1 => if beval2 e1 then false else true
  end.

Lemma beval_correct_value: forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
  intro.
  exists (beval1 e).
  induction e; simpl.
  - case b; constructor.
  - case_eq (beval1 e1).
    -- case_eq (beval1 e2); intros.
       --- rewrite H0 in IHe1.
           rewrite H in IHe2.
           constructor; assumption.
       --- rewrite H in IHe2.
           apply (eandr e1 e2); assumption.
    -- intro.
       rewrite H in IHe1.
       apply (eandl e1 e2); assumption.
  - case_eq (beval1 e); intro; rewrite H in IHe; constructor; assumption.
Qed.

Lemma beval_correct_lazy: forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
  intro.
  exists (beval2 e).
  induction e; simpl.
  - case b; constructor.
  - case_eq (beval2 e1).
    -- case_eq (beval2 e2); intros.
       --- rewrite H0 in IHe1.
           rewrite H in IHe2.
           constructor; assumption.
       --- rewrite H in IHe2.
           apply (eandr e1 e2); assumption.
    -- intro.
       rewrite H in IHe1.
       apply (eandl e1 e2); assumption.
  - case_eq (beval2 e); intro; rewrite H in IHe; constructor; assumption.
Qed.

Functional Scheme beval1_ind := Induction for beval1 Sort Prop.
#[local] Hint Constructors BEval : core.
Lemma beval_correct_value2: forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
  intro.
  exists (beval1 e).
  functional induction (beval1 e); auto;
  try rewrite e3 in IHv; try rewrite e4 in IHv0; try rewrite e2 in IHv;
  constructor; assumption.
Qed.

Functional Scheme beval2_ind := Induction for beval2 Sort Prop.
Lemma beval_correct_lazy2: forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
  intro.
  exists (beval2 e).
  functional induction (beval2 e); auto;
  try rewrite e3 in IHv; try rewrite e4 in IHv0; try rewrite e2 in IHv;
  try constructor; try assumption.
  - case_eq (beval2 e2); intro; rewrite H in IHv0.
    -- constructor; assumption.
    -- apply (eandr e1 e2); assumption.
Qed.

(* 3.3 *)
Extraction "beval1_correct1" beval_correct_value.
Extraction "beval1_correct2" beval_correct_value2.
Extraction "beval2_correct1" beval_correct_lazy.
Extraction "beval2_correct2" beval_correct_lazy2.

(* 3.4 *)
Extract Inductive bool => "Prelude:Bool" ["true" "false"].
Extraction "beval1_correct1" beval_correct_value.
    
Section list_perm.
Variable A:Set.
Inductive list : Set :=
  | nil : list
  | cons : A -> list -> list.
Fixpoint append (l1 l2 : list) {struct l1} : list :=
  match l1 with
    | nil => l2
    | cons a l => cons a (append l l2)
  end.
Inductive perm : list -> list ->Prop:=
  |perm_refl: forall l, perm l l
  |perm_cons: forall a l0 l1, perm l0 l1-> perm (cons a l0)(cons a l1)
  |perm_app: forall a l, perm (cons a l) (append l (cons a nil))
  |perm_trans: forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.

#[local]Hint Constructors perm : core. 

(* 4.1 *)
Fixpoint reverse (l1:list) :list :=
  match l1 with
      nil         => nil
    | cons a rest => (append (reverse rest) (cons a nil))
  end.

(* 4.2 *)
Lemma Ej6_4: forall l: list, {l2: list | perm l l2}.
Proof.
  intro l.
  exists (reverse l).
  induction l; simpl.
  - constructor.
  - apply (perm_trans (cons a l) (cons a (reverse l)) (append (reverse l) (cons a nil))).
    -- apply (perm_cons a l (reverse l)).
       exact IHl.
    -- apply (perm_app a (reverse l)).
Qed.

End list_perm.

(* 5.1 *)
Inductive Le: nat -> nat -> Prop :=
  | Le0: forall n:nat, Le 0 n
  | LeS: forall n m:nat, Le n m -> Le (S n) (S m).

Inductive Gt: nat -> nat -> Prop :=
  | Gt0: forall n:nat, Gt (S n) 0
  | GtS: forall n m:nat, Gt n m -> Gt (S n) (S m).

(* 5.2 *)

Fixpoint leBool (n m: nat):bool :=
  match n, m with
      0 , _         => true
    | _ , 0         => false
    | (S a) , (S b) => leBool a b
  end.

Functional Scheme leBool_rec := Induction for leBool Sort Set.
Lemma Le_Gt_dec: forall n m:nat, {(Le n m)}+{(Gt n m)}.
Proof.
  intros.
  functional induction (leBool n m).
  - left.
    constructor.
  - right.
    constructor.
  - elim IHb; intro H; [ left | right]; constructor; exact H.
Qed.

(* 5.3 *)
Require Import Lia.

Lemma le_gt_dec: forall n m:nat, {(le n m)}+{(gt n m)}.
Proof.
  intros.
  functional induction (leBool n m).
  - left; lia.
  - right; lia.
  - elim IHb; intro H; [left | right ]; lia.
Qed.

(* 6 *)
Require Import DecBool.
Require Import Compare_dec.
Require Import Plus.
Require Import Mult.
Definition spec_res_nat_div_mod (a b:nat) (qr:nat*nat) :=
 match qr with
 (q,r) => (a = b*q + r) /\ r < b
 end.
Definition nat_div_mod :
 forall a b:nat, not(b=0) -> {qr:nat*nat | spec_res_nat_div_mod a b qr}.  
Proof.
  intros a b b_neq_0.
  unfold spec_res_nat_div_mod.
  induction a.
  - exists (0, 0).
    lia.
  - elim IHa.
    intros x H.
    destruct x as [q' r'].
    elim (lt_dec r' (b - 1)); intro H'.
    -- exists (q', S r').
       lia.
    -- exists (S q',  0).
       lia.
Qed.

(* 7 *)
Inductive bintree_sub (A:Set) (t:bintree A) : bintree A -> Prop :=
 | tree_sub1 : forall (t':bintree A) (x:A), bintree_sub A t (node A x t t')
 | tree_sub2 : forall (t':bintree A) (x:A), bintree_sub A t (node A x t' t).


Theorem well_founded_tree_sub : forall A:Set, well_founded (bintree_sub A).
Proof.
  intro A.
  unfold well_founded.
  intro t.
  induction t.
  - constructor.
    intros t' H.
    inversion H.
  - constructor.
    intros t' H.
    inversion H.
    exact IHt1.
    exact IHt2.
Qed.

(* 8.1 *)
Fixpoint size (e: BoolExpr): nat :=
  match e with
    | bbool b => 1
    | band e1 e2 => (size e1) + (size e2)
    | bnot e' => (size e') + 1
  end.

Definition elt (e1 e2 : BoolExpr) := size e1 < size e2.
Require Import Wf_nat.
Require Import Inverse_Image.

Lemma well_founded_elt: well_founded elt.
Proof.
  apply well_founded_ltof.
Qed.

(* 9 *)
Section Ejercicio9.
Inductive listGen (A:Set):Set := 
  | nilGen : listGen A
  | consGen : A -> listGen A -> listGen A.

Fixpoint appendGen (A:Set) (l1 l2 : listGen A) {struct l1} : listGen A:=
  match l1 with
    | nilGen _ => l2
    | consGen _ a l => consGen _ a (appendGen _ l l2)
  end.
Inductive sorted (A:Set) (R: A -> A -> Prop): listGen A -> Prop :=
  | sorted_nil : sorted A R (nilGen A)
  | sorted_singleton : forall (a:A), sorted A R (consGen A a (nilGen A))
  | sorted_cons : forall (a b: A) l,
                  R a b -> sorted A R (consGen A b l) ->
                  sorted A R (consGen A a (consGen A b l)).
                  
Inductive permGen (A:Set): listGen A -> listGen A -> Prop:=
  |permGen_refl: forall l, permGen A l l
  |permGen_cons: forall a l0 l1, permGen A l0 l1 -> permGen _ (consGen _ a l0) (consGen _ a l1)
  |p_ccons: forall a b l, (permGen A (consGen _ a (consGen _ b l)) (consGen _ b (consGen _ a l)))
  |permGen_trans: forall l1 l2 l3, permGen A l1 l2 -> permGen _ l2 l3 -> permGen _ l1 l3.

Fixpoint insert_sortedGen (A:Set) (elem:A) (l:listGen A) (le: A -> A -> bool): listGen A :=
  match l with
      nilGen _ => consGen _ elem (nilGen _)
    | consGen _ h rest => if (le elem h) then (consGen _ elem (consGen _ h rest))
                                      else (consGen _ h (insert_sortedGen _ elem rest le))
  end.

Fixpoint insert_sortGen (A:Set) (l: listGen A) (le: A -> A -> bool): listGen A :=
  match l with
      nilGen _ => nilGen _
    | consGen _ h rest => (insert_sortedGen _ h (insert_sortGen _ rest le) le)
  end.

Lemma SORT: forall l:(listGen nat), {l':(listGen nat) | (sorted nat le l') /\ (permGen nat l l')}.
Proof.
  induction l.
  - exists (nilGen nat).
    split; constructor.
  - exists (insert_sortGen nat (consGen nat a l) leBool).
    split;simpl.
    
Qed.
End Ejercicio9.













