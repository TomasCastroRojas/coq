Require Import Coq.extraction.ExtrHaskellBasic.
Require Import FunInd.

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
Inductive bintree (A:Set):Set :=
  | empty: bintree A
  | node : A -> bintree A -> bintree A -> bintree A.
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