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
Hint Constructors mirror : core.
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
Hint Constructors BEval : core.
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









