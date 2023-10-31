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

(* 5.3.a *)
Lemma Lmem: forall (mem:Memoria), ~ BEval (BEBool true) mem false.
Proof.
  intro.
  intro.
  inversion H.
Qed.

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

Lemma unicidad: forall (mem: Memoria) (e: BoolExpr)  (w1 w2: Valor),
                  BEval e mem w1 -> BEval e mem w2 -> w1 = w2.
Proof.
  intros; induction e.
  - inversion H.
    inversion H0.
    reflexivity.
  - inversion H; inversion H0.
    -- reflexivity.
    -- rewrite <- H5 in H2.
       discriminate.
    -- rewrite <- H5 in H2.
       discriminate.
    -- reflexivity.
  - inversion_clear H in IHe1 IHe2; inversion_clear H0 in IHe1 IHe2; auto.
  - inversion H in IHe; inversion H0 in IHe; auto.
Qed.

Lemma correctitud: forall (mem:Memoria) (e1 e2: BoolExpr), BEval e1 mem false -> BEval (BENeg (BEAnd e1 e2)) mem true.
Proof.
  intro mem; induction e1; intros.
  - apply (Enotf (BEAnd (BEVar v) e2) mem).
    apply (Eandl (BEVar v) e2 mem).
    exact H.
  - apply (Enotf (BEAnd (BEBool b) e2) mem).
    apply (Eandl (BEBool b) e2 mem).
    exact H.
  - apply (Enotf (BEAnd (BEAnd e1_1 e1_2) e2) mem).
    apply (Eandl (BEAnd e1_1 e1_2) e2 mem).
    exact H.
  - apply (Enotf (BEAnd (BENeg e1) e2) mem).
    apply (Eandl (BENeg e1) e2 mem).
    exact H.
Qed.

(* 5.4 *)
Fixpoint beval (mem:Memoria) (e:BoolExpr): Valor :=
  match e with
    | BEVar v => lookup mem v
    | BEBool b => b
    | BEAnd e1 e2 => match beval mem e1 with
                      | false => false
                      | true => beval mem e2
                     end
    | BENeg e0 => match beval mem e0 with
                    | false => true
                    | true => false
                  end
  end.
  
(* 5.5 *)
Theorem bigstep_equal_smallstep: forall (mem: Memoria) (e: BoolExpr), BEval e mem (beval mem e).
Proof.
  intros.
  induction e.
  - simpl.
    constructor.
  - simpl.
    case b; constructor.
  - simpl.
    case_eq (beval mem e1); case_eq (beval mem e2).
    -- intros.
       constructor.
       rewrite H0 in IHe1.
       exact IHe1.
       rewrite H in IHe2.
       exact IHe2.
    -- intros.
       apply (Eandr e1 e2 mem).
       rewrite H in IHe2.
       exact IHe2.
    -- intros.
       constructor.
       rewrite H0 in IHe1.
       exact IHe1.
    -- intros.
       constructor.
       rewrite H0 in IHe1.
       exact IHe1.
  - simpl.
    case_eq (beval mem e); intro H; constructor; rewrite H in IHe; exact IHe.
Qed.
End Ejercicio5.


Section Ejercicio6.

(* 6.1 *)
Inductive Instr :=
  | Skip: Instr
  | Assign: Var -> BoolExpr -> Instr
  | IfThenElse: BoolExpr -> Instr -> Instr -> Instr
  | WhileDo: BoolExpr -> Instr -> Instr
  | Repeat: nat -> Instr -> Instr
  | BeginEnd: LInstr -> Instr
  with
  LInstr :=
    | nillLI: LInstr
    | consLI : Instr -> LInstr -> LInstr.

(* 6.2 *)
Infix "::" := consLI (at level 60, right associativity).

(* 6.2.a *)
Variables v1 v2: Var.
Definition PP := BeginEnd ((Assign v1 (BEBool true))::(Assign v2 (BENeg (BEVar v1)))::nillLI).

(* 6.2.b *)
Variables v3 v4 aux: Var.
Definition Swap := BeginEnd ((Assign aux (BEVar v1))::(Assign v1 (BEVar v2)):: (Assign v2 (BEVar aux))::nillLI).

(* 6.3 *)
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.

Definition update (mem: Memoria) (v:Var) (w: Valor) :=
  fun (x: Var) => if Nat.eqb v x 
                  then w
                  else mem x.

(* 6.4 *)
Lemma lookup_update1: forall (mem:Memoria) (var: Var) (val:Valor), lookup (update mem var val) var = val.
Proof.
  intros.
  unfold lookup.
  unfold update.
  rewrite (Nat.eqb_refl var).
  reflexivity.
Qed.

(* 6.5 *)
Lemma lookup_update2: forall (mem: Memoria) (var var':Var) (val:Valor), var <> var' -> lookup (update mem var val) var' = lookup mem var'.
Proof.
  intros.
  unfold lookup.
  unfold update.
  apply (Nat.eqb_neq var var') in H.
  rewrite H.
  reflexivity.
Qed.
End Ejercicio6.

Section Ejercicio7.
Infix "::" := consLI (at level 60, right associativity).
(* 7.1 *)
Inductive Execute: Instr -> Memoria -> Memoria -> Prop :=
  | xSkip: forall (mem:Memoria), Execute Skip mem mem
  | xAss: forall (mem:Memoria) (e:BoolExpr) (v:Var) (w:Valor),
             BEval e mem w -> Execute (Assign v e) mem (update mem v w)
  | xIfThen: forall (mem mem1:Memoria) (cond: BoolExpr) (p1 p2: Instr),
               BEval cond mem true -> Execute p1 mem mem1 -> Execute (IfThenElse cond p1 p2) mem mem1
  | xIfElse: forall (mem mem2:Memoria) (cond: BoolExpr) (p1 p2: Instr),
               BEval cond mem false -> Execute p2 mem mem2 -> Execute (IfThenElse cond p1 p2) mem mem2
  | xWhileTrue: forall (mem mem1 mem2: Memoria) (cond: BoolExpr) (p: Instr),
                  BEval cond mem true -> Execute p mem mem1 -> Execute (WhileDo cond p) mem1 mem2 -> Execute (WhileDo cond p) mem mem2
  | xWhileFalse: forall (mem: Memoria) (cond: BoolExpr) (p: Instr),
                  BEval cond mem false -> Execute (WhileDo cond p) mem mem
  | xRepeatO: forall (mem: Memoria) (p: Instr), Execute (Repeat 0 p) mem mem
  | xRepeatS: forall (mem1 mem2 mem3: Memoria) (p:Instr) (n: nat), 
                  Execute p mem1 mem2 -> Execute (Repeat n p) mem2 mem3 -> Execute (Repeat (S n) p) mem1 mem3
  | xBeginEnd: forall (mem mem1: Memoria) (prog: LInstr), ExecuteL prog mem mem1 -> Execute (BeginEnd prog) mem mem1
  with
    ExecuteL: LInstr -> Memoria -> Memoria -> Prop :=
      | xEmptyBlock: forall (mem: Memoria), ExecuteL nillLI mem mem
      | xNext: forall (mem mem1 mem2: Memoria) (instr: Instr) (li: LInstr),
                  Execute instr mem mem1 -> ExecuteL li mem1 mem2 -> ExecuteL (instr::li) mem mem2.

(* 7.2 *)
Lemma LExecute1: forall (c: BoolExpr) (p1 p2: Instr) (mem mem': Memoria), Execute (IfThenElse (BENeg c) p1 p2) mem mem' -> Execute (IfThenElse c p2 p1) mem mem'.
Proof.
  intros.
  inversion_clear H; inversion_clear H0; [apply xIfElse | apply xIfThen]; assumption.
Qed.

(* 7.3 *)
Lemma LExecute2: forall (p: Instr) (mem mem': Memoria), Execute (WhileDo (BEBool false) p) mem mem' -> mem = mem'.
Proof.
  intros.
  inversion H.
  inversion H2.
  reflexivity.
Qed.

(* 7.4 *)
Lemma LExecute3: forall (c: BoolExpr) (p: Instr) (mem mem': Memoria),
                  Execute (BeginEnd ((IfThenElse c p Skip)::(WhileDo c p)::nillLI)) mem mem' -> Execute (WhileDo c p) mem mem'.
Proof.
  intros.
  inversion H.
  inversion H1.
  inversion H9.
  inversion H6.
  - apply (xWhileTrue mem mem3 mem').
    -- exact H21.
    -- exact H22.
    -- inversion H15 in H12.
       exact H12.
  - inversion H22.
    inversion H15 in H12.
    exact H12.
Qed.

(* 7.5 *)
Lemma LExecute4: forall (n:nat) (i:Instr) (mem1 mem2:Memoria),
                    Execute (BeginEnd (i::(Repeat n i)::nillLI)) mem1 mem2 -> Execute (Repeat (S n) i) mem1 mem2.
Proof.
  intros.
  inversion H.
  inversion H1.
  inversion H9.
  inversion H15 in H12.
  apply (xRepeatS mem1 mem4 mem2 i n H6 H12).
Qed.

(* 7.6 *)
Lemma LExecute5: forall (n1 n2: nat) (i: Instr) (mem1 mem2 mem3: Memoria) ,
                   Execute (Repeat n1 i) mem1 mem2 -> Execute (Repeat n2 i) mem2 mem3 -> Execute (Repeat (n1+n2) i) mem1 mem3.
Proof.
  induction n1; intros; simpl.
  - inversion_clear H in H0.
    exact H0.
  - inversion_clear H.
    apply (xRepeatS mem1 mem4 mem3 i (n1 + n2)).
    exact H1.
    apply (IHn1 n2 i mem4 mem2 mem3 H2 H0).
Qed.

(* 7.7 *)
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.

Variables v1 v2: Var.
Lemma LExecute6: forall (mem mem': Memoria), v1 <> v2 -> Execute (PP v1 v2) mem mem' -> lookup mem' v2 = false /\ lookup mem' v1 = true.
Proof.
  intros.
  unfold PP in H0.
  inversion_clear H0.
  inversion_clear H1.
  inversion_clear H2.
  inversion_clear H3 in H1.
  inversion H0.
  inversion H6 in H5.
  rewrite <- H5 in H1.
  inversion H1.
  inversion H13; split.
  - rewrite (lookup_update1 (update mem v1 true) v2).
    reflexivity.
  - rewrite (lookup_update2 (update mem v1 true) v2 v1).
    rewrite (lookup_update1 mem v1 true).
    reflexivity.
    apply (Nat.neq_sym v1 v2); exact H.
  - rewrite (lookup_update1 (update mem v1 true) v2).
    inversion H15.
    rewrite (lookup_update1 mem v1 true).
    reflexivity.
  - rewrite (lookup_update2 (update mem v1 true) v2 v1).
    rewrite (lookup_update1 mem v1 true).
    reflexivity.
    apply (Nat.neq_sym v1 v2); exact H.
Qed.
End Ejercicio7.