(* ENTREGA Practica 1 *)
(* Tomas Castro Rojas *)

Section P1.
Variables A B C:Prop.

(* Ej 4.1 *)
Theorem e41: A -> ~~A.
Proof.
  intro a.
  unfold not.
  intro f.
  apply f.
  exact a.
Qed.

(* Ej 4.2 *)
Theorem e42: A -> B -> (A /\ B).
Proof.
  intros a b.
  split.
  exact a.
  exact b.
Qed.

(* Ej 4.3 *)
Theorem e43: (A->B->C) -> (A/\B->C).
Proof.
  intro f.
  intro ab.
  elim ab.
  exact f.
Qed.

(* Ej 4.4 *)
Theorem e44: A->(A\/B).
Proof.
  intro a.
  left.
  exact a.
Qed.

(* Ej 4.5 *)
Theorem e45: B->(A\/B).
Proof.
  intro b.
  right.
  exact b.
Qed.

(* Ej 4.6 *)
Theorem e46: (A \/ B) -> (B \/ A).
Proof.
  intro ab.
  elim ab.
  intro a.
  right.
  assumption.
  intro b.
  left.
  assumption.
Qed.

(* Ej 4.7 *)
Theorem e47: (A->C)->(B->C)->A\/B->C.
Proof.
  intro f.
  intro g.
  intro ab.
  elim ab.
  exact f.
  exact g.
Qed.

(* Ej 4.8 *)
Theorem e48: False->A.
Proof.
  intro false.
  elim false.
Qed.

(* Ej 5.1 *)
Theorem e51: (A->B)-> ~B-> ~A.
Proof.
  intro f.
  unfold not.
  intro g.
  intro a.
  absurd B.
  assumption.
  apply f.
  assumption.
Qed.

(* Ej 5.2 *)
Theorem e52: ~(A/\~A).
Proof.
  intro H.
  apply H.
  elim H.
  intro a.
  intro aa.
  assumption.
Qed.

(* Ej 5.3 *)
Theorem e53: (A->B)-> ~(A/\~B).
Proof.
  intro f.
  intro g.
  apply g.
  apply f.
  elim g.
  intro a.
  intro nb.
  assumption.
Qed.

(* Ej 5.4 *)
Theorem e54: (A/\B)->~(A->~B).
Proof.
  intro ab.
  intro f.
  elim f.
  elim ab.
  intro a.
  intro b.
  assumption.
  elim ab.
  intro a.
  intro b.
  assumption.
Qed.

(* Ej 5.5 *)
Theorem e55: (~A /\ ~~A) -> False.
Proof.
  intro H.
  absurd A.
  elim H.
  intro na.
  intro nna.
  assumption.
  elim H.
  intro na.
  unfold not in na.
  intro nna.
  unfold not in nna.
  elim nna.
  assumption.
Qed.

(* Ej 6.1 *)
Theorem e61: (A\/B) -> ~(~A/\~B).
Proof.
  intro ab.
  unfold not.
  intro and.
  apply and.
  elim ab.
  elim and.
  intro af.
  intro bf.
  intro a.
  elim af.
  assumption.
  intro b.
  assumption.
Qed.

(* Ej 6.2 *)
Theorem e62: A\/B <-> B\/A.
Proof.
  unfold iff.
  split.
  (* => *)
  intro ab.
  elim ab.
  intro a.
  right.
  assumption.
  intro b.
  left.
  assumption.
  (* <= *)
  intro ba.
  elim ba.
  intro b.
  right.
  assumption.
  intro a.
  left.
  assumption.
Qed.

(* Ej 6.3 *)
Theorem e63: A\/B -> ((A->B)->B).
Proof.
  intro ab.
  intro f.
  elim ab.
  assumption.
  intro b.
  assumption.
Qed.

End P1.


Section Logica_Clasica.
Variables A B C: Prop.

Require Import Classical.
Check classic.

(* Ej 8.1 *)
Theorem e81: forall A:Prop, ~~A->A.
Proof.
  intro.
  intro nna0.
  elim (classic A0).
  intro a0.
  assumption.
  intro na0.
  elim nna0.
  assumption.
Qed.

(* Ej 8.2 *)
Theorem e82: forall A B:Prop, (A->B)\/(B ->A).
Proof.
  intro.
  intro.
  elim (classic A0).
(* Caso A *)
  intro a0.
  right.
  intro b0.
  assumption.
(* Caso ~A *)
  intro na0.
  left.
  intro a0.
  elim na0.
  assumption.
Qed.

(* Ej 8.3 *)
Theorem e83: forall A B:Prop, ~(A/\B)-> ~A \/ ~B.
Proof.
  intros.
  elim (classic A0).
  intro a0.
  right.
  unfold not.
  intro b0.
  apply H.
  split.
  assumption.
  assumption.
  intro na0.
  left.
  assumption. 
Qed.

End Logica_Clasica.


Section Traducciones.

(* Ej 9 *)
(* Definiciones *)
Variable NM RED CONS UTIL : Prop.

Hypothesis H1 : NM \/ ~RED.
Hypothesis H2 : CONS \/ ~UTIL.

Theorem ej9 : ~NM /\ UTIL -> CONS /\ ~RED.
Proof.
  intro H3.
  split.
(* CONS *)
  elim H3.
  intro N.
  intro U.
  elim H2.
  (* CONS *)
    intro c.
    assumption.
  (* ~UTIL *)
    intro NU.
    elim NU.
    assumption.
(* ~RED *)
  elim H3.
  intro N.
  intro U.
  elim H1.
  (* NM *)
    intro N2.
    elim N.
    assumption.
  (* ~RED *)
    intro NRED.
    assumption.
Qed.
(* Ej 12 *)
(* Definiciones *)
Variable PF:Prop. (* el paciente tiene fiebre *)
Variable PA:Prop. (* el paciente tiene piel amarillenta *)
Variable PH:Prop. (* el paciente tiene hepatitis *)
Variable PR:Prop. (* el paciente tiene rubeola *)

Hypothesis Regla1: (PF \/ PA) -> (PH \/ PR).
Hypothesis Regla2: ~ PR \/ PF.
Hypothesis Regla3: (PH /\ ~PR) -> PA.


Theorem ej12: (~PA /\ PF) -> (PH \/ PR).
Proof.
  intro HH.
  apply Regla1.
  left.
  elim HH.
  intro a.
  intro b.
  assumption.
Qed.

End Traducciones.

