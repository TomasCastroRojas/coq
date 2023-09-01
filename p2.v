Section Ejercicio1.


Variable U  : Set.
Variable A B: U -> Prop.
Variable P Q: Prop.
Variable R S: U -> U -> Prop.

Theorem e11 : (forall x:U, A(x)) -> forall y:U, A(y).
Proof.
  intro.
  intro.
  apply H.
Qed.

Theorem e12 : (forall x y:U, (R x y)) -> forall x y:U, (R y x).
Proof.
  intro.
  intros.
  apply H.
Qed.


Theorem e13 : (forall x: U, ((A x)->(B x)))
                        -> (forall y:U, (A y))
                          -> (forall z:U, (B z)).
Proof.
  intro.
  intros.
  apply H.
  apply H0.
Qed.


End Ejercicio1.



Section Ejercicio2.

Variable U  : Set.
Variable A B: U -> Prop.
Variable P Q: Prop.
Variable R S: U -> U -> Prop.


Theorem e21 : (forall x:U, ((A x)-> ~(forall x:U, ~ (A x)))).
Proof.
  intro.
  intro.
  intro.
  unfold not in H0.
  apply H0 with (x := x).
  assumption.
Qed.

Theorem e22 : (forall x y:U, ((R x y)))-> (forall x:U, (R x x)).
Proof.
  intro.
  intro.
  apply H.
Qed.

Theorem e23 : (forall x:U, ((P -> (A x))))
                        -> (P -> (forall x: U, (A x))).
Proof.
  intro.
  intro.
  intro.
  apply H.
  assumption.
Qed.


Theorem e24 : (forall x:U, ((A x) /\ (B x)))
                        -> (forall x:U, (A x))
                          -> (forall x:U, (B x)).
Proof.
  intro.
  intro.
  intro.
  apply H.
Qed.


Theorem e25 : (forall x:U, (A x)) \/ (forall x:U, (B x)) -> 
                      forall x:U, ~(~(A x) /\ ~(B x)).
Proof.
  intros.
  unfold not.
  intro NAyNB.
  elim NAyNB.
  intro NA.
  intro NB.
  elim H.
  (* A x *)
    intro.
    apply NA.
    apply H0.
  (* B x *)
    intro.
    apply NB.
    apply H0.
Qed.


End Ejercicio2.



Section Ejercicio3.

Variable U   : Set.
Variable A B : U -> Prop.
Variable P Q : Prop.
Variable R S : U -> U -> Prop.

Definition H1 := forall x:U, (R x x).
Definition H2 := forall x y z:U, (R x y) /\ (R x z) -> (R y z).

Definition Sym := forall x y: U, (R x y) -> (R y x).
Definition Trans := forall x y z:U, (R x y) /\ (R y z) -> (R x z).

Theorem e231: H1 /\ H2 -> H1 /\ Sym /\ Trans.
Proof.
  intro H1H2.
  split.
  elim H1H2.
  intros; assumption.
  elim H1H2.
  intros H1 H2.
  split.
  (* Simetrica *)
    intro.
    intro.
    intro H.
    apply (H2 x y x).
    split.
    assumption.
    apply (H1 x).
  (* Transitiva *)
    intro xx.
    intro yy.
    intro zz.
    intro Rxy_and_Ryz.
    elim Rxy_and_Ryz.
    intros Rxy Ryz.
    apply (H2 yy xx zz).
    split.
    (* Transitiva de nuevo *)
      apply (H2 xx yy xx).
      split.
      assumption.
      apply (H1 xx).
    assumption.
Qed.

Definition Irreflexiva := forall x:U, ~ (R x x).
Definition Asimetrica := forall x y:U, (R x y) -> ~ (R y x).
 
Lemma e232 : Asimetrica -> Irreflexiva.
Proof.
  unfold Asimetrica.
  intro.
  unfold Irreflexiva.
  intro xx.
  unfold not in *.
  intro Rxx.
  apply (H xx xx).
  assumption.
  assumption.
Qed.

End Ejercicio3.



Section Ejercicio4.

Variable U : Set.
Variable A B : U->Prop.
Variable R : U->U->Prop.

Theorem e41: (exists x:U, exists y:U, (R x y)) -> 
                exists y:U, exists x:U, (R x y).
Proof.
  intro Exy.
  elim Exy.
  intro xx.
  intro Ey.
  elim Ey.
  intro yy.
  intro Rxy.
  exists yy.
  exists xx.
  assumption. 
Qed.

Theorem e42: (forall x:U, A(x)) -> 
                ~ exists x:U, ~ A(x).
Proof.
  intro Ax.
  unfold not.
  intro NotEx.
  elim NotEx.
  intro.
  intro NotAx.
  apply NotAx.
  apply (Ax x).
Qed.

Theorem e43: (exists x:U, ~(A x)) -> 
                ~(forall x:U, (A x)).
Proof.
  intro ExNotA.
  unfold not.
  intro ForXA.
  elim ExNotA.
  intro xx.
  unfold not.
  intro NotA.
  apply NotA.
  apply (ForXA xx).
Qed.

Theorem e44: (forall x:U, ((A x) /\ (B x)))
                -> (forall x:U, (A x)) /\ (forall x:U, (B x)).
Proof.
  intro ForAandB.
  split.
  intro x1.
  apply (ForAandB x1).
  intro x2.
  apply (ForAandB x2).
Qed.

Theorem e45: (exists x:U, (A x \/ B x))->
                (exists x:U, A x) \/ (exists x:U, B x).
Proof.
  intro ExAorB.
  elim ExAorB.
  intro xx.
  intro AorB.
  elim AorB.
  (* A x *)
    intro Ax.
    left.
    exists xx.
    assumption.
  (* B x *)
    intro Bx.
    right.
    exists xx.
    assumption.
Qed.

Theorem e46: (forall x:U, A x) \/ (forall y:U, B y) 
                -> forall z:U, A z \/ B z.
Proof.
  intro ForAllAorForAllB.
  elim ForAllAorForAllB.
  (* ForAll x, A x *)
    intro ForAllA.
    intro zz.
    left.
    apply (ForAllA zz).
  (* ForAll x, B x *)
    intro ForAllB.
    intro zz.
    right.
    apply (ForAllB zz).
Qed.



End Ejercicio4.



Section Ejercicio5.

Variable nat      : Set.
Variable S        : nat -> nat.
Variable a b c    : nat.
Variable odd even : nat -> Prop.
Variable P Q      : nat -> Prop.
Variable f        : nat -> nat.

Theorem e51: forall x:nat, exists y:nat, (P(x)->P(y)).
Proof.
  intro xx.
  exists xx.
  intro Px.
  assumption.
Qed.

Theorem e52: exists x:nat, (P x)
                            -> (forall y:nat, (P y)->(Q y))
                               -> (exists z:nat, (Q z)).
Proof.
  exists a.
  intro Pa.
  intro ForAllPyThenQy.
  exists a.
  apply (ForAllPyThenQy a).
  assumption.
Qed.


Theorem e53: even(a) -> (forall x:nat, (even(x)->odd (S(x)))) -> exists y: nat, odd(y).
Proof.
  intro even_a.
  intro ForAllEvenThenOddSucc.
  exists (S a).
  apply (ForAllEvenThenOddSucc a).
  exact even_a.
Qed.


Theorem e54: (forall x:nat, P(x) /\ odd(x) ->even(f(x)))
                            -> (forall x:nat, even(x)->odd(S(x)))
                            -> even(a)
                            -> P(S(a))
                            -> exists z:nat, even(f(z)).
Proof.
  intro ForAllPx_and_Oddx.
  intro ForAllEvenxThenOddSuccx.
  intro even_a.
  intro P_succ_a.
  exists (S a).
  apply (ForAllPx_and_Oddx (S a)).
  split.
  exact P_succ_a.
  apply (ForAllEvenxThenOddSuccx a).
  exact even_a.
Qed.

End Ejercicio5.



Section Ejercicio6.

Variable nat : Set.
Variable S   : nat -> nat.
Variable le  : nat -> nat -> Prop.
Variable f   : nat -> nat.
Variable P   : nat -> Prop.

Axiom le_n: forall n:nat, (le n n).
Axiom le_S: forall n m:nat, (le n m) -> (le n (S m)).
Axiom monoticity: forall n m:nat, (le n m) -> (le (f n) (f m)).


Lemma le_x_Sx: forall x:nat, (le x (S x)).
Proof.
  intro xx.
  apply (le_S xx).
  apply (le_n xx).
Qed.

Lemma le_x_SSx: forall x:nat, (le x (S (S x))).
Proof.
  intro xx.
  apply (le_S xx).
  apply (le_S xx).
  apply (le_n xx).
Qed.

Theorem T1: forall a:nat, exists b:nat, (le (f a) b).
Proof.
  intro aa.
  exists (f aa).
  apply (le_n (f aa)).
Qed.

End Ejercicio6.



Section Ejercicio7.

Variable U   : Set.
Variable A B : U -> Prop.

Theorem e71: (forall x:U, ((A x) /\ (B x)))
                       -> (forall x:U, (A x)) /\ (forall x:U, (B x)).
Proof.
  intro AandB; split ; [apply AandB | apply AandB].
Qed.

Theorem e72: (exists x:U, (A x \/ B x))->(exists x:U, A x )\/(exists x:U, B x).
Proof.
  intro ExisteAorB; elim ExisteAorB; intros x AorB; elim AorB; intro H; [left | right]; exists x; exact H.
Qed.

Theorem e73: (forall x:U, A x) \/ (forall y:U, B y) -> forall z:U, A z \/ B z.
Proof.
  intro AllAorAllB; elim AllAorAllB; intros H x; [left | right]; apply (H x).
Qed.

End Ejercicio7.


Section Ejercicio8.

Variables U : Set.
Variables T V : U -> Prop.
Variables R : U -> U -> Prop.

Theorem e81: (exists y : U, forall x : U, R x y) -> forall x : U, exists y : U, R x y.
Proof.

Qed.

Theorem e82:
  (exists x:U, True) /\ (forall x:U, (T x) \/ (V x))
    -> (exists z:U, (T z)) \/ (exists w:U, (V w)).
Proof.

Qed.

(* 
Parte 8.3. La proposición (exists x:U, True) ...
*)

End Ejercicio8.




Section Ejercicio9.
Require Import Classical.
Variables U : Set.
Variables A : U -> Prop.

Lemma not_ex_not_forall: (~exists x :U, ~A x) -> (forall x:U, A x).
Proof.
  
Qed.

Lemma not_forall_ex_not: (~forall x :U, A x) -> (exists x:U,  ~A x).
Proof.
  
Qed.

End Ejercicio9.



Section Ejercicio10.

Variable nat : Set.
Variable  O  : nat.
Variable  S  : nat -> nat.

Axiom disc   : forall n:nat, ~O=(S n).
Axiom inj    : forall n m:nat, (S n)=(S m) -> n=m.
Axiom allNat : forall n: Nat, n = O \/ exists m: nat, S m = n.

Variable sum prod : nat->nat->nat.

Axiom sum0   : forall n :nat, (sum n O)=n.
Axiom sumS   : forall n m :nat, (sum n (S m))=(S (sum n m)).
Axiom prod0  : forall n :nat, (prod n O)=O.
Axiom prodS  : forall n m :nat, (prod n (S m))=(sum n (prod n m)).

Lemma L10_1: (sum (S O) (S O)) = (S (S O)).
Proof.
  
Qed.

Lemma L10_2: forall n :nat, ~(O=n /\ (exists m :nat, n = (S m))).
Proof.
  
Qed.

Lemma prod_neutro: forall n :nat, (prod n (S O)) = n.
Proof.
  
Qed.

Lemma diff: forall n:nat, ~(S (S n))=(S O).
Proof.
  
Qed.

Lemma L10_3: forall n: nat, exists m: nat, prod n (S m) = sum n n. 
Proof.
  ...
Qed.

Lemma L10_4: forall m n: nat, n <> O -> sum m n <> O.  
Proof.
  ...
Qed.

Lemma L10_5: forall m n: nat, sum m n = O -> m = O /\ n = O.  
Proof.
  ...
Qed.

Lemma L10_6: forall m n: nat, prod m n = O -> m = O \/ n = O.  
Proof.
  ...
Qed.


End Ejercicio10.



Section Ejercicio11.

Variable le : nat->nat->Prop.
Axiom leinv: forall n m:nat, (le n m) -> n=O \/
      (exists p:nat, (exists q:nat, n=(S p)/\ m=(S q) /\ (le p q))).

Lemma notle_s_o: forall n:nat, ~(le (S n) O).
Proof.
  
Qed.

End Ejercicio11.
