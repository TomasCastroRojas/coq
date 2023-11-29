(*******************************************************************
 * Este archivo especifica las acciones Como transformadores de estado.
 * LAS DEFINICIONES DADAS PUEDEN SER USADAS DIRECTAMENTE O CAMBIADAS.
 ******************************************************************)
Print LoadPath.
Add LoadPath "." as Current.
Load "State.v".

Parameter ctxt : context.

Section Actions.
  
  Inductive Action :=
  ...

  (* Action preconditions *)
  Definition Pre (s : State) (a : Action) : Prop :=
    match a with
    ...
    end.

  (* Action postconditions *)
  Definition Post (s : State) (a : Action) (s' : State) : Prop :=
    match a with
    ...    
    end.

  Definition valid_state_iii (s : State) : Prop :=  
  ...
  
  Definition inyective {A B : Set} (pmap : A ⇸ B) :=
    forall x y, pmap x = pmap y -> x = y.

  Definition valid_state_v (s : State) : Prop :=
  ...

  Definition valid_state_vi (s : State) : Prop :=
  ...  
  
  Definition valid_state (s : State) : Prop :=
    valid_state_iii s /\ valid_state_v s /\ valid_state_vi s.
  
  Inductive one_step : State -> Action -> State -> Prop :=
  ...
 
  Notation "a ⇒ s ↪ s'" := (one_step s a s') (at level 50).


  Theorem one_step_preserves_prop_iii : forall (s s' : State) (a : Action),
      a ⇒ s ↪ s' -> valid_state_iii s'.
  Proof.
  ...
  Qed. 


  Theorem read_isolation : forall (s s' : State) (va : vadd),
  ...  
  Proof.
  ...
  Qed.

End Actions.