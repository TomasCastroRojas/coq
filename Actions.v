(*******************************************************************
 * Este archivo especifica las acciones Como transformadores de estado.
 * LAS DEFINICIONES DADAS PUEDEN SER USADAS DIRECTAMENTE O CAMBIADAS.
 ******************************************************************)
Add LoadPath "." as Current.
Load "State.v".

Parameter ctxt : context.

Section Actions.
  
  Inductive Action :=
    | Read: vadd -> Action
    | Write: vadd -> value -> Action
    | Chmod: Action.

  (* Action preconditions *)
  Definition Pre (s : State) (a : Action) : Prop :=
    match a with
      | Read va =>    (os_accessible ctxt va)
                   -> (aos_activity s) = running
                   -> (exists (ma:madd), (va_mapped_to_ma s va ma) -> (match (memory s) ma with
                                                                        | None => False
                                                                        | Some p => is_RW (page_content p)
                                                                       end))
      | Write va v =>    (os_accessible ctxt va)
                   -> (aos_activity s) = running
                   -> (exists (ma:madd), (va_mapped_to_ma s va ma) -> (match (memory s) ma with
                                                                        | None => False
                                                                        | Some p => is_RW (page_content p)
                                                                       end))
      | Chmod => (aos_activity s) = waiting ->  match (oss s) (active_os s) with
                                                  | Some os => hcall os = None
                                                  | _ => False
                                                end
              
    end.

  (* Auxiliary predicadates *)
  Definition differ_at_most_memory (s s': State) (ma: madd) : Prop :=
       active_os s = active_os s'
    /\ aos_exec_mode s = aos_exec_mode s'
    /\ aos_activity s = aos_activity s'
    /\ oss s = oss s'
    /\ hypervisor s = hypervisor s'
    /\ forall (m: madd), m <> ma -> memory(s) m = memory(s') m.

  Definition differ_chmod (s s': State) (mode: exec_mode) (oa: os_activity) : Prop :=
       active_os s = active_os s'
    /\ mode = aos_exec_mode s'
    /\ oa = aos_activity s'
    /\ oss s = oss s'
    /\ hypervisor s = hypervisor s'
    /\ memory s = memory s'.
  
  (* Action postconditions *)
  Definition Post (s : State) (a : Action) (s' : State) : Prop :=
    match a with
      | Read va => s = s'
      | Write va v => (exists ma:madd, (va_mapped_to_ma s va ma) 
                                    -> let p := mk_page (RW (Some v)) (Os (active_os s)) in
                                       (memory s') = update (memory s) ma p 
                                    -> differ_at_most_memory s s' ma)
      | Chmod =>    (trusted_os ctxt s -> differ_chmod s s' svc running)
                 \/ ((~ trusted_os ctxt s) -> differ_chmod s s' usr running)
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