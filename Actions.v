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
                   /\ (aos_activity s) = running
                   /\ (exists (ma:madd) (p: page), (va_mapped_to_ma s va ma) /\ (memory s) ma = Some p /\ is_RW (page_content p))
      | Write va v =>   (os_accessible ctxt va)
                     /\ (aos_activity s) = running
                     /\ (exists (ma:madd) (p: page), (va_mapped_to_ma s va ma) /\ (memory s) ma = Some p /\ is_RW (page_content p))
      | Chmod => (aos_activity s) = waiting /\ (exists o: os, (oss s) (active_os s) = Some o /\ (hcall o) = None)
              
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
      | Chmod =>    (trusted_os ctxt s /\ differ_chmod s s' svc running)
                 \/ ((~ trusted_os ctxt s) /\ differ_chmod s s' usr running)
    end.

  (*if the hypervisor or a trusted OS is running the processor must be in supervisor mode*)
  Definition valid_state_iii (s : State) : Prop :=  
    (aos_activity s = waiting \/ (aos_activity s = running -> trusted_os ctxt s)) -> aos_exec_mode s = svc.
  
  Definition inyective {A B : Set} (pmap : A ⇸ B) :=
    forall x y, pmap x = pmap y -> x = y.

  (* the hypervisor maps an OS physical address to a machine address owned by
     that same OS. This mapping is also injective *)
  Definition valid_state_v (s : State) : Prop :=
    forall (pa: padd),
    (exists (pmap:(padd ⇸ madd)) (ma: madd) (p: page),
       (hypervisor s) (active_os s) = Some pmap
    /\ pmap pa = Some ma
    /\ (memory s) ma = Some p
    /\ (match (page_owned_by p) with
          | Os id => id = active_os s
          | _ => False
        end)
    /\ inyective pmap).

  (* all page tables of an OS o map accessible virtual addresses to pages owned by o
     and not accessible ones to pages owned by the hypervisor *)
  Definition valid_state_vi (s : State) : Prop :=
    forall (p: page),
      match (page_content p), (page_owned_by p) with
        | PT ptmap, Os o =>
          forall (va: vadd) (ma: madd) (p': page), (ptmap va = Some ma /\
                                                    (memory s) ma = Some p') ->
                                                    ( (os_accessible ctxt va -> page_owned_by p = Os o)
                                                   /\ (~os_accessible ctxt va -> page_owned_by p = Hyp))
        | _, _ => False
      end.

  
  Definition valid_state (s : State) : Prop :=
    valid_state_iii s /\ valid_state_v s /\ valid_state_vi s.
  
  Inductive one_step : State -> Action -> State -> Prop :=
    | onestep: forall (s: State) (a: Action) (s': State),
                 valid_state s -> Pre s a -> Post s a s' -> one_step s a s'. 
 
  Notation "a ⇒ s ↪ s'" := (one_step s a s') (at level 50).


  Theorem one_step_preserves_prop_iii : forall (s s' : State) (a : Action),
      a ⇒ s ↪ s' -> valid_state_iii s'.
  Proof.
  Proof.
    intros s s' a OneStep.
    destruct OneStep.
    induction a; unfold valid_state in H; unfold Pre in H0;
    unfold Post in H1; unfold valid_state_iii; intro PropH.
    - elim H.
      intros Prop_iii H'.
      unfold valid_state_iii in Prop_iii.
      rewrite H1 in Prop_iii.
      apply Prop_iii.
      exact PropH.
    - elim H; intros.
      unfold valid_state_iii in H2; clear H H3.
      
      elim H0.
      intros OsAccess H0'; clear H0.
      elim H0'.
      intros OsRunning H0''; clear H0'.
      
      elim H1; clear H1.
      intro ma.
      intro H1'.
      elim H1'; clear H1'.
      intros va_map_ma H1''.
      elim H1''; clear H1''.
      
      intros UpdateMemory DifferMemory.
      unfold differ_at_most_memory in DifferMemory.
      inversion_clear DifferMemory.
      inversion_clear H0.
      inversion_clear H3.
      clear H4.
      
      rewrite <- H1.
      apply H2.
      elim PropH; intros.
      -- left.
         rewrite H0.
         exact H3.
      -- right.
         intro OsRunning'.
         unfold trusted_os; unfold trusted_os in H3.
         rewrite H.
         apply H3.
         rewrite <- H0.
         exact OsRunning'.
  - elim H0; intros curr_act H2; clear H2.
    elim H1; intro; elim H2; intros; clear H2;
    
    inversion_clear H4;
    inversion_clear H5;
    inversion_clear H6;
    clear H7.
    
    -- rewrite H4; reflexivity.
    -- elim PropH; intro.
       --- absurd (running = aos_activity s').
           rewrite H6.
           discriminate.
           exact H5.
       --- unfold trusted_os in H3.
           rewrite H2 in H3.
           absurd (trusted_os ctxt s').
           exact H3.
           apply H6.
           rewrite <- H5; reflexivity.
  Qed. 


  Theorem read_isolation : forall (s s' : State) (va : vadd),
    (Read va) ⇒ s ↪ s' ->
      exists (ma: madd), va_mapped_to_ma s va ma /\
        exists (p: page), Some p = (memory s) ma /\
          page_owned_by p = Os (active_os s).  
  Proof.
    intros s s' va OneStep.
    inversion_clear OneStep.
    inversion_clear H0.
    inversion_clear H3.
    inversion H1; clear H1.
    inversion_clear H.
    inversion_clear H5.
    
    elim H4.
    intros ma H4'.
    elim H4'.
    intros p PreH; clear H4 H4'.
    
    exists ma.
    split.
    - elim PreH.
      intros.
      rewrite H3 in H4.
      exact H4.
    - exists p.
      split.
      -- elim PreH.
         intros va_map_ma PreH'.
         elim PreH'.
         intros Memory RWPage; clear PreH PreH'.
         rewrite H3 in Memory.
         rewrite Memory; reflexivity.
      -- (* WIP: sale por valid_state_vi creo *)
  Qed.

End Actions.
