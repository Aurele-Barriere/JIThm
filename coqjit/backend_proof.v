(* Proving the correctness of using the CompCert backend *)

Require Import monad.
Require Import AST.
Require Import RTL.
Require Import Asm.
Require Import IR.
Require Import jit.
Require Import Errors.
Require Import mixed_sem.
Require Import backend.
Require Import primitives.
Require Import monad.
Require Import monad_impl.
Require Import internal_simulations.
Require Import flattenRTL_proof.

Require Import Compiler.
Require Import Linking.
Require Import Compopts.
Require Import Smallstep.
Require Import intpos.
Require Import common.

(** * CompCert's Backend Correctness Theorem  *)

Local Open Scope linking_scope.
Definition backend_passes :=
      mkpass (match_if Compopts.optim_tailcalls Tailcallproof.match_prog)
  (* ::: mkpass Inliningproof.match_prog *)
  ::: mkpass Renumberproof.match_prog
  ::: mkpass (match_if Compopts.optim_constprop Constpropproof.match_prog)
  ::: mkpass (match_if Compopts.optim_constprop Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.optim_CSE CSEproof.match_prog)
  ::: mkpass (match_if Compopts.optim_redundancy Deadcodeproof.match_prog)
  ::: mkpass Allocproof.match_prog
  ::: mkpass Tunnelingproof.match_prog
  ::: mkpass Linearizeproof.match_prog
  ::: mkpass CleanupLabelsproof.match_prog
  ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
  ::: mkpass Stackingproof.match_prog
  ::: mkpass Asmgenproof.match_prog
  ::: pass_nil _.

Definition backend_match_prog: RTL.program -> Asm.program -> Prop :=
  pass_match (compose_passes backend_passes).

Theorem transf_rtl_program_match:
  forall p tp,
  transf_rtl_program_ p = OK tp ->
  backend_match_prog p tp.
Proof.
  intros p tp T. rename p into p6.
  unfold transf_rtl_program_, time in T. (* rewrite ! compose_print_identity in T. *) simpl in T.
  set (p7 := total_if optim_tailcalls Tailcall.transf_program p6) in *.
  (* destruct (Inlining.transf_program p7) as [p8|e] eqn:P8; simpl in T; try discriminate. *)
  set (p9 := Renumber.transf_program p7) in *.
  set (p10 := total_if optim_constprop Constprop.transf_program p9) in *.
  set (p11 := total_if optim_constprop Renumber.transf_program p10) in *.
  destruct (partial_if optim_CSE CSE.transf_program p11) as [p12|e] eqn:P12; simpl in T; try discriminate.
  destruct (partial_if optim_redundancy Deadcode.transf_program p12) as [p13|e] eqn:P13; simpl in T; try discriminate.
  destruct (Allocation.transf_program p13) as [p15|e] eqn:P15; simpl in T; try discriminate.
  set (p16 := Tunneling.tunnel_program p15) in *.
  destruct (Linearize.transf_program p16) as [p17|e] eqn:P17; simpl in T; try discriminate.
  set (p18 := CleanupLabels.transf_program p17) in *.
  destruct (partial_if debug Debugvar.transf_program p18) as [p19|e] eqn:P19; simpl in T; try discriminate.
  destruct (Stacking.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
  unfold backend_match_prog; simpl.
  exists p7; split. apply total_if_match. apply Tailcallproof.transf_program_match.
  (* exists p8; split. apply Inliningproof.transf_program_match; auto. *)
  exists p9; split. apply Renumberproof.transf_program_match; auto.
  exists p10; split. apply total_if_match. apply Constpropproof.transf_program_match.
  exists p11; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p12; split. eapply partial_if_match; eauto. apply CSEproof.transf_program_match.
  exists p13; split. eapply partial_if_match; eauto. apply Deadcodeproof.transf_program_match.
  exists p15; split. apply Allocproof.transf_program_match; auto.
  exists p16; split. apply Tunnelingproof.transf_program_match.
  exists p17; split. apply Linearizeproof.transf_program_match; auto.
  exists p18; split. apply CleanupLabelsproof.transf_program_match; auto.
  exists p19; split. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
  exists p20; split. apply Stackingproof.transf_program_match; auto.
  exists tp; split. apply Asmgenproof.transf_program_match; auto.
  reflexivity.
Qed.

Theorem compcert_backend_forward:
  forall p tp,
  backend_match_prog p tp ->
  forward_simulation (RTL.semantics p) (Asm.semantics tp).
Proof.
  intros p tp H. unfold backend_match_prog, pass_match in H; simpl in H. repeat DestructM. subst tp.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Tailcallproof.transf_program_correct.
  (* eapply compose_forward_simulations. *)
  (*   eapply Inliningproof.transf_program_correct; eassumption. *)
  eapply compose_forward_simulations. eapply Renumberproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Constpropproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Renumberproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact CSEproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Deadcodeproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Allocproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Tunnelingproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Linearizeproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply CleanupLabelsproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Debugvarproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply Stackingproof.transf_program_correct with (return_address_offset := Asmgenproof0.return_address_offset).
    exact Asmgenproof.return_address_exists.
    eassumption.
  eapply Asmgenproof.transf_program_correct; eassumption.
Qed.

Theorem compcert_backend_backward:
  forall p tp,
    backend_match_prog p tp ->
    backward_simulation (RTL.semantics p) (Asm.semantics tp).
Proof.
  intros p tp H.
  apply forward_to_backward_simulation. apply compcert_backend_forward; auto.
  apply semantics_receptive. apply Asm.semantics_determinate.
Qed.

(* Proof of the CompCert backend *)
Theorem transf_rtl_program_correct:
  forall p tp,
  transf_rtl_program_ p = OK tp ->
  backward_simulation (RTL.semantics p) (Asm.semantics tp).
Proof.
  intros. apply compcert_backend_backward. apply transf_rtl_program_match; auto.
Qed.


(** * Proof of the Backend JIT Pass  *)

(* used for rewrite when simpl is stuck *)
Lemma fold_left_cons:
  forall A B (f:A -> B -> A) l b init,
    fold_left f (b::l) init =
    fold_left f l (f init b).
Proof.
  intros. simpl. auto.
Qed.

Lemma fold_left_ok:
  forall A B (f:A -> res B) l init r,
    fold_left (fun a p =>
                 do asms <- a;
                   do prog <- f (snd p);
                   OK (PTree.set (fst p) prog asms))l init = OK r ->
    exists i, init = OK i.
Proof.
  intros A B f l init r H. generalize dependent init. generalize dependent r.
  induction l; intros.
  - simpl in H. inv H. eauto.
  - rewrite fold_left_cons in H. apply IHl in H. destruct H as [i DO].
    repeat do_ok. eauto.
Qed.

(* adding new continuations doesn't remove the one that were already there *)
Lemma fold_set_monotonic:
  forall A B contid (f:A -> res B) (l: list (positive * A)) init result,
    fold_left (fun a p =>
                 do asms <- a;
                   do prog <- f (snd p);
                   OK (PTree.set (fst p) prog asms)) l init = OK result ->
    ~ In contid (map fst l) ->
    exists initr,
      init = OK initr /\
      result ! contid = initr ! contid.
Proof.
  intros A B contid f l.
  induction l; intros.
  - simpl in H. inv H. exists result. split; auto.
  - simpl in H0. apply Decidable.not_or in H0. destruct H0.
    rewrite fold_left_cons in H.
    apply IHl in H; auto. destruct H as [initr [OK SAME]].
    repeat do_ok. exists t. split; auto. rewrite PTree.gso in SAME; auto.
Qed.

Lemma cont_compiled:
  forall rtlfid rtlcode rtlentry rtlidx asm asmcont contlbl asmp,
    rtl_backend (rtlfid, rtlcode, rtlentry, rtlidx) = OK (asm, asmcont) ->
    asmcont ! contlbl = Some asmp ->
    exists entrylbl, rtlidx ! contlbl = Some entrylbl.
Proof.
  intros rtlfid rtlcode rtlentry rtlidx asm asmcont contlbl asmp H H0.
  unfold rtl_backend in H. repeat do_ok.
  unfold cont_backend in HDO0. rewrite PTree.fold_spec in HDO0.
  assert (NOREP: list_norepet (map fst (PTree.elements rtlidx))) by apply PTree.elements_keys_norepet.
  assert (H: forall l acont init,
               list_norepet (map fst l) ->
               acont ! contlbl = Some asmp ->
               fold_left (fun a p =>
                            do asms <- a;
                            do prog <- fun_backend rtlcode (snd p);
                            OK (PTree.set (fst p) prog asms))
                         l (OK init) = OK acont ->
               init ! contlbl = None ->
               exists entrylbl,
                 In (contlbl, entrylbl) l).
  { clear NOREP HDO0 H0. intros l; induction l; intros.
    - simpl in H1. inv H1. rewrite H2 in H0. inv H0.
    - rewrite fold_left_cons in H1. simpl in H. inv H.
      apply fold_left_ok in H1 as INIT. destruct INIT as [i INIT]. rewrite INIT in H1.
      poseq_destr (fst a) contlbl.
      + exists (snd a). simpl. left. destruct a. auto.
      + apply IHl in H1; eauto.
        * destruct H1 as [el IN]. exists el. simpl. right. auto.
        * unfold bind in INIT. destruct (fun_backend rtlcode (snd a)) eqn:BACK; inv INIT.
          rewrite PTree.gso; auto. }
  apply H in HDO0; eauto.
  (* 2: { rewrite PTree.gempty. auto. } *)
  destruct HDO0 as [el IN]. exists el. apply PTree.elements_complete. auto.
Qed.

Lemma cont_compiled_get_entry:
  forall rtlfid rtlcode rtlentry rtlidx asm asmcont contlbl asmp,
    rtl_backend (rtlfid, rtlcode, rtlentry, rtlidx) = OK (asm, asmcont) ->
    asmcont ! contlbl = Some asmp ->
    exists entrylbl, rtl_get_entry (rtlfid, rtlcode, rtlentry, rtlidx) (Cont contlbl) = Some entrylbl.
Proof.
  intros rtlfid rtlcode rtlentry rtlidx asm asmcont contlbl asmp H H0.
  eapply cont_compiled in H; eauto.
Qed.


(* Correctness of the function that compiles all continuations and main function *)
Theorem all_compiled:
  forall rtlfid rtlcode rtlentry rtlidx asmp asmcont contid entrylbl
    (BACKEND: rtl_backend (rtlfid, rtlcode, rtlentry, rtlidx) = OK (asmp, asmcont))
    (GET_RTL: rtl_get_entry (rtlfid, rtlcode, rtlentry, rtlidx) contid = Some entrylbl),
  exists asmf,
    asm_get (asmp, asmcont) contid = Some asmf /\
    Smallstep.backward_simulation (RTL.semantics (make_prog rtlcode entrylbl)) (Asm.semantics asmf).
Proof.
  intros rtlfid rtlcode rtlentry rtlidx asmp asmcont contid entrylbl BACKEND GET_RTL.
  destruct contid as [|contid].
  - simpl in GET_RTL. inv GET_RTL. exists asmp. split; auto.
    apply transf_rtl_program_correct. unfold rtl_backend in BACKEND.
    repeat do_ok. unfold fun_backend in HDO. auto.
  - simpl in GET_RTL. unfold rtl_backend in BACKEND. repeat do_ok. clear HDO. rename HDO0 into CONTS.
    unfold cont_backend in CONTS. rewrite PTree.fold_spec in CONTS.
    assert (NOREP: list_norepet (map fst (PTree.elements rtlidx))) by apply PTree.elements_keys_norepet.
    assert (H: forall l acont init,
               list_norepet (map fst l) ->
               In (contid, entrylbl) l ->
               fold_left (fun a p =>
                            do asms <- a;
                            do prog <- fun_backend rtlcode (snd p);
                            OK (PTree.set (fst p) prog asms))
                         l init = OK acont ->
               exists asmf,
                 fun_backend rtlcode entrylbl = OK asmf /\
                 asm_get (asmp, acont) (Cont contid) = Some asmf).
    { clear NOREP CONTS GET_RTL asmcont. intros l. induction l.
      - intros. inv H0.
      - intros. inv H0.
        + rewrite fold_left_cons in H1. inv H.
          eapply fold_set_monotonic in H1; eauto. destruct H1 as [initr [DO_OK SAME]].
          simpl fst in DO_OK. simpl snd in DO_OK. unfold bind in DO_OK. (* have to unfold. inversion is stuck *)
          destruct init. 2: inversion DO_OK.
          destruct (fun_backend rtlcode entrylbl) eqn:BACK; inv DO_OK.
          exists p. rewrite PTree.gss in SAME. split; auto. 
        + inv H. rewrite fold_left_cons in H1.
          apply IHl in H1; auto. }
    apply PTree.elements_correct in GET_RTL.
    specialize (H (PTree.elements rtlidx) asmcont (OK (PTree.empty Asm.program)) NOREP GET_RTL CONTS).
    destruct H as [asmf [BACKEND GET]]. exists asmf. split; auto.
    apply transf_rtl_program_correct. auto.
Qed.    


(* bsim_properties is like a backward, but with index, order, ms explicit *)
Theorem all_compiled':
  forall rtlfid rtlcode rtlentry rtlidx asmp asmcont contid entrylbl
    (BACKEND: rtl_backend (rtlfid, rtlcode, rtlentry, rtlidx) = OK (asmp, asmcont))
    (GET_RTL: rtl_get_entry (rtlfid, rtlcode, rtlentry, rtlidx) contid = Some entrylbl),
  exists asmf index order ms,
    asm_get (asmp, asmcont) contid = Some asmf /\
    Smallstep.bsim_properties (RTL.semantics (make_prog rtlcode entrylbl)) (Asm.semantics asmf) index order ms.
Proof.
  intros rtlfid rtlcode rtlentry rtlidx asmp asmcont contid entrylbl BACKEND GET_RTL.
  eapply all_compiled in BACKEND; eauto. destruct BACKEND as [asmf [GET_ASM SIMUL]].
  inv SIMUL. exists asmf. exists index. exists order. exists match_states. split; auto.
Qed.


Theorem compiled_from_rtl:
  forall rtlfid rtlcode rtlentry rtlidx asmp asmcont contid asmf
    (BACKEND: rtl_backend (rtlfid, rtlcode, rtlentry, rtlidx) = OK (asmp, asmcont))
    (GET_ASM: monad.asm_get (asmp, asmcont) contid = Some asmf),
  exists entrylbl,
    rtl_get_entry (rtlfid, rtlcode, rtlentry, rtlidx) contid = Some entrylbl /\
    Smallstep.backward_simulation (RTL.semantics (make_prog rtlcode entrylbl)) (Asm.semantics asmf).
Proof.
  intros rtlfid rtlcode rtlentry rtlidx asmp asmcont contid asmf BACKEND GET_ASM.
  destruct contid as [|contid].
  - exists rtlentry. split; auto. unfold rtl_backend in BACKEND. repeat do_ok. inv GET_ASM.
    unfold fun_backend in HDO. apply transf_rtl_program_correct. auto.
  - simpl in GET_ASM. unfold rtl_backend in BACKEND. repeat do_ok. clear HDO. rename HDO0 into CONTS.
    unfold cont_backend in CONTS. rewrite PTree.fold_spec in CONTS.
    assert (NOREP: list_norepet (map fst (PTree.elements rtlidx))) by apply PTree.elements_keys_norepet.
    assert (H: forall l acont init inres,
               list_norepet (map fst l) ->
               acont # contid = Some asmf ->
               init = OK inres ->
               inres # contid = None ->
               fold_left (fun a p =>
                            do asms <- a;
                            do prog <- fun_backend rtlcode (snd p);
                            OK (PTree.set (fst p) prog asms))
                         l init = OK acont ->
               exists entrylbl,
                 fun_backend rtlcode entrylbl = OK asmf /\
                 In (contid, entrylbl) l).

    { clear GET_ASM CONTS NOREP. intros l. induction l as [|[ID ENTRY] l IHL]; intros.
      - simpl in H3. rewrite H1 in H3. inv H3. rewrite H2 in H0. inv H0.
      - inv H. rewrite fold_left_cons in H3.
        apply fold_left_ok in H3 as INITOK. destruct INITOK as [init INITOK].
        poseq_destr ID contid.
        + exists ENTRY. split. 2: { simpl. left. auto. }
          apply fold_set_monotonic with (contid:=contid)in H3; auto. 
          destruct H3 as [initr [DO CONT]]. unfold bind in DO.
          replace (snd (contid, ENTRY)) with ENTRY in DO by auto.
          destruct (fun_backend rtlcode ENTRY); inv DO. rewrite PTree.gss in CONT; auto.
          rewrite H0 in CONT. inv CONT. auto.
        + eapply IHL in H3; eauto.
          * destruct H3 as [entrylbl [BACK IN]]. exists entrylbl. split; auto. right. auto.
          * unfold bind in INITOK. destruct (fun_backend rtlcode (snd (ID, ENTRY))); inv INITOK.
            rewrite PTree.gso; auto. }
    assert (EQ: OK (PTree.empty Asm.program) = OK (PTree.empty Asm.program)) by auto.
    assert (EMP: (PTree.empty Asm.program) # contid = None) by apply PTree.gempty.
    specialize (H (PTree.elements rtlidx) asmcont _ _ NOREP GET_ASM EQ EMP CONTS).
    destruct H as [entrylbl [BACK IN]]. exists entrylbl. split; auto.
    + simpl. apply PTree.elements_complete. auto.
    + unfold fun_backend in BACK. apply transf_rtl_program_correct. auto.
Qed.
            
Theorem compiled_from_rtl':
  forall rtlfid rtlcode rtlentry rtlidx asmp asmcont contid asmf
    (BACKEND: rtl_backend (rtlfid, rtlcode, rtlentry, rtlidx) = OK (asmp, asmcont))
    (GET_ASM: monad.asm_get (asmp, asmcont) contid = Some asmf),
  exists entrylbl index order ms,
    rtl_get_entry (rtlfid, rtlcode, rtlentry, rtlidx) contid = Some entrylbl /\
    Smallstep.bsim_properties (RTL.semantics (make_prog rtlcode entrylbl)) (Asm.semantics asmf) index order ms.
Proof.
  intros rtlfid rtlcode rtlentry rtlidx asmp asmcont contid asmf BACKEND GET_ASM.
  eapply compiled_from_rtl in GET_ASM; eauto. destruct GET_ASM as [lbl [GET SIM]]. destruct SIM.
  exists lbl. eauto.
Qed.


(** * Correctness of the JIT backend Compiler  *)
Require Import customSmallstep.
Require Import sem_properties.
Require Import Relation_Definitions.
Require Import Events.
Require Import common.

Definition rtlcode (rtl:RTLfun) : RTL.code :=
  match rtl with
  | (fid, rtlc, entry, contidx) => rtlc
  end.


(** * Same Plus and Star  *)
Lemma same_star:
  forall genv state (step:genv->state->trace->state->Prop) ge s1 t s2,
    Smallstep.star step ge s1 t s2 <-> star step ge s1 t s2.
Proof.
  intros genv state step ge s1 t s2. split; intros.
  - induction H. apply star_refl.
    eapply star_step; eauto.
  - induction H. apply Smallstep.star_refl.
    eapply Smallstep.star_step; eauto.
Qed.

Lemma same_plus:
  forall genv state (step:genv->state->trace->state->Prop) ge s1 t s2,
    Smallstep.plus step ge s1 t s2 <-> plus step ge s1 t s2.
Proof.
  intros genv state step ge s1 t s2. split; intros.
  - inv H. eapply plus_left; eauto. apply same_star. auto.
  - inv H. eapply Smallstep.plus_left; eauto. apply same_star. auto.
Qed.



(** *  Well-formedness of the generated RTLcode *)
(* in flattenRTL_proof, we've already showed that every RTL code produced was rtl_code_wf  *)
(* We now propagate similar invariants about the semantic states and stack *)

Definition stackframe_wf (s:RTL.stackframe) : Prop :=
  match s with
  | Stackframe r f v n rs => rtl_code_wf (RTL.fn_code f)
  end.

Definition stack_wf (s:list RTL.stackframe) : Prop :=
  match s with
  | nil => True                     (* nil when doing tailcall *)
  | sf::nil => stackframe_wf sf   (* when doing a call to EF *)
  | _ => False
  end.

Definition ge_wf (ge:RTL.genv) : Prop :=
  forall id rs ef, 
    find_function ge (inr id) rs = Some (ef) ->
    id <> main_id ->
    exists (p:ext_primitive), ef = External (EF p).

Definition rtl_state_wf (s:RTL.state) : Prop :=
  match s with
  | RTL.State stk f v n rs m => stk = nil /\ rtl_code_wf (RTL.fn_code f)
  | RTL.Callstate stk fd args m =>
    match fd with
    | Internal f => (* the only possible internal callstate is calling the main function *)
      stk = nil /\ args = nil /\ rtl_code_wf (RTL.fn_code f)
                     (* let ge := Globalenvs.Genv.globalenv p in *)
                     (*      Globalenvs.Genv.init_mem p = Some m0 -> *)
                     (*      Globalenvs.Genv.find_symbol ge (AST.prog_main p) = Some b -> *)
                     (*      Globalenvs.Genv.find_funct_ptr ge b = Some f -> *)
                     (*      funsig f = signature_main -> RTL.initial_state p (RTL.Callstate nil f nil m0) *)
    | External ef => stack_wf stk /\ exists (p:ext_primitive),
                    ef = EF_runtime (EF_name p) (EF_sig p)
    end
  (* at most one call to an EF always *)
  | RTL.Returnstate stk v m => stack_wf stk
  end.

Lemma step_pres_wf:
  forall ge rtls t rtls',
    ge_wf ge ->
    rtl_state_wf rtls ->
    RTL.step ge rtls t rtls' ->
    rtl_state_wf rtls'.
Proof.
  intros ge rtls t rtls' GEWF H STEP. destruct rtls; simpl in H.
  - destruct H as [STK WF]. subst. inv STEP; simpl; auto.
    + apply WF in H7. inv H7. apply GEWF in H8. destruct H8 as [p EF].
      { destruct ef; simpl; unfold not; intros H; inv H. }
      subst. split; auto. exists p. auto.
    + apply WF in H7. inv H7. 
  - destruct f.
    + destruct H as [STK [ARGS WF]]. subst. inv STEP. simpl. split; auto. 
    + destruct H as [STK [p EXT]]. subst. inv STEP. simpl. auto.
  - inv STEP. simpl. simpl in H. destruct s.
    + split; auto.
    + inv H.
Qed.

(* Showing that our runtime primitives don't have the same name as known builtins *)
Lemma known_prim_sem:
  forall prim,
    builtin_or_external_sem (EF_name prim) (EF_sig prim) =
    external_functions_sem (EF_name prim) (EF_sig prim).
Proof.
  intros prim. unfold builtin_or_external_sem. unfold Builtins.lookup_builtin_function.
  destruct prim; simpl; auto.
Qed.

Lemma known_external:
  forall prim,
    external_call (EF_runtime (EF_name prim) (EF_sig prim)) =
    external_functions_sem (EF_name prim) (EF_sig prim).
Proof.
  intros. simpl. rewrite known_prim_sem. auto.
Qed.
                            
      

Lemma silent_rtl_mixed:
  forall ge p or ac mut rtls rtls',
    rtl_state_wf rtls -> 
    RTL.step ge rtls E0 rtls' ->
      mixed_step AnchorOff p or ac (Halt_RTL ge rtls, mut) E0 (Halt_RTL ge rtls', mut).
Proof.
  intros ge p or ac mut rtls rtls' STATEWF STEP.
  destruct rtls.
  - apply rtl_step; auto. unfold not; intros INT. inv INT.
    inv STATEWF. unfold rtl_code_wf in H0. apply H0 in BUILTIN. inv BUILTIN.
  - inv STEP.
    + inv STATEWF. destruct H0 as [NIL WF]. apply rtl_step; auto. (* call to main *)
      { unfold not. intros H. inv H. }
      apply exec_function_internal. auto.
    + inv STATEWF. destruct H0 as [prim EXT]. subst. simpl in H5. rewrite known_prim_sem in H5.
      apply ext_prim_axiom in H5 as AX. (* using our AXIOM on ext primitives *)
      destruct AX as [a0 [r [HA [T [M [RES TRACE]]]]]]. inv TRACE.
  - apply rtl_step; auto. unfold not; intros INT. inv INT.
Qed.


Lemma silent_rtl_mixed_star:
  forall ge p or ac mut rtls rtls',
    ge_wf ge ->
    rtl_state_wf rtls ->
    Smallstep.star RTL.step ge rtls E0 rtls' ->
    Smallstep.star (mixed_step AnchorOff p or) ac (Halt_RTL ge rtls, mut) E0 (Halt_RTL ge rtls', mut) /\
    rtl_state_wf rtls'.
Proof.
  intros ge p or ac mut rtls rtls' GEWF H H0. remember E0 as t. induction H0.
  - split; auto. apply Smallstep.star_refl. 
  - subst. destruct t1; inv H2. destruct t2; inv H3.
    apply step_pres_wf in H0 as WF; auto. apply IHstar in WF; auto.
    destruct WF as [STAR WF].
    split; auto. eapply Smallstep.star_step with (t1:=nil) (s2:=(Halt_RTL ge s2, mut)); eauto.
    apply silent_rtl_mixed; auto.
Qed.

Lemma silent_rtl_mixed_star':
  forall ge p or ac mut rtls rtls',
    ge_wf ge ->
    rtl_state_wf rtls ->
    star RTL.step ge rtls E0 rtls' ->
    star (mixed_step AnchorOff p or) ac (Halt_RTL ge rtls, mut) E0 (Halt_RTL ge rtls', mut) /\
    rtl_state_wf rtls'.
Proof.
  intros ge p or ac mut rtls rtls' H H0 H1. rewrite <- same_star. rewrite <- same_star in H1.
  apply silent_rtl_mixed_star; auto.
Qed.


Lemma silent_rtl_mixed_plus:
  forall ge p or ac mut rtls rtls',
    ge_wf ge ->
    rtl_state_wf rtls ->
    Smallstep.plus RTL.step ge rtls E0 rtls' ->
    Smallstep.plus (mixed_step AnchorOff p or) ac (Halt_RTL ge rtls, mut) E0 (Halt_RTL ge rtls', mut) /\
    rtl_state_wf rtls'.
Proof.
  intros ge p or ac mut rtls rtls' GEWF H H0. inv H0.
  destruct t1; inv H3. destruct t2; inv H0.
  apply step_pres_wf in H1 as WF1; auto.
  eapply silent_rtl_mixed in H1 as STEP; eauto.
  eapply silent_rtl_mixed_star in H2 as [STAR WF2]; eauto.
  split; auto. apply Smallstep.plus_left with (t1:=nil) (t2:=nil) (s2:=(Halt_RTL ge s2, mut)); eauto.
Qed.



(** * Axiomatisation of the backend  *)
(* Here, we assume that the CompCert backend does not introduce any new builtins *)
(* In practice, this is true because the RTL programs we compile don't have any of such things *)
(* We could prove that by going into each pass *)
(* But in this proof we want to use CompCert as a black box with only a simulation and this axiom *)

Definition asm_external_prims (ge:genv):Prop :=
  forall b ef,
    Globalenvs.Genv.find_funct_ptr ge b = Some (External ef) ->
    exists (p:ext_primitive),
      ef = EF_runtime (EF_name p) (EF_sig p).
                                                
Definition asm_no_builtin (ge:genv) : Prop :=
  forall b f,
    (Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
     forall ofs ef args res,
       find_instr (Integers.Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) -> False).

Axiom no_builtin:
  forall rtlc entry ap,
    fun_backend rtlc entry = OK ap ->
    asm_no_builtin (Globalenvs.Genv.globalenv ap).


Definition asm_ge_wf (ge:genv): Prop :=
  asm_external_prims ge /\ asm_no_builtin ge.


(* The globalenvs we see *)
Inductive ok_ge {X:Type}: AST.program (AST.fundef X) unit -> Prop :=
| OKGE: forall f, 
    ok_ge {| prog_defs := (main_id, Gfun (Internal f))::prim_defs;
             prog_public := prim_id_defs;
             AST.prog_main := main_id |}.

Lemma ok_make_prog:
  forall rtlc entry,
    ok_ge (make_prog rtlc entry).
Proof.
  intros rtlc entry. unfold make_prog. constructor.
Qed.

Lemma transform_globdefs_ok:
  forall X Y (trans:AST.fundef X -> AST.fundef Y),
    (forall prim, trans (External (EF prim)) = (External (EF prim))) ->
    map (transform_program_globdef trans) prim_defs = prim_defs.
Proof.
  intros X Y trans SAME. simpl. unfold prim_defs. unfold EF_ident. simpl.
  repeat rewrite SAME. auto.
Qed.

Lemma transf_globdefs_ok:
  forall X Y (trans:AST.fundef X -> res (AST.fundef Y)),
    (forall prim, trans (External (EF prim)) = OK (External (EF prim))) ->
    transf_globdefs (fun (_ : ident) (f : AST.fundef X) => trans f)
                    (fun (_ : ident) (v : unit) => OK v) prim_defs = OK prim_defs.
Proof.
  intros X Y trans H. simpl. unfold prim_defs. unfold EF_ident. simpl.
  repeat rewrite H. simpl. auto.
Qed.


Lemma transform_program_ok:
  forall X1 X2 (p1:AST.program (AST.fundef X1) unit) (p2:AST.program (AST.fundef X2) unit) trans,
    transform_program trans p1 = p2 ->
    (forall prim, trans (External (EF prim)) = (External (EF prim))) ->
    (forall f, exists f', trans (Internal f) = Internal f') ->
    ok_ge p1 ->
    ok_ge p2.
Proof.
  Opaque prim_defs.
  intros X1 X2 p1 p2 trans H SAME INT H0. inv H0.
  unfold transform_program. simpl. rewrite transform_globdefs_ok; auto.
  specialize (INT f) as [f' INT]. rewrite INT.
  econstructor.
  Transparent prim_defs.
Qed.

Lemma transform_ok:
  forall X1 X2 (p1:AST.program (AST.fundef X1) unit) (trans:AST.fundef X1 -> AST.fundef X2),
    (forall prim, trans (External (EF prim)) = (External (EF prim))) ->
    (forall f, exists f', trans (Internal f) = Internal f') ->
    ok_ge p1 ->
    ok_ge (transform_program trans p1).
Proof.
  intros X1 X2 p1 trans H H0 H1. eapply transform_program_ok in H1; eauto.
Qed.

Lemma transform_partial_ok:
  forall X1 X2 (p1:AST.program (AST.fundef X1) unit) p2 (trans:AST.fundef X1 -> res (AST.fundef X2)),
    transform_partial_program trans p1 = OK p2 ->
    (forall prim, trans (External (EF prim)) = OK (External (EF prim))) ->
    (forall f ft, trans (Internal f) = OK (ft) -> exists f', ft = Internal f') ->
    ok_ge p1 ->
    ok_ge p2.
Proof.
  Opaque prim_defs.
  intros X1 X2 p1 p2 trans H SAME INT H1. unfold transform_partial_program, transform_partial_program2  in H.
  inv H1. simpl in H. repeat do_ok. destruct (trans (Internal f)) eqn:TRANSF; inv HDO. repeat do_ok.
  rewrite transf_globdefs_ok in HDO; auto. inv HDO.
  specialize (INT f) as [f' INT]. eauto. rewrite INT. 
  constructor.
  Transparent prim_defs.
Qed.




Lemma backend_ok:
  forall rtlc entry ap,
    fun_backend rtlc entry = OK ap ->
    ok_ge ap.
Proof.
  intros rtlc entry tp T. unfold fun_backend in T. 
  unfold transf_rtl_program_, time in T. (* rewrite ! compose_print_identity in T. *) simpl in T.
  set (p7 := total_if optim_tailcalls Tailcall.transf_program (make_prog rtlc entry)) in *.
  (* destruct (Inlining.transf_program p7) as [p8|e] eqn:P8; simpl in T; try discriminate. *)
  set (p9 := Renumber.transf_program p7) in *.
  set (p10 := total_if optim_constprop Constprop.transf_program p9) in *.
  set (p11 := total_if optim_constprop Renumber.transf_program p10) in *.
  destruct (partial_if optim_CSE CSE.transf_program p11) as [p12|e] eqn:P12; simpl in T; try discriminate.
  destruct (partial_if optim_redundancy Deadcode.transf_program p12) as [p13|e] eqn:P13; simpl in T; try discriminate.
  destruct (Allocation.transf_program p13) as [p15|e] eqn:P15; simpl in T; try discriminate.
  set (p16 := Tunneling.tunnel_program p15) in *.
  destruct (Linearize.transf_program p16) as [p17|e] eqn:P17; simpl in T; try discriminate.
  set (p18 := CleanupLabels.transf_program p17) in *.
  destruct (partial_if debug Debugvar.transf_program p18) as [p19|e] eqn:P19; simpl in T; try discriminate.
  destruct (Stacking.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
  assert (ok_ge p7).
  { subst p7. unfold total_if. destruct (optim_tailcalls tt); [|apply ok_make_prog].
    unfold Tailcall.transf_program. apply transform_ok; auto.
    2: { apply ok_make_prog. }
    simpl. eauto. }
  assert (ok_ge p9).
  { subst p9. unfold Renumber.transf_program. apply transform_ok; simpl; eauto. }
  assert (ok_ge p10).
  { subst p10. unfold total_if. destruct (optim_constprop tt); [|auto].
    unfold Constprop.transf_program. apply transform_ok; simpl; eauto. }
  assert (ok_ge p11).
  { subst p11. unfold total_if. destruct (optim_constprop tt); [|auto].
    unfold Constprop.transf_program. apply transform_ok; simpl; eauto. }
  assert (ok_ge p12).
  { unfold partial_if in P12. destruct (optim_CSE tt); try solve [inv P12; auto].
    unfold CSE.transf_program in P12. eapply transform_partial_ok; simpl; eauto.
    simpl. intros f ft H3. repeat do_ok. eauto. }
  assert (ok_ge p13).
  { unfold partial_if in P13. destruct (optim_redundancy tt); try solve [inv P13; auto].
    unfold Deadcode.transf_program in P13. eapply transform_partial_ok; eauto.
    simpl. intros f ft H4. repeat do_ok. eauto.  }
  assert (ok_ge p15).
  { unfold Allocation.transf_program in P15. eapply transform_partial_ok; eauto.
    simpl. intros f ft H5. repeat do_ok. eauto. }
  assert (ok_ge p16).
  { subst p16. unfold Tunneling.tunnel_program. apply transform_ok; simpl; eauto. }
  assert (ok_ge p17).
  { unfold Linearize.transf_program in P17. eapply transform_partial_ok; eauto.
    simpl. intros f ft H7. repeat do_ok. eauto. }
  assert (ok_ge p18).
  { subst p18. unfold CleanupLabels.transf_program. apply transform_ok; simpl; eauto. }
  assert (ok_ge p19).
  { unfold partial_if in P19. destruct (debug tt); try solve [inv P19; auto].
    unfold Debugvar.transf_program in P19. eapply transform_partial_ok; eauto.
    simpl. intros f ft H9. repeat do_ok. eauto. }
  assert (ok_ge p20).
  { unfold Stacking.transf_program in P20. eapply transform_partial_ok; eauto.
    simpl. intros f ft H10. repeat do_ok. eauto. }
  unfold Asmgen.transf_program in T. eapply transform_partial_ok; eauto.
  simpl. intros f ft H11. repeat do_ok. eauto.
Qed.

    
Lemma backend_extcalls:
  forall rtlc entry ap,
    fun_backend rtlc entry = OK ap ->
    asm_external_prims (Globalenvs.Genv.globalenv ap).
Proof.
  intros rtlc entry ap H. apply backend_ok in H. inv H.
  unfold asm_external_prims. intros b ef H.
  unfold Globalenvs.Genv.globalenv in H. simpl in H.
  unfold Globalenvs.Genv.find_funct_ptr in H.
  unfold Globalenvs.Genv.find_def in H.
  unfold Globalenvs.Genv.genv_defs in H. simpl in H.
  repeat (destruct b; simpl in H; try solve [inv H]);
    try solve [inv H; econstructor; unfold EF; eauto].
Qed.

Lemma backend_wf:
  forall rtlc entry ap,
    fun_backend rtlc entry = OK ap ->
    asm_ge_wf (Globalenvs.Genv.globalenv ap).
Proof.
  intros rtlc entry ap H. split.
  eapply backend_extcalls; eauto.
  eapply no_builtin; eauto.
Qed.



(* Qed stuck if we do inversion *)
Lemma init_invert:
  forall init rtlc ra ida next,
    (do asms <- OK init; do prog <- fun_backend rtlc ra; OK asms # ida <- prog) = OK next ->
    exists prog, fun_backend rtlc ra = OK prog /\ next = init # ida <- prog.
Proof.
  unfold bind. intros init rtlc ra ida next H.
  destruct (fun_backend rtlc ra); inv H. exists p. split; auto.
Qed. 

Lemma compiled_wf:
  forall rtl asm contid asmf,
    rtl_backend rtl = OK asm ->
    monad.asm_get asm contid = Some asmf ->
    asm_ge_wf (ASMinterpreter.build_genv asmf).
Proof.
  assert (forall rtlc l init result id ap,
             list_norepet (map fst l) ->
               fold_left
                 (fun (a : res (PTree.t Asm.program)) (p : positive * positive) =>
                    do asms <- a; do prog <- fun_backend rtlc (snd p); OK asms # (fst p) <- prog)
                 l (OK init) = OK result ->
               init # id = None ->
               result # id = Some ap ->
               exists r, In (id, r) l /\ fun_backend rtlc r = OK ap).
  { intros rtlc l. induction l; intros.
    - simpl in H. inv H0. rewrite H1 in H2. inv H2.
    - inv H. destruct a as [ida ra].
      rewrite fold_left_cons in H0.
      assert (exists i, (do asms <- OK init; do prog <- fun_backend rtlc (snd (ida,ra)); OK asms # (fst (ida,ra)) <- prog) = OK i).
      { eapply fold_left_ok; eauto. }
      destruct H as [newinit INIT]. rewrite INIT in H0. 
      poseq_destr id ida.
      + exists ra. split. left. auto. simpl in H5.
        eapply fold_set_monotonic with (contid:=ida) in H0; auto.
        destruct H0 as [initr [ISOK SAME]]. inv ISOK. apply init_invert in INIT.
        destruct INIT as [prog [ISOK INIT]]. subst. simpl in SAME. rewrite PTree.gss in SAME.
        rewrite SAME in H2. inv H2. simpl in ISOK. auto.
      + eapply IHl in H0; eauto. destruct H0 as [r [IN BACK]].
        exists r. split; auto. simpl. right. auto.
        apply init_invert in INIT.  destruct INIT as [prog [ISOK INIT]]. subst. simpl.
        rewrite PTree.gso; auto. }
  intros rtl asm contid asmf H1 H2. unfold asm_get in H2.
  unfold rtl_backend in H1. destruct rtl as [[[fid rtlc] rtle] cont]. repeat do_ok.
  destruct contid.
  - inv H2. eapply backend_wf; eauto.
  - simpl in H2. unfold cont_backend in HDO0. rewrite PTree.fold_spec in HDO0.
    eapply H in HDO0; eauto.
    2: { apply PTree.elements_keys_norepet. }
    (* 2: {rewrite PTree.gempty. auto. } *)
    destruct HDO0 as [r [IN BACK]]. eapply backend_wf; eauto.
Qed.



(** * Simulation relation, index, order  *)
(* Another try using dependent types *)
Record simul_index (rtl:RTLfun) (asm:asm_fun): Type := mkindex {
  index_type: Type;
  order: index_type -> index_type -> Prop;
  index: index_type;
  wf: well_founded order;
  match_states: index_type -> RTL.state -> Asm.state -> Prop;
  asmf: Asm.program;
  entrylbl: label;
  contid: cont_id;
  asm_get: asm_get asm contid = Some asmf;
  rtl_get: rtl_get_entry rtl contid = Some entrylbl;
  prop: Smallstep.bsim_properties (RTL.semantics (make_prog (rtlcode rtl) entrylbl)) (Asm.semantics asmf)
                                  index_type order match_states
                                                         }.

Definition change_index rtl asm (e:simul_index rtl asm) (i:(index_type rtl asm e)) : simul_index rtl asm :=
  mkindex rtl asm
          (index_type rtl asm e)
          (order rtl asm e)
          i
          (wf rtl asm e)
          (match_states rtl asm e)
          (asmf rtl asm e)
          (entrylbl rtl asm e)
          (contid rtl asm e)
          (asm_get rtl asm e)
          (rtl_get rtl asm e)
          (prop rtl asm e).


Inductive backend_index {rtl:RTLfun} {asm:asm_fun}: Type :=
| Refl: backend_index
| Simul (i: simul_index rtl asm): backend_index.

(* This order decreases whent he simul order decreases *)
Inductive backend_order {rtl:RTLfun} {asm:asm_fun}: backend_index -> backend_index -> Prop :=
| simul_ord :
    forall idx i,
      (order rtl asm idx) i (index rtl asm idx) ->
      (backend_order) (Simul (change_index rtl asm idx i)) (Simul idx).

Lemma acc_simul_order:
  forall idxt (ord:idxt -> idxt -> Prop) i
    (WF: well_founded ord),
    Acc ord i -> forall rtl asm ms asmf lbl id aget rget prop, Acc backend_order (Simul (mkindex rtl asm idxt ord i WF ms asmf lbl id aget rget prop)).
Proof.
  induction 1. intros.
  apply Acc_intro. intros. inv H1. 
  apply H0. auto.
Qed.

Lemma backend_order_wf:
  forall rtl asm,
    well_founded (@backend_order rtl asm).
Proof.
  intros rtl asm. unfold well_founded. intros a. destruct a.
  - apply Acc_intro. intros y H. inv H.
  - apply Acc_intro. intros y H.
    destruct y; inv H. unfold change_index. apply acc_simul_order.
    destruct i. unfold well_founded in wf0. simpl. apply wf0.
Qed.


(* The opt program does not encounter Halt_RTL states since the RTL has been compiled *)
Definition not_rtl (m:mixed_state) : Prop :=
  match m with
  | (sync, mut) =>
    match sync with
    | Halt_RTL _ _ => False
    | Halt_Block _ => False
    | _ => True
    end
  end.

Inductive backend_match_states (rtl:RTLfun) (asm:asm_fun):
  @backend_index rtl asm -> mixed_state -> mixed_state -> Prop :=
| match_refl:
    forall ms
      (NO_RTL: not_rtl ms),
      backend_match_states rtl asm Refl ms ms
| match_simul:
    forall mut rge age rtls asms (i:simul_index rtl asm)
      (RGE: rge = Globalenvs.Genv.globalenv (make_prog (rtlcode rtl) (entrylbl rtl asm i)))
      (AGE: age = Globalenvs.Genv.globalenv (asmf rtl asm i))
      (GE_WF: ge_wf rge)
      (ST_WF: rtl_state_wf rtls)
      (AGE_WF: asm_ge_wf age)
      (SIMUL_MATCH: (match_states rtl asm i) (index rtl asm i) rtls asms),
      backend_match_states rtl asm (Simul i) (Halt_RTL rge rtls,mut) (Halt_ASM age asms,mut).
    

Lemma init_asm_ok:
  forall xs asmp,
    ASMinterpreter.init_nat_state asmp = OK xs <->
    Asm.initial_state asmp xs.
Proof.
  intros xs asmp. split; intros H.
  - unfold ASMinterpreter.init_nat_state in H. repeat do_ok.
    constructor. auto.
  - unfold ASMinterpreter.init_nat_state. inv H. rewrite H0. simpl. auto.
Qed.

Lemma n_load_same:
  forall fid ms code asmf asmcont ms' asm_prog, 
    n_load_code (Call_id fid) (ms, code # fid <- (asmf, asmcont)) =
    SOK asm_prog (ms', code # fid <- (asmf, asmcont)) ->
    asm_prog = asmf /\ ms = ms'.
Proof.
  intros fid ms code asmf0 asmcont ms' asm_prog H. unfold n_load_code in H.
  repeat sdo_ok. unfold n_load_prog_code in HDO. simpl in HDO.
  rewrite PTree.gss in HDO. inv HDO. simpl. auto.
Qed.

Lemma n_load_cont_same:
  forall fid cont ms code asmf asmcont ms' asm_prog, 
    n_load_code (Cont_id fid cont) (ms, code # fid <- (asmf, asmcont)) =
    SOK asm_prog (ms', code # fid <- (asmf, asmcont)) ->
    (asmcont # cont) = Some asm_prog /\ ms = ms'.
Proof.
  intros fid cont ms code asmf0 asmcont ms' asm_prog H. unfold n_load_code in H.
  repeat sdo_ok. unfold n_load_prog_code in HDO. simpl in HDO.
  rewrite PTree.gss in HDO. inv HDO. simpl in H.
  destruct (asmcont # cont) eqn:CONT; inv H. split; auto.
Qed.




Require Import Integers.
Require Import ASMinterpreter.
Require Import Values.
Require Import Globalenvs.
(* The primitives that only depends on the mutables, not on the native codes *)
Inductive mut_prim : forall T:Type, primitive T -> Prop :=
| mut_save: forall i, mut_prim unit (Prim_Save i)
| mut_load: mut_prim int (Prim_Load)
| mut_memset: forall x y, mut_prim unit (Prim_MemSet x y)
| mut_memget: forall x, mut_prim int (Prim_MemGet x)
| mut_closesf: forall a b c, mut_prim unit (Prim_CloseSF a b c)
| mut_opensf: mut_prim open_sf (Prim_OpenSF)
| mut_pushirsf: forall sf, mut_prim unit (Prim_PushIRSF sf).
Arguments mut_prim [T] _.

Theorem mut_same_code:
  forall (T:Type) (p:primitive T) (t:T) (mut mut': mutables) (ac ac':asm_codes)
    (MUT: mut_prim p)
    (EXEC: exec_prim p naive_impl (mut, ac) = SOK t (mut', ac')),
    ac = ac'.
Proof.
  intros T p t mut mut' ac ac' MUT EXEC.
  destruct p; simpl; inv EXEC; inv MUT; auto. 
  - unfold n_load in H0. simpl in H0. destruct (state_stacktop mut); inv H0. auto.
  - unfold n_memset in H0. simpl in H0. destruct (Int.lt i mem_size); inv H0. auto.
  - unfold n_memget in H0. simpl in H0. destruct (Int.lt i mem_size); inv H0.
    destruct ((state_mem mut) # (pos_of_int i)); inv H1. auto.
  - unfold n_open_stackframe in H0. simpl in H0. destruct (state_stacktop mut); inv H0.
    destruct (state_stack mut); inv H1; auto. destruct s; inv H0; auto.
    destruct a, p, p. inv H1. auto.
  - unfold n_push_interpreter_stackframe in H0. simpl in H0. destruct (state_stacktop mut); inv H0. auto.
Qed.

Theorem mut_same_effect:
  forall (T:Type) (p:primitive T) (t:T) (mut mut':mutables) (ac ac':asm_codes)
    (MUT: mut_prim p)
    (EXEC: exec_prim p naive_impl (mut, ac) = SOK t (mut', ac')),
    forall ac'', exec_prim p naive_impl (mut, ac'') = SOK t (mut', ac'').
Proof.
  intros T p t mut mut' ac ac' MUT EXEC.
  destruct p; inv EXEC; inv MUT; simpl; auto.
  - unfold n_load in *. simpl in *. destruct (state_stacktop mut); inv H0. auto.
  - unfold n_memset in *. simpl in *.
    destruct (Int.lt i mem_size); inv H0. auto.
  - unfold n_memget in *. simpl in *.
    destruct (Int.lt i mem_size); inv H0.
    destruct ((state_mem mut) # (pos_of_int i)); inv H1. auto.
  - unfold n_open_stackframe in *. simpl in *. destruct (state_stacktop mut); inv H0.
    destruct (state_stack mut); inv H1. auto. destruct s; inv H0. auto.
    destruct a, p, p. inv H1. auto.
  - unfold n_push_interpreter_stackframe in *. simpl in *. destruct (state_stacktop mut); inv H0. auto.
Qed.

Theorem same_mut:
  forall (T:Type) (sprim: smon T) (p:primitive T) (t:T) (mut mut':mutables) (ac ac':asm_codes)
    (EXEC: sprim (mut, ac) = SOK t (mut', ac'))
    (PRIM: sprim = exec_prim p naive_impl)
    (MUT: mut_prim p),
  forall ac'', sprim (mut, ac'') = SOK t (mut', ac'').
Proof.
  intros T sprim p t mut mut' ac ac' EXEC PRIM MUT ac''.
  exploit mut_same_effect; eauto.
  - rewrite <- PRIM. apply EXEC.
  - intros H. rewrite <- PRIM in H. apply H.
Qed.

Theorem mut_twice:
  forall (T:Type) (p:primitive T) (t1 t2:T) (mut mut1 mut2:mutables) (ac ac':asm_codes)
    (MUT:mut_prim p)
    (EXEC1: exec_prim p naive_impl (mut, ac) = SOK t1 (mut1, ac))
    (EXEC2: exec_prim p naive_impl (mut, ac') = SOK t2 (mut2, ac')),
    t1 = t2 /\ mut1 = mut2.
Proof.
  intros T f t1 t2 mut mut1 mut2 ac ac' MUT EXEC1 EXEC2.
  eapply mut_same_effect in EXEC1; eauto. rewrite EXEC1 in EXEC2.
  inv EXEC2. auto.
Qed.


(* Typing free monads that only act on mutables *)
Inductive mut_monad {T:Type}: free T -> Prop :=
| m_pure:
    forall (t:T),
      mut_monad (pure t)
| m_error:
    forall (e:errmsg),
      mut_monad (ferror e)
| m_impure:
    forall {R:Type} (p:primitive R) (cont: R -> free T)
      (MUT_CONT: forall (r:R), mut_monad (cont r))
      (MUT_PRIM: mut_prim p),
      mut_monad (impure p cont).

Lemma mut_bind:
  forall (A B:Type) (f:free A) (g: A -> free B)
    (MUT_A: mut_monad f)
    (MUT_B: forall a, mut_monad (g a)),
    mut_monad (fbind f g).
Proof.
  intros A B f. generalize dependent B.
  induction f; intros.
  - simpl. auto.
  - simpl. repeat constructor.
    2: { inv MUT_A. apply Classical_Prop.EqdepTheory.inj_pair2 in H2. subst. auto. }
    intros r. apply H; auto. inv MUT_A.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H3. subst. auto.
  - simpl. constructor.
Qed.

Lemma mut_try:
  forall (A:Type) (o: option A) (s:string),
    mut_monad (try_option o s).
Proof.
  intros A o s. destruct o; simpl; constructor.
Qed.

Lemma mut_fret':
  forall (A:Type) (r:res A),
    mut_monad (fret' r).
Proof.
  intros A r. unfold fret'. destruct r; constructor.
Qed.

Ltac mut_auto':=
  match goal with
  | [ |- context[mut_monad(fret (?x))]] => constructor
  | [ |- context[mut_monad(ferror (?x))]] => constructor
  | [ |- context[mut_monad(pure (?x))]] => constructor
  | [ |- context[mut_monad(impure ?x ?y)]] => constructor
  | [ |- context[mut_prim ?x]] => constructor
  | [ |- context[mut_monad (fprim ?x)]] => constructor
  | [ |- context[mut_monad(fret' (?x))]] => apply mut_fret'
  | [ |- context[mut_monad(try_option ?x ?y)]] => apply mut_try
  | [ |- context[mut_monad(fbind ?x ?y)]] => apply mut_bind
  | [ |- context[mut_monad(fbind2 ?x ?y)]] => apply mut_bind
  | [ |- context[mut_monad(fbind3 ?x ?y)]] => apply mut_bind
  | [ |- context[mut_monad(fbind4 ?x ?y)]] => apply mut_bind
  | [ |- context[mut_monad(let (x, y) := ?z in _)]] => destruct z
  | [ |- context[mut_monad (match ?x with
                            | _ => _
                            end)]] => destruct x
  end.

Ltac mut_auto := intros; mut_auto'.


Theorem mut_monad_same_effect:
  forall (T:Type) (f:free T) (t:T) (mut mut':mutables) (ac ac':asm_codes)
    (MUT: mut_monad f)
    (EXEC: exec f naive_impl (mut, ac) = SOK t (mut', ac')),
    forall ac'', exec f naive_impl (mut, ac'') = SOK t (mut', ac'').
Proof.
  intros T f. induction f; intros; inv EXEC; auto.
  (* left with the recursive case *)
  repeat sdo_ok. unfold sbind.
  assert (MUT_PRIM: mut_prim prim).
  { inv MUT. apply Classical_Prop.EqdepTheory.inj_pair2 in H3. subst. auto. }
  assert (MUT_CONT: forall r, mut_monad (cont r)).
  { inv MUT. apply Classical_Prop.EqdepTheory.inj_pair2 in H4. subst. auto. }
  destruct n. exploit mut_same_effect; eauto. intros. rewrite H0.
  eapply H; eauto.
Qed.

Theorem mut_monad_same_code:
  forall (T:Type) (f:free T) (t:T) (mut mut':mutables) (ac ac':asm_codes)
    (MUT:mut_monad f)
    (EXEC: exec f naive_impl (mut, ac) = SOK t (mut', ac')),
    ac = ac'.
Proof.
  intros T f. induction f; intros; inv EXEC; auto.
  repeat sdo_ok. assert (MUT_PRIM: mut_prim prim).
  { inv MUT. apply Classical_Prop.EqdepTheory.inj_pair2 in H3. subst. auto. }
  assert (MUT_CONT: forall r, mut_monad (cont r)).
  { inv MUT. apply Classical_Prop.EqdepTheory.inj_pair2 in H4. subst. auto. }
  destruct n. apply H in H1; auto. subst. apply mut_same_code in HDO; auto.
Qed.

Theorem mut_monad_twice:
  forall (T:Type) (f:free T) (t1 t2:T) (mut mut1 mut2:mutables) (ac ac':asm_codes)
    (MUT:mut_monad f)
    (EXEC1: exec f naive_impl (mut, ac) = SOK t1 (mut1, ac))
    (EXEC2: exec f naive_impl (mut, ac') = SOK t2 (mut2, ac')),
    t1 = t2 /\ mut1 = mut2.
Proof.
  intros T f t1 t2 mut mut1 mut2 ac ac' MUT EXEC1 EXEC2. eapply mut_monad_same_effect in EXEC1; eauto. rewrite EXEC1 in EXEC2.
  inv EXEC2. auto.
Qed.


Lemma mut_get_args:
  forall (a:call_loc),
    mut_monad (get_args a).
Proof. intros a. unfold get_args. repeat mut_auto. unfold pop_args.
       intros a0. generalize (nil:list int). induction a0; simpl; repeat mut_auto. auto.
Qed.

Lemma mut_callee:
  forall cl, mut_monad (get_callee cl).
Proof. intros. unfold get_callee. repeat mut_auto. Qed.

Lemma mut_set_args:
  forall cl, mut_monad (set_up_args cl).
Proof. intros. unfold set_up_args. repeat mut_auto.
       induction l; simpl; repeat mut_auto. auto.
Qed.

Lemma mut_target:
  forall dl, mut_monad (get_target dl).
Proof. intros. unfold get_target. repeat mut_auto. Qed.

Lemma mut_get_retval:
  forall rl, mut_monad (get_retval rl).
Proof. intros. unfold get_retval. repeat mut_auto. Qed.

(* Lemma mut_set_retval: *)
(*   forall rl, mut_monad (set_up_retval rl). *)
(* Proof. intros. unfold set_up_retval. repeat mut_auto. Qed. *)



(* before typing, this was hard to do *)
(* because defined recursively *)
Lemma mut_get_varmap:
  forall (n:nat) l,
    mut_monad (get_varmap n l).
Proof.
  intros n. induction n; simpl; repeat mut_auto; auto.
Qed.

Lemma mut_build_rm:
  forall (l:deopt_loc),
    mut_monad (build_rm l).
Proof.
  intros l. unfold build_rm. repeat mut_auto. apply mut_get_varmap.
Qed.


(* Trying a more complicated monad *)
Lemma mut_ir:
  forall (irs:ir_state),
    mut_monad (IRinterpreter.ir_step irs).
Proof.
  intros irs. unfold IRinterpreter.ir_step. repeat mut_auto.
  unfold IRinterpreter.ir_int_step. repeat mut_auto.
Qed.  


Lemma mut_prim_sem:
  forall name sg a,
    mut_monad (prim_sem_dec name sg a).
Proof.
  intros name sg a. unfold prim_sem_dec.
  repeat mut_auto.
Qed.

Lemma mut_asm:
  forall ge s,
    mut_monad (asm_int_step ge s).
Proof.
  intros ge s. unfold asm_int_step. repeat mut_auto.
  unfold asm_step. repeat mut_auto.
  unfold ext_prim_sem. repeat mut_auto. apply mut_prim_sem.
Qed.

Ltac exec_match:=
  match goal with
  | [ H: exec (match ?x with | _ => _ end) ?i ?s = ?r |- _] => destruct x eqn:DES; inv H
  end.


Lemma safe_step_rtl:
  forall p rtl nc rge rtls ms,
    safe (mixed_sem p rtl nc AnchorOff) (Halt_RTL rge rtls, ms) ->
    exists t s', (mixed_step AnchorOff p rtl nc) (Halt_RTL rge rtls, ms) t s'.
Proof.
  intros p rtl nc rge rtls ms H. unfold safe in H.
  assert (Star (mixed_sem p rtl nc AnchorOff) (Halt_RTL rge rtls, ms) E0 (Halt_RTL rge rtls, ms)) by apply star_refl.
  specialize (H (Halt_RTL rge rtls, ms) H0). destruct H as [[r FINAL]|[t [s' STEP]]].
  - inv FINAL.
  - exists t. exists s'. auto.
Qed.


Lemma safe_step_call:
  forall p rtl nc loc ms,
    safe (mixed_sem p (Some rtl) nc AnchorOff) (S_Call loc, ms) ->
    exists t s', (mixed_step AnchorOff p (Some rtl) nc) (S_Call loc, ms) t s'.
Proof.
  intros p rtl nc loc ms H.
  unfold safe in H. specialize (H (S_Call loc, ms)).
  exploit H. apply star_refl. intros [[r FINAL]|[t [s' STEP]]].
  inv FINAL.
  exists t. exists s'. auto.
Qed.

Lemma safe_step_return:
  forall p codsrc asmf fid rtlc rtle cont contlbl retreg ms ms1 ms2 ms3 retval loc (* s' *) ,
    exec (get_retval loc) naive_impl (ms, codsrc # (pos_of_int fid) <- asmf) = SOK retval (ms1, codsrc # (pos_of_int fid) <- asmf) ->
    n_open_stackframe (ms1, codsrc # (pos_of_int fid) <- asmf) = SOK (nat_sf fid contlbl retreg) (ms2, codsrc # (pos_of_int fid) <- asmf) ->
    n_save retval (ms2, codsrc # (pos_of_int fid) <- asmf) = SOK tt (ms3, codsrc # (pos_of_int fid) <- asmf) ->
    n_check_compiled (pos_of_int fid) (ms3, codsrc) = SOK Not_compiled (ms3, codsrc) ->
    safe (mixed_sem p (Some (inl (pos_of_int fid, rtlc, rtle, cont))) codsrc AnchorOff) (S_Return loc, ms) ->
    exists ge rtls ms',
      (mixed_step AnchorOff p (Some (inl (pos_of_int fid, rtlc, rtle, cont))) codsrc) (S_Return loc, ms) E0
                                                                            (Halt_RTL ge rtls, ms').
Proof.
  intros p codsrc asmf0 fid rtlc rtle cont contlbl retreg ms ms1 ms2 ms3 retval loc GET OPEN SAVE CHECK SAFE.
  unfold safe in SAFE. specialize (SAFE (S_Return loc, ms)). exploit SAFE.
  apply star_refl. intros [[r FINAL]|[t [s'' STEP]]].
  inv FINAL. inv STEP; simpl in *.
  - assert (ms4 = ms1). { eapply mut_monad_twice; eauto. eapply mut_get_retval. } subst. (* return IR *)
    unfold n_open_stackframe in *. simpl in OPEN_SF, OPEN.
    destruct (state_stacktop ms1) eqn:TOP; inv OPEN.
    destruct (state_stack ms1) eqn:STK; inv H0.
    destruct s; inv H1. destruct a as [[[sf1 sf2]sf3] sf4]. inv OPEN_SF. 
  -                             (* return x86 *)
    assert (ms1 = ms4). { eapply mut_monad_twice; eauto. apply mut_get_retval. } subst.
    unfold n_open_stackframe in *. simpl in OPEN_SF, OPEN.
    destruct (state_stacktop ms4) eqn:TOP; inv OPEN.
    destruct (state_stack ms4) eqn:STK; inv H0.
    destruct s; inv H1. destruct a as [[[sf1 sf2]sf3] sf4]. inv OPEN_SF. inv H0.
    unfold n_check_compiled in CHECK. simpl in CHECK.
    destruct (codsrc # (pos_of_int fid)) eqn:SRC; inv CHECK. simpl in LOAD_CONT.
    unfold n_load_code in LOAD_CONT. repeat sdo_ok.
    unfold n_load_prog_code in HDO. simpl in HDO. rewrite SRC in HDO. inv HDO.
  -                             (* return RTL *)
    assert (ms1 = ms4). { eapply mut_monad_twice; eauto. apply mut_get_retval. } subst.
    unfold n_open_stackframe in *. simpl in OPEN_SF, OPEN.
    destruct (state_stacktop ms4) eqn:TOP; inv OPEN.
    destruct (state_stack ms4) eqn:STK; inv H0.
    destruct s; inv H1. destruct a as [[[sf1 sf2]sf3] sf4]. inv OPEN_SF. inv H0.
    econstructor. econstructor. econstructor.
    eapply Return_RTL; eauto. simpl.
    unfold n_open_stackframe. simpl. rewrite TOP. rewrite STK. eauto.
  - inv RTL_BLOCK.              (* return block *)
  -                             (* return EOE *)
    assert (ms1 = ms4). { eapply mut_monad_twice; eauto. apply mut_get_retval. } subst.
    unfold n_open_stackframe in *. simpl in OPEN_SF, OPEN.
    destruct (state_stacktop ms4) eqn:TOP; inv OPEN.
    destruct (state_stack ms4) eqn:STK; inv H0.
    destruct s; inv OPEN_SF. destruct a as [[[sf1 sf2]sf3] sf4]. inv H0.
Qed.

Definition match_loc_fid (fid:fun_id) (loc:call_loc) (ms:mutables) : Prop :=
  match loc with
  | ir_call fid' l => fid = fid'
  | nat_call =>
    match (state_stacktop ms) with
    | nil => False
    | i::_ => pos_of_int i = fid
    end
  end.
  

Lemma safe_step_call_rtl:
  forall p nc loc ms rtlc rtlentry cont fid,
    match_loc_fid fid loc ms ->
    safe (mixed_sem p (Some (inl (fid, rtlc, rtlentry, cont))) nc AnchorOff) (S_Call loc, ms) ->
    exists ge rtls ms',
      (mixed_step AnchorOff p (Some (inl (fid, rtlc, rtlentry, cont))) nc) (S_Call loc, ms) E0
                                                           (Halt_RTL ge rtls, ms').
Proof.
  intros p nc loc ms rtlc rtlentry cont fid MATCH H.
  unfold safe in H. specialize (H (S_Call loc, ms)).
  exploit H. apply star_refl. intros [[r FINAL]|[t [s' STEP]]].
  inv FINAL. inv STEP.
  - simpl in NOT_RTL. exfalso. apply NOT_RTL. (* callIR *)
    destruct loc; inv CALLEE.
    + simpl in MATCH. repeat sdo_ok. unfold n_load in HDO. simpl in HDO.
      destruct (state_stacktop ms) eqn:TOP; inv HDO. auto.
    + simpl in MATCH. f_equal. auto.
  - simpl in NOT_RTL. exfalso. apply NOT_RTL. auto. (* callx86 *)
    destruct loc; inv CALLEE.
    + simpl in MATCH. repeat sdo_ok. unfold n_load in HDO. simpl in HDO.
      destruct (state_stacktop ms); inv MATCH. inv HDO. auto.
    + simpl in MATCH. f_equal. auto.
  - inv RTL.
    exists (Globalenvs.Genv.globalenv (make_prog rtlcode0 entry)). exists rtls. exists ms3.
    eapply Call_RTL; eauto.
  - inv RTL_BLOCK.
Qed.


(** * Characterizing ASM Steps  *)
Inductive prim_step {state:Type} (i:monad_impl state) (prim:ext_primitive) (args:list int):
  Asm.genv -> Asm.state -> state -> trace -> (itret checkpoint Asm.state) -> state -> Prop :=
| halt_prim:
    forall ge rs m t newas b s s'
      (PC: rs PC = Vptr b Ptrofs.zero)
      (FINDF: Globalenvs.Genv.find_funct_ptr ge b = Some (External (EF_runtime (EF_name prim) (EF_sig prim))))
      (ARGS: extcall_arguments rs m (EF_sig prim) (intlistval args))
      (EXEC: exec (ext_prim_sem rs m (EF_name prim) (EF_sig prim)) i s = SOK (t, newas) s'),
      prim_step i prim args ge (Asm.State rs m) s t (Halt newas) s'.


Lemma prim_step_halt_asm:
  forall prim ge asms1 ms1 t asms2 ms2 args,
    prim_step naive_impl prim args ge asms1 ms1 t (Halt asms2) ms2 ->
    exists (ret:int),
      Asm.step ge asms1 (Event_syscall (EF_name prim) (intlisteval args) (EVint ret)::nil) asms2 /\
      exec (prim_sem_dec (EF_name prim) (EF_sig prim) (intlistval args)) naive_impl ms1 = SOK (t, ret) ms2.
Proof.
  intros prim ge asms1 ms1 t asms2 ms2 args H. inv H. unfold ext_prim_sem in EXEC.
  repeat sdo_ok. destruct p as [t r]. unfold prim_sem_dec in HDO0.
  rewrite <- extcall_arguments_eq in HDO1.
  destruct prim; simpl in HDO0; repeat sdo_ok; try solve[inv HDO0].
  - exists Int.zero. 
    assert (l = intlistval args) by (eapply extcall_arguments_determ; eauto). split.
    + eapply exec_step_external; eauto. simpl.
      replace ("_SAVE"%string) with (EF_name EF_save); auto. apply ext_prim_axiom.      
      exists args. exists Int.zero. repeat (split; auto).
      simpl. destruct args; subst; inv HDO0.
      destruct args; inv H0. repeat constructor.
    + subst. unfold prim_sem_dec. simpl. rewrite HDO0. simpl.
      unfold sbind. rewrite HDO2. auto.
  - exists r. 
    assert (l = intlistval args) by (eapply extcall_arguments_determ; eauto). split.
    + eapply exec_step_external; eauto. simpl.
      replace ("_LOAD"%string) with (EF_name EF_load); auto. apply ext_prim_axiom.
      exists args. exists r. repeat (split; auto).
      simpl. destruct args; subst; inv HDO0. constructor.
    + subst. unfold prim_sem_dec. simpl. rewrite HDO0. simpl.
      unfold sbind. rewrite HDO2. auto.
  - exists Int.zero. 
    assert (l = intlistval args) by (eapply extcall_arguments_determ; eauto). split.
    + eapply exec_step_external; eauto. simpl.
      replace ("_MEMSET"%string) with (EF_name EF_memset); auto. apply ext_prim_axiom.
      exists args. exists Int.zero. repeat (split; auto).
      destruct args; subst; inv HDO0. destruct args; try destruct args; inv H0. simpl. repeat constructor.
    + subst. unfold prim_sem_dec. simpl. rewrite HDO0. simpl.
      unfold sbind. rewrite HDO2. auto.
  - exists r. 
    assert (l = intlistval args) by (eapply extcall_arguments_determ; eauto). split.
    + eapply exec_step_external; eauto. simpl.
      replace ("_MEMGET"%string) with (EF_name EF_memget); auto. apply ext_prim_axiom.
      exists args. exists r. repeat (split; auto).
      destruct args; try destruct args; subst; inv HDO0. simpl. repeat constructor. 
    + subst. unfold prim_sem_dec. simpl. rewrite HDO0. simpl.
      unfold sbind. rewrite HDO2. auto.
  - destruct p as [[caller cont_lbl] retreg]. simpl in HDO2. exists Int.zero.
    assert (l = intlistval args) by (eapply extcall_arguments_determ; eauto). split.
    + eapply exec_step_external; eauto. simpl.
      replace ("_CLOSE"%string) with (EF_name EF_close); auto. apply ext_prim_axiom.
      exists args. exists Int.zero. repeat (split; auto).
      destruct args; try destruct args; try destruct args; try destruct args; inv HDO0; inv H1.
      repeat constructor.
    + subst. unfold prim_sem_dec. simpl. rewrite HDO0. simpl.
      unfold sbind. rewrite HDO2. auto.
  - exists Int.zero.
    assert (l = intlistval args) by (eapply extcall_arguments_determ; eauto). split.
    + eapply exec_step_external; eauto. simpl.
      replace ("_PRINT"%string) with (EF_name EF_print); auto. apply ext_prim_axiom.
      exists args. exists Int.zero. repeat (split; auto).
      destruct args; try destruct args; inv HDO0; inv H1.
      repeat constructor.
    + subst. unfold prim_sem_dec. simpl. rewrite HDO0. simpl. auto.
Qed.


Inductive internal_step (ge : genv) : Asm.state -> trace -> Asm.state -> Prop :=
| step_internal : forall (b : block) (ofs : ptrofs) (f : Asm.function) (i : Asm.instruction)
                    (rs : preg -> val) (m : Memory.Mem.mem) (rs' : regset) 
                    (m' : Memory.Mem.mem),
    rs PC = Vptr b ofs ->
    Globalenvs.Genv.find_funct_ptr ge b = Some (Internal f) ->
    find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
    exec_instr ge f i rs m = Next rs' m' ->
    internal_step ge (Asm.State rs m) E0 (Asm.State rs' m').

Lemma internal_step_asm:
  forall ge s1 t s2, internal_step ge s1 t s2 -> Asm.step ge s1 t s2.
Proof.
  intros ge s1 t s2 H. inv H. eapply exec_step_internal; eauto.
Qed.

Theorem internal_interp:
  forall (state:Type) ge s1 t s2 (i:monad_impl state) (s:state),
    internal_step ge s1 t s2 ->
    exec (asm_step ge s1) i s = SOK (t, Halt s2) s.
Proof.
  intros state ge s1 t s2 i s H. inv H.
  unfold asm_step. destruct (is_final (Asm.State rs m)) eqn:FINAL.
  { rewrite is_final_correct in FINAL.  inv FINAL. rewrite H5 in H0. inv H0. }
  rewrite H0. rewrite H1. rewrite H2. destruct i0; try rewrite H3; auto.
  simpl in H3. inv H3.
Qed.


Theorem asm_step_halt_correct:
  forall (state:Type) (age:Asm.genv) (asms asms':Asm.state) (i:monad_impl state) (t:trace) (s s':state),
    asm_ge_wf age ->
    exec (asm_step age asms) i s = SOK (t, Halt asms') s' ->
    (internal_step age asms t asms' /\ s = s' /\ t = E0) \/
    exists prim args, prim_step i prim args age asms s t (Halt asms') s'. 
Proof.
  intros state age asms asms' i t s s' AGEWF H.
  unfold asm_step in H.
  destruct (is_final asms) eqn:FINAL.
  { inv H. }
  destruct asms; inv H. destruct (r PC) eqn:PC; try solve[inv H1].
  destruct (Globalenvs.Genv.find_funct_ptr age b) eqn:FIND; inv H1.
  destruct f.
  - left. destruct (find_instr (Ptrofs.unsigned i0) (fn_code f)) eqn:FINDI.
    2: { inv H0. }
    destruct i1; inv H0; try exec_match;
      try (split; try eapply step_internal; eauto).
  - right. destruct e; inv H0.
    apply AGEWF in FIND as PRIM. destruct PRIM as [p EF]. inv EF. exists p.
    destruct (Ptrofs.eq i0 Ptrofs.zero) eqn:ZERO; inv H1.
    apply Ptrofs.same_if_eq in ZERO. subst i0. repeat sdo_ok. destruct p0 as [t asms].
    unfold ext_prim_sem in HDO; repeat sdo_ok.
    destruct p; try inv HDO; unfold prim_sem_dec in HDO1; simpl in HDO1; repeat sdo_ok; inv HDO0.
    + exists (i0::nil). econstructor; eauto.
      * rewrite extcall_arguments_eq. destruct l; try destruct l; try destruct v; inv HDO1. simpl. auto.
      * simpl. unfold ext_prim_sem. rewrite H0. simpl. unfold prim_sem_dec. simpl.
        rewrite HDO1. simpl. unfold sbind, sret. rewrite H1. auto.
    + exists nil. econstructor; eauto.
      * rewrite extcall_arguments_eq. destruct l; inv HDO1. simpl. auto.
      * simpl. unfold ext_prim_sem. rewrite H0. simpl. unfold prim_sem_dec. simpl.
        rewrite HDO1. simpl. unfold sbind, sret. rewrite H1. auto.
    + destruct p as [x y]. simpl in H1. exists (x::y::nil). econstructor; eauto.
      * rewrite extcall_arguments_eq.
        destruct l; try destruct l; try destruct l; try destruct v; try destruct v0; inv HDO1. simpl. auto.
      * simpl. unfold ext_prim_sem. rewrite H0. simpl. unfold prim_sem_dec. simpl.
        rewrite HDO1. simpl. unfold sbind, sret. rewrite H1. auto.
    + exists (i0::nil). econstructor; eauto.
      * rewrite extcall_arguments_eq. destruct l; try destruct l; try destruct v; inv HDO1. simpl. auto.
      * simpl. unfold ext_prim_sem. rewrite H0. simpl. unfold prim_sem_dec. simpl.
        rewrite HDO1. simpl. unfold sbind, sret. rewrite H1. auto.
    + destruct p as [[a' b'] c']. exists (a'::b'::c'::nil). econstructor; eauto.
      * rewrite extcall_arguments_eq.
        destruct l; try destruct l; try destruct l; try destruct l; try destruct v, v0, v1; inv HDO1.
        simpl in H1. simpl. auto.
      * simpl. unfold ext_prim_sem. rewrite H0. simpl. unfold prim_sem_dec. simpl.
        rewrite HDO1. simpl. unfold sbind, sret. simpl in H1. rewrite H1. auto.
    + destruct l; try destruct l; try destruct v; inv H1. exists (i0::nil). econstructor; eauto.
      * rewrite extcall_arguments_eq. auto.
      * simpl. unfold ext_prim_sem. rewrite H0. simpl. auto.
Qed.

Theorem asm_step_done_correct:
  forall (state:Type) (age:Asm.genv) (asms:Asm.state) (i:monad_impl state) (t:trace) (r:int) (s s':state),
    asm_ge_wf age -> 
    exec (asm_step age asms) i s = SOK (t, Done r) s' ->
    Asm.final_state asms r /\ t = E0 /\ s = s'.
Proof.
  intros state age asms i t r s s' AGEWF H.
  unfold asm_step in H.
  destruct (is_final asms) eqn:FINAL.
  2: { destruct asms. destruct (r0 PC); inv H.
       destruct (Globalenvs.Genv.find_funct_ptr age b); inv H1. destruct f; inv H0.
       - destruct (find_instr (Ptrofs.unsigned i0) (fn_code f)); inv H1. repeat exec_match.
       - destruct e; inv H1. repeat exec_match. repeat sdo_ok. }
  inv H. split; auto. apply is_final_correct. auto. 
Qed.


Lemma extract_simulation:
  forall (L1 L2:Smallstep.semantics) index order match_states,
    bsim_properties L1 L2 index order match_states ->
     forall (s2 : Smallstep.state L2) (t : trace) (s2' : Smallstep.state L2),
      Smallstep.step L2 (Smallstep.globalenv L2) s2 t s2' ->
       forall (i : index) (s1 : Smallstep.state L1),
         match_states i s1 s2 ->
         Smallstep.safe L1 s1 ->
         exists (i' : index) (s1' : Smallstep.state L1),
           (Smallstep.plus (Smallstep.step L1) (Smallstep.globalenv L1) s1 t s1' \/ Smallstep.star (Smallstep.step L1) (Smallstep.globalenv L1) s1 t s1' /\ order i' i) /\ match_states i' s1' s2'.
Proof.
  intros L1 L2 index0 order0 match_states0 bsim_prop. destruct bsim_prop. auto.
Qed.

Lemma extract_final:
  forall (L1 L2:Smallstep.semantics) index order match_states,
    bsim_properties L1 L2 index order match_states ->
    forall (i : index) (s1 : Smallstep.state L1) (s2 : Smallstep.state L2) (r : int),
      match_states i s1 s2 ->
      Smallstep.safe L1 s1 ->
      Smallstep.final_state L2 s2 r ->
      exists s1' : Smallstep.state L1,
        Smallstep.star (Smallstep.step L1) (Smallstep.globalenv L1) s1 E0 s1' /\ Smallstep.final_state L1 s1' r.
Proof.
  intros L1 L2 index0 order0 match_states0 H. destruct H. auto.
Qed.

Lemma extract_prop:
  forall rtl asm
    (i:simul_index rtl asm),
    bsim_properties (RTL.semantics (make_prog (rtlcode rtl) (entrylbl rtl asm i)))
                    (Asm.semantics (asmf rtl asm i))
                    (index_type rtl asm i) (order rtl asm i) (match_states rtl asm i).
Proof.
  intros rtl asm i. destruct i; auto.
Qed.

    

Lemma extract_init_exist:
  forall (L1 L2:Smallstep.semantics) index order match_states,
    bsim_properties L1 L2 index order match_states ->
    forall s1 : Smallstep.state L1,
      Smallstep.initial_state L1 s1 ->
      exists s2 : Smallstep.state L2, Smallstep.initial_state L2 s2.
Proof.
  intros L1 L2 index0 order0 match_states0 H. destruct H. auto.
Qed.

Lemma extract_progress:
   forall (L1 L2:Smallstep.semantics) index order match_states,
     bsim_properties L1 L2 index order match_states ->
     forall (i : index) (s1 : Smallstep.state L1) (s2 : Smallstep.state L2),
       match_states i s1 s2 ->
       Smallstep.safe L1 s1 ->
       (exists r : int, Smallstep.final_state L2 s2 r) \/
       (exists (t : trace) (s2' : Smallstep.state L2), Smallstep.step L2 (Smallstep.globalenv L2) s2 t s2').
Proof.
  intros L1 L2 index0 order0 match_states0 H. destruct H. auto.
Qed.

(** * Plus splitting  *)
(* when we have a plus or a star after using a backward simulation *)
(* if we have an event then we have a plus *)
Lemma plus_or_star_is_plus:
  forall genv state (step:genv->state->trace->state->Prop) ge s1 s2 t order,
    t <> E0 ->
    (Smallstep.plus step ge s1 t s2 \/
     Smallstep.star step ge s1 t s2 /\ order) ->
    Smallstep.plus step ge s1 t s2.
Proof.
  intros genv state step ge s1 s2 t order0 H H0. destruct H0; auto.
  destruct H0. inv H0.
  - exfalso. apply H. auto.
  - eapply Smallstep.plus_left; eauto.
Qed.

(* Decomposition of a plus with a single event *)
Lemma plus_dec:
  forall genv state (step:genv->state->trace->state->Prop) ge s1 s4 e,
    Smallstep.plus step ge s1 (e::nil) s4 ->
    exists s2 s3,
      Smallstep.star step ge s1 E0 s2 /\
      step ge s2 (e::nil) s3 /\
      Smallstep.star step ge s3 E0 s4.
Proof.
  intros genv state step ge s1 s4 e H. apply Smallstep.plus_star in H.
  remember (e::nil) as t.
  induction H. inv Heqt.
  subst. destruct t1 eqn:HT1; inv H1.
  - simpl in H2. symmetry in H2. apply IHstar in H2 as Hs. destruct Hs as [s4 [s5 [STAR [STEP STAR2]]]].
    exists s4. exists s5. subst. repeat split; auto.
    eapply Smallstep.star_step; eauto.
  - destruct t; inv H4. destruct t2; inv H1.
    exists s1. exists s2. repeat split; auto.
    apply Smallstep.star_refl.
Qed.

Lemma dec_plus:
  forall genv state (step:genv->state->trace->state->Prop) ge s1 s2 s3 s4 t,
    Smallstep.star step ge s1 E0 s2 ->
    step ge s2 t s3 ->
    Smallstep.star step ge s3 E0 s4 ->
    Smallstep.plus step ge s1 t s4.
Proof.
  intros genv state step ge s1 s2 s3 s4 t STAR1 STEP STAR2.
  assert (Smallstep.plus step ge s1 t s3).
  { clear STAR2 s4. generalize dependent t. remember E0 as silent. induction STAR1; intros.
    - eapply Smallstep.plus_left; eauto. apply Smallstep.star_refl. rewrite E0_right. auto.
    - subst. destruct t1; destruct t2; inv H0.
      eapply Smallstep.plus_left with (s2:=s2); eauto.
      apply Smallstep.plus_star. apply IHSTAR1; eauto. auto. }
  clear STAR1 STEP s2.
  inv H. eapply Smallstep.plus_left; eauto.
  eapply Smallstep.star_trans; eauto. rewrite  E0_right. auto.
Qed.

Lemma dec_plus':
  forall genv state (step:genv->state->trace->state->Prop) ge s1 s2 s3 t,
    Smallstep.star step ge s1 E0 s2 ->
    step ge s2 t s3 ->
    Smallstep.plus step ge s1 t s3.
Proof.
  intros genv state step ge s1 s2 s3 t H H0. generalize dependent t.
  remember E0 as st.
  induction H; intros.
  - rewrite same_plus. apply plus_one. auto.
  - subst. destruct t1; inv H1. destruct t2; inv H3.
    apply IHstar in H2; auto. apply Smallstep.plus_star in H2.
    econstructor; eauto.
Qed.



Lemma name_inj:
  forall p1 p2:ext_primitive,
    EF_name p1 = EF_name p2 ->
    p1 = p2.
Proof.
  intros p1 p2 H. destruct p1; destruct p2; inv H; auto.
Qed.


(* ugly but otherwise Qed gets stuck *)
Lemma in_defs:
  forall F id,
    In id (map fst (@prim_defs F)) ->
    exists ef, id = EF_ident ef.
Proof.
  intros F id H. simpl in H.
  destruct H as [E|H]. { subst. exists EF_save. auto. }
  destruct H as [E|H]. { subst. exists EF_load. auto. }
  destruct H as [E|H]. { subst. exists EF_memset. auto. }
  destruct H as [E|H]. { subst. exists EF_memget. auto. }
  destruct H as [E|H]. { subst. exists EF_close. auto. }
  destruct H as [E|H]. { subst. exists EF_print. auto. }
  inv H.
Qed.

Lemma find_find:
  forall rtlc entry ef b,
    Genv.find_symbol (Genv.globalenv (make_prog rtlc entry)) (EF_ident ef) = Some b ->
    Genv.find_funct_ptr (Genv.globalenv (make_prog rtlc entry)) b = Some (External (EF ef)).
Proof.
  intros rtlc entry ef b H. destruct ef; inv H; auto.
Qed.

Lemma rtl_ge_wf:
  forall rtlc entry,
    ge_wf (Globalenvs.Genv.globalenv (make_prog rtlc entry)).
Proof.
  unfold ge_wf, find_function. intros rtlc entry. intros.
  destruct (Globalenvs.Genv.find_symbol (Globalenvs.Genv.globalenv (make_prog rtlc entry)) id) eqn:SYM; inv H.
  apply Globalenvs.Genv.find_symbol_inversion in SYM as HID. 
  destruct HID as [MAIN|IN].  
  - subst. exfalso. apply H0. auto.
  - apply in_defs in IN. destruct IN as [e ID]. exists e. subst id.
    apply find_find in SYM. rewrite SYM in H2. inv H2. auto.
Qed.


Lemma find_funct_def:
  forall F V ge b f,
    Genv.find_funct_ptr ge b = Some f ->
    @Genv.find_def F V ge b = Some (Gfun f).
Proof.
  intros F V ge b f H. unfold Genv.find_funct_ptr in H.
  destruct (Genv.find_def ge b) eqn:FIND; try destruct g; inv H.
  auto.
Qed.    

Lemma rtl_init_wf:
  forall rtlc entry rtlinit,
    rtl_code_wf rtlc -> 
    RTL.initial_state (make_prog rtlc entry) rtlinit ->
    rtl_state_wf rtlinit.
Proof.
  intros rtlc entry rtlinit H H0. inv H0.
  simpl in H2.
  assert (GEWF: ge_wf ge). { apply rtl_ge_wf. }
  apply find_funct_def in H3 as FIND.
  
  unfold Globalenvs.Genv.find_def, Globalenvs.Genv.genv_defs in FIND.
  simpl in FIND.
  unfold PTree.get in FIND. 
  (* This is a bit ugly: I go through the Tree until I find leaves, then automatically find the primitives or main *)
  repeat (destruct b; simpl in FIND; try solve [inv FIND]); inv FIND;
    repeat split; auto; econstructor; unfold EF; auto.
Qed.
  
Definition rtl_is_final (s:RTL.state) : option int :=
  match s with
  | RTL.Returnstate nil v m =>
    match v with
    | Vint r => Some r
    | _ => None
    end
  | _ => None
  end.

Lemma rtl_is_final_correct:
  forall s r,
    rtl_is_final s = Some r <-> RTL.final_state s r.
Proof.
  intros. unfold rtl_is_final. split; intros.
  - destruct s; inv H. destruct stack; inv H1. destruct v; inv H0. constructor.
  - inv H. auto.
Qed.

Lemma mixed_rtl_safety:
  forall rtls ms p rtlf ac rtlp,
    rtl_state_wf rtls ->
    ge_wf (Globalenvs.Genv.globalenv rtlp) ->
    safe (mixed_sem p rtlf ac AnchorOff) (Halt_RTL (Globalenvs.Genv.globalenv rtlp) rtls, ms) ->
    (Smallstep.safe (RTL.semantics rtlp) rtls).
Proof.
  intros rtls ms p rtlf ac rtlp STWF GEWF SAFE.
  unfold Smallstep.safe.
  intros s' STAR.
  unfold safe in SAFE. eapply silent_rtl_mixed_star in STAR; eauto.
  destruct STAR as [STAR WF]. rewrite same_star in STAR. apply SAFE in STAR.
  destruct STAR as [[r FINAL]| [t [s'' STEP]]]. inv FINAL.
  inv STEP.
  - right. exists t. exists rtls2. auto.
  - right. simpl in WF. destruct WF as [STK [prim EF]]. inv EF.
    destruct prim; inv PRIM_CALL; unfold prim_sem_dec in H0; simpl in H0; repeat sdo_ok.
    + destruct args; inv HDO1. destruct args; inv H0. destruct v; inv H1.
      econstructor. econstructor. eapply exec_function_external. simpl.      
      replace ("_SAVE"%string) with (EF_name EF_save); auto. apply ext_prim_axiom.
      exists (i::nil). exists i. repeat (split; auto). repeat constructor.
    + destruct args; inv HDO1. 
      econstructor. econstructor. eapply exec_function_external. simpl.      
      replace ("_LOAD"%string) with (EF_name EF_load); auto. apply ext_prim_axiom.
      exists (nil). exists Int.zero. repeat (split; auto). repeat constructor.
    + destruct args; try destruct args; try destruct args; try destruct v; try destruct v0; inv HDO1.
      simpl in HDO0.
      econstructor. econstructor. eapply exec_function_external. simpl.      
      replace ("_MEMSET"%string) with (EF_name EF_memset); auto. apply ext_prim_axiom.
      exists (i::i0::nil). exists (Int.zero). repeat (split; auto). repeat constructor.
    + destruct args; try destruct args; try destruct v; inv HDO1. 
      econstructor. econstructor. eapply exec_function_external. simpl.      
      replace ("_MEMGET"%string) with (EF_name EF_memget); auto. apply ext_prim_axiom.
      exists (i::nil). exists retval. repeat (split; auto). repeat constructor.
    + destruct p0 as [[a b] c].
      destruct args; try destruct args; try destruct args; try destruct args; try destruct v, v0, v1; inv HDO1.
      simpl in HDO0.
      econstructor. econstructor. eapply exec_function_external. simpl.      
      replace ("_CLOSE"%string) with (EF_name EF_close); auto. apply ext_prim_axiom.
      exists (a::b::c::nil). exists Int.zero. repeat (split; auto). repeat constructor.
    + destruct args; try destruct args; try destruct v; inv HDO0. 
      econstructor. econstructor. eapply exec_function_external. simpl.      
      replace ("_PRINT"%string) with (EF_name EF_print); auto. apply ext_prim_axiom.
      exists (i::nil). exists Int.zero. repeat (split; auto). repeat constructor.
  - left. exists r. simpl. auto.
Qed.

Lemma mut_n_open:
  forall ms codsrc codopt sf1 sf2 ms1 ms2,
    n_open_stackframe (ms, codsrc) = SOK sf1 (ms1, codsrc) ->
    n_open_stackframe (ms, codopt) = SOK sf2 (ms2, codopt) ->
    sf1 = sf2 /\ ms1 = ms2.
Proof.
  intros ms codsrc codopt sf1 sf2 ms1 ms2 H H0.
  unfold n_open_stackframe in *. simpl in *.
  destruct (state_stacktop ms) eqn:TOP; inv H.
  destruct (state_stack ms) eqn:STK; inv H0.
  - inv H2. split; auto.
  - destruct s; inv H1.
    + inv H2. split; auto.
    + destruct a as [[[a1 a2] a3] a4]. inv H2. inv H0. split; auto.
Qed.

Lemma mut_n_memset:
  forall x y ms codsrc t1 codopt t2 ms1 ms2,
    n_memset x y (ms, codsrc) = SOK t1 (ms1, codsrc) ->
    n_memset x y (ms, codopt) = SOK t2 (ms2, codopt) ->
    ms1 = ms2.
Proof.
  intros x y ms codsrc t1 codopt t2 ms1 ms2 H H0. unfold n_memset in *.
  destruct (Int.lt x mem_size) eqn:MEMRANGE; inv H. inv H0. auto.
Qed.

Lemma mut_n_memget:
  forall x ms codsrc t1 codopt t2 ms1 ms2,
    n_memget x (ms, codsrc) = SOK t1 (ms1, codsrc) ->
    n_memget x (ms, codopt) = SOK t2 (ms2, codopt) ->
    ms1 = ms2.
Proof.
  intros x ms codsrc t1 codopt t2 ms1 ms2 H H0. unfold n_memget in *.
  destruct (Int.lt x mem_size) eqn:MEMRANGE; inv H. simpl in H0.
  destruct ((state_mem ms) # (pos_of_int x)) eqn:MEMGET; inv H0. inv H2. auto.
Qed.


Lemma same_get:
  forall p l,
    @PTree.get positive p l = @PTree.get label p l.
Proof.
  intros p l. auto.
Qed.

Lemma rtl_internal_silent:
  forall rtls rge t rtls',
    rtl_state_wf rtls ->
    ~ interrupt_rtl rtls ->
    RTL.step rge rtls t rtls' ->
    t = E0.
Proof.
  intros rtls rge t rtls' H H0 H1. inv H1; auto.
  - apply H in H2. inv H2.      (* rtlwf: no builtins *)
  - exfalso. apply H0. constructor. (* no interrupt: no calls *)
Qed.


(* Used to avoid Qed being stuck. To investigate... *)
Lemma same_genv:
  forall rtl,
    Smallstep.globalenv (RTL.semantics rtl) =
    Globalenvs.Genv.globalenv rtl.
Proof.
  simpl. auto.
Qed.

  
Theorem backend_progress:
  forall p (rtl: option (RTLfun + RTLblock.RTLblockfun)) rtlfid rtlcode rtlentry rtlidx asm mutsrc codsrc mut_comp codopt
    (RTL: rtl = Some (inl (rtlfid, rtlcode, rtlentry, rtlidx)))
    (RTLCODEWF: rtl_code_wf rtlcode)
    (NOCOMP: n_check_compiled rtlfid (mutsrc, codsrc) = SOK Not_compiled (mutsrc, codsrc))
    (BACKEND: rtl_backend (rtlfid, rtlcode, rtlentry, rtlidx) = OK asm)
    (INSTALL: n_install_code rtlfid asm (mutsrc, codsrc) = SOK tt (mut_comp, codopt)),
  forall (i : backend_index) (s1 s2 : mixed_state),
    backend_match_states (rtlfid, rtlcode, rtlentry, rtlidx) asm i s1 s2 ->
    safe (mixed_sem p (Some (inl (rtlfid, rtlcode, rtlentry, rtlidx))) codsrc AnchorOff) s1 ->
    (exists r : int, final_mixed_state p s2 r) \/
    (exists (t : trace) (s2' : state (mixed_sem p None codopt AnchorOff)), Step (mixed_sem p None codopt AnchorOff) s2 t s2').
Proof.
  intros p rtl rtlfid rtlcode0 rtlentry rtlidx asm mutsrc codsrc mut_comp codopt RTL RTLCODEWF NOCOMP BACKEND INSTALL.
  intros i s1 s2 MATCH SAFE. inv RTL.
  inv MATCH.
  - unfold safe in SAFE. specialize (SAFE s2 (star_refl _ _ _)). auto.
    destruct SAFE as [[r FINAL]|[t [s' STEP]]].
    { inv FINAL. left. exists r. constructor. }
    right. inv INSTALL. inv STEP; try simpl in STEP0; try simpl in NOT_RTL.
    + econstructor. econstructor. eapply IR_step; eauto.
      eapply mut_monad_same_effect; eauto. apply mut_ir.
    + econstructor. econstructor. eapply x86_step; eauto.
      eapply mut_monad_same_effect; eauto. apply mut_asm.
    + inv NO_RTL.
    + econstructor. econstructor. eapply Call_IR; eauto.
      eapply mut_monad_same_effect; eauto. apply mut_callee.
      { simpl in NOT_COMPILED. unfold n_check_compiled in NOT_COMPILED. simpl in NOT_COMPILED.
        simpl. unfold n_check_compiled. simpl. rewrite PTree.gso.
        destruct (codsrc # fid); inv NOT_COMPILED. eauto.
        unfold not. intros. subst. apply NOT_RTL. auto. }
      eapply mut_monad_same_effect; eauto. apply mut_get_args.
      simpl. intros H. inv H.
    + econstructor. econstructor. eapply Call_x86; eauto.
      eapply mut_monad_same_effect; eauto. apply mut_callee.
      { simpl in COMPILED. unfold n_check_compiled in COMPILED. simpl in COMPILED.
        simpl. unfold n_check_compiled. simpl. rewrite PTree.gso. destruct (codsrc # fid); inv COMPILED.
        eauto. unfold not. intros. subst. apply NOT_RTL. auto. }
      eapply mut_monad_same_effect; eauto. apply mut_set_args.
      simpl. intros H. inv H.
      { simpl in LOAD. repeat sdo_ok. unfold sbind. unfold n_load_prog_code in *. simpl in HDO.
        simpl. rewrite PTree.gso. destruct (codsrc # fid); inv HDO. eauto. unfold not. intros H.
        subst. apply NOT_RTL. auto. }
    + inv RTL. destruct asm as [asme asmc].
      assert (PROP: monad.asm_get (asme, asmc) Main = Some asme) by auto.
      eapply compiled_from_rtl' in PROP; eauto.
      destruct PROP as [entrylbl [index [order [mtc [RTLGET PROP]]]]]. inv RTLGET.
      eapply extract_init_exist in PROP; eauto.
      destruct PROP as [s2 INITASM].
      econstructor. econstructor.
      eapply Call_x86; eauto. (* calling the new compiled function *)
      eapply mut_monad_same_effect; eauto. apply mut_callee.
      simpl. unfold n_check_compiled. simpl. rewrite PTree.gss; auto.
      eapply mut_monad_same_effect; eauto. apply mut_set_args.
      simpl. unfold not. intros H. inv H.
      simpl. unfold sbind. unfold n_load_prog_code. simpl. rewrite PTree.gss; auto.
      rewrite init_asm_ok. simpl. apply INITASM.
    + inv RTL_BLOCK.
    + econstructor. econstructor. eapply Return_IR; eauto.
      eapply mut_monad_same_effect; eauto. apply mut_get_retval.
      eapply mut_same_effect; eauto. constructor.
    + assert (DIFF: pos_of_int caller_fid <> rtlfid).
      { unfold not. intros Heq. unfold n_check_compiled in NOCOMP. simpl in NOCOMP.
        destruct (codsrc # rtlfid) eqn:SRCFID; inv NOCOMP. simpl in LOAD_CONT.
        repeat sdo_ok. unfold n_load_prog_code in HDO. simpl in HDO. rewrite SRCFID in HDO. inv HDO. }
      econstructor. econstructor. eapply Return_x86; eauto.
      eapply mut_monad_same_effect; eauto. apply mut_get_retval.
      eapply mut_same_effect; eauto. constructor.
      eapply mut_same_effect; eauto. constructor.
      { simpl in LOAD_CONT. repeat sdo_ok. unfold sbind. unfold n_load_prog_code in *.
        simpl in HDO. simpl. rewrite PTree.gso; auto.
        destruct (codsrc # (pos_of_int caller_fid)); inv HDO.
        destruct ((snd a)# (pos_of_int cont_lbl)); inv LOAD_CONT. eauto. }
    + inv RTL. apply int_pos_correct in INTPOS_FID.
      destruct asm as [asme asmc].
      assert (PROP: rtl_get_entry (fid, rtlcode1, entry, contidx) (Cont (pos_of_int cont_lbl)) = Some cont_entry) by (simpl; auto).
      eapply all_compiled' in PROP; eauto.
      destruct PROP as [asmf [index [order [mtc [ASMGET PROP]]]]].
      eapply extract_init_exist in PROP; eauto.
      destruct PROP as [sinit ASMINIT].
      econstructor. econstructor. eapply Return_x86; eauto.
      eapply mut_monad_same_effect; eauto. apply mut_get_retval.
      eapply mut_same_effect; eauto. constructor.
      eapply mut_same_effect; eauto. constructor.
      simpl. unfold sbind. unfold n_load_prog_code. simpl. rewrite INTPOS_FID. rewrite PTree.gss; auto.
      simpl. simpl in ASMGET. rewrite ASMGET. eauto.
      rewrite init_asm_ok. eauto.
    + inv RTL_BLOCK.
    + econstructor. econstructor. eapply Return_EOE; eauto.
      eapply mut_monad_same_effect; eauto. apply mut_get_retval.
      eapply mut_same_effect; eauto. constructor.
    + econstructor. econstructor. eapply Deopt; eauto.
      eapply mut_monad_same_effect; eauto. apply mut_target.
      eapply mut_monad_same_effect; eauto. apply mut_build_rm.
    + inv NO_RTL.
    + inv NO_RTL.
    + inv NO_RTL.
      
  - right. simpl.
    set (rtlp := (rtlfid, rtlcode0, rtlentry, rtlidx)).
    set (rge := Globalenvs.Genv.globalenv (make_prog rtlcode0 (entrylbl rtlp asm i0))).
    apply mixed_rtl_safety in SAFE as RTLSAFE; auto.
    simpl in SAFE. simpl in RTLSAFE. simpl in SIMUL_MATCH. simpl in AGE_WF. simpl in GE_WF.
    specialize (extract_prop _ _ i0) as PROP. simpl in PROP.
    specialize (extract_progress _ _ _ _ _ PROP) as PROG. simpl in PROG.
    specialize (PROG _ _ _ SIMUL_MATCH RTLSAFE). 
    destruct PROG as [[retval FINAL]|[t [s' STEP]]]. 
    (* when a SAFE means a non-final RTL state matched with a final ASM one *)
    + specialize (extract_final _ _ _ _ _ PROP) as FINALMATCH. 
      (* by bsim_match_final states, the RTLstate has a RTL Star (E0) until a RTL final state *)
      specialize (FINALMATCH _ _ _ retval SIMUL_MATCH RTLSAFE FINAL).
      destruct FINALMATCH as [s1' [STAR RTLFINAL]]. rewrite same_star in STAR.
      eapply silent_rtl_mixed_star' with (or:=Some (inl (rtlfid, rtlcode0, rtlentry, rtlidx))) (ac:=codsrc) (p:=p) (mut:=mut) in STAR as [RTLSTAR WF]; eauto. 
      unfold safe in SAFE. rewrite <- same_genv in SAFE. 
      specialize (SAFE _ RTLSTAR).
      (* because RTL state is mixed safe, after that Star(E0) we are either mixed final or with a step *)
      destruct SAFE as [[r FINAL']|[t [s'' STEP]]]. inv FINAL'.
      rewrite same_genv in STEP.
      inversion STEP.
      * subst. inv RTLFINAL. inv RTL.
      * subst. inv RTLFINAL.
      * subst p0 ge rtls0 ms t. (* The step is a step where the RTL ends because we were RTL final *)
        (* then we now the final value can create a checkpoint and we get our ASMinterp Done step *)
        exists E0. econstructor. eapply x86_step; eauto.
        rewrite <- is_final_correct in FINAL.
        unfold asm_int_step, asm_step. rewrite FINAL. rewrite exec_bind2.
        unfold sbind2, sbind. simpl. assert (r = retval).
        { rewrite <- rtl_is_final_correct in RTLFINAL, FINAL0. rewrite RTLFINAL in FINAL0.
          inv FINAL0. auto. } subst r. rewrite CHK. simpl. eauto.
    
    + assert (STEPASM: Asm.step (Globalenvs.Genv.globalenv (asmf (rtlfid, rtlcode0, rtlentry, rtlidx) asm i0)) asms t s') by auto.
    inv STEP.
      * set (age := Globalenvs.Genv.globalenv (asmf (rtlfid, rtlcode0, rtlentry, rtlidx) asm i0)).
        assert (INT: internal_step age (Asm.State rs m) E0 (Asm.State rs' m')).
        { econstructor; eauto. } 
        eapply internal_interp with (i:=naive_impl) (s:=(mut,codopt)) in INT.
        exists E0. econstructor. eapply x86_step; eauto.
        unfold asm_int_step. rewrite exec_bind2. unfold sbind2, sbind.
        (* simpl in Heqage. rewrite <- Heqage. *)
        unfold age in INT. unfold rtlp. rewrite INT. simpl. eauto.
      * unfold asm_ge_wf, asm_no_builtin in AGE_WF. destruct AGE_WF as [_ AGE_WF].
        specialize (AGE_WF b f H0 ofs ef args res H1). inv AGE_WF.
    (* Builtins steps are not possible *)
      * (* we have a prim step in the asm. *)
        rename rtlcode0 into rtlc.
        set (age:= Globalenvs.Genv.globalenv (asmf (rtlfid, rtlc, rtlentry, rtlidx) asm i0)).
        (* we know it's an ext_prim thanks to asm_ge_wf *)
        assert (H3: exists (prim: ext_primitive), ef = EF prim).
        { unfold asm_ge_wf in AGE_WF. eapply AGE_WF. eauto. }
        destruct H3 as [prim EXT]. subst ef. simpl in H2.
        rewrite known_prim_sem in H2. 
        apply ext_prim_axiom in H2 as H4. destruct H4 as [intargs [ret [ARGS [TYP [MEM [RES EVENT]]]]]].
        subst m' args res t.
        (* with bsim_simulation we get in RTL a Plus (ev (prim)) *)
        specialize (extract_simulation _ _ _ _ _ PROP) as SIMUL.         
        specialize (SIMUL (Asm.State rs m)_ _ STEPASM _ _ SIMUL_MATCH RTLSAFE).
        destruct SIMUL as [i' [rtls' [PLUS MATCH]]].
        apply plus_or_star_is_plus in PLUS. 2: { unfold not. intros H'. inv H'. }
        (* This Plus in RTL is first a Star(E0), then a step (print_ev), then something else *)
        apply plus_dec in PLUS. destruct PLUS as [rtls1 [rtls2 [RTLSTAR [RTLSTEP _]]]].
        (* This star RTL E0 is also a star mixed E0 *)
        eapply silent_rtl_mixed_star with (or:=Some (inl (rtlfid, rtlc, rtlentry, rtlidx))) (mut:=mut) (ac:=codsrc)  (p:=p) in RTLSTAR; eauto.
        (* 2: { rewrite Heqrge in GE_WF. auto. } *)
        destruct RTLSTAR as [MIXEDSTAR WF].
        (* because rtls is mixed-safe, the next step with from rtls1 is possible in the mixed sem *)
        unfold safe in SAFE. 
        rewrite same_star in MIXEDSTAR. rewrite <- same_genv in SAFE. specialize (SAFE _ MIXEDSTAR).
        destruct SAFE as [[r FINAL]|[t [s'' SAFESTEP]]]. inv FINAL. 
        rewrite same_genv in SAFESTEP. inversion SAFESTEP.           (* this step has to be a prim step *)
        { subst. inv RTLSTEP. apply WF in H3. inv H3. exfalso. apply NO_INTERRUPT. constructor. }
        2: { subst. inv FINAL. inv RTLSTEP. }
        subst t0 ms ge nc rtl p0 rtls1. 
        (* This step also executes the same primitive *)
        (* because we are in a callstate calling prim *)
        assert (SAMEPRIM: name = EF_name prim /\ sg = EF_sig prim /\ args = intlistval intargs).
        { simpl in WF. destruct WF as [_ [prim' WF]]. inv WF. inv RTLSTEP.
          rewrite known_external in H9.
          apply ext_prim_axiom in H9. destruct H9 as [a [r [A [_ [_ [_ H']]]]]]. 
          inv H'. split; auto. split.
          - destruct prim; destruct prim'; inv H4; auto.
          - apply intlisteval_inj in H5. subst. auto. }
        destruct SAMEPRIM as [NAME [SIG ARGS]]. subst name sg args.        
        (* Now i know that the asm step calling the primtive may proceed without failing *)
        econstructor. econstructor. eapply x86_step; eauto.
        unfold asm_int_step, asm_step. destruct (is_final (Asm.State rs m)) eqn:FINAL.
        { rewrite is_final_correct in FINAL. inv FINAL. rewrite H6 in H. inv H. }
        rewrite exec_bind2. unfold sbind2, sbind. rewrite H. (* rewrite Heqage. *)
        simpl in H0. unfold age. unfold rtlp. rewrite H0. simpl. rewrite Ptrofs.eq_true.
        rewrite exec_bind2. unfold sbind2, sbind. unfold ext_prim_sem.
        rewrite exec_bind. unfold sbind, fret'. 
        rewrite extcall_arguments_eq in H1. simpl in H1. rewrite H1. simpl.
        rewrite exec_bind2. unfold sbind2, sbind.
        eapply mut_monad_same_effect in PRIM_CALL. 2: { apply mut_prim_sem. }
        rewrite PRIM_CALL. simpl. eauto.
Qed.


Theorem backend_simulation:
  forall p (rtl: option (RTLfun + RTLblock.RTLblockfun)) rtlfid rtlcode rtlentry rtlidx asm mutsrc codsrc mut_comp codopt
    (RTL: rtl = Some (inl (rtlfid, rtlcode, rtlentry, rtlidx)))
    (RTLCODEWF: rtl_code_wf rtlcode)
    (NOCOMP: n_check_compiled rtlfid (mutsrc, codsrc) = SOK Not_compiled (mutsrc, codsrc))
    (BACKEND: rtl_backend (rtlfid, rtlcode, rtlentry, rtlidx) = OK asm)
    (INSTALL: n_install_code rtlfid asm (mutsrc, codsrc) = SOK tt (mut_comp, codopt)),
  forall (s2 : state (mixed_sem p None codopt AnchorOff)) (t : trace) (s2' : state (mixed_sem p None codopt AnchorOff)),
    Step (mixed_sem p None codopt AnchorOff) s2 t s2' ->
    forall (i : backend_index) (s1 : mixed_state),
      backend_match_states (rtlfid, rtlcode, rtlentry, rtlidx) asm i s1 s2 ->
      safe (mixed_sem p (Some (inl (rtlfid, rtlcode, rtlentry, rtlidx))) codsrc AnchorOff) s1 ->
      exists (i' : backend_index) (s1' : state (mixed_sem p (Some (inl (rtlfid, rtlcode, rtlentry, rtlidx))) codsrc AnchorOff)),
        (SPlus (mixed_sem p (Some (inl (rtlfid, rtlcode, rtlentry, rtlidx))) codsrc AnchorOff) s1 t s1' \/
         Star (mixed_sem p (Some (inl (rtlfid, rtlcode, rtlentry, rtlidx))) codsrc AnchorOff) s1 t s1' /\
         backend_order i' i) /\ backend_match_states (rtlfid, rtlcode, rtlentry, rtlidx) asm i' s1' s2'.
Proof.
  intros p rtl rtlfid rtlcode0 rtlentry rtlidx asm mutsrc codsrc mut_comp codopt RTL RTLCODEWF NOCOMP BACKEND INSTALL.
  intros s2 t s2' STEP i s1 MATCH SAFE.
  inv MATCH.
  (* match_refl: from the same states *)
  + simpl in STEP. 
    simpl in STEP, SAFE, s2', s2. simpl. unfold n_install_code in INSTALL. inv INSTALL.
    inv STEP; simpl.  (* REFL *)
    * exists Refl. exists (synchro, ms1). split. (* IRstep *)
      ** left. apply plus_one. eapply IR_step.
         (* ** Using Typing *)
         eapply mut_monad_same_effect in STEP0; eauto. apply mut_ir.
      ** eapply match_refl. unfold IRinterpreter.ir_step in STEP0. repeat sdo_ok. destruct p0. simpl.
         destruct i; try destruct c; auto.
    * exists Refl. exists (synchro, ms1). split. (* x86_step *)
      ** left. apply plus_one. eapply x86_step.
         eapply mut_monad_same_effect in STEP0; eauto. apply mut_asm.
      ** eapply match_refl. unfold asm_int_step in STEP0. repeat sdo_ok. destruct p0. simpl in STEP0.
         destruct i; try destruct c; repeat sdo_ok; auto.
         unfold get_checkpoint in HDO1.
         destruct (Int.eq i RETRET); inv HDO1; simpl; auto.
         destruct (Int.eq i RETCALL); inv H0; simpl; auto.
         destruct (Int.eq i RETDEOPT); inv H1; simpl; auto.
    * inv NO_RTL.             (* RTL step *)
    * clear NOT_RTL. simpl in NOT_COMPILED. (* call IR *)
      unfold n_check_compiled in NOT_COMPILED. simpl in NOT_COMPILED.
      poseq_destr rtlfid fid.
      { rewrite PTree.gss in NOT_COMPILED. inv NOT_COMPILED. }
      rewrite PTree.gso in NOT_COMPILED; auto. destruct (codsrc#fid) eqn:COD; inv NOT_COMPILED.
      exists Refl. exists (Halt_IR (current_version func, ver_entry (current_version func), newrm), ms3). split.
      ** left. apply plus_one. eapply Call_IR with (fid:=fid); eauto.
         eapply mut_monad_same_effect; eauto. apply mut_callee. 
         simpl. unfold n_check_compiled. simpl. rewrite COD. auto.
         eapply mut_monad_same_effect; eauto. apply mut_get_args.
         simpl. unfold not. intros H. apply HEQ. inv H. auto.
      ** apply match_refl. simpl. auto.
    * poseq_destr rtlfid fid. (* call_x86 *)
      {                       (* calling the compiled function *)
        destruct asm as [asmp asmcont].
        apply n_load_same in LOAD. inv LOAD. 
        assert (RTL_GET: rtl_get_entry (fid, rtlcode0, rtlentry, rtlidx) Main = Some rtlentry) by auto.
        specialize (all_compiled' fid rtlcode0 rtlentry rtlidx asmp asmcont Main rtlentry BACKEND RTL_GET).
        intros [asmf [index [order [bwd_match [ASM_GET PROP]]]]].
        (* using safety to get an initial state *)
        apply safe_step_call_rtl in SAFE. destruct SAFE as [ge [rtls [ms' FWDSTEP]]].
        assert (asmp = asmf) by (inv ASM_GET; auto). subst. 
        inv FWDSTEP. inv RTL.
        2: { destruct loc; inv CALLEE; simpl; auto. repeat sdo_ok.
             unfold n_load in HDO. simpl in HDO.
             destruct (state_stacktop ms); inv HDO. auto. }
        (* Infering information about the monad executions *)
        assert (fid0 = fid0 /\ ms2 = ms1).
        { eapply mut_monad_twice; eauto. apply mut_callee. }
        destruct H. subst. clear H.
        assert (ms' = ms4).
        { eapply mut_monad_twice; eauto. apply mut_set_args. } subst.
        (* constructing the index. exploiting bsim_properties *)
        assert (wf: well_founded order) by (destruct PROP; auto).
        assert (INITR: exists (i:index) (rtl_init:RTL.state), RTL.initial_state (make_prog rtlcode1 entry) rtl_init /\ bwd_match i rtl_init xs).
        { destruct PROP. simpl in bsim_match_initial_states.
          apply init_asm_ok in INIT.
          specialize (bsim_match_initial_states rtls xs INIT0 INIT). apply bsim_match_initial_states. }
        destruct INITR as [i [rtlinit [INIT1 MATCHINIT]]].
        exists (Simul (mkindex (fid0, rtlcode1, entry, contidx) (asmf, asmcont) index order i wf
                          bwd_match asmf entry Main ASM_GET RTL_GET PROP)).
        (* constructing the RTL state of the source *)
        exists (Halt_RTL (Globalenvs.Genv.globalenv (make_prog rtlcode1 entry)) rtlinit, ms4).
        split.
        ** left. apply plus_one. eapply Call_RTL; eauto.
        ** apply match_simul; simpl; auto.
           apply rtl_ge_wf. eapply rtl_init_wf; eauto. eapply compiled_wf; eauto.
      }
      (* calling another function *)
      exists Refl. exists (Halt_ASM (build_genv asm_prog) xs, ms4). split.
      ** left. apply plus_one. eapply Call_x86; eauto.
         eapply mut_monad_same_effect; eauto. apply mut_callee.
         { simpl in COMPILED. unfold n_check_compiled in COMPILED. simpl in COMPILED.
           rewrite PTree.gso in COMPILED; auto. simpl.
           unfold n_check_compiled. simpl. destruct (codsrc # fid); inv COMPILED. eauto. }
         eapply mut_monad_same_effect; eauto. apply mut_set_args.
         simpl. unfold not. intros H. inv H. apply HEQ. auto.
         { simpl. simpl in LOAD. unfold n_load_prog_code in *. repeat sdo_ok. simpl in HDO.
           unfold sbind. simpl. rewrite PTree.gso in HDO; auto. destruct (codsrc#fid); inv HDO. auto. }
      ** eapply match_refl. simpl. auto.
    * inv RTL.                (* call RTL *)
    * inv RTL_BLOCK.
    * exists Refl.                 (* Return IR *)
      exists (Halt_IR (v, pc, rm # retreg <- retval), ms2). split.
      ** left. apply plus_one. eapply Return_IR; eauto.
         eapply mut_monad_same_effect; eauto. apply mut_get_retval.
         eapply same_mut with (p:=Prim_OpenSF); eauto. constructor.
      ** eapply match_refl. simpl. auto.
    * poseq_destr (intpos.pos_of_int caller_fid) rtlfid. (* Return x86 *)
      {                                                  (* returning to the compiled function *)
        destruct asm as [asmp asmcont].
        apply n_load_cont_same in LOAD_CONT. destruct LOAD_CONT as [LOAD_CONT SAME]. inv SAME.
        eapply cont_compiled_get_entry in LOAD_CONT as COMP; eauto.
        destruct COMP as [entrylbl RTL_GET]. 
        specialize (all_compiled' _ _ _ _ _ _ _ _ BACKEND RTL_GET).
        intros [asmf [index [order [bwd_match [ASM_GET PROP]]]]].
        (* using safety to get an initial state of the continuation *)
        eapply safe_step_return in SAFE; eauto.
        2: { unfold n_check_compiled in *. simpl in NOCOMP. simpl.
             destruct (codsrc # (pos_of_int caller_fid)); inv NOCOMP. auto. }
        destruct SAFE as [ge [rtls [ms' FWDSTEP]]]. inv FWDSTEP. inv RTL.
        (* Infering information about the monad executions *)
        assert (retval = retval0 /\ ms1 = ms3).
        { eapply mut_monad_twice; eauto. eapply mut_get_retval. } destruct H. subst.
        specialize (mut_n_open _ _ _ _ _ _ _ OPEN_SF0 OPEN_SF).
        intros [SF MS]. inv SF. clear OPEN_SF.
        assert (tt = tt /\ ms4 = ms').
        { eapply mut_twice; eauto. constructor. } destruct H as [_ H]. subst. simpl in NOT_COMPILED.
        apply n_check_same in NOT_COMPILED as SAME. inv SAME.
        simpl in RTL_GET. rewrite same_get in LOAD_CONT0. rewrite RTL_GET in LOAD_CONT0. inv LOAD_CONT0.
        simpl in ASM_GET. rewrite LOAD_CONT in ASM_GET. inv ASM_GET.
        (* constructing the index. exploiting bsim_properties *)
        assert (wf: well_founded order) by (destruct PROP; auto).
        assert (INITR: exists (i:index) (rtl_init:RTL.state), RTL.initial_state (make_prog rtlcode1 cont_entry) rtl_init /\ bwd_match i rtl_init xs).
        { destruct PROP. simpl in bsim_match_initial_states.
          apply init_asm_ok in INIT.
          specialize (bsim_match_initial_states rtls xs INIT0 INIT). eapply bsim_match_initial_states. }
        destruct INITR as [i [rtlinit [INIT1 MATCHINIT]]].
        exists (Simul (mkindex (pos_of_int caller_fid, rtlcode1, entry, contidx) (asmp, asmcont) index order i wf
                          bwd_match asmf cont_entry (Cont (pos_of_int cont_lbl)) LOAD_CONT RTL_GET PROP)).
        (* constructing the RTL state of the source *)
        exists (Halt_RTL (Globalenvs.Genv.globalenv (make_prog rtlcode1 cont_entry)) rtlinit, ms').
        split.
        ** left. apply plus_one. eapply Return_RTL; eauto.
        ** apply match_simul; simpl; auto.
           apply rtl_ge_wf. eapply rtl_init_wf; eauto.
           eapply compiled_wf with (contid:=Cont (pos_of_int cont_lbl)); eauto.
      }
      
      exists Refl.                                            (* Returning to the same x86 *)
      exists (Halt_ASM (build_genv asm_prog) xs, ms4). split.
      ** left. apply plus_one. eapply Return_x86; eauto.
         eapply mut_monad_same_effect; eauto. apply mut_get_retval.
         eapply same_mut with (p:=Prim_OpenSF); eauto. constructor.
         eapply same_mut with (p:=Prim_Save retval); eauto. constructor.
         { simpl. simpl in LOAD_CONT. unfold n_load_prog_code in *. repeat sdo_ok. simpl in HDO.
           unfold sbind. simpl. rewrite PTree.gso in HDO; auto.
           destruct (codsrc # (intpos.pos_of_int caller_fid)); inv HDO.
           destruct ((snd a)# (intpos.pos_of_int cont_lbl)); inv LOAD_CONT. auto. }
      ** eapply match_refl. simpl. auto.
    * inv RTL.                (* return RTL *)
    * inv RTL_BLOCK.
    * exists Refl.                 (* Return EOE *)
      exists (EOE retval, ms2). split.
      ** left. apply plus_one. eapply Return_EOE.
         eapply mut_monad_same_effect; eauto. apply mut_get_retval.
         eapply same_mut with (p:=Prim_OpenSF); eauto. constructor.
      ** apply match_refl. simpl. auto.
    * exists Refl.                 (* Deopt *)
      exists (Halt_IR (fn_base func, ltgt, rm), ms2). split.
      ** left. apply plus_one. eapply Deopt; eauto.
         eapply mut_monad_same_effect; eauto. apply mut_target.
         eapply mut_monad_same_effect; eauto. apply mut_build_rm.
      ** apply match_refl. simpl. auto.
    * inv NO_RTL.
    * exists Refl. (* RTL_end *)
      exists (synchro_of cp, ms). split.
      ** left. apply plus_one. eapply RTL_end; eauto.
      ** apply match_refl. simpl. unfold get_checkpoint in CHK.
         destruct (Int.eq r RETRET); inv CHK; simpl; auto.
         destruct (Int.eq r RETCALL); inv H0; simpl; auto.
         destruct (Int.eq r RETDEOPT); inv H1; simpl; auto.           
    * exists Refl.                 (* RTL block end *)
      exists (synchro_of cp, ms). split.
      ** left. apply plus_one. eapply RTL_block_end; eauto.
      ** apply match_refl. simpl. unfold get_checkpoint in CHK.
         destruct (Int.eq r RETRET); inv CHK; simpl; auto.
         destruct (Int.eq r RETCALL); inv H0; simpl; auto.
         destruct (Int.eq r RETDEOPT); inv H1; simpl; auto.           

  (* match_simul: matched using a CompCert simulation *)
  +
    { inv STEP. unfold asm_int_step in STEP0. repeat sdo_ok. destruct p0 as [trace cp].
      destruct cp; simpl.
      - simpl in STEP0. repeat sdo_ok. (* the ASM program has finished  *)
        set (age := Globalenvs.Genv.globalenv (asmf (rtlfid, rtlcode0, rtlentry, rtlidx) asm i0)).
        set (rge := Globalenvs.Genv.globalenv (make_prog rtlcode0 (entrylbl (rtlfid, rtlcode0, rtlentry, rtlidx) asm i0))).
        apply asm_step_done_correct in HDO as [FINAL [SILENT SAME]]; auto. subst t.
        specialize (extract_prop _ _ i0) as PROP. 
        specialize (extract_final _ _ _ _ _ PROP) as FINALMATCH. clear PROP.
        eapply FINALMATCH in FINAL; eauto.
        2: { eapply mixed_rtl_safety; eauto. }
        destruct FINAL as [rtls' [STAR FINAL']]. exists Refl. exists (synchro_of c, ms1). split.
        + left. rewrite <- same_plus. eapply dec_plus' with (s2:=(Halt_RTL rge rtls', mut)).
          ** rewrite same_star in STAR. eapply silent_rtl_mixed_star' in STAR as [RTLSTAR WF]; eauto.
             rewrite <- same_star in RTLSTAR. unfold rge. rewrite same_genv in RTLSTAR. eapply RTLSTAR.
          ** inv SAME. eapply RTL_end; eauto.
        + constructor. simpl. destruct c; simpl; auto.
          
      - apply asm_step_halt_correct in HDO; auto. (* Halt: the ASM steps are not over *)
        destruct HDO as [[ASMSTEP [SAME SILENT]]|PRIMSTEP].
        (* The Halting step is an internal silent step *)
        + inv SAME. specialize (extract_prop _ _ i0) as PROP. 
          specialize (extract_simulation _ _ _ _ _ PROP) as SIMUL. 
          apply internal_step_asm in ASMSTEP.
          eapply SIMUL in ASMSTEP; eauto. 
          2: { simpl in SAFE. eapply mixed_rtl_safety; eauto. }
          (* simpl in SAFE, GE_WF. *) clear SIMUL PROP.
          set (rge := Globalenvs.Genv.globalenv (make_prog rtlcode0 (entrylbl (rtlfid, rtlcode0, rtlentry, rtlidx) asm i0))).
          destruct ASMSTEP as [it [rtls'[[RTLPLUS|[RTLSTAR ORDER]] MATCH]]].
          * exists (Simul (change_index _ _ i0 it)). exists (Halt_RTL rge rtls', ms1).
            simpl in STEP0. inv STEP0.
            apply silent_rtl_mixed_plus with (p:=p) (or:=Some(inl(rtlfid, rtlcode0, rtlentry, rtlidx))) (ac:=codsrc) (mut:=ms1) in RTLPLUS as [RTLPLUS WF]; auto. split.
            ** left. rewrite same_plus in RTLPLUS. unfold rge. rewrite <- same_genv. apply RTLPLUS.
            ** constructor; auto.
          * exists (Simul (change_index _ _ i0 it)). exists (Halt_RTL rge rtls', ms1).
            simpl in STEP0. inv STEP0.
            apply silent_rtl_mixed_star with (p:=p) (or:=Some(inl(rtlfid, rtlcode0, rtlentry, rtlidx))) (ac:=codsrc) (mut:=ms1) in RTLSTAR as [RTLSTAR WF]; auto. split.
            ** right. rewrite same_star in RTLSTAR. split. unfold rge. rewrite <- same_genv. apply RTLSTAR.
               constructor; auto. 
            ** constructor; auto.
               
        (* the halting step is a primitive that stays in the ASM execution  *)
        + destruct PRIMSTEP as [prim [args PRIMSTEP]].
          apply prim_step_halt_asm in PRIMSTEP. destruct PRIMSTEP as [ret [STEP EXEC]].
          specialize (extract_prop _ _ i0) as PROP. 
          specialize (extract_simulation _ _ _ _ _ PROP) as SIMUL. 
          eapply SIMUL in STEP; eauto.
          2: { simpl in SAFE. eapply mixed_rtl_safety; eauto. }
          (* simpl in SAFE, GE_WF. *) clear SIMUL PROP.
          destruct STEP as [it [rtls' [PLUSORSTAR MATCH]]].
          apply plus_or_star_is_plus in PLUSORSTAR.
          2: { unfold not. intros H. inv H. }
          apply plus_dec in PLUSORSTAR as [scall [sret [STAR1 [STEP STAR2]]]].
          apply silent_rtl_mixed_star with (p:=p) (or:=Some(inl(rtlfid, rtlcode0, rtlentry, rtlidx))) (ac:=codsrc) (mut:=mut) in STAR1 as [RTLSTAR WFCALL]; auto.
          apply step_pres_wf in STEP as WFRET; auto. inv STEP.
          { apply WFCALL in H. inv H. }
          simpl in WFCALL. destruct WFCALL as [STACKWF [prim' EF]]. subst.
          rewrite known_external in H. apply ext_prim_axiom in H.
          destruct H as [intargs [intret [ARGS [TYP [MEM [RET EVENT]]]]]]. inv EVENT.
          apply name_inj in H0. apply intlisteval_inj in H1. subst.
          apply silent_rtl_mixed_star with (p:=p) (or:=Some(inl(rtlfid, rtlcode0, rtlentry, rtlidx))) (ac:=codsrc) (mut:=ms1) in STAR2 as [RTLSTAR2 WFEND]; auto.
          inv STEP0.
          set (rge := Globalenvs.Genv.globalenv (make_prog rtlcode0 (entrylbl (rtlfid, rtlcode0, rtlentry, rtlidx) asm i0))).            
          exists (Simul (change_index _ _ i0 it)). exists (Halt_RTL rge rtls', ms1). split.
          2: { constructor; auto. }
          left. rewrite <- same_plus.
          eapply dec_plus with (s2:=(Halt_RTL rge (RTL.Callstate s0 (External (EF_runtime (EF_name prim') (EF_sig prim'))) (intlistval intargs) m'), mut)).
          * unfold rge. rewrite <- same_genv. apply RTLSTAR.
          * apply RTL_prim. 
            eapply mut_monad_same_effect; eauto. apply mut_prim_sem.
          * unfold rge. rewrite <- same_genv. apply RTLSTAR2.
    }
Qed.





Theorem backend_pass_correct:
  forall p rtl rtlfid rtlcode rtlentry rtlidx asm mutsrc codsrc mut_comp codopt
    (RTL: rtl = Some (inl (rtlfid, rtlcode, rtlentry, rtlidx)))
    (RTLCODEWF: rtl_code_wf rtlcode)
    (NOCOMP: n_check_compiled rtlfid (mutsrc, codsrc) = SOK Not_compiled (mutsrc, codsrc))
    (BACKEND: rtl_backend (rtlfid, rtlcode, rtlentry, rtlidx) = OK asm)
    (INSTALL: n_install_code rtlfid asm (mutsrc, codsrc) = SOK tt (mut_comp, codopt)),
    backward_internal_simulation p p rtl None codsrc codopt AnchorOff AnchorOff.
                                 
Proof.
  intros p rtl rtlfid rtlcode rtlentry rtlidx asm mutsrc codsrc mut_comp codopt RTL RTLCODEWF NOCOMP BACKEND INSTALL.
  apply n_install_same in INSTALL as SAME. subst. simpl.
  eapply Backward_internal_simulation with (bsim_index:=backend_index) (bsim_order:=backend_order) (bsim_match_states:=backend_match_states (rtlfid, rtlcode, rtlentry, rtlidx) asm).
  - apply backend_order_wf.
  - econstructor. eapply match_refl. inv H. simpl. auto.
  - intros i s1 s2 r H H0 H1. simpl. exists s1. split; auto.
    apply star_refl. inv H. auto. inv H1.
  (* PROGRESS *)
  - eapply backend_progress; eauto.    

  (* SIMULATION *)
  - eapply backend_simulation; eauto.
Qed.
