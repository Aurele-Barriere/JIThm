(* Proving the JIT monad correct *)
Require Import Events.
Require Import Errors.
Require Import customSmallstep.
Require Import customBehaviors.

Require Import common.
Require Import IR.
Require Import intpos.
Require Import ASMinterpreter.
Require Import IRinterpreter.
Require Import optimizer.
Require Import backend.
Require Import primitives.
Require Import mixed_sem.
Require Import monad.
Require Import monad_impl.
Require Import monad_properties.
Require Import sem_properties.
Require Import jit.
Require Import dynamic_proof.
Require Import backend_proof.
Require Import Integers.



Lemma pop_args_same:
  forall nb mut ac mut1 ac1 l r,
    exec (pop_args' nb l) naive_impl (mut, ac) = SOK r (mut1, ac1) ->
    ac = ac1.
Proof.
  intros nb mut ac mut1 ac1 l r H.
  generalize dependent l. generalize dependent r. generalize dependent mut. 
  induction nb; intros.
  - simpl in H. inv H. auto.
  - simpl in H. repeat sdo_ok. destruct n. unfold n_load in HDO. simpl in HDO.
    destruct (state_stacktop mut); inv HDO. apply IHnb in H. auto.
Qed.


Lemma get_args_same:
  forall a mut ac mut1 ac1 l,
    exec (get_args a) naive_impl (mut, ac) = SOK l (mut1, ac1) ->
    ac = ac1.
Proof.
  unfold get_args. intros a mut ac mut1 ac1 l H. destruct a; inv H; auto. repeat sdo_ok.
  unfold pop_args in H1. destruct n. apply pop_args_same in H1. unfold n_load in HDO.
  simpl in HDO. destruct (state_stacktop mut); inv HDO. auto.  
Qed.

Lemma get_varmap_same:
  forall size mut ac mut2 ac2 r l,
    exec (get_varmap size l) naive_impl (mut, ac) = SOK r (mut2, ac2) ->
    ac = ac2.
Proof.
  intros size. induction size; intros mut0 ac mut2 ac2 r rm H.
  - inv H. auto.
  - simpl in H. repeat sdo_ok. destruct n. destruct n0.
    eapply IHsize in H. subst. apply load_same in HDO. apply load_same in HDO0. subst. auto.
Qed.

Lemma build_rm_same:
  forall mut ac mut2 ac2 r rml,
    exec (build_rm rml) naive_impl (mut, ac) = SOK r (mut2, ac2) ->
    ac = ac2.
Proof.
  intros mut0 ac mut2 ac2 r rml H. unfold build_rm in H. destruct rml.
  - repeat sdo_ok. inv HDO. destruct n. repeat sdo_ok. apply load_same in HDO. subst.
    apply get_varmap_same in HDO0. auto.
  - inv H. auto.
Qed.

        


Ltac eT :=
  match goal with
  | [H: existT _ _ _ = existT _ _ _ |- _ ] => apply Classical_Prop.EqdepTheory.inj_pair2 in H; subst
  end.


(** * A Specification for calling Native Code  *)
Lemma step_asm:
  forall {state:Type} g g' s s' (i:monad_impl state) ms ms' t,
    exec (native_step_spec (g, s)) i ms = SOK (t, Halt (g',s')) ms' ->
    g' = g /\ exec (asm_step g s) i ms = SOK (t, Halt s') ms'.
Proof.
  intros. unfold native_step_spec in H. repeat sdo_ok. destruct p. simpl in H. destruct i0; inv H.
  split; auto.
Qed.

Definition native_call_spec: @na_spec jit_state (Asm.genv * Asm.state) int :=
  mk_spec jit_state (Asm.genv * Asm.state) int
    (native_load_spec)
    (native_step_spec)
    (native_return_spec).


(** * Defining the semantics of the JIT non-atomic symbolic Monad  *)

Definition jit_sem {mstate:Type} (p:program) (i:@monad_impl mstate) :=
  unf_sem jit_prog i native_call_spec (init_jit_state p) (final_jit_state).


(** * Properties of the JIT semantics  *)
Lemma jit_single_events:
  forall p mstate (i:@monad_impl mstate),
    single_events (jit_sem p i).
Proof.
  unfold single_events, jit_sem, jit_prog. simpl. intros p mstate i s t s' STEP.
  inv STEP; try inv ATOMIC; try destruct s1; try inv RUN;
    try inv H0; try eT; repeat sdo_ok; auto.
  - destruct (next_status (profiler (prof_state j) c) c (nb_optim j)); repeat sdo_ok; auto.
  - destruct c; repeat sdo_ok; auto. simpl in EXEC_STEP. repeat sdo_ok.
    destruct c; repeat sdo_ok; auto.
    simpl in EXEC_STEP. repeat sdo_ok. destruct c; repeat sdo_ok; auto.
    simpl in EXEC_STEP. repeat sdo_ok. destruct c; repeat sdo_ok. auto. auto.
  - destruct c; repeat sdo_ok; auto.
    + destruct c0; repeat sdo_ok; auto.
    + destruct o; repeat sdo_ok; auto.
      * destruct i1, p0, p0. simpl in EXEC_STEP. repeat sdo_ok. auto.
      * simpl in EXEC_STEP. repeat sdo_ok. auto.
  - destruct p0. simpl in EXEC_STEP. destruct i1. simpl in EXEC_STEP. inv EXEC_STEP.
    eapply single_ir_int; eauto. inv EXEC_STEP. eapply single_ir_int; eauto.
  - inv EXEC_STEP. 
  - destruct i1, i2. simpl in EXEC_STEP. eapply single_asm; eauto.
    apply step_asm in EXEC_STEP. destruct EXEC_STEP. eauto.
  - destruct i1. simpl in EXEC_RET. inv EXEC_RET. eapply single_asm; eauto.
    simpl in EXEC_END. repeat sdo_ok. destruct p0. simpl in EXEC_END. destruct i0; inv EXEC_END. eauto.    
Qed.

Lemma jit_events:
  forall S (impl:monad_impl S) p t s s',
    Step (unf_sem jit_prog impl native_call_spec (init_jit_state p) final_jit_state) s t s' ->
    t = nil \/ exists v, t = (print_event v).
Proof.
  intros S impl p t s s' H. unfold jit_prog in H. simpl in H.
  inv H; auto; try inv ATOMIC; try destruct s1; try inv RUN; try inv H0; try eT; repeat sdo_ok; auto.
  - destruct (next_status (profiler (prof_state j) c) c (nb_optim j)); repeat sdo_ok; auto.
  - destruct c; repeat sdo_ok; auto. simpl in EXEC_STEP. repeat sdo_ok.
    destruct c; repeat sdo_ok; auto.
    simpl in EXEC_STEP. repeat sdo_ok. destruct c; repeat sdo_ok; auto.
    simpl in EXEC_STEP. repeat sdo_ok. destruct c; repeat sdo_ok. auto. auto.
  - destruct c; repeat sdo_ok; auto.
    + destruct c0; repeat sdo_ok; auto.
    + destruct o; repeat sdo_ok; auto.
      * destruct i, i0, p0, p, p0. simpl in EXEC_STEP. repeat sdo_ok. auto.
      * simpl in EXEC_STEP. repeat sdo_ok. auto.
  - destruct p0. simpl in EXEC_STEP. destruct i0. simpl in EXEC_STEP. inv EXEC_STEP.
    apply ir_events in HDO. auto.
    apply ir_events in HDO. inv EXEC_STEP. auto.
  - inv EXEC_STEP. 
  - destruct i1, i2. simpl in EXEC_STEP. repeat sdo_ok. destruct p0.
    apply asm_events in HDO. inv EXEC_STEP. destruct i; inv H0; auto.
  - destruct i1. simpl in EXEC_RET. simpl in EXEC_END. repeat sdo_ok.
    destruct p0. apply asm_events in HDO. inv EXEC_END.
    destruct i; inv H0; auto.
Qed.

(* Lemma match_single: *)
(*   forall t, *)
(*     (Datatypes.length t <= 1)%nat -> *)
(*     match_traces t t. *)
(* Proof. *)
(*   intros t H. destruct t as [|a [|b c]]; try constructor. *)
(*   simpl in H. lia. *)
(* Qed. *)
(* not true anymore with our new match_trace *)
  
Lemma jit_determinacy:
  forall p mstate (i:@monad_impl mstate),
    determinate (jit_sem p i).
Proof.
  intros p mstate i. apply Determinate.
  - intros s t1 s1 t2 s2 H H0. simpl in H, H0.
    apply jit_events in H as T1. apply jit_events in H0 as T2.
    specialize (jit_single_events p mstate i s t1 s1 H). intros SINGLE.
    inv H; inv H0; try solve[rewrite ATOMIC in RUN; inv RUN];
      try (rewrite ATOMIC0 in ATOMIC; inv ATOMIC); 
      try (rewrite EXEC_STEP0 in EXEC_STEP; inv EXEC_STEP); 
      try (rewrite RUN0 in RUN; inv RUN); 
      try (rewrite EXEC_END in EXEC_STEP; inv EXEC_STEP);
      try eT; subst.
    + split; auto. destruct T1. subst. constructor. destruct H. subst. constructor. 
    + rewrite LOAD0 in LOAD. inv LOAD. split. constructor. intros. auto.
    + split; auto. destruct T1. subst. constructor. destruct H. subst. constructor. 
    + rewrite EXEC_END0 in EXEC_END. inv EXEC_END. rewrite EXEC_RET0 in EXEC_RET. inv EXEC_RET. split; auto.
      destruct T1. subst. constructor. destruct H. subst. constructor. 
  - apply jit_single_events.
  - intros s1 s2 H H0. inv H. inv H0. inv INIT. inv INIT0. auto.
  - intros s r H. inv H. inv FINAL. unfold jit_final in FINAL0.
    destruct s0; inv FINAL0.  unfold nostep, not. intros t s' H. inv H. 2: { inv RUN. }
    inv ATOMIC. inv EXEC_STEP.
  - intros s r1 r2 H H0. inv H. inv H0. inv FINAL. inv FINAL0. rewrite FINAL in FINAL1. inv FINAL1. auto.
Qed.


Lemma jit_receptive:
  forall p mstate (i:@monad_impl mstate),
    receptive (jit_sem p i).
Proof.
  intros p mstate i. apply Receptive.
  2: { apply jit_single_events. }
  intros s t1 s1 t2 H H0. exists s1.
  simpl in H. apply jit_events in H as EV. destruct EV as [EV|[x EV]]; subst.
  - inv H0. simpl. auto.
  - inv H0. simpl. auto.
Qed.


(** * Correctness ot the JIT semantics with regards to the dynamic semantics  *)
Inductive match_cp : synchro_state -> checkpoint -> Prop :=
| cp_call:
    forall loc,
      match_cp (S_Call loc) (C_Call loc)
| cp_ret:
    forall loc,
      match_cp (S_Return loc) (C_Return loc)
| cp_deopt:
    forall loc,
      match_cp (S_Deopt loc) (C_Deopt loc).

Lemma match_sync_of:
  forall cp, match_cp (synchro_of cp) cp.
Proof.
  intros cp. destruct cp; constructor.
Qed.

Inductive match_states : nat -> dynamic_state -> (@unf_state jit_state (Asm.genv * Asm.state) * n_state) -> Prop :=
| match_prof:
    forall p sync ns nbopt cp ps
      (MATCH_CP: match_cp sync cp),
      match_states 3 (Dynamic p None sync ns nbopt) (EXT (PROF (mk_data p ps nbopt) cp), ns)
| match_opt:
    forall p loc ns nbopt ps,
      match_states 2 (Dynamic p None (S_Call loc) ns (S nbopt)) (EXT (OPT (mk_data p ps (S nbopt)) (C_Call loc)), ns)
| match_exe:
    forall p sync ns nbopt cp ps
      (MATCH_CP: match_cp sync cp),
      match_states 1 (Dynamic p None sync ns nbopt) (EXT (EXE (mk_data p ps nbopt) cp), ns)
| match_end:
    forall p ns nbopt r jd,
      match_states 0 (Dynamic p None (EOE r) ns nbopt) (EXT (END jd r), ns)
| match_ir:
    forall p ns nbopt irs ps, 
      match_states 0 (Dynamic p None (Halt_IR irs) ns nbopt) (EXT (EXE_IR (mk_data p ps nbopt) irs), ns)
| match_call:
    forall p ns nbopt ps fid loc ns2 ns3 ns4 af
      (GET_CALLEE: exec (get_callee loc) naive_impl ns = SOK fid ns2)
      (CHECK: exec_prim (Prim_Check_Compiled fid) naive_impl ns2 = SOK (Installed af) ns3)
      (SET_ARGS: exec (set_up_args loc) naive_impl ns3 = SOK tt ns4),
      match_states 0 (Dynamic p None (S_Call loc) ns nbopt)
                   (EXT (EXE_NAT (mk_data p ps nbopt) (Call_id fid)), ns4)
| match_ret:
    forall p nbopt ps loc ns ns1 ns2 ns3 retval i0 i1 i2
      (RETVAL: exec (get_retval loc) naive_impl ns = SOK retval ns1)
      (OPEN: n_open_stackframe ns1 = SOK (nat_sf i0 i1 i2) ns2)
      (SETUP: exec_prim (Prim_Save retval) naive_impl ns2 = SOK tt ns3),
      match_states 0 (Dynamic p None (S_Return loc) ns nbopt)
                   (EXT (EXE_NAT (mk_data p ps nbopt) (Cont_id (pos_of_int i0) (pos_of_int i1))), ns3)
| match_int:
    forall p ns nbopt ge asms asmid ps,
      match_states 0 (Dynamic p None (Halt_ASM ge asms) ns nbopt) (INT (EXE_NAT (mk_data p ps nbopt) asmid) (ge, asms), ns).


Lemma match_none:
  forall i p rtl sync ns nbopt s,
    match_states i (Dynamic p rtl sync ns nbopt) s ->
    rtl = None.
Proof.
  intros i p rtl sync ns nbopt s H. inv H; auto.
Qed.

Lemma safe_dynamic:
  forall p p0 sync mut ac nbopt ,
    safe (dynamic_sem p None) (Dynamic p0 None sync (mut, ac) nbopt) ->
    (exists r, sync = EOE r) \/ exists t sync2 mut2, mixed_step AnchorOff p0 None ac (sync, mut) t (sync2, mut2).
Proof.
  intros p p0 sync mut ac nbopt H. unfold safe in H. simpl in H.
  exploit (H (Dynamic p0 None sync (mut, ac) nbopt)). apply star_refl.
  intros H'. destruct H' as [[r FINAL]|[t [s'' STEP]]].
  - left. exists r. inv FINAL. auto.
  - right. inv STEP; eauto.
Qed.


                                                                   
Theorem jit_dynamic:
  forall p,
    backward_simulation (dynamic_sem p None) (jit_sem p naive_impl).
Proof.
  intros p. eapply Backward_simulation with (bsim_match_states := match_states).
  - apply lt_wf.
  - intros s1 H. simpl. exists (EXT (initial_jit_state p), init_n_state). constructor. constructor. auto.
  - intros s1 s2 H H0. inv H0. inv INIT. exists (3%nat).
    destruct s1. exists (Dynamic p None (S_Call (ir_call (prog_main p) nil)) init_n_state max_optim). split; repeat constructor; auto.
  - intros i s1 s2 r H H0 H1. inv H1. inv FINAL. destruct s; inv FINAL0. inv H.
    exists (Dynamic p0 None (EOE r) ms nbopt). split. apply star_refl. constructor.
  - intros i s1 s2 MATCH SAFE.  (* progress *)
    destruct s1 as [p0 rtl0 sync [mut ac] nbopt]. apply match_none in MATCH as NONE. subst.
    apply safe_dynamic in SAFE. destruct SAFE as [[r FINAL] | [t [sync' [mut' STEP]]]].
    { subst. destruct s2; inv MATCH; try inv MATCH_CP. left. exists r. constructor. constructor. auto. }
    simpl. inv MATCH.
    + right. exists E0. destruct (next_status (profiler ps cp) cp nbopt) eqn:STATUS. (* PROF *)
      esplit. eapply ext_step; simpl; auto. repeat sok_do. rewrite STATUS. simpl. eauto.
      esplit. eapply ext_step; simpl; auto. repeat sok_do. rewrite STATUS. simpl. eauto.
    + right. exists E0. destruct (n_check_compiled (backend_suggestion ps) (mut, ac)) eqn:CHECK. (* OPT *)
      { unfold n_check_compiled in CHECK. simpl in CHECK. destruct (ac#(backend_suggestion ps)); inv CHECK. }
      destruct c. 
      esplit. eapply ext_step; simpl; auto. repeat sok_do. unfold sbind. rewrite CHECK. simpl. auto.
      destruct ((prog_funlist p0) # (backend_suggestion ps)) eqn:FIND.
      destruct (backend (current_version f) (backend_suggestion ps) (fn_params f)) eqn:BACK.
      esplit. eapply ext_step; simpl; auto. repeat sok_do. rewrite FIND. unfold sbind. rewrite CHECK.
      rewrite exec_bind. unfold sbind.
      repeat sok_do. unfold backend_and_install. rewrite BACK. simpl. auto.
      esplit. eapply ext_step; simpl; auto. repeat sok_do. rewrite FIND. unfold sbind. rewrite CHECK.
      rewrite exec_bind. unfold sbind.
      repeat sok_do. unfold backend_and_install. rewrite BACK. simpl. auto.
      esplit. eapply ext_step; simpl; auto. repeat sok_do. unfold sbind. rewrite CHECK. rewrite FIND.
      simpl. auto.
    + right. exists E0. destruct cp; inv MATCH_CP.              (* EXE *)
      * inv STEP.                                   (* CALL *)
        ** esplit. eapply ext_step; simpl; auto. simpl.
           rewrite exec_bind.
           unfold sbind. rewrite CALLEE. simpl.
           unfold sbind. simpl in NOT_COMPILED. rewrite NOT_COMPILED.
           rewrite GETF. simpl. rewrite exec_bind. unfold sbind. simpl.
           rewrite ARGS. rewrite exec_bind. simpl.
           rewrite INIT. simpl. unfold sbind. simpl. eauto.
        ** esplit. eapply ext_step; simpl; auto. rewrite exec_bind. 
           simpl. unfold sbind. rewrite CALLEE. simpl in COMPILED. rewrite COMPILED.
           rewrite exec_bind. unfold sbind. rewrite ARGS. simpl. eauto.
        ** inv RTL.
        ** inv RTL_BLOCK.
      * inv STEP.               (* RET *)
        ** esplit. eapply ext_step; simpl; auto. rewrite exec_bind. unfold sbind.
           rewrite RETVAL. simpl. unfold sbind. simpl in OPEN_SF. rewrite OPEN_SF.
           simpl. eauto.
        ** esplit. eapply ext_step; simpl; auto. rewrite exec_bind. unfold sbind.
           rewrite RETVAL. simpl. unfold sbind. simpl in OPEN_SF. rewrite OPEN_SF.
           simpl. unfold sbind. simpl in SET_RETVAL. rewrite SET_RETVAL. simpl. eauto.
        ** inv RTL.
        ** inv RTL_BLOCK.
        ** esplit. eapply ext_step; simpl; auto. rewrite exec_bind. unfold sbind.
           rewrite RETVAL. simpl. unfold sbind. simpl in OPEN_SF. rewrite OPEN_SF.
           simpl. eauto.
      * inv STEP. esplit. eapply ext_step; simpl; auto. rewrite exec_bind2. unfold sbind2, sbind.
        rewrite TARGET. rewrite exec_bind. unfold sbind. rewrite BUILD_RM. simpl.
        rewrite FINDF. rewrite exec_bind. simpl. repeat sok_do. eauto.
    + left. exists r. constructor. constructor. auto. (* END *)
    + right. inv STEP.                           (* EXE_IR *)
      destruct (exec (ir_int_step irs) naive_impl (mut, ac)) eqn:INT.
      { unfold ir_step in STEP0. rewrite exec_bind2 in STEP0. simpl in STEP0.
        unfold sbind2, sbind in STEP0. rewrite INT in STEP0. inv STEP0. }
      unfold ir_step in STEP0. rewrite exec_bind2 in STEP0.
      unfold sbind2, sbind in STEP0. rewrite INT in STEP0. destruct p1.
      simpl in STEP0. destruct i; inv STEP0; exists t.
      * esplit. eapply ext_step; simpl; auto. rewrite exec_bind2.
        simpl. unfold sbind2, sbind. rewrite INT. simpl. auto.
      * esplit. eapply ext_step; simpl; auto. rewrite exec_bind2.
        simpl. unfold sbind2, sbind. rewrite INT. simpl. auto.
    + right. exists E0. inv STEP.    (* MATCH CALL *)
      * rewrite CALLEE in GET_CALLEE. inv GET_CALLEE.
        rewrite CHECK in NOT_COMPILED. inv NOT_COMPILED.
      * rewrite CALLEE in GET_CALLEE. inv GET_CALLEE.
        rewrite CHECK in COMPILED. inv COMPILED. rewrite SET_ARGS in ARGS. inv ARGS.
        simpl in LOAD. repeat sdo_ok. econstructor.
        eapply loop_start; simpl; auto. unfold sbind. rewrite HDO. simpl.
        rewrite exec_bind. unfold sbind. rewrite INIT. simpl. eauto.
      * inv RTL.
      * inv RTL_BLOCK.
    + right. exists E0. inv STEP.    (* MATCH_RET *)
      * simpl in OPEN_SF. rewrite RETVAL0 in RETVAL. inv RETVAL. rewrite OPEN_SF in OPEN. inv OPEN.
      * simpl in OPEN_SF. rewrite RETVAL0 in RETVAL. inv RETVAL. rewrite OPEN_SF in OPEN. inv OPEN.
        rewrite SETUP in SET_RETVAL. inv SET_RETVAL.
        simpl in LOAD_CONT. repeat sdo_ok. econstructor.
        eapply loop_start; simpl; auto. unfold sbind. rewrite HDO.
        destruct ((snd a)#(pos_of_int i1)); inv LOAD_CONT. rewrite exec_bind. unfold sbind.
        rewrite INIT. simpl. eauto.
      * inv RTL.
      * inv RTL_BLOCK.
      * simpl in OPEN_SF. rewrite RETVAL0 in RETVAL. inv RETVAL. rewrite OPEN_SF in OPEN. inv OPEN.
    + right. inv STEP. 
      destruct (exec (asm_step ge asms) naive_impl (mut, ac)) eqn:STEP. (* MATCH INT *)
      { unfold asm_int_step in STEP0. rewrite exec_bind2 in STEP0.
        simpl in STEP0. unfold sbind2, sbind in STEP0. simpl in STEP.
        rewrite STEP in STEP0. inv STEP0. }
      destruct p1. destruct n. unfold asm_int_step in STEP0. rewrite exec_bind2 in STEP0.
      unfold sbind2, sbind in STEP0. rewrite STEP in STEP0. simpl in STEP0.
      destruct i; repeat sdo_ok.
      * eapply asm_done in STEP as STEP'; eauto. 
        exists t. esplit. eapply loop_end.
        ** simpl. rewrite exec_bind2. unfold sbind2, sbind. rewrite STEP. simpl. eauto.
        ** simpl. unfold native_return_spec. simpl. unfold ret_spec. rewrite HDO0. simpl. eauto.
      * apply asm_halt in STEP as STEP'. 
        exists t. esplit. eapply int_step. simpl. rewrite exec_bind2. unfold sbind2, sbind. rewrite STEP.
        simpl. eauto.
  - intros s2 t s2' STEP i s1 MATCH SAFE. simpl in STEP. (* simulation *)
    inv MATCH.
    + inv STEP; try inv RUN; try inv ATOMIC. repeat sdo_ok. (* PROF *)
      destruct (next_status (profiler ps cp) cp nbopt) eqn:STATUS; repeat sdo_ok.
      * exists (1%nat). exists (Dynamic p0 None sync ms2 nbopt). split. right. split. apply star_refl. lia. constructor; auto.
      * exists (2%nat). exists (Dynamic p0 None sync ms2 nbopt). destruct nbopt. inv STATUS. destruct cp; inv STATUS. inv MATCH_CP.
        split. right. split. apply star_refl. lia. constructor; auto.
    + inv STEP; try inv RUN; try inv ATOMIC. simpl in EXEC_STEP. repeat sdo_ok.
      destruct ns as [mut1 ac1]. destruct ms2 as [mut2 ac2]. (* OPT *)
      destruct u.
      assert (OPT: exec (optimize ps p0) naive_impl (mut1, ac1) = SOK tt (mut2, ac2)).
      { unfold optimize. rewrite exec_bind. sok_do. unfold sbind. rewrite HDO. auto. }
      exists (1%nat). exists (Dynamic p0 None (S_Call loc) (mut2, ac2) nbopt). 
      repeat sdo_ok. apply n_check_same in HDO. inv HDO.
      apply safe_dynamic in SAFE. destruct SAFE as [[r FINAL] | SAFE_STEP]. inv FINAL.
      destruct c; inv HDO0.
      { split. left. apply plus_one. eapply opt_step; eauto. constructor; auto. constructor. }
      destruct ((prog_funlist p0) # (backend_suggestion ps)) eqn:FINDF; repeat sdo_ok.
      2: { inv H0. split. left. apply plus_one. eapply opt_step; eauto. constructor; auto. constructor. }
      unfold backend_and_install in H0. destruct (backend (current_version f) (backend_suggestion ps) (fn_params f)) eqn:BACK.
      2: { inv H0. split. left. apply plus_one. eapply opt_step; eauto. constructor; auto. constructor. }
      unfold exec in H0. simpl in H0. apply n_install_same in H0. subst.
      split. left. apply plus_one. eapply opt_step; eauto. constructor; auto. constructor.
    + inv STEP; try inv RUN; try inv ATOMIC. (* EXE *)
      destruct cp; repeat sdo_ok.
      * inv MATCH_CP. destruct c0; repeat sdo_ok. (* Call *)
        ** exists O. exists (Dynamic p0 None (S_Call c) ns nbopt). 
           apply n_check_same in HDO0 as CHK. subst. destruct u.
           split. right. split. apply star_refl. lia. eapply match_call; eauto.
        ** exists O. exists (Dynamic p0 None (Halt_IR (current_version f0,ver_entry (current_version f0),r)) ms2 nbopt).
           destruct n as [mut1 ac1]. destruct n0 as [mut2 ac2].
           destruct ms2 as [mut ac]. destruct ns as [mut0 ac0].
           apply get_args_same in HDO1 as SAME. apply n_check_same in HDO0 as SAME'. inv SAME'.
           assert (ac0 = ac). { eapply mut_monad_same_code; eauto. apply mut_callee. }
           subst. split. left. apply plus_one. apply exe_step. eapply Call_IR; eauto.
           unfold rtl_id. unfold not. intros H. inv H.
           constructor; auto.
      * inv MATCH_CP. simpl in EXEC_STEP. destruct o; repeat sdo_ok. (* Return *)
        ** destruct i0 as [[[retreg ver] retlbl] rm]. repeat sdo_ok.
           exists O. exists (Dynamic p0 None (Halt_IR (ver, retlbl, rm # retreg <- i)) ms2 nbopt).
           destruct ns as [mut ac]. destruct n as [mut1 ac1]. destruct ms2 as [mut2 ac2].
           apply open_sf_same in HDO0 as SAME. subst.
           assert (ac = ac2). { eapply mut_monad_same_code; eauto. apply mut_get_retval. }
           subst. split. left. apply plus_one. apply exe_step. eapply Return_IR; eauto.
           constructor; auto.
        ** simpl in EXEC_STEP. sdo_ok. destruct u. exists O. inv EXEC_STEP.
           exists (Dynamic p0 None (S_Return r) ns nbopt).
           split. right. split. apply star_refl. lia.
           eapply match_ret; eauto.
        ** exists O. exists (Dynamic p0 None (EOE i) ms2 nbopt). destruct ns as [mut ac]. destruct n as [mut1 ac1].
           destruct ms2 as [mut2 ac2]. 
           assert (ac = ac1). { eapply mut_monad_same_code; eauto. apply mut_get_retval. } subst.
           apply open_sf_same in HDO0 as SAME. subst.
           split. left. apply plus_one. apply exe_step. eapply Return_EOE; eauto.
           constructor; auto.
      * inv MATCH_CP. exists O. destruct p1 as [ftgt ltgt]. simpl in HDO2.
        exists (Dynamic p0 None (Halt_IR (fn_base f, ltgt, r)) ms2 nbopt).
        destruct ns as [mut ac]. destruct n as [mut1 ac1]. destruct ms2 as [mut2 ac2].
        apply build_rm_same in HDO0 as H. subst.
        assert (ac = ac2). { eapply mut_monad_same_code; eauto. apply mut_target. }
        subst. split.
        ** left. apply plus_one. eapply exe_step. eapply Deopt; eauto.
        ** constructor; auto.
    + inv STEP; try inv RUN; try inv ATOMIC. (* END *)
      inv EXEC_STEP.
    + inv STEP; try inv RUN; try inv ATOMIC. repeat sdo_ok. (* EXE_IR *)
      destruct ns as [mut ac]. destruct ms2 as [mut2 ac2]. destruct n as [mut1 ac1].
      apply ir_same in HDO as SAME. inv SAME.
      destruct irs as [[v pc] rm]. destruct p1 as [tr [cp|irs']]; inv EXEC_STEP. 
      * exists (3%nat). exists (Dynamic p0 None (synchro_of cp) (mut2, ac2) nbopt). 
        split. left. apply plus_one. apply exe_step. apply IR_step.
        unfold ir_step. apply ir_done; auto.
        constructor; auto. apply match_sync_of.
      * exists O. exists (Dynamic p0 None (Halt_IR irs') (mut2, ac2) nbopt).
        split. left. apply plus_one. apply exe_step. apply IR_step.
        apply ir_halt; auto.
        constructor; auto.
    + inv STEP; try inv RUN; try inv ATOMIC. simpl in LOAD. repeat sdo_ok. (* NAT CALL *)
      exists O. destruct a as [pr cont]. simpl in HDO. simpl.
      destruct ns as [mut ac]. destruct ns2 as [mut2 ac2].
      destruct ns3 as [mut3 ac3]. destruct ns4 as [mut4 ac4]. destruct ms2 as [mut5 ac5].
      assert (ac = ac2). { eapply mut_monad_same_code; eauto. apply mut_callee. }
      assert (ac3 = ac4). { eapply mut_monad_same_code; eauto. apply mut_set_args. }
      simpl in CHECK. apply n_check_same in CHECK as SAME. inv SAME.                                        
      apply load_prog_same in HDO1 as SAME. inv SAME. 
      exists (Dynamic p0 None (Halt_ASM (build_genv pr) s) (mut5, ac5) nbopt).
      split. left. apply plus_one. apply exe_step. eapply Call_x86; eauto.
      simpl. unfold not. intros H. inv H.
      simpl. unfold sbind. rewrite HDO1. auto.
      constructor; auto.
    + inv STEP; try inv RUN; try inv ATOMIC. simpl in LOAD. repeat sdo_ok. (* NAT RETURN *)
      exists O. destruct ((snd a)#(pos_of_int i1)) eqn:GET; inv HDO.
      destruct ns as [mut ac]. destruct ns1 as [mut1 ac1]. destruct ns2 as [mut2 ac2].
      destruct ms2 as [mut3 ac3]. destruct a as [pr cont]. simpl in GET.
      destruct ns3 as [mut4 ac4].
      apply open_sf_same in OPEN as SAME.
      assert (ac = ac1). { eapply mut_monad_same_code; eauto. apply mut_get_retval. } subst.
      assert (ac2 = ac4). { eapply mut_same_code; eauto. constructor. } subst.
      apply load_prog_same in HDO1 as SAME''. inv SAME''. 
      exists (Dynamic p0 None (Halt_ASM (build_genv p1) s) (mut3, ac3) nbopt).
      split. left. apply plus_one. apply exe_step. eapply Return_x86; eauto. simpl.
      unfold sbind. rewrite HDO1. simpl. rewrite GET. auto.
      constructor; auto.
    + inv STEP; try inv RUN; try inv ATOMIC. (* INT *)
      * destruct ns as [mut ac]. destruct ms2 as [mut2 ac2].
        exists O. destruct i2 as [ge' asms']. exists (Dynamic p0 None (Halt_ASM ge' asms') (mut2, ac2) nbopt).
        simpl in EXEC_STEP. repeat sdo_ok. destruct p1. simpl in EXEC_STEP. destruct i; inv EXEC_STEP.
        apply asm_same in HDO as SAME. inv SAME.
        split. left. apply plus_one. apply exe_step. apply x86_step.
        apply asm_halt. auto. constructor; auto.
      * destruct ns as [mut ac]. destruct ms2 as [mut2 ac2]. destruct ms3 as [mut3 ac3].
        simpl in EXEC_RET. unfold native_return_spec in EXEC_RET. simpl in EXEC_RET.
        unfold ret_spec in EXEC_RET. repeat sdo_ok.
        exists (3%nat). exists (Dynamic p0 None (synchro_of c) (mut3, ac3) nbopt).
        simpl in EXEC_END. repeat sdo_ok. destruct p1. simpl in EXEC_END. destruct i; inv EXEC_END.
        apply asm_same2 in HDO as SAME. inv SAME. split.
        ** left. apply plus_one. apply exe_step. apply x86_step. eapply asm_done; eauto. 
        ** constructor; auto. apply match_sync_of.
Qed.


(** * Correctness of the JIT with naive implementation of the primitives *)
Corollary jit_correctness_naive:
  forall p,
    backward_simulation (input_sem p) (jit_sem p naive_impl).
Proof.
  intros p. eapply compose_backward_simulation.
  - apply jit_single_events.
  - eapply dynamic_input_correct. 
  - apply jit_dynamic. 
Qed.

Corollary jit_correctness_array:
  forall p,
    backward_simulation (input_sem p) (jit_sem p array_impl).
Proof.
  intros p. eapply compose_backward_simulation.
  - apply jit_single_events.
  - eapply jit_correctness_naive.
  - apply forward_to_backward_simulation.
    + apply refinement. apply list_refine.
    + apply jit_receptive.
    + apply jit_determinacy.
Qed.


(** * Correctness of the JIT for any implementation  *)
Theorem jit_correctness:
  forall p mstate (impl: @monad_impl mstate)
    (REF: refines array_impl impl),
    backward_simulation (input_sem p) (jit_sem p impl).
Proof.
  intros p mstate impl REF.
  eapply compose_backward_simulation.
  { apply jit_single_events. }
  { apply jit_correctness_naive. }
  apply forward_to_backward_simulation.
  2: { apply jit_receptive. }
  2: { apply jit_determinacy. }
  eapply compose_forward_simulation with (L2:=jit_sem p array_impl).
  - apply refinement. apply list_refine.
  - apply refinement. apply REF.
Qed.
      
(** * Final Theorem *)
(* Any behavior of the JIT improves a behavior of the original program semantics *)
Theorem jit_preservation_array:
  forall p beh,
  program_behaves (jit_sem p array_impl) beh ->
  exists beh', program_behaves (input_sem p) beh' /\ behavior_improves beh' beh.
Proof.
  intros. eapply backward_simulation_behavior_improves; eauto.
  apply jit_correctness_array; auto.
Qed.

(* Same theorem for any implementation that refines array_impl *)
Theorem jit_preservation:
  forall (p:program) (beh:program_behavior) (state:Type) (impl: monad_impl state),
    refines array_impl impl ->
    program_behaves (jit_sem p impl) beh ->
    exists beh', program_behaves (input_sem p) beh' /\ behavior_improves beh' beh.
Proof.
  intros p beh state impl REFINES BEHAVES.
  eapply backward_simulation_behavior_improves; eauto.
  apply jit_correctness. apply REFINES.
Qed.
(* Print Assumptions jit_preservation. *)
      
