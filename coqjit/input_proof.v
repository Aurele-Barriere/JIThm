(* Proof that mixed_semantics is a particular case of the input semantics *)

Require Import IR.
Require Import common.
Require Import mixed_sem.
Require Import customSmallstep.
Require Import monad.
Require Import Events.
Require Import primitives.
Require Import IRinterpreter.
Require Import Errors.
Require Import monad_impl.

Inductive match_stackframe : IR_stackframe -> stackframe -> Prop :=
| match_sf: forall isf,
    match_stackframe isf (IR_SF isf).

Inductive match_stack : ir_stack -> stack -> Prop :=
| match_nil:
    match_stack nil nil
| match_cons:
    forall sf1 sf2 stk1 stk2
      (MATCH_SF: match_stackframe sf1 sf2)
      (MATCH_STK: match_stack stk1 stk2),
      match_stack (sf1::stk1) (sf2::stk2).

Definition nothing_compiled (ms:n_state) : Prop :=
  (cod ms) = PTree.empty asm_fun.


Inductive match_states : unit -> input_state -> (synchro_state * mutables) -> Prop :=
| match_call:
    forall fid args stk ms mem
      (NO_TOP: state_stacktop ms = nil)
      (MATCH_STACK: match_stack stk (state_stack ms))
      (MEM: state_mem ms = mem),
      match_states tt (Callstate fid args stk mem) (S_Call (ir_call fid args), ms)
| match_ret:
    forall retval ms stk mem
      (NO_TOP: state_stacktop ms = nil)
      (MATCH_STACK: match_stack stk (state_stack ms))
      (MEM: state_mem ms = mem),
      match_states tt (Returnstate retval stk mem) (S_Return (ir_ret retval), ms)
| match_deopt:
    forall ftgt ltgt rm stk ms mem
      (NO_TOP: state_stacktop ms = nil)
      (MATCH_STACK: match_stack stk (state_stack ms))
      (MEM: state_mem ms = mem),
      match_states tt (Deoptstate ftgt ltgt rm stk mem) (S_Deopt (ir_deopt ftgt ltgt rm), ms) 
| match_final:
    forall retval ms
      (NO_TOP: state_stacktop ms = nil),
      match_states tt (Final retval) (EOE retval, ms)
| match_st:
    forall irs stk ms mem
      (NO_TOP: state_stacktop ms = nil)
      (MATCH_STACK: match_stack stk (state_stack ms))
      (MEM: state_mem ms = mem),
      match_states tt (State irs stk mem) (Halt_IR irs, ms).

Inductive order : unit -> unit -> Prop := .
Lemma wfounded:
  well_founded order.
Proof.
  unfold well_founded. intros. destruct a. constructor. intros. inv H.
Qed.

Lemma safe_step_state:
  forall p irs stk mem,
    safe (input_sem p) (State irs stk mem) ->
    exists s', exists t, Step (input_sem p) (State irs stk mem) t s'.
Proof.
  intros p irs stk mem H.
  unfold safe in H. specialize (H (State irs stk mem)).
  exploit H. apply star_refl.
  intros [[r FINAL]|[t [s'' STEP]]]. inv FINAL.
  exists s''. exists t. auto.
Qed.

Lemma safe_step_call:
  forall p fid args stk mem,
    safe (input_sem p) (Callstate fid args stk mem) ->
    exists s', exists t, Step (input_sem p) (Callstate fid args stk mem) t s'.
Proof.
  intros p fid args stk mem H.
  unfold safe in H. specialize (H (Callstate fid args stk mem)).
  exploit H. apply star_refl.
  intros [[r FINAL]|[t [s'' STEP]]]. inv FINAL.
  exists s''. exists t. auto.
Qed.

Lemma safe_step_return:
  forall p retval stk mem,
    safe (input_sem p) (Returnstate retval stk mem) ->
    exists s', exists t, Step (input_sem p) (Returnstate retval stk mem) t s'.
Proof.
  intros p retval stk mem H.
  unfold safe in H. specialize (H (Returnstate retval stk mem)).
  exploit H. apply star_refl.
  intros [[r FINAL]|[t [s'' STEP]]]. inv FINAL.
  exists s''. exists t. auto.
Qed.

Lemma safe_step_deopt:
  forall p ftgt ltgt rm stk mem,
    safe (input_sem p) (Deoptstate ftgt ltgt rm stk mem) ->
    exists s', exists t, Step (input_sem p) (Deoptstate ftgt ltgt rm stk mem) t s'.
Proof.
  intros p ftgt ltgt rm stk mem H.
  unfold safe in H. specialize (H (Deoptstate ftgt ltgt rm stk mem)).
  exploit H. apply star_refl.
  intros [[r FINAL]|[t [s'' STEP]]]. inv FINAL.
  exists s''. exists t. auto.
Qed.


Lemma check_no_comp:
  forall ms fid,
    nothing_compiled ms -> 
    n_check_compiled fid ms = SOK Not_compiled ms.
Proof.
  unfold n_check_compiled, nothing_compiled. intros ms fid H. rewrite H. rewrite PTree.gempty. auto.
Qed.


Theorem input_mixed:
  forall p,
    backward_simulation (input_sem p) (mixed_sem p None nocode).
Proof.
  intros p. 
  eapply Backward_simulation with (bsim_match_states := match_states) (bsim_order := order); simpl in *.
  - apply wfounded.
  - intros s1 INIT. exists (S_Call (ir_call (prog_main p) nil), init_mutables). constructor.
  - intros s1 s2 INIT INIT'. inv INIT'. exists tt. exists (Callstate (prog_main p) nil nil init_mem). split; repeat constructor.
  - intros i s1 s2 r MATCH SAFE FINAL. inv FINAL. inv MATCH. exists (Final r). split.
    + apply star_refl.
    + constructor.
  -                             (* progress *)
    intros i s1 s2 MATCH SAFE. inv MATCH.
    + apply safe_step_call in SAFE. destruct SAFE as [s' [t STEP]]. inv STEP.
      right. exists E0. econstructor. eapply Call_IR; simpl; eauto.
      (* * apply check_no_comp. unfold nothing_compiled; auto. *)
      * unfold rtl_id. unfold not. intros H. inv H.
    + apply safe_step_return in SAFE. destruct SAFE as [s' [t STEP]]. inv STEP.
      * right. exists E0. inv MATCH_STACK. inv MATCH_SF. econstructor. eapply Return_IR; simpl; eauto.
        unfold n_open_stackframe. simpl. rewrite NO_TOP. rewrite <- H. simpl. eauto. 
      * right. exists E0. inv MATCH_STACK. exists (EOE retval, ms). eapply Return_EOE; simpl; eauto.
        unfold n_open_stackframe. simpl. rewrite NO_TOP. rewrite <- H. auto.
    + apply safe_step_deopt in SAFE. destruct SAFE as [s' [t STEP]]. inv STEP.
      right. exists E0. exists (Halt_IR (base_version func, ltgt, rm), ms). eapply Deopt; simpl; eauto.
    + left. exists retval. constructor.
    + right. apply safe_step_state in SAFE. destruct SAFE as [s' [t STEP]].
      inv STEP.
      * econstructor. econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE. simpl. eauto.
      * econstructor. econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE.
        simpl. rewrite EVAL. repeat sok_do. eauto.
      * econstructor. econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE.
        repeat sok_do. rewrite EVAL. repeat sok_do. eauto.
      * destruct (bool_of_int val) eqn:BOOL.
        ** econstructor. econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE.
           repeat sok_do. rewrite EVAL. repeat sok_do. rewrite BOOL. simpl. eauto.
        ** econstructor. econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE.
           repeat sok_do. rewrite EVAL. repeat sok_do. rewrite BOOL. simpl. eauto.
      * econstructor. econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE.
        repeat sok_do. rewrite EVALAD. rewrite EVALVAL. simpl. unfold n_memset. rewrite RANGE. 
        unfold sbind. eauto.
      * econstructor. econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE.
        repeat sok_do. rewrite EVALAD. simpl. unfold n_memget. rewrite RANGE.
        unfold sbind. simpl. rewrite GET. eauto.
      * econstructor. econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE.
        simpl. unfold n_push_interpreter_stackframe.
        unfold sbind. simpl. rewrite NO_TOP. rewrite exec_bind. rewrite EVAL. simpl.
        unfold sbind. simpl. eauto.
      * econstructor. econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE.
        repeat sok_do. rewrite EVAL. repeat sok_do. eauto.
      * econstructor. econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE.
        simpl. repeat sok_do. rewrite EVAL. repeat sok_do. rewrite GUARD_OK. repeat sok_do. eauto.
      * econstructor. econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE.
        simpl. repeat sok_do. rewrite EVAL. repeat sok_do. rewrite GUARD_OK. repeat sok_do.
        rewrite BUILD. repeat sok_do. eauto.
  -                             (* simulation diagram *)
    intros s2 t s2' STEP i s1 MATCH SAFE. exists tt. inv MATCH.
    + inv STEP.
      * exists (State (current_version func, ver_entry (current_version func), newrm) stk (state_mem ms)).
        simpl in ARGS. unfold sret in ARGS. inv ARGS.
        simpl in NOT_COMPILED. unfold n_check_compiled, nocode in NOT_COMPILED. simpl in NOT_COMPILED.
        (* rewrite PTree.gempty in NOT_COMPILED.  *) inv NOT_COMPILED. inv CALLEE. split.
        ** left. apply plus_one. constructor; auto. 
        ** constructor; auto. 
      * simpl in COMPILED. unfold n_check_compiled, nocode in COMPILED. simpl in COMPILED.
        (* rewrite PTree.gempty in COMPILED. *) inv COMPILED.
      * inv RTL.
      * inv RTL_BLOCK.
    + inv STEP.
      * simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF. inv RETVAL.
        rewrite NO_TOP in OPEN_SF.
        inv MATCH_STACK; rewrite <- H1 in OPEN_SF; inv OPEN_SF.
        inv MATCH_SF. inv H0. exists (State (v, pc, rm # retreg <- retval0) stk1 (state_mem ms1)). split.
        ** left. apply plus_one. constructor; auto.
        ** constructor; auto.
      * simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF. inv RETVAL.
        rewrite NO_TOP in OPEN_SF.
        inv MATCH_STACK; rewrite <- H1 in OPEN_SF; inv OPEN_SF.
        inv MATCH_SF. inv H0.
      * inv RTL.
      * inv RTL_BLOCK.
      * simpl in OPEN_SF. inv RETVAL. inv MATCH_STACK; unfold n_open_stackframe in OPEN_SF; simpl in OPEN_SF; rewrite NO_TOP in OPEN_SF; rewrite <- H1 in OPEN_SF.
        2: { inv MATCH_SF; inv OPEN_SF. }
        exists (Final retval0). split.
        ** left. apply plus_one. constructor.
        ** inv OPEN_SF. constructor; auto.
    + inv STEP. inv BUILD_RM. inv TARGET. exists (State (base_version func, ltgt0, rm0) stk (state_mem ms2)). split.
      * left. apply plus_one. eapply input_Deopt; eauto.
      * constructor; auto.
    + inv STEP. 
    + inv STEP. rename STEP0 into STEP.
      unfold ir_step, ir_int_step in STEP. destruct irs as [[v pc] rm]. repeat sdo_ok.
      destruct i; simpl in HDO; repeat sdo_ok.
      * exists (State (v, l, rm) stk (state_mem ms1)). split.
        ** left. apply plus_one. eapply input_Nop; eauto.
        ** simpl. constructor; auto.
      * exists (State (v, l, rm) stk (state_mem ms1)). split.
        ** left. apply plus_one. eapply input_Print; eauto.
        ** simpl. constructor; auto.
      * exists (Callstate f l1 ((r, v, l0, rm)::stk) (state_mem ms)). split.
        ** left. apply plus_one. eapply input_Call; eauto.
        ** simpl in HDO0. unfold n_push_interpreter_stackframe in HDO0.
           simpl in HDO0. rewrite NO_TOP in HDO0. inv HDO0. constructor; try constructor; auto. constructor.
      * exists (State (v, pc_cond (bool_of_int i) l l0, rm) stk (state_mem ms)). split.
        ** left. apply plus_one. simpl. destruct p0. replace t with E0.
           2: { destruct (bool_of_int i); inv HDO; auto. }
           simpl. eapply input_Cond; eauto.
        ** destruct p0. simpl. unfold pc_cond. destruct (bool_of_int i); inv HDO; constructor; auto.
      * exists (Returnstate i stk (state_mem ms1)). split.
        ** left. apply plus_one. eapply input_Return; eauto.
        ** constructor; auto.
      * exists (State (v, l, rm # r <- i) stk (state_mem ms1)). split.
        ** left. apply plus_one. eapply input_Op; eauto.
        ** constructor; auto.
      * exists (State (v, l, rm) stk ((state_mem ms) # (intpos.pos_of_int i) <- i0)).
        unfold n_memset in HDO3. destruct (Integers.Int.lt i mem_size) eqn:RANGE; inv HDO3. simpl.
        split.
        ** left. apply plus_one. eapply input_MemSet; eauto.
        ** constructor; auto.
      * exists (State (v, l, rm # r <- i0) stk (state_mem ms)).
        unfold n_memget in HDO2. destruct (Integers.Int.lt i mem_size) eqn:RANGE; inv HDO2.
        destruct ((state_mem ms) # (intpos.pos_of_int i)) eqn:GET; inv H0. simpl. split.
        ** left. apply plus_one. eapply input_MemGet; eauto.
        ** constructor; auto.
      * destruct d as [ftgt ltgt]. repeat sdo_ok.
        destruct (bool_of_int i) eqn:BOOLGUARD; inv HDO; simpl.
        ** exists (State (v, l, rm) stk (state_mem ms1)). split.
           *** left. apply plus_one. eapply input_Assume_holds; eauto.
           *** constructor; auto.
        ** repeat sdo_ok. simpl. exists (Deoptstate ftgt ltgt r stk (state_mem ms1)). split.
           *** left. eapply plus_one. eapply input_Assume_fails; eauto.
           *** constructor; auto.
      * destruct d. inv HDO.    (* Anchors are blocking outside of the middle-end *)
Qed.
