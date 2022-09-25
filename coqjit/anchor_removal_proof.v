(* Correctness proof of the Anchor Removal pass *)

Require Import IR.
Require Import anchor_removal.
Require Import sem_properties.
Require Import internal_simulations.
Require Import common.
Require Import IR.
Require Import IRinterpreter.
Require Import Errors.
Require Import monad.
Require Import monad_impl.
Require Import mixed_sem.
Require Import sem_properties.
Require Import customSmallstep.
Require Import assume_insertion_proof.
Require Import IRtoRTLblock_proof.

(* Matching stackframes: a version may have been replaced with its lowered version *)
Inductive match_stackframe: stackframe -> stackframe -> Prop :=
| frame_same: forall sf, match_stackframe sf sf
| frame_lowered:
    forall r v lbl rm vlow
      (LOW: lowering_version v = vlow),
      match_stackframe (IR_SF (r, v, lbl, rm)) (IR_SF (r, vlow, lbl, rm)).

(* Generalizing match_stackframe to the entire stack *)
Inductive match_stack: stack -> stack -> Prop :=
| match_nil:
    match_stack nil nil
| match_cons:
    forall s s' sf sf'
      (MS: match_stack s s')
      (MSF: match_stackframe sf sf'),
      match_stack (sf::s) (sf'::s').

Lemma match_stack_same:
  forall s, match_stack s s.
Proof.
  intros. induction s; constructor. auto. apply frame_same.
Qed.

Lemma match_app:
  forall synth s s',
    (match_stack) s s' ->
    (match_stack) (synth++s) (synth++s').
Proof.
  intros. induction synth.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. apply match_cons. auto. constructor.
Qed.


(** * Lowering Properties *)
(* adapted to the new implementation of PTrees *)
Lemma map1'_same:
  forall m,
    (forall (pc : label) (i : instruction), (PTree.Nodes m) ! pc = Some i -> ~ is_spec i) ->
    (PTree.map1' transf_instr m) = m.
Proof.
  intros. induction m; auto.
  - simpl. f_equal.
    + apply IHm. intros. apply H with (pc:=(pc~1)%positive).
      unfold PTree.get. simpl. unfold PTree.get in H0. auto.
  - simpl. f_equal.
    + destruct a; auto. exfalso. eapply H with (pc:=1%positive).
      unfold PTree.get. simpl. eauto. constructor.
  - simpl. f_equal.
    + destruct a; auto. exfalso. eapply H with (pc:=1%positive).
      unfold PTree.get. simpl. eauto. constructor.
    + apply IHm. intros. apply H with (pc:=(pc~1)%positive).
      unfold PTree.get. simpl. unfold PTree.get in H0. auto.
  - simpl. f_equal.
    + apply IHm. intros. apply H with (pc:=(pc~0)%positive).
      unfold PTree.get. simpl. unfold PTree.get in H0. auto.
  - simpl. f_equal.
    + apply IHm1. intros. apply H with (pc:=(pc~0)%positive).
      unfold PTree.get. simpl. unfold PTree.get in H0. auto.
    + apply IHm2. intros. apply H with (pc:=(pc~1)%positive).
      unfold PTree.get. simpl. unfold PTree.get in H0. auto.
  - simpl. f_equal.
    + apply IHm. intros. apply H with (pc:=(pc~0)%positive).
      unfold PTree.get. simpl. unfold PTree.get in H0. auto.
    + destruct a; auto. exfalso. eapply H with (pc:=1%positive).
      unfold PTree.get. simpl. eauto. constructor.
  - simpl. f_equal.
    + apply IHm1. intros. apply H with (pc:=(pc~0)%positive).
      unfold PTree.get. simpl. unfold PTree.get in H0. auto.
    + destruct a; auto. exfalso. eapply H with (pc:=1%positive).
      unfold PTree.get. simpl. eauto. constructor.
    + apply IHm2. intros. apply H with (pc:=(pc~1)%positive).
      unfold PTree.get. simpl. unfold PTree.get in H0. auto.
Qed.    

Lemma base_low_refl_code:
  forall c,
    base_code c ->
    lowering_code c = c.
Proof.
  intros c H. unfold base_code in H. unfold lowering_code.
  unfold PTree.map1. destruct c eqn:TREE; auto. f_equal. apply map1'_same. auto.
Qed.


Lemma fn_base_low:
  forall f,
    lowering_version (fn_base f) = fn_base f.
Proof.
  intros f. unfold lowering_version. rewrite base_low_refl_code.
  destruct f; simpl; auto. destruct fn_base; simpl; auto.
  destruct f. simpl. unfold base_version in base_no_spec. auto.
Qed.

Lemma base_low_refl:
  forall v,
    base_version v ->
    lowering_version v = v.
Proof.
  intros v H. unfold lowering_version. unfold base_version in H. rewrite base_low_refl_code; auto.
  destruct v. simpl. auto.
Qed.

Lemma same_params:
  forall f,
    (fn_params f) = (fn_params (lowering_function f)).
Proof.
  intros. unfold lowering_function. destruct (fn_opt f); simpl; auto.
Qed.

Lemma same_entry:
  forall f,
    ver_entry (current_version f) = ver_entry (current_version (lowering_function f)).
Proof.
  intros f. unfold lowering_function. destruct (fn_opt f) eqn:OPT; simpl; auto.
  unfold current_version. rewrite OPT. auto.
Qed.

Lemma lowering_current:
  forall f, lowering_version (current_version f) = current_version (lowering_function f).
Proof.
  intros f. unfold lowering_function. destruct (fn_opt f) eqn:OPT; simpl; auto.
  unfold current_version. rewrite OPT. simpl. auto.
  unfold current_version. rewrite OPT. apply fn_base_low.
Qed.

(** * Match states invariant  *)
(* This proof is a lockstep backward internal simulation.
   Each step of the optimized program is matched with a step of the source.
   No index is needed for the match_states invariant.
   Anchor steps are matched with Nop steps.

<<
                 
       st1 --------------- st2
        |                   |
       t|                   |t
        |                   |
        v                   v
       st1'--------------- st2'
                 
>>
*)

Inductive match_states (p:program) : unit -> mixed_state -> mixed_state -> Prop :=
| lowered_match:
    forall stk stk' v vlow pc rm top heap
      (LOW: lowering_version v = vlow)
      (MATCHSTACK: match_stack stk stk'),
      (match_states p) tt
        (Halt_IR (v, pc, rm), mkmut stk top heap)
        (Halt_IR (vlow, pc, rm), mkmut stk' top heap)
| refl_match:
    forall synchro stk stk' top heap 
      (MATCHSTACK: match_stack stk stk'),
      (match_states p) tt (synchro, mkmut stk top heap) (synchro, mkmut stk' top heap).

Inductive order : unit -> unit -> Prop := .
Lemma wfounded:
  well_founded order.
Proof.
  unfold well_founded. intros. destruct a. constructor. intros. inv H.
Qed.

Lemma trans:
  Relation_Definitions.transitive _ order.
Proof.
  unfold Relation_Definitions.transitive. intros. inv H.
Qed.

(** * Code preservation properties  *)
Lemma preserved_code:
  forall v vlow i pc,
    lowering_version v = vlow ->  
    (ver_code vlow) # pc = Some i ->
    exists i', (ver_code v) # pc = Some i' /\ transf_instr i' = i.
Proof.
  intros v vlow i pc LOW CODE. unfold lowering_version in LOW. rewrite <- LOW in CODE.
  simpl in CODE. unfold lowering_code in CODE.
  rewrite PTree.gmap1 in CODE. unfold option_map in CODE.
  destruct ((ver_code v)!pc); inv CODE.
  exists i0. split; auto.
Qed.

Lemma code_preserved:
  forall v vlow i pc,
    lowering_version v = vlow ->  
    (ver_code v) # pc = Some i ->
    (ver_code vlow) # pc = Some (transf_instr i).
Proof.
  intros v vlow i pc LOW CODE. unfold lowering_version in LOW. rewrite <- LOW. simpl.
  unfold lowering_code. rewrite PTree.gmap1. unfold option_map. rewrite CODE. auto.
Qed.

Lemma base_version_unchanged:
  forall p fid,
    find_base_version fid p = find_base_version fid (lowering p).
Proof.
  intros. unfold find_base_version, lowering, find_function_ir.
  simpl. rewrite PTree.gmap1. unfold option_map.
  destruct ((prog_funlist p)!fid) eqn:FINDF; auto.
  unfold lowering_function. destruct (fn_opt f); auto.
Qed.

Lemma find_function_lowered:
  forall p fid f,
    find_function_ir fid (lowering p) = Some f ->
    exists f', find_function_ir fid p = Some f' /\ lowering_function f' = f.
Proof.
  intros p fid f H. unfold find_function_ir in *. unfold lowering in H. simpl in H.
  rewrite PTree.gmap1 in H. unfold option_map in H.
  destruct ((prog_funlist p)!fid) eqn:FINDF; inv H.
  exists f0. split; auto.
Qed.

Lemma lowered_find_function:
  forall p fid f,
    find_function_ir fid p = Some f ->
    find_function_ir fid (lowering p) = Some (lowering_function f).
Proof.
  unfold find_function_ir, lowering. intros p fid f FINDF. simpl.
  rewrite PTree.gmap1. unfold option_map. rewrite FINDF. auto.
Qed.

(** * Invariant preservation  *)
(* Lemma match_synth: *)
(*   forall p rm sl synthlow p0, *)
(*     p0 = lowering p -> *)
(*     specIR.synthesize_frame p0 rm sl synthlow -> *)
(*     exists synthsrc, specIR.synthesize_frame p rm sl synthsrc /\ match_stack synthsrc synthlow. *)
(* Proof. *)
(*   intros p rm sl synthlow p0 LOW SYNTH. *)
(*   induction SYNTH; intros. *)
(*   - exists nil. split; constructor. *)
(*   - specialize (IHSYNTH LOW). destruct IHSYNTH as [synthsrc [SYNTH' MATCH]]. exists ((Stackframe r version l update)::synthsrc). *)
(*     split. constructor; auto. *)
(*     rewrite LOW in FINDV. rewrite <- base_version_unchanged in FINDV. rewrite FINDV. auto. *)
(*     constructor; auto. constructor; auto. *)
(* Qed. *)

(* Lemma synth_match: *)
(*   forall p rm sl synth, *)
(*     specIR.synthesize_frame p rm sl synth -> *)
(*     exists synthlow, specIR.synthesize_frame (lowering p) rm sl synthlow. *)
(* Proof. *)
(*   intros p rm sl synth SYNTH. induction SYNTH. *)
(*   - exists nil. constructor. *)
(*   - destruct IHSYNTH as [sylow IHSYNTH]. *)
(*     rewrite base_version_unchanged in FINDV. *)
(*     exists (Stackframe r version l update::sylow). constructor; auto. *)
(* Qed. *)

Lemma app_match:
  forall synth synthlow s slow,
    match_stack s slow ->
    match_stack synth synthlow ->
    match_stack (synth++s) (synthlow++slow).
Proof.
  intros. induction H0.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. apply match_cons; auto.
Qed.


(* for backward simulations, safety of the source must be shown to be preserved *)
Lemma safe_preserved_state:
  forall p nc i s v pc rm top heap s2,
    match_states p i (Halt_IR (v,pc,rm), mkmut s top heap) s2 ->
    safe (mixed_sem p None nc AnchorOn) (Halt_IR (v,pc,rm), mkmut s top heap) ->
    exists t, exists s2', mixed_step AnchorOn (lowering p) None nc s2 t s2'.
Proof.
  intros p nc i s v pc rm top heap s2 MATCH SAFE. inv MATCH.
  (* lowered match *)
  { apply safe_step in SAFE as [[t [nexts STEP]]|[r FINAL]]. 2: inv FINAL.
    exists t. inv STEP.
    - unfold ir_step in STEP0. repeat sdo_ok. unfold ir_int_step in HDO.
      { destruct ((ver_code v)!pc) eqn:CODE.
        2: { simpl in HDO. inv HDO. }
        repeat sdo_ok. inv HDO1.
        eapply code_preserved in CODE as SAME_CODE; eauto.
        destruct i0; repeat sdo_ok.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite SAME_CODE. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite SAME_CODE. simpl.
            unfold fret'. rewrite HDO. simpl. eauto.
          - simpl in HDO. repeat sdo_ok.
            unfold n_push_interpreter_stackframe in HDO0. simpl in HDO0. destruct top; inv HDO0.
            econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite SAME_CODE. simpl.
            unfold sbind. unfold n_push_interpreter_stackframe. simpl. rewrite HDO. simpl. eauto.
          - destruct (bool_of_int i) eqn:BOOL; repeat sdo_ok.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite SAME_CODE. simpl.
              rewrite HDO1. simpl. rewrite BOOL. simpl. eauto.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite SAME_CODE. simpl.
              rewrite HDO1. simpl. rewrite BOOL. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite SAME_CODE. simpl.
            rewrite HDO. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite SAME_CODE. simpl.
            rewrite HDO. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite SAME_CODE. simpl.
            rewrite HDO1. simpl. rewrite HDO. simpl. unfold sbind. unfold n_memset in HDO2.
            unfold n_memset. destruct (Integers.Int.lt i mem_size). inv HDO2. eauto. inv HDO2.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite SAME_CODE. simpl.
            rewrite HDO. simpl. unfold sbind. unfold n_memget in HDO1.
            unfold n_memget. destruct (Integers.Int.lt i mem_size). inv HDO1. 2: inv HDO1.
            simpl. destruct (heap ! (intpos.pos_of_int i)); inv H0. eauto.
          - destruct d. repeat sdo_ok. destruct (bool_of_int i) eqn:BOOL; repeat sdo_ok.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite SAME_CODE. simpl.
              rewrite HDO1. simpl. rewrite BOOL. simpl. eauto.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite SAME_CODE. simpl.
              rewrite HDO1. simpl. rewrite BOOL. simpl. rewrite HDO. simpl. eauto.
          - destruct d. repeat sdo_ok. inv HDO. }
    - eapply code_preserved in ANCHOR as CODE; eauto.
      econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE. simpl. eauto.
    - eapply code_preserved in ANCHOR as CODE; eauto.
      econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE. simpl. eauto. }
  (* refl match *)
  { apply safe_step in SAFE as [[t [nexts STEP]]|[r FINAL]]. 2: inv FINAL.
    exists t. inv STEP.
    - unfold ir_step in STEP0. repeat sdo_ok. unfold ir_int_step in HDO.
      { destruct ((ver_code v)!pc) eqn:CODE.
        2: { simpl in HDO. inv HDO. }
        repeat sdo_ok. inv HDO1.
        destruct i0; repeat sdo_ok.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE. simpl.
            unfold fret'. rewrite HDO. simpl. eauto.
          - simpl in HDO. repeat sdo_ok.
            unfold n_push_interpreter_stackframe in HDO0. simpl in HDO0. destruct top; inv HDO0.
            econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE. simpl.
            unfold sbind. unfold n_push_interpreter_stackframe. simpl. rewrite HDO. simpl. eauto.
          - destruct (bool_of_int i) eqn:BOOL; repeat sdo_ok.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE. simpl.
              rewrite HDO1. simpl. rewrite BOOL. simpl. eauto.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE. simpl.
              rewrite HDO1. simpl. rewrite BOOL. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE. simpl.
            rewrite HDO. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE. simpl.
            rewrite HDO. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE. simpl.
            rewrite HDO1. simpl. rewrite HDO. simpl. unfold sbind. unfold n_memset in HDO2.
            unfold n_memset. destruct (Integers.Int.lt i mem_size). inv HDO2. eauto. inv HDO2.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE. simpl.
            rewrite HDO. simpl. unfold sbind. unfold n_memget in HDO1.
            unfold n_memget. destruct (Integers.Int.lt i mem_size). inv HDO1. 2: inv HDO1.
            simpl. destruct (heap ! (intpos.pos_of_int i)); inv H0. eauto.
          - destruct d. repeat sdo_ok. destruct (bool_of_int i) eqn:BOOL; repeat sdo_ok.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE. simpl.
              rewrite HDO1. simpl. rewrite BOOL. simpl. eauto.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite CODE. simpl.
              rewrite HDO1. simpl. rewrite BOOL. simpl. rewrite HDO. simpl. eauto.
          - destruct d. repeat sdo_ok. inv HDO. }
    - econstructor. eapply Anchor_go_on; eauto. (* I could probably modify refl_match so we avoid these steps? *)
    - econstructor. eapply Anchor_deopt; eauto. }
Qed.


(* Proved directly with a backward simulation *)
Theorem lowering_correct:
  forall p nc newp,
    lowering p = newp ->
    backward_internal_simulation p newp None None nc nc AnchorOn AnchorOn.
Proof.
  intros. apply Backward_internal_simulation with (bsim_match_states:=match_states p) (bsim_order:=order).
  - apply wfounded.
  - unfold call_refl, p_reflexive. intros. exists tt. inv H0. destruct ms.
    eapply refl_match. apply match_stack_same.
  - intros i s1 s2 r MATCH SAFE FINAL.
    inv FINAL. inv MATCH. econstructor. split. eapply star_refl. constructor.

  - intros i s1 s2 MATCH SAFE.  (* progress preserved *)
    inv MATCH.
    + eapply safe_preserved_state in SAFE as [t [s2' STEP]]. 2: constructor; eauto.
      right. exists t. exists s2'. auto.
    +
      { assert (IS_SAFE: safe (mixed_sem p None nc AnchorOn) (synchro, {| state_stack := stk; state_stacktop := top; state_mem := heap |})) by auto.
        apply safe_step in IS_SAFE as [[t [nexts STEP]]|[r FINAL]].
        2: { inv FINAL. left. exists r. constructor. }
        right. inv STEP.
        + destruct irs, p0. eapply safe_preserved_state in SAFE as [t' [s2' STEP]].
          2: { apply refl_match. apply MATCHSTACK. }
          exists t'. exists s2'. auto.
        + destruct ms1. eapply addstk_same in STEP0 as [s [APP SAME]]; eauto.
          2: apply addstk_asmstep.
          exists t. econstructor. eapply x86_step. simpl. eauto.
        + econstructor. econstructor. eapply rtl_step; eauto.
        + destruct ms2, ms3. eapply addstk_same in CALLEE as [s [APP SAME]]; eauto.
          2: apply addstk_callee.
          eapply addstk_prim_same in NOT_COMPILED as [stk2 [APP2 SAME2]]; try constructor.
          apply app_same in APP2. subst.
          eapply addstk_same in ARGS as [s3 [APP3 SAME3]]; eauto.
          2: apply addstk_get_args.
          econstructor. econstructor.
          eapply Call_IR with (func:=lowering_function func); eauto.
          * unfold lowering. simpl. rewrite PTree.gmap1. unfold lowering_function, option_map.
            rewrite GETF. auto.
          * rewrite <- same_params. eauto.
    + destruct ms2, ms3, ms4. eapply addstk_same in CALLEE as [s [APP SAME]]; eauto.
      2: apply addstk_callee.
      eapply addstk_prim_same in COMPILED as [stk2 [APP2 SAME2]]; try constructor.
      apply app_same in APP2. subst.
      eapply addstk_same in ARGS as [stk3 [APP3 SAME3]]. 2: apply addstk_set_args. subst.
      eapply addstk_prim_same in LOAD as [stk4 [APP4 SAME4]]; try constructor. subst.
      exists E0. econstructor. eapply Call_x86; eauto.
    + inv RTL. 
    + inv RTL_BLOCK. 
    + destruct ms1. unfold jit.get_retval in RETVAL. destruct loc eqn:LOC.
      * destruct top eqn:TOP; inv RETVAL.
        simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
        destruct state_stacktop; inv OPEN_SF.
        inv MATCHSTACK; inv H0. destruct sf; inv H1.
        2: { destruct a, p, p0, p. inv H0. }
        inv MSF.
        ** econstructor. econstructor. eapply Return_IR; eauto.
           simpl. unfold sbind. simpl. eauto.
           simpl. unfold n_open_stackframe. simpl. eauto.
        ** econstructor. econstructor. eapply Return_IR; eauto.
           simpl. unfold sbind. simpl. eauto.
           simpl. unfold n_open_stackframe. simpl. eauto.
      * inv RETVAL.
        simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
        destruct state_stacktop; inv OPEN_SF.
        inv MATCHSTACK; inv H0. destruct sf; inv H1.
        2: { destruct a, p, p0, p. inv H0. }
        inv MSF.
        ** econstructor. econstructor. eapply Return_IR; eauto.
           simpl. unfold sbind. simpl. eauto.
           simpl. unfold n_open_stackframe. simpl. eauto.
        ** econstructor. econstructor. eapply Return_IR; eauto.
           simpl. unfold sbind. simpl. eauto.
           simpl. unfold n_open_stackframe. simpl. eauto.
    + destruct loc.
      * simpl in RETVAL.  repeat sdo_ok.  unfold n_load in HDO. simpl in HDO.
        destruct top; inv HDO.
        simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
        destruct top; inv OPEN_SF. destruct stk; inv H0. destruct s; inv H1.
        destruct a, p, p0, p. inv H0. inv MATCHSTACK. inv MSF.
        simpl in SET_RETVAL. unfold n_save in SET_RETVAL. inv SET_RETVAL.
        simpl in LOAD_CONT. repeat sdo_ok. unfold n_load_prog_code in HDO. simpl in HDO.
        destruct (nc ! (intpos.pos_of_int caller_fid)) eqn:LOADC; inv HDO.
        destruct a. simpl in LOAD_CONT.
        destruct (t ! (intpos.pos_of_int cont_lbl)) eqn:LOAD; inv LOAD_CONT.
        econstructor. econstructor. eapply Return_x86.
        ** simpl. unfold sbind. unfold n_load. simpl. eauto.
        ** simpl. unfold n_open_stackframe. simpl. eauto.
        ** simpl. unfold n_save. simpl. eauto.
        ** simpl. unfold sbind. unfold n_load_prog_code. simpl. rewrite LOADC. simpl. rewrite LOAD. eauto.
        ** eauto.
      * inv RETVAL. simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
        destruct top; inv OPEN_SF. destruct stk; inv H0. destruct s; inv H1.
        destruct a, p, p0, p. inv H0. inv MATCHSTACK. inv MSF.
        simpl in SET_RETVAL. unfold n_save in SET_RETVAL. inv SET_RETVAL.
        simpl in LOAD_CONT. repeat sdo_ok. unfold n_load_prog_code in HDO. simpl in HDO.
        destruct (nc ! (intpos.pos_of_int caller_fid)) eqn:LOADC; inv HDO.
        destruct a. simpl in LOAD_CONT.
        destruct (t ! (intpos.pos_of_int cont_lbl)) eqn:LOAD; inv LOAD_CONT.
        econstructor. econstructor. eapply Return_x86.
        ** simpl. auto.
        ** simpl. unfold n_open_stackframe. simpl. eauto.
        ** simpl. unfold n_save. simpl. eauto.
        ** simpl. unfold sbind. unfold n_load_prog_code. simpl. rewrite LOADC. simpl. rewrite LOAD. eauto.
        ** eauto.
    + inv RTL. 
    + inv RTL_BLOCK. 
    + destruct loc.
      * destruct top; inv RETVAL. inv OPEN_SF. unfold n_open_stackframe in H0. simpl in H0.
        destruct top; inv H0. destruct stk; inv H1.
        2: { destruct s; inv H0. destruct a, p, p0, p; inv H1. }
        inv MATCHSTACK. econstructor. econstructor. eapply Return_EOE; eauto.
        simpl. unfold sbind. simpl. eauto.
        simpl. unfold n_open_stackframe. simpl. eauto.
      * inv RETVAL. inv OPEN_SF. unfold n_open_stackframe in H0. simpl in H0.
        destruct top; inv H0. destruct stk; inv H1.
        2: { destruct s; inv H0. destruct a, p, p0, p; inv H1. }
        inv MATCHSTACK. econstructor. econstructor. eapply Return_EOE; eauto.
        simpl. unfold sbind. simpl. eauto.
        simpl. unfold n_open_stackframe. simpl. eauto.
    + destruct ms1, ms2. eapply addstk_same in TARGET as [s [APP SAME]].
      2: apply addstk_target.
      eapply addstk_same in BUILD_RM as [s2 [APP2 SAME2]].
      2: apply addstk_build.
      econstructor. econstructor. eapply Deopt with (func:=lowering_function func); eauto.
      unfold lowering. simpl. rewrite PTree.gmap1. unfold option_map. rewrite FINDF. auto.
    + destruct ms1. eapply addstk_same in PRIM_CALL as [s [APP SAME]].
      2: { unfold ASMinterpreter.prim_sem_dec. repeat addstk_auto. }
      econstructor. econstructor. eapply RTL_prim; eauto.
    + econstructor. econstructor. eapply RTL_end; eauto.
    + econstructor. econstructor. eapply RTL_block_end; eauto.
    + econstructor. econstructor. eapply Anchor_go_on; eauto.
    + econstructor. econstructor. eapply Anchor_deopt; eauto. }
      
      (* Simulation diagram *)

  - intros s2 t s2' STEP i s1 MATCH SAFE. exists tt. inv MATCH.
    +                           (* lowered_match *)
      inv STEP.
      { unfold ir_step, ir_int_step in STEP0; repeat sdo_ok.
        eapply preserved_code in HDO1 as [i' [SAME_CODE TRANSF]]; eauto.
        destruct i; destruct i'; inv TRANSF; repeat sdo_ok.
        - econstructor. split.
            * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
              rewrite SAME_CODE. simpl. eauto.
            * simpl. eapply lowered_match; eauto.
        -                       (* OPT is Nope, while SRC is Anchor  *)
          (* we need to know that deopt conditions are right, it comes from safety *)
          assert (exists newrm, update_regmap v0 rm = OK newrm).
          { apply safe_step_ir in SAFE as [t [s' STEP]]. inv STEP; eauto.
            - unfold ir_step, ir_int_step in STEP0. rewrite SAME_CODE in STEP0. simpl in STEP0.
              inv STEP0. destruct d. inv H0.
            - rewrite ANCHOR in SAME_CODE. inv SAME_CODE. eauto.
            - rewrite ANCHOR in SAME_CODE. inv SAME_CODE. eauto. }
          destruct H as [newrm UPD].
          econstructor. split.
          * left. apply plus_one. destruct d. eapply Anchor_go_on; eauto.
          * simpl. eapply lowered_match; eauto.
        - econstructor. split.
          * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
            rewrite SAME_CODE. simpl. rewrite HDO. simpl. eauto.
          * eapply lowered_match; eauto.
        - simpl in HDO. repeat sdo_ok. unfold n_push_interpreter_stackframe in HDO0.
          simpl in HDO0. destruct top; inv HDO0.
          econstructor. split.
          * left. apply plus_one. eapply IR_step; eauto. unfold ir_step, ir_int_step.
            rewrite SAME_CODE. simpl. unfold sbind. unfold n_push_interpreter_stackframe.
            simpl. rewrite HDO. simpl. eauto.
          * simpl. eapply refl_match; eauto. constructor; auto.
            eapply frame_lowered; eauto. 
        - destruct (bool_of_int i) eqn:BOOL; repeat sdo_ok.
          * econstructor. split.
            ** left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
               rewrite SAME_CODE. simpl. rewrite HDO1. simpl. rewrite BOOL. simpl. eauto.
            ** eapply lowered_match; eauto. 
          * econstructor. split.
            ** left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
               rewrite SAME_CODE. simpl. rewrite HDO1. simpl. rewrite BOOL. simpl. eauto.
            ** eapply lowered_match; eauto. 
        - econstructor. split.
          * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
            rewrite SAME_CODE. simpl. rewrite HDO. simpl. eauto.
          * simpl. eapply refl_match; eauto.
        - econstructor. split.
          * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
            rewrite SAME_CODE. simpl. rewrite HDO. simpl. eauto.
          * eapply lowered_match; eauto. 
        - unfold n_memset in HDO2. destruct (Integers.Int.lt i mem_size) eqn:RANGE; inv HDO2.
          econstructor. split.
          * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
            rewrite SAME_CODE. simpl. rewrite HDO. simpl. rewrite HDO1. simpl.
            unfold n_memset. rewrite RANGE. unfold sbind. simpl. eauto.
          * eapply lowered_match; eauto. 
        - unfold n_memget in HDO1. destruct (Integers.Int.lt i mem_size) eqn:RANGE; inv HDO1.
          destruct (heap ! (intpos.pos_of_int i)) eqn:HEAP; inv H0.
          econstructor. split.
          * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
            rewrite SAME_CODE. simpl. rewrite HDO. simpl. 
            unfold n_memget. rewrite RANGE. unfold sbind. simpl. rewrite HEAP. eauto.
          * eapply lowered_match; eauto. 
        - destruct d. repeat sdo_ok. destruct (bool_of_int i) eqn:BOOL; repeat sdo_ok.
          * econstructor. split.
            ** left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
               rewrite SAME_CODE. simpl. rewrite HDO1. simpl. rewrite BOOL. simpl. eauto.
            ** eapply lowered_match; eauto. 
          * econstructor. split.
            ** left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
               rewrite SAME_CODE. simpl. rewrite HDO1. simpl. rewrite BOOL. rewrite HDO. simpl. eauto.
            ** simpl. eapply refl_match; eauto. }
      * unfold lowering_version in ANCHOR. simpl in ANCHOR.
        unfold lowering_code in ANCHOR. rewrite PTree.gmap1 in ANCHOR. unfold option_map in ANCHOR.
        destruct ((ver_code v)!pc) eqn:CODE; inv ANCHOR.
        destruct i; inv H0.
      * unfold lowering_version in ANCHOR. simpl in ANCHOR.
        unfold lowering_code in ANCHOR. rewrite PTree.gmap1 in ANCHOR. unfold option_map in ANCHOR.
        destruct ((ver_code v)!pc) eqn:CODE; inv ANCHOR.
        destruct i; inv H0.

    +                           (* refl_match *)
      { inv STEP.
        - destruct ms1. eapply addstk_same in STEP0 as [s [APP SAME]]; eauto.
          2: apply addstk_irstep.
          econstructor. split.
          + left. apply plus_one. eapply IR_step; eauto.
          + apply refl_match. subst. apply app_match; auto. apply match_stack_same.
        - destruct ms1. eapply addstk_same in STEP0 as [s [APP SAME]]; eauto.
          2: apply addstk_asmstep.
          econstructor. split.
          + left. apply plus_one. eapply x86_step; eauto.
          + apply refl_match. subst. apply app_match; auto. apply match_stack_same.
        - econstructor. split.
          + left. apply plus_one. eapply rtl_step; eauto.
          + apply refl_match; auto.
        - simpl in GETF. rewrite PTree.gmap1 in GETF. unfold option_map in GETF.
          destruct ((prog_funlist p)!fid)eqn:FINDF; inv GETF.
          destruct ms2. eapply addstk_same in CALLEE as [s [APP SAME]].
          2: apply addstk_callee.
          simpl in NOT_COMPILED. unfold n_check_compiled in NOT_COMPILED. simpl in NOT_COMPILED.
          destruct (nc!fid) eqn:NOT; inv NOT_COMPILED.
          destruct ms3. eapply addstk_same in ARGS as [s2 [APP2 SAME2]].
          2: apply addstk_get_args.
          econstructor. split.
          * left. apply plus_one. eapply Call_IR; eauto; simpl.
            ** unfold n_check_compiled. simpl. rewrite NOT. eauto.
            ** rewrite same_params. eauto.
          * simpl. rewrite same_entry. eapply lowered_match; eauto.
            apply lowering_current. rewrite APP2. apply match_app. apply match_app.  auto.
        - destruct loc.
          + simpl in CALLEE. repeat sdo_ok. unfold n_load in HDO. simpl in HDO. destruct top; inv HDO.
            simpl in COMPILED. unfold n_check_compiled in COMPILED. simpl in COMPILED.
            destruct (nc ! (intpos.pos_of_int i)) eqn:COMP; inv COMPILED.
            destruct ms3. eapply addstk_same in ARGS as [s [APP SAME]]; eauto.
            2: apply addstk_set_args.
            simpl in LOAD. repeat sdo_ok. unfold n_load_prog_code in HDO. simpl in HDO.
            rewrite COMP in HDO. inv HDO.
            econstructor. split.
            * left. apply plus_one. eapply Call_x86; eauto; simpl.
              ** unfold n_load, sbind. simpl. eauto.
              ** unfold n_check_compiled. simpl. rewrite COMP. eauto.
              ** unfold n_load_prog_code, sbind. simpl. rewrite COMP. eauto.
            * eapply refl_match. apply app_match; auto. apply match_stack_same.
          + simpl in CALLEE. inv CALLEE.
            simpl in COMPILED. unfold n_check_compiled in COMPILED. simpl in COMPILED.
            destruct (nc ! fid) eqn:COMP; inv COMPILED.
            destruct ms3. eapply addstk_same in ARGS as [s [APP SAME]]; eauto.
            2: apply addstk_set_args.
            simpl in LOAD. repeat sdo_ok. unfold n_load_prog_code in HDO. simpl in HDO.
            rewrite COMP in HDO. inv HDO.
            econstructor. split.
            * left. apply plus_one. eapply Call_x86; eauto; simpl.
              ** unfold n_load, sbind. simpl. eauto.
              ** unfold n_check_compiled. simpl. rewrite COMP. eauto.
              ** unfold n_load_prog_code, sbind. simpl. rewrite COMP. eauto.
            * eapply refl_match. apply app_match; auto. apply match_stack_same.
        - inv RTL. 
        - inv RTL_BLOCK. 
        - destruct loc.
          + simpl in RETVAL; repeat sdo_ok. unfold n_load in HDO. simpl in HDO. destruct top; inv HDO.
            simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
            destruct top; inv OPEN_SF. destruct stk'; inv H0. destruct s; inv H1.
            2: { destruct a,p,p0,p. inv H0. }
            inv MATCHSTACK. inv MSF.
            * econstructor. split. (* returning to the same version *)
              ** left. apply plus_one. eapply Return_IR; eauto.
                 *** simpl. unfold n_load, sbind. simpl. eauto.
                 *** simpl. unfold n_open_stackframe. simpl. eauto.
              ** eapply refl_match; eauto.
            * econstructor. split. (* Returning to a function that was lowered in opt *)
              ** left. apply plus_one. eapply Return_IR; eauto.
                 *** simpl. unfold n_load, sbind. simpl. eauto.
                 *** simpl. unfold n_open_stackframe. simpl. eauto.
              ** eapply lowered_match; eauto.
          + simpl in RETVAL. inv RETVAL.
            simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
            destruct top; inv OPEN_SF. destruct stk'; inv H0. destruct s; inv H1.
            2: { destruct a,p,p0,p. inv H0. }
            inv MATCHSTACK. inv MSF.
            * econstructor. split. (* Returning to the same version *)
              ** left. apply plus_one. eapply Return_IR; eauto.
                 *** simpl. eauto.
                 *** simpl. unfold n_open_stackframe. simpl. eauto.
              ** eapply refl_match; eauto.
            * econstructor. split. (* Returning to a function that was lowered in opt *)
              ** left. apply plus_one. eapply Return_IR; eauto.
                 *** simpl. eauto.
                 *** simpl. unfold n_open_stackframe. simpl. eauto.
              ** eapply lowered_match; eauto.
        - destruct loc.
          + simpl in RETVAL. repeat sdo_ok. unfold n_load in HDO. simpl in HDO. destruct top; inv HDO.
            simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
            destruct top; inv OPEN_SF. destruct stk'; inv H0. destruct s; inv H1. destruct a, p, p0, p.
            inv H0. simpl in SET_RETVAL. unfold n_save in SET_RETVAL. simpl in SET_RETVAL. inv SET_RETVAL.
            simpl in LOAD_CONT. repeat sdo_ok. destruct a.
            unfold n_load_prog_code in HDO. simpl in HDO. destruct (nc!(intpos.pos_of_int caller_fid)) eqn:LOAD; inv HDO.
            simpl in LOAD_CONT.
            destruct (t!(intpos.pos_of_int cont_lbl)) eqn:LOAD2; inv LOAD_CONT.
            inv MATCHSTACK. inv MSF.
            econstructor. split.
            * left. apply plus_one. eapply Return_x86; eauto; simpl.
              ** unfold n_load, sbind. simpl. eauto.
              ** unfold n_open_stackframe. simpl. eauto.
              ** unfold n_save. simpl. eauto.
              ** unfold n_load_prog_code, sbind. simpl.  rewrite LOAD. simpl. rewrite LOAD2. eauto.
            * eapply refl_match. auto.
          + simpl in RETVAL. inv RETVAL.
            simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
            destruct top; inv OPEN_SF. destruct stk'; inv H0. destruct s; inv H1. destruct a, p, p0, p.
            inv H0. simpl in SET_RETVAL. unfold n_save in SET_RETVAL. simpl in SET_RETVAL. inv SET_RETVAL.
            simpl in LOAD_CONT. repeat sdo_ok. destruct a.
            unfold n_load_prog_code in HDO. simpl in HDO. destruct (nc!(intpos.pos_of_int caller_fid)) eqn:LOAD; inv HDO.
            simpl in LOAD_CONT.
            destruct (t!(intpos.pos_of_int cont_lbl)) eqn:LOAD2; inv LOAD_CONT.
            inv MATCHSTACK. inv MSF.
            econstructor. split.
            * left. apply plus_one. eapply Return_x86; eauto; simpl.
              ** unfold n_load, sbind. simpl. eauto.
              ** unfold n_open_stackframe. simpl. eauto.
              ** unfold n_save. simpl. eauto.
              ** unfold n_load_prog_code, sbind. simpl.  rewrite LOAD. simpl. rewrite LOAD2. eauto.
            * eapply refl_match. auto.
        - inv RTL. 
        - inv RTL_BLOCK. 
        - destruct loc.
          + simpl in RETVAL. repeat sdo_ok. unfold n_load in HDO. simpl in HDO. destruct top; inv HDO.
            simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
            destruct top; inv OPEN_SF. destruct stk'; inv H0.
            2: { destruct s; inv H1. destruct a, p, p0, p. inv H0. }
            inv MATCHSTACK.
            econstructor. split.
            * left. apply plus_one. eapply Return_EOE; eauto; simpl.
              ** unfold n_load, sbind. simpl. eauto.
              ** unfold n_open_stackframe. simpl. eauto.
            * eapply refl_match; eauto. constructor.
          + simpl in RETVAL. inv RETVAL.
            simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
            destruct top; inv OPEN_SF. destruct stk'; inv H0.
            2: { destruct s; inv H1. destruct a, p, p0, p. inv H0. }
            inv MATCHSTACK.
            econstructor. split.
            * left. apply plus_one. eapply Return_EOE; eauto; simpl.
              ** unfold n_load, sbind. simpl. eauto.
              ** unfold n_open_stackframe. simpl. eauto.
            * eapply refl_match; eauto. constructor.
        - destruct ms1, ms2. eapply addstk_same in TARGET as [s [APP SAME]]; eauto.
          2: apply addstk_target.
          eapply addstk_same in BUILD_RM as [s2 [APP2 SAME2]]; eauto.
          2: apply addstk_build.
          unfold lowering in FINDF. simpl in FINDF. rewrite PTree.gmap1 in FINDF. unfold option_map in FINDF.
          destruct ((prog_funlist p)!ftgt) eqn:FIND; inv FINDF.
          econstructor. split.
          * left. apply plus_one. eapply Deopt; eauto; simpl.
          * eapply lowered_match; eauto. rewrite fn_base_low. unfold lowering_function.
            destruct (fn_opt f); simpl; auto.
            apply match_app. apply match_app. auto.
        - destruct ms1. eapply addstk_same in PRIM_CALL as [s [APP SAME]].
          2: { unfold ASMinterpreter.prim_sem_dec. repeat addstk_auto. }
          econstructor. split.
          + left. apply plus_one. eapply RTL_prim; eauto.
          + eapply refl_match. subst. apply match_app. auto.
        - econstructor. split.
          + left. apply plus_one. eapply RTL_end; eauto.
          + eapply refl_match. auto.
        - econstructor. split.
          + left. apply plus_one. eapply RTL_block_end; eauto.
          + eapply refl_match. auto.
        - econstructor. split.
          + left. apply plus_one. eapply Anchor_go_on; eauto.
          + eapply refl_match. auto.
        - econstructor. split.
          + left. apply plus_one. eapply Anchor_deopt; eauto.
          + eapply refl_match. auto.
      }
Qed.      


(** * Removing Anchors leads to Anchor-free programs  *)


Theorem lowering_no_anchor:
  forall p newp,
    lowering p = newp ->
    no_anchor newp.
Proof.
  intros. unfold lowering in H.
  unfold no_anchor. intros.
  unfold no_anchor_code. intros.
  rewrite <- H in H0. simpl in H0. rewrite PTree.gmap1 in H0. unfold option_map in H0.
  destruct ((prog_funlist p)!fid) eqn:FINDF; inv H0.
  unfold lowering_function in H1. destruct (fn_opt f0) eqn:OPT; inv H1.
  - eapply preserved_code in H2; eauto. destruct H2. destruct H. destruct x; inv H0.
  - rewrite OPT in H0. inv H0.
Qed.
