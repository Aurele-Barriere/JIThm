(* Correctness of the Assume Insertion pass *)
(* A pass of the middle-end optimizer *)
(* Inserts an Assume insertion just after an Anchor *)

Require Import internal_simulations.
Require Import sem_properties.
Require Import assume_insertion.
Require Import Coq.MSets.MSetPositive.
Require Import def_regs.
Require Import common.
Require Import IR.
Require Import IRinterpreter.
Require Import Errors.
Require Import monad.
Require Import monad_impl.
Require Import mixed_sem.
Require Import sem_properties.
Require Import customSmallstep.

Require Import IRtoRTLblock_proof.
(* so we can resue the addstk typing of the monads *)
(* TODO: We could get that in another file *)


(** * Matching the stack and properties  *)
(* Matching stackframes: a version may have been replaced with its optimized version *)
Inductive match_stackframe (v:version) (fid:fun_id) (guard:expr) (ancl:label) (params:list reg): stackframe -> stackframe -> Prop :=
| frame_same:
    forall sf, (match_stackframe v fid guard ancl params) sf sf
| frame_opt:
    forall r lbl rm vins abs
      (AS_INSERT: insert_assume_version v fid guard ancl params = OK vins)
      (DEFREGS: defined_regs_analysis (ver_code v) params (ver_entry v) = Some abs)
      (DEF: forall retval, defined (rm#r<-retval) (def_absstate_get lbl abs)),
      (match_stackframe v fid guard ancl params) (IR_SF (r, v, lbl, rm)) (IR_SF (r, vins, lbl, rm)).

(* Generalizing match_stackframe to the entire stack *)
Inductive match_stack (v:version) (fid:fun_id) (guard:expr) (ancl:label) (params:list reg): stack -> stack -> Prop :=
| match_nil:
    (match_stack v fid guard ancl params) nil nil
| match_cons:
    forall s s' sf sf'
      (MS: (match_stack v fid guard ancl params) s s')
      (MSF: (match_stackframe v fid guard ancl params) sf sf'),
      (match_stack v fid guard ancl params) (sf::s) (sf'::s').

Lemma match_stack_same:
  forall s v fid guard ancl params,
    (match_stack v fid guard ancl params) s s.
Proof.
  intros s v fid guard ancl. induction s; constructor. auto. constructor.
Qed.

Lemma match_app:
  forall synth s s' v fid guard ancl params,
    (match_stack v fid guard ancl params) s s' ->
    (match_stack v fid guard ancl params) (synth++s) (synth++s').
Proof.
  intros. induction synth.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. apply match_cons. auto. constructor.
Qed.

Lemma app_match:
  forall synth synthopt s s' v fid guard ancl params,
    (match_stack v fid guard ancl params) s s' ->
    (match_stack v fid guard ancl params) synth synthopt ->
    (match_stack v fid guard ancl params) (synth++s) (synthopt++s').
Proof.
  intros. induction H0.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. apply match_cons; auto.
Qed.

(** * Index and order used in the simulation *)
(* There is one stuttering step for each inserted Anchor *)
Inductive as_index: Type :=
| One : as_index
| Zero: as_index.

Inductive as_order: as_index -> as_index -> Type :=
| order: as_order Zero One.

Lemma wfounded: well_founded as_order.
Proof.
  unfold well_founded. intros a. constructor. intros y H. inv H. constructor. intros y H. inv H.
Qed.

Lemma trans: Relation_Definitions.transitive _ as_order.
Proof.
  unfold Relation_Definitions.transitive. intros x y z H H0. inv H. inv H0.
Qed.


(** * The match_states relation  *)
(* This proof is a backward internal simulation.
   At the Anchor instruction, we take a stuttering step if the Assume succeeds
   If it fails, we take a single step to the target version.

<<
                 
       st1 --------------- st2
        |                   |
       t|(1 or 2 steps)     |t
        |                   |
        v                   v
       st1'--------------- st2'
                 
>>
*)

Inductive match_states (p:program) (v:version) (fid:fun_id) (guard: expr) (ancl:label) (params:list reg): as_index -> mixed_state -> mixed_state -> Prop :=
                                        
| assume_match:                     (* matching at the assume instruction *)
    forall vins stk stk' top heap rm fresh fa la vm next (* newver *) newrm abs
      (MATCHSTACK: (match_stack v fid guard ancl params) stk stk')
      (OPT: insert_assume_version v fid guard ancl params = OK vins)
      (DEFREGS: defined_regs_analysis (ver_code v) params (ver_entry v) = Some abs)
      (DEF: defined rm (def_absstate_get ancl abs))
      (VALIDATE: validator v ancl guard params = OK tt)
      (FS_OPT: (ver_code vins) # ancl = Some (Anchor (fa,la) vm fresh))
      (AS_OPT: (ver_code vins) # fresh = Some (Assume guard (fa,la) vm next))
      (FS_SRC: (ver_code v) # ancl = Some (Anchor (fa,la) vm next))
      (* (FINDF: find_base_version fa p = Some newver) *)
      (UPDATE: update_regmap vm rm = OK newrm),
      (match_states p v fid guard ancl params) Zero
        (Halt_IR (v, ancl, rm), mkmut stk top heap)
        (Halt_IR (vins, fresh, rm), mkmut stk' top heap)
      
| opt_match:           (* matching inside the optimized version *)
    forall vins stk stk' top heap lbl rm abs
      (MATCHSTACK: (match_stack v fid guard ancl params) stk stk')
      (OPT: insert_assume_version v fid guard ancl params = OK vins)
      (DEFREGS: defined_regs_analysis (ver_code v) params (ver_entry v) = Some abs)
      (DEF: defined rm (def_absstate_get lbl abs)),
      (match_states p v fid guard ancl params) One
        (Halt_IR (v, lbl, rm), mkmut stk top heap)
        (Halt_IR (vins, lbl, rm), mkmut stk' top heap)
                                        
| refl_match:                   (* matching outside of the optimized version *)
    forall synchro stk stk' top heap
      (MATCHSTACK: (match_stack v fid guard ancl params) stk stk'),
      (match_states p v fid guard ancl params) Zero (synchro, mkmut stk top heap) (synchro, mkmut stk' top heap).
                                        
(* | final_match:                  (* matching final states -> should be taken care of by refl*) *)
(*     forall retval ms, *)
(*       (match_states p v fid guard ancl params) One (Final retval ms) (Final retval ms). *)

(** * Code preservation properties  *)
Lemma code_preservation':
  forall vsrc vins fid guard ancl lbl params,
    insert_assume_version vsrc fid guard ancl params = OK vins ->
    lbl <> ancl ->
    forall iopt isrc,
      (ver_code vins) # lbl = Some iopt ->
      (ver_code vsrc) # lbl = Some isrc ->
      iopt = isrc.
Proof.
  intros vsrc vins fid guard ancl lbl params OPT NOTFS iopt isrc CODEOPT CODESRC.
  unfold insert_assume_version in OPT. repeat do_ok.
  destruct (c!ancl) eqn:CODEFS; inv H1. destruct i; inv H0. repeat do_ok. destruct u.
  simpl in CODEOPT. inv HDO.
  poseq_destr (fresh_sug (Pos.succ ancl) (ver_code vsrc)) lbl.
  - erewrite fresh_sug_correct in CODESRC; auto. inv CODESRC.
  - rewrite PTree.gso in CODEOPT; auto. rewrite PTree.gso in CODEOPT; auto.
    rewrite CODESRC in CODEOPT. inv CODEOPT. auto.
Qed.

Lemma safe_step_ir:
  forall p rtl nc anc ms v pc rm,
    safe (mixed_sem p rtl nc anc) (Halt_IR (v, pc, rm), ms) ->
    exists t s', (mixed_step anc p rtl nc) (Halt_IR (v, pc, rm), ms) t s'.
Proof.
  intros p rtl nc anc ms v pc rm H. specialize (H (Halt_IR (v,pc,rm), ms) (star_refl _ _ _)).
  destruct H as [[r FINAL]|[t [s'' STEP]]]; eauto. inv FINAL.
Qed.

Lemma safe_step:
  forall p rtl nc anc synchro ms,
    safe (mixed_sem p rtl nc anc) (synchro, ms) ->
    (exists t s', (mixed_step anc p rtl nc) (synchro, ms) t s') \/ (exists r, synchro = EOE r).
Proof.
  intros p rtl nc anc synchro ms H.
  specialize (H (synchro, ms) (star_refl _ _ _)). destruct H as [[r FINAL]|[t [s'' STEP]]]; eauto. inv FINAL.
  right. eauto.
Qed.

Lemma step_code_ir:
  forall p rtl nc anc v pc rm ms news t,
    Step (mixed_sem p rtl nc anc) (Halt_IR (v, pc, rm), ms) t news ->
    exists i, (ver_code v) ! pc = Some i.
Proof.
  intros. inv H; eauto.
  unfold ir_step in STEP. repeat sdo_ok. unfold ir_int_step in HDO. repeat sdo_ok. eauto.
Qed.


Lemma safe_code:
  forall p rtl nc anc s v pc rm ms top,
    safe (mixed_sem p rtl nc anc) (Halt_IR (v, pc, rm), mkmut s top ms) ->
    exists i, (ver_code v) ! pc = Some i.
Proof.
  intros. apply safe_step_ir in H as [s' [t STEP]].
  eapply step_code_ir; simpl; eauto.
Qed.


Lemma code_preservation:        (* use at opt_match *)
  forall p p' rtl nc s s' rm top ms t news vsrc vins fid guard ancl lbl params,
    insert_assume_version vsrc fid guard ancl params = OK vins ->
    lbl <> ancl ->
    safe (mixed_sem p rtl nc AnchorOn) (Halt_IR (vsrc, lbl, rm), mkmut s top ms) ->
    Step (mixed_sem p' rtl nc AnchorOn) (Halt_IR (vins, lbl, rm), mkmut s' top ms) t news ->
    (ver_code vsrc) # lbl = (ver_code vins) # lbl.
Proof.
  intros p p' rtl nc s s' rm top ms t news vsrc vins fid guard ancl lbl params H H0 H1 H2.
  apply safe_code in H1 as [isrc CODESRC]. apply step_code_ir in H2 as [iopt CODEOPT].
  rewrite CODESRC. rewrite CODEOPT. f_equal. symmetry. eapply code_preservation'; eauto.
Qed.

(* The anchor instruction has been changed to point to the Assume *)
Lemma anchor_changed:
  forall vsrc fid guard vins ancl params,
    insert_assume_version vsrc fid guard ancl params = OK vins ->
    exists tgt vm fresh next,
      (ver_code vins) # ancl = Some (Anchor tgt vm fresh) /\
      (ver_code vsrc) # ancl = Some (Anchor tgt vm next) /\
      (ver_code vins) # fresh = Some (Assume guard tgt vm next).
Proof.
  intros vsrc fid guard vins ancl params OPT. unfold insert_assume_version in OPT. repeat do_ok.
  inv HDO. destruct ((ver_code vsrc)!ancl) eqn:FS_SRC; inv H1.
  destruct i eqn:ANCHOR; inv H0. repeat do_ok. exists d. exists v.
  exists (fresh_sug (Pos.succ ancl) (ver_code vsrc)). exists l. simpl.
  split; auto; try split; auto. 
  - poseq_destr (fresh_sug (Pos.succ ancl) (ver_code vsrc)) ancl.
    + erewrite fresh_sug_correct in FS_SRC; eauto. inv FS_SRC.
    + rewrite PTree.gso; auto. rewrite PTree.gss. auto.
  - rewrite PTree.gss. auto.
Qed.


Lemma preservation_code:
  forall vsrc vins fid guard ancl lbl params i,
    insert_assume_version vsrc fid guard ancl params = OK vins ->
    lbl <> ancl ->
    (ver_code vsrc) # lbl = Some i ->
    (ver_code vins) # lbl = Some i.
Proof.
  intros vsrc vins fid guard ancl lbl params i H H0 H1. unfold insert_assume_version in H. repeat do_ok.
  destruct (c!ancl) eqn:CODEFS. 2: inv H2. destruct i0; inv H2. repeat do_ok. simpl. inv HDO.
  rewrite PTree.gso. rewrite PTree.gso; auto. poseq_destr lbl (fresh_sug (Pos.succ ancl) (ver_code vsrc)); auto.
  erewrite fresh_sug_correct in H1; auto. inv H1.
Qed.
  

(** * Progress Preservation  *)
Lemma evaluate_reg:
  forall rm rs r,
    defined rm (DefFlatRegset.Inj rs) ->
    check_reg r rs = true ->
    exists v, eval_reg r rm = OK v.
Proof.
  intros rm rs r H H0.
  unfold check_reg in H0. rewrite PositiveSet.mem_spec in H0.
  unfold defined in H. apply H in H0. destruct H0. exists x. unfold eval_reg. rewrite H0. auto.
Qed.

Lemma evaluate_expr:
  forall rm rs e,
    defined rm (DefFlatRegset.Inj rs) ->
    check_expr e rs = true ->
    exists v, eval_expr e rm = OK v.
Proof.
  intros rm rs e H H0. destruct e; simpl in H0.
  - assert (H': exists v, eval_reg r rm = OK v /\ exists v0, eval_reg r0 rm = OK v0).
    { destruct b; try solve[inv H0]; apply andb_prop in H0; destruct H0; eauto;
        eapply evaluate_reg in H0; eapply evaluate_reg in H1; eauto; destruct H0; destruct H1; eauto. }
    destruct H' as [v [EV [v' EV']]]. destruct b; simpl; rewrite EV; rewrite EV'; simpl; eauto.
    inv H0.
  - eapply evaluate_reg in H0; eauto. destruct H0. destruct u; simpl; rewrite H0; simpl; eauto.
  - destruct z; simpl; eauto.
Qed.

Lemma base_version_set_version:
  forall vins f,
    base_version (set_version_function vins f) = base_version f.
Proof.
  intros vins f. unfold set_version_function, base_version. simpl. auto.
Qed.

Lemma current_version_set_version:
  forall vins f,
    current_version (set_version_function vins f) = vins.
Proof.
  intros vins f. unfold set_version_function, current_version. simpl. auto.
Qed.




(* Evaluating a guard if it uses defined registers should be defined *)
(* Lemma evaluate_succeeds: *)
(*   forall rm guard rs, *)
(*     defined rm (DefFlatRegset.Inj rs) -> *)
(*     check_guard guard rs = true -> *)
(*     exists v, eval_list_expr guard rm v. *)
(* Proof. *)
(*   intros rm guard rs H H0. induction guard; intros. *)
(*   - exists true. constructor. *)
(*   - simpl in H0. apply andb_prop in H0. destruct H0. eapply evaluate_expr in H0; eauto. *)
(*     destruct H0. destruct x. apply IHguard in H1. destruct H1. destruct z. *)
(*     + esplit. eapply eval_cons_false; eauto. *)
(*     + esplit. eapply eval_cons_true; eauto. unfold Zne. unfold not. intro. inv H1; inv H2. *)
(*     + esplit. eapply eval_cons_true; eauto. unfold Zne. unfold not. intro. inv H1; inv H2. *)
(* Qed. *)
(* DEPRECATED until we use lists *)

Ltac def_ok :=
  match goal with
  | [CODE: (ver_code ?vsrc) ! ?lbl = Some ?i |- _] =>
    eapply def_analyze_correct; eauto; simpl; auto; unfold def_dr_transf; try rewrite CODE; auto
  end.

Lemma progress_preserved:
  forall f vsrc vins fid guard ancl params s1 s2 p nc i,
    insert_assume_version vsrc fid guard ancl params = OK vins ->
    find_function_ir fid p = Some f ->
    vsrc = current_version f ->
    match_states p vsrc fid guard ancl params i s1 s2 ->
    safe (mixed_sem p None nc AnchorOn) s1 ->
    (exists r : Integers.Int.int, final_mixed_state (set_version p fid vins) s2 r) \/
    (exists (t : trace) (s2' : mixed_state),
        Step (mixed_sem (set_version p fid vins) None nc AnchorOn) s2 t s2').
Proof.
  intros f vsrc vins fid guard ancl params s1 s2 p nc i OPTV FINDOPT CURVER MATCH SAFE.
  inv MATCH.
  - unfold validator in VALIDATE. rewrite FS_SRC in VALIDATE. repeat do_ok.
    destruct (def_absstate_get ancl d) eqn:ABSDR; inv H0.
    destruct (check_expr guard r) eqn:CHECK; inv H1.
    inv DEFREGS. rewrite ABSDR in DEF. eapply evaluate_expr in CHECK as [v EVAL]; eauto.
    right. exists E0. rewrite OPT in OPTV. inv OPTV. destruct (bool_of_int v) eqn:BOOL.
    + econstructor. apply IR_step. unfold ir_step. rewrite exec_bind2. unfold sbind2, sbind.
      unfold ir_int_step. rewrite AS_OPT. simpl. rewrite exec_bind. unfold sbind, fret'.
      rewrite EVAL. simpl. rewrite BOOL. simpl. eauto.
    + econstructor. apply IR_step. unfold ir_step. rewrite exec_bind2. unfold sbind2, sbind.
      unfold ir_int_step. rewrite AS_OPT. simpl. rewrite exec_bind. unfold sbind, fret'.
      rewrite EVAL. simpl. rewrite BOOL. rewrite UPDATE. simpl. eauto.
      
  - poseq_destr lbl ancl.
    + rewrite OPT in OPTV. inv OPTV. unfold insert_assume_version in OPT. repeat do_ok.
      destruct (c!ancl) eqn:CODEFS; inv H1. destruct i; inv H0.
      right. exists E0. exists (Halt_IR (vins, (fresh_sug (Pos.succ ancl) c), rm), mkmut stk' top heap). 
      repeat do_ok. simpl. destruct d as [ftgt ltgt].
      apply safe_step_ir in SAFE as STEP. destruct STEP as [t [s'' STEP]].
      inv HDO. inv STEP.
      * exfalso. eapply ir_noanchor in STEP0; eauto.
      * rewrite ANCHOR in CODEFS. inv CODEFS. eapply Anchor_go_on; eauto. simpl. rewrite PTree.gso.
        rewrite PTree.gss. eauto. unfold not; intros H.
        symmetry in H. apply fresh_sug_correct in H. rewrite H in ANCHOR. inv ANCHOR.
      * rewrite ANCHOR in CODEFS. inv CODEFS. eapply Anchor_go_on; eauto. simpl. rewrite PTree.gso.
        rewrite PTree.gss. eauto. unfold not; intros H.
        symmetry in H. apply fresh_sug_correct in H. rewrite H in ANCHOR. inv ANCHOR.
      
    + apply safe_step_ir in SAFE as STEP. destruct STEP as [t [s'' STEP]].
      right. rewrite OPT in OPTV. inv OPTV.
      apply safe_code in SAFE. destruct SAFE as [i CODESRC].
      eapply preservation_code in HEQ as SAME_CODE; eauto. 
      inv STEP.
      * exists t. unfold ir_step in STEP0. repeat sdo_ok. unfold ir_int_step in HDO.
        rewrite CODESRC in HDO. repeat sdo_ok. inv HDO1.
        { destruct i0; repeat sdo_ok.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite SAME_CODE. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite SAME_CODE. simpl.
            unfold fret'. rewrite HDO. simpl. eauto.
          - poseq_destr f0 fid.
            + simpl in HDO. repeat sdo_ok.
              unfold n_push_interpreter_stackframe in HDO0. simpl in HDO0. destruct top; inv HDO0.
              econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite SAME_CODE. simpl.
              unfold sbind. unfold n_push_interpreter_stackframe. simpl. rewrite HDO. simpl. eauto.
            + simpl in HDO. repeat sdo_ok.
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

      * exists E0. rewrite CODESRC in ANCHOR. inv ANCHOR.
        exists (Halt_IR (vins, next, rm), mkmut stk' top heap). eapply Anchor_go_on; eauto.
      * exists E0. rewrite CODESRC in ANCHOR. inv ANCHOR.
        exists (Halt_IR (vins, next, rm), mkmut stk' top heap). eapply Anchor_go_on; eauto.
                  
  - apply safe_step in SAFE. destruct SAFE as [[t [s'' STEP]]| [r FINAL]].
    2: { inv FINAL. left. exists r. constructor. }
    right. inv STEP.
    + destruct ms1. eapply addstk_same in STEP0 as [s [APP SAME]]; eauto.
      2: apply addstk_irstep.
      exists t. econstructor. eapply IR_step. simpl. eauto.
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
      poseq_destr fid fid0.
      * econstructor. econstructor.
        eapply Call_IR with (func:=set_version_function vins func) (ver:=vins); eauto.
        unfold set_version, set_version_funlist. simpl. rewrite GETF. rewrite PTree.gss. auto.
      * econstructor. econstructor.
        eapply Call_IR; eauto. unfold set_version, set_version_funlist. simpl.
        unfold find_function_ir in FINDOPT. rewrite FINDOPT. rewrite PTree.gso; auto.
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
      poseq_destr fid ftgt.
      * econstructor. econstructor. eapply Deopt; eauto.
        unfold set_version, set_version_funlist. simpl. unfold find_function_ir in FINDOPT. rewrite FINDOPT.
        rewrite PTree.gss; auto.
      * econstructor. econstructor. eapply Deopt; eauto.
        unfold set_version, set_version_funlist. simpl. unfold find_function_ir in FINDOPT. rewrite FINDOPT.
        rewrite PTree.gso; eauto.
    + destruct ms1. eapply addstk_same in PRIM_CALL as [s [APP SAME]].
      2: { unfold ASMinterpreter.prim_sem_dec. repeat addstk_auto. }
      econstructor. econstructor. eapply RTL_prim; eauto.
    + econstructor. econstructor. eapply RTL_end; eauto.
    + econstructor. econstructor. eapply RTL_block_end; eauto.
    + econstructor. econstructor. eapply Anchor_go_on; eauto.
    + econstructor. econstructor. eapply Anchor_deopt; eauto.
Qed.

(** * The Internal Backward Simulation  *)
Theorem assume_insertion_correct:
  forall p nc fid guard fs_lbl newp,
    insert_assume fid guard fs_lbl p = OK newp ->
    backward_internal_simulation p newp None None nc nc AnchorOn AnchorOn.
Proof.
  intros p nc fid guard fs_lbl newp OPT. unfold insert_assume in OPT. repeat do_ok.
  rename HDO1 into FINDOPTF. rename v into vins. set (vsrc:=current_version f).
  assert (OPTV: insert_assume_version vsrc fid guard fs_lbl (fn_params f) = OK vins) by auto.
  unfold insert_assume_version in HDO0. repeat do_ok. inv HDO. destruct u.
  set (c:=ver_code vsrc).  rename HDO0 into VALIDATE. fold vsrc in VALIDATE.
  fold vsrc in H1. fold c in H1. destruct (c!fs_lbl) eqn:CODE_FS; inv H1.
  destruct i; inv H0. repeat do_ok. rename d into tgt. rename v into vm_fs. rename l into next_fs.
  rename HDO0 into CODE_NEXT.
  set (vins := {| ver_code := (c # fs_lbl <- (Anchor tgt vm_fs (fresh_sug (Pos.succ fs_lbl) c))) #  (fresh_sug (Pos.succ fs_lbl) c) <- (Assume guard tgt vm_fs next_fs); ver_entry := ver_entry vsrc |}). fold vins in OPTV.
  apply Backward_internal_simulation with (bsim_order:=as_order) (bsim_match_states:=match_states p vsrc fid guard fs_lbl (fn_params f)).
  - apply wfounded.
  - unfold call_refl. unfold p_reflexive. intros s H. inv H. exists Zero. destruct ms. apply refl_match.
    apply match_stack_same.

  - intros. inv H1. inv H. econstructor. split. apply star_refl. constructor.

  - intros. eapply progress_preserved; eauto. 

  - intros s2 t s2' STEP i0 s1 MATCH SAFE.
    inv MATCH.

    + rewrite OPT in OPTV. inv OPTV. (* assume_match *)
      inv STEP.
      2: { rewrite ANCHOR in AS_OPT. inv AS_OPT. }
      2: { rewrite ANCHOR in AS_OPT. inv AS_OPT. }
      simpl in STEP0. unfold ir_step, ir_int_step in STEP0.
      rewrite AS_OPT in STEP0. simpl in STEP0. repeat sdo_ok.
      destruct (bool_of_int i0) eqn:GUARD. inv HDO.
      * exists One. econstructor. split.    (* Assume holds *)
        ** left. apply plus_one. eapply Anchor_go_on; eauto.
        ** simpl. eapply opt_match; eauto.
           eapply def_analyze_correct; eauto. simpl; auto. unfold def_dr_transf. rewrite FS_SRC. auto.
      * repeat sdo_ok. exists Zero. econstructor. split. (* Assume fails *)
        ** left. apply plus_one. eapply Anchor_deopt; eauto.
        ** simpl. eapply refl_match. auto.
        
    + rewrite OPT in OPTV. inv OPTV. (* opt_match *)
      poseq_destr lbl fs_lbl.
      (* We are at the anchor used for insertion*)
      { assert (OPT': insert_assume_version vsrc fid guard fs_lbl (fn_params f)= OK vins) by auto.
        apply anchor_changed in OPT as [[fa la][vm [fresh [next [CODE_INS_FS [CODE_SRC_FS CODE_INS_AS]]]]]].
        unfold c in CODE_FS. rewrite CODE_FS in CODE_SRC_FS. inv CODE_SRC_FS. inv STEP.
        - unfold ir_step, ir_int_step in STEP0. rewrite CODE_INS_FS in STEP0. simpl in STEP0. inv STEP0.
        - rewrite ANCHOR in CODE_INS_FS. inv CODE_INS_FS.
        (* The Anchor goes on in OPT. In SRC, it will depend on how the Assume evaluates *)
        (* So we take a stuttering step in the SRC *)
          exists Zero. econstructor. split.
          + right. split. apply star_refl. constructor.
          + eapply assume_match; eauto.
        - rewrite ANCHOR in CODE_INS_FS. inv CODE_INS_FS.
        (* The Anchor deopts in both OPT and SRC *)
          exists Zero. econstructor. split.
          + left. apply plus_one. eapply Anchor_deopt; eauto.
          + eapply refl_match; eauto. }
      
      (* We are not at the Anchor used for insertion *)
      { eapply code_preservation in OPT as SAME_CODE; eauto.
        inv STEP.
        - unfold ir_step, ir_int_step in STEP0. repeat sdo_ok. destruct p0 as [t it].
          destruct i0; repeat sdo_ok.
          + exists One. econstructor. split.
            * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
              rewrite SAME_CODE. simpl. eauto.
            * simpl. eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.
          + exists One. econstructor. split.
            * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
              rewrite SAME_CODE. simpl. rewrite HDO. simpl. eauto.
            * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.

          + simpl in HDO. repeat sdo_ok. unfold n_push_interpreter_stackframe in HDO0.
            simpl in HDO0. destruct top; inv HDO0.
            exists Zero. econstructor. split.
            * left. apply plus_one. eapply IR_step; eauto. unfold ir_step, ir_int_step.
              rewrite SAME_CODE. simpl. unfold sbind. unfold n_push_interpreter_stackframe.
              simpl. rewrite HDO. simpl. eauto.
            * simpl. eapply refl_match; eauto. constructor; auto.
              eapply frame_opt; eauto. intros. def_ok. rewrite SAME_CODE. apply define_insert. auto.
          + destruct (bool_of_int i0) eqn:BOOL; repeat sdo_ok.
            * exists One. econstructor. split.
              ** left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
                 rewrite SAME_CODE. simpl. rewrite HDO2. simpl. rewrite BOOL. simpl. eauto.
              ** eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.
            * exists One. econstructor. split.
              ** left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
                 rewrite SAME_CODE. simpl. rewrite HDO2. simpl. rewrite BOOL. simpl. eauto.
              ** eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.
          + exists Zero. econstructor. split.
            * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
              rewrite SAME_CODE. simpl. rewrite HDO. simpl. eauto.
            * simpl. eapply refl_match; eauto.
          + exists One. econstructor. split.
            * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
              rewrite SAME_CODE. simpl. rewrite HDO. simpl. eauto.
            * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. apply define_insert. auto.
          + unfold n_memset in HDO3. destruct (Integers.Int.lt i0 mem_size) eqn:RANGE; inv HDO3.
            exists One. econstructor. split.
            * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
              rewrite SAME_CODE. simpl. rewrite HDO. simpl. rewrite HDO2. simpl.
              unfold n_memset. rewrite RANGE. unfold sbind. simpl. eauto.
            * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.
          + unfold n_memget in HDO2. destruct (Integers.Int.lt i0 mem_size) eqn:RANGE; inv HDO2.
            destruct (heap ! (intpos.pos_of_int i0)) eqn:HEAP; inv H0.
            exists One. econstructor. split.
            * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
              rewrite SAME_CODE. simpl. rewrite HDO. simpl. 
              unfold n_memget. rewrite RANGE. unfold sbind. simpl. rewrite HEAP. eauto.
            * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. apply define_insert. auto.
          + destruct d. repeat sdo_ok. destruct (bool_of_int i0) eqn:BOOL; repeat sdo_ok.
            * exists One. econstructor. split.
              ** left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
                 rewrite SAME_CODE. simpl. rewrite HDO2. simpl. rewrite BOOL. simpl. eauto.
              ** eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.
            * exists Zero. econstructor. split.
              ** left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
                 rewrite SAME_CODE. simpl. rewrite HDO2. simpl. rewrite BOOL. rewrite HDO. simpl. eauto.
              ** simpl. eapply refl_match; eauto.
          + destruct d. inv HDO.
        
        - exists One. econstructor. split.
          + left. apply plus_one. eapply Anchor_go_on; eauto. rewrite SAME_CODE. apply ANCHOR.
          + eapply opt_match; eauto. clear CODE_NEXT CODE_FS. def_ok. rewrite ANCHOR in SAME_CODE.
            eauto. simpl; auto. rewrite SAME_CODE. rewrite ANCHOR. auto.
        - exists Zero. econstructor. split.
          + left. apply plus_one. eapply Anchor_deopt; eauto. rewrite SAME_CODE. eauto.
          + eapply refl_match. auto.
      }
            

    + { inv STEP.                 (* refl_match *)
        - destruct ms1. eapply addstk_same in STEP0 as [s [APP SAME]]; eauto.
          2: apply addstk_irstep.
          exists Zero. econstructor. split.
          + left. apply plus_one. eapply IR_step; eauto.
          + apply refl_match. subst. apply app_match; auto. apply match_stack_same.
        - destruct ms1. eapply addstk_same in STEP0 as [s [APP SAME]]; eauto.
          2: apply addstk_asmstep.
          exists Zero. econstructor. split.
          + left. apply plus_one. eapply x86_step; eauto.
          + apply refl_match. subst. apply app_match; auto. apply match_stack_same.
        - exists Zero. econstructor. split.
          + left. apply plus_one. eapply rtl_step; eauto.
          + apply refl_match; auto.
        - unfold find_function_ir in FINDOPTF.
          unfold set_version, set_version_funlist in GETF. simpl in GETF. rewrite FINDOPTF in GETF.
          poseq_destr fid fid0.
          +                     (* Calling the optimized function *)
            destruct ms2. eapply addstk_same in CALLEE as [s [APP SAME]].
            2: apply addstk_callee.
            simpl in NOT_COMPILED. unfold n_check_compiled in NOT_COMPILED. simpl in NOT_COMPILED.
            destruct (nc!fid0) eqn:NOT; inv NOT_COMPILED.
            destruct ms3. eapply addstk_same in ARGS as [s2 [APP2 SAME2]].
            rewrite PTree.gss in GETF. inv GETF.
            2: apply addstk_get_args.
            exists One. econstructor. split.
            * left. apply plus_one. eapply Call_IR; eauto; simpl.
              ** unfold n_check_compiled. simpl. rewrite NOT. eauto.
            * unfold validator in VALIDATE. fold c in VALIDATE. rewrite CODE_FS in VALIDATE. repeat do_ok.
              simpl.  rewrite current_version_set_version. eapply opt_match; eauto.
              ** apply app_match. apply app_match; auto. apply match_stack_same. apply match_stack_same.
              ** eapply def_analyze_init; eauto.
          +   (* calling another function *)
            rewrite PTree.gso in GETF; auto.
            destruct ms2. eapply addstk_same in CALLEE as [s [APP SAME]].
            2: apply addstk_callee.
            simpl in NOT_COMPILED. unfold n_check_compiled in NOT_COMPILED. simpl in NOT_COMPILED.
            destruct (nc!fid0) eqn:NOT; inv NOT_COMPILED.
            destruct ms3. eapply addstk_same in ARGS as [s2 [APP2 SAME2]].
            2: apply addstk_get_args.
            exists Zero. econstructor. split.
            * left. apply plus_one. eapply Call_IR; eauto; simpl.
              ** unfold n_check_compiled. simpl. rewrite NOT. eauto.
            * eapply refl_match. subst. apply match_app. apply match_app. auto.
        - destruct loc.
          + simpl in CALLEE. repeat sdo_ok. unfold n_load in HDO. simpl in HDO. destruct top; inv HDO.
            simpl in COMPILED. unfold n_check_compiled in COMPILED. simpl in COMPILED.
            destruct (nc ! (intpos.pos_of_int i0)) eqn:COMP; inv COMPILED.
            destruct ms3. eapply addstk_same in ARGS as [s [APP SAME]]; eauto.
            2: apply addstk_set_args.
            simpl in LOAD. repeat sdo_ok. unfold n_load_prog_code in HDO. simpl in HDO.
            rewrite COMP in HDO. inv HDO.
            exists Zero. econstructor. split.
            * left. apply plus_one. eapply Call_x86; eauto; simpl.
              ** unfold n_load, sbind. simpl. eauto.
              ** unfold n_check_compiled. simpl. rewrite COMP. eauto.
              ** unfold n_load_prog_code, sbind. simpl. rewrite COMP. eauto.
            * eapply refl_match. apply app_match; auto. apply match_stack_same.
          + simpl in CALLEE. inv CALLEE.
            simpl in COMPILED. unfold n_check_compiled in COMPILED. simpl in COMPILED.
            destruct (nc ! fid0) eqn:COMP; inv COMPILED.
            destruct ms3. eapply addstk_same in ARGS as [s [APP SAME]]; eauto.
            2: apply addstk_set_args.
            simpl in LOAD. repeat sdo_ok. unfold n_load_prog_code in HDO. simpl in HDO.
            rewrite COMP in HDO. inv HDO.
            exists Zero. econstructor. split.
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
            * exists Zero. econstructor. split. (* Returning to the same function *)
              ** left. apply plus_one. eapply Return_IR; eauto.
                 *** simpl. unfold n_load, sbind. simpl. eauto.
                 *** simpl. unfold n_open_stackframe. simpl. eauto.
              ** eapply refl_match; eauto.
            * exists One. econstructor. split. (* Returning to the optimized IR *)
              ** left. apply plus_one. eapply Return_IR; eauto.
                 *** simpl. unfold n_load, sbind. simpl. eauto.
                 *** simpl. unfold n_open_stackframe. simpl. eauto.
              ** eapply opt_match; eauto.
          + simpl in RETVAL. inv RETVAL.
            simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
            destruct top; inv OPEN_SF. destruct stk'; inv H0. destruct s; inv H1.
            2: { destruct a,p,p0,p. inv H0. }
            inv MATCHSTACK. inv MSF.
            * exists Zero. econstructor. split. (* Returning to the same function *)
              ** left. apply plus_one. eapply Return_IR; eauto.
                 *** simpl. eauto.
                 *** simpl. unfold n_open_stackframe. simpl. eauto.
              ** eapply refl_match; eauto.
            * exists One. econstructor. split. (* Returning to the optimized IR *)
              ** left. apply plus_one. eapply Return_IR; eauto.
                 *** simpl. eauto.
                 *** simpl. unfold n_open_stackframe. simpl. eauto.
              ** eapply opt_match; eauto.
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
            exists Zero. econstructor. split.
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
            exists Zero. econstructor. split.
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
            exists Zero. econstructor. split.
            * left. apply plus_one. eapply Return_EOE; eauto; simpl.
              ** unfold n_load, sbind. simpl. eauto.
              ** unfold n_open_stackframe. simpl. eauto.
            * eapply refl_match; eauto. constructor.
          + simpl in RETVAL. inv RETVAL.
            simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
            destruct top; inv OPEN_SF. destruct stk'; inv H0.
            2: { destruct s; inv H1. destruct a, p, p0, p. inv H0. }
            inv MATCHSTACK.
            exists Zero. econstructor. split.
            * left. apply plus_one. eapply Return_EOE; eauto; simpl.
              ** unfold n_load, sbind. simpl. eauto.
              ** unfold n_open_stackframe. simpl. eauto.
            * eapply refl_match; eauto. constructor.
        - destruct ms1, ms2. eapply addstk_same in TARGET as [s [APP SAME]]; eauto.
          2: apply addstk_target.
          eapply addstk_same in BUILD_RM as [s2 [APP2 SAME2]]; eauto.
          2: apply addstk_build.
          unfold find_function_ir in FINDOPTF.
          unfold set_version, set_version_funlist in FINDF. simpl in FINDF.
          rewrite FINDOPTF in FINDF.
          poseq_destr ftgt fid.
          + exists Zero. econstructor. split.
            * left. apply plus_one. eapply Deopt; eauto; simpl.
            * rewrite PTree.gss in FINDF. inv FINDF. rewrite base_version_set_version.
              eapply refl_match; eauto. apply match_app. apply match_app. auto.
          + exists Zero. econstructor. split.
            * left. apply plus_one. eapply Deopt; eauto; simpl.
              ** rewrite PTree.gso in FINDF; eauto.
            * eapply refl_match; eauto. subst. apply match_app. apply match_app. auto.
        - destruct ms1. eapply addstk_same in PRIM_CALL as [s [APP SAME]].
          2: { unfold ASMinterpreter.prim_sem_dec. repeat addstk_auto. }
          exists Zero. econstructor. split.
          + left. apply plus_one. eapply RTL_prim; eauto.
          + eapply refl_match. subst. apply match_app. auto.
        - exists Zero. econstructor. split.
          + left. apply plus_one. eapply RTL_end; eauto.
          + eapply refl_match. auto.
        - exists Zero. econstructor. split.
          + left. apply plus_one. eapply RTL_block_end; eauto.
          + eapply refl_match. auto.
        - exists Zero. econstructor. split.
          + left. apply plus_one. eapply Anchor_go_on; eauto.
          + eapply refl_match. auto.
        - exists Zero. econstructor. split.
          + left. apply plus_one. eapply Anchor_deopt; eauto.
          + eapply refl_match. auto.
      }
Qed.

