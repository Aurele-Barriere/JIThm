(* Some semantics properties *)

Require Import Coqlib.
Require Import mixed_sem.
Require Import IR.
Require Import RTL.
Require Import RTLblock.
Require Import Events.
Require Import ASMinterpreter.
Require Import IRinterpreter.
Require Import monad.
Require Import monad_impl.
Require Import common.
Require Import Errors.
Require Import primitives.
Require Import customSmallstep.
Require Import internal_simulations.
Require Import intpos.

(* Single events of all the semantics involved *)
Theorem single_input:
  forall p,
    single_events (input_sem p).
Proof.
  unfold single_events. intros p s t s' STEP.
  inv STEP; simpl; auto.
Qed.

Lemma single_rtl:
  forall ge s1 t s2
    (STEP: RTL.step ge s1 t s2),
    (Datatypes.length t <= 1)%nat.
Proof.
  intros ge s1 t s2 STEP. inv STEP; simpl; auto;
                            eapply external_call_trace_length; eauto.
Qed.

Lemma single_prim_sem:
  forall name sg args t retval mstate (impl: @monad_impl mstate) ms0 ms1
    (PRIM: exec (prim_sem_dec name sg args) impl ms0 = SOK (t, retval) ms1),
    (Datatypes.length t <= 1)%nat.
Proof.
  intros name sg args t retval mstate impl ms0 ms1 EXT.
  unfold prim_sem_dec in EXT. 
  destruct (name =? primitives.EF_name EF_save)%string; repeat sdo_ok; auto.
  destruct (name =? primitives.EF_name EF_load)%string; repeat sdo_ok; auto.
  destruct (name =? primitives.EF_name EF_memset)%string; repeat sdo_ok; auto.
  destruct (name =? primitives.EF_name EF_memget)%string; repeat sdo_ok; auto.
  destruct (name =? primitives.EF_name EF_close)%string; repeat sdo_ok; auto.
  destruct (name =? primitives.EF_name EF_print)%string; repeat sdo_ok; auto.
  inv EXT.
Qed.
    


Lemma single_asm_int:
  forall ge s1 s2 t mstate (impl: @monad_impl mstate) ms1 ms2
    (STEP: exec (asm_int_step ge s1) impl ms1 = SOK (t, s2) ms2),
    (Datatypes.length t <= 1)%nat.
Proof.
  intros ge s1 s2 t mstate impl ms1 ms2 STEP. unfold asm_int_step in STEP. repeat sdo_ok.
  destruct p as [tr r]. simpl in STEP. unfold asm_step in HDO. 
  destruct (is_final s1) eqn:FINAL.
  { unfold is_final in FINAL. destruct s1; inv FINAL.
    destruct r; inv STEP; repeat sdo_ok. simpl. lia. }
  destruct s1 as [rs mem].
  destruct (rs Asm.PC) eqn:PC; inv HDO.
  destruct (Globalenvs.Genv.find_funct_ptr ge b) eqn:FINDF; inv H0.
  destruct f eqn:F; inv H1.
  - destruct (Asm.find_instr (Integers.Ptrofs.unsigned i) (Asm.fn_code f0)); inv H0.
    destruct (Asm.exec_instr ge f0 i0 rs mem); inv H1.
    destruct i0; inv H0; inv STEP; auto. destruct i0; inv H0; auto.
  - destruct e; inv H0.
    destruct (Integers.Ptrofs.eq i Integers.Ptrofs.zero); inv H1. repeat sdo_ok.
    unfold ASMinterpreter.ext_prim_sem in HDO; inv HDO. repeat sdo_ok. simpl.    
    destruct p0. simpl. eapply single_prim_sem; eauto.
Qed.

Lemma single_asm:
  forall ge s1 s2 t mstate (impl: @monad_impl mstate) ms1 ms2
    (STEP: exec (asm_step ge s1) impl ms1 = SOK (t, s2) ms2),
    (Datatypes.length t <= 1)%nat.
Proof.
  intros ge s1 s2 t mstate impl ms1 ms2 STEP. unfold asm_step in STEP.
  destruct (is_final s1) eqn:FINAL.
  { unfold is_final in FINAL. destruct s1; inv FINAL.
    destruct r; inv STEP; repeat sdo_ok; simpl; lia. }
  destruct s1; inv STEP. destruct (r Asm.PC) eqn:PC; inv H0.
  destruct (Globalenvs.Genv.find_funct_ptr ge b) eqn:FINDF; inv H1.
  destruct f eqn:F; inv H0.
  - destruct (Asm.find_instr (Integers.Ptrofs.unsigned i) (Asm.fn_code f0)); inv H1.
    destruct (Asm.exec_instr ge f0 i0 r m); inv H0.
    destruct i0; inv H1; auto. destruct i0; inv H1; auto.
  - destruct e; inv H1.
    destruct (Integers.Ptrofs.eq i Integers.Ptrofs.zero); inv H0. repeat sdo_ok. 
    unfold ASMinterpreter.ext_prim_sem in HDO; repeat sdo_ok. destruct p0. simpl.
    eapply single_prim_sem; eauto.
Qed.

Lemma single_ir_int:
  forall s1 s2 t mstate (impl: @monad_impl mstate) ms1 ms2
    (STEP: exec (ir_int_step s1) impl ms1 = SOK (t, s2) ms2),
    (Datatypes.length t <= 1)%nat.
Proof.
  intros s1 s2 t mstate impl ms1 ms2 STEP. unfold ir_int_step in STEP.
  destruct s1 as [[v pc] rm]. repeat sdo_ok.
  destruct i; inv STEP; repeat sdo_ok; auto.
  destruct (bool_of_int i); inv H0; auto.
  destruct d. repeat sdo_ok. destruct (bool_of_int i); repeat sdo_ok; auto.
  destruct d. inv H0.
Qed.

Lemma single_ir:
  forall s1 s2 t mstate (impl: @monad_impl mstate) ms1 ms2
    (STEP: exec (ir_step s1) impl ms1 = SOK (t, s2) ms2),
    (Datatypes.length t <= 1)%nat.
Proof.
  intros s1 s2 t mstate impl ms1 ms2 STEP. unfold ir_step, ir_int_step in STEP.
  destruct s1 as [[v pc] rm]. repeat sdo_ok.
  destruct i; inv HDO; repeat sdo_ok; auto.
  destruct (bool_of_int i); inv H0; auto.
  destruct d. repeat sdo_ok. destruct (bool_of_int i); repeat sdo_ok; auto.
  destruct d. inv H0.
Qed.

Lemma single_block_instr:
  forall bi rs state (impl: @monad_impl state) ms t rs' ms'
    (EXEC: exec (exec_block_instr bi rs) impl ms = SOK (t, rs') ms'),
    (Datatypes.length t <= 1)%nat.
Proof.
  intros bi rs state impl ms t rs' ms' EXEC. unfold exec_block_instr in EXEC.
  destruct bi; repeat sdo_ok; auto.
  destruct p. simpl. eapply single_prim_sem; eauto.
Qed.

Lemma single_block:
  forall rtlb bs1 bs2 t mstate (impl: @monad_impl mstate) ms1 ms2
    (STEP: exec (block_step rtlb bs1) impl ms1 = SOK (t, bs2) ms2),
    (Datatypes.length t <= 1)%nat.
Proof.
  intros rtlb bs1 bs2 t mstate impl ms1 ms2 STEP. unfold block_step in STEP.
  destruct bs1; inv STEP.
  { repeat sdo_ok. auto. }
  destruct b as [[blkis exiti] | cond args next [blkis exiti]]; inv H0.
  - destruct blkis.
    + destruct exiti; repeat sdo_ok; auto.
    + repeat sdo_ok. destruct p. simpl. eapply single_block_instr; eauto.
  - repeat sdo_ok. destruct b; repeat sdo_ok; auto.
Qed.


Theorem single_mixed:
  forall p rtl nc,
    single_events (mixed_sem p rtl nc).
Proof.
  unfold single_events. intros p rtl nc s t s' STEP.
  inv STEP; simpl; auto.
  - eapply single_ir; eauto. 
  - eapply single_asm_int; eauto. 
  - inv RTL; simpl; auto; eapply external_call_trace_length; eauto.
  - eapply single_block; eauto.
  - eapply single_prim_sem; eauto.
Qed.


Theorem single_dynamic:
  forall p rtl, single_events (dynamic_sem p rtl).
Proof.
  intros p rtl. unfold single_events. intros s t s' STEP. inv STEP; auto.
  specialize (single_mixed p0 rtl0 nc (sy1,ms1) t (sy2,ms2) MIXED). intros; auto.
Qed.


    
Lemma ir_same:
  forall irs mut ac mut2 ac2 r,
    exec (ir_int_step irs) naive_impl (mut, ac) = SOK r (mut2, ac2) ->
    ac = ac2.
Proof.
  intros irs mut1 ac1 mut2 ac2 r H. destruct r. unfold ir_int_step in H. destruct irs as [[v pc] rm]. repeat sdo_ok.
  destruct i0; simpl in H; repeat sdo_ok; auto. 
  inv HDO. unfold n_push_interpreter_stackframe in H0. simpl in H0. destruct (state_stacktop mut1); inv H0. auto.
  destruct (bool_of_int i0); inv H; auto.
  { unfold n_memset in HDO2. destruct (Integers.Int.lt i0 mem_size); inv HDO2. auto. }
  { unfold n_memget in HDO1. destruct (Integers.Int.lt i0 mem_size); inv HDO1.
    destruct ((state_mem mut1) # (pos_of_int i0)); inv H0. auto. }
  destruct d. repeat sdo_ok. destruct (bool_of_int i0); repeat sdo_ok; auto.
  destruct d. inv H.
Qed.


Lemma ir_done:
  forall irs mut ac mut' cp t,
    exec (ir_int_step irs) naive_impl (mut, ac) = SOK (t, Done cp) (mut', ac) ->
    exec (ir_step irs) naive_impl (mut, ac) = SOK (t, synchro_of cp) (mut', ac).
Proof.
  intros irs mut ac mut' cp t H. unfold ir_step. rewrite exec_bind2. simpl.
  unfold sbind2. unfold sbind. rewrite H. simpl. unfold sret. destruct cp; auto.
Qed.

Lemma ir_halt:
  forall irs mut ac mut' irs' t,
    exec (ir_int_step irs) naive_impl (mut, ac) = SOK (t, Halt irs') (mut', ac) ->
    exec (ir_step irs) naive_impl (mut, ac) = SOK (t, Halt_IR irs') (mut', ac).
Proof.
  intros irs mut ac mut' irs' t H. unfold ir_step. rewrite exec_bind2. simpl.
  unfold sbind2, sbind, sret. rewrite H. simpl. auto.
Qed.

Lemma done_ir:
  forall irs mut ac mut' cp t,
    exec (ir_step irs) naive_impl (mut, ac) = SOK (t, synchro_of cp) (mut', ac) ->
    exec (ir_int_step irs) naive_impl (mut, ac) = SOK (t, Done cp) (mut', ac).
Proof.
  intros irs mut ac mut' cp t H. unfold ir_step in H. rewrite exec_bind2 in H. simpl in H.
  unfold sbind2, sbind in H.
  destruct (exec (ir_int_step irs) naive_impl (mut, ac)) eqn:INT; inv H. destruct p. simpl in H2.
  destruct cp; destruct i; try destruct c; inv H2; simpl; auto; destruct c0; inv H0; auto.
Qed.

Lemma halt_ir:
  forall irs mut ac mut' irs' t,
    exec (ir_step irs) naive_impl (mut, ac) = SOK (t, Halt_IR irs') (mut', ac) ->
    exec (ir_int_step irs) naive_impl (mut, ac) = SOK (t, Halt irs') (mut', ac).
Proof.
  intros irs mut ac mut' irs' t H. unfold ir_step in H. rewrite exec_bind2 in H. simpl in H.
  unfold sbind2, sbind in H.
  destruct (exec (ir_int_step irs) naive_impl (mut, ac)) eqn:INT; inv H. destruct p. simpl in H2.
  destruct i; try destruct c; inv H2. simpl. auto.
Qed.


Lemma asm_same:
  forall ge asms mut ac mut2 ac2 asms' t,
    exec (asm_step ge asms) naive_impl (mut, ac) =
    SOK (t, Halt (asms')) (mut2, ac2) ->
    ac = ac2.
Proof.
  intros ge asms mut1 ac1 mut2 ac2 asms' t H. unfold asm_step in H. destruct asms.
  destruct (is_final (Asm.State r m)) eqn:FINAL. inv H.
  destruct (r Asm.PC) eqn:PC; inv H. destruct (Globalenvs.Genv.find_funct_ptr ge b) eqn:FIND; inv H1.
  destruct f.
  - destruct (Asm.find_instr (Integers.Ptrofs.unsigned i) (Asm.fn_code f)) eqn:INSTR; inv H0.
    destruct (Asm.exec_instr ge f i0 r m) eqn:EXEC.
    2: { destruct i0; inv H1. }
    destruct i0 eqn:I; inv H1; try solve [split; auto].
  - destruct e eqn:EF; inv H0. unfold ASMinterpreter.ext_prim_sem in H1; repeat sdo_ok.
    destruct (Integers.Ptrofs.eq i Integers.Ptrofs.zero); inv H1. repeat sdo_ok. destruct p0.
    unfold prim_sem_dec in HDO1.
    destruct (name =? primitives.EF_name EF_save)%string; repeat sdo_ok.
    { inv HDO2. auto. }
    destruct (name =? primitives.EF_name EF_load)%string; repeat sdo_ok.
    { inv HDO2. unfold n_load, sbind in H0. simpl in H0. destruct (state_stacktop mut1); inv H0. auto. }
    destruct (name =? primitives.EF_name EF_memset)%string; repeat sdo_ok; auto.
    { unfold n_memset in HDO2. destruct (Integers.Int.lt (fst p) mem_size); inv HDO2. auto. }
    destruct (name =? primitives.EF_name EF_memget)%string; repeat sdo_ok; auto.
    { inv HDO2. unfold n_memget, sbind in H0. simpl in H0.
      destruct (Integers.Int.lt i1 mem_size); inv H0. destruct ((state_mem mut1) # (pos_of_int i1)); inv H1.
      auto. }
    destruct (name =? primitives.EF_name EF_close)%string; repeat sdo_ok; auto.
    { destruct p as [[a' b'] c'].
      destruct l; try destruct l; try destruct l; try destruct l; try destruct v, v0, v1; inv HDO1.
      simpl in HDO2. inv HDO2. auto. }
    destruct (name =? primitives.EF_name EF_print)%string; repeat sdo_ok; auto.
    inv HDO1.
Qed.

Lemma asm_same2:
  forall ge asms mut ac mut2 ac2 r t,
    exec (asm_step ge asms) naive_impl (mut, ac) =
    SOK (t, r) (mut2, ac2) ->
    ac = ac2.
Proof.
  intros ge asms mut1 ac1 mut2 ac2 itr t H. unfold asm_step in H. destruct asms.
  destruct (is_final (Asm.State r m)) eqn:FINAL. inv H. auto.
  destruct (r Asm.PC) eqn:PC; inv H. destruct (Globalenvs.Genv.find_funct_ptr ge b) eqn:FIND; inv H1.
  destruct f.
  - destruct (Asm.find_instr (Integers.Ptrofs.unsigned i) (Asm.fn_code f)) eqn:INSTR; inv H0.
    destruct (Asm.exec_instr ge f i0 r m) eqn:EXEC.
    2: { destruct i0; inv H1. }
    destruct i0 eqn:I; inv H1; try solve [split; auto].
  - destruct e eqn:EF; inv H0. unfold ASMinterpreter.ext_prim_sem in H1; repeat sdo_ok.
    destruct (Integers.Ptrofs.eq i Integers.Ptrofs.zero); inv H1. repeat sdo_ok.
    destruct p0. unfold prim_sem_dec in HDO1.
    destruct (name =? primitives.EF_name EF_save)%string; repeat sdo_ok; auto.
    { inv HDO2. auto. }
    destruct (name =? primitives.EF_name EF_load)%string; repeat sdo_ok; auto.
    { unfold n_load in HDO2. simpl in HDO2. destruct (state_stacktop mut1); inv HDO2. auto. }
    destruct (name =? primitives.EF_name EF_memset)%string; repeat sdo_ok; auto.
    { unfold n_memset in HDO2. destruct (Integers.Int.lt (fst p) mem_size); inv HDO2. auto. }
    destruct (name =? primitives.EF_name EF_memget)%string; repeat sdo_ok; auto.
    { unfold n_memget in HDO2. simpl in HDO2.
      destruct (Integers.Int.lt i1 mem_size); inv HDO2.
      destruct ((state_mem mut1) # (pos_of_int i1)); inv H0. auto. }
    destruct (name =? primitives.EF_name EF_close)%string; repeat sdo_ok; auto.
    { destruct p as [[a' b'] c'].
      destruct l; try destruct l; try destruct l; try destruct l; try destruct v, v0, v1; inv HDO1.
      inv HDO2. auto. }
    destruct (name =? primitives.EF_name EF_print)%string; repeat sdo_ok; auto.
    inv HDO1.
Qed.
  

Lemma asm_done:
  forall ge asms i cp mut ac mut' t,
    exec (asm_step ge asms) naive_impl (mut, ac) = SOK (t, Done i) (mut', ac) ->
    get_checkpoint i = OK cp ->
    exec (asm_int_step ge asms) naive_impl (mut, ac) = SOK (t, synchro_of cp) (mut', ac).
Proof.
  intros ge asms i cp mut ac mut' t H CHK.
  unfold asm_int_step. rewrite exec_bind2. 
  unfold sbind2, sbind. rewrite H. simpl. rewrite CHK. simpl. auto.
Qed.

Lemma asm_halt:
  forall ge asms asms' mut ac mut' t,
    exec (asm_step ge asms) naive_impl (mut, ac) = SOK (t, Halt (asms')) (mut', ac) ->
    exec (asm_int_step ge asms) naive_impl (mut, ac) = SOK (t, Halt_ASM ge asms') (mut', ac).
Proof.
  intros ge asms asms' mut ac mut' t H. unfold asm_int_step. rewrite exec_bind2.
  simpl. simpl in H. unfold sbind2, sbind. rewrite H. auto.
Qed.

(** * Receptiveness  *)
Lemma match_traces_exact:
  forall l1 l2,
    match_traces l1 l2 ->
    l1 = l2.
Proof.
  intros l1 l2 H. induction l1; intros; inv H; auto.
Qed.

Theorem mixed_receptive:
  forall p rtl nc,
  receptive (mixed_sem p rtl nc).
Proof.
  intros p rtl nc. constructor.
  2: apply single_mixed.
  intros s t1 s1 t2 H H0. apply match_traces_exact in H0. subst. eauto.
Qed.
  
(** * Determinacy  *)
Definition trace_length (l:trace):= Datatypes.length l.  

Lemma exact_match_traces:
  forall l,
    (trace_length l <= 1)%nat ->
    match_traces l l.
Proof.
  intros l H. destruct l. constructor. destruct l. constructor. simpl in H. lia.
Qed.

Lemma mixed_match:
  forall p rtl nc s t s',
    Step (mixed_sem p rtl nc) s t s' ->
    match_traces t t.
Proof.
  intros p rtl nc s t s' H.
  assert (single_events (mixed_sem p rtl nc)) by apply single_mixed.
  unfold single_events in H0. apply H0 in H. apply exact_match_traces. auto.
Qed.

                   

Theorem rtl_interrupt_determinate:
  forall ge r1 r2 r3 t1 t2,
    ~ interrupt_rtl r1 ->
    RTL.step ge r1 t1 r2 ->
    RTL.step ge r1 t2 r3 ->
    t1 = t2 /\ r2 = r3.
Proof.
  intros ge r1 r2 r3 t1 t2 NO_INT STEP STEP0.
  inv STEP; inv STEP0; repeat match_some; try solve[split;auto].
  - exfalso. apply NO_INT. eapply interrupt_builtin; eauto.
  - rewrite H11 in H0. inv H0. match_some. split; auto.
  - rewrite H6 in H. inv H. split; auto.
  - exfalso. apply NO_INT. apply interrupt_extcall.
Qed.

Ltac match_sok:=
  match goal with
  | [ H: ?e = SOK ?i ?j,
      H1: ?e = SOK ?ii ?jj |- _ ] =>
    try (rewrite H in H1; inv H1)
  end.

Ltac match_ok:=
  match goal with
  | [ H: ?e = OK ?i,
      H1: ?e = OK ?ii |- _ ] =>
    try (rewrite H in H1; inv H1)
  end.

(* RTL is conflicting with native codes if the fid of the RTL function has already been compiled to native *)
Inductive rtl_conflict : option (RTLfun+RTLblockfun) -> asm_codes -> Prop :=
| conflict: forall fid rtlc entry contidx nc af
              (NAT_RTL: nc # fid = Some af),
    rtl_conflict (Some (inr (fid, rtlc, entry, contidx))) nc
| conflict_block: forall fid rtlc entry contidx nc af
                    (NAT_RTL: nc # fid = Some af),
    rtl_conflict (Some (inl (fid, rtlc, entry, contidx))) nc.
    


Theorem mixed_determinate:
  forall p rtl nc,
    ~ rtl_conflict rtl nc ->
    determinate (mixed_sem p rtl nc).
Proof.
  intros p rtl nc NO_CONFLICT. constructor.
  - intros s t1 s1 t2 s2 H H0.
    apply mixed_match in H as MATCH1. apply mixed_match in H0 as MATCH2.
    inv H.
    + inv H0; repeat match_some; repeat match_sok; repeat match_ok; split; auto.
    + inv H0; repeat match_some; repeat match_sok; repeat match_ok; split; auto.
    + inv H0; try solve [exfalso; apply NO_INTERRUPT; constructor].
      * eapply rtl_interrupt_determinate in RTL; eauto.
        destruct RTL. subst. split; auto.
      * inv FINAL. inv RTL.
    + inv H0; repeat match_some; repeat match_sok; repeat match_ok; split; auto; inv BLOCK.
    + inv H0; repeat match_some; repeat match_sok; repeat match_ok; split; intros; auto.
      * rewrite GETF0 in GETF. inv GETF. rewrite INIT0 in INIT. inv INIT. auto. 
      * simpl in NOT_RTL. contradiction.
      * simpl in NOT_RTL. contradiction.
    + inv H0; repeat match_some; repeat match_sok; repeat match_ok. split; auto.
    + inv H0; repeat match_some; repeat match_sok; repeat match_ok; split; auto.
      * simpl in NOT_RTL. contradiction.
      * inv RTL. inv INIT. inv INIT0. unfold ge in *. unfold ge0 in *.
        repeat match_some. split; auto.
      * inv RTL_BLOCK.
    + inv H0; repeat match_some; repeat match_sok; repeat match_ok; split; auto.
      * simpl in NOT_RTL. contradiction.
      * inv RTL.
      * inv RTL_BLOCK. eauto.
    + inv H0; repeat match_some; repeat match_sok; repeat match_ok; split; auto.
    + inv H0; repeat match_some; repeat match_sok; repeat match_ok; split; auto.
      (* using the no conflict hypothesis *)
      * exfalso. apply NO_CONFLICT. simpl in LOAD_CONT. repeat sdo_ok.
        unfold n_load_prog_code in HDO. simpl in HDO. apply int_pos_correct in INTPOS_FID.
        rewrite INTPOS_FID in HDO. destruct (nc # fid) eqn:FID; inv HDO. econstructor. eauto.
      * exfalso. apply NO_CONFLICT. simpl in LOAD_CONT. repeat sdo_ok.
        unfold n_load_prog_code in HDO. simpl in HDO. apply int_pos_correct in INTPOS_FID.
        rewrite INTPOS_FID in HDO. destruct (nc # fid) eqn:FID; inv HDO. econstructor. eauto.      
    + inv H0; repeat match_some; repeat match_sok; repeat match_ok; split; auto.
      * exfalso. apply NO_CONFLICT. (* using the no conflict hypothesis *)
        simpl in LOAD_CONT0. repeat sdo_ok. unfold n_load_prog_code in HDO. simpl in HDO.
        apply int_pos_correct in INTPOS_FID. rewrite INTPOS_FID in HDO. destruct (nc #fid) eqn:FID; inv HDO.
        econstructor. eauto.
      * specialize (int_of_pos_injective fid fid0 fidint0 INTPOS_FID INTPOS_FID0) as SAME_FID. subst.
        repeat match_sok. inv RTL. inv INIT. inv INIT0.
        unfold ge in *. unfold ge0 in *. repeat match_some. repeat match_ok.
        rewrite LOAD_CONT0 in LOAD_CONT. inv LOAD_CONT.
        rewrite H4 in H0. inv H0. rewrite H5 in H1. inv H1. rewrite H3 in H. inv H. auto.
      * inv RTL_BLOCK.
    + inv H0; repeat match_some; repeat match_sok; repeat match_ok; split; auto.
      * exfalso. apply NO_CONFLICT. simpl in LOAD_CONT0. repeat sdo_ok.
        unfold n_load_prog_code in HDO. simpl in HDO. destruct (nc #(pos_of_int caller_fid)) eqn:FID; inv HDO.
        apply int_pos_correct in INTPOS_FID. rewrite INTPOS_FID in FID. econstructor; eauto.
      * inv RTL.
      * inv RTL_BLOCK. rewrite LOAD_CONT0 in LOAD_CONT. inv LOAD_CONT. eauto.
    + inv H0; repeat match_some; repeat match_sok; repeat match_ok; split; auto.
    + inv H0; repeat match_some; repeat match_sok; repeat match_ok; split; auto.
      intros. rewrite FINDF0 in FINDF. inv FINDF. auto.
    + inv H0; repeat match_some; repeat match_sok; repeat match_ok; split; auto.
      * exfalso. apply NO_INTERRUPT. constructor.
      * exfalso. apply NO_INTERRUPT. constructor.
      * inv FINAL.
      * inv FINAL.
    + inv FINAL. inv H0. inv RTL. inv FINAL. rewrite CHK0 in CHK. inv CHK. split; intros; auto.
    + inv H0. inv BLOCK. rewrite CHK0 in CHK. inv CHK. split; intros; auto.
  - apply single_mixed.
  - intros s1 s2 H H0. inv H. inv H0. auto.
  - intros s r H. inv H. unfold nostep. intros t s'. unfold not. intros H. inv H.
  - intros s r1 r2 H H0. inv H. inv H0. auto.
Qed.
(* Proving determinate is useful to get forward to backward *)
(* Note that this is on mixed semantics, where Anchors are blocking *)
