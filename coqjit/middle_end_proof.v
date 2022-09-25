(* Middle-end optimizer Proof *)

Require Import RTL.
Require Import IR.
Require Import monad.
Require Import common.
Require Import Coqlib.
Require Import backend.
Require Import primitives.
Require Import anchor_insertion.
Require Import assume_insertion.
Require Import anchor_removal.
Require Import anchor_insertion_proof.
Require Import assume_insertion_proof.
Require Import anchor_removal_proof.
Require Import IRtoRTLblock_proof.
Require Import IRinterpreter.
Require Import profiler_types.
Require Import Errors.
Require Import monad.
Require Import middle_end.
Require Import mixed_sem.
Require Import customSmallstep.
Require Import sem_properties.
Require Import internal_simulations.
Require Import monad_impl.

(* Optimizations are "safe" if they return the original program instead of a crash *)
(* Here we exploit the safety to show that we always return a simulated program *)
Lemma safe_backward:
  forall (p:program) nc (opt:program -> res program)
    (OPT_OK: forall p', opt p = OK p' -> backward_internal_simulation p p' None None nc nc AnchorOn AnchorOn),
    backward_internal_simulation p (safe_res opt p) None None nc nc AnchorOn AnchorOn.
Proof.
  intros p nc opt OPT_OK.
  unfold safe_res. destruct (opt p) eqn:OPT.
  - specialize (OPT_OK p0 eq_refl). auto.
  - apply backward_internal_reflexivity.
Qed.


Lemma safe_assume:
  forall p nc fid guard anc_lbl,
    backward_internal_simulation p (safe_insert_assume p fid guard anc_lbl) None None nc nc AnchorOn AnchorOn.
Proof.
  intros p nc fid guard anc_lbl. unfold safe_insert_assume. apply safe_backward. intros p' H.
  eapply assume_insertion_correct. eauto.
Qed.

Lemma safe_anchor:
  forall p nc fid lbllist,
    backward_internal_simulation p (safe_insert_anchor p fid lbllist) None None nc nc AnchorOn AnchorOn.
Proof.
  intros p nc fid lbllist. unfold safe_insert_anchor. apply safe_backward. intros p' H.
  eapply anchor_insertion_correct. eauto.
Qed.

Lemma safe_anchor_list:
  forall p nc fsl,
    backward_internal_simulation p (process_anc_list p fsl) None None nc nc AnchorOn AnchorOn.
Proof.
  intros. generalize dependent p. induction fsl; simpl; intros.
  - apply  backward_internal_reflexivity.
  - destruct a. eapply compose_backward_simulation.
    + apply single_mixed.
    + eapply safe_anchor.
    + eapply IHfsl.
Qed.

(* Each optimization pass preserves an internal backward simulation *)
Lemma opt_list_backward:
  forall lopt p nc,
    backward_internal_simulation p (process_optim_list p lopt) None None nc nc AnchorOn AnchorOn.
Proof.
  intros lopt. induction lopt; intros.
  - simpl. apply backward_internal_reflexivity.
  - simpl. destruct a as [fid optw]. destruct optw.
    + eapply compose_backward_simulation. apply single_mixed.
      eapply safe_assume. eapply IHlopt.
Qed.

(* The entire optimization process returns a simulated program *)
Lemma safe_optimize_correct_on:
  forall p nc ps newp,
    safe_middle_end ps p = newp ->
    backward_internal_simulation p newp None None nc nc AnchorOn AnchorOn.
Proof.
  intros p nc ps newp SAFEOPT. unfold safe_middle_end in SAFEOPT. rewrite <- SAFEOPT. apply safe_backward.
  intros p' OPT. clear SAFEOPT.
  unfold middle_end in OPT. repeat do_ok. inv HDO.
  eapply compose_backward_simulation. apply single_mixed.
  2: { eapply lowering_correct; eauto. }
  eapply compose_backward_simulation. apply single_mixed.
  apply safe_anchor_list.
  apply opt_list_backward.
Qed. 


(** * AnchorOn to AnchorOff  *)
(* So far, we have proved the middle-end correct with a simulation on AnchorOn semantics  *)
(* But for the final optimizer theorem, we want a simulation with AnchorOff (needed for the backend proof) *)
(* Here we show that on programs that have no Anchors, the two semantics match exactly *)

Definition synchro_no_anchor (sy:synchro_state) : Prop :=
  match sy with
  | Halt_IR (v, pc, rm) => no_anchor_code (ver_code v)
  | _ => True
  end.


(* The primitives that do not modify the stack invariant (but may modify the stacktop) *)
(* every primitive except Open_SF and push_irsf *)
Inductive stk_prim : forall T:Type, primitive T -> Prop :=
| stk_save: forall i, stk_prim unit (Prim_Save i)
| stk_load: stk_prim Integers.Int.int (Prim_Load)
| stk_memset: forall x y, stk_prim unit (Prim_MemSet x y)
| stk_memget: forall x, stk_prim Integers.Int.int (Prim_MemGet x)
| stk_closesf: forall a b c, stk_prim unit (Prim_CloseSF a b c)
| stk_install: forall f a, stk_prim unit (Prim_Install_Code f a)
| stk_loadc: forall a, stk_prim Asm.program (Prim_Load_Code a)
| stk_check: forall f, stk_prim compiled_status (Prim_Check_Compiled f).
Arguments stk_prim [T] _.

Lemma stk_prim_same:
  forall (T:Type) (p:primitive T) (t:T) (stk1 stk1':stack) (top top':env) (mem mem':memory) (ac ac':asm_codes)
    (ADD: stk_prim p)
    (NO: stk_no_anchor stk1)
    (EXEC: exec_prim p naive_impl (mkmut stk1 top mem, ac) = SOK t (mkmut stk1' top' mem', ac')),
    stk_no_anchor stk1'.
Proof.
  intros T p t stk1 stk1' top top' mem mem' ac ac' ADD NO EXEC.
  destruct p; simpl; inv EXEC; inv ADD; auto.
  - unfold n_load in H0. simpl in H0. destruct top; inv H0. auto.
  - unfold n_memset in H0. simpl in H0. destruct (Integers.Int.lt i mem_size) eqn:SIZE; inv H0. auto.
  - unfold n_memget in H0. simpl in H0. destruct (Integers.Int.lt i mem_size) eqn:SIZE; inv H0. 
    destruct (mem # (intpos.pos_of_int i)) eqn:MEM; inv H1. auto.
  - apply CONS_NO; auto. constructor.
  - unfold n_load_code in H0. destruct a.
    + repeat sdo_ok. unfold n_load_prog_code in HDO. simpl in HDO. destruct (ac#f) eqn:AC; inv HDO. auto.
    + repeat sdo_ok. destruct a. simpl in H0. destruct (t0#l) eqn:CONT; inv H0.
      unfold n_load_prog_code in HDO. simpl in HDO. destruct (ac#f) eqn:AC; inv HDO. auto.
  - unfold n_check_compiled in H0. simpl in H0. destruct (ac#f) eqn:AC; inv H0; auto.
Qed.


(* Typing free monads that do not change our stack invariant *)
Inductive stk_monad {T:Type}: free T -> Prop :=
| a_pure:
    forall (t:T),
      stk_monad (pure t)
| a_error:
    forall (e:errmsg),
      stk_monad (ferror e)
| a_impure:
    forall {R:Type} (p:primitive R) (cont: R -> free T)
      (STKCONT: forall (r:R), stk_monad (cont r))
      (STKPRIM: stk_prim p),
      stk_monad (impure p cont).

Lemma stk_bind:
  forall (A B:Type) (f:free A) (g: A -> free B)
    (STK_A: stk_monad f)
    (STK_B: forall a, stk_monad (g a)),
    stk_monad (fbind f g).
Proof.
  intros A B f. generalize dependent B.
  induction f; intros.
  - simpl. auto.
  - simpl. repeat constructor.
    2: { inv STK_A. apply Classical_Prop.EqdepTheory.inj_pair2 in H2. subst. auto. }
    intros r. apply H; auto. inv STK_A.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H3. subst. auto.
  - simpl. constructor.
Qed.

Lemma stk_try:
  forall (A:Type) (o: option A) (s:string),
    stk_monad (try_option o s).
Proof.
  intros A o s. destruct o; simpl; constructor.
Qed.

Lemma stk_fret':
  forall (A:Type) (r:res A),
    stk_monad (fret' r).
Proof.
  intros A r. unfold fret'. destruct r; constructor.
Qed.

Ltac stk_auto':=
  match goal with
  | [ |- context[stk_monad(fret (?x))]] => constructor
  | [ |- context[stk_monad(ferror (?x))]] => constructor
  | [ |- context[stk_monad(pure (?x))]] => constructor
  | [ |- context[stk_monad(impure ?x ?y)]] => constructor
  | [ |- context[stk_prim ?x]] => constructor
  | [ |- context[stk_monad (fprim ?x)]] => constructor
  | [ |- context[stk_monad(fret' (?x))]] => apply stk_fret'
  | [ |- context[stk_monad(try_option ?x ?y)]] => apply stk_try
  | [ |- context[stk_monad(fbind ?x ?y)]] => apply stk_bind
  | [ |- context[stk_monad(fbind2 ?x ?y)]] => apply stk_bind
  | [ |- context[stk_monad(fbind3 ?x ?y)]] => apply stk_bind
  | [ |- context[stk_monad(fbind4 ?x ?y)]] => apply stk_bind
  | [ |- context[stk_monad(let (x, y) := ?z in _)]] => destruct z
  | [ |- context[stk_monad (match ?x with
                            | _ => _
                            end)]] => destruct x
  end.

Ltac stk_auto := intros; stk_auto'.

Lemma stk_invariant:
  forall (T:Type) (f:free T) (t:T) (stk1 stk1':stack) (top top':env) (mem mem':memory) (ac ac':asm_codes)
    (ADD: stk_monad f)
    (NO: stk_no_anchor stk1)
    (EXEC: exec f naive_impl (mkmut stk1 top mem, ac) = SOK t (mkmut stk1' top' mem', ac')),
    stk_no_anchor stk1'.
Proof.
  intros T f. induction f; intros; inv EXEC; auto.
  repeat sdo_ok.
  assert (ADD_PRIM: stk_prim prim).
  { inv ADD. apply Classical_Prop.EqdepTheory.inj_pair2 in H3. subst. auto. }
  assert (ADD_CONT: forall r, stk_monad (cont r)).
  { inv ADD. apply Classical_Prop.EqdepTheory.inj_pair2 in H4. subst. auto. }
  destruct n. destruct m. exploit stk_prim_same; eauto. 
Qed.


Lemma base_no_spec_no_anchor:
  forall func, 
    no_anchor_code (ver_code (fn_base func)).
Proof.
  intros. unfold no_anchor_code. intros.
  assert (base_version (fn_base func)) by apply (base_no_spec func).
  unfold base_version, base_code in H0. apply H0 in H. apply H. constructor.
Qed.

Lemma step_preserve_no_anchor:
  forall p nc anc sy1 stk1 top1 heap1 t sy2 stk2 top2 heap2,
    no_anchor p ->
    stk_no_anchor stk1 ->
    synchro_no_anchor sy1 ->
    mixed_step anc p None nc (sy1, mkmut stk1 top1 heap1) t (sy2, mkmut stk2 top2 heap2) ->
    stk_no_anchor stk2 /\ synchro_no_anchor sy2.
Proof.
  intros p nc anc sy1 stk1 top1 heap1 t sy2 stk2 top2 heap2 PNO STKNO SYNO STEP.
  inv STEP.
  - unfold ir_step, ir_int_step in STEP0; repeat sdo_ok.
    destruct irs. destruct p1. repeat sdo_ok. destruct i; repeat sdo_ok; simpl in SYNO; simpl; auto.
    + simpl in HDO. repeat sdo_ok. unfold n_push_interpreter_stackframe in HDO0.
      simpl in HDO0. destruct top1; inv HDO0. simpl. split; auto.
      apply CONS_NO; auto. apply IR_NO; auto.
    + destruct (bool_of_int i); repeat sdo_ok; auto.
    + unfold n_memset in HDO3. destruct (Integers.Int.lt i mem_size); inv HDO3.
      split; auto.
    + unfold n_memget in HDO2. destruct (Integers.Int.lt i mem_size); inv HDO2.
      destruct (heap1 ! (intpos.pos_of_int i)); inv H0.
      split; auto.
    + destruct d. repeat sdo_ok. destruct (bool_of_int i); inv HDO.
      * split; auto.
      * repeat sdo_ok. simpl. split; auto.
    + destruct d. inv HDO.
  - unfold ASMinterpreter.asm_int_step in STEP0. repeat sdo_ok.
    destruct p0. simpl in STEP0. destruct n. destruct m.
    apply stk_invariant in HDO; auto.
    2: { unfold ASMinterpreter.asm_step. repeat stk_auto.
         unfold ASMinterpreter.ext_prim_sem. repeat stk_auto.
         unfold ASMinterpreter.prim_sem_dec. repeat stk_auto. }
    destruct i; repeat sdo_ok; auto.
    destruct c; auto.
  - simpl. auto.
  - simpl. split.
    + destruct ms2. apply stk_invariant in CALLEE; auto.
      2: { unfold jit.get_callee. repeat stk_auto. }
      apply stk_invariant in ARGS; auto.
      { unfold jit.get_args. repeat stk_auto.
        unfold jit.pop_args. generalize (nil:list Integers.Int.int).
        intros l a0. generalize dependent l. induction a0; intros; simpl; repeat stk_auto.
        intros. apply IHa0. }
    + unfold current_version. destruct (fn_opt func) eqn:OPT.
      * eapply PNO in OPT; eauto.
      * apply base_no_spec_no_anchor.
  - simpl. split; auto. destruct ms2. apply stk_invariant in CALLEE; auto.
    2: { unfold jit.get_callee. repeat stk_auto. }
    destruct ms3. apply stk_invariant in ARGS; auto.
    2: { clear SYNO ARGS. unfold jit.set_up_args. repeat stk_auto.
         induction l; repeat stk_auto.
         simpl. stk_auto.
         simpl. repeat stk_auto. intros. auto. }
    apply stk_prim_same in LOAD; auto. constructor.
  - inv RTL.
  - inv RTL_BLOCK.
  - simpl. split.
    + destruct ms1. apply stk_invariant in RETVAL; auto.
      2: { unfold jit.get_retval. repeat stk_auto. }
      simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
      destruct state_stacktop; inv OPEN_SF. destruct state_stack; inv H0.
      destruct s; inv H1.
      * inv RETVAL. auto.
      * destruct a, p, p0, p. inv H0.
    + destruct ms1. apply stk_invariant in RETVAL; auto.
      2: { unfold jit.get_retval. repeat stk_auto. }
      simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
      destruct state_stacktop; inv OPEN_SF. destruct state_stack; inv H0.
      destruct s; inv H1.
      * inv RETVAL. inv SF_NO. auto.
      * destruct a, p, p0, p. inv H0.
  - split; auto.
    destruct ms1. apply stk_invariant in RETVAL; auto.
    2: { unfold jit.get_retval. repeat stk_auto. }
    simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
    destruct state_stacktop; inv OPEN_SF. destruct state_stack; inv H0.
    destruct s; inv H1. destruct a, p, p0, p. inv H0. inv RETVAL.
    destruct ms3. eapply stk_prim_same in SET_RETVAL; auto.
    2: { constructor. }
    apply stk_prim_same in LOAD_CONT; auto. constructor.
  - inv RTL.
  - inv RTL_BLOCK.
  - split; auto.
    destruct ms1. apply stk_invariant in RETVAL; auto.
    2: { unfold jit.get_retval. repeat stk_auto. }
    simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
    destruct state_stacktop; inv OPEN_SF. destruct state_stack; inv H0; auto.
    destruct s; inv H1. destruct a, p, p0, p; inv H0.
  - destruct ms1. apply stk_invariant in TARGET; auto.
    2: { unfold jit.get_target. repeat stk_auto. }
    apply stk_invariant in BUILD_RM; auto.
    2: { unfold jit.build_rm. repeat stk_auto.
         generalize (nil:list Integers.Int.int).
         intros l. generalize dependent l. induction a0; intros; simpl; repeat stk_auto.
         intros. apply IHa0. }
    split; auto. simpl. apply base_no_spec_no_anchor.
  - apply stk_invariant in PRIM_CALL; auto. unfold ASMinterpreter.prim_sem_dec. repeat stk_auto.
  - split; auto. destruct cp; auto.
  - split; auto. destruct cp; auto.
  - simpl in SYNO. apply SYNO in ANCHOR. inv ANCHOR.
  - simpl in SYNO. apply SYNO in ANCHOR. inv ANCHOR.
  - simpl in SYNO. apply SYNO in ANCHOR. inv ANCHOR.
  - simpl in SYNO. apply SYNO in ANCHOR. inv ANCHOR.    
Qed.    
  
Lemma same_step:
  forall p nc sy1 stk1 top1 heap1 t sy2 stk2 top2 heap2,
    no_anchor p ->
    synchro_no_anchor sy1 ->
    stk_no_anchor stk1 ->
    mixed_step AnchorOn p None nc (sy1, mkmut stk1 top1 heap1) t (sy2, mkmut stk2 top2 heap2) <->
      mixed_step AnchorOff p None nc (sy1, mkmut stk1 top1 heap1) t (sy2, mkmut stk2 top2 heap2).
Proof.
  intros p nc sy1 stk1 top1 heap1 t sy2 stk2 top2 heap2 PNO SYNO STKNO.
  split; intros STEP.
  - inv STEP; try solve[constructor; auto].
    + eapply Call_IR; eauto.
    + eapply Call_x86; eauto.
    + inv RTL.
    + inv RTL_BLOCK.
    + eapply Return_IR; eauto.
    + eapply Return_x86; eauto.
    + inv RTL.
    + inv RTL_BLOCK.
    + eapply Return_EOE; eauto.
    + eapply Deopt; eauto.
    + eapply RTL_end; eauto.
    + eapply RTL_block_end; eauto.
    + simpl in SYNO. apply SYNO in ANCHOR. inv ANCHOR.
    + simpl in SYNO. apply SYNO in ANCHOR. inv ANCHOR.
  - inv STEP; try solve[constructor; auto].
    + eapply Call_IR; eauto.
    + eapply Call_x86; eauto.
    + inv RTL.
    + inv RTL_BLOCK.
    + eapply Return_IR; eauto.
    + eapply Return_x86; eauto.
    + inv RTL.
    + inv RTL_BLOCK.
    + eapply Return_EOE; eauto.
    + eapply Deopt; eauto.
    + eapply RTL_end; eauto.
    + eapply RTL_block_end; eauto.
Qed.

(* Now the simulations themselves *)
Inductive match_states : unit -> mixed_state -> mixed_state -> Prop :=
| ms_no: forall sy stk top heap
           (SYNO: synchro_no_anchor sy)
           (STKNO: stk_no_anchor stk),
    match_states tt (sy, mkmut stk top heap) (sy, mkmut stk top heap).

Inductive order : unit -> unit -> Prop := .
Lemma wfounded:
  well_founded order.
Proof.
  unfold well_founded. intros. destruct a. constructor. intros. inv H.
Qed.


Lemma anchor_on_off:
  forall p nc,
    no_anchor p ->
    backward_internal_simulation p p None None nc nc AnchorOn AnchorOff.
Proof.
  intros p nc H.
  eapply Backward_internal_simulation with (bsim_match_states:=match_states) (bsim_order:=order).
  - apply wfounded.
  - unfold call_refl, p_reflexive. intros. inv H0. exists tt. destruct ms.
    constructor; simpl; auto. 
  - intros. inv H2. inv H0. econstructor. split. eapply star_refl. constructor.
  - intros. inv H0. apply safe_step in H1 as [[t [s' STEP]]|[r FINAL]].
    + right. exists t. exists s'. destruct s'. destruct m. simpl. rewrite <- same_step; auto.
    + left. exists r. subst. constructor.
  - intros. inv H1. destruct s2'. destruct m. simpl in H0. rewrite <- same_step in H0; auto.
    apply step_preserve_no_anchor in H0 as H3; auto. destruct H3.
    exists tt. econstructor. split. left. apply plus_one. simpl. eauto.
    constructor; auto.
Qed.


Lemma anchor_off_on:
  forall p nc,
    no_anchor p ->
    backward_internal_simulation p p None None nc nc AnchorOff AnchorOn.
Proof.
  intros p nc H.
  eapply Backward_internal_simulation with (bsim_match_states:=match_states) (bsim_order:=order).
  - apply wfounded.
  - unfold call_refl, p_reflexive. intros. inv H0. exists tt. destruct ms.
    constructor; simpl; auto. 
  - intros. inv H2. inv H0. econstructor. split. eapply star_refl. constructor.
  - intros. inv H0. apply safe_step in H1 as [[t [s' STEP]]|[r FINAL]].
    + right. exists t. exists s'. destruct s'. destruct m. simpl. rewrite same_step; auto.
    + left. exists r. subst. constructor.
  - intros. inv H1. destruct s2'. destruct m. simpl in H0. rewrite same_step in H0; auto.
    apply step_preserve_no_anchor in H0 as H3; auto. destruct H3.
    exists tt. econstructor. split. left. apply plus_one. simpl. eauto.
    constructor; auto.
Qed.

(** * Final Specification of the Middle-End  *)
(* The entire optimization process returns a simulated program *)
Lemma middle_end_no_anchor:
  forall p ps newp,
    no_anchor p ->
    safe_middle_end ps p = newp ->
    no_anchor newp.
Proof.
  intros. unfold safe_middle_end, safe_res in H0.
  destruct (middle_end ps p) eqn:MID; inv H0; auto.
  unfold middle_end in MID. repeat do_ok.
  eapply lowering_no_anchor; eauto.
Qed.

Theorem safe_optimize_correct:
  forall p nc ps newp,
    no_anchor p ->
    safe_middle_end ps p = newp ->
    backward_internal_simulation p newp None None nc nc AnchorOff AnchorOff.
Proof.
  intros p nc ps newp NO SAFEOPT.
  eapply compose_backward_simulation. apply single_mixed.
  2: { apply anchor_on_off. eapply middle_end_no_anchor; eauto. }
  eapply compose_backward_simulation. apply single_mixed.
  2: { eapply safe_optimize_correct_on; eauto. }
  apply anchor_off_on. auto.
Qed. 
