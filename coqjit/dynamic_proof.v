(* Proving that adding optimizations dynamically to the execution is correct *)
Require Import common.
Require Import mixed_sem.
Require Import IR.
Require Import optimizer.
Require Import optimizer_proof.
Require Import input_proof.
Require Import Events.
Require Import customSmallstep.
Require Import monad_impl.
Require Import internal_simulations.
Require Import sem_properties.

(* The number of optimizations left *)
Definition optim_index: Type := nat.
Definition optim_order: optim_index -> optim_index -> Prop := lt.

Lemma optim_order_wf: well_founded optim_order.
Proof.
  unfold optim_order. apply Nat.lt_wf_0.
Qed.

(* The decreasing order, during the execution, given by the current backward simulation *)
Record exec_index : Type := mkindex {
  index_type: Type; 
  matchs: index_type -> mixed_state -> mixed_state -> Prop;
  index: index_type;
  order: index_type -> index_type -> Prop;
  wf: well_founded order;
                              }.

(* Update the exec_index with a new index *)
Definition change_index (e:exec_index) (i:(index_type e)) : exec_index :=
  mkindex (index_type e) (matchs e) i (order e) (wf e).

(* This order decreases only if the order and relation stay the same *)
Inductive exec_order: exec_index -> exec_index -> Prop :=
| exec_ord :
    forall e i,
      (order e) i (index e) ->
      exec_order (change_index e i) e.

Lemma acc_exec_order:
  forall idxt (ord:idxt -> idxt -> Prop) i
    (WF: well_founded ord),
    Acc ord i -> forall ms, Acc exec_order (mkindex idxt ms i ord WF).
Proof.
  induction 1. intros.
  apply Acc_intro. intros. inv H1. simpl in H2.
  apply H0. auto.
Qed.

Lemma exec_order_wf: well_founded exec_order.
Proof.
  unfold well_founded. intros. destruct a.
  apply acc_exec_order. unfold well_founded in wf0. apply wf0. 
Qed.

(* The order that decreases each time the dynamic semantics takes a stuttering step *)
Definition dynamic_index: Type := optim_index * exec_index.

(* Helper functions *)
Definition joptim: dynamic_index -> optim_index := fst.
Definition jexec: dynamic_index -> exec_index := snd.
Definition jtype (ji:dynamic_index) := index_type (jexec ji).
Definition jrel (ji:dynamic_index) := matchs (jexec ji).
Definition jindex (ji:dynamic_index) := index (jexec ji).
Definition jorder (ji:dynamic_index) := order (jexec ji).

(* Update the index, but not the order or relation *)
Definition jupdate (ji:dynamic_index) (i:jtype ji) : dynamic_index :=
  (joptim ji, change_index (jexec ji) i).

Lemma optim_update:
  forall ji i,
    joptim ji = joptim (jupdate ji i).
Proof. intros. unfold jupdate. simpl. auto. Qed.
           
Definition dynamic_order: dynamic_index -> dynamic_index -> Prop :=
  lex_ord lt exec_order.

Definition optim_decreases:= lex_ord_left.
Definition exec_decreases:= lex_ord_right.

(* The order that decreases on stuttering steps is well-founded *)
Theorem dynamic_order_wf: well_founded dynamic_order.
Proof.
  unfold dynamic_order. apply wf_lex_ord. apply lt_wf. apply exec_order_wf.
Qed.

Ltac destruct_dynamic_index :=
  let optim_idx := fresh "optim_idx" in
  let exec_idx := fresh "exec_idx" in
  match goal with
  | [ji: dynamic_index |- _ ] => destruct ji as [optim_idx exec_idx]
  end.

Ltac destruct_exec_index :=
  let idxt := fresh "index_type" in
  let matchs := fresh "match_states" in
  let idx := fresh "index" in
  let ord := fresh "order" in
  let refl := fresh "REFL" in
  let wf := fresh "WF" in
  match goal with
  | [e: exec_index |- _ ] => destruct e as [idxt matchs idx ord refl wf]
  end.


(* Relating semantic states of the original program and dynamic states *)
Inductive match_states: program -> dynamic_index -> mixed_state -> dynamic_state -> Prop :=
| dynamic_match: forall p nc' ji sync sync' ms ms'
               (INTERNAL_SIM: backward_internal_simulation' p p None None nocode nc' (jorder ji) (jrel ji))
               (INTERNAL_MATCH: (jrel ji) (jindex ji) (sync, ms) (sync', ms')),
    match_states p ji
                 (sync, ms)
                 (Dynamic p None sync' (ms', nc') (joptim ji)).


Theorem dynamic_optim_correct:
  forall p,
    backward_simulation (mixed_sem p None nocode)
                        (dynamic_sem p None).
Proof.
  intros p.
  eapply Backward_simulation with (bsim_match_states:=match_states p) (bsim_order:=dynamic_order).
  - eapply dynamic_order_wf.
  - intros s1 H. exists (Dynamic p None (S_Call (ir_call (prog_main p) nil)) init_n_state 0). constructor.
  - intros s1 s2 H H0. inv H. inv H0. exists (nb_opt, mkindex refl_type refl_match_states tt refl_order wf_refl).
    exists (S_Call (ir_call (prog_main p) nil), init_mutables). split; constructor. auto.
    apply backward_refl. unfold jrel, jindex. simpl. constructor.
  - intros i s1 s2 r MATCH SAFE FINAL. inv FINAL. inv MATCH.
    eapply (match_final_states INTERNAL_SIM) in INTERNAL_MATCH; eauto. constructor.
  - intros i s1 s2 MATCH SAFE. inv MATCH. (* progress *)
    apply (progress INTERNAL_SIM) in INTERNAL_MATCH as [[retval FINAL]|[t [s2' STEP]]] ; auto.
    + left. simpl. exists retval. inv FINAL. constructor.
    + right. simpl. simpl in STEP. exists t. destruct s2' as [sync'' ms''].
      exists (Dynamic p None sync'' (ms'', nc') (joptim i)). apply exe_step. auto. (* simulation diagram *)
  - intros s2 t s2' DYN_STEP ji s1 MATCH SAFE. inv MATCH. simpl in DYN_STEP. inv DYN_STEP.
    + eapply (simulation INTERNAL_SIM) in MIXED; eauto. (* execution step *)
      destruct MIXED as [i' [[sy1 ms1]  [[PLUS | [STAR ORDER]] MATCH]]].
      * exists (jupdate ji i'). exists (sy1, ms1). split; auto. unfold jupdate. erewrite optim_update.
        constructor; auto.
      * exists (jupdate ji i'). exists (sy1, ms1). split; auto. right. split; auto.
        ** destruct ji. eapply exec_decreases. simpl. constructor. auto. 
        ** erewrite optim_update. constructor; auto.
    + apply optimizer_correct in OPT; auto.
      apply backward_eq in OPT. destruct OPT as [optidx [optorder [optms OPT_SIM]]].
      specialize (match_states_refl OPT_SIM). unfold call_refl, p_reflexive. intros REFL.
      specialize (REFL (S_Call loc, ms')). exploit REFL. constructor.
      intros [i2 OPT_MATCH].
      (* composing the two backward simulations *)
      eapply compose_backward_simulation' in OPT_SIM as NEW_SIM; eauto.
      2: { apply single_mixed. } 
      (* Constructing the new index, with a new relation and new order *)
      set (neword:= lex_ord (Relation_Operators.clos_trans (index_type (jexec ji)) (jorder ji)) optorder).
      set (newms := bb_ms p None nc' (jrel ji) optms).
      assert (NEWWF: well_founded neword) by apply (order_wf NEW_SIM).
      fold neword in NEW_SIM. fold newms in NEW_SIM.
      (* constructing the new match *)
      exists (Nat.pred (joptim ji), mkindex (index_type (jexec ji) * optidx) newms (jindex ji, i2) neword NEWWF).
      exists (sync,ms). split. (* no execution progress has been made this step *)
      * right. split. apply star_refl. destruct ji. unfold jindex. simpl. apply optim_decreases.
        unfold joptim in H5. simpl in H5. rewrite <- H5. simpl. lia.
      * replace nb_opt with (Nat.pred (joptim ji)) by lia. econstructor; auto.
        unfold jrel, jindex, jexec, newms. simpl. eapply bb_match_at'; eauto.
Qed.

Corollary dynamic_input_correct:
  forall p,
    backward_simulation (input_sem p)
                        (dynamic_sem p None).
Proof.
  intros p. eapply customSmallstep.compose_backward_simulation.
  - apply single_dynamic.
  - eapply input_mixed. 
  - apply dynamic_optim_correct. 
Qed.

    
