(* Modified Smallstep library to verify dynamic optimizations *)

Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Smallstep.
Require Import IR.
Require Import RTLblock.
Require Import mixed_sem.
Require Import monad_impl.
Require Import customSmallstep.

Set Implicit Arguments.

(** * Reflexivity of our match_states relations  *)
Definition reflexive {index:Type} {state:Type} (match_states: index -> state -> state -> Prop): Prop :=
  forall s, exists i, match_states i s s.

(** * Reflexivity on Call states  *)
Definition p_reflexive {index:Type} (P:mixed_state -> Prop) (match_states: index -> mixed_state -> mixed_state -> Prop):Prop :=
  forall s, P s -> exists i, match_states i s s.

Inductive refl_point: mixed_state -> Prop :=
| refl_call:
  forall loc ms
    (NO_ANCHOR: stk_no_anchor (state_stack ms)),
      refl_point (S_Call loc, ms).

Definition call_refl {index:Type} (match_states: index -> mixed_state -> mixed_state -> Prop) : Prop :=
  p_reflexive refl_point match_states.

(** * Forward Internal Simulations between two transition semantics. *)
(** The general form of a forward internal simulation. *)
Record forward_internal_simulation (p1 p2:program) (rtl1 rtl2: option (RTLfun+RTLblockfun)) (nc1 nc2: asm_codes) (anc1 anc2: anchor_status): Type :=
  Forward_internal_simulation {
    fsim_index: Type;
    fsim_order: fsim_index -> fsim_index -> Prop;
    fsim_order_wf: well_founded fsim_order;
    fsim_match_states :> fsim_index -> mixed_state -> mixed_state -> Prop;
    fsim_match_states_refl: call_refl fsim_match_states;
    fsim_match_final_states:
      forall i s1 s2 r,
      fsim_match_states i s1 s2 -> final_mixed_state p1 s1 r -> final_mixed_state p2 s2 r;
    fsim_simulation:
      forall s1 t s1', Step (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' ->
      forall i s2, fsim_match_states i s1 s2 ->
      exists i', exists s2',
         (SPlus (mixed_sem p2 rtl2 nc2 anc2) s2 t s2' \/ (Star (mixed_sem p2 rtl2 nc2 anc2) s2 t s2' /\ fsim_order i' i))
      /\ fsim_match_states i' s1' s2';
  }.

(* Implicit Arguments forward_simulation []. *)
Arguments forward_internal_simulation: clear implicits.

(** An alternate form of the simulation diagram *)

Lemma fsim_simulation':
  forall p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 (S: forward_internal_simulation p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2),
  forall i s1 t s1', Step (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' ->
  forall s2, S i s1 s2 ->
  (exists i', exists s2', SPlus (mixed_sem p2 rtl2 nc2 anc2) s2 t s2' /\ S i' s1' s2')
  \/ (exists i', fsim_order S i' i /\ t = E0 /\ S i' s1' s2).
Proof.
  intros. exploit fsim_simulation; eauto.
  intros [i' [s2' [A B]]]. intuition.
  left; exists i'; exists s2'; auto.
  inv H2.
  right; exists i'; auto.
  left; exists i'; exists s2'; split; auto. econstructor; eauto.
Qed.

(** ** Forward simulation diagrams. *)

(** Various simulation diagrams that imply forward simulation *)
(* not needed *)

(** ** Forward simulation of transition sequences *)
(* not needed *)

(** ** Composing two forward simulations *)
(* We only compose backward simulations now *)


(** * Backward simulations between two transition semantics. *)
(** The general form of a backward internal simulation. *)
(* The one used as an invariant of the JIT execution, on silent semantics *)
Record backward_internal_simulation (p1 p2: program) (rtl1 rtl2:option (RTLfun+RTLblockfun)) (nc1 nc2: asm_codes) (anc1 anc2:anchor_status): Type :=
  Backward_internal_simulation {
    bsim_index: Type;
    bsim_order: bsim_index -> bsim_index -> Prop;
    bsim_order_wf: well_founded bsim_order;
    (* bsim_order_trans: transitive _ bsim_order; *)
    bsim_match_states :> bsim_index -> mixed_state -> mixed_state -> Prop;
    bsim_match_states_refl: call_refl bsim_match_states;
    bsim_match_final_states:
      forall i s1 s2 r,
      bsim_match_states i s1 s2 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 -> final_mixed_state p2 s2 r ->
      exists s1', Star (mixed_sem p1 rtl1 nc1 anc1) s1 E0 s1' /\ final_mixed_state p1 s1' r;
    bsim_progress:
      forall i s1 s2,
      bsim_match_states i s1 s2 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 ->
      (exists r, final_mixed_state p2 s2 r) \/
      (exists t, exists s2', Step (mixed_sem p2 rtl2 nc2 anc2) s2 t s2');
    bsim_simulation:
      forall s2 t s2', Step (mixed_sem p2 rtl2 nc2 anc2) s2 t s2' ->
      forall i s1, bsim_match_states i s1 s2 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 ->
      exists i', exists s1',
         (SPlus (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' \/ (Star (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' /\ bsim_order i' i))
      /\ bsim_match_states i' s1' s2';
  }.

(** An alternate form of the simulation diagram *)
Lemma bsim_simulation':
  forall p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 (S: backward_internal_simulation p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2),
  forall i s2 t s2', Step (mixed_sem p2 rtl2 nc2 anc2) s2 t s2' ->
  forall s1, S i s1 s2 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 ->
  (exists i', exists s1', SPlus (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' /\ S i' s1' s2')
  \/ (exists i', bsim_order S i' i /\ t = E0 /\ S i' s1 s2').
Proof.
  intros. exploit bsim_simulation; eauto.
  intros [i' [s1' [A B]]]. intuition.
  left; exists i'; exists s1'; auto.
  inv H3.
  right; exists i'; auto.
  left; exists i'; exists s1'; split; auto. econstructor; eauto.
Qed.

(** ** Backward simulation diagrams. *)

(** ** Backward simulation of transition sequences *)
Section BACKWARD_SIMULATION_SEQUENCES.

Variable p1 p2: program.
Variable rtl1 rtl2: option (RTLfun+RTLblockfun).
Variable nc1: asm_codes.
Variable nc2: asm_codes.
Variable anc1 anc2: anchor_status.
Variable S: backward_internal_simulation p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2.

Lemma bsim_E0_star:
  forall s2 s2', Star (mixed_sem p2 rtl2 nc2 anc2) s2 E0 s2' ->
  forall i s1, S i s1 s2 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 ->
  exists i', exists s1', Star (mixed_sem p1 rtl1 nc1 anc1) s1 E0 s1' /\ S i' s1' s2'.
Proof.
  intros s20 s20' STAR0. pattern s20, s20'. eapply star_E0_ind; eauto.
(* base case *)
  intros. exists i; exists s1; split; auto. apply star_refl.
(* inductive case *)
  intros. exploit bsim_simulation; eauto. intros [i' [s1' [A B]]].
  assert (Star (mixed_sem p1 rtl1 nc1 anc1) s0 E0 s1'). intuition. apply plus_star; auto.
  exploit H0. eauto. eapply star_safe; eauto. intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto. eapply star_trans; eauto.
Qed.

Lemma bsim_safe:
  forall i s1 s2,
  S i s1 s2 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 -> safe (mixed_sem p2 rtl2 nc2 anc2) s2.
Proof.
  intros; red; intros.
  exploit bsim_E0_star; eauto. intros [i' [s1' [A B]]].
  eapply bsim_progress; eauto. eapply star_safe; eauto.
Qed.

Lemma bsim_E0_plus:
  forall s2 t s2', SPlus (mixed_sem p2 rtl2 nc2 anc2) s2 t s2' -> t = E0 ->
  forall i s1, S i s1 s2 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 ->
     (exists i', exists s1', SPlus (mixed_sem p1 rtl1 nc1 anc1) s1 E0 s1' /\ S i' s1' s2')
  \/ (exists i', clos_trans _ (bsim_order S) i' i /\ S i' s1 s2').
Proof.
  induction 1 using plus_ind2; intros; subst t.
(* base case *)
  exploit bsim_simulation'; eauto. intros [[i' [s1' [A B]]] | [i' [A [B C]]]].
  left; exists i'; exists s1'; auto.
  right; exists i'; intuition.
(* inductive case *)
  exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  exploit bsim_simulation'; eauto. intros [[i' [s1' [A B]]] | [i' [A [B C]]]].
  exploit bsim_E0_star. apply plus_star with (s2:=s3); eauto. eauto. eapply star_safe; eauto. apply plus_star; auto.
  intros [i'' [s1'' [P Q]]].
  left; exists i''; exists s1''; intuition. eapply plus_star_trans; eauto.
  exploit IHplus; eauto. intros [P | [i'' [P Q]]].
  left; auto.
  right; exists i''; intuition. eapply t_trans; eauto. apply t_step; auto.
Qed.

Lemma star_non_E0_split:
  forall s2 t s2', Star (mixed_sem p2 rtl2 nc2 anc2) s2 t s2' -> (length t = 1)%nat ->
  exists s2x, exists s2y, Star (mixed_sem p2 rtl2 nc2 anc2) s2 E0 s2x /\ Step (mixed_sem p2 rtl2 nc2 anc2) s2x t s2y /\ Star (mixed_sem p2 rtl2 nc2 anc2) s2y E0 s2'.
Proof.
  induction 1; intros.
  simpl in H; discriminate.
  subst t.
  assert (EITHER: t1 = E0 \/ t2 = E0).
    unfold Eapp in H2; rewrite app_length in H2.
    destruct t1; auto. destruct t2; auto. simpl in H2; lia.
  destruct EITHER; subst.
  exploit IHstar; eauto. intros [s2x [s2y [A [B C]]]].
  exists s2x; exists s2y; intuition. eapply star_left; eauto.
  rewrite E0_right. exists s1; exists s2; intuition. apply star_refl.
Qed.

End BACKWARD_SIMULATION_SEQUENCES.

(* Transitive closure is transitive *)
Lemma clos_trans_trans :
  forall (X:Type) R, transitive X (clos_trans X R).
Proof.
  intros X R. unfold transitive. intros x y z H. generalize dependent z.
  induction H; intros.
  - apply t_trans with (y:=y). apply t_step. auto. auto.
  - apply IHclos_trans1. apply IHclos_trans2. auto.
Qed.


(** ** Composing two backward simulations *)

Section COMPOSE_INTERNAL_BACKWARD_SIMULATIONS.

Variable p1 p2 p3: program.
Variable rtl1 rtl2 rtl3: option (RTLfun+RTLblockfun).
Variable nc1: asm_codes.
Variable nc2: asm_codes.
Variable nc3: asm_codes.
Variable anc1 anc2 anc3: anchor_status.
Hypothesis p3_single_events: single_events (mixed_sem p3 rtl3 nc3 anc3).
Variable S12: backward_internal_simulation p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2.
Variable S23: backward_internal_simulation p2 p3 rtl2 rtl3 nc2 nc3 anc2 anc3.

Let bb_index : Type := (bsim_index S12 * bsim_index S23)%type.

Let bb_order : bb_index -> bb_index -> Prop :=
  lex_ord (clos_trans _ (bsim_order S12)) (bsim_order S23).

Inductive bb_match_states: bb_index -> mixed_state -> mixed_state -> Prop :=
  | bb_match_later: forall i1 i2 s1 s3 s2x s2y,
      S12 i1 s1 s2x -> Star (mixed_sem p2 rtl2 nc2 anc2) s2x E0 s2y -> S23 i2 s2y s3 ->
      bb_match_states (i1, i2) s1 s3.

Lemma bb_match_at: forall i1 i2 s1 s3 s2,
  S12 i1 s1 s2 -> S23 i2 s2 s3 ->
  bb_match_states (i1, i2) s1 s3.
Proof.
  intros. econstructor; eauto. apply star_refl.
Qed.


Lemma bb_simulation_base:
  forall s3 t s3', Step (mixed_sem p3 rtl3 nc3 anc3) s3 t s3' ->
  forall i1 s1 i2 s2, S12 i1 s1 s2 -> S23 i2 s2 s3 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 ->
  exists i', exists s1',
    (SPlus (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' \/ (Star (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' /\ bb_order i' (i1, i2)))
    /\ bb_match_states i' s1' s3'.
Proof.
  intros.
  exploit (bsim_simulation' S23); eauto. eapply bsim_safe; eauto. 
  intros [ [i2' [s2' [PLUS2 MATCH2]]] | [i2' [ORD2 [EQ MATCH2]]]].
  (* 1 L2 makes one or several transitions *)
  assert (EITHER: t = E0 \/ (length t = 1)%nat).
  exploit p3_single_events; eauto.
    destruct t; auto. destruct t; auto. simpl. intros. lia.
  destruct EITHER.
  (* 1.1 these are silent transitions *)
  subst t. exploit bsim_E0_plus; eauto.
  intros [ [i1' [s1' [PLUS1 MATCH1]]] | [i1' [ORD1 MATCH1]]].
  (* 1.1.1 L1 makes one or several transitions *)
  exists (i1', i2'); exists s1'; split. auto. eapply bb_match_at; eauto.
  (* 1.1.2 L1 makes no transitions *)
  exists (i1', i2'); exists s1; split.
  right; split. apply star_refl. left; auto.
  eapply bb_match_at; eauto.
  (* 1.2 non-silent transitions *)
  exploit star_non_E0_split. apply plus_star; eauto. auto.
  intros [s2x [s2y [P [Q R]]]].
  exploit bsim_E0_star. eexact P. eauto. auto. intros [i1' [s1x [X Y]]].
  exploit bsim_simulation'. eexact Q. eauto. eapply star_safe; eauto.
  intros [[i1'' [s1y [U V]]] | [i1'' [U [V W]]]]; try (subst t; discriminate).
  exists (i1'', i2'); exists s1y; split.
  left. eapply star_plus_trans; eauto. eapply bb_match_later; eauto.
  (* 2. L2 makes no transitions *)
  subst. exists (i1, i2'); exists s1; split.
  right; split. apply star_refl. right; auto.
  eapply bb_match_at; eauto.
Qed.

Lemma bb_simulation:
  forall s3 t s3', Step (mixed_sem p3 rtl3 nc3 anc3) s3 t s3' ->
  forall i s1, bb_match_states i s1 s3 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 ->
  exists i', exists s1',
    (SPlus (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' \/ (Star (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' /\ bb_order i' i))
    /\ bb_match_states i' s1' s3'.
Proof.
  intros. inv H0.
  exploit star_inv; eauto. intros [[EQ1 EQ2] | PLUS].
  (* 1. match at *)
  subst. eapply bb_simulation_base; eauto.
  (* 2. match later *)
  exploit bsim_E0_plus; eauto.
  intros [[i1' [s1' [A B]]] | [i1' [A B]]].
  (* 2.1 one or several silent transitions *)
  exploit bb_simulation_base. eauto. auto. eexact B. eauto.
    eapply star_safe; eauto. eapply plus_star; eauto.
  intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto.
  left. eapply plus_star_trans; eauto.
  destruct C as [P | [P Q]]. apply plus_star; eauto. eauto.
  traceEq.
  (* 2.2 no silent transition *)
  exploit bb_simulation_base. eauto. auto. eexact B. eauto. auto.
  intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto.
  intuition. right; intuition.
  inv H6. left. eapply t_trans; eauto. left; auto.
Qed.

Lemma compose_backward_simulation: backward_internal_simulation p1 p3 rtl1 rtl3 nc1 nc3 anc1 anc3.
Proof.
  apply Backward_internal_simulation with (bsim_order := bb_order) (bsim_match_states := bb_match_states).
(* well founded *)
  unfold bb_order. apply wf_lex_ord. apply wf_clos_trans. apply bsim_order_wf. apply bsim_order_wf.
  (* transitivity *)
  (* { unfold bb_order. apply transitive_lex_ord. *)
  (*   - apply clos_trans_trans. *)
  (*   - apply (bsim_order_trans S23). }   *)
  (* reflexivity *)
  { unfold call_refl, p_reflexive. intros s REFL.
    specialize (bsim_match_states_refl S12). intros H. unfold call_refl, p_reflexive in H.
    specialize (H s REFL). destruct H as [i2 MATCH1].
    specialize (bsim_match_states_refl S23). intros H. unfold call_refl, p_reflexive in H.
    specialize (H s REFL). destruct H as [i3 MATCH2].
    exists (i2, i3). eapply bb_match_at; eauto. }
(* match final states *)
  intros i s1 s3 r MS SAFE FIN. inv MS.
  exploit (bsim_match_final_states S23); eauto.
    eapply star_safe; eauto. eapply bsim_safe; eauto.
  intros [s2' [A B]].
  exploit bsim_E0_star. eapply star_trans. eexact H0. eexact A. auto. eauto. auto.
  intros [i1' [s1' [C D]]].
  exploit (bsim_match_final_states S12); eauto. eapply star_safe; eauto.
  intros [s1'' [P Q]].
  exists s1''; split; auto. eapply star_trans; eauto.
(* progress *)
  intros i s1 s3 MS SAFE. inv MS.
  eapply (bsim_progress S23). eauto. eapply star_safe; eauto. eapply bsim_safe; eauto.
(* simulation *)
  exact bb_simulation.
Qed.


End COMPOSE_INTERNAL_BACKWARD_SIMULATIONS.


Section FORWARD_TO_BACKWARD.

Variable p1 p2: program.
Variable rtl1 rtl2: option (RTLfun+RTLblockfun).
Variable nc1: asm_codes.
Variable nc2: asm_codes.
Variable anc1 anc2: anchor_status. 
Variable FS: forward_internal_simulation p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2.
Hypothesis p1_receptive: receptive (mixed_sem p1 rtl1 nc1 anc1).
Hypothesis p2_determinate: determinate (mixed_sem p2 rtl2 nc2 anc2).

(** Exploiting forward simulation *)

Inductive f2b_transitions: mixed_state -> mixed_state -> Prop :=
  | f2b_trans_final: forall s1 s2 s1' r,
      Star (mixed_sem p1 rtl1 nc1 anc1) s1 E0 s1' ->
      final_mixed_state p1 s1' r ->
      final_mixed_state p2 s2 r ->
      f2b_transitions s1 s2
  | f2b_trans_step: forall s1 s2 s1' t s1'' s2' i' i'',
      Star (mixed_sem p1 rtl1 nc1 anc1) s1 E0 s1' ->
      Step (mixed_sem p1 rtl1 nc1 anc1) s1' t s1'' ->
      SPlus (mixed_sem p2 rtl2 nc2 anc2) s2 t s2' ->
      FS i' s1' s2 ->
      FS i'' s1'' s2' ->
      f2b_transitions s1 s2.

Lemma f2b_progress:
  forall i s1 s2, FS i s1 s2 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 -> f2b_transitions s1 s2.
Proof.
  intros i0; pattern i0. apply well_founded_ind with (R := fsim_order FS).
  apply fsim_order_wf.
  intros i REC s1 s2 MATCH SAFE.
  destruct (SAFE s1) as [[r FINAL] | [t [s1' STEP1]]]. apply star_refl.
  (* final state reached *)
  eapply f2b_trans_final; eauto.
  apply star_refl.
  eapply fsim_match_final_states; eauto.
  (* L1 can make one step *)
  exploit (fsim_simulation FS); eauto. intros [i' [s2' [A MATCH']]].
  assert (B: SPlus (mixed_sem p2 rtl2 nc2 anc2) s2 t s2' \/ (s2' = s2 /\ t = E0 /\ fsim_order FS i' i)).
    intuition.
    destruct (star_inv H0); intuition.
  clear A. destruct B as [PLUS2 | [EQ1 [EQ2 ORDER]]].
  eapply f2b_trans_step; eauto. apply star_refl.
  subst. exploit REC; eauto. eapply star_safe; eauto. apply star_one; auto.
  intros TRANS; inv TRANS.
  eapply f2b_trans_final with (s1':=s1'0); eauto. eapply star_left; eauto.
  eapply f2b_trans_step; eauto. eapply star_left; eauto.
Qed.

Lemma fsim_simulation_not_E0:
  forall s1 t s1', Step (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' -> t <> E0 ->
  forall i s2, FS i s1 s2 ->
  exists i', exists s2', SPlus (mixed_sem p2 rtl2 nc2 anc2) s2 t s2' /\ FS i' s1' s2'.
Proof.
  intros. exploit (fsim_simulation FS); eauto. intros [i' [s2' [A B]]].
  exists i'; exists s2'; split; auto.
  destruct A. auto. destruct H2. exploit star_inv; eauto. intros [[EQ1 EQ2] | P]; auto.
  congruence.
Qed.

(** Exploiting determinacy *)

Remark silent_or_not_silent:
  forall t, t = E0 \/ t <> E0.
Proof.
  intros; unfold E0; destruct t; auto; right; congruence.
Qed.

Remark not_silent_length:
  forall t1 t2, (length (t1 ** t2) <= 1)%nat -> t1 = E0 \/ t2 = E0.
Proof.
  unfold Eapp, E0; intros. rewrite app_length in H.
  destruct t1; destruct t2; auto. simpl in H. lia.
Qed.

Lemma f2b_determinacy_inv:
  forall s2 t' s2' t'' s2'',
  Step (mixed_sem p2 rtl2 nc2 anc2) s2 t' s2' -> Step (mixed_sem p2 rtl2 nc2 anc2) s2 t'' s2'' ->
  (t' = E0 /\ t'' = E0 /\ s2' = s2'')
  \/ (t' <> E0 /\ t'' <> E0 /\ match_traces (* (symbolenv L1) *) t' t'').
Proof.
  intros.
  assert (match_traces (* (symbolenv L2) *) t' t'').
    eapply sd_determ_1; eauto.
  destruct (silent_or_not_silent t').
  subst. inv H1.
  left; intuition. eapply sd_determ_2; eauto.
  destruct (silent_or_not_silent t'').
  subst. inv H1. elim H2; auto.
  right; intuition.
Qed.

Lemma f2b_determinacy_star:
  forall s s1, Star (mixed_sem p2 rtl2 nc2 anc2) s E0 s1 ->
  forall t s2 s3,
  Step (mixed_sem p2 rtl2 nc2 anc2) s1 t s2 -> t <> E0 ->
  Star (mixed_sem p2 rtl2 nc2 anc2) s t s3 ->
  Star (mixed_sem p2 rtl2 nc2 anc2) s1 t s3.
Proof.
  intros s0 s01 ST0. pattern s0, s01. eapply star_E0_ind; eauto.
  intros. inv H3. congruence.
  exploit f2b_determinacy_inv. eexact H. eexact H4.
  intros [[EQ1 [EQ2 EQ3]] | [NEQ1 [NEQ2 MT]]].
  subst. simpl in *. eauto.
  congruence.
Qed.

(** Orders *)

Inductive f2b_index : Type :=
  | F2BI_before (n: nat)
  | F2BI_after (n: nat).

Inductive f2b_order: f2b_index -> f2b_index -> Prop :=
  | f2b_order_before: forall n n',
      (n' < n)%nat ->
      f2b_order (F2BI_before n') (F2BI_before n)
  | f2b_order_after: forall n n',
      (n' < n)%nat ->
      f2b_order (F2BI_after n') (F2BI_after n)
  | f2b_order_switch: forall n n',
      f2b_order (F2BI_before n') (F2BI_after n).

Lemma wf_f2b_order:
  well_founded f2b_order.
Proof.
  assert (ACC1: forall n, Acc f2b_order (F2BI_before n)).
    intros n0; pattern n0; apply lt_wf_ind; intros.
    constructor; intros. inv H0. auto.
  assert (ACC2: forall n, Acc f2b_order (F2BI_after n)).
    intros n0; pattern n0; apply lt_wf_ind; intros.
    constructor; intros. inv H0. auto. auto.
  red; intros. destruct a; auto.
Qed.

Lemma trans_f2b_order:
  transitive _ f2b_order.
Proof.
  unfold transitive. intros x y z HXY HYZ.
  inv HXY; inv HYZ.
  - constructor. lia.
  - constructor.
  - constructor. lia.
  - constructor.
Qed.

(** Constructing the backward simulation *)

Inductive f2b_match_states: f2b_index -> mixed_state -> mixed_state -> Prop :=
  | f2b_match_at: forall i s1 s2,
      FS i s1 s2 ->
      f2b_match_states (F2BI_after O) s1 s2
  | f2b_match_before: forall s1 t s1' s2b s2 n s2a i,
      Step (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' ->  t <> E0 ->
      Star (mixed_sem p2 rtl2 nc2 anc2) s2b E0 s2 ->
      starN (step (mixed_sem p2 rtl2 nc2 anc2)) (globalenv (mixed_sem p2 rtl2 nc2 anc2)) n s2 t s2a ->
      FS i s1 s2b ->
      f2b_match_states (F2BI_before n) s1 s2
  | f2b_match_after: forall n s2 s2a s1 i,
      starN (step (mixed_sem p2 rtl2 nc2 anc2)) (globalenv (mixed_sem p2 rtl2 nc2 anc2)) (S n) s2 E0 s2a ->
      FS i s1 s2a ->
      f2b_match_states (F2BI_after (S n)) s1 s2.

Remark f2b_match_after':
  forall n s2 s2a s1 i,
  starN (step (mixed_sem p2 rtl2 nc2 anc2)) (globalenv (mixed_sem p2 rtl2 nc2 anc2)) n s2 E0 s2a ->
  FS i s1 s2a ->
  f2b_match_states (F2BI_after n) s1 s2.
Proof.
  intros. inv H.
  econstructor; eauto.
  econstructor; eauto. econstructor; eauto.
Qed.

(** Backward simulation of L2 steps *)

Lemma f2b_simulation_step:
  forall s2 t s2', Step (mixed_sem p2 rtl2 nc2 anc2) s2 t s2' ->
  forall i s1, f2b_match_states i s1 s2 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 ->
  exists i', exists s1',
    (SPlus (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' \/ (Star (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' /\ f2b_order i' i))
     /\ f2b_match_states i' s1' s2'.
Proof.
  intros s2 t s2' STEP2 i s1 MATCH SAFE.
  inv MATCH.
(* 1. At matching states *)
  exploit f2b_progress; eauto. intros TRANS; inv TRANS.
  (* 1.1  L1 can reach final state and L2 is at final state: impossible! *)
  exploit (sd_final_nostep p2_determinate); eauto. contradiction.
  (* 1.2  L1 can make 0 or several steps; L2 can make 1 or several matching steps. *)
  inv H2.
  exploit f2b_determinacy_inv. eexact H5. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  (* 1.2.1  L2 makes a silent transition *)
  destruct (silent_or_not_silent t2).
  (* 1.2.1.1  L1 makes a silent transition too: perform transition now and go to "after" state *)
  subst. simpl in *. destruct (star_starN H6) as [n STEPS2].
  exists (F2BI_after n); exists s1''; split.
  left. eapply plus_right; eauto.
  eapply f2b_match_after'; eauto.
  (* 1.2.1.2 L1 makes a non-silent transition: keep it for later and go to "before" state *)
  subst. simpl in *. destruct (star_starN H6) as [n STEPS2].
  exists (F2BI_before n); exists s1'; split.
  right; split. auto. constructor.
  econstructor. eauto. auto. apply star_one; eauto. eauto. eauto.
  (* 1.2.2 L2 makes a non-silent transition, and so does L1 *)
  exploit not_silent_length. eapply (sr_traces p1_receptive); eauto. intros [EQ | EQ].
  congruence.
  subst t2. rewrite E0_right in H1.
  (* Use receptiveness to equate the traces *)
  exploit (sr_receptive p1_receptive). apply H1. apply MT. eauto. intros [s1''' STEP1].
  exploit fsim_simulation_not_E0. eexact STEP1. auto. eauto.
  intros [i''' [s2''' [P Q]]]. inv P.
  (* Exploit determinacy *)
  exploit not_silent_length. eapply (sr_traces p1_receptive); eauto. intros [EQ | EQ].
  subst t0. simpl in *. exploit sd_determ_1. eauto. eexact STEP2. eexact H2.
  intros. elim NOT2. inv H8. auto.
  subst t2. rewrite E0_right in *.
  assert (s4 = s2'). eapply sd_determ_2; eauto. subst s4.
  (* Perform transition now and go to "after" state *)
  destruct (star_starN H7) as [n STEPS2]. exists (F2BI_after n); exists s1'''; split.
  left. eapply plus_right; eauto.
  eapply f2b_match_after'; eauto.

(* 2. Before *)
  inv H2. congruence.
  exploit f2b_determinacy_inv. eexact H4. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  (* 2.1 L2 makes a silent transition: remain in "before" state *)
  subst. simpl in *. exists (F2BI_before n0); exists s1; split.
  right; split. apply star_refl. constructor. lia.
  econstructor; eauto. eapply star_right; eauto.
  (* 2.2 L2 make a non-silent transition *)
  exploit not_silent_length. eapply (sr_traces p1_receptive); eauto. intros [EQ | EQ].
  congruence.
  subst. rewrite E0_right in *.
  (* Use receptiveness to equate the traces *)
  exploit (sr_receptive p1_receptive). apply H. apply MT. intros [s1''' STEP1].
  exploit fsim_simulation_not_E0. eexact STEP1. auto. eauto.
  intros [i''' [s2''' [P Q]]].
  (* Exploit determinacy *)
  exploit f2b_determinacy_star. eauto. eexact STEP2. auto. apply plus_star; eauto.
  intro R. inv R. congruence.
  exploit not_silent_length. eapply (sr_traces p1_receptive); eauto. intros [EQ | EQ].
  subst. simpl in *. exploit sd_determ_1. eauto. eexact STEP2. eexact H2.
  intros. elim NOT2. inv H7; auto.
  subst. rewrite E0_right in *.
  assert (s3 = s2'). eapply sd_determ_2; eauto. subst s3.
  (* Perform transition now and go to "after" state *)
  destruct (star_starN H6) as [n STEPS2]. exists (F2BI_after n); exists s1'''; split.
  left. apply plus_one; auto.
  eapply f2b_match_after'; eauto.

(* 3. After *)
  inv H. exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  exploit f2b_determinacy_inv. eexact H2. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  subst. exists (F2BI_after n); exists s1; split.
  right; split. apply star_refl. constructor; lia.
  eapply f2b_match_after'; eauto.
  congruence.
Qed.

(** The backward simulation *)

Lemma forward_to_backward_simulation: backward_internal_simulation p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2.
Proof.
  eapply Backward_internal_simulation.
   (* with (bsiml_order := f2b_order). (bsiml_match_states := f2b_match_states). *)
  apply wf_f2b_order.
  (* transitivity *)
  (* apply trans_f2b_order. *)
  (* reflexivity *)
  { unfold call_refl, p_reflexive. intros s REFL.
    specialize (fsim_match_states_refl FS). intros H. unfold call_refl, p_reflexive in H.
    specialize (H s REFL). destruct H as [i MATCH].
    exists (F2BI_after 0). eapply f2b_match_at. eauto. }
(* final states *)
  intros. inv H.
  exploit f2b_progress; eauto. intros TRANS; inv TRANS.
  assert (r0 = r) by (eapply (sd_final_determ p2_determinate); eauto). subst r0.
  exists s1'; auto.
  inv H4. exploit (sd_final_nostep p2_determinate); eauto. contradiction.
  inv H5. congruence. exploit (sd_final_nostep p2_determinate); eauto. contradiction.
  inv H2. exploit (sd_final_nostep p2_determinate); eauto. contradiction.
(* progress *)
  intros. inv H.
  exploit f2b_progress; eauto. intros TRANS; inv TRANS.
  left; exists r; auto.
  inv H3. right; econstructor; econstructor; eauto.
  inv H4. congruence. right; econstructor; econstructor; eauto.
  inv H1. right; econstructor; econstructor; eauto.
(* simulation *)
  exact f2b_simulation_step.
Qed.

End FORWARD_TO_BACKWARD.


(** * Alernate internal backward definition  *)
(* Where the order and match_states relation are made parameters *)
(* This helps writing the external simulation invariant *)

Record backward_internal_simulation' (p1 p2: program) (rtl1 rtl2:option (RTLfun+RTLblockfun)) (nc1 nc2: asm_codes) (anc1 anc2:anchor_status)
       (idxt: Type)
       (order: idxt -> idxt -> Prop)
       (match_states: idxt -> mixed_state -> mixed_state -> Prop)
  : Type :=
  Backward_internal_simulation' {
    order_wf: well_founded order;
    (* order_trans: transitive _ order;   *)
    match_states_refl: call_refl match_states;
    match_final_states:
      forall i s1 s2 r,
      match_states i s1 s2 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 -> final_mixed_state p2 s2 r ->
      exists s1', Star (mixed_sem p1 rtl1 nc1 anc1) s1 E0 s1' /\ final_mixed_state p1 s1' r;
    progress:
      forall i s1 s2,
      match_states i s1 s2 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 ->
      (exists r, final_mixed_state p2 s2 r) \/
      (exists t, exists s2', Step (mixed_sem p2 rtl2 nc2 anc2) s2 t s2');
    simulation:
      forall s2 t s2', Step (mixed_sem p2 rtl2 nc2 anc2) s2 t s2' ->
      forall i s1, match_states i s1 s2 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 ->
      exists i', exists s1',
         (SPlus (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' \/ (Star (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' /\ order i' i))
      /\ match_states i' s1' s2';
  }.

Lemma bsim_simulation'':
  forall p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 idx (ord:idx->idx->Prop) ms
    (S: backward_internal_simulation' p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 ord ms),
  forall i s2 t s2', Step (mixed_sem p2 rtl2 nc2 anc2) s2 t s2' ->
  forall s1, ms i s1 s2 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 ->
  (exists i', exists s1', SPlus (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' /\ ms i' s1' s2')
  \/ (exists i', ord i' i /\ t = E0 /\ ms i' s1 s2').
Proof.
  intros. exploit simulation; eauto.
  intros [i' [s1' [A B]]]. intuition.
  left; exists i'; exists s1'; auto.
  inv H3.
  right; exists i'; auto.
  left; exists i'; exists s1'; split; auto. econstructor; eauto.
Qed.


(* Equivalence between the two definition *)
Theorem backward_eq:
  forall p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2,
    backward_internal_simulation p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 ->
    exists idxt (order:idxt->idxt->Prop) ms, backward_internal_simulation' p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 order ms.
Proof.
  intros p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 X. exists (bsim_index X). exists (bsim_order X). exists (bsim_match_states X).
  apply Backward_internal_simulation'; destruct X; auto.
Qed.


Theorem eq_backward:
  forall p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2,
  forall idxt (order:idxt->idxt->Prop) ms, backward_internal_simulation' p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 order ms ->
                                 backward_internal_simulation p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2.
Proof.
  intros p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 idxt order ms H.
  apply Backward_internal_simulation with (bsim_order:=order) (bsim_match_states:=ms);
    destruct H; auto.
Qed.
  
(** * Backward simulation reflexivity  *)
(* This is used at the very beginning of the JIT proof, to show that there is an internal simulation between the initial program and itself *)
Definition refl_type := unit.
Inductive refl_order: unit -> unit -> Prop := .
Inductive refl_match_states: refl_type -> mixed_state -> mixed_state -> Prop :=
| match_same: forall s, refl_match_states tt s s.

Theorem wf_refl: well_founded refl_order.
Proof.
  unfold well_founded. intros. destruct a. constructor. intros. inv H.
Qed.

Theorem refl_refl: reflexive refl_match_states.
Proof.
  unfold reflexive. intros. exists tt. constructor.
Qed.

Theorem trans_refl: transitive _ refl_order.
Proof.
  unfold transitive. intros. inv H.
Qed.

Lemma backward_refl:
  forall p nc rtl anc,
    backward_internal_simulation' p p rtl rtl nc nc anc anc refl_order refl_match_states.
Proof.
  intros p rtl nc anc. apply Backward_internal_simulation'.
  - apply wf_refl.
  (* - apply trans_refl. *)
  - unfold call_refl, p_reflexive. intros s REFL. exists tt. split; auto.
  - intros i s1 s2 r H H0 H1. inv H. exists s2. split. apply star_refl. auto.
  - intros i s1 s2 H H0. inv H. unfold safe in H0. apply H0. apply star_refl.
  - intros s2 t s2' H i s1 H0 H1. inv H0. exists tt. exists s2'. split.
    left. apply plus_one. auto. constructor.
Qed.

(* non-explicit version *)
Lemma backward_internal_reflexivity:
  forall p rtl nc anc, backward_internal_simulation p p rtl rtl nc nc anc anc.
Proof.
  intros p rtl nc anc. eapply eq_backward. eapply backward_refl.
Qed.

(** * Exploiting Sequences  *)

(* Exploiting silent stars *)
Lemma bsim_E0_star':
  forall (p1 p2: program) (rtl1 rtl2:option (RTLfun+RTLblockfun)) (nc1 nc2:asm_codes) (anc1 anc2:anchor_status) idxt (ord:idxt->idxt->Prop) ms
    (S: backward_internal_simulation' p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 ord ms),
  forall s2 s2', Star (mixed_sem p2 rtl2 nc2 anc2) s2 E0 s2' ->
  forall i s1, ms i s1 s2 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 ->
  exists i', exists s1', Star (mixed_sem p1 rtl1 nc1 anc1) s1 E0 s1' /\ ms i' s1' s2'.
Proof.
  intros p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 idxt ord ms S.
  intros s20 s20' STAR0. pattern s20, s20'. eapply star_E0_ind; eauto.
(* base case *)
  intros. exists i; exists s1; split; auto. apply star_refl.
(* inductive case *)
  intros. exploit simulation; eauto. intros [i' [s1' [A B]]].
  assert (Star (mixed_sem p1 rtl1 nc1 anc1) s0 E0 s1'). intuition. apply plus_star; auto.
  exploit H0. eauto. eapply star_safe; eauto. intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto. eapply star_trans; eauto.
Qed.

(* Exploiting silent plus *)
(* We use the transitivity of the order to make this possible *)
(* This shows that on a PLUS we can have a simulation diagram without changing orders *)
(* Lemma bsim_E0_plus': *)
(*   forall (p1 p2: program) (rtl1 rtl2: option RTLfun) (nc1 nc2: asm_codes) idxt (ord:idxt->idxt->Prop) ms *)
(*     (S: backward_internal_simulation' p1 p2 rtl1 rtl2 nc1 nc2 ord ms), *)
(*   forall s2 t s2', SPlus (mixed_sem p2 rtl2 nc2) s2 t s2' -> t = E0 -> *)
(*   forall i s1, ms i s1 s2 -> safe (mixed_sem p1 rtl1 nc1) s1 -> *)
(*      (exists i', exists s1', SPlus (mixed_sem p1 rtl1 nc1) s1 E0 s1' /\ ms i' s1' s2') *)
(*   \/ (exists i', ord i' i /\ ms i' s1 s2'). *)
(* Proof. *)
(*   intros p1 p2 rtl1 rtl2 nc1 nc2 idxt ord ms S. *)
(*   induction 1 using plus_ind2; intros; subst t. *)
(* (* base case *) *)
(*   exploit bsim_simulation''; eauto. intros [[i' [s1' [A B]]] | [i' [A [B C]]]]. *)
(*   left; exists i'; exists s1'; auto. *)
(*   right; exists i'; intuition. *)
(* (* inductive case *) *)
(*   exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst. *)
(*   exploit bsim_simulation''; eauto. *)
(*   intros [[i' [s1' [A B]]] | [i' [A [B C]]]]. *)
(*   exploit bsim_E0_star'. eauto. apply plus_star with (s1:=s2); eauto. eauto.  *)
(*   eapply star_safe; eauto. apply plus_star; eauto. *)
(*   intros [i'' [s1'' [P Q]]]. *)
(*   left; exists i''; exists s1''; intuition. eapply plus_star_trans; eauto. *)
(*   exploit IHplus; eauto. intros [P | [i'' [P Q]]]. *)
(*   left; auto. *)
(*   right; exists i''; intuition. assert (OT: transitive _ ord) by apply (order_trans S). *)
(*   unfold transitive in OT. eapply OT; eauto. *)
(* Qed. *)

Lemma star_E0:
  forall p rtl nc anc s1 s2,
    Star (mixed_sem p rtl nc anc) s1 E0 s2 ->
    SPlus (mixed_sem p rtl nc anc) s1 E0 s2 \/ s1 = s2.
Proof.
  intros. inv H.
  right. auto. left. econstructor; eauto.
Qed.

(* Lemma exploit_starstep: *)
(*   forall (p1 p2: program) (rtl1 rtl2:option RTLfun) (nc1 nc2:asm_codes) idxt (ord:idxt->idxt->Prop) ms *)
(*     (S: backward_internal_simulation' p1 p2 rtl1 rtl2 nc1 nc2 ord ms), *)
(*   forall s2 t s2' s2'', Star (mixed_sem p2 rtl2 nc2) s2 E0 s2' -> *)
(*                    Step (mixed_sem p2 rtl2 nc2) s2' t s2'' -> *)
(*   forall i s1, ms i s1 s2 -> safe (mixed_sem p1 rtl1 nc1) s1 -> *)
(*           exists i', exists s1', (SPlus (mixed_sem p1 rtl1 nc1) s1 t s1' \/ (Star (mixed_sem p1 rtl1 nc1) s1 t s1' /\ ord i' i) ) /\ *)
(*                        ms i' s1' s2''. *)
(* Proof. *)
(*   intros p1 p2 rtl1 rtl2 nc1 nc2 idxt ord ms S s2 t s2' s2'' STAR STEP i s1 MATCH SAFE. *)
(*   apply star_E0 in STAR. destruct STAR as [PLUS | EQ]. *)
(*   - specialize (bsim_E0_plus' S PLUS eq_refl i MATCH SAFE). *)
(*     intros [[i' [s1' [PLUSSRC MATCH']]]|[i' [ORD MATCH']]]. *)
(*     + assert (SAFE': safe (mixed_sem p1 rtl1 nc1) s1'). *)
(*       { eapply star_safe; eauto. apply plus_star. auto. } *)
(*       specialize ((simulation S) s2' t s2'' STEP i' s1' MATCH' SAFE'). *)
(*       intros [i'' [s1'' [[PLUS' | [STAR ORD]] MATCH'']]]. *)
(*       * exists i''. exists s1''. split; auto. left. eapply plus_trans; eauto. *)
(*       * exists i''. exists s1''. split; auto. left. eapply plus_star_trans; eauto. *)
(*     + specialize ((simulation S) s2' t s2'' STEP i' s1 MATCH' SAFE). *)
(*       intros [i'' [s1'' [[PLUS' | [STAR ORD']] MATCH'']]]. *)
(*       * exists i''. exists s1''. split; auto. *)
(*       * exists i''. exists s1''. split; auto. right. split; auto. *)
(*         assert (TRANS: transitive _ ord) by apply (order_trans S). unfold transitive in TRANS. *)
(*         eapply TRANS; eauto. *)
(*   - subst. *)
(*     specialize ((simulation S) s2' t s2'' STEP i s1 MATCH SAFE). *)
(*     intros [i' [s1' [[PLUS | [STAR ORD]] MATCH']]]. *)
(*     + exists i'. exists s1'. split; auto. *)
(*     + exists i'. exists s1'. split; auto. *)
(* Qed. *)

(** * Composing simulations explicitely  *)
Lemma bsim_E0_star'':
  forall p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 i (ord:i->i->Prop) ms
    (SIM: backward_internal_simulation' p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 ord ms),
  forall s2 s2', Star (mixed_sem p2 rtl2 nc2 anc2) s2 E0 s2' ->
  forall i s1, ms i s1 s2 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 ->
  exists i', exists s1', Star (mixed_sem p1 rtl1 nc1 anc1) s1 E0 s1' /\ ms i' s1' s2'.
Proof.
  intros p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 idx ord ms SIM.
  intros s20 s20' STAR0. pattern s20, s20'. eapply star_E0_ind; eauto.
(* base case *)
  intros. exists i; exists s1; split; auto. apply star_refl.
(* inductive case *)
  intros. exploit simulation; eauto. intros [i' [s1' [A B]]].
  assert (Star (mixed_sem p1 rtl1 nc1 anc1) s0 E0 s1'). intuition. apply plus_star; auto.
  exploit H0. eauto. eapply star_safe; eauto. intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto. eapply star_trans; eauto.
Qed.

Lemma bsim_E0_plus'':
  forall p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 i (ord:i->i->Prop) ms
    (SIM: backward_internal_simulation' p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 ord ms),
  forall s2 t s2', SPlus (mixed_sem p2 rtl2 nc2 anc2) s2 t s2' -> t = E0 ->
  forall i s1, ms i s1 s2 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 ->
     (exists i', exists s1', SPlus (mixed_sem p1 rtl1 nc1 anc1) s1 E0 s1' /\ ms i' s1' s2')
  \/ (exists i', clos_trans _ (ord) i' i /\ ms i' s1 s2').
Proof.
  intros p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 idx ord ms SIM.
  induction 1 using plus_ind2; intros; subst t.
(* base case *)
  exploit bsim_simulation''; eauto. intros [[i' [s1' [A B]]] | [i' [A [B C]]]].
  left; exists i'; exists s1'; auto.
  right; exists i'; intuition.
(* inductive case *)
  exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  exploit bsim_simulation''; eauto. intros [[i' [s1' [A B]]] | [i' [A [B C]]]].
  exploit bsim_E0_star''. apply SIM. apply plus_star with (s1:=s2); eauto. eauto.
  eapply star_safe; eauto. apply plus_star; auto.
  intros [i'' [s1'' [P Q]]].
  left; exists i''; exists s1''; intuition. eapply plus_star_trans; eauto.
  exploit IHplus; eauto. intros [P | [i'' [P Q]]].
  left; auto.
  right; exists i''; intuition. eapply t_trans; eauto. apply t_step; auto.
Qed.


Section COMPOSE_INTERNAL_BACKWARD_SIMULATIONS_EXPLICIT.

Variable p1 p2 p3: program.
Variable rtl1 rtl2 rtl3:option (RTLfun+RTLblockfun).
Variable nc1: asm_codes.
Variable nc2: asm_codes.
Variable nc3: asm_codes.
Variable anc1 anc2 anc3: anchor_status.
Hypothesis p3_single_events: single_events (mixed_sem p3 rtl3 nc3 anc3).
Variable i12: Type.
Variable i23: Type.
Variable ord12: i12 -> i12 -> Prop.
Variable ord23: i23 -> i23 -> Prop.
Variable ms12: i12 -> mixed_state -> mixed_state -> Prop.
Variable ms23: i23 -> mixed_state -> mixed_state -> Prop.
Variable S12: backward_internal_simulation' p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 ord12 ms12.
Variable S23: backward_internal_simulation' p2 p3 rtl2 rtl3 nc2 nc3 anc2 anc3 ord23 ms23.


Let bb_index: Type := (i12 * i23)%type.

Let bb_order: bb_index -> bb_index -> Prop :=
  lex_ord (clos_trans _ ord12) (ord23).

Inductive bb_ms: bb_index -> mixed_state -> mixed_state -> Prop :=
  | bb_later: forall i1 i2 s1 s3 s2x s2y,
      ms12 i1 s1 s2x -> Star (mixed_sem p2 rtl2 nc2 anc2) s2x E0 s2y -> ms23 i2 s2y s3 ->
      bb_ms (i1, i2) s1 s3.

Lemma bb_match_at':
  forall i1 i2 s1 s2 s3,
  ms12 i1 s1 s2 -> ms23 i2 s2 s3 ->
  bb_ms (i1, i2) s1 s3.
Proof.
  intros. econstructor; eauto. apply star_refl.
Qed.

Lemma bsim_safe':
  forall p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 i (ord:i->i->Prop) ms
    (SIM: backward_internal_simulation' p1 p2 rtl1 rtl2 nc1 nc2 anc1 anc2 ord ms),
  forall i s1 s2,
  ms i s1 s2 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 -> safe (mixed_sem p2 rtl2 nc2 anc2) s2.
Proof.
  intros; red; intros.
  exploit bsim_E0_star''; eauto. intros [i' [s1' [A B]]].
  eapply progress; eauto. eapply star_safe; eauto.
Qed.


Lemma bb_simulation_base':
  forall s3 t s3', Step (mixed_sem p3 rtl3 nc3 anc3) s3 t s3' ->
  forall i1 s1 i2 s2, ms12 i1 s1 s2 -> ms23 i2 s2 s3 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 ->
  exists i', exists s1',
    (SPlus (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' \/ (Star (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' /\ bb_order i' (i1, i2)))
    /\ bb_ms i' s1' s3'.
Proof.
  intros.
  exploit (bsim_simulation'' S23); eauto. eapply bsim_safe'; eauto. 
  intros [ [i2' [s2' [PLUS2 MATCH2]]] | [i2' [ORD2 [EQ MATCH2]]]].
  (* 1 L2 makes one or several transitions *)
  assert (EITHER: t = E0 \/ (length t = 1)%nat).
  exploit p3_single_events; eauto.
    destruct t; auto. destruct t; auto. simpl. intros. lia.
  destruct EITHER.
  (* 1.1 these are silent transitions *)
  subst t. exploit bsim_E0_plus''. apply S12. eauto. auto. eauto. auto.
  intros [ [i1' [s1' [PLUS1 MATCH1]]] | [i1' [ORD1 MATCH1]]].
  (* 1.1.1 L1 makes one or several transitions *)
  exists (i1', i2'); exists s1'; split. auto. eapply bb_match_at'; eauto.
  (* 1.1.2 L1 makes no transitions *)
  exists (i1', i2'); exists s1; split.
  right; split. apply star_refl. left; auto.
  eapply bb_match_at'; eauto.
  (* 1.2 non-silent transitions *)
  exploit star_non_E0_split. apply plus_star; eauto. auto.
  intros [s2x [s2y [P [Q R]]]].
  exploit bsim_E0_star''. apply S12. eexact P. eauto. auto. intros [i1' [s1x [X Y]]].
  exploit bsim_simulation''. apply S12. eexact Q. eauto. eapply star_safe; eauto.
  intros [[i1'' [s1y [U V]]] | [i1'' [U [V W]]]]; try (subst t; discriminate).
  exists (i1'', i2'); exists s1y; split.
  left. eapply star_plus_trans; eauto. eapply bb_later; eauto.
  (* 2. L2 makes no transitions *)
  subst. exists (i1, i2'); exists s1; split.
  right; split. apply star_refl. right; auto.
  eapply bb_match_at'; eauto.
Qed.

Lemma bb_simulation':
  forall s3 t s3', Step (mixed_sem p3 rtl3 nc3 anc3) s3 t s3' ->
  forall i s1, bb_ms i s1 s3 -> safe (mixed_sem p1 rtl1 nc1 anc1) s1 ->
  exists i', exists s1',
    (SPlus (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' \/ (Star (mixed_sem p1 rtl1 nc1 anc1) s1 t s1' /\ bb_order i' i))
    /\ bb_ms i' s1' s3'.
Proof.
  intros. inv H0.
  exploit star_inv; eauto. intros [[EQ1 EQ2] | PLUS].
  (* 1. match at *)
  subst. eapply bb_simulation_base'; eauto.
  (* 2. match later *)
  exploit bsim_E0_plus''. apply S12. eauto. auto. eauto. auto.
  intros [[i1' [s1' [A B]]] | [i1' [A B]]].
  (* 2.1 one or several silent transitions *)
  exploit bb_simulation_base'. apply H.  eexact B. eauto.
    eapply star_safe; eauto. eapply plus_star; eauto.
  intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto.
  left. eapply plus_star_trans; eauto.
  destruct C as [P | [P Q]]. apply plus_star; eauto. eauto.
  traceEq.
  (* 2.2 no silent transition *)
  exploit bb_simulation_base'. apply H.  eexact B. eauto. auto.
  intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto.
  intuition. right; intuition.
  inv H6. left. eapply t_trans; eauto. left; auto.
Qed.


Theorem compose_backward_simulation':
  backward_internal_simulation' p1 p3 rtl1 rtl3 nc1 nc3 anc1 anc3 (bb_order) (bb_ms).
Proof.
  apply Backward_internal_simulation'. 
(* well founded *)
  unfold bb_order. apply wf_lex_ord. apply wf_clos_trans. apply (order_wf S12). apply (order_wf S23).
  (* transitivity *)
  (* { unfold bb_order. apply transitive_lex_ord. *)
  (*   - apply clos_trans_trans. *)
  (*   - apply (order_trans S23). }   *)
  (* reflexivity *)
  { unfold call_refl, p_reflexive. intros s REFL.
    specialize (match_states_refl S12). intros H. unfold call_refl, p_reflexive in H.
    specialize (H s REFL). destruct H as [i2 MATCH1].
    specialize (match_states_refl S23). intros H. unfold call_refl, p_reflexive in H.
    specialize (H s REFL). destruct H as [i3 MATCH2].
    exists (i2, i3). eapply bb_match_at'; eauto. }
(* match final states *)
  intros i s1 s3 r MS SAFE FIN. inv MS.
  exploit (match_final_states S23 ); eauto.
    eapply star_safe; eauto. eapply bsim_safe'; eauto. 
  intros [s2' [A B]].
  exploit bsim_E0_star''. apply S12. eapply star_trans. eexact H0. eexact A. auto. eauto. auto.
  intros [i1' [s1' [C D]]].
  exploit (match_final_states S12); eauto. eapply star_safe; eauto.
  intros [s1'' [P Q]].
  exists s1''; split; auto. eapply star_trans; eauto.
(* progress *)
  intros i s1 s3 MS SAFE. inv MS.
  eapply (progress S23). eauto. eapply star_safe; eauto. eapply bsim_safe'; eauto.
  (* simulation *)
  exact bb_simulation'.
Qed.

End COMPOSE_INTERNAL_BACKWARD_SIMULATIONS_EXPLICIT.
