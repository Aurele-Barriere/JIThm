(* Correctness of the optimization step *)

Require Import RTL.
Require Import IR.
Require Import monad.
Require Import monad_impl.
Require Import common.
Require Import Coqlib.
Require Import primitives.
Require Import optimizer.
Require Import mixed_sem.
Require Import customSmallstep.
Require Import internal_simulations.
Require Import Errors.
Require Import sem_properties.
Require Import IRtoRTLblock.
Require Import flattenRTL.
Require Import backend.
Require Import IRtoRTLblock_proof.
Require Import flattenRTL_proof.
Require Import backend_proof.

(** * Backward simulation reflexivity  *)
(* Show that there is a simulation between a program and itself *)
Definition refl_type := unit.
Inductive refl_order: unit -> unit -> Prop := .
Inductive refl_match_states (state:Type): refl_type -> state -> state -> Prop :=
| match_same: forall s, refl_match_states state tt s s.

Theorem wf_refl: well_founded refl_order.
Proof.
  unfold well_founded. intros. destruct a. constructor. intros. inv H.
Qed.

Lemma backward_refl:
  forall s,
    backward_simulation s s.
Proof.
  intros s. eapply Backward_simulation with (bsim_order:=refl_order) (bsim_match_states:=refl_match_states (state s)).
  - apply wf_refl.
  - intros s1 H. exists s1. auto.
  - intros s1 s2 H H0. exists tt. exists s2. split. auto. constructor.
  - intros i s1 s2 r H H0 H1. inv H. exists s2. split. apply star_refl. auto.
  - intros i s1 s2 H H0. inv H. unfold safe in H0. apply H0. apply star_refl.
  - intros s2 t s2' H i s1 H0 H1. inv H0. exists tt. exists s2'. split.
    left. apply plus_one. auto. constructor.
Qed.

Lemma backward_internal_refl:
  forall p rtl nc,
    backward_internal_simulation p p rtl rtl nc nc.
Proof.
  intros p rtl nc. eapply Backward_internal_simulation with (bsim_order:=refl_order) (bsim_match_states:=refl_match_states mixed_state).
  - apply wf_refl.
  - unfold call_refl, p_reflexive. intros s H. inv H. exists tt. constructor.
  - intros i s1 s2 r H H0 H1. exists s2. inv H. split. apply star_refl. auto.
  - intros i s1 s2 H H0. unfold safe in H0. apply H0. inv H. apply star_refl.
  - intros s2 t s2' H i s1 H0 H1. inv H0. exists tt. exists s2'. split.
    left. apply plus_one. auto. constructor.
Qed.





(** * Correctness of the optimizer step  *)
(* using the correctness of the 3 components: RTLblok generation, RTL flattening, and backend *)
Theorem optimizer_correct:
  forall p ms nc ms' nc' ps
    (OPT: exec (optimize ps p) naive_impl (ms, nc) = SOK tt (ms', nc')),
    backward_internal_simulation p p None None nc nc'.
Proof.
  intros p ms nc ms' nc' ps OPT. unfold optimize in OPT.
  repeat sdo_ok. destruct n0 as [mut cod]. apply n_check_same in HDO0 as SAME. inv SAME. destruct c.
  { inv OPT. apply backward_internal_refl. }
  destruct ((prog_funlist p) # (backend_suggestion ps)) eqn:INSTALLED; inv OPT.
  2: { apply backward_internal_refl. }
  unfold backend_and_install in H0.
  destruct (backend (current_version f) (backend_suggestion ps) (fn_params f)) eqn:BACKEND; inv H0.
  2: { apply backward_internal_refl. }
  unfold backend in BACKEND.
  destruct (IRtoRTLblock.rtlgen (backend_suggestion ps) (current_version f) (fn_params f)) as [[[block_code block_entry]block_idx]|] eqn:BLOCKGEN.
  2: { inv BACKEND. } unfold bind3, bind in BACKEND. simpl fst in BACKEND. simpl snd in BACKEND.
  destruct (flattenRTL.flatten ((backend_suggestion ps:positive), block_code, block_entry, block_idx)) eqn:FLATTEN.
  2: { inv BACKEND. }
  apply compose_backward_simulation with (p2:=p) (rtl2:=Some (inr (backend_suggestion ps, block_code, block_entry, block_idx))) (nc2:=cod).
  { apply single_mixed. }
  - eapply block_gen_correct; eauto. (* IRtoRTLblock is correct *)
    unfold n_check_compiled in HDO0. simpl in HDO0.
    destruct (cod # (backend_suggestion ps)); inv HDO0. auto.
  - apply compose_backward_simulation with (p2:=p) (rtl2:=Some (inl r)) (nc2:=cod).
    { apply single_mixed. }
    + apply flatten_correct; auto.    (* flattening RTLblock is correct *)
      intros H. inv H. unfold n_check_compiled in HDO0. simpl in HDO0. rewrite NAT_RTL in HDO0. inv HDO0.
    + replace cod with (snd (mut, cod)) by auto.
      destruct r as [[[fid rtlcode] rtlentry] rtlidx].
      apply same_id in FLATTEN as SAME. simpl in SAME. inv SAME.
      eapply backend_pass_correct; eauto. (* backend is correct *)
      { apply flatten_wf in FLATTEN. auto. }
      simpl. unfold n_install_code. eauto.
Qed.
