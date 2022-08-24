(* Semantics and Properties of the monads *)
Require Import Events.
Require Import customSmallstep.
Require Import Integers.

Require Import common.
Require Import monad.
Require Import monad_impl.
Require Import ASMinterpreter.
Require Import jit.


(** * Loop Semantics (deprecated)  *)
(* building the semantics of a monad designed to be looped *)
Inductive loop_step {mstate prog_state:Type} (prog:prog_state -> free (prog_state * trace)) (i:monad_impl mstate) :
  unit -> (prog_state * mstate) -> trace -> (prog_state * mstate) -> Prop :=
| loop:
    forall ps1 ps2 t ms1 ms2
      (EXEC_STEP: (exec (prog ps1)) i ms1 = SOK (ps2, t) ms2),
      loop_step prog i tt (ps1, ms1) t (ps2, ms2).

(* Extending the notion of initial state, from a prog_state definition, to a full state (with monad state) *)
Inductive extend_init {mstate prog_state:Type} (init:prog_state -> Prop) (i:monad_impl mstate) :
  (prog_state * mstate) -> Prop :=
| init_extend:
    forall ps
      (INIT: init ps),
      extend_init init i (ps, init_state i).

(* extending to any monad state *)
Inductive extend_final {mstate prog_state:Type} (final:prog_state -> int -> Prop) (i:monad_impl mstate):
  (prog_state * mstate) -> int -> Prop :=
| final_extend:
    forall ps val ms
      (FINAL: final ps val),
      extend_final final i (ps, ms) val.

(* Loop Semantics given an implem *)
(* prog has the type that the jit_step would be typed with *)
Definition loop_sem {mstate prog_state:Type} (prog:prog_state -> free (prog_state * trace)) (i:monad_impl mstate) (init:prog_state -> Prop) (final:prog_state -> int -> Prop): semantics :=
  Semantics_gen (loop_step prog i) (extend_init init i) (extend_final final i) tt.

(* Forward sim proof *)
Inductive f_match {istate jstate prog_state:Type} (i:monad_impl istate) (j:monad_impl jstate) (R:refines i j): unit -> (prog_state * istate) -> (prog_state * jstate) -> Prop :=
| f_m : forall ps mi mj
          (MATCH: (match_states i j R) mi mj),
    f_match i j R tt (ps, mi) (ps, mj).

Inductive order : unit -> unit -> Prop := .
Lemma wfounded:
  well_founded order.
Proof.
  unfold well_founded. intros. destruct a. constructor. intros. inversion H.
Qed.

Lemma forward_prim:
  forall (A istate jstate R:Type) (i:monad_impl istate) (j:monad_impl jstate) a mi mi' mj
    (Ref: refines i j)
    (p: primitive R)
    (MATCH: match_states i j Ref mi mj)
    (EXEC: exec_prim p i mi = SOK a mi'),
  exists mj', exec_prim p j mj = SOK a mj' /\
         (match_states i j Ref) mi' mj'.
Proof.
  intros A istate jstate R i j a mi mi' mj Ref p MATCH EXEC.
  destruct p; inv EXEC.
  - rename H0 into Hsave. destruct a. (* save *)
    eapply (match_save i j Ref) in Hsave; eauto.
  - rename H0 into Hload. destruct a.       (* load *)
    eapply (match_load i j Ref) in Hload; eauto.
  - rename H0 into Hpusharg. destruct a. (* pusharg *)
    eapply (match_memset i j Ref) in Hpusharg; eauto.
  - rename H0 into Hpoparg. destruct a. (* poparg *)
    eapply (match_memget i j Ref) in Hpoparg; eauto.
  - rename H0 into Hclosesf. destruct a. (* closesf *)
    eapply (match_closesf i j Ref) in Hclosesf; eauto.
  - rename H0 into Hopensf. (* opensf *)
    eapply (match_opensf i j Ref) in Hopensf; eauto.
  - rename H0 into Hpushirsf. destruct a. (* pushirsf *)
    eapply (match_pushirsf i j Ref) in Hpushirsf; eauto.
  - rename H0 into Hinstall_code. destruct a. (* install_code *)
    eapply (match_install_code i j Ref) in Hinstall_code; eauto.
  - rename H0 into Hload_code. destruct a. (* load_call_code *)
    eapply (match_load_code i j Ref) in Hload_code; eauto.
  - rename H0 into Hcheck_compiled.  (* check_compiled *)
    eapply (match_check_compiled i j Ref) in Hcheck_compiled; eauto.
Qed.

Lemma forward_diagram:
  forall {A istate jstate:Type} (i:monad_impl istate) (j:monad_impl jstate) a mi mi' mj
    (R: refines i j)
    (m: free A)
    (MATCH: (match_states i j R) mi mj)
    (EXEC: exec m i mi = SOK a mi'),
  exists mj', exec m j mj = SOK a mj' /\
         (match_states i j R) mi' mj'.
Proof.
  intros A istate jstate i j a mi mi' mj R m MATCH EXEC.
  generalize dependent mi. generalize dependent mi'. generalize dependent mj. generalize dependent a.
  induction m; intros; inversion EXEC; simpl; subst.
  - exists mj. split; auto.          (* ret *)
  - rename H1 into EXEC_CONT. repeat sdo_ok. simpl in EXEC.
    unfold sbind in EXEC. rewrite HDO in EXEC. rewrite EXEC_CONT in EXEC. inv EXEC.
    eapply forward_prim in HDO; eauto. destruct HDO as [j0 [EXEC_PRIM MATCH']].
    specialize (H r a j0 mi' i0 MATCH' EXEC_CONT).
    destruct H as [mj' [EXEC_CONT' MATCH'']].
    exists mj'. unfold sbind. rewrite EXEC_PRIM. split; auto.
Qed.

Theorem loop_refinement:
  forall (prog_state istate jstate:Type) (prog:prog_state -> free (prog_state * trace))  init final
    (i:monad_impl istate) (j:monad_impl jstate)
    (R: refines i j),
    forward_simulation
      (loop_sem prog i init final)
      (loop_sem prog j init final).
Proof.
  intros prog_state istate jstate prog init final i j R.
  eapply Forward_simulation.
  - apply wfounded.
  - intros s1 H. exists tt. simpl in H. inversion H.
    exists (ps, init_state j). split; simpl.
    + constructor. auto.
    + eapply (f_m i j R). apply (match_init i j R).
  - intros tt s1 s2 r H H0. simpl in s1, s2. destruct s1 as [ps1 mi1]. destruct s2 as [ps mi2].
    inversion H. subst. simpl. constructor. inversion H0. auto.
  - intros s1 t s1' H i0 s2 H0. simpl in s1, s1'. destruct s1 as [ps1 mi1]. destruct s1' as [ps1' mi1'].
    inversion H0. subst. exists tt. inversion H. subst.
    eapply forward_diagram in EXEC_STEP; eauto.
    destruct EXEC_STEP as [mj' [EXEC' MATCH']].
    exists (ps1', mj'). split; auto.
    + left. apply plus_one. constructor. auto.
    + constructor. auto.
Qed.


(** * Giving Semantics the Non-Atomic step of a NASM  *)
Record na_spec {state I R:Type}: Type :=
  mk_spec {
      load_: state -> free I;         
      step_: I -> free (trace * itret R I);
      ret_ : state -> R -> free state
    }.
(* I defines the type of intermediate states *)
(* R represents the return value type of the internal iteration *)


(** * Unfolded Semantics  *)
Inductive unf_state {S I:Type} :=
| EXT: S -> unf_state       (* when we're executing the main program *)
| INT: S -> I -> unf_state.       (* when we're executing the non-atomic loop. we remember the calling S state *)

  
Inductive unf_step {state mstate I R:Type} (prog: @nasm_prog state) (impl:monad_impl mstate) (spec: @na_spec state I R):
  unit -> (@unf_state state I * mstate) -> trace -> (@unf_state state I * mstate) -> Prop :=
| ext_step:
    forall (s1 s2:state) t ms1 ms2 symbmon
      (ATOMIC: prog s1 = Ato symbmon)
      (EXEC_STEP: exec symbmon impl ms1 = SOK (t, s2) ms2),
      unf_step prog impl spec tt (EXT s1, ms1) t (EXT s2, ms2)
| loop_start:
    forall s1 ms1 start ms2
      (RUN: prog s1 = LoadAndRun)
      (LOAD: exec (load_ spec s1) impl ms1 = SOK start ms2),
      unf_step prog impl spec tt (EXT s1, ms1) E0 (INT s1 start, ms2)
| int_step:
    forall i1 t i2 ms1 ms2 call_state
      (EXEC_STEP: exec (step_ spec i1) impl ms1 = SOK (t, Halt i2) ms2),
      unf_step prog impl spec tt (INT call_state i1, ms1) t (INT call_state i2, ms2)
| loop_end:
    forall i1 t r s2 ms1 ms2 ms3 call_state
      (EXEC_END: exec (step_ spec i1) impl ms1 = SOK (t, Done r) ms2)
      (EXEC_RET: exec (ret_ spec call_state r) impl ms2 = SOK (s2) ms3),
      unf_step prog impl spec tt (INT call_state i1, ms1) t (EXT s2, ms3).

(* Liftinf initial and final from state to unf_state *)
Inductive init_unf_state {state mstate I:Type} (init:state -> Prop) (impl:monad_impl mstate) : (@unf_state state I  * mstate) -> Prop :=
| init_unf: forall s
              (INIT: init s),
    init_unf_state init impl (EXT s, init_state impl).

Inductive final_unf_state {state mstate I:Type} (final:state -> int -> Prop) (impl:monad_impl mstate) : (@unf_state state I * mstate) -> int -> Prop :=
| final_unf: forall s ms r
               (FINAL: final s r),
    final_unf_state final impl (EXT s, ms) r.

Definition unf_sem {state mstate I R:Type} (prog: @nasm_prog state) (impl:monad_impl mstate) (spec: @na_spec state I R) (init:state->Prop) (final:state->int->Prop): semantics :=
  Semantics_gen (unf_step prog impl spec) (init_unf_state init impl) (final_unf_state final impl) tt.


(** * Refinement Simulation  *)
(* Forward sim proof *)

Theorem refinement:
  forall (state istate jstate I R:Type) (prog: @nasm_prog state) init final
    (i: monad_impl istate) (j:monad_impl jstate) (spec: @na_spec state I R) 
    (Ref: refines i j),
    forward_simulation
      (unf_sem prog i spec init final)
      (unf_sem prog j spec init final).
Proof.
  intros state istate jstate I R prog init final i j spec Ref.
  eapply Forward_simulation.
  - apply wfounded.
  - intros s1 H. exists tt. simpl in H. inversion H.
    exists (EXT s, init_state j). split; simpl.
    + constructor. auto.
    + eapply (f_m i j Ref). apply (match_init i j Ref).
  - intros tt s1 s2 r H H0. simpl in s1, s2. destruct s1 as [ps1 mi1]. destruct s2 as [ps mi2].
    inversion H. subst. simpl. inversion H0. subst. constructor. auto.
  - intros s1 t s1' STEP i0 s2 MATCH. simpl in s1, s1'. destruct s1 as [ps1 mi1]. destruct s1' as [ps1' mi1'].
    inversion MATCH. subst. exists tt. inversion STEP; subst.
    + eapply forward_diagram in EXEC_STEP; eauto.
      destruct EXEC_STEP as [mj' [EXEC' MATCH']].
      exists (EXT s2, mj'). split; auto.
      * left. apply plus_one. eapply ext_step; eauto.
      * constructor. auto.
    + eapply forward_diagram in LOAD; eauto.
      destruct LOAD as [mj' [EXEC' MATCH']].
      exists (INT s1 start, mj'). split; auto.
      * left. apply plus_one. eapply loop_start; eauto.
      * constructor. auto.
    + eapply forward_diagram in EXEC_STEP; eauto.
      destruct EXEC_STEP as [mj' [EXEC' MATCH']].
      exists (INT call_state i2, mj'). split; auto.
      * left. apply plus_one. eapply int_step; eauto.
      * constructor. auto.
    + eapply forward_diagram in EXEC_END; eauto.
      destruct EXEC_END as [mj' [EXEC' MATCH']].
      eapply forward_diagram in EXEC_RET; eauto.
      destruct EXEC_RET as [mj'' [EXEC'' MARCH'']].
      exists (EXT s2, mj''). split; auto.
      * left. apply plus_one. eapply loop_end; eauto.
      * constructor. auto.
Qed.


