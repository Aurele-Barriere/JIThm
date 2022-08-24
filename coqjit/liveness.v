(* Liveness Analysis *)

(** Liveness analysis on SpecIR *)
(* Inspired by CompCert analysis over RTL *)

Require Import Coqlib.
Require Import Maps.
Require Import Kildall.
Require Import Lattice.
Require Import IR.
Require Import IRinterpreter.
Require Import Ordered.
Require Import Coq.MSets.MSetPositive.
Require Import common.
Require Import Errors.
Require Import RTL.

(** A register [r] is live at a point [p] if there exists a path
  from [p] to some instruction that uses [r] as argument,
  and [r] is not redefined along this path.
  Liveness can be computed by a backward dataflow analysis.
  The analysis operates over sets of (live) pseudo-registers. *)

(* Basic definitions over register sets *)
Definition regset: Type := PositiveSet.t.
Lemma regset_eq_refl: forall x, PositiveSet.eq x x.
Proof. apply PositiveSet.eq_equiv. Qed.
Lemma regset_eq_sym: forall x y, PositiveSet.eq x y -> PositiveSet.eq y x.
Proof. apply PositiveSet.eq_equiv. Qed.
Lemma regset_eq_trans: forall x y z, PositiveSet.eq x y -> PositiveSet.eq y z -> PositiveSet.eq x z.
Proof. apply PositiveSet.eq_equiv. Qed.

(* Definition of the lattice used to compute liveness *)
Module LiveFlatRegset <: SEMILATTICE.

Definition t : Type := regset.

Definition eq (x y: t) : Prop :=
  PositiveSet.Equal x y.

Lemma eq_refl: forall x, eq x x.
Proof. apply regset_eq_refl. Qed.

Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof. apply regset_eq_sym. Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof. apply regset_eq_trans. Qed.

Definition beq (x y: t) : bool := PositiveSet.equal x y.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof.
  unfold eq. intros. apply PositiveSet.equal_spec. auto.
Qed.

Definition ge (x y: t) : Prop :=
  PositiveSet.Subset y x.

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof.
  unfold eq, ge. intros x y EQ r IN. apply EQ. auto. 
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge. intros x y z Hxy Hyz r IN. auto. 
Qed.

Definition bot: t := PositiveSet.empty.

Lemma ge_bot: forall x, ge x bot.
Proof.
  unfold ge. intros x r IN. inv IN.
Qed.

Definition lub (x y: t) : t :=
  PositiveSet.union x y.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof.
  intros x y r IN. apply PositiveSet.union_spec. left. auto.
Qed.

Lemma ge_lub_right: forall x y, ge (lub x y) y.
Proof.
  intros x y r IN. apply PositiveSet.union_spec. right. auto.
Qed.

End LiveFlatRegset.

Definition live_abs_dr: Type := regset.

(* Starting the analysis, no registers are live *)
Definition live_entry_abs_dr: live_abs_dr :=
  PositiveSet.empty.

(* Associating a live_abs_dr to each label *)
Definition live_abs_state : Type := PMap.t live_abs_dr.
Definition live_absstate_get (pc:label) (abs:live_abs_state) : live_abs_dr :=
  PMap.get pc abs.

(* Inserting a new live register into an abstract set *)
Definition reg_live (r:reg) (adr:live_abs_dr) : live_abs_dr :=
  PositiveSet.add r adr.

(* Removing a new live register from an abstract set *)
Definition reg_dead (r:reg) (adr:live_abs_dr) : live_abs_dr :=
  PositiveSet.remove r adr.

(* Inserting a list of live registers *)
Fixpoint reg_list_live
             (rl: list reg) (lv: live_abs_dr) : live_abs_dr :=
  match rl with
  | nil => lv
  | r1 :: rs => reg_list_live rs (reg_live r1 lv)
  end.

(* Removing a list of live registers *)
Fixpoint reg_list_dead
             (rl: list reg) (lv: live_abs_dr) : live_abs_dr :=
  match rl with
  | nil => lv
  | r1 :: rs => reg_list_dead rs (reg_dead r1 lv)
  end.

(* Various operations on regsets, used in transfer function *)
Definition expr_live (expr: expr) (after: live_abs_dr): live_abs_dr :=
  match expr with
  | ZAR _ => after
  | UNA _ r => reg_live r after
  | BIN _ r1 r2 => reg_live r1 (reg_live r2 after)
  end.

Fixpoint expr_list_live (exl: list expr) (after: live_abs_dr): live_abs_dr :=
  match exl with
  | nil => after
  | e::t => expr_live e (expr_list_live t after)
  end.

Fixpoint varmap_live (vm: varmap) (after: live_abs_dr): live_abs_dr :=
  match vm with
  | nil => after
  | (r,e)::t => expr_live e (varmap_live t after)
  end.

(** Here is the transfer function for the dataflow analysis.
  Since this is a backward dataflow analysis, it takes as argument
  the abstract register set ``after'' the given instruction,
  i.e. the registers that are live after; and it returns as result
  the abstract register set ``before'' the given instruction,
  i.e. the registers that must be live before.
  The general relation between ``live before'' and ``live after''
  an instruction is that a register is live before if either
  it is one of the arguments of the instruction, or it is not the result
  of the instruction and it is live after. *)
(* The transf function that updates live_abs_dr *)
Definition live_dr_transf
            (c: IR.code) (pc: positive) (after: live_abs_dr) : live_abs_dr :=
  match c!pc with
  | None =>
    PositiveSet.empty
  | Some i =>
    match i with
    | Nop next => after
    | IPrint r next => reg_live r after
    | MemSet adreg valreg next =>
      reg_live adreg (reg_live valreg after)
    | MemGet dstreg adreg next =>
      reg_live adreg (reg_dead dstreg after)
    | Call f args retreg next =>
      reg_list_live args (reg_dead retreg after)
    | Cond r tr fl => reg_live r after
    | Return r =>
      reg_live r after
    | Op r ex next =>
      expr_live ex (reg_dead r after)
    | Assume r tgt vm next =>
      reg_live r (varmap_live vm after)
    end
  end.
      
(** The liveness analysis is then obtained by instantiating the
  general framework for backward dataflow analysis provided by
  module [Kildall].  *)
Module DS := Backward_Dataflow_Solver (LiveFlatRegset) (NodeSetBackward).

Definition list_entries (f: version) : list (label * live_abs_dr) :=
  ((ver_entry f), PositiveSet.empty)::nil.

Definition liveness_analyze (f: version): option live_abs_state :=
  DS.fixpoint (ver_code f) (IR.successors) (live_dr_transf (ver_code f)).

(** Basic property of the liveness information computed by [analyze]. *)
Lemma liveness_successor:
  forall f live n i s,
  liveness_analyze f = Some live ->
  (ver_code f)!n = Some i ->
  In s (successors i) ->
  PositiveSet.Subset (live_dr_transf (ver_code f) s (live_absstate_get s live)) (live_absstate_get n live).
Proof.
  unfold liveness_analyze. intros. eapply DS.fixpoint_solution; eauto.
  intros n0 a H2. unfold live_dr_transf. rewrite H2. unfold DS.L.bot.
  apply DS.L.eq_refl.
Qed.

(* Basic inclusions of regsets *)
Lemma reg_live_subset:
  forall r live, PositiveSet.Subset live (reg_live r live).
Proof.
  unfold PositiveSet.Subset. unfold reg_live. intros.
  apply PositiveSet.add_spec. right. auto.
Qed.

Lemma expr_live_subset:
  forall e rs, PositiveSet.Subset rs (expr_live e rs).
Proof.
  unfold PositiveSet.Subset. unfold expr_live. intros.
  destruct e;
    repeat (apply PositiveSet.add_spec; right); auto.
Qed.

Lemma reg_list_live_subset:
  forall rl rs, PositiveSet.Subset rs (reg_list_live rl rs).
Proof.
  unfold PositiveSet.Subset. induction rl; intros; auto.
  simpl. apply IHrl. apply reg_live_subset. auto.
Qed.

Lemma expr_list_live_subset:
  forall exl rs, PositiveSet.Subset rs (expr_list_live exl rs).
Proof.
  unfold PositiveSet.Subset. induction exl; intros; auto.
  simpl. apply expr_live_subset. auto.
Qed.

Lemma varmap_subset:
  forall v rs, PositiveSet.Subset rs (varmap_live v rs).
Proof.
  unfold PositiveSet.Subset. intros v rs. induction v; intros; auto. destruct a.
  simpl. apply expr_live_subset. apply IHv. auto.
Qed.


Lemma in_or_not:
  forall (l:label) l_fs,
    In l l_fs \/ ~ In l l_fs.
Proof.
  intros l l_fs. induction l_fs.
  - right. unfold not; intros. inv H.
  - poseq_destr a l.
    + left. simpl. left. auto.
    + destruct IHl_fs; [left | right]; simpl; try (right; auto).
      unfold not. intros [EQ | IN]; auto. 
Qed.

