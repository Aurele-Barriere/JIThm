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
  | r1 :: rs => reg_live r1 (reg_list_live rs lv)
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
    | IPrint e next => expr_live e after
    | MemSet adreg valreg next =>
      reg_live adreg (reg_live valreg after)
    | MemGet dstreg adreg next =>
      reg_live adreg (reg_dead dstreg after)
    | Call f args retreg next =>
      reg_list_live args (reg_dead retreg after)
    | Cond r tr fl => reg_live r after
    | Return e =>
      expr_live e after
    | Op r ex next =>
      expr_live ex (reg_dead r after)
    | Assume guard tgt vm next =>
        expr_live guard (varmap_live vm after)
    | Anchor tgt vm next =>
        varmap_live vm after
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
  simpl. apply reg_live_subset. apply IHrl. auto.
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



(** * AGREEEMENT  *)
(* This to relate regmaps with regsets *)
(* But IR_to_RTLBlock uses its own version of agreement *)

(* Two regmaps agree on a regset iff they have the same values
   on the registers of the regset (may be None) *)
Definition agree (rm1 rm2:reg_map) (adr:live_abs_dr) :=
  forall r:reg, PositiveSet.In r adr -> rm1 # r = rm2 # r.

Lemma agree_refl:
  forall rs rm,
    agree rm rm rs.
Proof.
  unfold agree. intros. auto.
Qed.

Lemma agree_sym:
  forall rs rm1 rm2,
    agree rm1 rm2 rs ->
    agree rm2 rm1 rs.
Proof.
  unfold agree. intros. symmetry. auto.
Qed.

Lemma agree_trans:
  forall rs rm1 rm2 rm3,
    agree rm1 rm2 rs ->
    agree rm2 rm3 rs ->
    agree rm1 rm3 rs.
Proof.
  unfold agree. intros. rewrite H; auto.
Qed.

Lemma agree_subset:
  forall rs1 rs2 rms rmo,
    PositiveSet.Subset rs1 rs2 ->
    agree rms rmo rs2 ->
    agree rms rmo rs1.
Proof.
  unfold agree. intros. auto.
Qed.

(* Liveness transfer preserves agree *)
Lemma agree_transfer:
  forall live rms rmo f pc pc' i,
    liveness_analyze f = Some live ->
    (ver_code f)!pc = Some i ->
    In pc' (successors i) ->
    agree rms rmo (live!!pc) ->
    agree rms rmo (live_dr_transf (ver_code f) pc' (live!!pc')).
Proof.
  intros. apply agree_subset with (live!!pc); auto.
  eapply liveness_successor; eauto.
Qed.

(* The following lemmas express the fact that agreeing on the regset obtained 
   after adding registers implies agreeing on the original regset 
   (which contains less registers) *)
Lemma expr_live_agree:
  forall e rs rms rmo,
    agree rms rmo (expr_live e rs) ->
    agree rms rmo rs.
Proof.
  intros. eapply agree_subset; eauto. apply expr_live_subset.
Qed.

Lemma expr_list_live_agree:
  forall exl rs rms rmo,
    agree rms rmo (expr_list_live exl rs) ->
    agree rms rmo rs.
Proof.
  intros. eapply agree_subset; eauto. apply expr_list_live_subset.
Qed.

(* Lemma movelist_live_agree: *)
(*   forall ml rs rms rmo, *)
(*     agree rms rmo (movelist_live ml rs) -> *)
(*     agree rms rmo rs. *)
(* Proof. *)
(*   intros. eapply agree_subset; eauto. apply movelist_subset. *)
(* Qed. *)

Lemma varmap_live_agree:
  forall vm rs rms rmo,
    agree rms rmo (varmap_live vm rs) ->
    agree rms rmo rs.
Proof.
  intros. eapply agree_subset; eauto. apply varmap_subset.
Qed.

(* Lemma synth_live_agree: *)
(*   forall sl rs rms rmo, *)
(*     agree rms rmo (synth_live sl rs) -> *)
(*     agree rms rmo rs. *)
(* Proof. *)
(*   intros. eapply agree_subset; eauto. apply synth_subset. *)
(* Qed. *)

Lemma agree_eval_reg:
  forall r v rs rms rmo ,
    agree rms rmo (reg_live r rs) ->
    eval_reg r rms = OK v ->
    eval_reg r rmo = OK v.
Proof.
  intros. unfold agree in H. unfold eval_reg in H0. rewrite H in H0.
    2: { simpl. apply PositiveSet.add_spec. left. auto. }
    unfold eval_reg. rewrite H0. simpl. auto.
Qed.


(* If two regmaps agree on the registers used for the evaluation of e, 
   then e evaluates to the same value in both regmaps *)
Lemma agree_eval_expr:
  forall e v rs rms rmo ,
    agree rms rmo (expr_live e rs) ->
    eval_expr e rms = OK v ->
    eval_expr e rmo = OK v.
Proof.
  intros. destruct e; simpl in H0.
  - destruct (eval_reg r rms) eqn:EVALL; inv H0.
    destruct (eval_reg r0 rms) eqn:EVALR; inv H2.
    unfold agree in H. unfold eval_reg in EVALL. rewrite H in EVALL.
    2: { simpl. apply PositiveSet.add_spec. left. auto. }
    unfold eval_reg in EVALR. rewrite H in EVALR.
    2: { simpl. apply PositiveSet.add_spec. right. apply PositiveSet.add_spec. auto. }
    simpl. unfold eval_reg. rewrite EVALL. rewrite EVALR. simpl. auto.
  - destruct (eval_reg r rms) eqn:EVAL; inv H0.
    unfold agree in H. unfold eval_reg in EVAL. rewrite H in EVAL.
    2: { simpl. apply PositiveSet.add_spec. left. auto. }
    simpl. unfold eval_reg. rewrite EVAL. simpl. auto.
  - destruct z. inv H0. simpl. auto.
Qed.

(* If two regmaps agree on the registers used for the evaluation of 
   the list of expressions [le], then [le] evaluates to the same boolean value
   in both regmaps *)
(* Lemma agree_eval_list_expr: *)
(*   forall rs rm1 rm2 le b, *)
(*     agree rm1 rm2 (expr_list_live le rs) -> *)
(*     eval_list_expr le rm1 b -> *)
(*     eval_list_expr le rm2 b. *)
(* Proof. *)
(*   intros. generalize dependent b. induction le; intros; inv H0; try constructor. *)
(*   - eapply agree_eval_expr in EVAL; eauto. *)
(*   - eapply agree_eval_expr in EVALH; eauto. *)
(*     econstructor; eauto. apply IHle; auto. *)
(*     unfold agree in *. intros. apply H. simpl. *)
(*     eapply expr_live_subset; eauto. *)
(* Qed. *)

(* If two regmaps agree on the registers used for the evaluation of 
   the list of expressions [le], then each expression of [le] evaluates to the same value
   in both regmaps *)
Lemma agree_eval_list:
  forall rs rm1 rm2 le lv,
    agree rm1 rm2 (expr_list_live le rs) ->
    eval_list le rm1 = OK lv ->
    eval_list le rm2 = OK lv.
Proof.
  intros. generalize dependent lv.
  induction le; intros.
  - inv H0. simpl. auto.
  - simpl in H0. destruct (eval_expr a rm1) eqn:EVAL1; inv H0.
    eapply agree_eval_expr in EVAL1; eauto.
    destruct (eval_list le rm1) eqn:EVAL2; inv H2.
    simpl. rewrite EVAL1. simpl.
    assert (OK l = OK l) by auto. apply IHle in H0.
    2: { eapply agree_subset; eauto. apply expr_live_subset. }
    rewrite H0. simpl. auto.
Qed.

Lemma agree_eval_list_reg:
  forall rs rm1 rm2 le lv,
    agree rm1 rm2 (reg_list_live le rs) ->
    eval_list_reg le rm1 = OK lv ->
    eval_list_reg le rm2 = OK lv.
Proof.
  intros. generalize dependent lv.
  induction le; intros.
  - inv H0. simpl. auto.
  - simpl in H0. destruct (eval_reg a rm1) eqn:EVAL1; inv H0.
    eapply agree_eval_reg in EVAL1; eauto.
    destruct (eval_list_reg le rm1) eqn:EVAL2; inv H2.
    simpl. rewrite EVAL1. simpl.
    assert (OK l = OK l) by auto. apply IHle in H0.
    2: { eapply agree_subset; eauto. simpl.
         apply reg_live_subset. }
    rewrite H0. simpl. auto.
Qed.


(* Auxiliary lemmas on movelists *)
(* If a register is not assigned by a movelist, it contains the same value 
   before and after the update *)
(* Lemma not_use_movelist: *)
(*   forall ml r rm rmu, *)
(*     ~(In r (map fst ml)) -> *)
(*     update_movelist ml rm rmu -> *)
(*     rm ! r = rmu ! r. *)
(* Proof. *)
(*   induction ml; intros. *)
(*   - inv H0. auto. *)
(*   - inv H0. poseq_destr r r0. *)
(*     + simpl in H. unfold not in H. *)
(*       exfalso. apply H. left. auto.  *)
(*     + rewrite PTree.gso; auto. simpl in H. *)
(*       eapply Classical_Prop.not_or_and in H as [NEQ NIN]. apply IHml; auto. *)
(* Qed. *)

(* If a register is assigned by a movelist and two regmaps agree on all the
   registers whose value is needed to evaluate all the expressions of
   the movelist, then we can decompose the movelist appropriately *)
(* Lemma reg_in_movelist: *)
(*   forall ml r rs rm1 rm2, *)
(*     agree rm1 rm2 (movelist_live ml rs) -> *)
(*     In r (map fst ml) -> *)
(*     exists ml1 ml2 e rs', *)
(*       ml = ml1 ++ (r,e)::ml2 /\ ~(In r (map fst ml1)) /\ *)
(*       agree rm1 rm2 (expr_live e rs'). *)
(* Proof. *)
(*   induction ml; intros; inv H0. *)
(*   - simpl in H. destruct a. exists nil, ml, e, (movelist_live ml rs). *)
(*     split; auto. *)
(*   - simpl in H. destruct a. *)
(*     apply IHml with r rs rm1 rm2 in H1 as [ml1 [ml2 [e' [rs' [EQ [NIN AGREE]]]]]]. *)
(*     2: { eapply expr_live_agree. eauto. } *)
(*     poseq_destr r r0. *)
(*     + exists nil, (ml1 ++ (r0,e')::ml2), e, (movelist_live (ml1 ++ (r0, e') :: ml2) rs). *)
(*       split; auto. *)
(*     + exists ((r0,e)::ml1), ml2, e', rs'. subst. *)
(*       split; auto; try split; auto. *)
(*       simpl. intros [EQ' | IN]; subst; auto. *)
(* Qed. *)

(* If we assign a register [r] with a movelist, and two regmaps agree on the 
   registers used by the expression assigned to [r], then they agree on [r]
   after the update no matter what was the value before *)
(* Lemma use_movelist: *)
(*   forall ml1 ml2 ml r e rs rm1 rm1u rm2 rm2u, *)
(*     ml = ml1 ++ (r,e)::ml2 -> *)
(*     ~(In r (map fst ml1)) -> *)
(*     agree rm1 rm2 (expr_live e rs) -> *)
(*     update_movelist ml rm1 rm1u -> *)
(*     update_movelist ml rm2 rm2u -> *)
(*     rm1u ! r = rm2u ! r. *)
(* Proof. *)
(*   induction ml1. *)
(*   - intros. inv H2; inv H4. *)
(*     inv H3. rewrite PTree.gss. rewrite PTree.gss. f_equal. *)
(*     eapply agree_eval_expr in EVAL; eauto. *)
(*     eapply eval_expr_determ; eauto. *)
(*   - intros. inv H2; inv H4. *)
(*     inv H3. assert (r <> r0). *)
(*     { intros contra. apply H0. simpl. left. auto. } *)
(*     rewrite PTree.gso; auto. rewrite PTree.gso; auto. *)
(*     eapply IHml1; eauto. intros contra. simpl in H0. *)
(*     apply H0. right. auto. *)
(* Qed. *)

(* Two agreeing regmaps still agree after having the same update *)
(* Lemma agree_update_movelist_aux: *)
(*   forall ml rs rm1 rm2 rm1u rm2u, *)
(*     agree rm1 rm2 (movelist_live ml rs) -> *)
(*     update_movelist ml rm1 rm1u -> *)
(*     update_movelist ml rm2 rm2u -> *)
(*     agree rm1u rm2u (movelist_live ml rs). *)
(* Proof. *)
(*   induction ml; intros; inv H0; inv H1; auto. *)
(*   unfold agree. intros. *)
(*   simpl in H0. simpl in H. poseq_destr r r0. *)
(*   - repeat rewrite PTree.gss. f_equal. *)
(*     eapply agree_eval_expr in EVAL; eauto. *)
(*     eapply eval_expr_determ; eauto. *)
(*   - repeat (rewrite PTree.gso; auto). *)
(*     assert (In r0 (map fst ml) \/ ~(In r0 (map fst ml))) as [IN' | NIN'] by (apply in_or_not). *)
(*     + eapply reg_in_movelist in IN' as [ml1 [ml2 [e' [rs' [EQ [NIN'' AGREE]]]]]]; eauto. *)
(*       * eapply use_movelist; eauto. *)
(*       * eapply expr_live_agree; eauto. *)
(*     + assert (rm1 ! r0 = rm' ! r0). *)
(*       { eapply not_use_movelist; eauto. } *)
(*       assert (rm2 ! r0 = rm'0 ! r0). *)
(*       { eapply not_use_movelist; eauto. } *)
(*       rewrite <- H1. rewrite <- H2. apply H. apply H0. *)
(* Qed. *)

(* Lemma agree_update_movelist: *)
(*   forall rs rm1 rm2 rm2u ml, *)
(*     agree rm1 rm2 (movelist_live ml rs) -> *)
(*     update_movelist ml rm2 rm2u -> *)
(*     exists rm1u, *)
(*       update_movelist ml rm1 rm1u /\ *)
(*       agree rm1u rm2u (movelist_live ml rs). *)
(* Proof. *)
(*   intros. generalize dependent rm2u. induction ml; intros; inv H0. *)
(*   - exists rm1. split; auto. constructor. *)
(*   - assert (UPDATE':= UPDATE). apply IHml in UPDATE as [rm1u [UPDATE EQ]]. *)
(*     2: { unfold agree in *. intros. apply H. simpl. *)
(*          apply expr_live_subset. auto. } *)
(*     apply agree_sym in H. *)
(*     assert (EVAL':=EVAL). *)
(*     eapply agree_eval_expr in EVAL; eauto. *)
(*     exists (rm1u#r<-v). split; try constructor; eauto. *)
(*     apply agree_sym. eapply agree_update_movelist_aux; eauto; econstructor; eauto. *)
(* Qed. *)

Lemma agree_update_regmap:
  forall rs rm1 rm2 newrm vm,
    agree rm1 rm2 (varmap_live vm rs) ->
    update_regmap vm rm2 = OK newrm ->
    update_regmap vm rm1 = OK newrm.
Proof.
  intros. generalize dependent newrm.
  induction vm; intros; inv H0; auto.
  destruct a. destruct (eval_expr e rm2) eqn:EVAL1; inv H2.
  apply agree_sym in H. eapply agree_eval_expr in EVAL1; eauto.
  simpl. rewrite EVAL1. simpl.
  destruct (update_regmap vm rm2) eqn:EVAL2; inv H1.
  assert (OK r0 = OK r0) by auto. apply IHvm in H0.
  rewrite H0. auto.
  eapply expr_live_agree. apply agree_sym in H. simpl in H. eauto.
Qed.

(* Lemma agree_synthesize_frame: *)
(*   forall rs rm1 rm2 p sl stack, *)
(*     agree rm1 rm2 (synth_live sl rs) -> *)
(*     synthesize_frame p rm2 sl stack -> *)
(*     synthesize_frame p rm1 sl stack. *)
(* Proof. *)
(*   intros. generalize dependent stack. *)
(*   induction sl; intros; inv H0; try constructor; auto. *)
(*   - eapply agree_update_regmap in UPDATE; eauto. *)
(*   - apply IHsl; auto. simpl in H. *)
(*     eapply varmap_live_agree. eauto. *)
(* Qed. *)

(* It is sufficient to agree on all the registers of [rs] excepted [reg]
   before an assignation provided we assign the same value to [reg]
   on both sides *)
Lemma agree_insert_dead:
  forall rs rm rm_opt reg v,
    agree rm rm_opt (reg_dead reg rs) ->
    agree (rm # reg <- v) (rm_opt # reg <- v) rs.
Proof.
  intros. unfold agree in *.
  intros r IN. poseq_destr r reg.
  - rewrite PTree.gss. rewrite PTree.gss. auto.
  - rewrite PTree.gso; auto. rewrite PTree.gso; auto. apply H.
    apply PositiveSet.remove_spec; split; auto.
Qed.

(* updating the rm on both sides *)
Lemma agree_insert:
  forall rs rm rm_opt reg v,
    agree rm rm_opt rs ->
    agree (rm # reg <- v) (rm_opt # reg <- v) rs.
Proof.
  intros. apply agree_subset with (reg_dead reg rs) rs rm rm_opt in H.
  - apply agree_insert_dead. auto.
  - intros r IN. apply PositiveSet.remove_spec in IN as [IN _]. auto.
Qed.

(* Lemma agree_movelist_live: *)
(*   forall ml rs rs' rms rmo, *)
(*     agree rms rmo (movelist_live ml rs) -> *)
(*     agree rms rmo rs -> *)
(*     agree rms rmo rs' -> *)
(*     agree rms rmo (movelist_live ml rs'). *)
(* Proof. *)
(*   induction ml; intros; auto. *)
(*   simpl. destruct a. simpl in H. intros r' IN. *)
(*   destruct e; destruct o; try destruct o0; simpl in *; *)
(*     try (apply (IHml rs rs' rms rmo); assumption); poseq_destr r' r0; *)
(*       try (apply H; apply PositiveSet.add_spec; left; reflexivity). *)
(*   - poseq_destr r' r1. *)
(*     + apply H. apply PositiveSet.add_spec. right. *)
(*       apply PositiveSet.add_spec. left. auto. *)
(*     + apply (IHml rs rs' rms rmo); auto. *)
(*       * eapply agree_subset; try apply H. *)
(*         intros reg IN'. repeat (apply PositiveSet.add_spec; right; auto). *)
(*       * repeat (apply PositiveSet.add_spec in IN as [contra | IN]; auto; *)
(*                 try contradiction). *)
(*   - apply (IHml rs rs' rms rmo); auto. *)
(*     + eapply agree_subset; try apply H. *)
(*       intros reg IN'. apply PositiveSet.add_spec. right. auto. *)
(*     + apply PositiveSet.add_spec in IN as [contra | IN]; auto. contradiction. *)
(*   - apply (IHml rs rs' rms rmo); auto. *)
(*     + eapply agree_subset; try apply H. *)
(*       intros reg IN'. apply PositiveSet.add_spec. right. auto. *)
(*     + apply PositiveSet.add_spec in IN as [contra | IN]; auto. contradiction. *)
(*   - apply (IHml rs rs' rms rmo); auto. *)
(*     + eapply agree_subset; try apply H. *)
(*       intros reg IN'. apply PositiveSet.add_spec. right. auto. *)
(*     + apply PositiveSet.add_spec in IN as [contra | IN]; auto. contradiction. *)
(* Qed. *)

(* Lemma movelist_reg_dead_subset: *)
(*   forall ml r rs, *)
(*     PositiveSet.Subset (movelist_dead ml (reg_dead r rs)) (reg_dead r (movelist_dead ml rs)). *)
(* Proof. *)
(*   induction ml; intros. *)
(*   - simpl. intros r' IN. auto. *)
(*   - simpl. destruct a. intros r' IN. poseq_destr r' r0. *)
(*     + apply PositiveSet.remove_spec in IN as [_ contra]. destruct contra. auto. *)
(*     + poseq_destr r' r. *)
(*       * apply PositiveSet.remove_spec in IN as [IN _]. apply IHml in IN. *)
(*         apply PositiveSet.remove_spec in IN as [_ contra]. destruct contra. auto. *)
(*       * repeat (apply PositiveSet.remove_spec; split; auto). *)
(*         apply PositiveSet.remove_spec in IN as [IN _]. apply IHml in IN. *)
(*         apply PositiveSet.remove_spec in IN as [IN _]. auto. *)
(* Qed. *)

(* (* Before an update_movelist, it is sufficient to agree on all the registers *)
(*    of [rs] excepted the registers assigned by the movelist *) *)
(* Lemma agree_movelist_dead: *)
(*   forall ml rs rms rmsu rmo rmou, *)
(*     agree rms rmo (movelist_live ml (movelist_dead ml rs)) -> *)
(*     update_movelist ml rms rmsu -> *)
(*     update_movelist ml rmo rmou -> *)
(*     agree rmsu rmou rs. *)
(* Proof. *)
(*   induction ml; intros; inv H0; inv H1; simpl in H; auto. *)
(*   simpl in H. eapply agree_eval_expr in EVAL; eauto. *)
(*   eapply eval_expr_determ in EVAL0; eauto. *)
(*   inv EVAL0. apply agree_insert_dead. *)
(*   eapply IHml; eauto. *)
(*   apply agree_subset with *)
(*       (movelist_live ml (reg_dead r (movelist_dead ml rs))) *)
(*       (expr_live e (movelist_live ml (reg_dead r (movelist_dead ml rs)))) *)
(*       rms rmo in H; try apply expr_live_subset. *)
(*   eapply agree_movelist_live; eauto. *)
(*   + eapply movelist_live_agree. eauto. *)
(*   + eapply agree_subset. apply movelist_reg_dead_subset. *)
(*     eapply movelist_live_agree. eauto. *)
(* Qed. *)

