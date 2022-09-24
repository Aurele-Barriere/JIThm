(* Verification of the Anchor Insertion pass *)
(* The first pass of the dynamic optimizer *)

Require Import IR.
Require Import IRinterpreter.
Require Import anchor_insertion.
Require Import sem_properties.
Require Import internal_simulations.
Require Import customSmallstep.
Require Import Coq.MSets.MSetPositive.
Require Import Lists.SetoidList.
Require Import def_regs.
Require Import IRtoRTLblock_proof.
Require Import liveness.
Require Import monad.
Require Import monad_impl.
Require Import Errors.
Require Import common.
Require Import mixed_sem.
Require Import assume_insertion_proof.


Lemma Inl_In:
  forall r l, PositiveSet.InL r l <-> In r l.
Proof.
  intros. induction l.
  - split; intros. inv H. inv H.
  - split; intros.
    + inv H.
      * unfold PositiveSet.E.eq in H1. subst. simpl. left. auto.
      * apply IHl in H1. simpl. right. auto.
    + inv H.
      * constructor. unfold PositiveSet.E.eq. auto.
      * apply InA_cons_tl. apply IHl. auto.
Qed.

Lemma PSin_in:
  forall r rs,
    PositiveSet.In r rs <-> In r (PositiveSet.elements rs).
Proof.
  intros. rewrite <- PositiveSet.elements_spec1.
  apply Inl_In.
Qed.

Lemma nodup_elements:
  forall rs, NoDup (PositiveSet.elements rs).
Proof.
  assert (forall l, NoDupA PositiveSet.E.eq l <-> NoDup l).
  { intros. induction l.
    - split; intros. constructor. constructor.
    - split; intros.
      + inv H. constructor.
        * unfold not. intros. rewrite <- Inl_In in H. auto.
        * apply IHl. auto.
      + inv H. constructor.
        * unfold not. intros. rewrite Inl_In in H. auto.
        * apply IHl. auto. }
  intros. apply H. apply PositiveSet.elements_spec2w.
Qed.

Lemma defined_ind:
  forall a l rm,
    NoDup (a::l) ->
    (forall r : positive, In r (a :: l) -> (exists v : Integers.Int.int, rm ! r = Some v)) ->
    (forall r : positive, In r l -> (exists v, (PTree.remove a rm)!r = Some v)).
Proof.
  intros. assert (In r (a::l)) by (right; auto). apply H0 in H2 as [v SOME].
  exists v. rewrite PTree.gro. auto. inv H. poseq_destr r a; auto.
Qed.

Lemma eval_remove:
  forall r1 r2 rm i,
    eval_reg r1 (PTree.remove r2 rm) = OK i ->
    r1 <> r2 ->
    eval_reg r1 rm = OK i.
Proof.
  intros r1 r2 rm i H H0. unfold eval_reg in *.
  rewrite PTree.gro in H; auto.
Qed.

Lemma update_more:
  forall rm newrm l a,
    ~ In a l ->
    update_regmap (map (fun r : reg => (r, UNA (uplus Integers.Int.zero) r)) l) (PTree.remove a rm) = OK newrm ->
    update_regmap (map (fun r : reg => (r, UNA (uplus Integers.Int.zero) r)) l) rm = OK newrm.
Proof.
  intros. generalize dependent rm. generalize dependent newrm. induction l; intros.
  - inv H0. auto.
  - inv H0. poseq_destr a a0.
    + simpl in H. exfalso. apply H. left. auto.
    + assert (~ In a l).
      { unfold not. intros. apply H. simpl. right. auto. }
      specialize (IHl H0). simpl. repeat ok_do.
      unfold bind in H2. destruct (eval_reg a0 (PTree.remove a rm)) eqn:EVAL; inv H2.
      destruct (update_regmap (map (fun r : reg => (r, UNA (uplus Integers.Int.zero) r)) l) (PTree.remove a rm)) eqn:EVAL0; inv H3.
      apply IHl in EVAL0. rewrite EVAL0. apply eval_remove in EVAL; auto. rewrite EVAL.
      simpl. auto.
Qed.

(* rs is a subset of the set obtained by adding successively all its elements
   (actually both are the same set) *)
Lemma fold_elements:
  forall r rs,
    PositiveSet.In r rs -> PositiveSet.In r (fold_right PositiveSet.add PositiveSet.empty (PositiveSet.elements rs)).
Proof.
  intros r rs. rewrite PSin_in.
  induction (PositiveSet.elements rs).
  - intros. inv H.
  - simpl. intros. destruct H.
    + apply PositiveSet.add_spec. left. auto.
    + apply IHl in H. apply PositiveSet.add_spec. right. auto.
Qed.

(* If the regmap in the optimized version is defined on rs, the regmap obtained after 
   deoptimizing using the identity varmap on [rs'] a subset of [rs]
   agrees with the old regmap on rs'. *)
Theorem defined_deopt_subset_agree:
  forall rm rs rs' ,
    defined rm (DefFlatRegset.Inj rs) ->
    PositiveSet.Subset rs' rs ->
    exists rmdeopt,
      update_regmap (identity_varmap rs') rm = OK rmdeopt /\
      agree rm rmdeopt rs'.
Proof.
  assert (forall l, NoDup l ->
                    forall rm,
                      (forall r, In r l -> exists v, rm!r = Some v) ->
                      exists rmdeopt,
                        update_regmap (map (fun r : reg => (r, UNA (uplus Integers.Int.zero) r)) l) rm = OK rmdeopt /\
                        agree rm rmdeopt (fold_right PositiveSet.add PositiveSet.empty l)).
  { intros l NODUP. induction l; intros.
    - simpl in H. simpl. exists empty_regmap. split. constructor.
      intros r IN. inv IN.
    - specialize (defined_ind a l rm NODUP H). intros H1.
      apply IHl in H1.
      2: { apply NoDup_cons_iff in NODUP. destruct NODUP. auto. }
      destruct H1 as [rmdeopt [UPDATE AGREE]].
      assert (GETA: exists va, rm ! a = Some va).
      { apply H. simpl. left. auto. }
      destruct GETA as [va GETA].
      exists (rmdeopt # a <- va). split.
      + simpl. unfold eval_reg. rewrite GETA. simpl. apply update_more in UPDATE.
        2: { unfold not; intros IN. inv NODUP. apply H2; auto. }
        rewrite UPDATE. simpl. rewrite Integers.Int.add_zero. auto.
      + unfold agree. intros r. specialize (AGREE r). poseq_destr r a.
        * rewrite PTree.gss. auto.
        * intros. rewrite PTree.gro in AGREE; auto. rewrite PTree.gso; auto.
          apply PositiveSet.add_spec in H0 as [contra | IN]; auto.
          apply HEQ in contra. inv contra. }
  intros. specialize (H (PositiveSet.elements rs')).
  assert (NoDup (PositiveSet.elements rs')) by (apply nodup_elements).
  apply H with rm in H2.
  - destruct H2 as [rmdeopt [UPDATE AGREE]]. exists rmdeopt. split; auto.
    unfold agree. intros r IN. apply AGREE. apply fold_elements. auto.
  - unfold defined in H0. intro. rewrite <- PSin_in. intros IN. apply H0. auto.
Qed.

Lemma deopt_subset_agree:
  forall rm rs rs' newrm,
    defined rm (DefFlatRegset.Inj rs) ->
    PositiveSet.Subset rs' rs ->
    update_regmap (identity_varmap rs') rm = OK newrm ->
    agree rm newrm rs'.
Proof.
  intros. apply defined_deopt_subset_agree with rm rs rs' in H; auto.
  destruct H as [rmdeopt [UPDATE AGREE]].
  rewrite H1 in UPDATE. inv UPDATE. auto.
Qed.

(* If we apply update_regmap with the identity over a given regset, the 
   resulting regmap will be undefined outside of the regset *)
Lemma update_not_captured:
  forall rm newrm rs r,
    ~ PositiveSet.In r rs ->
    update_regmap (identity_varmap rs) rm = OK newrm ->
    newrm ! r = None.
Proof.
  intros rm newrm rs r. rewrite PSin_in. 
  assert (forall l r rm newrm,
             ~ In r l ->
             update_regmap (map (fun r : reg => (r, UNA (uplus Integers.Int.zero) r)) l) rm = OK newrm ->
             newrm ! r = None).
  { induction l; intros.
    - inv H0. unfold empty_regmap. apply PTree.gempty.
    - inv H0. poseq_destr r0 a.
      + simpl in H. exfalso. apply H. left. auto.
      + destruct (eval_reg a rm0) eqn:EVAL; inv H2.
        destruct (update_regmap (map (fun r : reg => (r, UNA (uplus Integers.Int.zero) r)) l) rm0) eqn:UPD; inv H1.
        rewrite PTree.gso; auto. eapply IHl.
        2: { apply UPD. }
        intros IN. apply H. simpl. right. auto. }
  apply H.
Qed.

(** * Properties of clean_label_list *)
Lemma nodup_clean:
  forall def l c,
    NoDup (clean_label_list def c l).
Proof.
  intros def l c. unfold clean_label_list.
  assert (ND: NoDup (remove_dup l)).
  { unfold remove_dup. apply NoDup_nodup. }
  unfold filter_unused.
  assert (P: forall X (li:list X) f, NoDup li -> NoDup (filter f li)).
  { intros X li f H. induction li; simpl. constructor.
    destruct (f a) eqn:FA.
    - constructor.
      + unfold not. intros. apply filter_In in H0. destruct H0. inv H. apply H4. auto.
      + apply IHli. inv H. auto.
    - apply IHli. inv H. auto. }
  apply P. auto.
Qed.

Definition used (l:list label) (c:code) :=
  forall lbl, In lbl l -> exists i, c ! lbl = Some i.

Lemma used_clean:
  forall def l c, used (clean_label_list def c l) c.
Proof.
  unfold used. intros def l c lbl IN. unfold clean_label_list in IN.
  apply filter_In in IN as [IN _]. apply filter_In in IN as [IN USED].
  unfold is_used in USED. destruct (c!lbl); inv USED. eauto.
Qed.

Lemma used_cons:
  forall a l c,
    used (a::l) c -> used l c.
Proof.
  unfold used. intros a l c H lbl H0. apply H. simpl. right. auto.
Qed.

Lemma nodup_cons_in:
  forall  (l:list label) x y,
    NoDup (y::l) ->
    In x (y::l) ->
    (x = y /\ ~ In x l) \/ (x <> y /\ In x l).
Proof.
  intros l x y H H0. inv H. simpl in H0.
  poseq_destr x y.
  - left. split; auto.
  - right. split; auto. destruct H0. exfalso. apply HEQ. auto. auto.
Qed.



(** * Matching the stack and properties  *)
(* Matching stackframes: a version may have been replaced with its optimized version *)
Inductive match_stackframe (v:version) (fid:fun_id) (l:list label) (live:live_abs_state) (def:def_abs_state): stackframe -> stackframe -> Prop :=
| frame_same:              (* when doing a call from an unoptimized function *)
    forall sf,
      (match_stackframe v fid l live def) sf sf
| frame_deopt:             (* when doing a call after deoptimization *)
    forall r lbl rms rmo
      (AGREE: forall retval, agree (rms#r<-retval) (rmo#r<-retval) (live_dr_transf (ver_code v) lbl (live_absstate_get lbl live))),
      (match_stackframe v fid l live def) (IR_SF (r, v, lbl, rms)) (IR_SF (r, v, lbl, rmo))
| frame_opt:               (* when doing a call from the optimized version *)
    forall r lbl rms vins
      (ANC_INSERT: anc_insert_version v fid l live def = OK vins)
      (DEF: forall retval, defined (rms#r<-retval) (def_absstate_get lbl def)),
      (match_stackframe v fid l live def) (IR_SF (r, v, lbl, rms)) (IR_SF (r, vins, lbl, rms)).

(* Generalizing match_stackframe to the entire stack *)
Inductive match_stack (v:version) (fid:fun_id) (l:list label) (live:live_abs_state) (def:def_abs_state): stack -> stack -> Prop :=
| match_nil:
    (match_stack v fid l live def) nil nil
| match_cons:
    forall s s' sf sf'
      (MS: (match_stack v fid l live def) s s')
      (MSF: (match_stackframe v fid l live def) sf sf'),
      (match_stack v fid l live def) (sf::s) (sf'::s').

Lemma match_stackframe_same:
  forall v fid l live def sf,
    (match_stackframe v fid l live def) sf sf.
Proof.
  intros v fid l live def sf. destruct sf; apply frame_same.
Qed.

Lemma match_stack_same:
  forall s v fid l live def,
    (match_stack v fid l live def) s s.
Proof.
  intros s v fid l live def. induction s; constructor. auto. apply match_stackframe_same.
Qed.

Lemma match_app:
  forall synth s s' v fid l live def,
    (match_stack v fid l live def) s s' ->
    (match_stack v fid l live def) (synth++s) (synth++s').
Proof.
  intros. induction synth.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. apply match_cons. auto. apply match_stackframe_same.
Qed.

Lemma app_match:
  forall synth synthopt s s' v fid l live def,
    (match_stack v fid l live def) s s' ->
    (match_stack v fid l live def) synth synthopt ->
    (match_stack v fid l live def) (synth++s) (synthopt++s').
Proof.
  intros. induction H0.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. apply match_cons; auto.
Qed.

(** * Index and order used in the simulation *)
(* There is one stuttering step for each inserted Anchor *)
Inductive anc_index: Type :=
| Two : anc_index
| One : anc_index
| Zero: anc_index.

Inductive anc_order: anc_index -> anc_index -> Prop :=
| order10: anc_order Zero One
| order20: anc_order Zero Two
| order21: anc_order One Two.

Lemma wfounded: well_founded anc_order.
Proof.
  unfold well_founded. intros a. constructor. intros y H. inv H.
  - constructor. intros y H. inv H.
  - constructor. intros y H. inv H.
  - constructor. intros y H. inv H. constructor. intros y H. inv H.
Qed.

Lemma trans: Relation_Definitions.transitive _ anc_order.
Proof.
  unfold Relation_Definitions.transitive. intros x y z H H0. inv H; inv H0. constructor.
Qed.

(** * The match_states relation  *)
(* This proof is a backward internal simulation.
   Each step of the source is matched with a step of the optimized program.
   Except for the steps of newly inserted Anchors.
   At a new Anchor, we stutter in the source.

<<

       st1 --------------- st2
        |                   |
       t|(1 or 2 steps)     |t
        |                   |
        v                   v
       st1'--------------- st2'

>>
 *)

Inductive match_states (p:program) (v:version) (fid:fun_id) (lbllist:list label) (live:live_abs_state) (def:def_abs_state): anc_index -> mixed_state -> mixed_state -> Prop :=
| anc_match:                (* matching at a new Anchor in the optimized version *)
    forall vins s s' rms top heap lbl
      (MATCHSTACK: (match_stack v fid lbllist live def) s s')
      (DEF: defined rms (def_absstate_get lbl def))
      (OPT: anc_insert_version v fid lbllist live def = OK vins)
      (IN: In lbl lbllist),
      (match_states p v fid lbllist live def) Two
        (Halt_IR (v, lbl, rms), mkmut s top heap)
        (Halt_IR (vins, lbl, rms), mkmut s' top heap)

| deoptstate_match:
  forall vins s s' rms newrm top heap lbl
    (MATCHSTACK: (match_stack v fid lbllist live def) s s')
    (OPT: anc_insert_version v fid lbllist live def = OK vins)
    (AGREE: agree rms newrm (live_dr_transf (ver_code v) lbl (live_absstate_get lbl live)))
    (IN: In lbl lbllist),
    (match_states p v fid lbllist live def) One
      (Halt_IR (v, lbl, newrm), mkmut s top heap)
      (S_Deopt (ir_deopt fid lbl rms), mkmut s' top heap)
  

| shift_match:                     (* matching at a shifted instruction *)
    forall vins s s' rms top heap lbl fresh
      (MATCHSTACK: (match_stack v fid lbllist live def) s s')
      (DEF: defined rms (def_absstate_get lbl def))
      (OPT: anc_insert_version v fid lbllist live def = OK vins)
      (NOT_IN: ~ In fresh lbllist)
      (SAME_CODE: (ver_code v) # lbl = (ver_code vins) # fresh),
      (match_states p v fid lbllist live def) Zero
        (Halt_IR (v, lbl, rms), mkmut s top heap)
        (Halt_IR (vins, fresh, rms), mkmut s' top heap)

| opt_match:                        (* matching inside the optimized version *)
    forall vins s s' lbl rms top heap
      (MATCHSTACK: (match_stack v fid lbllist live def) s s')
      (DEF: defined rms (def_absstate_get lbl def))
      (OPT: anc_insert_version v fid lbllist live def = OK vins)
      (NOTIN: ~ In lbl lbllist),
      (match_states p v fid lbllist live def) Zero
        (Halt_IR (v, lbl, rms), mkmut s top heap)
        (Halt_IR (vins, lbl, rms), mkmut s' top heap)

| refl_match:                   (* matching outside of the optimized version *)
    forall s s' synchro top heap
      (MATCHSTACK: (match_stack v fid lbllist live def) s s'),
      (match_states p v fid lbllist live def) Zero
        (synchro, mkmut s top heap)
        (synchro, mkmut s' top heap)

| deopt_match:   (* matching after deoptimization at the inserted Anchors *)
    forall s s' pc rms rmo top heap
      (MATCHSTACK: (match_stack v fid lbllist live def) s s')
      (AGREE: agree rms rmo (live_dr_transf (ver_code v) pc (live_absstate_get pc live))),
      (match_states p v fid lbllist live def) Zero
        (Halt_IR (v, pc, rms), mkmut s top heap)
        (Halt_IR (v, pc, rmo), mkmut s' top heap).


(** * Code preservation properties  *)
Lemma code_preservation':        (* use at opt_match *)
  forall vbase vins fid l_anc lbl live def,
    anc_insert_version vbase fid l_anc live def = OK vins ->
    ~ In lbl l_anc ->
    forall iopt isrc,
      (ver_code vins) # lbl = Some iopt ->
      (ver_code vbase) # lbl = Some isrc ->
      iopt = isrc.
Proof.
  intros vbase vins fid l_anc lbl live def OPT NOTIN iopt isrc CODEOPT CODESRC.
  unfold anc_insert_version in OPT. repeat do_ok.
  assert (H: forall cs co, insert_list_anchor (ver_code vbase) cs fid l_anc live def = OK co ->
                           co ! lbl = Some iopt -> cs ! lbl = Some isrc -> iopt = isrc).
  { clear HDO CODEOPT CODESRC. induction l_anc; intros.
    - simpl in H. inv H. rewrite H0 in H1. inv H1. auto.
    - simpl in H. repeat do_ok. simpl in NOTIN.
      assert (NOTIN': a<>lbl /\ ~ In lbl l_anc).
      { split; unfold not; intros; apply NOTIN. left. auto. right. auto. }
      clear NOTIN. destruct NOTIN' as [DIFF NOTIN].
      specialize (IHl_anc NOTIN c0 co H3 H0). unfold insert_single_anchor in HDO. repeat do_ok.
      rewrite PTree.gso in IHl_anc; auto.
      poseq_destr (fresh_sug (Pos.add a spacing) cs) lbl.
      + erewrite fresh_sug_correct in H1; eauto. inv H1.
      + rewrite PTree.gso in IHl_anc; auto. }
  eapply H; eauto.
Qed.

Lemma code_preservation:        (* use at opt_match *)
  forall p rtl nc p' s s' rms rmo top heap t news vbase vins fid l_anc lbl live def,
    anc_insert_version vbase fid l_anc live def = OK vins ->
    ~ In lbl l_anc ->
    safe (mixed_sem p rtl nc AnchorOn) (Halt_IR (vbase, lbl, rms), mkmut s top heap) ->
    Step (mixed_sem p' rtl nc AnchorOn) (Halt_IR (vins, lbl, rmo), mkmut s' top heap) t news ->
    (ver_code vbase) # lbl = (ver_code vins) # lbl.
Proof.
  intros p rtl nc p' s s' rms rmo top heap t news vbase vins fid l_anc lbl live def H H0 H1 H2.
  unfold safe in H1. specialize (H1 _ (star_refl _ _ _)). destruct H1 as [[r FINAL]|[t' [s'' STEP]]].
  { inv FINAL. }
  assert (exists iins, (ver_code vins) # lbl = Some iins).
  { inv H2; eauto. unfold ir_step, ir_int_step in STEP0. repeat sdo_ok. eauto. }
  assert (exists ibase, (ver_code vbase) # lbl = Some ibase).
  { inv STEP; eauto. unfold ir_step, ir_int_step in STEP0. repeat sdo_ok. eauto. }
  destruct H1. destruct H3. rewrite H1. rewrite H3.
  apply f_equal. symmetry. eapply code_preservation'; eauto.
Qed.    


(* The pass  cannot remove any code *)
Lemma more_code:
  forall vbase vins fid l_anc lbl live def,
    anc_insert_version vbase fid l_anc live def = OK vins ->
    (ver_code vins) # lbl = None ->
    (ver_code vbase) # lbl = None.
Proof.
  intros vbase vins fid l_anc lbl live def OPT CODE.
  unfold anc_insert_version in OPT. repeat do_ok.
  assert (H: forall cs co, insert_list_anchor (ver_code vbase) cs fid l_anc live def = OK co -> co ! lbl = None -> cs ! lbl = None).
  { clear HDO. induction l_anc; intros.
    - unfold insert_list_anchor in H. inv H. auto.
    - simpl in H. repeat do_ok. specialize (IHl_anc c0 co H2 H0).
      unfold insert_single_anchor in HDO. repeat do_ok.
      poseq_destr a lbl.
      + rewrite PTree.gss in IHl_anc. inv IHl_anc.
      + rewrite PTree.gso in IHl_anc; auto.
        poseq_destr (fresh_sug (Pos.add a spacing) cs) lbl.
        * eapply fresh_sug_correct. eauto.
        * rewrite PTree.gso in IHl_anc; auto. }
  specialize (H (ver_code vbase) c HDO CODE). auto.
Qed.

Lemma more_code':
  forall base_c cs co fid lbl anc_lbl live def,
    insert_single_anchor base_c cs fid anc_lbl live def = OK co ->
    co ! lbl = None ->
    cs ! lbl = None.
Proof.
  intros base_c cs co fid lbl anc_lbl live def H H0. unfold insert_single_anchor in H. repeat do_ok.
  poseq_destr anc_lbl lbl.
  - rewrite PTree.gss in H0. inv H0.
  - rewrite PTree.gso in H0; auto.
    poseq_destr (fresh_sug (Pos.add anc_lbl spacing) cs) lbl.
    + rewrite PTree.gss in H0. eapply fresh_sug_correct. eauto.
    + rewrite PTree.gso in H0; auto.
Qed.

(* The code is preserved outside of the list of labels *)
Lemma code_preserved:
  forall fid lbl i l live def base_c cs co,
    insert_list_anchor base_c cs fid l live def = OK co ->
    cs ! lbl = Some i ->
    ~ In lbl l ->
    co ! lbl = Some i.
Proof.
  intros fid lbl i l live def base_c. induction l; intros.
  - simpl in H. inv H. auto.
  - simpl in H. repeat do_ok.
    specialize (IHl c co H3). rewrite in_cns in H1. apply Decidable.not_or in H1. destruct H1.
    apply IHl; auto.
    unfold insert_single_anchor in HDO. repeat do_ok. rewrite PTree.gso; auto.
    poseq_destr (fresh_sug (Pos.add a spacing) cs) lbl.
    + erewrite fresh_sug_correct in H0; auto. inv H0.
    + rewrite PTree.gso; auto.
Qed.

(* Used is preserved by insertion of anchor *)
Lemma used_insert_single_anchor:
  forall l base_c cs co fid lbl live def,
    used l cs ->
    insert_single_anchor base_c cs fid lbl live def = OK co ->
    used l co.
Proof.
  intros. unfold insert_single_anchor in H0. repeat do_ok.
  unfold used. intros x IN. apply H in IN as [i' CODE].
  poseq_destr lbl x.
  - rewrite PTree.gss. eauto.
  - rewrite PTree.gso; auto. poseq_destr (fresh_sug (Pos.add lbl spacing) cs) x.
    + rewrite PTree.gss. eauto.
    + rewrite PTree.gso; auto. eauto.
Qed.

(* At the insertion point, the code is shifted *)
Lemma code_anc:                  (* use at anc_match *)
  forall vbase vins fid l_anc lbl live def,
    anc_insert_version vbase fid l_anc live def = OK vins ->
    In lbl l_anc ->
    NoDup l_anc ->
    used l_anc (ver_code vbase) ->
    (exists freshlbl rs_def rs_live,
        def_absstate_get lbl def = DefFlatRegset.Inj rs_def /\
        live_dr_transf (ver_code vbase) lbl (live_absstate_get lbl live) = rs_live /\
        (ver_code vins) # lbl = Some (Anchor (fid,lbl) (identity_varmap (PositiveSet.inter rs_def rs_live)) freshlbl) /\
        (ver_code vbase) # freshlbl = None /\
        exists i, (ver_code vbase) # lbl = Some i /\ (ver_code vins) # freshlbl = Some i).
Proof.
  intros vbase vins fid l_anc lbl live def OPT IN NODUP DEF.
  unfold anc_insert_version in OPT. repeat do_ok.
  assert (forall cs co, insert_list_anchor (ver_code vbase) cs fid l_anc live def = OK co ->
                        In lbl l_anc -> used l_anc cs ->
                        exists freshlbl rs_def rs_live,
                          def_absstate_get lbl def = DefFlatRegset.Inj rs_def /\
                          live_dr_transf (ver_code vbase) lbl (live_absstate_get lbl live) = rs_live /\
                          co ! lbl = Some (Anchor (fid,lbl) (identity_varmap (PositiveSet.inter rs_def rs_live)) freshlbl) /\
                          cs ! freshlbl = None /\
                          exists i, cs ! lbl = Some i /\
                                    co ! freshlbl = Some i).
  { clear HDO IN. induction l_anc; intros.
    - simpl in H. inv H. inv H0.
    - simpl in H. repeat do_ok. apply nodup_cons_in in H0; auto.
      destruct H0 as [[EQ NOTIN] | [DIFF IN]].
      + subst. unfold insert_single_anchor in HDO. repeat do_ok.
        exists (fresh_sug (Pos.add a spacing) cs). exists r.
        exists (live_dr_transf (ver_code vbase) a (live_absstate_get a live)).
        split; try split; auto. unfold defined_rs in HDO1. destruct (def_absstate_get a def); inv HDO1. auto. split.
        * eapply code_preserved; eauto. rewrite PTree.gss. auto.
        * split. { eapply fresh_sug_correct. eauto. }
          exists i. split; auto. poseq_destr (fresh_sug (Pos.add a spacing) cs) a.
          erewrite fresh_sug_correct in HDO; eauto. inv HDO.
          eapply code_preserved; eauto. rewrite PTree.gso; auto. rewrite PTree.gss. auto.
          unfold not; intro. apply used_cons in H1. apply H1 in H. destruct H.
          erewrite fresh_sug_correct in H; auto. inv H.
      + inv NODUP. apply used_cons in DEF as DEF'. apply used_cons in H1 as DEF''.
        assert (used l_anc c0) by (eapply used_insert_single_anchor; eauto).
        specialize (IHl_anc H4 DEF' c0 co H3 IN H). destruct IHl_anc as [freshlbl [rs_def [rs_live [GETDEF [GETLIVE [CO [FRESH [i [C0 CO']]]]]]]]].
        exists freshlbl. exists rs_def. exists rs_live.
        split; auto. split; auto. split; auto. split.
        { eapply more_code'; eauto. }
        exists i. split; auto.
        unfold insert_single_anchor in HDO. repeat do_ok. rewrite PTree.gso in C0; auto.
        poseq_destr (fresh_sug (Pos.add a spacing) cs) lbl.
        * apply DEF'' in IN. destruct IN. erewrite fresh_sug_correct in H0; eauto. inv H0.
        * rewrite PTree.gso in C0; auto. }
  apply H; auto.
Qed.

Lemma code_notanc:               (* for progress preservation *)
  forall vbase vins fid l_anc lbl live def,
    anc_insert_version vbase fid l_anc live def = OK vins ->
    ~ In lbl l_anc ->
    forall i, (ver_code vbase) # lbl = Some i ->
              (ver_code vins) # lbl = Some i.
Proof.
  assert (H: forall (l:list label) i lbl fid live def base_c cs co,
             insert_list_anchor base_c cs fid l live def = OK co ->
             ~ In lbl l ->
             cs # lbl = Some i ->
             co # lbl = Some i).
  { intros. generalize dependent cs.
    induction l; intros.
    - simpl in H. inv H. auto.
    - simpl in H. repeat do_ok. simpl in H0.
      assert (NOTIN: ~ In lbl l).
      { unfold not. intros. apply H0. right. auto. }
      assert (NOTA: a <> lbl).
      { unfold not. intros. apply H0. left. auto. }
      specialize (IHl NOTIN c H3). unfold insert_single_anchor in HDO.
      repeat do_ok. rewrite PTree.gso in IHl; auto.
      apply IHl. poseq_destr (fresh_sug (Pos.add a spacing) cs) lbl.
      + erewrite fresh_sug_correct in H1; auto. inv H1.
      + rewrite PTree.gso; auto. }
  intros vbase vins fid l_anc lbl live def H0 H1 i H2.
  unfold anc_insert_version in H0. repeat do_ok.
  eapply H in HDO; eauto.
Qed.


Ltac rmagreef :=
  match goal with
  | [H: eval_expr ?e ?rms = OK ?v,
        H1: agree ?rms ?rmo ?live |- _] => eapply agree_eval_expr in H; eauto
  | [H: eval_list ?e ?rms = OK ?v,
        H1: agree ?rms ?rmo ?live |- _] => eapply agree_eval_list in H; eauto
  | [H: eval_list_reg ?e ?rms = OK ?v,
        H1: agree ?rms ?rmo ?live |- _] => eapply agree_eval_list_reg in H; eauto
  end.

Lemma progress_preserved:
  forall vbase vins fid l_anc live def s1 s2 p rtl nc i,
    anc_insert_version vbase fid l_anc live def = OK vins ->
    find_base_version fid p = Some vbase ->
    match_states p vbase fid l_anc live def i s1 s2 ->
    safe (mixed_sem p rtl nc AnchorOn) s1 ->
    NoDup l_anc ->
    used l_anc (ver_code vbase) ->
    (exists r : Integers.Int.int, final_mixed_state (set_version p fid vins) s2 r) \/
    (exists (t : trace) (s2' : mixed_state),
        Step (mixed_sem (set_version p fid vins) rtl nc AnchorOn) s2 t s2').
Proof.
  intros vbase vins fid l_anc live def s1 s2 p rtl nc i OPTV FINDBASE MATCH SAFE NODUP DEF.
  inv MATCH.
  + rewrite OPT in OPTV. inv OPTV.
    right. exists E0. apply code_anc with (lbl:=lbl)in OPT as CODE; auto.
    destruct CODE as [freshlbl [rs_def [rs_live [GETDEF [GETLIVE [ANCCODE [BASECODE [i SHIFTCODE]]]]]]]].
    rewrite GETDEF in DEF0. 
    exists (Halt_IR (vins, freshlbl, rms), mkmut s' top heap). 
    assert (exists newrm,
               update_regmap (identity_varmap (PositiveSet.inter rs_def rs_live)) rms = OK newrm /\
               agree rms newrm (PositiveSet.inter rs_def rs_live))
      as [newrm [UPDATE' AGREE]].
    { eapply defined_deopt_subset_agree; eauto.
      intros r IN'. apply PositiveSet.inter_spec in IN' as [IN' _]. auto. }
    eapply Anchor_go_on; eauto.
  + rewrite OPT in OPTV. inv OPTV.
    unfold find_base_version, find_function_ir in FINDBASE.
    destruct ((prog_funlist p) # fid) eqn:FIND; inv FINDBASE. 
    right. exists E0. econstructor. eapply Deopt; simpl; eauto.
    unfold set_version_funlist. rewrite FIND. rewrite PTree.gss. eauto.
  + apply safe_step in SAFE. destruct SAFE as [[t [s'' STEP]]|[r FINAL]].
    2: { inv FINAL. } 
    right. rewrite OPT in OPTV. inv OPTV. simpl. inv STEP.
    * unfold ir_step, ir_int_step in STEP0. repeat sdo_ok.
      destruct p0. exists t. 
      { destruct i; repeat sdo_ok.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE. simpl.
            unfold fret'. rewrite HDO. simpl. eauto.
          - poseq_destr f fid.
            + simpl in HDO. repeat sdo_ok.
              unfold n_push_interpreter_stackframe in HDO0. simpl in HDO0. destruct top; inv HDO0.
              econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE. simpl.
              unfold sbind. unfold n_push_interpreter_stackframe. simpl. rewrite HDO. simpl. eauto.
            + simpl in HDO. repeat sdo_ok.
              unfold n_push_interpreter_stackframe in HDO0. simpl in HDO0. destruct top; inv HDO0.
              econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE. simpl.
              unfold sbind. unfold n_push_interpreter_stackframe. simpl. rewrite HDO. simpl. eauto.
          - destruct (bool_of_int i) eqn:BOOL; repeat sdo_ok.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE. simpl.
              rewrite HDO2. simpl. rewrite BOOL. simpl. eauto.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE. simpl.
              rewrite HDO2. simpl. rewrite BOOL. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE. simpl.
            rewrite HDO. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE. simpl.
            rewrite HDO. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE. simpl.
            rewrite HDO2. simpl. rewrite HDO. simpl. unfold sbind. unfold n_memset in HDO3.
            unfold n_memset. destruct (Integers.Int.lt i mem_size). inv HDO3. eauto. inv HDO3.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE. simpl.
            rewrite HDO. simpl. unfold sbind. unfold n_memget in HDO2.
            unfold n_memget. destruct (Integers.Int.lt i mem_size). inv HDO2. 2: inv HDO2.
            simpl. destruct (heap ! (intpos.pos_of_int i)); inv H0. eauto.
          - destruct d. repeat sdo_ok. destruct (bool_of_int i) eqn:BOOL; repeat sdo_ok.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE. simpl.
              rewrite HDO2. simpl. rewrite BOOL. simpl. eauto.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE. simpl.
              rewrite HDO2. simpl. rewrite BOOL. simpl. rewrite HDO. simpl. eauto.
          - destruct d. repeat sdo_ok. inv HDO. }
    * exists E0. econstructor. eapply Anchor_go_on; eauto. rewrite <- SAME_CODE. eauto.
    * exists E0. econstructor. eapply Anchor_deopt; eauto. rewrite <- SAME_CODE. eauto.
    
  + rewrite OPT in OPTV. inv OPTV. apply safe_step in SAFE as SAFE'.
    destruct SAFE' as [[t [s'' STEP]]|[r FINAL]]. 2: { inv FINAL. }
    specialize (code_notanc vbase vins fid l_anc lbl live def OPT NOTIN).
    intros SAME_CODE.
    assert ((ver_code vbase) ! lbl = (ver_code vins) ! lbl) as SAME_CODE'.
    {
      destruct ((ver_code vbase) ! lbl) eqn:Hbase.
      - symmetry. auto.
      - apply safe_code in SAFE as [i BASE]. rewrite BASE in Hbase. discriminate Hbase.
    }
    right. inv STEP.
    * exists t. unfold ir_step, ir_int_step in STEP0. repeat sdo_ok.
      { destruct i; repeat sdo_ok.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE'. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE'. simpl.
            unfold fret'. rewrite HDO. simpl. eauto.
          - poseq_destr f fid.
            + simpl in HDO. repeat sdo_ok.
              unfold n_push_interpreter_stackframe in HDO0. simpl in HDO0. destruct top; inv HDO0.
              econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE'. simpl.
              unfold sbind. unfold n_push_interpreter_stackframe. simpl. rewrite HDO. simpl. eauto.
            + simpl in HDO. repeat sdo_ok.
              unfold n_push_interpreter_stackframe in HDO0. simpl in HDO0. destruct top; inv HDO0.
              econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE'. simpl.
              unfold sbind. unfold n_push_interpreter_stackframe. simpl. rewrite HDO. simpl. eauto.
          - destruct (bool_of_int i) eqn:BOOL; repeat sdo_ok.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE'. simpl.
              rewrite HDO2. simpl. rewrite BOOL. simpl. eauto.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE'. simpl.
              rewrite HDO2. simpl. rewrite BOOL. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE'. simpl.
            rewrite HDO. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE'. simpl.
            rewrite HDO. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE'. simpl.
            rewrite HDO2. simpl. rewrite HDO. simpl. unfold sbind. unfold n_memset in HDO3.
            unfold n_memset. destruct (Integers.Int.lt i mem_size). inv HDO3. eauto. inv HDO3.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE'. simpl.
            rewrite HDO. simpl. unfold sbind. unfold n_memget in HDO2.
            unfold n_memget. destruct (Integers.Int.lt i mem_size). inv HDO2. 2: inv HDO2.
            simpl. destruct (heap ! (intpos.pos_of_int i)); inv H0. eauto.
          - destruct d. repeat sdo_ok. destruct (bool_of_int i) eqn:BOOL; repeat sdo_ok.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE'. simpl.
              rewrite HDO2. simpl. rewrite BOOL. simpl. eauto.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite <- SAME_CODE'. simpl.
              rewrite HDO2. simpl. rewrite BOOL. simpl. rewrite HDO. simpl. eauto.
          - destruct d. repeat sdo_ok. inv HDO. }
    * exists E0. econstructor. eapply Anchor_go_on; eauto. 
    * exists E0. econstructor. eapply Anchor_deopt; eauto. 

  + rename s into stk. rename s' into stk'.
{ apply safe_step in SAFE. destruct SAFE as [[t [s'' STEP]]| [r FINAL]].
    2: { inv FINAL. left. exists r. constructor. }
    right. inv STEP.
    + destruct ms1. eapply addstk_same in STEP0 as [s [APP SAME]]; eauto.
      2: apply addstk_irstep.
      exists t. econstructor. eapply IR_step. simpl. eauto.
    + destruct ms1. eapply addstk_same in STEP0 as [s [APP SAME]]; eauto.
      2: apply addstk_asmstep.
      exists t. econstructor. eapply x86_step. simpl. eauto.
    + econstructor. econstructor. eapply rtl_step; eauto.
    + destruct ms'. eapply addstk_same in BLOCK as [s [APP SAME]]; eauto.
      2: { unfold block_step. repeat addstk_auto. unfold exec_block_instr. repeat addstk_auto.
           unfold ASMinterpreter.prim_sem_dec. repeat addstk_auto. }
      exists t. econstructor. eapply rtl_block_step. eauto.
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
        unfold find_base_version, find_function_ir in FINDBASE.
        destruct ((prog_funlist p)#fid); inv FINDBASE. rewrite PTree.gso; auto.
    + destruct ms2, ms3, ms4. eapply addstk_same in CALLEE as [s [APP SAME]]; eauto.
      2: apply addstk_callee.
      eapply addstk_prim_same in COMPILED as [stk2 [APP2 SAME2]]; try constructor.
      apply app_same in APP2. subst.
      eapply addstk_same in ARGS as [stk3 [APP3 SAME3]]. 2: apply addstk_set_args. subst.
      eapply addstk_prim_same in LOAD as [stk4 [APP4 SAME4]]; try constructor. subst.
      exists E0. econstructor. eapply Call_x86; eauto.
    + destruct ms2, ms3. eapply addstk_same in CALLEE as [s [APP SAME]].
      2: apply addstk_callee.
      eapply addstk_prim_same in COMPILED as [stk2 [APP2 SAME2]]; try constructor.
      apply app_same in APP2. subst.
      eapply addstk_same in ARGS as [stk3 [APP3 SAME3]]. 2: apply addstk_set_args. subst.
      econstructor. econstructor. eapply Call_RTL; eauto.
    + destruct ms1, ms2. eapply addstk_same in CALLEE as [s [APP SAME]].
      2: apply addstk_callee.
      eapply addstk_prim_same in COMPILED as [stk2 [APP2 SAME2]]; try constructor.
      apply app_same in APP2. subst.
      eapply addstk_same in ARGS as [stk3 [APP3 SAME3]]. 2: apply addstk_set_args. subst.
      econstructor. econstructor. eapply Call_RTL_Block; eauto.
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
    + destruct loc.
      * destruct top; inv RETVAL. inv OPEN_SF. unfold n_open_stackframe in H0. simpl in H0.
        destruct top; inv H0. destruct stk; inv H1. destruct s; inv H0.
        destruct a, p, p0, p; inv H1. simpl in SETRETVAL. unfold n_save in SETRETVAL. inv SETRETVAL.
        simpl in NOT_COMPILED. unfold n_check_compiled in NOT_COMPILED. simpl in NOT_COMPILED.
        destruct (nc ! fid0) eqn:NOT; inv NOT_COMPILED.
        inv MATCHSTACK. inv MSF.
        econstructor. econstructor. eapply Return_RTL; eauto.
        ** simpl. unfold sbind. simpl. eauto.
        ** simpl. unfold n_open_stackframe. simpl. eauto.
        ** simpl. unfold n_save. simpl. eauto.
        ** simpl. unfold n_check_compiled. simpl. rewrite NOT. auto.
      * inv RETVAL. inv OPEN_SF. unfold n_open_stackframe in H0. simpl in H0.
        destruct top; inv H0. destruct stk; inv H1. destruct s; inv H0.
        destruct a, p, p0, p; inv H1. simpl in SETRETVAL. unfold n_save in SETRETVAL. inv SETRETVAL.
        simpl in NOT_COMPILED. unfold n_check_compiled in NOT_COMPILED. simpl in NOT_COMPILED.
        destruct (nc ! fid0) eqn:NOT; inv NOT_COMPILED.
        inv MATCHSTACK. inv MSF.
        econstructor. econstructor. eapply Return_RTL; simpl; eauto.
        ** unfold n_open_stackframe. simpl. eauto.
        ** unfold n_save. simpl. eauto.
        ** unfold n_check_compiled. simpl. rewrite NOT. auto.
    + destruct loc.
      * destruct top; inv RETVAL. inv OPEN_SF. unfold n_open_stackframe in H0. simpl in H0.
        destruct top; inv H0. destruct stk; inv H1. destruct s; inv H0.
        destruct a, p, p0, p; inv H1. simpl in SETRETVAL. unfold n_save in SETRETVAL. inv SETRETVAL.
        simpl in NOT_COMPILED. unfold n_check_compiled in NOT_COMPILED. simpl in NOT_COMPILED.
        destruct (nc ! fid0) eqn:NOT; inv NOT_COMPILED.
        inv MATCHSTACK. inv MSF.
        econstructor. econstructor. eapply Return_RTL_Block; eauto.
        ** simpl. unfold sbind. simpl. eauto.
        ** simpl. unfold n_open_stackframe. simpl. eauto.
        ** simpl. unfold n_save. simpl. eauto.
        ** simpl. unfold n_check_compiled. simpl. rewrite NOT. auto.
      * inv RETVAL. inv OPEN_SF. unfold n_open_stackframe in H0. simpl in H0.
        destruct top; inv H0. destruct stk; inv H1. destruct s; inv H0.
        destruct a, p, p0, p; inv H1. simpl in SETRETVAL. unfold n_save in SETRETVAL. inv SETRETVAL.
        simpl in NOT_COMPILED. unfold n_check_compiled in NOT_COMPILED. simpl in NOT_COMPILED.
        destruct (nc ! fid0) eqn:NOT; inv NOT_COMPILED.
        inv MATCHSTACK. inv MSF.
        econstructor. econstructor. eapply Return_RTL_Block; simpl; eauto.
         ** unfold n_open_stackframe. simpl. eauto.
         ** unfold n_save. simpl. eauto.
         ** unfold n_check_compiled. simpl. rewrite NOT. auto.
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
      unfold find_base_version, find_function_ir in FINDBASE.
      destruct ((prog_funlist p) # ftgt) eqn:FIND; inv FINDBASE. inv FINDF.
      poseq_destr fid ftgt.
      * econstructor. econstructor. eapply Deopt; eauto.
        unfold set_version, set_version_funlist. simpl.
        rewrite FIND. rewrite PTree.gss; eauto.
      * econstructor. econstructor. eapply Deopt; eauto.
        unfold set_version, set_version_funlist. simpl. 
        destruct ((prog_funlist p) # fid) eqn:FIND'; inv H0. rewrite PTree.gso; eauto.
      * inv FINDF. 
    + destruct ms1. eapply addstk_same in PRIM_CALL as [s [APP SAME]].
      2: { unfold ASMinterpreter.prim_sem_dec. repeat addstk_auto. }
      econstructor. econstructor. eapply RTL_prim; eauto.
    + econstructor. econstructor. eapply RTL_end; eauto.
    + econstructor. econstructor. eapply RTL_block_end; eauto.
    + econstructor. econstructor. eapply Anchor_go_on; eauto.
    + econstructor. econstructor. eapply Anchor_deopt; eauto.
}      

  + right. apply safe_step in SAFE. destruct SAFE as [[t [s'' STEP]]|[r FINAL]].
    2: { inv FINAL. }
    inv STEP.
    * unfold ir_step, ir_int_step in STEP0. repeat sdo_ok.
      unfold live_dr_transf in AGREE. rewrite HDO1 in AGREE.
      destruct p0. exists t. 
      { destruct i; repeat sdo_ok; repeat rmagreef.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite HDO1. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite HDO1. simpl.
            unfold fret'. rewrite HDO. simpl. eauto.
          - poseq_destr f fid.
            + simpl in HDO. repeat sdo_ok; repeat rmagreef.
              unfold n_push_interpreter_stackframe in HDO0. simpl in HDO0. destruct top; inv HDO0.
              econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite HDO1. simpl.
              unfold sbind. rewrite HDO. simpl. eauto.
            + simpl in HDO. repeat sdo_ok; repeat rmagreef.
              unfold n_push_interpreter_stackframe in HDO0. simpl in HDO0. destruct top; inv HDO0.
              econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite HDO1. simpl.
              unfold sbind. unfold n_push_interpreter_stackframe. simpl. rewrite HDO. simpl. eauto.
          - destruct (bool_of_int i) eqn:BOOL; repeat sdo_ok; repeat rmagreef.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite HDO1. simpl.
              eapply agree_eval_reg in HDO2; eauto.
              rewrite HDO2. simpl. rewrite BOOL. simpl. eauto.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite HDO1. simpl.
              eapply agree_eval_reg in HDO2; eauto.
              rewrite HDO2. simpl. rewrite BOOL. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite HDO1. simpl.
            rewrite HDO. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite HDO1. simpl.
            rewrite HDO. simpl. eauto.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite HDO1. simpl.
            eapply agree_eval_reg in HDO; eauto. eapply agree_eval_reg in HDO2; eauto.
            2: { eapply agree_subset; eauto. apply reg_live_subset. }
            rewrite HDO2. simpl. rewrite HDO. simpl. unfold sbind. unfold n_memset in HDO3.
            unfold n_memset. destruct (Integers.Int.lt i mem_size). inv HDO3. eauto. inv HDO3.
          - econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite HDO1. simpl.
            eapply agree_eval_reg in HDO; eauto.
            rewrite HDO. simpl. unfold sbind. unfold n_memget in HDO2.
            unfold n_memget. destruct (Integers.Int.lt i mem_size). inv HDO2. 2: inv HDO2.
            simpl. destruct (heap ! (intpos.pos_of_int i)); inv H0. eauto.
          - destruct d. repeat sdo_ok. destruct (bool_of_int i) eqn:BOOL; repeat sdo_ok.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite HDO1. simpl.
              eapply agree_eval_expr in HDO2; eauto. rewrite HDO2. simpl. rewrite BOOL. simpl. eauto.
            + econstructor. eapply IR_step. unfold ir_step, ir_int_step. rewrite HDO1. simpl.
              eapply agree_eval_expr in HDO2; eauto. rewrite HDO2. simpl. rewrite BOOL. simpl.
              eapply agree_update_regmap in HDO; eauto. rewrite HDO. simpl. eauto.
              apply agree_sym. eapply agree_subset; eauto. apply expr_live_subset.
          - destruct d. repeat sdo_ok. inv HDO. }
    * exists E0. econstructor. eapply Anchor_go_on; eauto. eapply agree_update_regmap in BUILD; eauto.
      unfold live_dr_transf in AGREE. rewrite ANCHOR in AGREE. apply agree_sym. eauto.
    * exists E0. econstructor. eapply Anchor_deopt; eauto. eapply agree_update_regmap in BUILD; eauto.
        unfold live_dr_transf in AGREE. rewrite ANCHOR in AGREE. apply agree_sym. eauto.
Qed.
    

Ltac def_ok :=
  match goal with
  | [CODE: (ver_code ?vsrc) ! ?lbl = Some ?i |- _] =>
    eapply def_analyze_correct; eauto; simpl; auto; unfold def_dr_transf; try rewrite CODE; auto
  end.
(* WIP *)

Ltac rmagreeb :=
  match goal with
  | [ |- agree (?rm1 # ?r <- ?v) (?rm2 # ?r <- ?v) ?rs] => apply agree_insert; auto
  | [H: eval_expr ?e ?rmo = OK ?v,
        H1: agree ?rms ?rmo ?rs |- _] => eapply agree_eval_expr in H; eauto
  | [H: eval_list ?e ?rmo = OK ?v,
        H1: agree ?rms ?rmo ?rs |- _] => eapply agree_eval_list in H; eauto
  | [H: eval_list_reg ?e ?rmo = OK ?v,
        H1: agree ?rms ?rmo ?rs |- _] => eapply agree_eval_list_reg in H; eauto

  end.

(* The diagram of a backward simulation for lowered steps *)
(* We only require the same code on both sides, and reuse this lemma for both opt_match and shift_match *)
Lemma lowered_diagram:
  forall p rtl nc vbase fid l_anc live def vins lblsrc lblopt s s' rms top heap t s2' mut2' f
         (OPT: anc_insert_version vbase fid l_anc live def = OK vins)
         (FINDF: find_function_ir fid p = Some f)
         (NOOPT: fn_opt f = None)
         (BASE': fn_base f = vbase)
         (MATCHSTACK: match_stack vbase fid l_anc live def s s')
         (SAME_CODE: (ver_code vbase) ! lblsrc = (ver_code vins) ! lblopt)
         (DEFREGS: defined_regs_analysis (ver_code vbase) (fn_params f) (ver_entry vbase) = Some def)
         (LIVENESS: liveness_analyze vbase = Some live)
         (DEF: defined rms (def_absstate_get lblsrc def))
         (STEP: exec (ir_step (vins, lblopt, rms)) naive_impl (mkmut s' top heap, nc) = SOK (t, s2') (mut2', nc)) 
         (SAFE: safe (mixed_sem p rtl nc AnchorOn) (Halt_IR (vbase, lblsrc, rms), mkmut s top heap)),
  exists (i: anc_index) (s1': mixed_state),
    (SPlus (mixed_sem p rtl nc AnchorOn) (Halt_IR (vbase, lblsrc, rms), mkmut s top heap) t s1' \/
     Star (mixed_sem p rtl nc AnchorOn) (Halt_IR (vbase, lblsrc, rms), mkmut s top heap) t s1' /\ anc_order i Zero) /\
    match_states p vbase fid l_anc live def i s1' (s2', mut2').
Proof.
  intros p rtl nc vbase fid l_anc live def vins lblsrc lblopt s s' rms top heap t s2' mut2' f OPT FINDF NOOPT BASE' MATCHSTACK SAME_CODE DEFREGS LIVENESS DEF STEP SAFE.
  assert (BASE: find_base_version fid p = Some vbase).
  { unfold find_base_version. rewrite FINDF. f_equal. auto. } clear BASE'.
  unfold ir_step, ir_int_step in STEP. repeat sdo_ok.
  destruct i; repeat sdo_ok.
  - destruct (in_or_not l l_anc) as [IN | NOTIN].
    + exists Two. econstructor. split.
      * left. apply plus_one. apply IR_step. unfold ir_step, ir_int_step.
        rewrite SAME_CODE. simpl. eauto.
      * eapply anc_match; eauto. def_ok. rewrite SAME_CODE. auto.
    + exists Zero. econstructor. split.
      * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
        rewrite SAME_CODE. simpl. eauto.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.
  - destruct (in_or_not l l_anc) as [IN | NOTIN].
    + exists Two. econstructor. split.
      * left. apply plus_one. apply IR_step. unfold ir_step, ir_int_step.
        rewrite SAME_CODE. simpl. rewrite HDO. simpl. eauto.
      * eapply anc_match; eauto. def_ok. rewrite SAME_CODE. auto.
    + exists Zero. econstructor. split.
      * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
        rewrite SAME_CODE. simpl. rewrite HDO. simpl. eauto.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.
  - simpl in HDO. repeat sdo_ok. unfold n_push_interpreter_stackframe in HDO0.
    simpl in HDO0. destruct top; inv HDO0.
    exists Zero. econstructor. split.
    * left. apply plus_one. apply IR_step. unfold ir_step, ir_int_step.
      simpl. rewrite SAME_CODE. simpl. unfold sbind.
      unfold n_push_interpreter_stackframe.  simpl. rewrite HDO. simpl. eauto.
    * simpl. apply refl_match. apply match_cons; auto. apply frame_opt; auto.
      intros retval. eapply def_analyze_correct; eauto. simpl; auto.
      unfold def_dr_transf. rewrite SAME_CODE. apply define_insert. auto.
  - destruct (bool_of_int i) eqn:BOOL; inv HDO.
    + destruct (in_or_not l l_anc) as [IN | NOTIN].
      * exists Two. econstructor. split.
        ** left. apply plus_one. apply IR_step. unfold ir_step, ir_int_step.
           rewrite SAME_CODE. simpl. rewrite HDO2. simpl. rewrite BOOL. simpl. eauto.
        ** eapply anc_match; eauto. def_ok. rewrite SAME_CODE. auto.
      * exists Zero. econstructor. split.
        ** left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
           rewrite SAME_CODE. simpl. rewrite HDO2. simpl. rewrite BOOL. simpl. eauto.
        ** eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.
    + destruct (in_or_not l0 l_anc) as [IN | NOTIN].
      * exists Two. econstructor. split.
        ** left. apply plus_one. apply IR_step. unfold ir_step, ir_int_step.
           rewrite SAME_CODE. simpl. rewrite HDO2. simpl. rewrite BOOL. simpl. eauto.
        ** eapply anc_match; eauto. def_ok. rewrite SAME_CODE. auto.
      * exists Zero. econstructor. split.
        ** left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
           rewrite SAME_CODE. simpl. rewrite HDO2. simpl. rewrite BOOL. simpl. eauto.
        ** eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.
  - exists Zero. econstructor. split.
    * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
      rewrite SAME_CODE. simpl. rewrite HDO. simpl. eauto.
    * eapply refl_match; eauto.
  - destruct (in_or_not l l_anc) as [IN | NOTIN].
    + exists Two. econstructor. split.
      * left. apply plus_one. apply IR_step. unfold ir_step, ir_int_step.
        rewrite SAME_CODE. simpl. rewrite HDO. simpl. eauto.
      * eapply anc_match; eauto. def_ok. rewrite SAME_CODE. apply define_insert. auto.
    + exists Zero. econstructor. split.
      * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
        rewrite SAME_CODE. simpl. rewrite HDO. simpl. eauto.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. apply define_insert. auto.
  - unfold n_memset in HDO3. destruct (Integers.Int.lt i mem_size) eqn:RANGE; inv HDO3.
    destruct (in_or_not l l_anc) as [IN | NOTIN].
    + exists Two. econstructor. split.
      * left. apply plus_one. apply IR_step. unfold ir_step, ir_int_step.
        rewrite SAME_CODE. simpl. rewrite HDO. simpl. rewrite HDO2. simpl.
        unfold n_memset. rewrite RANGE. unfold sbind. simpl. eauto.
      * eapply anc_match; eauto. def_ok. rewrite SAME_CODE. auto.
    + exists Zero. econstructor. split.
      * left. apply plus_one. apply IR_step. unfold ir_step, ir_int_step.
        rewrite SAME_CODE. simpl. rewrite HDO. simpl. rewrite HDO2. simpl.
        unfold n_memset. rewrite RANGE. unfold sbind. simpl. eauto.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.
  - unfold n_memget in HDO2. destruct (Integers.Int.lt i mem_size) eqn:RANGE; inv HDO2.
    destruct (heap # (intpos.pos_of_int i)) eqn:HEAP; inv H0.
    destruct (in_or_not l l_anc) as [IN | NOTIN].
    + exists Two. econstructor. split.
      * left. apply plus_one. apply IR_step. unfold ir_step, ir_int_step.
        rewrite SAME_CODE. simpl. rewrite HDO. simpl. 
        unfold n_memget. rewrite RANGE. unfold sbind. simpl. rewrite HEAP. eauto.
      * eapply anc_match; eauto. def_ok. rewrite SAME_CODE. apply define_insert. auto.
    + exists Zero. econstructor. split.
      * left. apply plus_one. apply IR_step. unfold ir_step, ir_int_step.
        rewrite SAME_CODE. simpl. rewrite HDO. simpl. 
        unfold n_memget. rewrite RANGE. unfold sbind. simpl. rewrite HEAP. eauto.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. apply define_insert. auto.
  - destruct d. repeat sdo_ok. destruct (bool_of_int i) eqn:GUARD; inv HDO.
    + destruct (in_or_not l l_anc) as [IN | NOTIN].
      * exists Two. econstructor. split.
        ** left. apply plus_one. apply IR_step. unfold ir_step, ir_int_step.
           rewrite SAME_CODE. simpl. rewrite HDO2. simpl. rewrite GUARD. simpl. eauto.
        ** eapply anc_match; eauto. def_ok. rewrite SAME_CODE. auto.
      * exists Zero. econstructor. split.
        ** left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
           rewrite SAME_CODE. simpl. rewrite HDO2. simpl. rewrite GUARD. simpl. eauto.
        ** eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.
    + repeat sdo_ok. exists Zero. econstructor. split.
      * left. apply plus_one. eapply IR_step; eauto. unfold ir_step, ir_int_step.
        rewrite SAME_CODE. simpl. rewrite HDO2. simpl. rewrite GUARD. rewrite HDO0. simpl. eauto.
      * simpl. apply refl_match. auto.
  - destruct d. inv HDO.
Qed.
  
 

(* Proved directly with a backward simulation *)
Theorem anchor_insertion_correct:
  forall p nc fid lbllist newp,
    insert_anchor fid lbllist p = OK newp ->
    backward_internal_simulation p newp None None nc nc AnchorOn AnchorOn.
Proof.
  intros p nc fid lbllist newp OPT. unfold insert_anchor in OPT. repeat do_ok.
  rename HDO1 into FINDOPTF. rename d into def. rename l into live.
  set (l_anc := (clean_label_list def (ver_code (fn_base f)) lbllist)).
  rename v into vins. unfold check_no_opt in HDO0. destruct (fn_opt f) eqn:NO_OPT; inv HDO0.
  set (vbase := (fn_base f)). fold l_anc vbase in HDO2. rename v0 into vins.
  assert (OPTV: anc_insert_version vbase fid l_anc live def = OK vins) by auto.
  unfold anc_insert_version in HDO3. repeat do_ok.
  set (vins := {|ver_code := c; ver_entry := ver_entry vbase |}). fold vins in OPTV.
  apply Backward_internal_simulation with (bsim_order := anc_order) (bsim_match_states := match_states p vbase fid l_anc live def).
  - apply wfounded.
  - unfold call_refl, p_reflexive. intros s H. inv H. exists Zero. destruct ms. apply refl_match.
    apply match_stack_same.

  - intros i s1 s2 r H H0 H1. inv H1. econstructor. split. apply star_refl. inv H. constructor.
    
  - intros. eapply progress_preserved; eauto. unfold find_base_version. rewrite FINDOPTF. eauto.
    apply nodup_clean. apply used_clean.

  - intros s2 t s2' STEP i s1 MATCH SAFE.
    assert (NODUP: NoDup l_anc) by apply nodup_clean.
    assert (DEF: used l_anc (ver_code vbase)) by apply used_clean.
    inv MATCH.

    + rewrite OPT in OPTV. inv OPTV. (* anc_match *)
      assert (IN': In lbl l_anc) by auto.
      eapply code_anc in IN as [fresh [rs_def [rs_live [GETDEF [GETLIVE [ANCCODE [FRESH [nextinstr [CODESRC CODEOPT]]]]]]]]]; eauto.
      inv STEP.
      { unfold ir_step, ir_int_step in STEP0. repeat sdo_ok. destruct i; repeat sdo_ok; inv ANCCODE.
        inv HDO0. }
      { exists Zero. econstructor. split. (* stuttering, Anchor goes on *)
        - right. split. 2:constructor. apply star_refl.
        - simpl in CODEOPT. simpl in ANCHOR. simpl in ANCCODE. rewrite ANCHOR in ANCCODE. inv ANCCODE.
          eapply shift_match; auto.
          + unfold not; intros. apply DEF in H as [i CODE']. rewrite CODE' in FRESH. inv FRESH.
          + simpl. rewrite CODESRC. rewrite CODEOPT. auto. }
      { exists One. econstructor. split. (* stuttering, Anchor deoptimizes *)
        - right. split. 2:constructor. apply star_refl.
        - simpl in CODEOPT. simpl in ANCHOR. simpl in ANCCODE. rewrite ANCHOR in ANCCODE. inv ANCCODE.
          eapply deoptstate_match; eauto.
          rewrite GETDEF in DEF0. eapply defined_deopt_subset_agree in DEF0 as DEF0'; eauto.
          2: { intros r IN. apply PositiveSet.inter_spec in IN as [IN _]. eauto. }
          destruct DEF0' as [rmdeopt [UPDATE' AGREE]].
          eapply deopt_subset_agree in BUILD as AGREE'; eauto.
          2: { intros r IN. apply PositiveSet.inter_spec in IN as [IN _]. auto. }
          intros r IN.
          destruct (PositiveSet.mem r rs_def) eqn:Emem.
          + symmetry. apply AGREE'. apply PositiveSet.inter_spec. split; auto.
          + assert (rms ! r = None).
            { unfold defined in DEF0. specialize (DEF0 r).
              rewrite <- PositiveSet.mem_spec in DEF0.
              rewrite Emem in DEF0. destruct (rms ! r) eqn:Er; auto.
              assert (exists v, Some i = Some v) by eauto.
              apply DEF0 in H. discriminate. }
            rewrite H. eapply update_not_captured; eauto.
            intros IN''. apply PositiveSet.inter_spec in IN'' as [IN'' _].
            rewrite <- PositiveSet.mem_spec in IN''.
            rewrite IN'' in Emem. discriminate. }

    + rewrite OPT in OPTV. inv OPTV. (* deoptstate_match *)
      inv STEP. simpl in TARGET. inv TARGET. simpl in BUILD_RM. inv BUILD_RM.
      simpl in FINDF. unfold set_version_funlist in FINDF. unfold find_function_ir in FINDOPTF.
      rewrite FINDOPTF in FINDF. rewrite PTree.gss in FINDF. inv FINDF. simpl.
      simpl. exists Zero. econstructor. split.
      * right. split. 2:constructor. eapply star_refl.
      * eapply deopt_match; auto. apply agree_sym. auto.
      
    + rewrite OPT in OPTV. inv OPTV. (* shift_match *)
      inv STEP.
      { eapply lowered_diagram; eauto. }
      * admit.                  (* TODO: I must reuse base_no_spec *)
      * admit.                  (* TODO: I must reuse base_no_spec *)
        (* inv DEOPT_COND.         (* Anchor steps can't happen in shift_match *) *)
        (* rewrite CODE in SAME_CODE. unfold vbase in SAME_CODE. apply (base_no_spec f) in SAME_CODE. *)
        (* exfalso. apply SAME_CODE. constructor. *)

    + rewrite OPT in OPTV. inv OPTV. (* opt_match *)
      eapply code_preservation in NOTIN as SAME_CODE; eauto.
      inv STEP.
      { eapply lowered_diagram; eauto. }
      * admit.                  (* TODO: I must reuse base_no_spec *)
      * admit.                  (* TODO: I must reuse base_no_spec *)
      (* * inv DEOPT_COND. (* Anchor steps can't happen in opt_match *) *)
      (*   rewrite CODE in SAME_CODE. unfold vbase in SAME_CODE. apply (base_no_spec f) in SAME_CODE. *)
      (*   exfalso. apply SAME_CODE. constructor. *)

    +
      rename s into stk. rename s' into stk'. rename HDO into INSERT.
      { inv STEP.                 (* refl_match *)
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
            assert (CURRENT: current_version f = vbase).
            { unfold current_version. rewrite NO_OPT. auto. }
            assert (ENTRY: ver_entry (current_version f) = ver_entry (fn_base f)).
            { unfold current_version. rewrite NO_OPT. auto. }
            destruct ms2. eapply addstk_same in CALLEE as [s [APP SAME]].
            2: apply addstk_callee.
            simpl in NOT_COMPILED. unfold n_check_compiled in NOT_COMPILED. simpl in NOT_COMPILED.
            destruct (nc!fid0) eqn:NOT; inv NOT_COMPILED.
            destruct ms3. eapply addstk_same in ARGS as [s2 [APP2 SAME2]].
            rewrite PTree.gss in GETF. inv GETF.
            2: apply addstk_get_args.
            destruct (in_or_not (ver_entry (current_version f)) l_anc) as [IN | NOTIN]. (* entry is Anchor *)
            { exists Two. econstructor. split.
              + left. apply plus_one. eapply Call_IR; eauto.
                simpl. unfold n_check_compiled. simpl. rewrite NOT. eauto.
              + simpl. rewrite current_version_set_version.  eapply anc_match; auto.
                * apply match_app; auto. apply match_app; auto.
                * eapply def_analyze_init; eauto.
                * rewrite <- ENTRY. auto. }
            { exists Zero. econstructor. split. (* entry is not Anchor *)
              + left. apply plus_one. eapply Call_IR; eauto.
                simpl. unfold n_check_compiled. simpl. rewrite NOT. eauto.
              + simpl. eapply opt_match; eauto.
                * apply match_app; auto. apply match_app; auto.
                * eapply def_analyze_init; eauto.
                * rewrite <- ENTRY. auto. }
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
            destruct (nc ! (intpos.pos_of_int i)) eqn:COMP; inv COMPILED.
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
            * exists Zero. econstructor. split. (* Returning to the base IR version after deopt *)
              ** left. apply plus_one. eapply Return_IR; eauto.
                 *** simpl. unfold n_load, sbind. simpl. eauto.
                 *** simpl. unfold n_open_stackframe. simpl. eauto.
              ** eapply deopt_match; eauto.
            * destruct (in_or_not pc l_anc) as [IN | NOTIN]. (* Returning to the opt version *)
              { exists Two. econstructor. split. 
                ** left. apply plus_one. eapply Return_IR; eauto.
                   *** simpl. unfold n_load, sbind. simpl. eauto.
                   *** simpl. unfold n_open_stackframe. simpl. eauto.
                ** eapply anc_match; eauto. }
              { exists Zero. econstructor. split.
                ** left. apply plus_one. eapply Return_IR; eauto.
                   *** simpl. unfold n_load, sbind. simpl. eauto.
                   *** simpl. unfold n_open_stackframe. simpl. eauto.
                ** eapply opt_match; eauto. }
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
            * exists Zero. econstructor. split. (* Returning to the base IR version after deopt *)
              ** left. apply plus_one. eapply Return_IR; eauto.
                 *** simpl. eauto.
                 *** simpl. unfold n_open_stackframe. simpl. eauto.
              ** eapply deopt_match; eauto.
            * destruct (in_or_not pc l_anc) as [IN | NOTIN]. (* Returning to the opt version *)
              { exists Two. econstructor. split. 
                ** left. apply plus_one. eapply Return_IR; eauto.
                   *** simpl. unfold n_load, sbind. simpl. eauto.
                   *** simpl. unfold n_open_stackframe. simpl. eauto.
                ** eapply anc_match; eauto. }
              { exists Zero. econstructor. split.
                ** left. apply plus_one. eapply Return_IR; eauto.
                   *** simpl. unfold n_load, sbind. simpl. eauto.
                   *** simpl. unfold n_open_stackframe. simpl. eauto.
                ** eapply opt_match; eauto. }
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


    + inv STEP.                (* deopt_match *)
      { unfold ir_step, ir_int_step in STEP0. repeat sdo_ok. destruct p0.
        destruct i; repeat sdo_ok; unfold live_dr_transf in AGREE; rewrite HDO3 in AGREE.
        - exists Zero. econstructor. split.
          + left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
            rewrite HDO3. simpl. eauto.
          + apply deopt_match; eauto.
            eapply agree_transfer; eauto. simpl; auto.
        - eapply agree_eval_expr in HDO0; eauto.
          2: { apply agree_sym. eauto. }
          exists Zero. econstructor. split.
          + left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
            rewrite HDO3. simpl. rewrite HDO0. simpl. eauto.
          + apply deopt_match; eauto.
            eapply agree_transfer; eauto. simpl; auto.
            eapply expr_live_agree; eauto.
        - simpl in HDO0. repeat sdo_ok. unfold n_push_interpreter_stackframe in HDO1.
          simpl in HDO1. destruct top; inv HDO1.
          eapply agree_eval_list_reg in HDO0; eauto.
          2: { apply agree_sym; eauto. }
          exists Zero. econstructor. split.
          + left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
            rewrite HDO3. simpl. unfold n_push_interpreter_stackframe. unfold sbind.
            simpl. rewrite HDO0. simpl. eauto.
          + simpl. eapply refl_match; eauto. apply match_cons; auto.
            apply frame_deopt. intros retval.
            eapply agree_transfer; eauto. simpl; auto.
            apply agree_insert_dead.
            eapply reg_list_live_agree. eauto.
        - eapply agree_eval_reg in HDO5; eauto.
          2: { apply agree_sym. eauto. }
          destruct (bool_of_int i) eqn:COND; repeat sdo_ok.                                          
          + exists Zero. econstructor. split.
            * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
              rewrite HDO3. simpl. rewrite HDO5. simpl. rewrite COND. simpl. eauto.
            * apply deopt_match; eauto.
              eapply agree_transfer; eauto. simpl; auto. 
              eapply reg_live_agree; eauto.
          + exists Zero. econstructor. split.
            * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
              rewrite HDO3. simpl. rewrite HDO5. simpl. rewrite COND. simpl. eauto.
            * apply deopt_match; eauto.
              eapply agree_transfer; eauto. simpl; auto. 
              eapply reg_live_agree; eauto.
        - eapply agree_eval_expr in HDO0; eauto.
          2: { apply agree_sym. eauto. }
          exists Zero. econstructor. split.
          + left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
            rewrite HDO3. simpl. rewrite HDO0. simpl. eauto.
          + simpl. eapply refl_match. auto.
        - eapply agree_eval_expr in HDO0; eauto.
          2: { apply agree_sym. eauto. }
          exists Zero. econstructor. split.
          + left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
            rewrite HDO3. simpl. rewrite HDO0. simpl. eauto.
          + apply deopt_match; eauto.
            eapply agree_transfer; eauto. simpl; auto.
            apply agree_insert_dead. eapply expr_live_agree; eauto.
        - eapply agree_eval_reg in HDO5; eauto.
          2: { apply agree_sym. eauto. }
          eapply agree_eval_reg in HDO0; eauto.
          2: { apply agree_sym. eapply agree_subset; eauto. apply reg_live_subset. }
          unfold n_memset in HDO6. destruct (Integers.Int.lt i mem_size) eqn:RANGE; inv HDO6.
          exists Zero. econstructor. split.
          + left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
            rewrite HDO3. simpl. rewrite HDO0. simpl. rewrite HDO5. simpl.
            unfold n_memset. unfold sbind. rewrite RANGE. simpl. eauto.
          + apply deopt_match; eauto.
            eapply agree_transfer; eauto. simpl; auto.
            eapply reg_live_agree. eapply reg_live_agree; eauto.
        - eapply agree_eval_reg in HDO0; eauto.
          2: { apply agree_sym. eauto. }
          unfold n_memget in HDO5. destruct (Integers.Int.lt i mem_size) eqn:RANGE; inv HDO5.
          destruct (heap # (intpos.pos_of_int i)) eqn:HEAP; inv H0.
          exists Zero. econstructor. split.
          + left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
            rewrite HDO3. simpl. rewrite HDO0. simpl. 
            unfold n_memget. unfold sbind. rewrite RANGE. simpl. rewrite HEAP. simpl. eauto.
          + apply deopt_match; eauto.
            eapply agree_transfer; eauto. simpl; auto.
            apply agree_insert_dead; eauto. eapply reg_live_agree; eauto.
        - destruct d. repeat sdo_ok. eapply agree_eval_expr in HDO5; eauto.
          (* we could avoid with base_no_spec *)
          2: { apply agree_sym. eauto. }
          destruct (bool_of_int i) eqn:GUARD; repeat sdo_ok. 
          + exists Zero. econstructor. split.
            * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
              rewrite HDO3. simpl. rewrite HDO5. simpl. rewrite GUARD. simpl. eauto.
            * eapply deopt_match; auto. eapply agree_transfer; eauto.
              simpl. auto. eapply varmap_live_agree. eapply expr_live_agree; eauto.
          + eapply agree_update_regmap in HDO0; eauto.
            2: { eapply expr_live_agree; eauto. }
            exists Zero. econstructor. split.
            * left. apply plus_one. eapply IR_step. unfold ir_step, ir_int_step.
              rewrite HDO3. simpl. rewrite HDO5. simpl. rewrite GUARD. rewrite HDO0. simpl. eauto.
            * simpl. eapply refl_match; auto.
        - destruct d. inv HDO0. }
      * admit.                   (* base no spec *)
      * admit.                   (* base no spec *)
Admitted.
