(* Proving the correctness of generating RTL from RTLblock *)

Require Import common.
Require Import monad.
Require Import monad_impl.
Require Import Errors.
Require Import RTL.
Require Import RTLblock.
Require Import IR.
Require Import flattenRTL.
Require Import customSmallstep.
Require Import internal_simulations.
Require Import sem_properties.
Require Import backend.
Require Import Globalenvs.
Require Import Values.
Require Import Integers.
Require Import IRtoRTLblock.
Require Import Op.
Require Import Integers.

(** * Simple lemmas *)
Lemma same_id:
  forall rtlb rtl,
    flatten rtlb = OK rtl ->
    prtl_id (Some (inr rtlb)) = prtl_id (Some (inl rtl)).
Proof.
  destruct rtlb as  (((fid, code), entry), ci).
  unfold flatten; intros rtl Hf.
  do_ok.
  destruct p; inv H0.
  reflexivity.
Qed.

Lemma same_cont_idx:
  forall i c e cont_ind i' c' e' cont_ind',
    flatten (i, c, e, cont_ind) = OK (i', c', e', cont_ind') ->
    cont_ind = cont_ind'.
Proof.
  intros i c e cont_ind i' c' e' cont_ind' H. unfold flatten in H.
  repeat do_ok. destruct p. inv H1. auto.
Qed.

Lemma same_entry:
  forall i c e cont_ind i' c' e' cont_ind',
    flatten (i, c, e, cont_ind) = OK (i', c', e', cont_ind') ->
    e = e'.
Proof.
  intros i c e cont_ind i' c' e' cont_ind' H. unfold flatten in H.
  repeat do_ok. destruct p. inv H1. auto.
Qed.

(** * Positive arithmetic  *)
Lemma inv_lt:
  forall p,
    (p < p)%positive -> False.
Proof.
  intros p H. eapply Pos.lt_irrefl. eauto.
Qed.

Lemma inv_succ:
  forall p,
    (Pos.succ p <= p)%positive -> False.
Proof.
  intros p H. rewrite Pos.le_succ_l in H. eapply inv_lt; eauto.
Qed.

Lemma succ_le:
  forall p l,
    (Pos.succ p <= l)%positive ->
    (p <= l)%positive.
Proof.
  intros p l H. eapply Pos.le_trans; eauto. apply Pos.lt_le_incl. apply Pos.lt_succ_diag_r.
Qed.

Lemma succ_le_lt:
  forall p l,
    (Pos.succ p <= l)%positive ->
    (p < l)%positive.
Proof.
  lia.
Qed.

Lemma le_succ:
  forall p l,
    (p <= l)%positive ->
    (p <= Pos.succ l)%positive.
Proof.
  intros p l H. eapply Pos.le_trans; eauto. apply Pos.lt_le_incl. apply Pos.lt_succ_diag_r.
Qed.

Lemma lt_succ:
  forall p l,
    (p < l)%positive ->
    (p < Pos.succ l)%positive.
Proof.
  intros p l H. eapply Pos.lt_trans; eauto. apply Pos.lt_succ_diag_r.
Qed.

Lemma succ_lt:
  forall p l,
    (Pos.succ p < l)%positive ->
    (p < l)%positive.
Proof.
  intros p l H. eapply Pos.lt_trans; eauto. apply Pos.lt_succ_diag_r.
Qed.

Lemma lt_le:
  forall p1 p2,
    (p1 < p2)%positive ->
    (p2 <= p1)%positive ->
    False.
Proof.
  intros p1 p2 H H0. assert (p1 < p1)%positive.
  { eapply Pos.lt_le_trans; eauto. }
  eapply inv_lt; eauto.
Qed.


(** * BLOCK Representation  *)
(* representing that some blocks have been unfolded in the rtl code *)


(* expressing that some list of instructions is in rtlc at label pc, ending on next *)
Inductive unf_list: RTL.code -> list block_instr -> positive -> positive -> Prop :=
| unf_nil: forall rtlc pc,   
    unf_list rtlc nil pc pc
| unf_cons: forall rtlc pc next bi l (i:RTL.instruction)
              (TRANSF_INSTR: basic_transf_block_instr bi (Pos.succ pc) = i)
              (FIRST: rtlc # pc = Some i)
              (NEXT: unf_list rtlc l (Pos.succ pc) next),
    unf_list rtlc (bi::l) pc next.

(* Expressing that some basic block is in rtlc at label pc *)
Inductive unf_bb: RTL.code -> basic_block -> positive -> Prop :=
| unf_basic: forall rtlc pc next li exiti e
               (LIST: unf_list rtlc li pc next)
               (TRANSF_EXIT: basic_transf_exit_instr exiti = e) 
               (EXIT: rtlc # next = Some e),
    unf_bb rtlc (li, exiti) pc.

(* Expressing that some block is in rtlc at label pc *)
Inductive unf_block: RTL.code -> RTLblock.block -> positive -> Prop :=
| unf_bblock: forall rtlc pc bb next
                (BB: unf_bb rtlc bb next)
                (NOP: rtlc # pc = Some (Inop next)),
    unf_block rtlc (Bblock bb) pc
| unf_cblock: forall rtlc pc op args iftrue bb next
                (BB: unf_bb rtlc bb (Pos.succ next))
                (EVAL: rtlc # pc = Some (Iop op args guard_reg next))
                (COND: rtlc # next = Some (Icond (Ccompimm Ceq Int.zero) (guard_reg::nil) (Pos.succ next) iftrue)),
    unf_block rtlc (Cblock op args iftrue bb) pc.

(** * Code Generation Invariants  *)
(* Everything above the fresh label is undefined *)
Definition fresh (fsh:positive) (rtlc:RTL.code) :=
  forall l, (fsh <= l)%positive -> rtlc # l = None.

(* basic inclusion, for what's above the fresh label *)
Definition included (rtlc1 rtlc2:RTL.code) :=
  forall pc i, rtlc1 # pc = Some i -> rtlc2 # pc = Some i.

(* preservation of what's under the fresh label *)
Definition preserved (rtlc1 rtlc2:RTL.code) (fsh:positive) :=
  forall x, (x < fsh)%positive -> rtlc1 # x = rtlc2 # x.

(* When doing the PTree.fold, everything under fresh is set 1 by 1, only changing the current pc *)
Definition preserved_but (rtlc1 rtlc2:RTL.code) (fsh pc:positive) :=
  forall x, (x < fsh)%positive ->
       x <> pc ->
       rtlc1 # x = rtlc2 # x.

(* invariants lemmas *)
Lemma preserved_refl:
  forall r f,
    preserved r r f.
Proof.
  unfold preserved. intros r f x H. auto.
Qed.

Lemma unf_list_set:
  forall rtlc li pc next pcset i,
    unf_list rtlc li pc next ->
    fresh pcset rtlc ->
    unf_list (rtlc # pcset <- i) li pc next.
Proof.
  intros rtlc li pc next pcset i H H0. induction H.
  - constructor.
  - econstructor; eauto. rewrite PTree.gso; auto.
    intros EQ. subst. specialize (H0 _ (Pos.le_refl pcset)). rewrite FIRST in H0. inv H0.
Qed.

Lemma included_refl:
  forall rtlc, included rtlc rtlc.
Proof.
  unfold included. intros rtlc pc i H. auto.
Qed.

Lemma included_trans:
  forall r1 r2 r3,
    included r1 r2 -> included r2 r3 -> included r1 r3.
Proof.
  unfold included. intros r1 r2 r3 H H0 pc i H1. eapply H0. eapply H. auto.
Qed.

Lemma included_set:
  forall pc r i,
    fresh pc r ->
    included r (r # pc <- i).
Proof.
  unfold included, fresh. intros pc r i H pc0 i0 H0. rewrite PTree.gso. auto.
  intros EQ. subst. specialize (H _ (Pos.le_refl pc)). rewrite H in H0. inv H0.
Qed.

Lemma unf_list_inc:
  forall r1 li pc next r2,
    included r1 r2 ->
    unf_list r1 li pc next ->
    unf_list r2 li pc next.
Proof.
  intros r1 li pc next r2 H H0. induction H0.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma unf_bb_inc:
  forall r1 bb pc r2,
    included r1 r2 ->
    unf_bb r1 bb pc ->
    unf_bb r2 bb pc.
Proof.
  intros r1 bb pc r2 H H0. inv H0. econstructor; eauto.
  eapply unf_list_inc; eauto.
Qed.

Lemma unf_block_inc:
  forall r1 b pc r2,
    included r1 r2 ->
    unf_block r1 b pc ->
    unf_block r2 b pc.
Proof.
  intros r1 b pc r2 H H0. inv H0.
  - econstructor; eauto. eapply unf_bb_inc; eauto.
  - econstructor; eauto. eapply unf_bb_inc; eauto.
Qed.    


(** * Initial correctness of the transformations  *)
Lemma tbb_init_ok:
  forall r1 bb r2,
    transf_basic_block r1 bb = OK r2 ->
    exists rtlc1 pc, r1 = OK (rtlc1, pc).
Proof.
  intros r1 bb r2 H. unfold transf_basic_block in H. destruct bb.
  generalize dependent r1. induction l; intros.
  - inv H. unfold transf_exit_instr in H1. repeat do_ok. destruct p. inv H0. eauto.
  - simpl in H. apply IHl in H as [rtlc1 [pc H]]. unfold transf_block_instr in H. repeat do_ok.
    destruct p. inv H1. eauto.
Qed.

Lemma tei_init_ok:
  forall r1 ei r2,
    transf_exit_instr r1 ei = OK r2 ->
    exists rtlc1 pc, r1 = OK (rtlc1, pc).
Proof.
  intros r1 ei r2 H. unfold transf_exit_instr in H. repeat do_ok. destruct p. inv H1. eauto.
Qed.

Lemma tb_init_ok:
  forall r1 pc b r2,
    transf_block r1 pc b = OK r2 ->
    exists rtlc1 pc, r1 = OK (rtlc1, pc).
Proof.
  intros r1 pc b r2 H. unfold transf_block in H. destruct b.
  - repeat do_ok. destruct p. apply tbb_init_ok in H1 as H'. destruct H' as [r1 [l INIT]].
    inv INIT. eauto.
  - repeat do_ok. destruct p. apply tbb_init_ok in H1 as H'. destruct H' as [r1 [l' INIT]].
    inv INIT. eauto.
Qed.

Lemma fold_left_init_ok:
  forall l r1 r2,
    fold_left (fun a p => transf_block a (fst p) (snd p)) l r1 = OK (r2) ->
    exists rtlc1 pc, r1 = OK (rtlc1, pc).
Proof.
  intros l. induction l; intros.
  - simpl in H. inv H. destruct r2. eauto.
  - simpl in H. apply IHl in H as H'. destruct H' as [rtlc1 [p1 INIT]].
    apply tb_init_ok in INIT as H'. destruct H' as [rtlc' [p' INIT']]. eauto.
Qed.


(** * Incremental specifications of the transformations  *)
Lemma list_fold_ok:
  forall li rtlc1 fsh rtlc2 next,
    fold_left transf_block_instr li (OK (rtlc1, fsh)) = OK (rtlc2, next) ->
    fresh fsh rtlc1 ->
    fresh next rtlc2 /\
    (fsh <= next)%positive /\
    included rtlc1 rtlc2 /\
    preserved rtlc1 rtlc2 fsh /\
    unf_list rtlc2 li fsh next.
Proof.
  intros li. induction li; intros.
  - simpl in H. inv H. split; auto. split. apply Pos.le_refl. split.
    apply included_refl. split. apply preserved_refl. constructor. 
  - simpl in H. apply IHli in H as H'. destruct H' as [FRESH [LT [INCL [PRES UNF]]]].
    + repeat try split; auto.
      * apply succ_le. auto.
      * eapply included_trans; eauto. apply included_set; auto.
      * unfold preserved in *. intros x H1. apply lt_succ in H1 as H2. apply PRES in H2.
        rewrite PTree.gso in H2. 2: { intros EQ. subst. eapply inv_lt. eauto. } auto.
      * econstructor; eauto. apply INCL. rewrite PTree.gss. auto.
    + unfold fresh. intros l H1. rewrite PTree.gso.
      2: { intros EQ. subst. eapply inv_succ; eauto. }
      apply H0. apply succ_le. auto.
Qed.

Lemma tbb_ok:
  forall rtlc1 fsh rtlc2 next bb,
    transf_basic_block (OK (rtlc1, fsh)) bb = OK (rtlc2, next) ->
    fresh fsh rtlc1 ->
    fresh next rtlc2 /\
    (fsh <= next)%positive /\
    included rtlc1 rtlc2 /\
    preserved rtlc1 rtlc2 fsh /\
    unf_bb rtlc2 bb fsh.
Proof.
  intros rtlc1 pc rtlc2 next bb H H0. destruct bb as [li ei]. unfold transf_basic_block in H.
  apply tei_init_ok in H as H'. destruct H' as [rtlc1' [pc' FOLD]]. rewrite FOLD in H.
  apply list_fold_ok in FOLD as H'; auto. destruct H' as [FRESH [LT [INCL [PRES UNF]]]].
  unfold transf_exit_instr in H. repeat do_ok. inv HDO. inv H2. repeat try split; auto.
  - unfold fresh. intros l H. rewrite PTree.gso; auto.
    + apply FRESH. apply succ_le. auto.
    + intros EQ. subst. eapply inv_succ; eauto.
  - apply le_succ. auto.
  - eapply included_trans; eauto. apply included_set; auto.
  - unfold preserved in *. intros x H. apply PRES in H as H'.
    rewrite PTree.gso; auto. intros EQ. subst. eapply lt_le; eauto.
  - eapply unf_basic with (next:=pc'); eauto.
    + apply unf_list_set; auto.
    + rewrite PTree.gss. auto.
Qed.

Lemma tb_ok:
  forall rtlc1 fsh pc rtlc2 next b,
    transf_block (OK (rtlc1, fsh)) pc b = OK (rtlc2, next) ->
    fresh fsh rtlc1 ->
    (pc < fsh)%positive ->
    rtlc1 # pc = None ->
    fresh next rtlc2 /\
    (fsh <= next)%positive /\
    included rtlc1 rtlc2 /\
    preserved_but rtlc1 rtlc2 fsh pc /\
    unf_block rtlc2 b pc.
Proof.
  intros rtlc1 fsh pc rtlc2 next b H H0 H1 H2. destruct b.
  - apply tbb_ok in H as H'. destruct H' as [FRESH [LT [INCL [PRES UNF]]]].
    2: { unfold fresh; intros. rewrite PTree.gso. apply H0. auto.
         intros EQ. subst. eapply lt_le; eauto. }
    repeat try split; auto.
    + eapply included_trans; eauto. unfold included.
      intros pc0 i H3. rewrite PTree.gso; auto. intros EQ. subst. rewrite H2 in H3. inv H3.
    + unfold preserved_but. intros x H3 H4. apply PRES in H3 as H'. rewrite PTree.gso in H'; auto.
    + eapply unf_bblock; eauto. apply INCL. rewrite PTree.gss. auto.
  - apply tbb_ok in H as H'. destruct H' as [FRESH [LT [INCL [PRES UNF]]]].
    2: { unfold fresh; intros. apply succ_le_lt in H3. 
         rewrite PTree.gso; try lia. rewrite PTree.gso; try lia. apply H0. lia. }
    repeat try split; auto.
    + lia.
    + eapply included_trans; eauto. unfold included.
      intros pc0 i H3.
      rewrite PTree.gso. 2: { intros EQ. subst. rewrite H0 in H3. inv H3. lia. }
      rewrite PTree.gso. 2: { intros EQ. subst. rewrite H3 in H2. inv H2. }
      auto.
    + unfold preserved_but. intros x H3 H4. assert ((x < Pos.succ fsh)%positive) by lia.
      apply PRES in H5 as H'.
      rewrite PTree.gso in H' by lia. rewrite PTree.gso in H' by lia. auto.
    + eapply unf_cblock; eauto.
      * apply INCL. rewrite PTree.gso by lia. rewrite PTree.gss. auto.
      * apply INCL. rewrite PTree.gss. auto.
Qed.

Lemma flatten_fold_ok:
  forall l rtlc1 rtlc2 fsh next,
    list_norepet (map fst l) ->
    fold_left (fun a p => transf_block a (fst p) (snd p)) l (OK (rtlc1, fsh)) = OK (rtlc2, next) ->
    fresh fsh rtlc1 ->
    (forall x, In x (map fst l) -> (x < fsh)%positive) ->
    (forall x, In x (map fst l) -> rtlc1 # x = None) ->
    fresh next rtlc2 /\
    (fsh <= next)%positive /\
    included rtlc1 rtlc2 /\
    forall pc blk, In (pc, blk) l -> unf_block rtlc2 blk pc.
Proof.
  intros l. induction l; intros.
  - simpl in H0. inv H0. split; try split; try split; auto.
    + apply Pos.le_refl.
    + apply included_refl.
    + intros pc blk H0. inv H0.
  - inv H. destruct a as [pc blk]. simpl in *.
    apply fold_left_init_ok in H0 as H'. destruct H' as [rtlc' [fsh' INIT]].
    apply tb_ok in INIT as H'; auto. destruct H' as [FRESH [LT [INCL [PRES UNF]]]].
    rewrite INIT in H0. apply IHl in H0 as H'; auto. destruct H' as [FRESH' [LT' [INCL' UNF']]].
    2: { intros x H. eapply Pos.lt_le_trans; eauto. }
    2: { intros y H. rewrite <- PRES; auto. intros EQ. subst. apply H6. apply H. }
    split; try split; try split; auto.
    + eapply Pos.le_trans; eauto.
    + eapply included_trans; eauto.
    + intros pc0 blk0 H. destruct H.
      * inv H. eapply unf_block_inc; eauto.
      * apply UNF'. auto.
Qed.

Lemma in_map:
  forall X Y l (x:X),
    In x (map fst l) ->
    exists (y:Y), In (x,y) l.
Proof.
  intros X Y l x H. induction l; inv H.
  - destruct a. exists y. simpl. left. auto.
  - apply IHl in H0. destruct H0. exists x0. simpl. right. auto.
Qed.

(** * Final code preservation theorem  *)
Lemma flatten_ok:
  forall id entry cont blkc rtlc pc blk,
    flatten (id, blkc, entry, cont) = OK (id, rtlc, entry, cont) ->
    blkc # pc = Some blk ->
    unf_block rtlc blk pc. 
Proof.
  intros id entry cont blkc rtlc pc blk H H0. unfold flatten in H. repeat do_ok.
  rewrite PTree.fold_spec in HDO. destruct p as [blkc' next]. inv H2.
  apply flatten_fold_ok in HDO as H'. destruct H' as [FRESH [LT [INCL BLK]]].
  - apply BLK. apply PTree.elements_correct. auto.
  - apply PTree.elements_keys_norepet.
  - unfold fresh. intros. rewrite PTree.gempty. auto.
  - intros. unfold fresh_label, max_label.
    apply in_map in H. destruct H as [y IN].
    apply PTree.elements_complete in IN.
    apply max_pos_correct in IN.
    eapply Pos.le_lt_trans; eauto. apply Pos.lt_succ_diag_r.
  - intros x H. rewrite PTree.gempty. auto.
Qed.  


(** * Simulation Invariant, order, index  *)

Definition match_states_is_refl (s:synchro_state) : Prop :=
  match s with
  | Halt_RTL _ _ | Halt_Block _ => False
  | _ => True
  end.

  

(* The index holds the current entry  *)
(* This can be the entry point of a continuation, so it changes along the simulation *)
(* We also include a boolean for the stuttering step of the Cblock *)

Inductive stutter : Type :=
| ONE: stutter
| ZERO: stutter.
Definition index : Type := (positive * stutter).

Inductive order: index -> index -> Prop :=
| stut: forall i,
    order (i, ZERO) (i, ONE).

Lemma order_wf:
  well_founded order.
Proof.
  unfold well_founded. intros a. constructor. intros y H. inv H. constructor. intros y H. inv H.
Qed.


Inductive match_states (p:program) (rtlc:RTL.code): index -> mixed_sem.mixed_state -> mixed_sem.mixed_state -> Prop :=
| ms_refl s m entry: match_states_is_refl s -> match_states p rtlc (entry,ONE) (s, m) (s,m)
| ms_block f stk pc mrtl ge m lbi exb rs next entry
    (GE: ge = Globalenvs.Genv.globalenv (make_prog rtlc entry))
    (FUN: f = make_fun rtlc entry)
    (UNF: unf_list rtlc lbi pc next)
    (EXIT: rtlc # next = Some (basic_transf_exit_instr exb)):
  match_states p rtlc (entry, ONE) (Halt_Block (BState (Bblock (lbi, exb)) rs), m)
                                   (Halt_RTL ge (State nil f (Vptr stk Ptrofs.zero) pc rs mrtl), m)
| ms_cblock f stk pc mrtl ge m rs next entry deoptbb cond args iftrue
    (GE: ge = Globalenvs.Genv.globalenv (make_prog rtlc entry))
    (FUN: f = make_fun rtlc entry)
    (COND: rtlc # next = Some (Icond (Ccompimm Ceq Int.zero) [guard_reg] (Pos.succ next) iftrue))
    (EVAL: rtlc # pc = Some (Iop cond args guard_reg next))
    (UNF: unf_bb rtlc deoptbb (Pos.succ next)):
    match_states p rtlc (entry, ZERO) (Halt_Block (BState (Cblock cond args iftrue deoptbb) rs), m)
                                      (Halt_RTL ge (State nil f (Vptr stk Ptrofs.zero) pc rs mrtl), m)
| ms_bpf f stk pc mrtl ge m rs entry
  (GE: ge = Globalenvs.Genv.globalenv (make_prog rtlc entry))
  (FUN: f = make_fun rtlc entry):
  match_states p rtlc (entry, ONE)  (Halt_Block (BPF pc rs), m)
                                    (Halt_RTL ge (State nil f (Vptr stk Ptrofs.zero) pc rs mrtl), m)
| ms_final r mrtl ge m entry
  (GE: ge = Globalenvs.Genv.globalenv (make_prog rtlc entry)):
  match_states p rtlc (entry, ONE) (Halt_Block (BFinal r), m)
                                   (Halt_RTL ge (Returnstate nil (Vint r) mrtl), m).

Require Import mixed_sem.

Lemma simul_one_step_is_sufficient :
  forall L,
  forall Order:Prop,
  forall match_states: state L -> state L -> Prop,
  forall s t s0,
    (exists s', (Step L s t s' /\ match_states s0 s')) ->
    exists s',
      (SPlus L s t s' \/ (Star L s t s' /\ Order)) /\ match_states s0 s'.
Proof.
  intros L Order ms s t s0 (s', (T1, T2)).
  exists s'; split; auto.
  left.
  constructor 1 with t s' nil; simpl; eauto.
  - constructor 1.
  - unfold Events.Eapp.
    rewrite app_nil_r.
    reflexivity.
Qed.

Ltac inv_not_true:=
  match goal with
  | [H: ~ True |- _] => exfalso; apply H; auto
  end.

(** * Axiomatization of existing initial states for the functions we generate *)
(* There exists an initial memory where the globals (the JIT primitive and the main function) have been *)
(* installed. In practice, this is not in the memory handled by CompCert, but CompCert has no view of *)
(* the external memory *)
Axiom external_in_memory:
  forall rtlc entry,
  exists initm,
    Genv.alloc_globals (Genv.globalenv (make_prog rtlc entry)) Memory.Mem.empty
                       (AST.prog_defs (make_prog rtlc entry)) = Some initm.

Lemma initial_rtl_exists:
  forall rtlc entry,
    exists r, RTL.initial_state (backend.make_prog rtlc entry) r.
Proof.
  intros rtlc entry.
  specialize (external_in_memory rtlc entry) as [initm INITMEM].
  econstructor. eapply initial_state_intro with (b:=backend.main_id) (m0:=initm); unfold backend.make_prog; simpl.
  - unfold Globalenvs.Genv.init_mem. auto.
  - unfold Globalenvs.Genv.find_symbol. simpl. eauto.
  - unfold Globalenvs.Genv.find_funct_ptr. simpl. eauto.
  - simpl. auto.
Qed.
      
Lemma block_eval_condition_exists_eval_condition mrtl c args b:
  block_eval_condition c args = Some b ->
  Op.eval_condition c args mrtl = Some b.
Proof.
  unfold block_eval_condition.
  destruct c; try congruence;
    repeat (destruct args; try congruence);
    simpl; auto.
Qed.


(** *  Globalenv lemmas *)
Lemma find_ex_prim:
  forall rtlc entry prim rs,
    find_function (Globalenvs.Genv.globalenv (make_prog rtlc entry)) (inr (primitives.EF_ident prim)) rs
    = Some (AST.External (AST.EF_runtime (primitives.EF_name prim) (primitives.EF_sig prim))).
Proof.
  intros rtlc entry prim rs.
  unfold make_prog, Globalenvs.Genv.globalenv. simpl.
  unfold Genv.find_symbol. unfold Genv.genv_symb, Genv.find_funct_ptr. simpl.
  destruct prim; simpl; eauto.
Qed.


Lemma find_main:
  forall rtlc entry b f,
    Genv.find_symbol (Genv.globalenv (make_prog rtlc entry)) main_id = Some b ->
    Genv.find_funct_ptr (Genv.globalenv (make_prog rtlc entry)) b = Some f ->
    f = AST.Internal (make_fun rtlc entry).
Proof.
  unfold make_prog. intros rtlc entry b f H H0.
  unfold Genv.find_symbol, Genv.genv_symb, Genv.globalenv in H.
  simpl in H. inv H.
  unfold Genv.find_funct_ptr, Genv.find_def, Genv.globalenv in H0. simpl in H0. inv H0. auto.
Qed.

(* Freeing of size 0 *)
Lemma free_0:
  forall m stk, exists m',
    Memory.Mem.free m stk 0 0 = Some m'.
Proof.
  intros m stk. Transparent Memory.Mem.free. unfold Memory.Mem.free.
  destruct (Memory.Mem.range_perm_dec m stk 0 0 Memtype.Cur Memtype.Freeable) eqn:FREE.
  - unfold Memory.Mem.unchecked_free. destruct m. simpl.  eauto.    
  - unfold Memory.Mem.range_perm in n. exfalso. apply n. intros ofs H. inv H. lia.
    Opaque Memory.Mem.free.
Qed.
  

(** * Forward Simulation  *)
Theorem flatten_forward:
  forall (p:program) (nc:asm_codes) (rtlb:RTLblockfun) (rtl:RTLfun)
    (NO_CONFLICT: ~ rtl_conflict (Some (inr rtlb)) nc) (* nc doesn't contain a function fid *)
    (FLATTEN: flatten rtlb = OK rtl),
    forward_internal_simulation p p (Some (inr rtlb)) (Some (inl rtl)) nc nc AnchorOff AnchorOff.
Proof.
  intros p nc rtlb rtl; intros.
  destruct rtl as [[[rtlfid rtlc] rtlentry] rtlcont].
  destruct rtlb as [[[fid blockc] entry] cont].
  assert (rtlfid = fid). { apply same_id in FLATTEN. inv FLATTEN. auto. } subst rtlfid.
  apply same_cont_idx in FLATTEN as SAME. subst rtlcont.
  apply same_entry in FLATTEN as SAME. subst rtlentry.
  
  eapply Forward_internal_simulation with (fsim_match_states:=match_states p rtlc) (fsim_order := order).
  - apply order_wf.
  - unfold call_refl, p_reflexive. intros s H.
    exists (entry, ONE). destruct s. eapply ms_refl. inv H. constructor.
  - intros p0 s1 s2 r Hm Hf1.
    inv Hm; auto; inv Hf1.
  -
{ intros s1 t s1' STEP i s2 MATCH. inv MATCH.
  - destruct s1' as (s', m').
      assert (M:match_states_is_refl s' \/ ~ match_states_is_refl s').
      { destruct s'; simpl; intuition. }
      destruct M.
    + exists (xH, ONE). apply simul_one_step_is_sufficient. exists (s', m').
        split; [idtac | econstructor 1; eauto].        
        inv STEP; try (elim H; fail); try (elim H0; fail); econstructor; eauto. 
    + inv STEP; try solve[inv H]; simpl in H0; try inv_not_true; try inv RTL.
        (* interpreter can't produce RTL states *)
        { unfold IRinterpreter.ir_step in STEP0. rewrite exec_bind2 in STEP0. simpl in STEP0.
          repeat sdo_ok. destruct p0. destruct i; simpl in H0; try inv_not_true.
          destruct c; simpl in H0; try inv_not_true. }
        (* ASM can't produce RTL states *)
        { unfold ASMinterpreter.asm_int_step in STEP0. rewrite exec_bind2 in STEP0. simpl in STEP0.
          repeat sdo_ok. destruct p0. destruct i; simpl in STEP0; repeat sdo_ok; simpl in H0; try inv_not_true.
          destruct c; simpl in H0; try inv_not_true. }
      * inv RTL_BLOCK.  (* calling RTLBLOCK *)
        exists (entry1, ONE).
        specialize (initial_rtl_exists rtlc entry1) as [inits INIT].
        { inv INIT.
          apply find_main in H3 as MAIN; auto. subst f.
          destruct (Memory.Mem.alloc m0 0 0) as [m0' stk] eqn:E.
          (* Going into the entry program *)
          econstructor; esplit.
          - left. simpl. eapply plus_two.
            + eapply Call_RTL; eauto. econstructor; eauto.
            + eapply rtl_step; eauto.
              * intro T; inv T.
              * eapply exec_function_internal; eauto.
            + reflexivity.
          - simpl. constructor; auto. }
      * inv RTL_BLOCK. (* returning to RTLBLOCK *)
        specialize (initial_rtl_exists rtlc cont_entry) as [inits INIT].
        { inv INIT.
          apply find_main in H3 as MAIN; auto. subst f.
          destruct (Memory.Mem.alloc m0 0 0) as [m0' stk] eqn:E .
          exists (cont_entry, ONE).      (* going into continuation *)
          econstructor; esplit.
          - left. simpl. eapply plus_two.
            + eapply Return_RTL; eauto. econstructor; eauto.
               + eapply rtl_step; eauto.
                 * intro T; inv T.
                 * eapply exec_function_internal; eauto.
               + reflexivity.
          - simpl. constructor; auto. }
    
  - inv STEP.                   (* ms_block *)
    destruct lbi.
    + inv UNF.                  (* exit instruction *)
      simpl in BLOCK. exists (entry0, ONE). destruct exb.
      * inv BLOCK. econstructor. split. (* nop *)
        ** left. apply plus_one. econstructor. 
           { intros H. inv H. simpl in BUILTIN. rewrite BUILTIN in EXIT. inv EXIT. }
           eapply exec_Inop. simpl. eauto.
        ** constructor; auto.
      * repeat sdo_ok. econstructor. split. (* cond *)
        ** left. apply plus_one. econstructor.
           { intros H. inv H. simpl in BUILTIN. rewrite BUILTIN in EXIT. inv EXIT. }
           eapply exec_Icond; eauto. apply eval_condition_correct. eauto.
        ** constructor; auto.
      * assert (HMEM: exists m',  Memory.Mem.free mrtl stk 0 0 = Some m') by apply free_0.
        destruct HMEM as [m' HMEM]. repeat sdo_ok.
        unfold get_int_reg in HDO0. destruct (rs !! r) eqn:GET; inv HDO0.
        repeat sdo_ok. econstructor. split. (* return *)
        ** left. apply plus_one. econstructor.
           { intros H. inv H. simpl in BUILTIN. rewrite BUILTIN in EXIT. inv EXIT. }
           eapply exec_Ireturn; eauto.
        ** unfold Registers.regmap_optget. rewrite GET. constructor. auto.

    + inv UNF.                  (* peeling off one instruction of the block *)
      simpl in BLOCK. repeat sdo_ok. destruct b; simpl in FIRST; simpl in HDO.
      * repeat sdo_ok. eapply eval_operation_correct in HDO. (* Op *)
        exists (entry0, ONE). econstructor. split.
        ** left. apply plus_one. simpl. econstructor.
           { intros H. inv H. simpl in BUILTIN. rewrite BUILTIN in FIRST. inv FIRST. }
           eapply exec_Iop; eauto.
        ** simpl. eapply ms_block; eauto.
      * assert (A: find_function (Globalenvs.Genv.globalenv (make_prog rtlc entry0)) (inr (primitives.EF_ident e)) rs = Some (AST.External (AST.EF_runtime (primitives.EF_name e) (primitives.EF_sig e))) ).
        { apply find_ex_prim. }
        repeat sdo_ok. destruct p1. exists (entry0, ONE). econstructor. split. (* prim call *)
        ** left. eapply plus_three.
           *** eapply rtl_step.
               { intros H. inv H. simpl in BUILTIN. rewrite BUILTIN in FIRST. inv FIRST. }
               eapply exec_Icall; eauto. 
           *** eapply RTL_prim. eapply HDO0.
           *** eapply rtl_step.
               { intros H. inv H. }
               eapply exec_return.
           *** simpl. rewrite Events.E0_right. auto.
        ** simpl. eapply ms_block; eauto.

  - exists (entry0, ONE). inv UNF. inv STEP. (* ms_cblock *)
    simpl in BLOCK. repeat sdo_ok.
    eapply eval_operation_correct in HDO0; eauto.
    destruct b.
    + inv BLOCK. econstructor. split.
      * left. eapply plus_two with (t1:=nil) (t2:=nil); auto.
        { eapply rtl_step.
          { intros H. inv H. simpl in BUILTIN. rewrite BUILTIN in EVAL. inv EVAL. }
          eapply exec_Iop; eauto. }
        eapply rtl_step.
        { intros H. inv H. simpl in BUILTIN. rewrite BUILTIN in COND. inv COND. }
        eapply exec_Icond; eauto. simpl. rewrite Registers.Regmap.gss. apply HDO1.
      * simpl. eapply ms_block; eauto.
    + inv BLOCK. econstructor. split.
      * left. eapply plus_two with (t1:=nil) (t2:=nil); auto.
        { eapply rtl_step.
          { intros H. inv H. simpl in BUILTIN. rewrite BUILTIN in EVAL. inv EVAL. }
          eapply exec_Iop; eauto. }
        eapply rtl_step.
        { intros H. inv H. simpl in BUILTIN. rewrite BUILTIN in COND. inv COND. }
        eapply exec_Icond; eauto. simpl. rewrite Registers.Regmap.gss. apply HDO1.
      * eapply ms_bpf; eauto.

  - inv STEP.                   (* ms_bpf *)
    simpl in BLOCK. repeat sdo_ok.
    eapply flatten_ok in FLATTEN as H; eauto. inv H.
    + exists (entry0, ONE). econstructor. split.      (* going into Bblock *)
      * left. apply plus_one. apply rtl_step.
        { intros H. inv H. simpl in BUILTIN. rewrite BUILTIN in NOP. inv NOP. }
        eapply exec_Inop; eauto.
      * destruct bb. inv BB. eapply ms_block; eauto.
    + exists (entry0, ZERO). inv BB. econstructor. split.      (* going into Cblock *)
      * right. split. 2: { apply stut. } eapply star_refl. (* stuttering *)
      * eapply ms_cblock; eauto. econstructor; eauto. 

  - inv STEP.                   (* ms_final *)
    { simpl in BLOCK. inv BLOCK. }
    exists (entry0, ONE). econstructor. split.
    + left. eapply plus_one.
      eapply RTL_end; eauto. constructor.
    + apply ms_refl. destruct cp; simpl; auto. }
Qed.


Theorem flatten_correct:
  forall (p:program) (nc:asm_codes) (rtlb:RTLblockfun) (rtl:RTLfun)
    (NO_CONFLICT: ~ rtl_conflict (Some (inr rtlb)) nc) 
    (FLATTEN: flatten rtlb = OK rtl),
    backward_internal_simulation p p (Some (inr rtlb)) (Some (inl rtl)) nc nc AnchorOff AnchorOff.
Proof.
  intros p nc rtlb rtl NO_CONFLICT FLATTEN.
  apply forward_to_backward_simulation.
  - apply flatten_forward; auto.
  - apply mixed_receptive.
  - apply mixed_determinate. unfold not. intros H.
    apply NO_CONFLICT. inv H. apply same_id in FLATTEN. destruct rtlb as [[[fid' blk] ent] cont].
    simpl in FLATTEN. inv FLATTEN. eapply conflict; eauto.
Qed.



(** * We show here that we only produce a subset of RTL *)
Require Import primitives.
Require Import Errors.


Inductive rtl_instr_wf : RTL.instruction -> Prop :=
(* no load, no store, no builtin, no jumptable *)
| inop_wf: forall n, rtl_instr_wf (Inop n)
| iop_wf: forall o l r n, rtl_instr_wf (Iop o l r n)
| icond_wf: forall o l n1 n2, rtl_instr_wf (Icond o l n1 n2)
(* calls are limited to primitives *)
| icall_wf: forall (ef:ext_primitive) l r n,
    rtl_instr_wf (Icall (EF_sig ef) (inr (EF_ident ef)) l r n)
| ireturn_wf: forall r, rtl_instr_wf (Ireturn (Some r)).

Definition rtl_code_wf (c:RTL.code): Prop :=
  forall pc i, c#pc = Some i -> rtl_instr_wf i.


Lemma fold_ok:
  forall l cf1 c2 n,
    fold_left (fun a p => transf_block a (fst p) (snd p)) l cf1 = OK (c2, n) ->
    exists cf, cf1 = OK (cf).
Proof.
  intros l. induction l; intros.
  - simpl in H. inv H. eauto.
  - simpl in H. apply IHl in H. destruct H as [cf OK].
    destruct cf1; eauto.
    unfold transf_block in OK. destruct a as [na [b1 | b2]];  inv OK.
Qed.

Lemma transf_basic_ok:
  forall b c1 f1 c2 f2,
    transf_basic_block (OK (c1, f1)) b = OK (c2, f2) ->
    rtl_code_wf c1 ->
    rtl_code_wf c2.
Proof.
  intros [l e]. induction l; intros.
  - simpl in H. inv H. unfold rtl_code_wf in *. unfold basic_transf_exit_instr. destruct e; intros.
    + poseq_destr pc f1.
      * rewrite PTree.gss in H. inv H. constructor.
      * rewrite PTree.gso in H; auto. apply H0 in H. auto.
    + poseq_destr pc f1.
      * rewrite PTree.gss in H. inv H. constructor.
      * rewrite PTree.gso in H; auto. apply H0 in H. auto.
    + poseq_destr pc f1.
      * rewrite PTree.gss in H. inv H. constructor.
      * rewrite PTree.gso in H; auto. apply H0 in H. auto.
  - simpl in H. eapply IHl in H; eauto. unfold rtl_code_wf in *. destruct a; intros.
    + poseq_destr pc f1.
      * rewrite PTree.gss in H1. inv H1. constructor.
      * rewrite PTree.gso in H1; auto. apply H0 in H1. auto.
    + poseq_destr pc f1.
      * rewrite PTree.gss in H1. inv H1. constructor.
      * rewrite PTree.gso in H1; auto. apply H0 in H1. auto.
Qed.

Lemma transf_block_ok:
  forall c1 f1 l b c2 f2,
    transf_block (OK (c1, f1)) l b = OK (c2, f2) ->
    rtl_code_wf c1 ->
    rtl_code_wf c2.
Proof.
  intros c1 f1 l b c2 f2 H H0. unfold transf_block in H.
  destruct b.
  + repeat do_ok. inv HDO. apply transf_basic_ok in H2; auto. unfold rtl_code_wf in *. intros.
    poseq_destr pc l.
    * rewrite PTree.gss in H. inv H. constructor.
    * rewrite PTree.gso in H; auto. apply H0 in H. auto.
  + repeat do_ok. inv HDO. apply transf_basic_ok in H2; auto. unfold rtl_code_wf in *. intros.
    poseq_destr pc f1.
    * rewrite PTree.gss in H. inv H. constructor.
    * rewrite PTree.gso in H; auto. poseq_destr pc l.
      ** rewrite PTree.gss in H. inv H. constructor.
      ** rewrite PTree.gso in H; auto. apply H0 in H. auto.
Qed.


Theorem flatten_wf:
  forall rtlb fid rtlc entry cont,
    flatten rtlb = OK (fid, rtlc, entry, cont) ->
    rtl_code_wf rtlc.
Proof.
  assert (forall l fresh c1 c2 n, rtl_code_wf c1 -> fold_left (fun a p => transf_block a (fst p) (snd p)) l (OK (c1, fresh)) = OK (c2, n) -> rtl_code_wf c2). 
  { intros l.
    induction l; intros; simpl in H0. { inv H0. auto. }
    apply fold_ok in H0 as OKinit. destruct OKinit as [[c f] OK]. rewrite OK in H0.
    apply IHl in H0; auto.
    destruct a as [label blk]. simpl in OK. apply transf_block_ok in OK; auto. }
  intros [[[f blkc] ent] co] fid rtlc entry cont H1.
  unfold flatten in H1. do_ok. destruct p as [rtlc' n]. inv H2.
  rewrite PTree.fold_spec in HDO. apply H in HDO; auto.
  unfold rtl_code_wf. intros pc i H0. rewrite PTree.gempty in H0. inv H0.
Qed.
