(* Proving the correctness of the RTLblock generation *)

Require Import Values.
Require Import IRtoRTLblock.
Require Import RTL.
Require Import RTLblock.
Require Import Events.
Require Import Errors.
Require Import mixed_sem.
Require Import monad.
Require Import monad_impl.
Require Import primitives.
Require Import internal_simulations.
Require Import sem_properties.
Require Import liveness.
Require Import def_regs.
Require Import intpos.
Require Import IRinterpreter.
Require Import customSmallstep.
Require Import Registers.
Require Import IR.
Require Import common.
Require Import Coq.MSets.MSetPositive.
Require Import Lists.SetoidList.
Require Import Lia.

Lemma app_same:
  forall A (l1 l2:list A),
    l2 = l1 ++ l2 -> l1 = [].
Proof.
  intros A l1 l2 H. apply f_equal with (f:=@Datatypes.length A) in H.
  rewrite app_length in H. destruct l1; auto. simpl in H. rewrite <- plus_Sn_m in H. lia.
Qed.

Lemma cons_same:
  forall A (a:A) l,
    l = a::l -> False.
Proof.
  intros A a l H. induction l; inv H. apply IHl; auto.
Qed.

Lemma shift_inj:
  forall r1 r2,
    shift_reg r1 = shift_reg r2 ->
    r1 = r2.
Proof.
  intros r1 r2 H. unfold shift_reg in H. eapply Pos.add_reg_r. eauto.
Qed.

Lemma not_shift_eq:
  forall r1 r2,
    r1 <> r2 -> shift_reg r1 <> shift_reg r2.
Proof.
  intros r1 r2 H. intros Heq. apply shift_inj in Heq. apply H. apply Heq.
Qed.



(** * Properties of the new graph *)
Lemma fold_left_cons:
  forall A B (f:A -> B -> A) l b init,
    fold_left f (b::l) init =
    fold_left f l (f init b).
Proof.
  intros. simpl. auto.
Qed.

Lemma fold_ok:
  forall live def fid min l init blockc contidx,
    fold_left
      (fun (a : res (block_code * cont_idx)) (p : positive * instruction) =>
         handle_instr live def fid min a (fst p) (snd p))
      l init = OK (blockc, contidx) ->
    exists initc initidx, init = OK (initc, initidx).
Proof.
  intros live def fid min l init blockc contidx H.
  generalize dependent init. generalize dependent blockc. generalize dependent contidx.
  induction l; intros.
  - simpl in H. inv H. eauto.
  - rewrite fold_left_cons in H. apply IHl in H. destruct H as [initc [initidx HANDLE]].
    unfold handle_instr in HANDLE. repeat do_ok. destruct p. repeat do_ok. destruct a. simpl in H1.
    destruct i; inv H1; eauto.
Qed.

Lemma set_more_def:
  forall A (p:PTree.t A) l1 v l2,
    (p # l1 <- v) # l2 = None ->
    p # l2 = None.
Proof.
  intros A p l1 v l2 H. poseq_destr l1 l2.
  - rewrite PTree.gss in H; auto. inv H.
  - rewrite PTree.gso in H; auto.
Qed.   

Lemma transf_code_more_def:
  forall fid v params blockc contidx lbl 
    (TRANSF: transf_code fid v params = OK (blockc, contidx)),
    blockc # lbl = None -> (ver_code v) # lbl = None.
Proof.
  intros fid v params blockc contidx lbl TRANSF NONE.
  unfold transf_code in TRANSF. repeat do_ok.
  rewrite PTree.fold_spec in H1. rename l into live. rename d into def.
  assert (forall l min ic iidx rc ridx,
             fold_left (fun (a : res (block_code * cont_idx)) (p : positive * instruction) =>
             handle_instr live def fid min a (fst p) (snd p)) l (OK (ic, iidx))  = OK (rc, ridx) ->
             forall lbl, rc # lbl = None ->
                    ~ In lbl (map fst l) /\ ic # lbl = None).
  { clear H1 NONE. intros l. induction l; intros.
    - simpl in H. inv H. auto.
    - rewrite fold_left_cons in H.
      destruct a as [pc instr]. simpl fst in H. simpl snd in H.
      apply fold_ok in H as OK. destruct OK as [initc [initidx HANDLE]].
      rewrite HANDLE in H. apply IHl with (lbl:=lbl0) in H; auto. destruct H as [NOTIN INIT]. simpl.      
      unfold handle_instr in HANDLE. repeat do_ok. destruct p. repeat do_ok.
      destruct instr; inv H2; inv HDO; split; try solve [eapply set_more_def; eauto];
        try (intros [PC|IN]; [|contradiction]); subst;
          try solve[rewrite PTree.gss in INIT; auto; inv INIT]; repeat do_ok.
      + poseq_destr lbl0 (fresh_label_min min b # lbl0 <- b0); try subst.
        rewrite <- HEQ in INIT. rewrite PTree.gss in INIT; auto. inv INIT.
        rewrite PTree.gso in INIT; auto. rewrite PTree.gss in INIT; auto. inv INIT.
      + poseq_destr lbl0 (fresh_label_min min b # pc <- b0); try subst.
        rewrite PTree.gss in INIT; auto. inv INIT.
        rewrite PTree.gso in INIT; auto. poseq_destr pc lbl0.
        rewrite PTree.gss in INIT; auto. inv INIT.
        rewrite PTree.gso in INIT; auto. }
  apply H with (lbl:=lbl) in H1; auto. destruct H1 as [NOTIN EMPTY].
  destruct ((ver_code v) # lbl) eqn:CODE; auto. exfalso. apply PTree.elements_correct in CODE.
  apply NOTIN. replace lbl with (fst (lbl, i)) by auto. apply in_map. auto.
Qed.
    

Lemma fresh_label_min_correct:
  forall A (c:PTree.t A) min fl, fresh_label_min min c = fl -> c # fl = None.
Proof.
  intros A c min fl H. unfold fresh_label_min in H.
  destruct (c # fl) eqn:GET; auto. exfalso.
  apply max_pos_correct in GET. unfold fresh_label, max_label in H.
  specialize (Pos.le_max_r min (Pos.succ (max_pos c))). intros MAX.
  rewrite H in MAX. clear H. apply Pos.succ_le_mono in GET.
  specialize (Pos.le_trans _ _ _ GET MAX). intros H. apply Pos.le_succ_l in H.
  eapply Pos.lt_irrefl; eauto.
Qed.

Lemma fresh_label_min_set:
  forall A (c:PTree.t A) min l i, fresh_label_min min (c # l <- i) <> l.
Proof.
  intros A c min l i. specialize (PTree.gss l i c) as CODE.
  assert (fresh_label_min min c # l <- i = fresh_label_min min c # l <- i) by auto.
  apply fresh_label_min_correct in H.
  poseq_destr l (fresh_label_min min c # l <- i); auto.
  rewrite <- HEQ in H. rewrite H in CODE. inv CODE.
Qed.

Lemma fresh_label_min_fresh:
  forall A B (c:PTree.t A) (c':PTree.t B), c # (fresh_label_min (fresh_label c) c') = None.
Proof.
  intros A B c c'. destruct (c # (fresh_label_min (fresh_label c) c')) eqn:FRESH; auto.
  unfold fresh_label_min in FRESH. apply max_pos_correct in FRESH. unfold fresh_label in FRESH.
  unfold max_label in FRESH. apply Pos.max_lub_l in FRESH. apply Pos.le_succ_l in FRESH.
  apply Pos.lt_irrefl in FRESH. inv FRESH.
Qed.
    

Lemma set_none:
  forall A (c:PTree.t A) p1 i p2,
    (c # p1 <- i) # p2 = None ->
    c # p2 = None.
Proof.
  intros A c p1 i p2 H. poseq_destr p1 p2.
  - rewrite PTree.gss in H; auto. inv H.
  - rewrite PTree.gso in H; auto.
Qed.


(* adding new instructions doesn't remove those that were already there *)
Lemma fold_monotonic:
  forall live def fid min l init blockc contidx lbl,
  fold_left
  (fun (a : res (block_code * cont_idx)) (p : positive * instruction) =>
     handle_instr live def fid min a (fst p) (snd p))
  l init = OK (blockc, contidx) ->
  ~ In lbl (map fst l) ->
  exists initc initidx,
    init = OK (initc, initidx) /\
    forall i, initc # lbl = Some i ->
         blockc # lbl = Some i.
Proof.
  intros live def fid min l.
  induction l; intros.
  - simpl in H. inv H. eauto.
  - destruct a as [label instr]. simpl in H0. apply Decidable.not_or in H0. destruct H0.
    rewrite fold_left_cons in H. apply IHl with (lbl:=lbl) in H; auto.
    destruct H as [initc [initidx [HANDLE INIT]]]. unfold handle_instr in HANDLE.
    repeat do_ok. destruct p as [blkc cont]. repeat do_ok.
    destruct instr;
      try solve[inv H3; repeat esplit; rewrite PTree.gso in INIT; auto].
    repeat do_ok. repeat esplit.
    intros i IN. apply INIT. rewrite PTree.gso. rewrite PTree.gso; auto.
    unfold not. intros H. rewrite H in IN. symmetry in H.
    specialize (fresh_label_min_correct _ (blkc # label <- b) min lbl H). intros H'.
    apply set_none in H'. rewrite <- H in H'. rewrite H' in IN. inv IN.
Qed.  

Lemma fold_index_monotonic:
  forall live def fid min l init blockc contidx lbl,
  fold_left
  (fun (a : res (block_code * cont_idx)) (p : positive * instruction) =>
     handle_instr live def fid min a (fst p) (snd p))
  l init = OK (blockc, contidx) ->
  ~ In lbl (map fst l) ->
  exists initc initidx,
    init = OK (initc, initidx) /\
    forall i, initidx # lbl = Some i ->
         contidx # lbl = Some i.
Proof.
  intros live def fid min l.
  induction l; intros.
  - simpl in H. inv H. eauto.
  - destruct a as [label instr]. simpl in H0. apply Decidable.not_or in H0. destruct H0.
    rewrite fold_left_cons in H. apply IHl with (lbl:=lbl) in H; auto.
    destruct H as [initc [initidx [HANDLE INIT]]]. unfold handle_instr in HANDLE.
    repeat do_ok. destruct p as [blkc cont]. repeat do_ok.
    destruct instr; try solve [inv H3; repeat esplit; auto].
    repeat do_ok. repeat esplit.
    intros i IN. apply INIT. rewrite PTree.gso; auto.
Qed.  

(* Code is preserved at the same labels, but transformed into a block *)
Lemma transf_code_same_code:
  forall fid v params blockc contidx lbl i live def
    (TRANSF: transf_code fid v params = OK (blockc, contidx))
    (INSTR: (ver_code v) # lbl = Some i)
    (LIVE: liveness_analyze v = Some live)
    (DEF: defined_regs_analysis (ver_code v) params (ver_entry v) = Some def),
  exists blk,
    instr_to_block i live def fid lbl = OK blk /\
    blockc # lbl = Some blk.
Proof.
  intros fid v params blockc contidx lbl i live def TRANSF INSTR LIVE DEF.
  unfold transf_code in TRANSF. repeat do_ok. inv DEF. inv LIVE.
  rewrite PTree.fold_spec in H1.
  assert (forall l init blockc contidx lbl i,
             list_norepet (map fst l) ->
             fold_left (fun (a : res (block_code * cont_idx)) (p : positive * instruction) =>
          handle_instr live def fid (fresh_label (ver_code v)) a (fst p) (snd p)) l init = 
             OK (blockc, contidx) ->
             In (lbl,i) l ->
             exists blk, instr_to_block i live def fid lbl = OK blk /\
                    blockc # lbl = Some blk).
  { clear blockc contidx H1. intros l.
    induction l; intros.
    - simpl in H. inv H1.
    - rewrite fold_left_cons in H0. destruct H1 as [A | IN].
      + inv A. simpl in H0. inv H. apply fold_monotonic with (lbl:=lbl0) in H0; auto.
        destruct H0 as [initc [initidx [HANDLE SAME]]]. unfold handle_instr in HANDLE.
        repeat do_ok. destruct p. repeat do_ok.
        destruct i0; inv H1; repeat esplit; eauto; apply SAME; try apply PTree.gss.
        repeat do_ok. rewrite PTree.gso. apply PTree.gss.
        apply not_eq_sym. apply fresh_label_min_set.
      + inv H. eapply IHl in H0; eauto. }
  eapply H; eauto. apply PTree.elements_keys_norepet. apply PTree.elements_correct. auto.
Qed.

(* Same for the entire process *)
Lemma same_code:
  forall fid v params blockc newentry contidx lbl i live def
    (GEN: rtlgen fid v params = OK (blockc, newentry, contidx))
    (INSTR: (ver_code v) # lbl = Some i)
    (LIVE: liveness_analyze v = Some live)
    (DEF: defined_regs_analysis (ver_code v) params (ver_entry v) = Some def),
  exists blk,
    instr_to_block i live def fid lbl = OK blk /\
    blockc # lbl = Some blk.
Proof.
  intros fid v params blockc newentry contidx lbl i live def GEN INSTR LIVE DEF.
  unfold rtlgen in GEN. repeat do_ok. destruct p as [blkc contid]. inv H0.
  eapply transf_code_same_code in HDO as SAME; eauto. destruct SAME as [blk [BLOCK GET]].
  exists blk. split; auto. rewrite PTree.gso; auto.
  unfold not; intros H. symmetry in H. apply fresh_label_correct in H. rewrite GET in H. inv H.
Qed.

(* Entry has been prefixed by an entry block *)
Lemma code_entry:
  forall fid v params blockc newentry contidx
    (GEN: rtlgen fid v params = OK (blockc, newentry, contidx)),
    (ver_code v) # newentry = None /\ (* fresh *)
    blockc # newentry = Some (Bblock (entry_block params (ver_entry v))). (* entry block *)
Proof.
  intros fid v params blockc newentry contidx GEN.
  unfold rtlgen in GEN. repeat do_ok. destruct p as [blkc contid].
  inv H0. split.
  - apply transf_code_more_def with (lbl:=fresh_label blkc) in HDO. auto.
    apply fresh_label_correct. auto.
  - rewrite PTree.gss; auto.
Qed.

Lemma in_fst:
  forall A B x (l: list (A * B)),
    In x (map fst l) ->
    exists y, In (x,y) l.
Proof.
  intros A B x l H. induction l; inv H.
  - destruct a as [i j]. exists j. simpl. left. auto.
  - apply IHl in H0. destruct H0 as [y IN]. exists y. simpl. right. auto.
Qed.


Lemma transf_code_list:
  forall fid call_lbl call_next call_fid call_retreg call_args live_regs live def v l init tfc tfx,
    fold_left (fun (a : res (block_code * cont_idx)) (p : positive * instruction) =>
                 handle_instr live def fid (fresh_label (ver_code v)) a (fst p) (snd p))
              l init = OK (tfc, tfx) ->
    In (call_lbl, Call call_fid call_args call_retreg call_next) l ->
    (forall x y, In (x, y) l -> (ver_code v) # x = Some y) ->
    list_norepet (map fst l) ->
    live_def_regs call_lbl live def call_retreg = OK live_regs -> 
    exists fresh initc initidx,
      init = OK (initc, initidx) /\
      ~ In fresh (map fst l) /\
      initc # fresh = None /\
      tfx # call_lbl = Some fresh /\
      tfc # fresh = Some (Bblock (preamble_block live_regs call_retreg call_next)).
Proof.
  (* this proof has some weird tactics. Because sometimes, depending on the combination of *)
  (* unfolds, intros, etc..., the Qed gets stuck at the end *)
  (* so I reordered tactics until Qed finishes but I still don't understand why *)
  intros fid call_lbl call_next call_fid call_retreg call_args live_regs live def v l.
  induction l; intros.
  { simpl in H. inv H0. }
  rename H3 into LIVEDEF.
  rewrite fold_left_cons in H. simpl in H0. destruct H0 as [IS|IN].
  - inv IS. simpl in H. apply fold_ok in H as HINIT. unfold handle_instr in HINIT.
    destruct HINIT as [nextc [nextidx HANDLE]]. destruct init as [[firstc firstidx]|].
    2: { simpl in HANDLE. inv HANDLE. }
    rewrite LIVEDEF in HANDLE. unfold bind2 in HANDLE.
    repeat do_ok.
    exists (fresh_label_min (fresh_label (ver_code v)) firstc # call_lbl <- b). exists firstc. exists firstidx.
    split; auto. apply fold_ok in H as HANDLE. destruct HANDLE as [initc [initidx HANDLE]].
    unfold handle_instr in HANDLE. rewrite LIVEDEF in HANDLE. repeat do_ok. inv HDO0.
    rewrite LIVEDEF in H3. repeat do_ok.
    rename HDO0 into HCLOSE. rename HDO2 into HGEN. rename HDO3 into HPUSH. inv HDO1.
    repeat split; auto.
    + intros IN. simpl in IN. destruct IN as [ISCALL|INLIST].
      { eapply fresh_label_min_set. eauto. }
      simpl in H1. apply in_fst in INLIST. destruct INLIST as [y INLIST].
      specialize (H1 _ _ (or_intror INLIST)). rewrite fresh_label_min_fresh in H1. inv H1.
    + eapply set_more_def; eauto. eapply fresh_label_min_correct; eauto.
    + apply fold_index_monotonic with (lbl:=call_lbl) in H as HANDLE. 2: { inv H2. auto. }
      destruct HANDLE as [initc [initidx [HANDLE SAME]]]. unfold handle_instr in HANDLE.
      rewrite LIVEDEF in HANDLE. repeat do_ok. inv HDO0. rewrite LIVEDEF in H3. repeat do_ok.
      apply SAME. rewrite PTree.gss. unfold instr_to_block in HDO.
      rewrite LIVEDEF in HDO. repeat do_ok. inv HDO0. inv HDO2. inv HDO3. inv HGEN. inv HCLOSE.
      inv HPUSH. inv HDO4. auto.
    + eapply fold_monotonic in H as HANDLE.
      * destruct HANDLE as [initc [initidx [HANDLE SAME]]]. unfold handle_instr in HANDLE.
        rewrite LIVEDEF in HANDLE. repeat do_ok. inv HDO0. rewrite LIVEDEF in H3. repeat do_ok.
        apply SAME. unfold instr_to_block in HDO.
        rewrite LIVEDEF in HDO. repeat do_ok. inv HDO0. inv HDO2. inv HDO3. inv HGEN. inv HCLOSE.
        inv HPUSH. inv HDO4. rewrite PTree.gss. auto.
      * intros IN. apply in_fst in IN. destruct IN as [y IN]. specialize (H1 _ _ (or_intror IN)).
        rewrite fresh_label_min_fresh in H1. inv H1.
    - destruct a as [label instr]. assert (HNEQ: call_lbl <> label).
      { intros Heq. subst. simpl in H2. inv H2. apply H4. apply in_map with (f:=fst) in IN.
        simpl in IN. auto. } simpl in H, H2.
      apply IHl in H; auto.
      2: { intros x y H0. apply H1. simpl. right. auto. }
      2: { simpl in H2. inversion H2. auto. }
      destruct H as [fresh [initc [initidx [HANDLE [FRESHL [FRESHI [IDX PRES]]]]]]]. inv H2.
      exists fresh. destruct init as [[firstc firstidx]|]; simpl in HANDLE.
      2: { inv HANDLE. } exists firstc. exists firstidx. split; auto. repeat split; auto.
      + intros HIN. simpl in HIN. destruct HIN. 2:{ apply FRESHL. auto. }
        destruct instr; try solve[repeat do_ok; rewrite PTree.gss in FRESHI; inv FRESHI].
        repeat do_ok. rewrite PTree.gso in FRESHI.
        2: { apply not_eq_sym. apply fresh_label_min_set. }
        rewrite PTree.gss in FRESHI. inv FRESHI.
      + repeat do_ok. destruct instr; try solve[inv H0; eapply set_more_def; eauto].
        repeat do_ok. eapply set_more_def; eapply set_more_def; eauto.
Qed.

(* Each re-entry for a continuation has been prefixed by a preamble and stored in the contidx *)
Lemma transf_code_reentry:
  forall fid v params blockc newentry contidx call_lbl call_fid call_args call_retreg call_next live def live_regs
    (GEN: rtlgen fid v params = OK (blockc, newentry, contidx))
    (CALL: (ver_code v) # call_lbl = Some (Call call_fid call_args call_retreg call_next))
    (LIVE: liveness_analyze v = Some live)
    (DEF: defined_regs_analysis (ver_code v) params (ver_entry v) = Some def)
    (LIVEDEF: live_def_regs call_lbl live def call_retreg = OK live_regs),
  exists fresh,
    (ver_code v) # fresh = None /\
    contidx # call_lbl = Some fresh /\
    blockc # fresh = Some (Bblock (preamble_block live_regs call_retreg call_next)).
Proof.
  intros fid v params blockc newentry contidx call_lbl call_fid call_args call_retreg call_next live def live_regs GEN CALL LIVE DEF LIVEDEF.
  unfold rtlgen in GEN. repeat do_ok. destruct p as [tfc tfx]. inv H0. unfold transf_code in HDO.
  repeat do_ok. inv LIVE. inv DEF. rewrite PTree.fold_spec in H1.
  apply PTree.elements_correct in CALL.
  specialize (transf_code_list _ _ _ _ _ _ _ _ _ _ (PTree.elements (ver_code v)) (OK (PTree.empty RTLblock.block, PTree.empty label)) tfc contidx H1 CALL (PTree.elements_complete _) (PTree.elements_keys_norepet _) LIVEDEF).
  intros. destruct H as [fresh [initc [initidx [OK [FRESHL [FRESHI [IDX PRES]]]]]]]. auto.
  inv OK. exists fresh. repeat split; auto.
  - destruct ((ver_code v) # fresh) eqn:CODE; auto. apply PTree.elements_correct in CODE.
    exfalso. apply FRESHL. replace fresh with (fst (fresh, i)) by auto. apply in_map. auto.
  - rewrite PTree.gso. auto. poseq_destr (fresh) (fresh_label tfc); auto.
    rewrite fresh_label_correct in PRES; auto. inv PRES.
Qed.


(** * Agreeing regmaps and regsets  *)
(** When going from IR to RTL(block)  *)


(* Two regmaps agree on a regset iff they have the same values
   on the registers of the regset (may be None) *)
Inductive value_agree: option Integers.Int.int -> val -> Prop :=
| agree_none:
    value_agree None Values.Vundef
| agree_some:
    forall i,
      value_agree (Some i) (Vint i).

Definition agree (rm:reg_map) (rs:RTL.regset) (adr:live_abs_dr) :=
  forall r:reg, PositiveSet.In r adr -> value_agree (rm # r) (Regmap.get (shift_reg r) rs).

Lemma agree_subset:
  forall s1 s2 rm rs,
    PositiveSet.Subset s1 s2 ->
    agree rm rs s2 ->
    agree rm rs s1.
Proof.
  unfold agree. intros. auto.
Qed.

(* Liveness transfer preserves agree *)
Lemma agree_transfer:
  forall live rm rs f pc pc' i,
    liveness_analyze f = Some live ->
    (ver_code f)!pc = Some i ->
    In pc' (successors i) ->
    agree rm rs (live!!pc) ->
    agree rm rs (live_dr_transf (ver_code f) pc' (live!!pc')).
Proof.
  intros. apply agree_subset with (live!!pc); auto.
  eapply liveness_successor; eauto.
Qed.

(* The following lemmas express the fact that agreeing on the regset obtained 
   after adding registers implies agreeing on the original regset 
   (which contains less registers) *)
Lemma expr_live_agree:
  forall e live rm rs,
    agree rm rs (expr_live e live) ->
    agree rm rs live.
Proof.
  intros. eapply agree_subset; eauto. apply expr_live_subset.
Qed.

Lemma reg_live_agree:
  forall r live rm rs,
    agree rm rs (reg_live r live) ->
    agree rm rs live.
Proof.
  intros. eapply agree_subset; eauto. apply reg_live_subset.
Qed.

Lemma reg_list_live_agree:
  forall rl live rm rs,
    agree rm rs (reg_list_live rl live) ->
    agree rm rs live.
Proof.
  intros. eapply agree_subset; eauto. apply reg_list_live_subset.
Qed.

Lemma varmap_live_agree:
  forall v live rm rs,
    agree rm rs (varmap_live v live) ->
    agree rm rs live.
Proof.
  intros v live rm rs H. eapply agree_subset; eauto. apply varmap_subset.
Qed.


Lemma expr_list_live_agree:
  forall exl live rm rs,
    agree rm rs (expr_list_live exl live) ->
    agree rm rs live.
Proof.
  intros. eapply agree_subset; eauto. apply expr_list_live_subset.
Qed.

Lemma agree_eval_reg:
  forall r v rm rs live,
    agree rm rs live ->
    PositiveSet.In r live -> 
    eval_reg r rm = OK v ->
    Regmap.get (shift_reg r) rs = Vint v.
Proof.
  intros r v rm rs live H H0 H1. unfold agree in H. specialize (H r H0).
  unfold eval_reg in H1. destruct (rm # r) eqn:EVAL; inv H1. inv H. auto.
Qed.

Lemma agree_eval_expr:
  forall e v live rm rs op vals,
    agree rm rs (expr_live e live) ->
    eval_expr e rm = OK v ->
    transf_expr e = (op, vals) ->
    block_eval_operation op (rs ## vals) = Some (Values.Vint v).
Proof.
  intros e v live rm rs op vals H H0 H1. unfold eval_expr in H0.
  destruct e; inv H1.
  - repeat do_ok. eapply agree_eval_reg in HDO; eauto.
    2: { simpl. unfold reg_live. rewrite PositiveSet.add_spec. left. auto. }
    eapply agree_eval_reg in HDO0; eauto.
      2: { simpl. unfold reg_live. rewrite PositiveSet.add_spec. right.
           rewrite PositiveSet.add_spec. left. auto. }
      destruct b; inv H1; inv H3; simpl; rewrite HDO; rewrite HDO0; simpl; auto.
    + rewrite Integers.Int.add_zero. auto.
    + destruct (Integers.Int.eq i i0) eqn:EQ; simpl; auto.
    + destruct (Integers.Int.lt i i0) eqn:LT; simpl; auto.
    + unfold eval_mod in H2.
      destruct (Integers.Int.eq i0 Integers.Int.zero || Integers.Int.eq i (Integers.Int.repr Integers.Int.min_signed) && Integers.Int.eq i0 Integers.Int.mone); inv H2. auto.
  - repeat do_ok. eapply agree_eval_reg in HDO; eauto.
    2: { simpl. unfold reg_live. rewrite PositiveSet.add_spec. left. auto. }
    destruct u; inv H2; inv H3; simpl; rewrite HDO; simpl; auto.
    + destruct (Integers.Int.eq i Integers.Int.zero) eqn:Z; simpl; auto.
    + rewrite Integers.Int.repr_signed. auto.
  - destruct z. inv H0. inv H3. simpl. auto.
Qed.


(* the order with which we insert live registers doesn't matter *)
Lemma list_reg_commut:
  forall le a live,
    PositiveSet.In a live ->
    PositiveSet.In a (reg_list_live le live).
Proof.
  intros le a rs H. generalize dependent rs. induction le; intros; simpl; auto.
  apply IHle. unfold reg_live. rewrite PositiveSet.add_spec. right. auto.
Qed.

(* It is sufficient to agree on all the registers of [live] except [reg]
   before an assignation provided we assign the same value to [reg]
   on both sides *)
Lemma agree_insert_dead:
  forall live rm rs reg v,
    agree rm rs (reg_dead reg live) ->
    agree (rm # reg <- v) (Registers.Regmap.set (shift_reg reg) (Vint v) rs) live.
Proof.
  intros. unfold agree in *.
  intros r IN. poseq_destr r reg.
  - rewrite PTree.gss. rewrite Regmap.gss. constructor.
  - rewrite PTree.gso; auto. rewrite Regmap.gso; auto.
    2: { apply not_shift_eq. auto. }
    apply H. apply PositiveSet.remove_spec; split; auto.
Qed.

(* updating the rm on both sides *)
Lemma agree_insert:
  forall live rm rs reg v,
    agree rm rs live ->
    agree (rm # reg <- v) (Registers.Regmap.set (shift_reg reg) (Vint v) rs) live.
Proof.
  intros. apply agree_subset with (reg_dead reg live) live rm rs in H.
  - apply agree_insert_dead. auto.
  - intros r IN. apply PositiveSet.remove_spec in IN as [IN _]. auto.
Qed.


Lemma agree_void:
  forall rm rs live v,
    agree rm rs live ->
    agree rm (Registers.Regmap.set void_reg v rs) live.
Proof.
  intros rm rs live v H. unfold agree in *. intros r H0.
  rewrite Regmap.gso.
  2: { unfold shift_reg. unfold void_reg, IRtoRTLblock.shift. intros HEQ.
       destruct r; inv HEQ. }
  apply H. auto.
Qed.

Lemma agree_cond:
  forall rm rs live r i b,
    agree rm rs live ->
    PositiveSet.In r live ->
    eval_reg r rm = OK i ->
    bool_of_int i = b -> 
    (Val.cmp_bool Integers.Ceq (Regmap.get (shift_reg r) rs) (Vint Integers.Int.zero)) = Some (negb b).
Proof.
  intros rm rs live r i b H H0 H1 H2. unfold bool_of_int in H2.
  eapply agree_eval_reg in H1; eauto. rewrite H1.
  unfold Val.cmp_bool.
  destruct (Integers.Int.intval i) eqn:INTVAL; subst.
  - simpl. destruct i. simpl in INTVAL. subst.
    unfold Integers.Int.eq. simpl. rewrite Integers.Int.unsigned_zero. auto.
  - simpl. destruct i. simpl in INTVAL. subst.
    unfold Integers.Int.eq. simpl. rewrite Integers.Int.unsigned_zero. auto.
  - simpl. destruct i. simpl in INTVAL. subst.
    unfold Integers.Int.eq. simpl. rewrite Integers.Int.unsigned_zero. auto.
Qed.


(* The list of saved registers and arguments can all be evaluated to integers *)
Inductive eval_list_int: RTL.regset -> list reg -> list Integers.Int.int -> Prop :=
| eli_nil:
    forall rs, eval_list_int rs nil nil
| eli_cons:
    forall rs lr li r i,
      Regmap.get (shift_reg r) rs = Vint i ->
      eval_list_int rs lr li ->
      eval_list_int rs (r::lr) (i::li).

(* evaluation of varmaps for deoptimization *)
Inductive eval_varmap_int: RTL.regset -> varmap -> list Integers.Int.int -> Prop :=
| evi_nil:
    forall rs, eval_varmap_int rs nil nil
| evi_cons:
    forall reg expr vm li rs rint eint op lst,
      eval_varmap_int rs vm li ->
      int_of_pos reg = OK rint ->
      transf_expr expr = (op, lst) ->
      block_eval_operation op (rs ## lst) = Some (Vint eint) ->
      eval_varmap_int rs ((reg,expr)::vm) (eint::rint::li).

(* this list of integers is then used to reconstruct a regmap *)
Inductive construct_regmap : list Integers.Int.int -> reg_map -> Prop :=
| cr_nil:
    construct_regmap nil empty_regmap
| cr_cons:
    forall rint eint rm l reg,
      construct_regmap l rm ->
      reg = pos_of_int rint ->
      construct_regmap (eint::rint::l) (rm # reg <- eint).

Lemma construct_ok:
  forall l rm,
    construct_regmap l rm -> jit.rebuild_regmap l = OK rm.
Proof.
  intros l rm H. induction H.
    { simpl. auto. }
    simpl. rewrite IHconstruct_regmap. simpl. rewrite H0. auto.
Qed.

Lemma agree_list:
  forall l rm rs live lr,
    agree rm rs (reg_list_live l live) ->
    eval_list_reg l rm = OK lr ->
    eval_list_int rs l lr.
Proof.
  intros l rm rs live lr H H0.
  generalize dependent lr. generalize dependent live. induction l; intros.
  { inv H0. constructor. }
  inv H0. repeat do_ok. eapply agree_eval_reg in HDO; eauto.
  2: { simpl. apply list_reg_commut. unfold reg_live. rewrite PositiveSet.add_spec. left. auto. }
  constructor; auto. eapply IHl; eauto.
Qed.

Inductive double : nat -> nat -> Prop :=
| double_z:
    double 0 0
| double_s:
    forall n m, double n m -> 
           double (S n) (S (S m)).


Lemma eval_varmap_size:
  forall rs vm li,
    eval_varmap_int rs vm li ->
    double (Datatypes.length vm) (Datatypes.length li).
Proof.
  intros rs vm li H. generalize dependent li.
  induction vm; intros; simpl; inv H; simpl; constructor; auto.
Qed.

(* to avoid a bug with Qed not finishing *)
Lemma gen_cons:
  forall r e vm linstr,
    generate_pushvm ((r, e) :: vm) = OK linstr ->
    exists rint linstr',
      int_of_pos r = OK rint /\
      generate_pushvm vm = OK linstr' /\
      linstr = [Bop (fst (transf_expr e)) (snd (transf_expr e)) guard_reg; Bcall EF_save [guard_reg] void_reg;
        Bop (Op.Ointconst rint) [ ] guard_reg; Bcall EF_save [guard_reg] void_reg] ++ linstr'.
Proof.
  simpl. unfold bind. intros r e vm linstr H.
  destruct (int_of_pos r) eqn:R; inv H. destruct (transf_expr e).
  destruct (generate_pushvm vm) eqn:VM; inv H1.
  eauto.
Qed.
(* I could do it in a simpler way: *)
(* intros r e vm linstr H. simpl in H. repeat do_ok. destruct (transf_expr e). repeat do_ok. exists i. exists l0. auto. *)
(* But then Qed gets stuck *)           


Lemma agree_varmap:
  forall vm rm rs live rmdeopt linstr,
    generate_pushvm vm = OK linstr -> (* so we know the int conversion went well *)
    agree rm rs (varmap_live vm live) ->
    update_regmap vm rm = OK rmdeopt -> (* if in the source, the varmap can be used *)
    exists li,
      eval_varmap_int rs vm li /\ (* then it evaluates *)
      construct_regmap li rmdeopt. (* to something that builds the same reg_map *)
Proof.
  intros vm rm rs live rmdeopt linstr GEN H H0.
  generalize dependent rmdeopt. generalize dependent linstr.
  induction vm.
  { intros. simpl in H0. inv H0. exists nil. split; constructor. }
  destruct a as [reg_ expr_].
  destruct (transf_expr expr_) as [op lst] eqn:TRANSF.
  intros linstr GEN rmdeopt UPD.
  assert (AG: agree rm rs (varmap_live vm live)).
  { eapply expr_live_agree. eauto. }
  simpl in UPD. repeat do_ok.
  apply gen_cons in GEN. destruct GEN as [rint [linstr' [S1 [S2 s3]]]]. subst.
  assert (OK r = OK r) by auto. eapply IHvm in H0; eauto.
  destruct H0 as [li [EVAL CONSTRUCT]].  
  eapply agree_eval_expr in HDO; eauto.
  econstructor. split.
  - econstructor; eauto.
  - econstructor; eauto. apply int_pos_correct in S1. auto.
Qed.



(** * Index & Order *)
Definition index: Type := unit.  (* no stuttering in the source, each step is one or more steps *)

Inductive order: index -> index -> Prop := . (* no order needed *)

Lemma order_wf:
  well_founded order.
Proof.
  unfold well_founded. intros a. constructor. intros y H. inv H.
Qed.



(** * Capturing live and defined registers  *)
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
      * apply SetoidList.InA_cons_tl. apply IHl. auto.
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
  

Lemma intersection_defined:
  forall pc live def retreg l r,
    live_def_regs pc live def retreg = OK l ->
    In r l ->
    exists rs, def_absstate_get pc def = DefFlatRegset.Inj rs /\
          PositiveSet.In r rs.
Proof.
  intros pc live def retreg l r H H0.
  unfold live_def_regs in H. unfold defined_rs in H.
  destruct (def_absstate_get pc def) eqn:H1; inv H.
  rewrite <- PSin_in in H0. apply PositiveSet.inter_spec in H0. destruct H0. exists r0. auto.
Qed.

Lemma intersection_live:
  forall pc live def retreg l r,
    live_def_regs pc live def retreg = OK l ->
    In r l ->
    PositiveSet.In r (reg_dead retreg (live_absstate_get pc live)).
Proof.
  intros pc live def retreg l r H H0. unfold live_def_regs in H. repeat do_ok.
  rewrite <- PSin_in in H0. apply PositiveSet.inter_spec in H0. destruct H0. auto.
Qed.
  

Lemma eval_reg_defined:
  forall l rm pc def live retreg r,
    defined rm (def_absstate_get pc def) ->
    live_def_regs pc live def retreg = OK l ->
    In r l ->
    exists i, eval_reg r rm = OK i.
Proof.
  intros l rm pc def live retreg r H H0 H1.
  eapply intersection_defined in H0; eauto. destruct H0 as [rs [DEF IN]].
  unfold defined in H. rewrite DEF in H. apply H in IN as [v EVAL]. exists v.
  unfold eval_reg. rewrite EVAL. auto.
Qed.

Lemma eval_defined:
  forall l rm pc def live retreg,
    defined rm (def_absstate_get pc def) ->
    live_def_regs pc live def retreg = OK l ->
    exists li, eval_list_reg l rm = OK li.
Proof.
  intros l rm pc def live retreg DEF LD.
  assert (forall l',
             (forall x, In x l' -> In x l) ->
             exists li, eval_list_reg l' rm = OK li).
  { intros l' SUBS. induction l'; intros.
    - exists nil. auto.
    - simpl. assert (exists i, eval_reg a rm = OK i).
      { eapply eval_reg_defined; eauto. apply SUBS. simpl. left. auto. }
      destruct H as [i EVAL]. rewrite EVAL. simpl.
      assert (exists li', eval_list_reg l' rm = OK li').
      { eapply IHl'; eauto. intros x H. apply SUBS. simpl. right. auto. }
      destruct H as [li' EVALL].
      rewrite EVALL. simpl. exists (i::li'). auto. }
  apply H. intros x; auto.
Qed.
(* might not be used anymore since we have the following lemma *)


Lemma defined_agree:
  forall l rm pc def live retreg rs,
    defined rm (def_absstate_get pc def) ->
    live_def_regs pc live def retreg = OK l ->
    agree rm rs (reg_dead retreg (live_absstate_get pc live)) ->
    exists li, eval_list_int rs l li.
Proof.
  intros l rm pc def live retreg rs DEF LD AGREE.
  assert (forall l',
             (forall x, In x l' -> In x l) ->
             exists li, eval_list_int rs l' li).
  { intros l' SUBS. induction l'; intros.
    - exists nil. constructor.
    - assert (exists i, eval_reg a rm = OK i).
      { eapply eval_reg_defined; eauto. apply SUBS. left. auto. }
      destruct H as [i EVAL].
      assert (Regmap.get (shift_reg a) rs = Vint i).
      { eapply agree_eval_reg; eauto. eapply intersection_live; eauto. apply SUBS. left. auto. }
      assert (exists li', eval_list_int rs l' li').
      { apply IHl'. intros x H0. apply SUBS. right. auto. }
      destruct H0 as [li' EVALL]. exists (i::li'). constructor; auto. }
  apply H. intros. auto.
Qed.



(** * match_stack  *)
Inductive match_stackframe (v:version) (fid:fun_id) (live:live_abs_state) (def:def_abs_state): stackframe -> stackframe -> Prop :=
| frame_same:
    forall sf,
      (match_stackframe v fid live def) sf sf
| frame_opt:
    forall retreg call_lbl rm rs iret ifid ilbl saved lregs callee_id args next
      (CODE: (ver_code v) # call_lbl = Some (Call callee_id args retreg next))
      (DEFINED: defined rm (def_absstate_get call_lbl def))
      (RET: int_of_pos (shift_reg retreg) = OK iret)
      (ID: int_of_pos fid = OK ifid)
      (LBL: int_of_pos call_lbl = OK ilbl)
      (AGREE: agree rm rs (reg_list_live args (reg_dead retreg (live_absstate_get call_lbl live))))
      (LIVE_REGS: live_def_regs call_lbl live def retreg = OK lregs)
      (LIVE_EVAL: eval_list_int rs lregs saved), 
    (match_stackframe v fid live def)
      (IR_SF (retreg, v, next, rm))
      (ASM_SF (ifid, ilbl, iret, rev saved)).

Inductive match_stack (v:version) (fid:fun_id) (live:live_abs_state) (def:def_abs_state) : stack -> stack -> Prop :=
| match_nil:
    (match_stack v fid live def) nil nil
| match_cons:
    forall sf1 sf2 stk1 stk2
      (MATCH_SF: match_stackframe v fid live def sf1 sf2)
      (MATCH_STK: match_stack v fid live def stk1 stk2),
      (match_stack v fid live def) (sf1::stk1) (sf2::stk2).

Lemma match_stackframe_same:
  forall v fid live def sf,
    (match_stackframe v fid live def) sf sf.
Proof.
  intros v fid live def sf. apply frame_same.
Qed.

Lemma match_stack_same:
  forall s v fid live def,
    (match_stack v fid live def) s s.
Proof.
  intros s v fid live def. induction s; constructor; auto. apply match_stackframe_same.
Qed.

Lemma match_stack_app:
  forall stk1 stk2 stk v fid live def,
    (match_stack v fid live def) stk1 stk2 ->
    (match_stack v fid live def) (stk++stk1) (stk++stk2).
Proof.
  intros stk1 stk2 stk v fid live def H. induction stk; simpl; auto.
  constructor. apply frame_same. auto.
Qed.



(** * match_states  *)
(* On all other states than RTL, nothing changes *)
Definition not_rtl (sync:synchro_state) : Prop :=
  match sync with
  | Halt_RTL _ _ => False
  | Halt_Block _ => False
  | _ => True
  end.

Inductive match_states (v:version) (fid:fun_id) (live:live_abs_state) (def:def_abs_state):
  index -> mixed_state -> mixed_state -> Prop :=
| match_refl:                   (* outside of RTL *)
    forall sync stkir stkblk top mem
      (NO_RTL: not_rtl sync)
      (MATCH_STACK: match_stack v fid live def stkir stkblk),
      (match_states v fid live def) tt
                                    (sync, mkmut stkir top mem)
                                    (sync, mkmut stkblk top mem)
| match_block:                  (* matching in the generated block code *)
    forall pc rm rs stkir stkblk top mem
      (MATCH_STACK: match_stack v fid live def stkir stkblk)
      (DEFINED: defined rm (def_absstate_get pc def))
      (AGREE: agree rm rs (live_dr_transf (ver_code v) pc (live_absstate_get pc live))),
      (match_states v fid live def) tt
                                    (Halt_IR (v, pc, rm), mkmut stkir top mem)
                                    (Halt_Block (BPF pc rs), mkmut stkblk top mem)
| match_call:                   (* when doing a Call from the block code *)
    forall callee_fid args retreg next call_lbl stkir stkblk mem rm iargs ifid ilength
      (CODE: (ver_code v) # call_lbl = Some (Call callee_fid args retreg next))
      (IFID: int_of_pos callee_fid = OK ifid)
      (ILENGTH: int_of_nat (Datatypes.length args) = OK ilength)
      (ARGS: eval_list_reg args rm = OK iargs)
      (MATCH_STACK: match_stack v fid live def stkir stkblk),
      (match_states v fid live def) tt
                                    (S_Call (ir_call callee_fid iargs), mkmut stkir nil mem)
                                    (S_Call nat_call, mkmut stkblk (ifid::ilength::rev iargs) mem)
| match_return:
    forall i stkir stkblk top mem
      (MATCH_STACK: match_stack v fid live def stkir stkblk),
      (match_states v fid live def) tt
                                    (S_Return (ir_ret i), mkmut stkir top mem)
                                    (S_Return nat_ret, mkmut stkblk (i::top) mem)
| match_deopt:
    forall stkir stkblk top mem fint lint size li rm
      (MATCH_STACK: match_stack v fid live def stkir stkblk)
      (SIZE: double (nat_of_int size) (Datatypes.length li))
      (CONS: construct_regmap li rm),
      (match_states v fid live def) tt
                                    (S_Deopt (ir_deopt (pos_of_int fint) (pos_of_int lint) rm), mkmut stkir top mem)
                                    (S_Deopt nat_deopt, mkmut stkblk (fint::lint::size::(rev li)++top) mem).
      
      


  


(* As we call our primitives, we get a regset that is identical except for the reserved registers *)
Definition same_shift (rs1 rs2:RTL.regset) :=
  forall p,
    (IRtoRTLblock.shift < p)%positive ->
    Regmap.get p rs1 = Regmap.get p rs2.

Lemma same_shift_refl:
  forall rs,
    same_shift rs rs.
Proof. intros. unfold same_shift. auto. Qed.

Lemma same_shift_trans:
  forall rs1 rs2 rs3,
    same_shift rs1 rs2 ->
    same_shift rs2 rs3 ->
    same_shift rs1 rs3.
Proof.
unfold same_shift. intros. specialize (H p H1). specialize (H0 p H1). rewrite <- H0. auto.
Qed.

Lemma same_shift_sym:
  forall rs1 rs2,
    same_shift rs1 rs2 ->
    same_shift rs2 rs1.
Proof.
  unfold same_shift. intros. specialize (H p H0). auto.
Qed.

Lemma same_shift_set_void:
  forall rs v,
    same_shift rs (Regmap.set void_reg v rs).
Proof.
  intros. unfold same_shift. intros. rewrite Regmap.gso; auto.
  intros Heq. subst. inv H.
Qed.

Lemma same_shift_set:
  forall rs v r,
    (r < IRtoRTLblock.shift)%positive -> 
    same_shift rs (Regmap.set r v rs).
Proof.
  intros. unfold same_shift. intros. rewrite Regmap.gso; auto.
  intros Heq. subst. apply Pos.lt_nle in H. apply H. apply Pos.lt_le_incl. auto.
Qed.

Lemma shift_ok:
  forall r,
    (IRtoRTLblock.shift < shift_reg r)%positive.
Proof.
  intros r. unfold shift_reg. rewrite Pos.add_comm. apply Pos.lt_add_r.
Qed.

Lemma same_shift_eval:
  forall rs1 rs2 lr li,
    same_shift rs1 rs2 ->
    eval_list_int rs1 lr li ->
    eval_list_int rs2 lr li.
Proof.
  intros rs1 rs2 lr li H H0. generalize dependent li.
  induction lr; intros.
  - inv H0. constructor.
  - inv H0. constructor.
    + unfold same_shift in H. rewrite <- H; auto. apply shift_ok.
    + apply IHlr. auto.
Qed.

Lemma same_shift_reg:
  forall rs1 rs2 r,
    same_shift rs1 rs2 ->
    Regmap.get (shift_reg r) rs1 = Regmap.get (shift_reg r) rs2.
Proof.
  intros rs1 rs2 r H. apply H. apply shift_ok.
Qed.


Lemma same_shift_expr:
  forall rs1 rs2 e op lst,
    same_shift rs1 rs2 ->
    transf_expr e = (op, lst) ->
    block_eval_operation op (rs1 ## lst) = block_eval_operation op (rs2 ## lst).
Proof.
  intros rs1 rs2 e op lst H H0. destruct e.
  - destruct b; inv H0; simpl; repeat (erewrite same_shift_reg with (rs1:=rs1); eauto).
  - destruct u; inv H0; simpl; repeat (erewrite same_shift_reg with (rs1:=rs1); eauto).
  - inv H0; destruct z; inv H2; simpl; repeat (erewrite same_shift_reg with (rs1:=rs1); eauto).
    auto.
Qed.


Lemma same_shift_varmap:
  forall rs1 rs2 vm li,
    same_shift rs1 rs2 ->
    eval_varmap_int rs1 vm li ->
    eval_varmap_int rs2 vm li.
Proof.
  intros rs1 rs2 vm li H H0. generalize dependent li.
  induction vm; intros.
  - inv H0. constructor.
  - inv H0. econstructor; eauto. erewrite same_shift_expr in H8; eauto.
Qed.


Lemma push_exec:
  forall iargs stk top mem nc,
    exec (jit.push_args iargs) naive_impl (mkmut stk top mem, nc) =
    SOK tt (mkmut stk ((rev iargs)++top) mem, nc).
Proof.
  intros iargs stk top mem nc. generalize dependent top. induction iargs; intros; eauto.
  simpl. unfold n_save, sbind. simpl. rewrite IHiargs. rewrite <- app_assoc. simpl. auto.
Qed.

Lemma exec_push:
  forall iargs stk top mem nc ms, 
    exec (jit.push_args iargs) naive_impl (mkmut stk top mem, nc) = SOK tt (ms, nc) ->
    ms = mkmut stk ((rev iargs)++top) mem.
Proof.
  intros iargs stk top mem nc ms H. generalize dependent top. induction iargs; intros.
  { inv H. simpl. auto. }
  simpl in H. repeat sdo_ok. inv HDO. apply IHiargs in H. rewrite <- app_assoc. simpl. auto.
Qed.

Lemma exec_pop:
  forall args stk top mem nc l,
    exec (jit.pop_args' (Datatypes.length args) l) naive_impl (mkmut stk (args++top) mem, nc) =
    SOK ((rev args) ++ l) (mkmut stk top mem, nc).
Proof.
  intros args stk top mem nc l. generalize dependent top. generalize dependent l.
  induction args; intros; simpl; eauto.
  unfold n_load, sbind. simpl. rewrite IHargs. rewrite <- app_assoc. simpl. auto.
Qed.

Lemma eval_list_length:
  forall l1 l2 rm,
    eval_list_reg l1 rm = OK l2 ->
    Datatypes.length l1 = Datatypes.length l2.
Proof.
  intros l1 l2 rm H. generalize dependent l2. induction l1; intros; inv H; auto.
  repeat do_ok. simpl. f_equal. apply IHl1. auto.
Qed.

Lemma double_end:
  forall A (l:list A) m,
    S (S m) = Datatypes.length l ->
    exists a b l', l = l' ++ [a;b].
Proof.
  intros A l m H. rewrite <- rev_length in H.
  destruct (rev l) eqn:REV1. inv H.
  destruct (l0) eqn:REV2. inv H. subst.
  exists a0. exists a. exists (rev l1). apply f_equal with (f:=@rev A) in REV1; eauto.
  rewrite rev_involutive in REV1. simpl in REV1. rewrite <- app_assoc in REV1. simpl in REV1. auto.
Qed.

(* we can restore the reg_map with what we've saved *)
Lemma exec_get_varmap:
  forall size length stk li top mem nc l,
    double size length ->
    length = Datatypes.length li ->
    exec (jit.get_varmap size l) naive_impl (mkmut stk ((rev li)++top) mem, nc) =
    SOK (li ++ l) (mkmut stk top mem, nc).
Proof.
  intros size length stk li top mem nc l DOUBLE LENGTH.
  generalize dependent top. generalize dependent l. generalize dependent li. 
  induction DOUBLE; intros.
  - simpl. destruct li; inv LENGTH. simpl. auto.
  - assert (exists l1 l2 li', li = li' ++ [l1; l2]).
    { eapply double_end; eauto. }
    destruct H as [l1 [l2 [li' H]]]. subst. rewrite rev_app_distr. simpl.
    unfold n_load, sbind. simpl. rewrite <- app_assoc. simpl. apply IHDOUBLE.
    rewrite app_length in LENGTH. simpl in LENGTH. rewrite plus_comm in LENGTH. inv LENGTH. auto.
Qed.


(* In the Call block, we can step to a state where all live registers have been saved *)
Lemma generate_saves_star:
  forall p rtl nc (lr:list reg) (lbi:list block_instr) (li:list Integers.Int.int) (ei:exit_instr) (rs:RTL.regset) (stk:stack) (stktop:env) (mem:memory),
    eval_list_int rs lr li ->
    exists rs', 
    star (mixed_step p (Some (inr rtl))) nc
         (Halt_Block (BState (Bblock ((generate_saves lr) ++ lbi, ei)) rs), mkmut stk stktop mem ) E0
         (Halt_Block (BState (Bblock (lbi, ei)) rs'), mkmut stk ((rev li)++stktop) mem) /\
    same_shift rs rs'.
Proof.
  intros p rtl nc lr lbi lv ei rs stk stktop mem H.
  generalize dependent lv. generalize dependent stktop. generalize dependent rs. induction lr; intros.
  { inv H. simpl. exists rs. split. apply star_refl. apply same_shift_refl. }
  destruct lv as [|v lv]; inv H; repeat do_ok.
  assert (HEV: eval_list_int (Regmap.set void_reg (Vint Integers.Int.zero) rs) lr lv).
  { eapply same_shift_eval; eauto. apply same_shift_set_void. }
  specialize (IHlr (Regmap.set void_reg (Vint Integers.Int.zero) rs) (v::stktop) lv HEV).
  destruct IHlr as [rs' [STAR SAME]].
  simpl. exists (rs'). split.
  2: { eapply same_shift_trans; eauto. apply same_shift_set_void. }
  eapply star_step with (t1:=E0) (t2:=E0); auto.
  { eapply rtl_block_step. simpl. unfold ASMinterpreter.prim_sem_dec. simpl.
    rewrite H4. simpl. unfold n_save. unfold sbind. simpl. eauto. }
  rewrite <- app_assoc. simpl. apply STAR.
Qed.

Lemma generate_pushvm_star:
  forall p rtl nc (vm:varmap) (lvm lbi:list block_instr) (li:list Integers.Int.int) (ei:exit_instr) (rs:RTL.regset) (stk:stack) (top:env) (mem:memory),
    generate_pushvm vm = OK lvm ->
    eval_varmap_int rs vm li -> 
    exists rs',
    star (mixed_step p (Some (inr rtl))) nc
         (Halt_Block (BState (Bblock (lvm ++ lbi, ei)) rs), mkmut stk top mem) E0
         (Halt_Block (BState (Bblock (lbi, ei)) rs'), mkmut stk ((rev li) ++ top) mem) /\
    same_shift rs rs'.
Proof.
  intros p rtl nc vm lvm lbi li ei rs stk top mem H H0.
  generalize dependent li. generalize dependent top. generalize dependent rs. generalize dependent lvm.
  induction vm; intros.
  { inv H0. inv H. simpl. exists rs. split. apply star_refl. apply same_shift_refl. }
  destruct a as [reg expr].
  apply gen_cons in H. destruct H as [rint [linstr' [INT [GEN LVM]]]]. subst.
  inv H0. rewrite H7. simpl.
  pose (newrs := Regmap.set void_reg (Vint Integers.Int.zero) (Regmap.set guard_reg (Vint rint) (Regmap.set void_reg (Vint Integers.Int.zero) (Regmap.set guard_reg (Vint eint) rs)))).
  assert (same_shift rs newrs).
  { unfold newrs.
    eapply same_shift_trans. 2: eapply same_shift_set_void.
    eapply same_shift_trans. 2: { eapply same_shift_set. unfold guard_reg, ret_reg, IRtoRTLblock.shift. lia. }
    eapply same_shift_trans. 2: eapply same_shift_set_void.
    eapply same_shift_trans. 2: { eapply same_shift_set. unfold guard_reg, ret_reg, IRtoRTLblock.shift. lia. }
    apply same_shift_refl. }
  assert (EVAL: eval_varmap_int newrs vm li0).
  { eapply same_shift_varmap; eauto.  }
  specialize (IHvm linstr' GEN newrs (rint::eint::top) li0 EVAL).
  destruct IHvm as [rs' [STAR SAME]]. 
  econstructor. split.
  - eapply star_step with (t1:=E0) (t2:=E0); auto.
    { eapply rtl_block_step. simpl. rewrite H8. simpl. eauto. }
    eapply star_step with (t1:=E0) (t2:=E0); auto.
    { eapply rtl_block_step. simpl. unfold ASMinterpreter.prim_sem_dec. simpl. rewrite Regmap.gss.
      simpl. unfold n_save, sbind. simpl. eauto. }
    eapply star_step with (t1:=E0) (t2:=E0); auto.
    { eapply rtl_block_step. simpl. eauto. }
    eapply star_step with (t1:=E0) (t2:=E0); auto.
    { eapply rtl_block_step. simpl. unfold ASMinterpreter.prim_sem_dec. simpl. rewrite Regmap.gss.
      simpl. unfold n_save, sbind. simpl. eauto. }
    repeat rewrite <- app_assoc. simpl.
    rewrite H5 in INT. inv INT. apply STAR.
  - eapply same_shift_trans; eauto. 
Qed.

(* Stepping to a state where all arguments have been pushed to the stack *)
Lemma generate_pushargs_star:
  forall p rtl nc (lr:list reg) (lbi:list block_instr) (li:list Integers.Int.int) (ei:exit_instr) (rs:RTL.regset) (stk:stack) (stktop:env) (mem:memory),
    eval_list_int rs lr li ->
    exists rs',
    star (mixed_step p (Some (inr rtl))) nc
         (Halt_Block (BState (Bblock ((generate_pushargs lr) ++ lbi, ei)) rs), mkmut stk stktop mem ) E0
         (Halt_Block (BState (Bblock (lbi, ei)) rs'), mkmut stk ((rev li)++stktop) mem) /\
    same_shift rs rs'.
Proof.
  intros p rtl nc lr lbi li ei rs stk stktop mem H.
  generalize dependent li. generalize dependent stktop. generalize dependent rs. induction lr; intros.
  { inv H. simpl. exists rs. split. apply star_refl. apply same_shift_refl. }
  destruct li as [|v lv]; inv H; repeat do_ok.
  assert (HEV: eval_list_int (Regmap.set void_reg (Vint Integers.Int.zero) rs) lr lv).
  { eapply same_shift_eval; eauto. apply same_shift_set_void. }
  specialize (IHlr (Regmap.set void_reg (Vint Integers.Int.zero) rs) (v::stktop) lv HEV).
  destruct IHlr as [rs' [STAR SAME]].
  simpl. exists (rs'). split.
  2: { eapply same_shift_trans; eauto. apply same_shift_set_void. }
  eapply star_step with (t1:=E0) (t2:=E0); auto.
  { eapply rtl_block_step. simpl. unfold ASMinterpreter.prim_sem_dec. simpl.
    rewrite H4. simpl. unfold n_save. unfold sbind. simpl. eauto. }
  rewrite <- app_assoc. simpl. apply STAR.
Qed.

(* Stepping to a state where all live registers have been restored *)
Lemma generate_loads_star:
  forall p rtl nc (lregs:list reg) (lbi:list block_instr) (saved top:list Integers.Int.int) (ei:exit_instr) (rs initrs:RTL.regset) (stk:stack) (mem:memory),
    NoDup lregs ->
    eval_list_int rs lregs saved ->
    exists rs',
      star (mixed_step p (Some (inr rtl))) nc
           (Halt_Block (BState (Bblock ((generate_loads lregs) ++ lbi, ei)) initrs), mkmut stk ((rev saved)++top) mem) E0
           (Halt_Block (BState (Bblock (lbi, ei)) rs'), mkmut stk top mem) /\
      (forall r, In r lregs -> Regmap.get (shift_reg r) rs' = Regmap.get (shift_reg r) rs) /\
      (forall r, (~ In r lregs) -> Regmap.get (shift_reg r) rs' = Regmap.get (shift_reg r) initrs).
Proof.
  intros p rtl nc lregs lbi saved top ei rs initrs stk mem NODUP H.
  generalize dependent lbi. generalize dependent top. generalize dependent saved. generalize dependent initrs.
  induction lregs; intros.
  { inv H. exists initrs. simpl. split. apply star_refl. split; intros; auto. inv H. }
  inv NODUP.
  destruct saved as [|s saved]; inv H. simpl. rewrite <- app_assoc. rewrite <- app_assoc.
  specialize (IHlregs H3 initrs saved H8 ([s]++top) ([Bcall EF_load [ ] (shift_reg a)] ++ lbi)).
  destruct IHlregs as [rs' [STAR [SAME OTHER]]].
  econstructor. split; [|split].
  - eapply star_trans with (t1:=E0) (t2:=E0); auto.
    { apply STAR. }
    eapply star_one. simpl. apply rtl_block_step. simpl.
    unfold n_load, sbind. simpl. eauto.
  - intros r H. destruct H.
    + subst. rewrite Regmap.gss. auto.
    + rewrite Regmap.gso. apply SAME. auto. apply not_shift_eq. intros Heq. subst. apply H2 in H. inv H.
  - intros r H. apply Decidable.not_or in H. destruct H as [NEQ IN].
    rewrite Regmap.gso. apply OTHER. auto. apply not_shift_eq. auto.
Qed.


(* Same as init_regs but makes the intermediate rm apparent for a better induction *)
Inductive initr: list Integers.Int.int -> list reg -> reg_map -> Prop :=
| initr_nil:
    initr nil nil empty_regmap
| initr_cons:
    forall val vals param params rm,
      initr vals params rm ->
      initr (val::vals) (param::params) (rm # param <- val).

Lemma init_regs_ok:
  forall vals params rm,
    init_regs vals params = OK rm <-> initr vals params rm.
Proof.
  intros vals params rm. generalize dependent params. generalize dependent rm. induction vals; intros.
  { simpl. destruct params; split; intros; inv H.
    constructor. auto. }
  split; intros.
  - destruct params; inv H. repeat do_ok. apply IHvals in HDO.
    constructor. auto.
  - destruct params; inv H. apply IHvals in H5. simpl. rewrite H5. simpl. auto.
Qed.

(* stepping to a state where the parameters have been loaded *)
Lemma generate_popargs_star:
  forall p rtl nc (params:list reg) (lbi:list block_instr) (vals top:list Integers.Int.int) (ei:exit_instr) (stk:stack) (mem:memory) rm,
    initr vals params rm ->
  exists rs',
    star (mixed_step p (Some (inr rtl))) nc
         (Halt_Block (BState (Bblock ((generate_popargs params) ++ lbi, ei)) init_regset), mkmut stk ((rev vals)++top) mem) E0
         (Halt_Block (BState (Bblock (lbi, ei)) rs'), mkmut stk top mem) /\
    (forall r, value_agree (rm # r) (Regmap.get (shift_reg r) rs')).
Proof.
  intros p rtl nc params lbi vals top ei stk mem rm INITR.
  generalize dependent lbi. generalize dependent top. generalize dependent vals. 
  generalize dependent rm.
  induction params; intros.
  { simpl. destruct vals; inv INITR. exists init_regset. split. simpl. apply star_refl. intros r.
    unfold empty_regmap, init_regset. rewrite Regmap.gi. rewrite PTree.gempty. constructor. }
  destruct vals as [|val vals]; inv INITR. 
  simpl. rewrite <- app_assoc. rewrite <- app_assoc. simpl.
  specialize (IHparams rm0 vals H4 (val::top) (Bcall EF_load [ ] (shift_reg a) :: lbi)).
  destruct IHparams as [rs' [STAR EVAL]].
  econstructor. split.
  - eapply star_trans with (t1:=E0) (t2:=E0); auto.
    { apply STAR. }
    eapply star_one. apply rtl_block_step. simpl.
    unfold n_load, sbind. simpl. eauto.
  - intros r. poseq_destr a r.
    + rewrite PTree.gss. rewrite Regmap.gss. constructor.
    + rewrite PTree.gso; auto. rewrite Regmap.gso; auto. apply not_shift_eq. auto.
Qed.

Lemma exec_pop_args':
  forall nb l stk top mem nc result stk' top' mem' nc',
    exec (jit.pop_args' nb l) naive_impl (mkmut stk top mem, nc) =
    SOK (result) (mkmut stk' top' mem', nc') ->
    exists args, 
    stk = stk' /\
    mem = mem' /\
    nc = nc' /\
    result = args ++ l /\
    top = (rev args) ++ top'.
Proof.
  intros nb l stk top mem nc result stk' top' mem' nc' H.
  generalize dependent l. generalize dependent top. generalize dependent result.
  induction nb; intros.
  { simpl in H. inv H. exists nil. simpl. auto. }
  simpl in H. repeat sdo_ok. destruct n. unfold n_load in HDO. simpl in HDO.
  destruct top; inv HDO. apply IHnb in H. destruct H as [args [S [M [N [R T]]]]]. subst.
  exists (args ++ [i]). repeat split; auto.
  - rewrite <- app_assoc. simpl. auto.
  - rewrite rev_app_distr. simpl. auto.
Qed.

Lemma exec_pop_args:
  forall nb stk top mem nc args stk' top' mem' nc',
    exec (jit.pop_args nb) naive_impl (mkmut stk top mem, nc) =
    SOK (args) (mkmut stk' top' mem', nc') ->
    stk = stk' /\
    mem = mem' /\
    nc = nc' /\
    top = (rev args) ++ top'.
Proof.
  intros nb stk top mem nc args stk' top' mem' nc' H. unfold jit.pop_args in H.
  apply exec_pop_args' in H. destruct H as [args' [S [M [N [R T]]]]]. subst.
  rewrite app_nil_r. auto.
Qed.



(** * Having matching stacks produces equivalent results  *)
(* The primitives that may add to the stack but not open it *)
(* every primitive except Open_SF *)
Inductive addstk_prim : forall T:Type, primitive T -> Prop :=
| addstk_save: forall i, addstk_prim unit (Prim_Save i)
| addstk_load: addstk_prim Integers.Int.int (Prim_Load)
| addstk_memset: forall x y, addstk_prim unit (Prim_MemSet x y)
| addstk_memget: forall x, addstk_prim Integers.Int.int (Prim_MemGet x)
| addstk_closesf: forall a b c, addstk_prim unit (Prim_CloseSF a b c)
| addstk_pushirsf: forall sf, addstk_prim unit (Prim_PushIRSF sf)
| addstk_install: forall f a, addstk_prim unit (Prim_Install_Code f a)
| addstk_loadc: forall a, addstk_prim Asm.program (Prim_Load_Code a)
| addstk_check: forall f, addstk_prim compiled_status (Prim_Check_Compiled f).
Arguments addstk_prim [T] _.

Lemma addstk_prim_same:
  forall (T:Type) (p:primitive T) (t:T) (stk1 stk2 stk1':stack) (top top':env) (mem mem':memory) (ac ac':asm_codes)
    (ADD: addstk_prim p)
    (EXEC: exec_prim p naive_impl (mkmut stk1 top mem, ac) = SOK t (mkmut stk1' top' mem', ac')),
  exists stk, stk1' = stk ++ stk1 /\
         exec_prim p naive_impl (mkmut stk2 top mem, ac) = SOK t (mkmut (stk++stk2) top' mem', ac').
Proof.
  intros T p t stk1 stk2 stk1' top top' mem mem' ac ac' ADD EXEC.
  destruct p; simpl; inv EXEC; inv ADD; auto.
  - unfold n_save. exists nil. simpl. auto.
  - unfold n_load in H0. simpl in H0. destruct top; inv H0.
    unfold n_load. exists nil. simpl. auto.
  - unfold n_memset in H0. simpl in H0. destruct (Integers.Int.lt i mem_size) eqn:SIZE; inv H0.
    exists nil. unfold n_memset. simpl. rewrite SIZE. auto.
  - unfold n_memget in H0. simpl in H0. destruct (Integers.Int.lt i mem_size) eqn:SIZE; inv H0.
    destruct (mem # (pos_of_int i)) eqn:MEM; inv H1.
    exists nil. unfold n_memget. simpl. rewrite SIZE. rewrite MEM. auto.
  - unfold n_closesf. simpl. exists [ASM_SF (i, i0, i1, top)]. simpl. auto.
  - unfold n_push_interpreter_stackframe in H0. simpl in H0. destruct top; inv H0.
    unfold n_push_interpreter_stackframe. simpl. exists [IR_SF i]. auto.
  - unfold n_install_code. simpl. exists nil. simpl. auto.
  - unfold n_load_code in H0. destruct a.
    + repeat sdo_ok. unfold n_load_prog_code in HDO. simpl in HDO. destruct (ac#f) eqn:AC; inv HDO.
      exists nil. unfold n_load_prog_code, sbind. simpl. rewrite AC. auto.
    + repeat sdo_ok. destruct a. simpl in H0. destruct (t0#l) eqn:CONT; inv H0.
      unfold n_load_prog_code in HDO. simpl in HDO. destruct (ac#f) eqn:AC; inv HDO.
      exists nil. unfold n_load_prog_code, sbind. simpl. rewrite AC. simpl. rewrite CONT. auto.
  - unfold n_check_compiled in H0. simpl in H0. destruct (ac#f) eqn:AC; inv H0.
    + exists nil. unfold n_check_compiled. simpl. rewrite AC. auto.
    + exists nil. unfold n_check_compiled. simpl. rewrite AC. auto.
Qed.


(* Typing free monads that only add to the stack *)
Inductive addstk_monad {T:Type}: free T -> Prop :=
| a_pure:
    forall (t:T),
      addstk_monad (pure t)
| a_error:
    forall (e:errmsg),
      addstk_monad (ferror e)
| a_impure:
    forall {R:Type} (p:primitive R) (cont: R -> free T)
      (ADDSTKCONT: forall (r:R), addstk_monad (cont r))
      (ADDSTKPRIM: addstk_prim p),
      addstk_monad (impure p cont).

Lemma addstk_bind:
  forall (A B:Type) (f:free A) (g: A -> free B)
    (ADDSTK_A: addstk_monad f)
    (ADDSTK_B: forall a, addstk_monad (g a)),
    addstk_monad (fbind f g).
Proof.
  intros A B f. generalize dependent B.
  induction f; intros.
  - simpl. auto.
  - simpl. repeat constructor.
    2: { inv ADDSTK_A. apply Classical_Prop.EqdepTheory.inj_pair2 in H2. subst. auto. }
    intros r. apply H; auto. inv ADDSTK_A.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H3. subst. auto.
  - simpl. constructor.
Qed.

Lemma addstk_try:
  forall (A:Type) (o: option A) (s:string),
    addstk_monad (try_option o s).
Proof.
  intros A o s. destruct o; simpl; constructor.
Qed.

Lemma addstk_fret':
  forall (A:Type) (r:res A),
    addstk_monad (fret' r).
Proof.
  intros A r. unfold fret'. destruct r; constructor.
Qed.

Ltac addstk_auto':=
  match goal with
  | [ |- context[addstk_monad(fret (?x))]] => constructor
  | [ |- context[addstk_monad(ferror (?x))]] => constructor
  | [ |- context[addstk_monad(pure (?x))]] => constructor
  | [ |- context[addstk_monad(impure ?x ?y)]] => constructor
  | [ |- context[addstk_prim ?x]] => constructor
  | [ |- context[addstk_monad (fprim ?x)]] => constructor
  | [ |- context[addstk_monad(fret' (?x))]] => apply addstk_fret'
  | [ |- context[addstk_monad(try_option ?x ?y)]] => apply addstk_try
  | [ |- context[addstk_monad(fbind ?x ?y)]] => apply addstk_bind
  | [ |- context[addstk_monad(fbind2 ?x ?y)]] => apply addstk_bind
  | [ |- context[addstk_monad(fbind3 ?x ?y)]] => apply addstk_bind
  | [ |- context[addstk_monad(fbind4 ?x ?y)]] => apply addstk_bind
  | [ |- context[addstk_monad(let (x, y) := ?z in _)]] => destruct z
  | [ |- context[addstk_monad (match ?x with
                            | _ => _
                            end)]] => destruct x
  end.

Ltac addstk_auto := intros; addstk_auto'.

Lemma addstk_same:
  forall (T:Type) (f:free T) (t:T) (stk1 stk2 stk1':stack) (top top':env) (mem mem':memory) (ac ac':asm_codes)
    (ADD: addstk_monad f)
    (EXEC: exec f naive_impl (mkmut stk1 top mem, ac) = SOK t (mkmut stk1' top' mem', ac')),
  exists stk, stk1' = stk ++ stk1 /\
         exec f naive_impl (mkmut stk2 top mem, ac) = SOK t (mkmut (stk++stk2) top' mem', ac').
Proof.
  intros T f. induction f; intros; inv EXEC; auto.
  { exists nil. simpl. auto. }
  repeat sdo_ok.
  assert (ADD_PRIM: addstk_prim prim).
  { inv ADD. apply Classical_Prop.EqdepTheory.inj_pair2 in H3. subst. auto. }
  assert (ADD_CONT: forall r, addstk_monad (cont r)).
  { inv ADD. apply Classical_Prop.EqdepTheory.inj_pair2 in H4. subst. auto. }
  destruct n. destruct m. exploit addstk_prim_same; eauto. intros.
  destruct H0 as [stkp [APP SAME]]. eapply H in H1. destruct H1 as [stkc [APPC SAMEC]].
  2: { apply ADD_CONT. }
  exists (stkc ++ stkp). unfold sbind. rewrite SAME. rewrite SAMEC. auto. subst. repeat rewrite app_assoc. auto.
Qed.

Lemma addstk_push_args:
  forall l, addstk_monad (jit.push_args l).
Proof.
  intros l. induction l; repeat addstk_auto.
  simpl. addstk_auto.
  simpl. repeat addstk_auto. intros. auto.
Qed.

Lemma addstk_irstep:
  forall irs, addstk_monad (ir_step irs).
Proof. unfold ir_step. repeat addstk_auto. unfold ir_int_step. repeat addstk_auto. Qed.

Lemma addstk_asmstep:
  forall ge xs, addstk_monad (ASMinterpreter.asm_int_step ge xs).
Proof.
  unfold ASMinterpreter.asm_int_step. repeat addstk_auto.
  unfold ASMinterpreter.asm_step. repeat addstk_auto.
  unfold ASMinterpreter.ext_prim_sem. repeat addstk_auto.
  unfold ASMinterpreter.prim_sem_dec. repeat addstk_auto.
Qed.

Lemma addstk_callee:
  forall loc, addstk_monad (jit.get_callee loc).
Proof. unfold jit.get_callee. repeat addstk_auto. Qed.

Lemma addstk_set_args:
  forall loc, addstk_monad (jit.set_up_args loc).
Proof. unfold jit.set_up_args. repeat addstk_auto. apply addstk_push_args. Qed.

Lemma addstk_retval:
  forall loc, addstk_monad (jit.get_retval loc).
Proof. unfold jit.get_retval. repeat addstk_auto. Qed.

Lemma addstk_target:
  forall loc, addstk_monad (jit.get_target loc).
Proof. unfold jit.get_target. repeat addstk_auto. Qed.

Lemma addstk_get_args:
  forall loc, addstk_monad (jit.get_args loc).
Proof.
  unfold jit.get_args. repeat addstk_auto.
  unfold jit.pop_args. generalize (nil:list Integers.Int.int).
  intros l a0. generalize dependent l. induction a0; intros; simpl; repeat addstk_auto.
  intros. apply IHa0.
Qed.

Lemma addstk_build:
  forall loc, addstk_monad (jit.build_rm loc).
Proof.
  unfold jit.build_rm. repeat addstk_auto.
  generalize (@nil Integers.Int.int). generalize (a0).
  intros n; induction n; intros; simpl; repeat addstk_auto.
  intros. apply IHn.
Qed.

(* To avoid some bug where Qed gets stuck in the main proof *)
Lemma invert_gen_close:
  forall caller_id cont_id retreg l,
    generate_close caller_id cont_id retreg = OK l ->
    exists cer con rr,
      int_of_pos caller_id = OK cer /\
      int_of_pos cont_id = OK con /\
      int_of_pos (shift_reg retreg) = OK rr /\
      l = [Bop (Op.Ointconst cer) [ ] caller_reg; Bop (Op.Ointconst con) [ ] cont_reg;
             Bop (Op.Ointconst rr) [ ] ret_reg; Bcall EF_close [caller_reg; cont_reg; ret_reg] void_reg].
Proof.
  unfold generate_close. intros caller_id cont_id retreg l H. repeat do_ok.
  exists i. exists i0. exists i1. eauto.
Qed.                            (* if I unfold afert intros, Qed is stuck *)

Lemma invert_push_callee:
  forall callee_id l,
    generate_push_callee callee_id = OK l ->
    exists cee,
      int_of_pos callee_id = OK cee /\
      l = [Bop (Op.Ointconst cee) [ ] callee_reg; Bcall EF_save [callee_reg] void_reg].
Proof.
  unfold generate_push_callee. intros callee_id l H. repeat do_ok. exists i. eauto.
Qed.                            (* same issue, Qed stuck if I intros before unfold *)


Theorem block_gen_forward:
  forall p nc fid f v params blockc entry contidx
    (FINDF: (prog_funlist p) # fid = Some f)
    (CURV: current_version f = v)
    (PARAMS: fn_params f = params)
    (NO_ASM: nc # fid = None)
    (BLOCKGEN: rtlgen fid v params = OK (blockc, entry, contidx)),
    forward_internal_simulation p p None (Some (inr (fid, blockc, entry, contidx))) nc nc.
Proof.
  intros p nc fid f v params blockc entry contidx FINDF CURV PARAMS NO_ASM BLOCKGEN.
  destruct (liveness_analyze v) as [live|] eqn:LIVE.
  2: { unfold rtlgen, transf_code in BLOCKGEN. repeat do_ok. inv LIVE. }
  destruct (defined_regs_analysis (ver_code v) params (ver_entry v)) as [def|] eqn:DEFS.
  2: { unfold rtlgen, transf_code in BLOCKGEN. repeat do_ok. inv DEFS. }
  apply Forward_internal_simulation with (fsim_match_states:=match_states v fid live def) (fsim_order:=order).
  - apply order_wf.
  - unfold call_refl, p_reflexive. intros s H. exists tt. inv H. destruct ms.
    apply match_refl. constructor. apply match_stack_same.
  - intros i s1 s2 r H H0. inv H0. inv H. constructor.
  - simpl. intros s1 t s1' STEP i s2 MATCH.
    inv MATCH.

    +                           (* match_refl *)
      inv STEP; try solve[inv NO_RTL]; try solve [inv RTL]; try solve [inv RTL_BLOCK].
      * destruct ms1. eapply addstk_same in STEP0 as [stk [APP SAME]]. 2: apply addstk_irstep. subst.
        exists tt. econstructor. split.
        ** left. apply plus_one. apply IR_step. apply SAME.
        ** apply match_refl.
           { unfold ir_step in SAME. repeat sdo_ok. destruct p0. simpl. destruct i; auto.
             destruct c; auto. }
           apply match_stack_app. auto.
      * destruct ms1. eapply addstk_same in STEP0 as [stk [APP SAME]]. 2: apply addstk_asmstep. subst.
        exists tt. econstructor. split.
        ** left. apply plus_one. apply x86_step. apply SAME.
        ** apply match_refl.
           { unfold ASMinterpreter.asm_int_step in SAME. repeat sdo_ok. destruct p0. simpl in SAME.
           destruct i; inv SAME; auto. repeat sdo_ok. destruct c; auto. }
           apply match_stack_app. auto.
      * destruct ms2. eapply addstk_same in CALLEE as [stk [APP SAME]]. 2: apply addstk_callee.
        eapply addstk_prim_same in NOT_COMPILED as [stk2 [APP2 SAME2]]; try constructor.
        apply app_same in APP2. subst.
        destruct ms3. eapply addstk_same in ARGS as [stk3 [APP3 SAME3]]. 2: apply addstk_get_args.
        poseq_destr fid fid0.
        ** apply code_entry in BLOCKGEN as [FRESH BLK].
           rewrite GETF in FINDF. inv FINDF.
           destruct loc.        (* we take different steps if we call from native or IR *)
         {                      (* call to the new RTLblock from NATIVE *)
           simpl in SAME. unfold n_load in SAME. repeat sdo_ok. simpl in HDO. destruct top; inv HDO.
           apply app_same in H1. inv H1.
           simpl in SAME3. unfold n_load in SAME3. repeat sdo_ok. simpl in HDO.
           destruct state_stacktop; inv HDO.
           apply exec_pop_args in SAME3. destruct SAME3 as [S1 [S2 [S3 S4]]]. subst. clear S3.
           apply app_same in S1. inv S1.
           exploit generate_popargs_star.
           { apply init_regs_ok. eauto. } intros H. destruct H as [rs' [STAR SAMER]].
          exists tt. econstructor. split.
           *** left. 
               eapply plus_left with (t1:=E0) (t2:=E0); auto.
               { eapply Call_RTL_Block; eauto.
                 simpl. unfold n_load, sbind. simpl. eauto.
                 simpl. unfold n_load, sbind. simpl. eauto. }
               eapply star_step with (t1:=E0) (t2:=E0); auto.
               { apply rtl_block_step. simpl. rewrite BLK. simpl. eauto. } (* fetching entry block *)
               unfold entry_block. 
               rewrite <- app_nil_r with (l:=generate_popargs (fn_params f)).
               eapply star_trans with (t1:=E0) (t2:=E0); auto.
               { apply STAR. }
               eapply star_one.
               { apply rtl_block_step. simpl. eauto. }
           *** simpl. apply match_block. auto. eapply def_analyze_init; eauto.
               unfold agree. intros r H. apply SAMER.
         }
         (* call to the new RTLblock from IR *)
         simpl in SAME. inv SAME. apply app_same in H1. inv H1.
         simpl in SAME3. inv SAME3. apply app_same in H1. inv H1.
         simpl in SAME2. unfold n_check_compiled in SAME2. simpl in SAME2.
         destruct (nc #fid0) eqn:NC; inv SAME2. clear NO_ASM.
         exploit generate_popargs_star.
         { apply init_regs_ok. eauto. } intros H. destruct H as [rs' [STAR SAMER]].
         exists tt. econstructor. split.
           *** left. 
               eapply plus_left with (t1:=E0) (t2:=E0); auto.
               { eapply Call_RTL_Block; eauto. simpl. eauto. 
                 simpl. unfold n_check_compiled, sbind. simpl. rewrite NC. eauto.
                 unfold jit.set_up_args. apply push_exec. }
               eapply star_step with (t1:=E0) (t2:=E0); auto.
               { apply rtl_block_step. simpl. rewrite BLK. simpl. eauto. } (* fetching entry block *)
               unfold entry_block. 
               rewrite <- app_nil_r with (l:=generate_popargs (fn_params f)).
               eapply star_trans with (t1:=E0) (t2:=E0); auto.
               { apply STAR. }
               eapply star_one.
               { apply rtl_block_step. simpl. eauto. }
           *** simpl. apply match_block. auto. eapply def_analyze_init; eauto.
               unfold agree. intros r H. apply SAMER.
        ** subst. exists tt. econstructor. split. (* calling any other function *)
           *** left. apply plus_one. eapply Call_IR; eauto.
               { simpl. unfold n_check_compiled, sbind. simpl.
                 simpl in SAME2. unfold n_check_compiled in SAME2. simpl in SAME2.
                 destruct (nc # fid0); inv SAME2. auto. }
               simpl. intros H. inv H. apply HEQ. auto.
           *** apply match_refl. auto. repeat rewrite app_assoc. apply match_stack_app. auto.
      * destruct ms2. destruct ms3. destruct ms4.
        eapply addstk_same in CALLEE as [stk [APP SAME]]. 2: apply addstk_callee.
        eapply addstk_prim_same in COMPILED as [stk2 [APP2 SAME2]]; try constructor.
        apply app_same in APP2. subst.
        eapply addstk_same in ARGS as [stk3 [APP3 SAME3]]. 2: apply addstk_set_args. subst.
        eapply addstk_prim_same in LOAD as [stk4 [APP4 SAME4]]; try constructor. subst.
        exists tt. econstructor. split.
        ** left. apply plus_one. eapply Call_x86; eauto. simpl. intros H. inv H.
           simpl in SAME2. unfold n_check_compiled in SAME2. simpl in SAME2. rewrite NO_ASM in SAME2.
           inv SAME2.
        ** apply match_refl. auto. repeat rewrite app_assoc. apply match_stack_app. auto.
      * destruct ms1. eapply addstk_same in RETVAL as [stk [APP SAME]]. 2: apply addstk_retval.
        destruct stk.
        2: { unfold jit.get_retval in SAME. destruct loc; inv SAME; repeat sdo_ok.
             - unfold n_load in HDO. simpl in HDO. destruct top; inv HDO.
               rewrite app_comm_cons in H1. apply app_same in H1. inv H1.
             - rewrite app_comm_cons in H1. apply app_same in H1. inv H1. }
        simpl in SAME. simpl in APP. subst.
        simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
        destruct state_stacktop; inv OPEN_SF. destruct stkir; inv H0. destruct s; inv H1.
        2: { destruct a, p0, p0. inv H0. }
        inv MATCH_STACK. inv MATCH_SF.
        ** exists tt. econstructor. split. (* returning to IR *)
           *** left. apply plus_one. eapply Return_IR.
               apply SAME. simpl. unfold n_open_stackframe. simpl. eauto. eauto.
           *** apply match_refl; auto.
        ** eapply transf_code_reentry in CODE as ENTRY; eauto. destruct ENTRY as [reentry [FRESH [REENTRY BLK]]].
           exploit generate_loads_star; eauto.
           { unfold live_def_regs in LIVE_REGS. repeat do_ok. apply nodup_elements. }
           intros [rs' [STAR [SAME' OTHER]]].
           exists tt. econstructor. split.
           *** left. eapply plus_left with (t1:=E0) (t2:=E0); auto.
               { eapply Return_RTL_Block with (fid:=fid); eauto. (* returning to the re-entry *)
                 - simpl. unfold n_open_stackframe, sbind. simpl. eauto.
                 - simpl. unfold n_save, sbind. simpl. eauto.
                 - simpl. unfold n_check_compiled, sbind. simpl. rewrite NO_ASM. auto.
                 - apply int_pos_correct in LBL. rewrite LBL. eauto. }
               eapply star_step with (t1:=E0) (t2:=E0); auto.
               { eapply rtl_block_step. simpl. rewrite BLK. simpl. eauto. } (* fetching *)
               unfold preamble_block. eapply star_step with (t1:=E0) (t2:=E0); auto.
               { eapply rtl_block_step. simpl. unfold n_load, sbind. simpl. eauto. } (* getting retreg *)
               rewrite <- app_nil_r with (l:=generate_loads lregs). rewrite <- app_nil_r with (l:=rev saved).
               eapply star_trans with (t1:=E0) (t2:=E0); auto.
               { apply STAR. }  (* loading all the live registers *)
               apply star_one.
               apply rtl_block_step. simpl. unfold sret. eauto.
           *** apply match_block; auto.
               { eapply def_analyze_correct; eauto. simpl. left. auto.
                 unfold def_dr_transf. rewrite CODE. apply define_insert. auto. }
               (* now we show that the restored regset agrees on live values *)
               eapply agree_transfer; eauto. simpl. left. auto.
               unfold agree. intros r H. unfold live_def_regs in LIVE_REGS. repeat do_ok.
               poseq_destr r retreg.
               { rewrite PTree.gss. rewrite OTHER. rewrite Regmap.gss. constructor.
                 rewrite <- Inl_In. rewrite PositiveSet.elements_spec1. rewrite PositiveSet.inter_spec.
                 intros HN. destruct HN. unfold reg_dead in H1. rewrite PositiveSet.remove_spec in H1. destruct H1.
                 apply H2. auto. }
               rewrite PTree.gso; auto.
               unfold defined_rs in HDO0. destruct (def_absstate_get call_lbl def) eqn:DEF; inv HDO0. unfold defined in DEFINED.
               destruct (rm # r) eqn:RMR.
               **** assert (H0: exists v, rm # r = Some v) by eauto. apply DEFINED in H0. rewrite <- RMR.
                    rewrite SAME'. apply AGREE. apply reg_list_live_subset. unfold reg_dead. rewrite PositiveSet.remove_spec.
                    unfold live_absstate_get. split; auto.
                    rewrite <- Inl_In. rewrite PositiveSet.elements_spec1. rewrite PositiveSet.inter_spec. split; auto.
                    rewrite PositiveSet.remove_spec. unfold live_absstate_get. split; auto.
               **** rewrite OTHER. rewrite Regmap.gso. 2: { apply not_shift_eq. auto. }
                    unfold init_regset. rewrite Regmap.gi. constructor.
                    intros HIN. rewrite <- Inl_In in HIN. rewrite PositiveSet.elements_spec1 in HIN. rewrite PositiveSet.inter_spec in HIN.
                    destruct HIN. apply DEFINED in H0. destruct H0. rewrite H0 in RMR. inv RMR.
      * destruct ms1. eapply addstk_same in RETVAL as [stk [APP SAME]]. 2: apply addstk_retval. 
        destruct stk.
        2: { unfold jit.get_retval in SAME. destruct loc; inv SAME; repeat sdo_ok.
             - unfold n_load in HDO. simpl in HDO. destruct top; inv HDO.
               rewrite app_comm_cons in H1. apply app_same in H1. inv H1.
             - rewrite app_comm_cons in H1. apply app_same in H1. inv H1. }
        simpl in SAME. simpl in APP. subst.
        simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
        destruct state_stacktop; inv OPEN_SF. destruct stkir; inv H0. destruct s; inv H1.
        destruct a, p0, p0. inv H0. inv MATCH_STACK. inv MATCH_SF.
        simpl in SET_RETVAL. unfold n_save in SET_RETVAL. inv SET_RETVAL.
        simpl in LOAD_CONT. simpl in LOAD_CONT. repeat sdo_ok. destruct a. simpl in LOAD_CONT.
        destruct (t # (pos_of_int cont_lbl)) eqn:CONT; inv LOAD_CONT.
        unfold n_load_prog_code in HDO. simpl in HDO. destruct (nc # (pos_of_int caller_fid)) eqn:NC; inv HDO.
        exists tt. econstructor. split.
        ** left. apply plus_one. eapply Return_x86.
           apply SAME. simpl. unfold n_open_stackframe. simpl. eauto.
           simpl. unfold n_save. simpl. eauto.
           { simpl. unfold n_load_prog_code, sbind. simpl. rewrite NC. simpl. rewrite CONT. eauto. }
           eauto.
        ** eapply match_refl; auto. 
      * destruct ms1. destruct ms2.
        eapply addstk_same in RETVAL as [stk [APP SAME]]. 2: apply addstk_retval. subst. simpl in OPEN_SF.
        unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF. destruct state_stacktop; inv OPEN_SF.
        destruct (stk ++ stkir) eqn:APP; inv H0.
        2: { destruct s; inv H1. destruct a. destruct p0. destruct p0. inv H0. }
        destruct stk; inv APP. destruct stkir; inv H. inv MATCH_STACK.
        exists tt. econstructor. split.
        ** left. apply plus_one. eapply Return_EOE; eauto. simpl.
           unfold n_open_stackframe. simpl. eauto.
        ** apply match_refl. auto. apply match_nil.
      * destruct ms1. destruct ms2.
        eapply addstk_same in TARGET as [stk [APP SAME]]. 2: apply addstk_target.
        eapply addstk_same in BUILD_RM as [stk2 [APP2 SAME2]]. 2: apply addstk_build. subst.
        exists tt. econstructor. split.
        ** left. apply plus_one. eapply Deopt; eauto.
        ** apply match_refl. auto. repeat rewrite app_assoc. apply match_stack_app. auto.

           
    + inv STEP. unfold ir_step in STEP0. repeat sdo_ok. (* match_block *)
      destruct p0 as [t next]. simpl. unfold live_dr_transf in AGREE.
      unfold ir_int_step in HDO. repeat sdo_ok. rename HDO1 into CODE.
      eapply same_code in CODE as C; eauto. destruct C as [blk [INSTR BLK]].
      destruct i; inv HDO.
      
      * inv INSTR.     (* Nop *)
        exists tt. exists (Halt_Block (BPF l rs), mkmut stkblk top mem). split; auto.
        ** left. eapply plus_left with (t1:=E0) (t2:=E0); auto.
           { eapply rtl_block_step. simpl. rewrite BLK. simpl. eauto. }
           eapply star_one; eauto.
           { apply rtl_block_step. simpl. eauto. }
        ** eapply match_block; eauto.
           { eapply def_analyze_correct; eauto. simpl. left. auto.
             unfold def_dr_transf. rewrite CODE. auto. }
           eapply agree_transfer; eauto. simpl. left. auto.

      * repeat sdo_ok. inv INSTR. (* Print *)
        exists tt. exists (Halt_Block (BPF l (Regmap.set void_reg (Vint Integers.Int.zero) rs)), mkmut stkblk top mem). split; auto.
        ** left. eapply agree_eval_reg in HDO0; eauto.
           2: { unfold reg_live. rewrite PositiveSet.add_spec. left. auto. }
           eapply plus_left with (t1:=E0) (t2:=print_event i); auto.
           { eapply rtl_block_step. simpl. rewrite BLK. simpl. eauto. }
           eapply star_step with (t1:=print_event i) (t2:=E0); auto.
           { apply rtl_block_step. simpl. unfold ASMinterpreter.prim_sem_dec. simpl. rewrite HDO0.
             simpl. eauto. }
           eapply star_one; eauto.
           { apply rtl_block_step. simpl. eauto. }
        ** eapply match_block; eauto.
           { eapply def_analyze_correct; eauto. simpl. left. auto.
             unfold def_dr_transf. rewrite CODE. auto. }
           eapply agree_transfer; eauto. simpl. left. auto. apply agree_void. eapply reg_live_agree. eauto.
           
      * repeat sdo_ok. unfold instr_to_block in INSTR. repeat do_ok. (* Call *) simpl.
        unfold generate_args in HDO3. unfold generate_retcall in BLK. repeat do_ok.
        apply invert_gen_close in HDO2. destruct HDO2 as [cer [con [rr [icer [icon [irr L]]]]]]. subst.
        apply invert_push_callee in HDO4. destruct HDO4 as [cee [icee L]]. subst.        
        assert (HEV: exists li, eval_list_int rs l2 li). (* saved regs can be evaluated to integers *)
        { eapply defined_agree; eauto. eapply reg_list_live_agree; eauto. }
        destruct HEV as [li HEV].
        assert (HEVARGS: eval_list_int rs l l1). (* arguments can be evaluated to integers *)
        { eapply agree_list; eauto. }        
        exists tt. econstructor.
        split; auto.
        ** left.           
           exploit generate_saves_star. apply HEV. intros [rs' [STARSAVE SAME]].           
           eapply plus_left with (t1:=E0) (t2:=E0); auto.
           { eapply rtl_block_step. simpl. rewrite BLK. simpl. eauto. } (* fetching *)
           eapply star_trans with (t1:=E0) (t2:=E0); auto.
           { apply STARSAVE. }  (* saving the live registers *)
           clear STARSAVE. 
           eapply star_step with (t1:=E0) (t2:=E0); auto.
           { apply rtl_block_step. simpl. eauto. } (* setting caller_reg *)
           eapply star_step with (t1:=E0) (t2:=E0); auto.
           { apply rtl_block_step. simpl. eauto. } (* setting cont_reg *)
           eapply star_step with (t1:=E0) (t2:=E0); auto.
           { apply rtl_block_step. simpl. eauto. } (* setting ret_reg *)
           eapply star_step with (t1:=E0) (t2:=E0); auto.
           { apply rtl_block_step. simpl. unfold ASMinterpreter.prim_sem_dec. simpl. (* closing the stackframe *)
             rewrite Regmap.gso. 2: { intros H. inv H. }
             rewrite Regmap.gss. rewrite Regmap.gso. 2: { intros H. inv H. }
             rewrite Regmap.gss. rewrite Regmap.gso. 2: { intros H. inv H. } rewrite Regmap.gss.
             simpl. unfold n_closesf. unfold sbind. eauto. }
           set (newrs := Regmap.set void_reg (Vint Integers.Int.zero)
                                    (Regmap.set ret_reg (Vint rr)
                                                (Regmap.set cont_reg (Vint con)
                                                            (Regmap.set caller_reg (Vint cer) rs')))).
           assert (HEVARGS': eval_list_int newrs l l1).
           { eapply same_shift_eval. 2: apply HEVARGS. unfold newrs. eapply same_shift_trans; eauto.
             eapply same_shift_trans. 2: eapply same_shift_set_void.
             eapply same_shift_trans. 2: { eapply same_shift_set. unfold ret_reg, IRtoRTLblock.shift. lia. }
             eapply same_shift_trans. 2: { eapply same_shift_set. unfold cont_reg, IRtoRTLblock.shift. lia. }
             eapply same_shift_set. unfold caller_reg, IRtoRTLblock.shift. lia. }
           exploit generate_pushargs_star. apply HEVARGS'. intros [rs'' [STARARGS SAME']].
           eapply star_trans with (t1:=E0) (t2:=E0); auto.
           { rewrite <- app_assoc. apply STARARGS. } (* pushing the arguments *)
           clear STARARGS. rewrite app_nil_r. simpl.
           eapply star_step with (t1:=E0) (t2:=E0); auto.
           { apply rtl_block_step. simpl. eauto. } (* pushing the number of arguments *)
           eapply star_step with (t1:=E0) (t2:=E0); auto.
           {  apply rtl_block_step. simpl. unfold ASMinterpreter.prim_sem_dec. simpl. (* pushing the return value *)
              rewrite Regmap.gss. simpl. unfold n_save. unfold sbind. eauto. }
           simpl. eapply star_step with (t1:=E0) (t2:=E0); auto.
           { apply rtl_block_step. simpl. eauto. } (* setting calling_reg *)
           eapply star_step with (t1:=E0) (t2:=E0); auto.
           { apply rtl_block_step. simpl. unfold ASMinterpreter.prim_sem_dec. simpl. (* pushing the callee *)
             rewrite Regmap.gss. simpl. unfold n_save. unfold sbind. eauto. }
           simpl. eapply star_step with (t1:=E0) (t2:=E0); auto.
           { apply rtl_block_step. simpl. eauto. } (* doing the RETCALL *)
           eapply star_step with (t1:=E0) (t2:=E0); auto.
           { apply rtl_block_step. simpl. unfold get_int_reg. rewrite Regmap.gss. simpl. eauto. }
           eapply star_step with (t1:=E0) (t2:=E0); auto.
           { eapply RTL_block_end. (* Final step, going into S_Call *)
             - unfold ASMinterpreter.get_checkpoint. rewrite Integers.Int.eq_true.
               rewrite Integers.Int.eq_false. eauto. intros H. inv H.
             - simpl. eauto. }
           eapply star_refl.
        ** unfold n_push_interpreter_stackframe in HDO. simpl in HDO. destruct top; inv HDO. 
           eapply match_call; eauto. 
           eapply match_cons; eauto.
           rewrite app_nil_r. eapply frame_opt; eauto.

      * inv INSTR. repeat sdo_ok. destruct (bool_of_int i) eqn:COND; inv H0. (* Cond *)
        ** exists tt. exists (Halt_Block (BPF l rs), mkmut stkblk top mem). split; auto.
           *** left.
               eapply plus_left with (t1:=E0) (t2:=E0); eauto.
               { eapply rtl_block_step. simpl. rewrite BLK. simpl. eauto. }
               apply star_one.
               { eapply rtl_block_step. simpl. eapply agree_cond in COND; eauto.
                 2: { unfold reg_live. rewrite PositiveSet.add_spec. left. auto. }
                 rewrite COND. simpl. eauto. }
           *** eapply match_block; eauto.
               { eapply def_analyze_correct; eauto. simpl. left. auto.
                 unfold def_dr_transf. rewrite CODE. auto. }
               eapply agree_transfer; eauto. simpl. left. auto. eapply reg_live_agree; eauto.
        ** exists tt. exists (Halt_Block (BPF l0 rs), mkmut stkblk top mem). split; auto.
           *** left. eapply plus_left with (t1:=E0) (t2:=E0); eauto.
               { eapply rtl_block_step. simpl. rewrite BLK. simpl. eauto. }
               apply star_one.
               { eapply rtl_block_step. simpl. eapply agree_cond in COND; eauto.
                 2: { unfold reg_live. rewrite PositiveSet.add_spec. left. auto. }
                 rewrite COND. simpl. eauto. }
           *** eapply match_block; eauto.
               { eapply def_analyze_correct; eauto. simpl. right. left. auto.
                 unfold def_dr_transf. rewrite CODE. auto. }
               eapply agree_transfer; eauto. simpl. right. left. auto. eapply reg_live_agree; eauto.

      * repeat sdo_ok. inv INSTR. (* Return *)
        eapply agree_eval_reg in HDO0; eauto.
        2: { unfold reg_live. rewrite PositiveSet.add_spec. left. auto. }
        exists tt. econstructor. split.
        ** left. eapply plus_left with (t1:=E0) (t2:=E0); auto.
           { apply rtl_block_step. simpl. rewrite BLK. simpl. eauto. }
           eapply star_step with (t1:=E0) (t2:=E0); auto.
           { apply rtl_block_step. simpl. unfold ASMinterpreter.prim_sem_dec. simpl.
             rewrite HDO0. simpl. unfold n_save. unfold sbind. eauto. }
           simpl. eapply star_step with (t1:=E0) (t2:=E0); auto.
           { apply rtl_block_step. simpl. eauto. }
           eapply star_step with (t1:=E0) (t2:=E0); eauto.
           { apply rtl_block_step. simpl. unfold get_int_reg. rewrite Regmap.gss. simpl. eauto. }
           eapply star_one.
           { eapply RTL_block_end. 
             - unfold ASMinterpreter.get_checkpoint. rewrite Integers.Int.eq_true. eauto.
             - eauto. }
        ** apply match_return. auto.
             
      * repeat sdo_ok. inv INSTR. (* Op *)
        destruct (transf_expr e) as [op lst] eqn:TRANSFEXPR. inv H0.
        eapply agree_eval_expr in HDO0; eauto.
        exists tt. exists (Halt_Block (BPF l (Regmap.set (shift_reg r) (Vint i) rs)), mkmut stkblk top mem).
        split; auto.
        ** left. eapply plus_left with (t1:=E0) (t2:=E0); eauto.
           { apply rtl_block_step. simpl. rewrite BLK. simpl. eauto. }
           eapply star_step with (t1:=E0) (t2:=E0); eauto.
           { apply rtl_block_step. simpl. rewrite HDO0. simpl. eauto. }
           eapply star_one.
           { apply rtl_block_step. simpl. eauto. }
        ** eapply match_block; eauto.
           { eapply def_analyze_correct; eauto. simpl. left. auto.
             unfold def_dr_transf. rewrite CODE. apply define_insert. auto. }
           eapply agree_transfer; eauto. simpl. left. auto.
           apply agree_insert_dead. eapply expr_live_agree; eauto. 

      * repeat sdo_ok. inv INSTR. (* MemSet *)
        unfold n_memset in HDO1. destruct (Integers.Int.lt i mem_size) eqn:RANGE; inv HDO1.        
        exists tt. exists (Halt_Block (BPF l (Regmap.set void_reg (Vint Integers.Int.zero) rs)), mkmut stkblk top (mem # (pos_of_int i) <- i0)).
        split; auto.
        ** left. eapply agree_eval_reg in HDO0; eauto.
           2: { unfold reg_live. rewrite PositiveSet.add_spec. left. auto. }
           eapply agree_eval_reg in HDO2; eauto.
           2: { unfold reg_live. rewrite PositiveSet.add_spec. right.
                rewrite PositiveSet.add_spec. left. auto. }
           eapply plus_left with (t1:=E0) (t2:=E0); eauto.
           { apply rtl_block_step. simpl. rewrite BLK. simpl. eauto. }
           eapply star_step with (t1:=E0) (t2:=E0); eauto.
           { apply rtl_block_step. simpl. unfold ASMinterpreter.prim_sem_dec. simpl.
             rewrite HDO0. rewrite HDO2. simpl. unfold sbind. unfold n_memset. rewrite RANGE.
             simpl. eauto. }
           apply star_one.
           { apply rtl_block_step. simpl. eauto. }             
        ** eapply match_block; eauto.
           { eapply def_analyze_correct; eauto. simpl. left. auto.
             unfold def_dr_transf. rewrite CODE. auto. }
           eapply agree_transfer; eauto. simpl. left. auto.
           apply agree_void. eapply reg_live_agree. eapply reg_live_agree. eauto.

      * repeat sdo_ok. inv INSTR. (* MemGet *)
        unfold n_memget in HDO0. destruct (Integers.Int.lt i mem_size) eqn:RANGE; inv HDO0.
        destruct (mem # (pos_of_int i)) eqn:MEM; inv H0.
        eapply agree_eval_reg in HDO1; eauto.
        2: { unfold reg_live. rewrite PositiveSet.add_spec. left. auto. }
        exists tt. exists (Halt_Block (BPF l (Regmap.set (shift_reg r) (Vint i0) rs)), mkmut stkblk top mem).
        split; auto.
        ** left. eapply plus_left with (t1:=E0) (t2:=E0); auto.
           { apply rtl_block_step. simpl. rewrite BLK. simpl. eauto. }
           eapply star_step with (t1:=E0) (t2:=E0); eauto.
           { apply rtl_block_step. simpl. unfold ASMinterpreter.prim_sem_dec. simpl. rewrite HDO1. simpl.
             unfold n_memget. rewrite RANGE. unfold sbind. simpl. rewrite MEM. eauto. }
           apply star_one.
           { apply rtl_block_step. simpl. eauto. }
        ** eapply match_block; eauto.
           { eapply def_analyze_correct; eauto. simpl. left. auto.
             unfold def_dr_transf. rewrite CODE. apply define_insert. auto. }
           eapply agree_transfer; eauto. simpl. left. auto.
           apply agree_insert_dead. eapply reg_live_agree. eauto.

      * destruct d as [ftgt ltgt]. repeat sdo_ok. (* Assume *)
        eapply agree_eval_reg in HDO0 as EVALRS; eauto.
        2: { unfold reg_live. apply PositiveSet.add_spec. left. auto. }
        destruct (bool_of_int i) eqn:GUARD.
        ** inv INSTR. inv H0.   (* Assume holds: going into the rest of the function *)
           exists tt. exists (Halt_Block (BPF l rs), mkmut stkblk top mem). split.
           *** left. eapply plus_left with (t1:=E0) (t2:=E0); auto.
               { apply rtl_block_step. simpl. rewrite BLK. simpl. eauto. }
               apply star_one.
               { apply rtl_block_step. simpl. eapply agree_cond in GUARD; eauto.
                 2: { unfold reg_live. apply PositiveSet.add_spec. left. auto. }
                 repeat do_ok. simpl. rewrite GUARD. simpl. eauto. }
           *** eapply match_block. auto.
               { eapply def_analyze_correct; eauto. simpl. left. auto.
                 unfold def_dr_transf. rewrite CODE. auto. }
               eapply agree_transfer; eauto. simpl. left. auto.
               eapply varmap_live_agree. eapply reg_live_agree. eauto.
        ** repeat sdo_ok. inv INSTR. repeat do_ok.
           apply int_pos_correct in HDO. apply int_pos_correct in HDO3.
           eapply agree_cond in GUARD; eauto.
           2: { unfold reg_live. rewrite PositiveSet.add_spec. left. auto. }
           unfold generate_varmap in HDO2. repeat do_ok.
           exploit agree_varmap; eauto.
           { eapply reg_live_agree; eauto. } intros [li [EVI CONS]].
           exploit generate_pushvm_star; eauto. intros [rs' [STAR SHIFT]].
           exists tt. econstructor. split.
           *** left. eapply plus_left with (t1:=E0) (t2:=E0); auto.
               { apply rtl_block_step. simpl. rewrite BLK. simpl. eauto. } (* fetching *)
               eapply star_step with (t1:=E0) (t2:=E0); auto.
               { apply rtl_block_step. simpl. rewrite GUARD. simpl. eauto. } (* going into deopt *)
               rewrite <- app_assoc. eapply star_trans with (t1:=E0) (t2:=E0); auto. 
               { apply STAR. }  (* pushing varmap *)
               simpl. eapply star_step with (t1:=E0) (t2:=E0); auto.
               { apply rtl_block_step. simpl. eauto. }
               eapply star_step with (t1:=E0) (t2:=E0); auto.
               { apply rtl_block_step. simpl. unfold ASMinterpreter.prim_sem_dec. simpl.
                 rewrite Regmap.gss. simpl. unfold n_save, sbind. eauto. } (* push length of varmap *)
               eapply star_step with (t1:=E0) (t2:=E0); auto.
               { apply rtl_block_step. simpl. eauto. }
               eapply star_step with (t1:=E0) (t2:=E0); auto.
               { apply rtl_block_step. simpl. unfold ASMinterpreter.prim_sem_dec. simpl.
                 rewrite Regmap.gss. simpl. unfold n_save, sbind. eauto. } (* push ltgt *)
               eapply star_step with (t1:=E0) (t2:=E0); auto.
               { apply rtl_block_step. simpl. eauto. }
               eapply star_step with (t1:=E0) (t2:=E0); auto.
               { apply rtl_block_step. simpl. unfold ASMinterpreter.prim_sem_dec. simpl.
                 rewrite Regmap.gss. simpl. unfold n_save, sbind. eauto. } (* push ftgt *)
               eapply star_step with (t1:=E0) (t2:=E0); auto.
               { apply rtl_block_step. simpl. eauto. }
               eapply star_step with (t1:=E0) (t2:=E0); auto.
               { apply rtl_block_step. simpl. unfold get_int_reg. rewrite Regmap.gss. simpl. eauto. }
               apply star_one.
               { eapply RTL_block_end; eauto. unfold ASMinterpreter.get_checkpoint.
                 rewrite Integers.Int.eq_false. rewrite Integers.Int.eq_false.
                 rewrite Integers.Int.eq_true. eauto. intros H. inv H. intros H. inv H. }
           *** simpl. apply match_deopt; auto.
               apply int_nat_correct in HDO4. rewrite HDO4. eapply eval_varmap_size; eauto.
               
    + inv STEP.                 (* match_call *)
      * simpl in CALLEE. inv CALLEE. simpl in ARGS0. inv ARGS0.
        simpl in NOT_COMPILED. unfold n_check_compiled in NOT_COMPILED. simpl in NOT_COMPILED.
        destruct (nc # fid0) eqn:NOCOMP; inv NOT_COMPILED.
        apply int_pos_correct in IFID. apply int_nat_correct in ILENGTH. apply eval_list_length in ARGS as SLENGTH.
        rename fid0 into callee. poseq_destr callee fid.
        ** 
          apply code_entry in BLOCKGEN as E. destruct E as [FRESH BLK].
          rewrite GETF in FINDF. inv FINDF.
          exploit generate_popargs_star.
          { apply init_regs_ok. eauto. } intros H. destruct H as [rs' [STAR SAME]].
          exists tt. econstructor.  (* calling the transformed function *)
          split.
          *** left. 
              eapply plus_left with (t1:=E0) (t2:=E0); auto.
               { eapply Call_RTL_Block; eauto. simpl. unfold n_load, sbind. simpl. eauto.
                 simpl. unfold n_check_compiled. simpl. rewrite NOCOMP. eauto.
                 simpl. unfold n_load, sbind. simpl. eauto. } (* Call step *)
               eapply star_step with (t1:=E0) (t2:=E0); auto.
               { apply rtl_block_step. simpl. rewrite BLK. simpl. eauto. } (* fetching entry block *)
               unfold entry_block. rewrite <- app_nil_r with (l:=rev args0).
               rewrite <- app_nil_r with (l:=generate_popargs (fn_params f)).
               eapply star_trans with (t1:=E0) (t2:=E0); auto.
               { apply STAR. }
               eapply star_one.
               { apply rtl_block_step. simpl. eauto. }
          *** apply match_block. auto. eapply def_analyze_init; eauto.
              unfold agree. intros r H. apply SAME.

        ** exists tt. econstructor.  (* calling another function *)
           split.
           *** left. apply plus_one. eapply Call_IR; eauto.
               unfold jit.get_callee. simpl. unfold n_load, sbind. simpl. rewrite IFID. eauto.
               simpl. unfold n_check_compiled, sbind. simpl. rewrite NOCOMP. eauto.
               simpl. unfold n_load, sbind. simpl. rewrite ILENGTH. rewrite SLENGTH.
               unfold jit.pop_args. rewrite <- app_nil_r with (l:=rev args0). rewrite <- rev_length.
               rewrite exec_pop. rewrite rev_involutive. rewrite app_nil_r. eauto.
               simpl. intros H. inv H. apply HEQ. auto.
           *** apply match_refl. constructor. auto.
               
      * simpl in CALLEE. inv CALLEE.
        simpl in COMPILED. unfold n_check_compiled in COMPILED. simpl in COMPILED. destruct (nc # fid0) eqn:COMP; inv COMPILED.
        apply int_pos_correct in IFID.
        simpl in LOAD. repeat sdo_ok. unfold n_load_prog_code in HDO. simpl in HDO. rewrite COMP in HDO. inv HDO. destruct a.
        exists tt. econstructor. split.
        ** left. apply plus_one. eapply Call_x86.
           simpl. unfold n_load, sbind. simpl. eauto.
           simpl. unfold n_check_compiled, sbind. simpl. rewrite COMP. eauto.
           simpl. unfold n_load, sbind. simpl. eauto.
           simpl. intros HEQ. inv HEQ. rewrite NO_ASM in COMP. inv COMP.
           simpl. unfold n_load_prog_code, sbind. simpl. rewrite COMP. eauto. eauto.
        ** simpl. unfold jit.set_up_args in ARGS0. apply exec_push in ARGS0. inv ARGS0. rewrite app_nil_r.
           apply match_refl. constructor. auto.
      * inv RTL.
      * inv RTL_BLOCK.

    + inv STEP.                 (* match_return *)
      * simpl in RETVAL. inv RETVAL. simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF. (* Return IR *)
        destruct top; inv OPEN_SF. rename H0 into OPEN_SF.
        destruct stkir; inv OPEN_SF. destruct s; inv H0.
        2: { destruct a. destruct p0. destruct p0. inv H1. }
        inv MATCH_STACK. inv MATCH_SF; simpl.
        ** exists tt. exists (Halt_IR (v, pc, rm # retreg <- retval), mkmut stk2 nil mem). split.
           *** left. apply plus_one. eapply Return_IR; eauto.
               simpl. unfold n_load, sbind. simpl. eauto.
               simpl. unfold n_open_stackframe, sbind; eauto.
           *** eapply match_refl. constructor. auto.
        ** eapply transf_code_reentry in CODE as ENTRY; eauto. destruct ENTRY as [reentry [FRESH [REENTRY BLK]]].
           exploit generate_loads_star; eauto.
           { unfold live_def_regs in LIVE_REGS. repeat do_ok. apply nodup_elements. }
           intros [rs' [STAR [SAME OTHER]]].
           exists tt. econstructor. split. (* returning to RTLblock *)
           *** left. eapply plus_left with (t1:=E0) (t2:=E0); auto.
               { eapply Return_RTL_Block with (fid:=fid); eauto. (* returning to the re-entry *)
                 - simpl. unfold n_load, sbind. simpl. eauto.
                 - simpl. unfold n_open_stackframe, sbind. simpl. eauto.
                 - simpl. unfold n_save, sbind. simpl. eauto.
                 - simpl. unfold n_check_compiled, sbind. simpl. rewrite NO_ASM. auto.
                 - apply int_pos_correct in LBL. rewrite LBL. eauto. }
               eapply star_step with (t1:=E0) (t2:=E0); auto.
               { eapply rtl_block_step. simpl. rewrite BLK. simpl. eauto. } (* fetching *)
               unfold preamble_block. eapply star_step with (t1:=E0) (t2:=E0); auto.
               { eapply rtl_block_step. simpl. unfold n_load, sbind. simpl. eauto. } (* getting retreg *)
               rewrite <- app_nil_r with (l:=generate_loads lregs). rewrite <- app_nil_r with (l:=rev saved).               
               eapply star_trans with (t1:=E0) (t2:=E0); auto.
               { apply STAR. }  (* loading all the live registers *)
               apply star_one.
               apply rtl_block_step. simpl. unfold sret. eauto.
           *** apply match_block; auto.
               { eapply def_analyze_correct; eauto. simpl. left. auto.
                 unfold def_dr_transf. rewrite CODE. apply define_insert. auto. }
               (* now we show that the restored regset agrees on live values *)
               eapply agree_transfer; eauto. simpl. left. auto.
               unfold agree. intros r H. unfold live_def_regs in LIVE_REGS. repeat do_ok.
               poseq_destr r retreg.
               { rewrite PTree.gss. rewrite OTHER. rewrite Regmap.gss. constructor.
                 rewrite <- Inl_In. rewrite PositiveSet.elements_spec1. rewrite PositiveSet.inter_spec.
                 intros HN. destruct HN. unfold reg_dead in H1. rewrite PositiveSet.remove_spec in H1. destruct H1.
                 apply H2. auto. }
               rewrite PTree.gso; auto.
               unfold defined_rs in HDO0. destruct (def_absstate_get call_lbl def) eqn:DEF; inv HDO0. unfold defined in DEFINED.
               destruct (rm # r) eqn:RMR.
               **** assert (H0: exists v, rm # r = Some v) by eauto. apply DEFINED in H0. rewrite <- RMR.
                    rewrite SAME. apply AGREE. apply reg_list_live_subset. unfold reg_dead. rewrite PositiveSet.remove_spec.
                    unfold live_absstate_get. split; auto.
                    rewrite <- Inl_In. rewrite PositiveSet.elements_spec1. rewrite PositiveSet.inter_spec. split; auto.
                    rewrite PositiveSet.remove_spec. unfold live_absstate_get. split; auto.
               **** rewrite OTHER. rewrite Regmap.gso. 2: { apply not_shift_eq. auto. }
                    unfold init_regset. rewrite Regmap.gi. constructor.
                    intros HIN. rewrite <- Inl_In in HIN. rewrite PositiveSet.elements_spec1 in HIN. rewrite PositiveSet.inter_spec in HIN.
                    destruct HIN. apply DEFINED in H0. destruct H0. rewrite H0 in RMR. inv RMR.

      * simpl in RETVAL. inv RETVAL. (* Return x86 *)
        inv MATCH_STACK.
        { simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
          destruct top; inv OPEN_SF. }
        inv MATCH_SF.
        2: { simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
             destruct top; inv OPEN_SF. }
        simpl in OPEN_SF. unfold n_open_stackframe in OPEN_SF. simpl in OPEN_SF.
        destruct top; inv OPEN_SF. rename H0 into OPEN_SF. destruct sf2; inv OPEN_SF.
        destruct a. destruct p0. destruct p0. inv H0.
        simpl in LOAD_CONT. unfold n_load_prog_code in LOAD_CONT. repeat sdo_ok. destruct a.
        simpl in HDO. simpl in LOAD_CONT. destruct (nc # (pos_of_int caller_fid)) eqn:NC; inv HDO.
        destruct (t # (pos_of_int cont_lbl)) eqn:CONT; inv LOAD_CONT.
        exists tt. econstructor. split.
        ** left. apply plus_one. eapply Return_x86.
           simpl. unfold n_load, sbind. simpl. eauto.
           simpl. unfold n_open_stackframe, sbind. simpl. eauto.
           simpl. unfold n_save, sbind. simpl. eauto.
           simpl. unfold n_load_prog_code, sbind. simpl. rewrite NC. simpl. rewrite CONT. eauto. eauto.
        ** simpl in SET_RETVAL. unfold n_save in SET_RETVAL. inv SET_RETVAL.
           apply match_refl. constructor. auto.
      * inv RTL.                     (* Return RTL *)
      * inv RTL_BLOCK.
      * simpl in RETVAL. inv RETVAL. (* Return EOE *)
        exists tt. exists (EOE retval, ms2). split.
        ** left. apply plus_one. eapply Return_EOE.
           { simpl. unfold n_load. unfold sbind. simpl. eauto. }
           simpl in OPEN_SF. simpl. unfold n_open_stackframe in *.
           simpl in OPEN_SF. simpl. destruct top; inv OPEN_SF. destruct (stkir); inv H0.
           2: { destruct s; inv H1. destruct a. destruct p0. destruct p0. inv H0. }
           inv MATCH_STACK. eauto.
        ** destruct ms2. apply match_refl. constructor. apply match_stack_same.

    + inv STEP.                 (* match_deopt *)
      simpl in TARGET. inv TARGET. simpl in BUILD_RM. inv BUILD_RM.
      exists tt. econstructor. split.
      * left. apply plus_one. eapply Deopt; eauto.
        { simpl. unfold n_load, sbind. simpl. eauto. }
        { simpl. unfold n_load, sbind. simpl. rewrite exec_bind. unfold sbind.
          erewrite exec_get_varmap; eauto.
          apply construct_ok in CONS. rewrite app_nil_r. rewrite CONS. simpl. eauto. }
      * apply match_refl; simpl; auto.
Qed.


Theorem block_gen_correct:
  forall p nc fid f v params blockc entry contidx
    (FINDF: (prog_funlist p) # fid = Some f)
    (CURV: current_version f = v)
    (PARAMS: fn_params f = params)
    (NO_ASM: nc # fid = None)
    (BLOCKGEN: rtlgen fid v params = OK (blockc, entry, contidx)),
    backward_internal_simulation p p None (Some (inr (fid, blockc, entry, contidx))) nc nc.
Proof.
  intros p nc fid f v params blockc entry contidx FINDF CURV PARAMS NO_ASM BLOCKGEN.
  apply internal_simulations.forward_to_backward_simulation.
  - eapply block_gen_forward; eauto.
  - apply mixed_receptive.
  - apply mixed_determinate. unfold not. intros H. inv H.
    rewrite NAT_RTL in NO_ASM. inv NO_ASM.
Qed.    

