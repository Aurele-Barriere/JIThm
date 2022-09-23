(* Anchor insertion: inserting Anchor instructions *)
(* Such instructions act as templates for the insertion of speculation *)
(* This is the first pass of the dynamic optimizer *)

Require Import List.
Require Import Coqlib.
Require Import Maps.
Require Import IR.
Require Import Coq.MSets.MSetPositive.
Require Import liveness.
Require Import def_regs.
Require Import common.
Require Import monad.
Require Import monad_impl.
Require Import Errors.

(* The identity varmap for the set of defined registers *)
(* Maps to each defined register its current value *)
Definition identity_varmap (rs:regset) : varmap :=
  map (fun r => (r, UNA (uplus Integers.Int.zero) r)) (PositiveSet.elements rs).
(* TODO: we could have an unary expression that is just a register, without this need to do r + 0 *)

Definition defined_rs (abs:def_abs_state) (l:label) : option regset :=
  match (def_absstate_get l abs) with
  | DefFlatRegset.Top => None       (* The analysis wasn't precise enough *)
  | DefFlatRegset.Inj rs => Some rs
  | DefFlatRegset.Bot => None       (* Did not converge *)
  end.

(* The list of labels where we must insert Anchors has to be cleaned *)
(* We can't allow inserting twice at the same place: no duplicates in the list *)
(* And labels must be associated with some code in the original code *)
(* And we can't insert if the analysis failed to get the exact set of defined registers *)
Definition remove_dup (l:list label): list label := nodup Pos.eq_dec l.

Definition is_used (c:code) (l:label) : bool :=
  match (c # l) with
  | Some _ => true
  | None => false
  end.

Definition filter_unused (c:code) (l:list label) := filter (is_used c) l.

Definition is_analyzed (abs:def_abs_state) (l:label) : bool :=
  match (defined_rs abs l) with
  | Some _ => true
  | None => false
  end.

Definition filter_analyzed (abs:def_abs_state) (l:list label) := filter (is_analyzed abs) l.

Definition clean_label_list (def:def_abs_state) (c:code) (l:list label) : list label :=
  filter_analyzed def (filter_unused c (remove_dup l)).

(* The spacing between the inserted Anchor and the replaced instruction *)
(* Used as heuristics for the fresh_label procedure *)
(* Set to 1 for now, could be an external parameter *)
Definition spacing: positive := xH.

Definition insert_single_anchor (base_c:code) (c:code) (fid:fun_id) (lbl:label) (live:live_abs_state) (def:def_abs_state): res code :=
  do instr <- try_op (c # lbl) "Label is not used in the function"; (* this shouldn't happen (filter_unused) *)
  do rs_def <- try_op (defined_rs def lbl) "Defined regs analysis failed"; (* this shouldn't happen (filter_analyzed) *)
  do rs_live_before <- OK (live_dr_transf base_c lbl (live_absstate_get lbl live));
  (* base_c is needed to remember what was the code like before 
     all the optimisations, in order to apply the transfer function *)
  do identity <- OK (identity_varmap (PositiveSet.inter rs_def rs_live_before));
  (* we assign all the registers that are both defined at the instruction 
     and live before the instruction *)
  do freshlbl <- OK (fresh_sug (Pos.add lbl spacing) c);
  do move_instr <- OK (c # freshlbl <- instr); (* moving the old instruction *)
  (* constructing the Anchor instruction *)
  do anc_instr <- OK (Anchor (fid, lbl) identity freshlbl); (* deoptimizing to the same function *)
  do new_code <- OK (move_instr # lbl <- anc_instr);           (* inserting the anchor *)
  OK new_code.


Fixpoint insert_list_anchor (base_c:code) (c:code) (fid:fun_id) (lbllist:list label) (live:live_abs_state) (def:def_abs_state): res code :=
  match lbllist with
  | nil => OK c
  | lbl::l => do newc <- insert_single_anchor base_c c fid lbl live def;
              insert_list_anchor base_c newc fid l live def
  end.

Definition anc_insert_version (v:version) (fid:fun_id) (lbllist:list label) (live:live_abs_state) (def:def_abs_state) : res version :=
  do code_ins <- insert_list_anchor (ver_code v) (ver_code v) fid lbllist live def;
  OK (mk_version code_ins (ver_entry v)).

(* Returns the base version and checks that there is no optimized version *)
Definition check_no_opt (f:function): res version :=
  match (fn_opt f) with
  | None => OK (fn_base f)
  | Some _ => Error ((MSG "Insertion in previously optimized functions is not supported yet")::nil)
  end.

(* fid is the identifier of the function to insert anchor in *)
(* lbllist is the places we want to insert anchors at, just before the current instruction *)
Definition insert_anchor (fid:fun_id) (lbllist: list label) (p:program) : res program :=
  do f <- try_op (find_function_ir fid p) "Function to optimize not found";
  do v <- check_no_opt f;      (* gets the base version and checks that there is no opt version *)
  do params <- OK (fn_params f);
  do live <- try_op (liveness_analyze v) "Liveness analysis failed";
  do def <- try_op (defined_regs_analysis (ver_code v) (fn_params f) (ver_entry v)) "Def_regs analysis failed";
  do code <- OK (ver_code v);
  do clean_list <- OK (clean_label_list def code lbllist);
  do new_ver <- anc_insert_version v fid clean_list live def;
  do new_prog <- OK (set_version p fid new_ver);
  OK (new_prog).

(* Tries to insert all possible Anchors *)
Definition insert_all_anchors (fid:fun_id) (p:program): res program :=
  do f <- try_op (find_function_ir fid p) "Function to optimize not found";
  do v <- check_no_opt f;      (* gets the base version and checks that there is no opt version *)
  do params <- OK (fn_params f);
  do live <- try_op (liveness_analyze v) "Liveness analysis failed";
  do def <- try_op (defined_regs_analysis (ver_code v) (fn_params f) (ver_entry v)) "Def_regs analysis failed";
  do code <- OK (ver_code v);
  do clean_list <- OK (clean_label_list def code (map fst (PTree.elements code)));
  do new_ver <- anc_insert_version v fid clean_list live def;
  do new_prog <- OK (set_version p fid new_ver);
  OK (new_prog).


Definition safe_insert_anchor (p:program) (fid: fun_id) (lbllist:list label): program :=
  safe_res (insert_anchor fid lbllist) p.
