(* Assume insertion: inserting Assume instructions *)
(* A pass of the middle-end optimizer *)
(* To insert an assume, you need a guard (what to speculate on) *)
(* And you need a label where there is an anchor, that you want to copy the metadata of *)
(* And the Assume is inserted next to that Anchor instruction *)

Require Import List.
Require Import Coqlib.
Require Import Maps.
Require Import IR.
Require Import Coq.MSets.MSetPositive.
Require Import def_regs.
Require Import common.
Require Import Errors.
Require Import monad.

(** * Guard checking  *)
(* To ensure that the Assume does not intriduce bugs, *)
(* We check that the guard can evaluate without errors *)
Definition check_reg (r:reg) (def:regset) : bool :=
  PositiveSet.mem r def.

Definition check_expr (e:expr) (def:regset) : bool :=
  match e with
  | BIN bop r1 r2 => andb (check_reg r1 def) (check_reg r2 def)
  | UNA uop r => check_reg r def
  | ZAR z => true
  end.


(* making sure that the guard can evaluate, given a set of defined registers *)
(* Fixpoint check_guard (guard:list expr) (def:regset): bool := *)
(*   match guard with *)
(*   | nil => true *)
(*   | e::guard' => *)
(*     andb (check_expr e def) (check_guard guard' def) *)
(*   end.    *)
(* DEPRECATED until we allow lists of guards *)


(** * The optimization that inserts Assume directly after an Anchor *)

(* Verify that the assume can be inserted: no code between assume and anchor *)
Definition validator (v:version) (anc_lbl: label) (guard:expr) (params: list reg): res unit :=
  match ((ver_code v) # anc_lbl) with
  | Some (Anchor _ _ next) =>
    do abs <- try_op (defined_regs_analysis (ver_code v) params (ver_entry v)) "Def_regs analysis failed";
      do def_regs <- OK(def_absstate_get anc_lbl abs);
      match def_regs with
      | DefFlatRegset.Inj def =>
        match (check_expr guard def) with
        | true => OK tt
        | false => Error ((MSG "The guard might evaluate to an error")::nil)
        end
      | DefFlatRegset.Top => Error ((MSG "The analysis couldn't get the exact set of defined registers: TOP")::nil)
      | DefFlatRegset.Bot => Error ((MSG "The analysis couldn't get the exact set of defined registers: BOT")::nil)
      end
  | _ => Error ((MSG "Not pointing to a valid Anchor")::nil)
  end.

(* Returns the version where the Assume has been inserted *)
Definition insert_assume_version (v:version) (fid:fun_id) (guard:expr) (ancl:label) (params:list reg): res version :=
  do code <- OK(ver_code v);
    do freshlbl <- OK (fresh_sug (Pos.succ ancl) code);
    do _ <- validator v ancl guard params; (* validating that the assume can be inserted *)
    match (code # ancl) with
    | Some (Anchor tgt vm next) =>
      do instr <- try_op (code # next) "Next Label is not used in the function";
        do update_anc <- OK (code # ancl <- (Anchor tgt vm freshlbl));
        do new_code <- OK (update_anc # freshlbl <- (Assume guard tgt vm next));
        (* in the new assume, the deopt target and the varmap are copied from the anchor *)
        OK (mk_version new_code (ver_entry v))
    | _ => Error ((MSG "Not pointing to a valid Anchor")::nil)
    end.

(* The optimization pass *)
Definition insert_assume (fid: fun_id) (guard:expr) (anc_lbl: label) (p:program): res program :=
  do f <- try_op (find_function_ir fid p) "Function to optimize not found";
    do v <- OK(current_version f); (* the optimized code if it exists, the base version otherwise *)
    do newv <- insert_assume_version v fid guard anc_lbl (fn_params f);
    do new_program <- OK (set_version p fid newv);
    OK (new_program).
    

Definition safe_insert_assume (p:program) (fid:fun_id) (guard:expr) (anc_lbl: label): program :=
  safe_res (insert_assume fid guard anc_lbl) p.
