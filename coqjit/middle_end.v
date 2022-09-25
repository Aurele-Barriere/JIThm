(* Middle-end optimizer *)
(* Inerting Speculation in CoreIR programs *)

Require Import RTL.
Require Import IR.
Require Import monad.
Require Import common.
Require Import Coqlib.
Require Import backend.
Require Import primitives.
Require Import anchor_insertion.
Require Import assume_insertion.
Require Import anchor_removal.
Require Import profiler_types.
Require Import Errors.
Require Import monad.

(* Inserting Anchors in all functions according to the profiler wish *)
Fixpoint process_anc_list (p:program) (l:list (fun_id * list label)): program :=
  match l with
  | nil => p
  | (fid, anc_lbl)::l' => process_anc_list (safe_insert_anchor p fid anc_lbl) l'
  end.

(* Processing each middle_end optimization sugeested by the profiler *)
(* Using the safe optimizations: if one fails, it is just ignored by the optimizer *)
Fixpoint process_optim_list (p:program) (l:list (fun_id * middle_wish)): program :=
  match l with
  | nil => p
  | (fid, AS_INS guard anc_lbl)::l' => process_optim_list (safe_insert_assume p fid guard anc_lbl) l'
  end.

Definition middle_end (ps:profiler_state) (p:program): res program :=
    do optims <- OK (middle_end_suggestion ps);
    do fs_list <- OK (anchors_to_insert ps);
    do pfs <- OK (process_anc_list p fs_list);
    do newp <- OK (process_optim_list pfs optims);
    OK (lowering newp).

(* An error in optimization should not stop the execution *)
Definition safe_middle_end (ps:profiler_state) (p:program): program :=
  safe_res (middle_end ps) p.


