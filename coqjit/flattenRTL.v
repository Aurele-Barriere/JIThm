(* ransforming RTLblock into RTL *)

Require Import common.
Require Import monad.
Require Import Errors.
Require Import RTL.
Require Import RTLblock.
Require Import IR.
Require Import primitives.

Definition basic_transf_block_instr (bi: block_instr) (succ:node) : RTL.instruction :=
  match bi with
  | Bop op args dest => Iop op args dest succ
  | Bcall ef args dest => Icall (EF_sig ef) (inr (EF_ident ef)) args dest succ
  end.

Definition transf_block_instr (c: res (RTL.code * node)) (bi: block_instr): res (RTL.code * node) :=
  do (rtlc, next) <- c;
  let next' := Pos.succ next in
  let instr := basic_transf_block_instr bi next' in
  OK (PTree.set next instr rtlc, next').

Definition basic_transf_exit_instr (ei: exit_instr) : RTL.instruction :=
  match ei with
  | Bnop succ => Inop succ
  | Bcond op args ifso ifnot => Icond op args ifso ifnot
  | Breturn r => Ireturn (Some r)
  end.

Definition transf_exit_instr (c: res (RTL.code * node)) (ei: exit_instr): res (RTL.code * node) :=
  do (rtlc, next) <- c;
  let instr := basic_transf_exit_instr ei in
  OK (PTree.set next instr rtlc, Pos.succ next).

Definition transf_basic_block (c: res (RTL.code * node)) (bb: basic_block): res (RTL.code * node) :=
  let (instrs, exit) := bb in
  let c' :=  List.fold_left transf_block_instr instrs c in
  transf_exit_instr c' exit.

Definition transf_block (c: res (RTL.code * node)) (lbl: node) (b: block): res (RTL.code * node) :=
  match b with
  | Bblock bb =>
      do (rtlc, next) <- c;
      let rtlc' := PTree.set lbl (Inop next) rtlc in
      transf_basic_block (OK (rtlc', next)) bb
  | Cblock op args if_true bb =>
      do (rtlc, next) <- c;      
      let rtlc' := PTree.set lbl (Icond op args next if_true ) rtlc in
      transf_basic_block (OK (rtlc', next)) bb
  end.

Definition flatten (rtlb:RTLblockfun) : res RTLfun :=
  let '(fid, code, entry, ci) := rtlb in
  let fresh := fresh_label code in
  do (rtl_code, _) <-  PTree.fold transf_block code (OK (PTree.empty RTL.instruction, fresh));
  OK (fid, rtl_code, entry, ci).

