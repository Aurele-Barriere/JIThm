(* An intermediate language between our IR and RTL *)
Require Import RTL.
Require Import Globalenvs.
Require Import Coqlib.
Require Import Values.
Require Import Integers.
Require Import Maps.
Require Import common.
Require Import Smallstep.
Require Import primitives.
Require Import Registers.


(** * RTLblock  *)
(* we first define an alternate version of RTL where we have blocks of instructions *)
(* The IR will first be transformed to RTLblock, then to RTL *)


(* Instructions inside of blocks *)
(* Compared to RTL, we don't see the next PC, these will be put in a list *)
(* The only possible calls are calls to external primitives *)
Inductive block_instr : Type :=
| Bop: Op.operation -> list reg -> reg -> block_instr
| Bcall: ext_primitive -> list reg -> reg -> block_instr.

(* At the end of a block *)
(* All possible returns need return a register (not an option) *)
Inductive exit_instr: Type :=
| Bnop : label -> exit_instr
| Bcond : Op.condition -> list reg -> label -> label -> exit_instr
| Breturn : reg -> exit_instr.


(* Blocks that we generate that correspond to our IR instructions *)
(* Either Basic blocks: sequential instructions ending in an exit_instr *)
(* Or a Conditional block: either the condition evaluates to TRUE, then we go to the next label  *)
(* And if false we go through another basic block: the DEOPT branch *)
Definition basic_block : Type := list block_instr * exit_instr.

Inductive block : Type :=
| Bblock : basic_block -> block
| Cblock : Op.condition -> list reg -> label -> basic_block -> block.
                                 

(* Blocks are indexed by labels *)
Definition block_code: Type := PTree.t block.

(* A program can hold a single RTL function during compilation *)
Definition cont_idx: Type := PTree.t label.
Definition RTLblockfun: Type := fun_id * block_code * label * cont_idx.

Definition get_block (rtlb:RTLblockfun) (lbl:positive) : option block :=
  match rtlb with
  | (fid, blkc, entry, contidx) =>
    PTree.get lbl blkc
  end.

(** * Semantic States *)
(* no memory, no stack: our instructions don't modify them *)
Inductive block_state : Type :=
| BPF: label -> regset -> block_state (* Pre-fetching: At a label *)
| BState: block -> regset -> block_state (* Inside a block *)
| BFinal: int -> block_state.

Definition init_regset : regset :=
  Regmap.init Vundef.

(** * Evaluating Operations *)
(* Partial functions that don't need a global env or a stack pointer *)
(* We'll show that all the expr we generated work for these functions *)
(* And we'll show that these coincide with the full functions *)
Require Import Op.


(* Only for the addressing we generate *)
Definition block_eval_addressing32 (addr: addressing) (vl: list val) : option val :=
  match addr, vl with
  | Aindexed n, v1::nil =>
    Some (Val.add v1 (Vint (Int.repr n)))
  | Aindexed2 n, v1::v2::nil =>
    Some (Val.add (Val.add v1 v2) (Vint (Int.repr n)))
  | _, _ => None
  end.


Lemma eval_addressing_correct:
  forall F V (ge:Genv.t F V) sp addr vl v,
    block_eval_addressing32 addr vl = Some v ->
    eval_addressing32 ge sp addr vl = Some v.
Proof.
  intros F V ge sp addr vl v H. destruct addr; simpl; inv H; auto.
Qed.
  
(* Only for the conditions we generate *)
Definition block_eval_condition (cond: condition) (vl: list val): option bool :=
  match cond, vl with
  | Ccomp c, v1 :: v2 :: nil => Val.cmp_bool c v1 v2
  | Ccompimm c n, v1 :: nil => Val.cmp_bool c v1 (Vint n)
  | _, _ => None
  end.

Lemma eval_condition_correct:
  forall m cond vl b,
    block_eval_condition cond vl = Some b ->
    eval_condition cond vl m = Some b.
Proof.
  intros m cond vl b H. destruct cond; inv H; auto.
Qed.

Definition optval_of_optbool (ob:option bool) : option val :=
  match ob with
  | Some true => Some Vtrue
  | Some false => Some Vfalse
  | None => None
  end.

(* Only for the operations we generate *)
Definition block_eval_operation (op: operation) (vl: list val): option val :=
  match op, vl with
  | Ointconst n, nil => Some (Vint n)
  | Oneg, v1::nil => Some (Val.neg v1)
  | Osub, v1::v2::nil => Some (Val.sub v1 v2)
  | Omul, v1::v2::nil => Some (Val.mul v1 v2)
  | Omulimm n, v1::nil => Some (Val.mul v1 (Vint n))
  | Olea addr, _ => block_eval_addressing32 addr vl (* partial version *)
  | Ocmp c, _ => optval_of_optbool (block_eval_condition c vl) (* partial version *)
  | Omod, v1::v2::nil => Val.mods v1 v2
  | _, _ => None
  end.


Lemma eval_operation_correct:
  forall F V (ge:Genv.t F V) sp m op vl v,
    block_eval_operation op vl = Some v ->
    eval_operation ge sp op vl m = Some v.
Proof.
  intros F V ge sp m op vl v H. destruct op; simpl; inv H; auto.
  - rewrite H1. eapply eval_addressing_correct in H1. eauto.
  - destruct (block_eval_condition cond vl) eqn:COND; inv H1.
    eapply eval_condition_correct in COND. rewrite COND. destruct b; inv H0; simpl; auto.
Qed.
