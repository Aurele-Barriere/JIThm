(* Common definitions for the JIT compiler *)

Require Export Coqlib.
Require Export String.
Require Export Maps.

(* Identifying functions and labels in our programs *)
Definition label: Type := positive.
Definition fun_id: Type := positive.


(* Notations for maps *)
Notation "a # b" := (PTree.get b a) (at level 1).
Notation "a # b <- c" := (PTree.set b c a) (at level 1, b at next level).

(* A JIT execution is a serie of optimization or execution steps *)
(* jit_status represents these two types of steps *)
Inductive jit_status: Type :=
| Exe                           (* execution *)
| Opt.                           (* optimization (middle-end and backend) *)


(* Destructing on the equality of two ppositives *)
Ltac poseq_destr b1 b2 :=
  let HEQ := fresh "HEQ" in
  destruct (Pos.eqb b1 b2) eqn:HEQ; [apply Pos.eqb_eq in HEQ; subst | apply Pos.eqb_neq in HEQ].

(** * Optimization hints  *)
(* We allow annotations in our program, to help the dynamic optimizer *)
(* A Frontend can use this for instance to guide speculation *)
Parameter hint: Type.

(** * Sum Type *)
(* used for the return type of functions to iter *)
Inductive itret (A I:Type): Type := (* I is the type of intermediate states *)
| Done: A -> itret A I
| Halt: I -> itret A I.
Arguments Done [A I].
Arguments Halt [A I].

Require Import Integers.
Require Import Events.

Definition print_event (i:int) : trace :=
  (Event_annot "PRINT"%string ((EVint i)::nil))::nil.
