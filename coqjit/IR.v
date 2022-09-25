(* An IR for the JIT *)
(* A simplified equivalent to SpecIR/CoreIR *)
(* This IR is translated to RTL for later native code generation *)

Require Import RTL.
Require Import RTLblock.
Require Import Asm.
Require Import Globalenvs.
Require Import Coqlib.
Require Import Values.
(* the only values this language uses are machine integers *)
Require Import Integers.
(* in particular, we can't reference the CompCert Memory, which does not exsist for this language *)
Require Import Maps.
Require Import common.
Require Import Smallstep.



(** * Syntax *)
Definition reg: Type := positive. (* same def as in RTL *)

(* binary operations, with 2 registers as arguments *)
Inductive bin_op: Type :=
| bplus : bin_op
| bneg : bin_op
| bmul : bin_op
| beq  : bin_op
| blt : bin_op
| bmod : bin_op.

(* unary operations, with 1 register as argument *)
Inductive un_op: Type :=
| uneg : un_op
| ueqzero : un_op
| uplus : int -> un_op
| umul : int -> un_op.

(* 0ary operations *)
Inductive z_op: Type :=
| zconst: int -> z_op.

Inductive expr: Type :=
| BIN: bin_op -> reg -> reg -> expr
| UNA: un_op -> reg -> expr
| ZAR: z_op -> expr.

(* Where to go to when deoptimizing *)
Definition deopt_target: Type := fun_id * label.

(* Binding registers to an expression, for deoptimizations *)
Definition varmap: Type := list (reg * expr).

Definition empty_varmap: varmap := nil.

(* Instruction set *)
Inductive instruction: Type :=
| Nop: label -> instruction
| IPrint: expr -> label -> instruction
| Call: fun_id -> list reg -> reg -> label -> instruction (* list reg, not expr *)
| Cond: reg -> label -> label -> instruction             (* branching *)
| Return: expr -> instruction
| Op: reg -> expr -> label -> instruction
(* Memory Manipulaiton *)
| MemSet: reg -> reg -> label -> instruction (* 1st reg: address, 2nd reg: value *)
| MemGet: reg -> reg -> label -> instruction (* 1st reg: dst, 2nd reg: address *)
(* Speculation *)
| Assume: expr -> deopt_target -> varmap -> label -> instruction
(* no synthesizing of extra frames for now *)
| Anchor: deopt_target -> varmap -> label -> instruction. 


Definition code: Type := PTree.t instruction.

Record version: Type := mk_version {
  ver_code: code;
  ver_entry: label;
}.

(* Defining base versions: no speculative (Anchor & Assume) instructions *)
Inductive is_spec: instruction -> Prop :=
| spec_assume: forall g tgt vm next,
    is_spec (Assume g tgt vm next)
| spec_framestate: forall tgt vm next,
    is_spec (Anchor tgt vm next).           

Definition base_code (c:code): Prop :=
  forall (pc:label) (i:instruction), c!pc = Some i -> ~ (is_spec i).

(* Code without anchors, used after lowering *)
Definition no_anchor_code (c:code) : Prop :=
  forall pc tgt vm next, c!pc = Some (Anchor tgt vm next) -> False.

Definition base_version (v:version): Prop :=
  base_code (ver_code v).


Record function': Type := mk_function {
  fn_params : list reg;
  fn_base : version;
  fn_opt : option version;
  base_no_spec: base_version fn_base
                            }.
(* The native code is stored in another data-structure *)

Definition function: Type := function'.

(* A program can hold a single RTL function during compilation *)
Definition RTLfun: Type := fun_id * RTL.code * label * cont_idx.

(* Indexing such a data-structure *)
Inductive cont_id: Type :=
| Main: cont_id
| Cont : positive -> cont_id.

Definition rtl_get_entry (rtl:RTLfun) (id:cont_id): option label :=
  match rtl with
  | (fid, graph, main, contidx) =>
    match id with
    | Main => Some main
    | Cont p => PTree.get p contidx
    end
  end.

Definition rtlblock_get_entry (rtl:RTLblockfun) (id:cont_id): option label :=
  match rtl with
  | (fid, graph, main, contidx) =>
    match id with
    | Main => Some main
    | Cont p => PTree.get p contidx
    end
  end.


Record program: Type := mk_program {
  prog_main : fun_id;
  prog_funlist : PTree.t function;
}.

(* A CoreIR program that does not contain Anchors *)
(* We only need to define it on opt versions, since base versions use base_no_spec *)
Definition no_anchor (p:program) : Prop :=
  forall fid f vopt,
    (prog_funlist p) ! fid = Some f ->
    fn_opt f = Some vopt ->
    no_anchor_code (ver_code vopt).

(** * Program manipulation  *)
Definition successors (instr:instruction) : list label :=
  match instr with
  | Nop next => next::nil
  | IPrint _ next => next::nil
  | Call _ _ _ next => next::nil
  | Cond _ tr fl => tr::fl::nil
  | Op _ _ next => next::nil
  | Return _ => nil
  | MemSet _ _ next => next::nil
  | MemGet _ _ next => next::nil
  | Assume _ _ _ next => next::nil
  | Anchor _ _ next => next::nil
  end.

Definition current_version (f:function): version :=
  match (fn_opt f) with
  | None => fn_base f
  | Some o => o
  end.


Definition find_function_ir (fid:fun_id) (p:program): option function :=
  (prog_funlist p) ! fid.

(* Find a base version given a function id and a program *)
Definition find_base_version (fid:fun_id) (p:program): option version :=
  match (find_function_ir fid p) with
  | None => None
  | Some f => Some (fn_base f)
  end.

(* Replacing the optimized version of a function *)
Program Definition set_version_function (v:version) (f:function): function :=
  mk_function (fn_params f) (fn_base f) (Some v) _.
Next Obligation.
  apply (base_no_spec f).
Qed.

(* Update a fun_list with the new function containing the new version *)
Definition set_version_funlist (fid:fun_id) (v:version) (fl:PTree.t function): PTree.t function :=
  match (fl ! fid) with
  | None => fl
  | Some f => fl # fid <- (set_version_function v f)
  end.

(* Updates versions in a program. *)
Definition set_version (p:program) (fid:fun_id) (v:version): program :=
  mk_program (prog_main p) (set_version_funlist fid v (prog_funlist p)).


Definition rtl_id (r:option RTLfun) : option fun_id :=
  match (r) with
  | None => None
  | Some (fid, _, _, _) => Some fid
  end.

Definition prtl_id (r:option (RTLfun + RTLblockfun)) : option fun_id :=
  match (r) with
  | None => None
  | Some (inl (fid, _, _, _)) => Some fid
  | Some (inr (fid, _, _, _)) => Some fid
  end.

(* Max positive used in a PTree *)
Fixpoint max_pos' {A:Type} (vl:list (positive * A)): positive :=
  match vl with
  | nil => xH
  | (vid,v)::vl' => Pos.max vid (max_pos' vl')
  end.

Definition max_pos {A:Type} (tree:PTree.t A): positive :=
  max_pos' (PTree.elements tree).

Definition max_label {A:Type} (c:PTree.t A): label :=
  max_pos c.

Definition fresh_label {A:Type} (c:PTree.t A) :=
  Pos.succ (max_label c).

(* Another version that takes a fresh label suggestion *)
(* This helps inserts Assumes and Anchors provided that there is space between the labels *)
Definition fresh_sug (sug:label) (c:code) : label :=
  match (c!sug) with
  | Some _ => fresh_label c
  | None => sug
  end.

Lemma max_pos'_correct:
    forall A vid v, forall vl:list (positive * A),
      In (vid,v) vl ->
      Pos.le vid (max_pos' vl).
Proof.
  intros.
  induction vl. inversion H.
  destruct a. simpl. inv H.
  - inversion H0. subst. apply Pos.le_max_l.
  - apply IHvl in H0. eapply Pos.le_trans. eauto. apply Pos.le_max_r.
Qed.

Lemma max_pos_correct:
  forall A vid v, forall tree:PTree.t A,
    tree ! vid = Some v ->
    Pos.le vid (max_pos tree).
Proof.
  intros. unfold max_pos.
  apply PTree.elements_correct in H.
  eapply max_pos'_correct. eauto.
Qed.

(* fresh_label returns an identifier associated with no instruction *)
Theorem fresh_label_correct:
  forall A (c:PTree.t A) fl,
    fresh_label c = fl ->
    c ! fl = None.
Proof.
  intros. destruct (c # fl) eqn:HH; auto.
  apply max_pos_correct in HH.
  unfold fresh_label in H. subst. unfold max_label in HH. exfalso.
  apply Pos2Nat.inj_le in HH. simpl in HH. rewrite Pos2Nat.inj_succ in HH.
  lia. 
Qed.


Theorem fresh_sug_correct:
  forall c sug l,
    fresh_sug sug c = l ->
    c ! l = None.
Proof.
  intros c sug l H. unfold fresh_sug in H. destruct (c # sug) eqn:CODE; subst; auto.
  apply fresh_label_correct. auto.
Qed.
  


Definition reg_map: Type := PTree.t int. (* values are int *)
Definition empty_regmap: reg_map := PTree.empty int.

(** * The environment we save *)
Definition env : Type := list int.

(** * Argument Buffer  *)
Definition buf : Type := list int.
(* substituted with an actual buffer *)

(** * Stackframes and Stack  *)
Definition IR_stackframe : Type := reg * version * label * reg_map.
(* Definition RTL_stackframe : Type := Registers.reg * RTL.function * val * node * regset. *)
(* maybe we'll use env in that RTL stackframe *)
(* it should be a continuation and an env I guess *)
Definition ASM_stackframe : Type := int * int * int * list int.

(* What we put in the stack model *)
Inductive stackframe : Type :=
| IR_SF : IR_stackframe -> stackframe
| ASM_SF : ASM_stackframe -> stackframe.

(* Stack model *)
Definition stack : Type := list stackframe.


(** * Semantic States *)
Definition ir_state : Type := (version * label * reg_map).

(** * Synchronisation States  *)
(* Such states are reached at each Call and Return *)
(* These are States where we expect the JIT to take control, possibly optimize, and *)
(* possibly switch between languages. *)

Inductive call_loc: Type :=
| nat_call: call_loc            (* the callee_id and the args have been pushed to the arg buffer *)
| ir_call: fun_id -> list int -> call_loc.

Inductive ret_loc: Type :=
| nat_ret: ret_loc              (* the return value has been pushed to the arg buffer *)
| ir_ret: int -> ret_loc.

Inductive deopt_loc: Type :=
| nat_deopt: deopt_loc          (* the target is on the arge buffer, the metadata is on the stack *)
| ir_deopt: fun_id -> label -> reg_map -> deopt_loc.

Inductive synchro_state:=
| S_Call: call_loc -> synchro_state
| S_Return: ret_loc -> synchro_state
| S_Deopt: deopt_loc -> synchro_state
| Halt_IR: ir_state -> synchro_state (* halt because of fuel *)
| Halt_ASM: Asm.genv -> Asm.state -> synchro_state (* halt because of fuel *)
| Halt_RTL: RTL.genv -> RTL.state -> synchro_state (* for the semantics, although not used by the JIT *)
| Halt_Block: block_state -> synchro_state        (* same for RTLblock *)
| EOE: int -> synchro_state.                 (* end of execution *)


(** * Checkpoints  *)
(* like synchro_states, but restricted to Call and Return *)
Inductive checkpoint: Type :=   (* the states at which we return to the hypervisor *)
| C_Call: call_loc -> checkpoint
| C_Return: ret_loc -> checkpoint
| C_Deopt: deopt_loc -> checkpoint.


Definition synchro_of (cp:checkpoint) : synchro_state :=
  match cp with
  | C_Call loc => S_Call loc
  | C_Return loc => S_Return loc
  | C_Deopt loc => S_Deopt loc
  end.

(** * No Anchors in our Stacks *)
(* This is used as an invariant of the JIT execution *)
Inductive sf_no_anchor: stackframe -> Prop :=
| ASM_NO: forall asmf, sf_no_anchor (ASM_SF asmf)
| IR_NO: forall retreg v pc rm
           (NO_ANC_CODE: no_anchor_code (ver_code v)),
    sf_no_anchor (IR_SF (retreg, v, pc, rm)).

Inductive stk_no_anchor: stack -> Prop :=
| NIL_NO: stk_no_anchor nil
| CONS_NO: forall stk sf
             (STK_NO: stk_no_anchor stk)
             (SF_NO: sf_no_anchor sf),
    stk_no_anchor (sf::stk).
