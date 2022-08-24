(* Generating RTLblock *)

Require Import RTLblock.
Require Import IR.
Require Import monad.
Require Import common.
Require Import Coqlib.
Require Import Op.
Require Import Integers.
Require Import primitives.
Require Import AST.
Require Import intpos.
Require Import Errors.
Require Import liveness.
Require Import def_regs.
Require Import Coq.MSets.MSetPositive.

(* Lists Notations *)
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


(** * Generating Fresh Labels  *)
(* As we generate new instructions for each call, we want labels that are: *)
(* - fresh for the code we've generated so far *)
(* - also not used in the base code, as we reuse the same labels  *)

(* Call fresh_label_min with [min] being a fresh label for the original code *)
Definition fresh_label_min {A:Type} (min:positive) (c: PTree.t A) :=
  Pos.max (min) (fresh_label c).


(** * Liveness and Defined analysis *)
(* To capture the env to save before a call *)
Definition defined_rs (abs:def_abs_state) (l:label) : option regset :=
  match (def_absstate_get l abs) with
  | DefFlatRegset.Top => None       (* The analysis wasn't precise enough *)
  | DefFlatRegset.Inj rs => Some rs
  | DefFlatRegset.Bot => None       (* Did not converge *)
  end.

Definition live_def_regs (call_lbl:label) (live:live_abs_state) (def:def_abs_state) (retreg:reg): res (list reg) :=
  do rs_def <- try_op (defined_rs def call_lbl) "Defined regs analysis failed";
    do rs_live <- OK (live_absstate_get call_lbl live);
    OK (PositiveSet.elements (PositiveSet.inter rs_def (reg_dead retreg rs_live))).
(* we take the registers that are both
- defined before the call
- live after the call *)
(* we also remove the return register (which will be set anyway) *)


(** * Compiling Expressions  *)
(* All registers are shifted, because the first few RTL registers are reserved *)
Definition shift : positive := xI (xI (xH)).
(* from IR reg to RTL reg *)
Definition shift_reg (r:reg) : reg :=
  Pos.add r shift.

Definition shift_list_reg : list reg -> list reg :=
  List.map shift_reg.

(* This does the job of SelectOp *)
Definition transf_expr (e:IR.expr) : operation * list reg :=
  match e with
  | ZAR z =>
    match z with
    | zconst i => (Ointconst i, [])
    end
  | UNA u r =>
    match u with
    | uneg => (Oneg, [shift_reg r])
    | ueqzero => (Ocmp (Ccompimm Ceq Int.zero), [shift_reg r])
    | uplus i => (Olea (Aindexed (Int.signed i)), [shift_reg r])
    | umul i => (Omulimm i, [shift_reg r])
    end
  | BIN b r1 r2 =>
    match b with
    | bplus => (Olea (Aindexed2 0), [shift_reg r1; shift_reg r2])
    | bneg => (Osub, [shift_reg r1; shift_reg r2])
    | bmul => (Omul, [shift_reg r1; shift_reg r2])
    | beq => (Ocmp (Ccomp Ceq), [shift_reg r1; shift_reg r2])
    | blt => (Ocmp (Ccomp Clt), [shift_reg r1; shift_reg r2])
    | bmod => (Omod, [shift_reg r1; shift_reg r2]) 
    end
  end.

(** * Reserved Registers *)
(* Reserved for the return of void functions, or to store the arguments to a retcall *)
Definition void_reg : reg := xH.
Definition callee_reg : reg := xO (xH).
Definition caller_reg : reg := xI (xH).
Definition cont_reg : reg := xO (xO (xH)).
Definition ret_reg : reg := xI (xO (xH)).
Definition guard_reg : reg := ret_reg. (* we also use this register to evaluate guards of speculations *)
Definition ret_id_reg : reg := xI (xI (xH)). (* where we store the return ID, RETRET, RETCALL or RETDEOPT *)



(** * Generating Blocks  *)
(* Inserts [void_reg = _SAVE(shift r)] primitives for each register r in l *)
Fixpoint generate_saves (l:list reg): list block_instr :=
  match l with
  | nil => nil
  | r::l' =>
    (Bcall EF_save [shift_reg r] void_reg)::generate_saves l'
  end.

(* Inserts [void_reg = _PUSHARG(shift r)] primitives for each register r in l *)
Fixpoint generate_pushargs (l:list reg): list block_instr :=
  match l with
  | nil => nil
  | r::l' =>
    (Bcall EF_save [shift_reg r] void_reg)::generate_pushargs l'
  end.

Fixpoint generate_pushvm (vm:varmap): res (list block_instr) :=
  match vm with
  | nil => OK nil
  | (r,e)::vm' =>
    do r_int <- int_of_pos r;    (* we save the identifier of the register *)
      do (op, lst) <- OK (transf_expr e); (* we evaluate the expression *)
      do instr <-
         OK [Bop op lst guard_reg; (* evaluating the expression *)
               Bcall EF_save [guard_reg] void_reg; (* pushing the value *)
               Bop (Ointconst r_int) [] guard_reg; (* evaluating r_int *)
               Bcall EF_save [guard_reg] void_reg]; (* pushing the reg identifier *)
      do next <- generate_pushvm vm';
      OK (instr ++ next)
  end.

Definition generate_varmap (vm:varmap): res (list block_instr) :=
  do nb <- int_of_nat (length vm);
    do lst <- generate_pushvm vm;
    OK (lst ++ [Bop (Ointconst nb) [] guard_reg;
                  Bcall EF_save [guard_reg] void_reg]). (* pushing the size of the varmap *)

(* generating the pushargs, and also pushing the number of arguments *)
Definition generate_args (l:list reg): res (list block_instr) :=
  do nb <- int_of_nat (length l);
    OK ((generate_pushargs l) ++
                              [Bop (Ointconst nb) [] callee_reg; 
                               Bcall EF_save [callee_reg] void_reg]).

(* Generate [r = _LOAD()] for each register r, in reverse order *)
Fixpoint generate_loads (l:list reg): list block_instr :=
  match l with
  | nil => nil
  | r::l' =>
    generate_loads l' ++ [Bcall EF_load [] (shift_reg r)]
  end.

(* Generate [r = _POPARG()] for each register r, in reverse order *)
Fixpoint generate_popargs (l:list reg): list block_instr :=
  match l with
  | nil => nil
  | r::l' =>
    generate_popargs l' ++ [Bcall EF_load [] (shift_reg r)]
  end.


(* Generates the call to close the current stackframe *)
Definition generate_close (caller_id:positive) (cont_id:positive) (retreg:positive) : res (list block_instr) :=
  do cer <- int_of_pos caller_id; (* this fails if the identifiers are out of int range *)
    do con <- int_of_pos cont_id;
    do rr <- int_of_pos (shift_reg retreg);
    OK
      [Bop (Ointconst cer) [] caller_reg;
       Bop (Ointconst con) [] cont_reg;
       Bop (Ointconst rr) [] ret_reg;
       Bcall EF_close [caller_reg; cont_reg; ret_reg] void_reg]. 

(* Pushes the callee_id to the stack *)
Definition generate_push_callee (callee_id:positive) : res (list block_instr) :=
  do cee <- int_of_pos callee_id;
    OK [Bop (Ointconst cee) [] callee_reg;
        Bcall EF_save [callee_reg] void_reg].

(* Generates the operation that stores the RETCALL value in the return register *)
Definition generate_retcall : list block_instr :=
  [Bop (Ointconst primitives.RETCALL) [] ret_id_reg].


(* The block that loads the arguments at the very beginning of the function, then points to entry e *)
Definition entry_block (l:list reg) (e:positive) : basic_block :=
  (generate_popargs l, Bnop e).

(* The block that loads the live registers after a call, then points to the re-entry *)
(* also pops the return value *)
Definition preamble_block (l:list reg) (retreg:positive) (re:positive) : basic_block :=
  ((Bcall EF_load [] (shift_reg retreg))::generate_loads l, Bnop re).

(* The Deoptimization basic block if the guard fails *)
Definition deopt_block (tgt:deopt_target) (vm:varmap) : res basic_block :=
  match tgt with
  | (ftgt, ltgt) =>
    do gen_vm <- generate_varmap vm;
      do fint <- int_of_pos ftgt;
      do lint <- int_of_pos ltgt;
      OK (gen_vm ++
                 [Bop (Ointconst lint) [] guard_reg;
                    Bcall EF_save [guard_reg] void_reg; (* pushing ltgt *)
                    Bop (Ointconst fint) [] guard_reg;
                    Bcall EF_save [guard_reg] void_reg; (* pushing ftgt *)
                    Bop (Ointconst primitives.RETDEOPT) [] ret_id_reg], (* indicating deopt *)
          Breturn ret_id_reg)
  end.

(* A one-to-one correspondance between IR.instr and blocks *)
(* We also need to insert preamble_blocks for each continuation *)
Definition instr_to_block (i:IR.instruction) (live:live_abs_state) (def:def_abs_state) (currentfun currentlbl: positive): res block :=
  match i with
  | Nop next => OK (Bblock ([], Bnop next))
                  
  | IPrint r next =>
    OK (Bblock ([Bcall EF_print [shift_reg r] void_reg], Bnop next))
       
  | Cond r tr fl =>
    OK (Bblock ([], Bcond (Ccompimm Ceq Int.zero) [shift_reg r] fl tr))
       
  | Op r ex next =>
    let (op, lst) := transf_expr ex in
    OK (Bblock ([Bop op lst (shift_reg r)], Bnop next))
       
  | Call callee_fid args retreg next =>
    do live_regs <- live_def_regs currentlbl live def retreg; (* the list of regs to save and restore *)
    do push_live <- OK (generate_saves live_regs);   (* saving lives *)
    do close <- generate_close currentfun currentlbl retreg; (* closing stackframe *)
    do push_args <- generate_args args;             (* pushing args *)
    do push_callee <- generate_push_callee callee_fid;       (* pushing callee *)
    do retcall <- OK (generate_retcall);                     (* setting up return reg *)
    OK (Bblock (push_live ++ close ++ push_args ++ push_callee ++ retcall,
                Breturn ret_id_reg))
    
  | Return retreg =>
    OK (Bblock
          ([Bcall EF_save [shift_reg retreg] void_reg;
            Bop (Ointconst primitives.RETRET) [] ret_id_reg],
           Breturn ret_id_reg))

  | MemSet adreg valreg next =>
    OK (Bblock ([Bcall EF_memset [shift_reg adreg; shift_reg valreg] void_reg], Bnop next))

  | MemGet dstreg adreg next =>
    OK (Bblock ([Bcall EF_memget [shift_reg adreg] (shift_reg dstreg)], Bnop next))
          
  | Assume guard tgt vm next =>
    do deopt_blk <- deopt_block tgt vm;
      OK (Cblock (Ccompimm Ceq Int.zero) [shift_reg guard] next deopt_blk)
  end.


Definition handle_instr (live:live_abs_state) (def:def_abs_state) (currentfun: positive) (min:positive) (c: res (block_code * cont_idx)) (currentlbl:positive) (i:IR.instruction): res (block_code * cont_idx) :=
  do (code, ci) <- c;
  do block <- instr_to_block i live def currentfun currentlbl;
  do newcode <- OK (code # currentlbl <- block); (* adding the one transformation *)
  match i with
  | Call callee_fid args retreg next =>
    do live_regs <- live_def_regs currentlbl live def retreg;
    do fresh <- OK (fresh_label_min min newcode);
    do newcode' <- OK ((newcode # fresh <- (Bblock (preamble_block live_regs retreg next)))); (* adding the preamble *)
    OK (newcode', ci # currentlbl <- fresh)
  | _ => OK (newcode, ci)
  end.
  


(** * Creating the RTLblock code of a function  *)
Definition transf_code (currentfun:positive) (v:IR.version) (params:list reg) : res (block_code * cont_idx) :=
  do live <- try_op (liveness_analyze v) "Liveness analysis failed";
  do def <- try_op (defined_regs_analysis (ver_code v) params (ver_entry v)) "Def_regs analysis failed";
  do fresh <- OK (fresh_label (ver_code v)); (* upper-bound for the new label *)
  PTree.fold (handle_instr live def currentfun fresh) (ver_code v) (OK (PTree.empty RTLblock.block, PTree.empty label)).


(** * RTL generation  *)
(* We return the RTL graph, the new entry label, and the continuation index *)
Definition rtlgen (currentfun:positive) (v:IR.version) (params:list reg): res (block_code * label * cont_idx) :=
  do (rtlc, ci) <- transf_code currentfun v params;
    do fresh_entry <- OK (fresh_label rtlc);
    do final_code <- OK (rtlc # fresh_entry <- (Bblock (entry_block params (ver_entry v))));
    OK (final_code, fresh_entry, ci).
