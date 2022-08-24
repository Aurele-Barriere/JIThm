(* Mixed Semantics *)

Require Import RTL.
Require Import RTLblock.
Require Import Globalenvs.
Require Import AST.
Require Import Asm.
Require Import IR.
Require Import monad.
Require Import monad_impl.
Require Import Integers.
Require Import common.
Require Import Events.
Require Import Errors.
Require Import IRinterpreter.
Require Import primitives.
Require Import ASMinterpreter.
Require Import intpos.
Require Import customSmallstep.
Require Import optimizer.
Require Import jit.
Require Import Values.

Definition pc_cond (b:bool) (tr fl:label) : label :=
  if b then tr else fl.



(** * RTLblock Semantics  *)
Notation "a ## b" := (List.map (fun r => Registers.Regmap.get r a) b) (at level 1).


Definition exec_block_instr (bi:block_instr) (rs:RTL.regset) : free (trace * RTL.regset) :=
  match bi with
  | Bop op args r =>
    do v <<- try_option (block_eval_operation op (rs ## args)) "Wrong Op";
      fret (E0, Registers.Regmap.set r v rs)
  | Bcall ef args r =>
    do (t, i) <<- prim_sem_dec (EF_name ef) (EF_sig ef) (rs ## args);
      fret (t, Registers.Regmap.set r (Vint i) rs)
  end.


Definition get_int_reg (rs:RTL.regset) (r:reg) : res int :=
  match (Registers.Regmap.get r rs) with
  | Vint i => OK i
  | _ => Error (MSG "No int value to return"::nil)
  end.


Definition block_step (rtlblock:RTLblockfun) (bs:block_state) : free (trace * block_state) :=
  match bs with
  | BPF pc rs =>
    do block <<- try_option (get_block rtlblock pc) "Missing block";
      fret (E0, BState block rs)
  | RTLblock.BState blk rs =>
    match blk with
    | Bblock (blkis, exiti) =>
      match blkis with
      | nil =>
        match exiti with        (* executing the exit instruction *)
        | Bnop next =>
          fret (E0, BPF next rs)
        | Bcond op lst tr fl =>
          do b <<- try_option (block_eval_condition op (rs ## lst)) "Wrong Cond";
            fret (E0, BPF (pc_cond b tr fl) rs)
        | Breturn reg =>
          do retval <<- fret' (get_int_reg rs reg);
          fret (E0, BFinal retval)
        end
      | bi::blkis' =>
        do (t, rs') <<- exec_block_instr bi rs;
        fret (t, BState (Bblock (blkis',exiti)) rs') (* peeling off 1 block instruction *)
      end
    | Cblock guard lst next bb =>
      do b <<- try_option (block_eval_condition guard (rs ## lst)) "Wrong Cond";
        match b with
        | false => fret (E0, BPF next rs)
        | true => fret (E0, BState (Bblock bb) rs) (* heading into the deopt branch *)
        end   
    end
  | BFinal i => ferror (MSG "Final RTLblock state"::nil)
  end.

(** * Mixed Semantics  *)
                     
(* Where we don't want RTL step, but instead use the primitive monads *)
Inductive interrupt_rtl: RTL.state -> Prop :=
| interrupt_extcall:
    forall s ef args m,
      interrupt_rtl (RTL.Callstate s (AST.External ef) args m)
| interrupt_builtin:
    forall s f sp pc rs m ef args res pc'
      (BUILTIN: (RTL.fn_code f) # pc = Some (Ibuiltin ef args res pc')),
      interrupt_rtl (RTL.State s f sp pc rs m).
(* We interrupt builtins because we don't generate any and they aren't determinate *)

Definition mixed_state : Type := (synchro_state * mutables).

(* A static mixed semantic (no optimization possible) *)
(* Using atomic steps instead of loops *)
Inductive mixed_step : program -> option (RTLfun + RTLblockfun) -> asm_codes -> mixed_state -> Events.trace -> mixed_state -> Prop :=
| IR_step:
    forall p rtl nc irs ms t synchro ms1
      (STEP: exec (IRinterpreter.ir_step irs) naive_impl (ms,nc) = SOK (t, synchro) (ms1,nc)),
      mixed_step p rtl nc (Halt_IR irs, ms) t (synchro, ms1)
| x86_step:                     (* all x86 steps, including returning to the hypervisor *)
    forall p rtl nc xs ge t ms ms1 synchro
      (STEP: exec (ASMinterpreter.asm_int_step ge xs) naive_impl (ms,nc) = SOK (t, synchro) (ms1,nc)),
      mixed_step p rtl nc (Halt_ASM ge xs, ms) t (synchro, ms1)
| rtl_step:                     (* all steps except external functions. no change to the monad *)
    forall p rtl nc ge rtls1 t rtls2 ms
      (NO_INTERRUPT: ~ interrupt_rtl rtls1)
      (RTL: RTL.step ge rtls1 t rtls2),
      mixed_step p rtl nc (Halt_RTL ge rtls1, ms) t (Halt_RTL ge rtls2, ms)
| rtl_block_step:
    forall p rtlb nc bs1 t bs2 ms ms'
      (BLOCK: exec (block_step rtlb bs1) naive_impl (ms, nc) = SOK (t, bs2) (ms', nc)),
      mixed_step p (Some (inr rtlb)) nc (Halt_Block bs1, ms) t (Halt_Block bs2, ms')
| Call_IR:
    forall p rtl nc fid args ms ms2 ms3 func ver newrm loc
      (CALLEE: exec (get_callee loc) naive_impl (ms, nc) = SOK fid (ms2, nc))
      (NOT_COMPILED: exec_prim (Prim_Check_Compiled fid) naive_impl (ms2,nc) = SOK Not_compiled (ms2,nc))
      (ARGS: exec (get_args loc) naive_impl (ms2,nc) = SOK args (ms3,nc))
      (NOT_RTL: ~ (prtl_id rtl = Some fid))
      (GETF: (prog_funlist p) # fid = Some func)
      (CURVER: current_version func = ver)
      (INIT: init_regs args (fn_params func) = OK newrm),
      mixed_step p rtl nc (S_Call loc, ms) E0 (Halt_IR (ver, ver_entry ver, newrm), ms3)
| Call_x86:
    forall p rtl nc fid ms ms2 ms3 ms4 af asm_prog xs loc
      (CALLEE: exec (get_callee loc) naive_impl (ms, nc) = SOK fid (ms2, nc))
      (COMPILED: exec_prim (Prim_Check_Compiled fid) naive_impl (ms2,nc) = SOK (Installed af) (ms2,nc))
      (ARGS: exec (set_up_args loc) naive_impl (ms2,nc) = SOK tt (ms3, nc))
      (NOT_RTL: ~ (prtl_id rtl = Some fid))
      (LOAD: exec_prim (Prim_Load_Code (Call_id fid)) naive_impl (ms3,nc) = SOK asm_prog (ms4,nc))
      (INIT: init_nat_state asm_prog = OK xs),
      mixed_step p rtl nc (S_Call loc, ms) E0 (Halt_ASM (build_genv asm_prog) xs, ms4)
| Call_RTL:
    forall p rtl nc fid rtlcode entry contidx rtlprog rtls ms ms2 ms3 loc
      (CALLEE: exec (get_callee loc) naive_impl (ms, nc) = SOK fid (ms2, nc))
      (COMPILED: exec_prim (Prim_Check_Compiled fid) naive_impl (ms2,nc) = SOK Not_compiled (ms2,nc))
      (ARGS: exec (set_up_args loc) naive_impl (ms2,nc) = SOK tt (ms3, nc))
      (RTL: rtl = Some (inl (fid, rtlcode, entry, contidx)))
      (MAKE_PROG: backend.make_prog rtlcode entry = rtlprog)
      (INIT: RTL.initial_state rtlprog rtls),
      mixed_step p rtl nc (S_Call loc, ms) E0 (Halt_RTL (Genv.globalenv rtlprog) rtls, ms3)
| Call_RTL_Block:
    forall p rtl nc fid blkcode entry contidx ms ms1 ms2 loc
      (CALLEE: exec (get_callee loc) naive_impl (ms, nc) = SOK fid (ms1, nc))
      (COMPILED: exec_prim (Prim_Check_Compiled fid) naive_impl (ms1,nc) = SOK Not_compiled (ms1,nc))
      (ARGS: exec (set_up_args loc) naive_impl (ms1,nc) = SOK tt (ms2, nc))
      (RTL_BLOCK: rtl = Some (inr (fid, blkcode, entry, contidx))),
      mixed_step p rtl nc (S_Call loc, ms) E0 (Halt_Block (BPF entry init_regset), ms2)
| Return_IR:
    forall p rtl nc retval ms ms1 ms2 retreg v pc rm newrm loc
      (RETVAL: exec (get_retval loc) naive_impl (ms,nc) = SOK retval (ms1,nc))
      (OPEN_SF: exec_prim (Prim_OpenSF) naive_impl (ms1,nc) = SOK (ir_sf (retreg, v, pc, rm)) (ms2,nc))
      (UPDATE: newrm = rm # retreg <- retval),
      mixed_step p rtl nc (S_Return loc, ms) E0 (Halt_IR (v, pc, newrm), ms2)
| Return_x86:
    forall p rtl nc ms ms1 ms2 ms3 ms4 caller_fid cont_lbl retreg asm_prog xs loc retval
      (RETVAL: exec (get_retval loc) naive_impl (ms,nc) = SOK retval (ms1,nc))
      (OPEN_SF: exec_prim (Prim_OpenSF) naive_impl (ms1,nc) = SOK (nat_sf caller_fid cont_lbl retreg) (ms2,nc))
      (SET_RETVAL: exec_prim (Prim_Save retval) naive_impl (ms2,nc) = SOK tt (ms3,nc))
      (LOAD_CONT: exec_prim (Prim_Load_Code (Cont_id (pos_of_int caller_fid) (pos_of_int cont_lbl))) naive_impl (ms3,nc) = SOK asm_prog (ms4,nc))
      (INIT: init_nat_state asm_prog = OK xs),
      mixed_step p rtl nc (S_Return loc, ms) E0 (Halt_ASM (build_genv asm_prog) xs, ms4)
| Return_RTL:
    forall p rtl nc fid fidint rtlcode entry contidx cont_lbl retreg cont_entry rtlprog rtls ms ms1 ms2 ms3 loc retval
      (INTPOS_FID: int_of_pos fid = OK fidint)
      (RETVAL: exec (get_retval loc) naive_impl (ms,nc) = SOK retval (ms1,nc))
      (OPEN_SF: exec_prim (Prim_OpenSF) naive_impl (ms1,nc) = SOK (nat_sf fidint cont_lbl retreg) (ms2,nc))
      (SETRETVAL: exec_prim (Prim_Save retval) naive_impl (ms2,nc) = SOK tt (ms3,nc))
      (NOT_COMPILED: exec_prim (Prim_Check_Compiled fid) naive_impl (ms3,nc) = SOK Not_compiled (ms3,nc))
      (RTL: rtl = Some (inl (fid, rtlcode, entry, contidx)))
      (LOAD_CONT: PTree.get (pos_of_int cont_lbl) contidx = Some cont_entry)
      (MAKE_PROG: backend.make_prog rtlcode cont_entry = rtlprog)
      (INIT: RTL.initial_state rtlprog rtls),
      mixed_step p rtl nc (S_Return loc, ms) E0 (Halt_RTL (Genv.globalenv rtlprog) rtls, ms3)
| Return_RTL_Block:
    forall p rtl nc fid fidint blockcode entry contidx cont_lbl retreg cont_entry ms ms1 ms2 ms3 loc retval
      (INTPOS_FID: int_of_pos fid = OK fidint)
      (RETVAL: exec (get_retval loc) naive_impl (ms, nc) = SOK retval (ms1, nc))
      (OPEN_SF: exec_prim (Prim_OpenSF) naive_impl (ms1,nc) = SOK (nat_sf fidint cont_lbl retreg) (ms2,nc))
      (SETRETVAL: exec_prim (Prim_Save retval) naive_impl (ms2,nc) = SOK tt (ms3,nc))
      (NOT_COMPILED: exec_prim (Prim_Check_Compiled fid) naive_impl (ms3,nc) = SOK Not_compiled (ms3,nc))
      (RTL_BLOCK: rtl = Some (inr (fid, blockcode, entry, contidx)))
      (LOAD_CONT: PTree.get (pos_of_int cont_lbl) contidx = Some cont_entry),
    mixed_step p rtl nc (S_Return loc, ms) E0 (Halt_Block (BPF cont_entry init_regset), ms3)
| Return_EOE:
    forall p rtl nc retval ms ms1 ms2 loc
      (RETVAL: exec (get_retval loc) naive_impl (ms,nc) = SOK retval (ms1,nc))
      (OPEN_SF: exec_prim (Prim_OpenSF) naive_impl (ms1,nc) = SOK empty_stack (ms2,nc)),
      mixed_step p rtl nc (S_Return loc, ms) E0 (EOE retval, ms2)
| Deopt:
    forall p rtl nc ftgt ltgt rm ms ms1 ms2 func newver loc
      (TARGET: exec (get_target loc) naive_impl (ms,nc) = SOK (ftgt, ltgt) (ms1,nc))
      (BUILD_RM: exec (build_rm loc) naive_impl (ms1,nc) = SOK rm (ms2,nc))
      (FINDF: (prog_funlist p)#ftgt = Some func)
      (TGTVER: base_version func = newver),
      mixed_step p rtl nc (S_Deopt loc, ms) E0 (Halt_IR (newver, ltgt, rm), ms2)
(* Giving semantics to the primitives in RTL *)
| RTL_prim:
    forall p rtl nc ge stk name sg args mem ms ms1 retval t
      (PRIM_CALL: exec (prim_sem_dec name sg args) naive_impl (ms,nc) = SOK (t, retval) (ms1,nc)),
      mixed_step p rtl nc
                 (Halt_RTL ge (RTL.Callstate stk (AST.External (EF_runtime name sg)) args mem), ms) t
                 (Halt_RTL ge (RTL.Returnstate stk (Vint retval) mem), ms1)
| RTL_end:                      (* Returning from the RTL program *)
    forall p rtl nc ge rtls r cp ms
      (FINAL: RTL.final_state rtls r)
      (CHK: get_checkpoint r = OK cp),
      mixed_step p rtl nc
                 (Halt_RTL ge rtls, ms) E0 (synchro_of cp, ms)
| RTL_block_end:
    forall p rtl nc r cp ms s
      (CHK: get_checkpoint r = OK cp)
      (SYNC: synchro_of cp = s),
      mixed_step p rtl nc (Halt_Block (BFinal r), ms) E0 (s, ms).

Inductive init_mixed_state (p:program) (nc:asm_codes): mixed_state -> Prop :=
| init_mixed:
    init_mixed_state p nc (S_Call (ir_call (prog_main p) nil), init_mutables).

Inductive final_mixed_state (p:program) : mixed_state -> int -> Prop :=
| final_mixed': forall retval ms,
    final_mixed_state p (EOE retval, ms) retval.

Definition mixed_sem (p:program) (rtl:option (RTLfun + RTLblockfun)) (nc:asm_codes): semantics :=
  Semantics_gen (mixed_step p rtl) (init_mixed_state p nc) (final_mixed_state p) nc.

(** * Input Semantics *)
(* the semantics for the input program. Only IR, no native code, no monad state *)

Definition ir_stack : Type := list IR_stackframe.

Inductive input_state: Type :=
| State: ir_state -> ir_stack -> memory -> input_state
| Callstate : fun_id -> list int -> ir_stack -> memory -> input_state
| Returnstate : int -> ir_stack -> memory -> input_state
| Deoptstate: fun_id -> label -> reg_map -> ir_stack -> memory -> input_state
| Final : int -> input_state.

Inductive input_step : program -> input_state -> Events.trace -> input_state -> Prop :=
| input_Nop:
    forall p v pc rm stk next mem
      (CODE: (ver_code v) # pc = Some (Nop next)),
      input_step p (State (v, pc, rm) stk mem) E0 (State (v, next, rm) stk mem)
| input_Print:
    forall p v pc rm stk next r val mem
      (CODE: (ver_code v) # pc = Some (IPrint r next))
      (EVAL: eval_reg r rm = OK val),
      input_step p (State (v, pc, rm) stk mem) (print_event val) (State (v, next, rm) stk mem)
| input_Op:
    forall p v pc rm stk r expr next val mem
      (CODE: (ver_code v) # pc = Some (Op r expr next))
      (EVAL: eval_expr expr rm = OK val),
      input_step p (State (v, pc, rm) stk mem) E0 (State (v, next, rm # r <- val) stk mem)
| input_Cond:
    forall p v pc rm stk r tr fl val mem
      (CODE: (ver_code v) # pc = Some (Cond r tr fl))
      (EVAL: eval_reg r rm = OK val),
      input_step p (State (v, pc, rm) stk mem) E0 (State (v, pc_cond (bool_of_int val) tr fl, rm) stk mem)
| input_MemSet:
    forall p v pc rm stk adreg valreg next address val mem
      (CODE: (ver_code v) # pc = Some (MemSet adreg valreg next))
      (EVALAD: eval_reg adreg rm = OK address)
      (EVALVAL: eval_reg valreg rm = OK val)
      (RANGE: Integers.Int.lt address mem_size = true),
      input_step p (State (v, pc, rm) stk mem) E0 (State (v, next, rm) stk (mem # (pos_of_int address) <- val))
| input_MemGet:
    forall p v pc rm stk dstreg adreg next address val mem
      (CODE: (ver_code v) # pc = Some (MemGet dstreg adreg next))
      (EVALAD: eval_reg adreg rm = OK address)
      (RANGE: Integers.Int.lt address mem_size = true)
      (GET: mem # (pos_of_int address) = Some val),
      input_step p (State (v, pc, rm) stk mem) E0 (State (v, next, rm # dstreg <- val) stk mem)
| input_Call:
    forall p v pc rm stk fid args retreg next argvals mem
      (CODE: (ver_code v) # pc = Some (Call fid args retreg next))
      (EVAL: eval_list_reg args rm = OK argvals),
      input_step p (State (v, pc, rm) stk mem) E0 (Callstate fid argvals ((retreg, v, next, rm)::stk) mem)
| input_Callstep:
    forall p fid argvals func newrm stk mem
      (GETF: (prog_funlist p) # fid = Some func)
      (INIT: init_regs argvals (fn_params func) = OK newrm),
      input_step p (Callstate fid argvals stk mem) E0
                 (State (current_version func, ver_entry (current_version func), newrm) stk mem)
| input_Return:
    forall p v pc rm r retval stk mem
      (CODE: (ver_code v) # pc = Some (Return r))
      (EVAL: eval_reg r rm = OK retval),
      input_step p (State (v, pc, rm) stk mem) E0 (Returnstate retval stk mem)
| input_Returnstep:
    forall p retreg callee_v callee_next callee_rm retval stk mem,
      input_step p (Returnstate retval ((retreg, callee_v, callee_next, callee_rm)::stk) mem) E0
                 (State (callee_v, callee_next, callee_rm # retreg <- retval) stk mem)
| input_EOE:
    forall p retval mem,
      input_step p (Returnstate retval nil mem) E0 (Final retval)
(* we could choose not to put any assume in the input language *)
(* but this might be an alternative to generating them dynamically *)
| input_Assume_holds:
    forall p v pc rm stk e ftgt ltgt vm next guard mem
      (CODE: (ver_code v) # pc = Some (Assume e (ftgt, ltgt) vm next))
      (EVAL: eval_reg e rm = OK guard)
      (GUARD_OK: bool_of_int guard = true),
      input_step p (State (v, pc, rm) stk mem) E0 (State (v, next, rm) stk mem)
| input_Assume_fails:
    forall p v pc rm stk e ftgt ltgt vm next guard newrm mem
      (CODE: (ver_code v) # pc = Some (Assume e (ftgt, ltgt) vm next))
      (EVAL: eval_reg e rm = OK guard)
      (GUARD_OK: bool_of_int guard = false)
      (BUILD: update_regmap vm rm = OK newrm),
      input_step p (State (v, pc, rm) stk mem) E0 (Deoptstate ftgt ltgt newrm stk mem)
| input_Deopt:
    forall p stk ftgt ltgt newrm func newver mem
      (FINDF: (prog_funlist p)#ftgt = Some func)
      (TGTVER: base_version func = newver),
      input_step p (Deoptstate ftgt ltgt newrm stk mem) E0 (State (newver, ltgt, newrm) stk mem).

Inductive init_input_state (p:program) : input_state -> Prop :=
| init_input:
      init_input_state p (Callstate (prog_main p) nil nil init_mem).

Inductive final_input_state (p:program) : input_state -> int -> Prop  :=
| final_input:
    forall retval,
      final_input_state p (Final retval) retval.

Definition input_sem (p:program) : semantics :=
  Semantics_gen input_step (init_input_state p) (final_input_state p) p.


(** * Dynamic Semantics  *)
(* Same semantics as the mixed one, except that optimizations can happen dynamically at call states *)
Inductive dynamic_state : Type :=
| Dynamic: program -> option (RTLfun + RTLblockfun) -> synchro_state -> n_state -> nat -> dynamic_state.
(* The nat is a bound on the number of optims to do *)
(* Everything that a JIT state has except the profiler state *)

Inductive dynamic_step : unit -> dynamic_state -> Events.trace -> dynamic_state -> Prop :=
| exe_step:
    forall p rtl nc sy1 ms1 sy2 ms2 nb_opt t
      (MIXED: mixed_step p rtl nc (sy1, ms1) t (sy2, ms2)),
      dynamic_step tt (Dynamic p rtl sy1 (ms1,nc) nb_opt) t (Dynamic p rtl sy2 (ms2,nc) nb_opt)
| opt_step:
    forall p rtl nc1 nc2 loc ms nb_opt ps
      (EXE: exists t sy2 ms2, mixed_step p rtl nc1 (S_Call loc, ms) t (sy2, ms2))
      (OPT: exec (optimize ps p) naive_impl (ms,nc1) = SOK tt (ms,nc2)),
      dynamic_step tt (Dynamic p rtl (S_Call loc) (ms,nc1) (S nb_opt)) E0
                   (Dynamic p rtl (S_Call loc) (ms,nc2) nb_opt).
(* Optimizations are only possible when execution is also possible *)
(* This also the dynamic sem to be blocking exactly when the mixed_sem is *)

(* Only possible at S_Call *)
(* We might need to restrict the optim steps to when the profiler wants it *)
(* Otherwise the proof between jit and dynamic might not respect progress *)
(* This also means restricting when the profiler updates its state (eg Call/Return states) *)
(* Because we don't want to miss any update when going to the JIT sem *)

Inductive init_dynamic_state (p:program) (rtl:option (RTLfun + RTLblockfun)): dynamic_state -> Prop :=
| init_dynamic: forall nb_opt,
    init_dynamic_state p rtl (Dynamic p rtl (S_Call (ir_call (prog_main p) nil)) init_n_state nb_opt).

Inductive final_dynamic_state : dynamic_state -> int -> Prop :=
| final_dynamic:
    forall p rtl retval ms nb_opt,
      final_dynamic_state (Dynamic p rtl (EOE retval) ms nb_opt) retval.

Definition dynamic_sem (p:program) (rtl:option (RTLfun + RTLblockfun)): semantics :=
  Semantics_gen dynamic_step (init_dynamic_state p rtl) final_dynamic_state tt.
      
