(** * The JIT hypervisor function  *)

Require Import Events.
Require Import Values.
Require Import Integers.
Require Import IR.
Require Import backend.
Require Import optimizer.
Require Import ASMinterpreter.
Require Import IRinterpreter.
Require Import common.
Require Import primitives.
Require Import monad.
Require Import Errors.
Require Import intpos.


(** * Hypervisor Helper functions  *)

(* getting the function that we want to call *)
Definition get_callee (cl:call_loc) : free fun_id :=
  match cl with
  | ir_call fid _ => fret fid
  | nat_call =>
    do id <<- fprim (Prim_Load);
      fret (pos_of_int id)
  end.

(* Pushing all arguments to the stack, first argument is pushed first *)
Fixpoint push_args (l:list int) : free unit :=
  match l with
  | nil => fret (tt)
  | arg::l' => do _ <<- fprim(Prim_Save arg);
               push_args l'
  end.

(* We want to call a native function so we want the arguments in the arg buffer *)
Definition set_up_args (cl:call_loc) : free unit :=
  match cl with
  | ir_call fid args => push_args args
  | nat_call =>
    do _ <<- fprim(Prim_Load);
      fret (tt) (* calling native from native: the args are already set up but we remove the nb of args *)
  end.

(* Pops n times the arguments and reverses them *)
Fixpoint pop_args' (nb:nat) (l:list int) : free (list int) :=
  match nb with
  | O => fret (l)
  | S nb' =>
    do arg <<- fprim(Prim_Load);
      pop_args' nb' (arg::l)
  end.

Definition pop_args (nb:nat) : free (list int) :=
  pop_args' nb nil.

(* Getting the arguments for an IR call, wether there are already there or have to be loaded *)
Definition get_args (a:call_loc) : free (list int) :=
  match a with
  | ir_call fid args => fret args
  | nat_call =>
    do nb_args <<- fprim(Prim_Load);
      do nb <<- fret(nat_of_int (nb_args));
      pop_args nb
  end.


(* pops n*2 the varmap that has been saved to the stack *)
Fixpoint get_varmap (nb:nat) (l:list int) : free (list int) :=
  match nb with
  | O => fret l
  | S nb' =>
    do rint <<- fprim(Prim_Load);
      do vint <<- fprim(Prim_Load);
      get_varmap nb' (vint::rint::l)
  end.

(* creates a regmap from the loaded list of integers *)
Fixpoint rebuild_regmap (l:list int) : res reg_map :=
  match l with
  | nil => OK (empty_regmap)
  | vint::rint::l' =>
    do rm <- rebuild_regmap l';
      OK (rm # (pos_of_int rint) <- vint)
  | _ => Error (MSG "Can't rebuild regmap"::nil)
  end.

(* gets the regmap in the stack *)
Definition build_rm (rml:deopt_loc) : free (reg_map) :=
  match rml with
  | ir_deopt ftgt ltgt rm => fret rm
  | nat_deopt =>
    do intsize <<- fprim(Prim_Load);
      do size <<- fret (nat_of_int intsize);
      do lst <<- get_varmap size nil;
      fret' (rebuild_regmap lst)
  end.


(* Getting the target of a deopt *)
Definition get_target (dl:deopt_loc) : free (fun_id * label) :=
  match dl with
  | ir_deopt ftgt ltgt rm => fret (ftgt, ltgt)
  | na_deopt =>
    do ftgt <<- fprim(Prim_Load);
      do ltgt <<- fprim(Prim_Load);
      fret (pos_of_int ftgt, pos_of_int ltgt)
  end.

(* When we encounter a return, we want to either get the return value, or set it up in the stack *)
Definition get_retval (rl:ret_loc) : free int :=
  match rl with
  | ir_ret i => fret i
  | nat_ret => fprim (Prim_Load)
  end.


(** * Profiler oracle, external heuristics  *)
(* The JIT correctness does not depend on their implementation *)
Parameter initial_profiler_state: profiler_state.
Parameter profiler: profiler_state -> checkpoint -> profiler_state.
Parameter optim_policy: profiler_state -> jit_status.

(** * JIT Data  *)
(* The state of the JIT that gets modified with each step *)
(* Not counting the global data-structures in the monad state *)
Record jit_data: Type := mk_data {
  prog: program;                (* current program *)
  prof_state: profiler_state;   (* state of the profiler *)
  nb_optim: nat                   (* number of optimizations left *)
}.

(* Maximum number of optimizations to perform *)
Parameter max_optim: nat.

(* Maximum number of interpreter steps *)
Parameter interpreter_fuel : nat.

Definition initial_jit_data (p:program) : jit_data :=
  (mk_data p initial_profiler_state max_optim).

(* Choosing the next step of the JIT (execution or optimizing) *)
Definition next_status (ps:profiler_state) (cp:checkpoint) (nb_optim:nat): jit_status :=
  match nb_optim with
  | O => Exe                    (* force execution if we've reached the max number of optims *)
  | _ =>
    match cp with
    | C_Call _ => optim_policy ps (* only optimizing at Call states *)
    | _ => Exe
    end
  end.


(** * The JIT state machine *)
Inductive jit_state : Type :=
| PROF: jit_data -> checkpoint -> jit_state    (* before calling the profiler*)
| OPT: jit_data -> checkpoint -> jit_state     (* before calling the optimizer *)
| EXE: jit_data -> checkpoint -> jit_state     (* when the JIT has decided to execute *)
| EXE_IR: jit_data -> ir_state -> jit_state    (* when using the interpreter to execute the IR *)
| EXE_NAT: jit_data -> asm_id -> jit_state     (* when executing native code *)
| END: jit_data -> int -> jit_state.

Definition initial_jit_state (p:program) : jit_state :=
  PROF (initial_jit_data p) (C_Call (ir_call (prog_main p) nil)).

Inductive init_jit_state (p:program) : jit_state -> Prop :=
| init_js :
    forall js
      (INIT: initial_jit_state p = js),
      init_jit_state p js.

Definition jit_final (js:jit_state) : option int :=
  match js with
  | END _ r => Some r
  | _ => None
  end.

Inductive final_jit_state : jit_state -> int -> Prop :=
| final_js:
    forall js r
      (FINAL: jit_final js = Some r),
      final_jit_state js r.


Definition jit_prog: nasm_prog jit_state :=
  fun (js:jit_state) =>
    match js with
    | PROF jd cp => Ato           (* Calling the Profiler to decide whether to Execute or Optimize *)
      (do newps <<- fret (profiler (prof_state jd) cp);
         do newjd <<- fret (mk_data (prog jd) newps (nb_optim jd));
         match (next_status newps cp (nb_optim jd)) with
         | Exe => fret (E0, EXE newjd cp)
         | Opt => fret (E0, OPT newjd cp)
         end)

    | OPT jd cp => Ato                             (* Optimizing Before Executing *)
      (do _ <<- optimize (prof_state jd) (prog jd); (* Calls the backend and installs code *)
         do newjd <<- fret (mk_data (prog jd) (prof_state jd) (Nat.pred (nb_optim jd)));
         fret (E0, EXE newjd cp))  (* we can go to PROF again if we wish to optimize twice *)

    | EXE jd cp => Ato            (* Dispatching execution *)
      (match cp with
       | C_Call loc =>
         do fid <<- get_callee(loc); (* getting the function to call *)
           do compiled <<- fprim(Prim_Check_Compiled fid);
           match compiled with
           | Not_compiled =>     (* Building the IR interpreter state *)
             do args <<- get_args (loc);
               do func <<- try_option ((prog_funlist (prog jd)) # fid) "Unkown function";
               do version <<- fret (current_version func);
               do newrm <<- fret' (init_regs args (fn_params func));
               fret (E0, EXE_IR jd (version, ver_entry version, newrm))
           | Installed af =>
             do _ <<- set_up_args (loc); (* putting the args in the stack if they aren't here already *)
               fret (E0, EXE_NAT jd (Call_id fid))
           end
       | C_Return loc =>
         do retval <<- get_retval (loc); (* pops the return value of the stack *)
         do osf <<- fprim(Prim_OpenSF); (* pops the top of the last stackframe *)
          match osf with
          | empty_stack =>       (* end of execution *)
            fret (E0, END jd retval)                  
          | ir_sf (retreg, v, pc, rm) =>         (* return to the interpreter by creating an interp state *)
            do newrm <<- fret (rm # retreg <- retval);
              fret (E0, EXE_IR jd (v, pc, newrm))
          | nat_sf caller_fid cont_lbl retreg => (* Calling the native continuation *)
            do _ <<- fprim(Prim_Save retval);   (* setting up the return value on top of the stack *)
              fret (E0, EXE_NAT jd (Cont_id (pos_of_int caller_fid) (pos_of_int cont_lbl)))
          end
       | C_Deopt loc =>
         do (ftgt, ltgt) <<- get_target (loc);
         do rm <<- build_rm (loc);
           do func <<- try_option ((prog_funlist (prog jd)) # ftgt) "Unkown function";
           do version <<- fret (base_version func);
           fret (E0, EXE_IR jd (version, ltgt, rm))
       end)

    | EXE_IR jd int_st => Ato  (* calling the IR interpreter *)
      (do (t, icp) <<- ir_int_step int_st;
         match icp with
         | Done cp => fret (t, PROF jd cp)
         | Halt int_st' => fret (t, EXE_IR jd int_st')
         end)

    | EXE_NAT jd id => LoadAndRun

    | END _ r => Ato (ferror (MSG "Uncaught End of Execution"::nil))
              
    end.

(* Is the JIT at a Final Value *)
(* Returning the final returned value of the JIT *)
Definition jit_final_value (js:jit_state): option int :=
  match js with
  | END _ i => Some i
  | _ => None
  end.

(* Returning the program of a JIT state *)
(* Useful if we want to look at the optimizations a JIT performed *)
Definition current_program (js:jit_state): program :=
  match js with
  | PROF jd _ => prog jd
  | OPT jd _ => prog jd
  | EXE jd _ => prog jd
  | EXE_IR jd _ => prog jd
  | EXE_NAT jd _ => prog jd
  | END jd _ => prog jd
  end.

(** * Specifying the Start and End of Non-Atomic LoadAndRun *)
Definition load_spec (a:asm_id) : free (Asm.genv * Asm.state) :=
  do asmp <<- fprim(Prim_Load_Code a);
    do s <<- fret' (init_nat_state asmp);
    fret (build_genv asmp, s).

Definition ret_spec (jd:jit_data) (i:int) : free jit_state :=
  do cp <<- fret' (get_checkpoint i);
  fret (PROF jd cp).

(** * A Specification for calling Native Code  *)
Definition native_step_spec (geasms:Asm.genv * Asm.state): free (trace * itret int (Asm.genv * Asm.state)) :=
  let (ge, asms) := geasms in
  do (t, i) <<- asm_step ge asms;
    match i with
    | Done r => fret (t, Done r)
    | Halt s => fret (t, Halt (ge, s)) (* preservig global env *)
    end.

Definition get_id (s:jit_state) : free asm_id :=
  match s with
  | EXE_NAT jd id => fret id
  | _ => ferror (MSG "Wrong Call State"::nil)
  end.

Definition get_data (s:jit_state) : free jit_data :=
  match s with
  | EXE_NAT jd id => fret jd
  | _ => ferror (MSG "Wrong Call State"::nil)
  end.

Definition native_load_spec : jit_state -> free (Asm.genv * Asm.state) :=
  fun call_state => do id <<- get_id call_state; load_spec (id).

Definition native_return_spec : jit_state -> int -> free jit_state :=
  fun call_state r => do jd <<- get_data call_state; ret_spec jd r.
