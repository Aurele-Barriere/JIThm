(* Using the extracted JIT *)
open Backend
open IR
open BinNums
open Maps
open IRtoRTLblock
open FlattenRTL
open Asmexpand
open ASMinterpreter
open Monad
open Camlcoq
open Profiler
open Events
open Int64
open Jit
open Common
open IRast
open Lexing
open Printf
open Flags
open Monad_impl
open Printer

(** * Parsing and Lexing IR Programs *)
(* https://v1.realworldocaml.org/v1/en/html/parsing-with-ocamllex-and-menhir.html *)
let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
  
let parse_with_error lexbuf =
  try IRparser.prog IRlexer.read lexbuf with
  | IRlexer.SyntaxError msg ->
     fprintf stderr "%a: %s\n" print_position lexbuf msg;
     None
  | IRparser.Error ->
     fprintf stderr "%a: syntax error\n" print_position lexbuf;
     exit (-1)

let get_program filename: program =
  let inx = open_in filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let (apo:IRast.aprogram option) = parse_with_error lexbuf in
  match apo with
  | None -> let _ = close_in inx in failwith "Failed to parse a program"
  | Some ap -> let _ = close_in inx in IRast.convert_program ap

   
(** * Int Conversions  *)
(* from the CamlCoq library *)
let int64_of_coqint (n:Integers.Int.int) : int64 =
  camlint64_of_coqint n

let coqint_of_int64 (n:int64) : Integers.Int.int =
  coqint_of_camlint64 n


(** * Non Monadic Impure Execution  *)
(* By non-monadic, I mean not even keeping a trivial state monad where the state is unit *)
(* the monad was good for the semantics and proofs, but for the impure version it's no better  *)
(* than using [;] and [let ... in] *)

(** * External Primitives  *)
(* written in C, in the c_primitives directory *)
external init_stack: unit -> unit = "caml_init_stk"
external stack_push: int64 -> unit = "caml_stack_push"
external stack_pop: unit -> int64 = "caml_stack_pop"
external push_ir_id: unit -> unit = "caml_push_ir_id"
external close_sf: int64 -> int64 -> int64 -> unit = "caml_close_sf"
external free_stack: unit -> unit = "caml_free_stack"
external print_stack: unit -> unit = "caml_print_stack"

external init_heap: unit -> unit = "caml_init_heap"
external heap_set: int64 -> int64 -> unit = "caml_heap_set"
external heap_get: int64 -> int64 = "caml_heap_get"
external free_heap: unit -> unit = "caml_free_heap"

external install: unit -> int64 = "caml_install"
external run_code: int64 -> int64 = "caml_run_code"
  
  
(** * Declaring Global Data-Structures *)
let ir_stack : (coq_IR_stackframe list) ref = ref []

(* For the generated codes, we store two things *)
(* First, we store the entire program in case we want to interpret it (safe mode) *)
let safe_native_codes : asm_codes ref = ref (PTree.empty)
(* Second, we store addresses where the native code is installed for unsafe mode *)
type native_fun = int64 * (int64 PTree.t)
type native_codes = native_fun PTree.t
let unsafe_native_codes : native_codes ref = ref (PTree.empty)


let init() =
  Printf.printf "=== Initializing Stack and Heap ===\n\n";
  init_stack();
  init_heap();
  ir_stack := [];
  safe_native_codes := PTree.empty;
  unsafe_native_codes := PTree.empty;
  Printf.printf "OK\n\n"

let ignore_rm s =
  try (Sys.remove s) with
  | _ -> ()
  
let clean() =
  free_stack();
  free_heap();
  ignore_rm "tmp.s";
  ignore_rm "linked.s";
  ignore_rm "linked.o"
                                 

(** * Impure Primitives, when called from OCaml  *)
let save (x:Integers.Int.int) : unit =
  let x64 = int64_of_coqint x in
  stack_push(x64)
  
let load () : Integers.Int.int =
  let x = stack_pop() in
  coqint_of_int64 (x)
                                   
let push_irsf (irsf:coq_IR_stackframe) : unit =
  push_ir_id();
  ir_stack := irsf::(!ir_stack)

let pop_irsf () : coq_IR_stackframe =
  let istk = !ir_stack in
  match istk with
  | [] -> failwith "Missing IR stackframe"
  | isf::istk' -> ir_stack := istk'; isf

let close_sf (caller:Integers.Int.int) (cont:Integers.Int.int) (retreg:Integers.Int.int) : unit =
  let ca = int64_of_coqint caller in
  let co = int64_of_coqint cont in
  let re = int64_of_coqint retreg in
  close_sf ca co re

let open_sf () : open_sf =
  let id = load() in
  if (id = coq_EMPTY) then
    begin Coq_empty_stack end
  else if (id = coq_IR_ID) then
    begin
      let isf = pop_irsf() in Coq_ir_sf (isf)
    end
  else if (id = coq_NAT_ID) then
    begin
      let caller = load() in
      let cont = load() in
      let retreg = load() in
      Coq_nat_sf (caller, cont, retreg)
    end
  else
    failwith "Unknown Stackframe ID"

let memset (i:Integers.Int.int) (j:Integers.Int.int) : unit =
  let i64 = int64_of_coqint i in
  let j64 = int64_of_coqint j in
  heap_set i64 j64

let memget (i:Integers.Int.int) : Integers.Int.int =
  let i64 = int64_of_coqint i in
  let x = heap_get(i64) in
  coqint_of_int64 (x)

let check_compiled (f:fun_id) : compiled_status =
  let codes = !safe_native_codes in
  match (PTree.get f codes) with
  | None -> Not_compiled
  | Some af -> Installed af

let install_single_fun (p:Asm.program): int64 =
  (* writes to tmp.s *)
  let oc = open_out "tmp.s" in
  Printer.print_single_asm p oc;
  close_out oc;
  install()

let install_conts (conts: Asm.program PTree.t): int64 PTree.t =
  PTree.map (fun contid cont -> install_single_fun cont) conts
    
             
let install_code (f:fun_id) (af:asm_fun) : unit =
  (* first, we store the x86_64 into the safe codes *)
  safe_native_codes := PTree.set f af !safe_native_codes;
  if (not !safe_mode) then
    match af with
    | (entryp, contp) ->
       let entry_addr = install_single_fun entryp in
       let cont_addr = install_conts contp in
       unsafe_native_codes := PTree.set f (entry_addr, cont_addr) !unsafe_native_codes
  

let safe_load_prog_code (fid:fun_id) : asm_fun =
  let codes = !safe_native_codes in
  match (PTree.get fid codes) with
  | None -> failwith "Loading unknown code"
  | Some af -> af
  
let safe_load_code (aid:asm_id) : Asm.program =
  match aid with
  | Call_id fid ->
     let asmf = safe_load_prog_code fid in
     fst asmf
  | Cont_id (fid, cont_lbl) ->
     let asmf = safe_load_prog_code fid in
     match (PTree.get cont_lbl (snd asmf)) with
     | None -> failwith "Can't find this continuation"
     | Some cont -> cont

let unsafe_load_prog_code (fid:fun_id) : native_fun =
  let codes = !unsafe_native_codes in
  match (PTree.get fid codes) with
  | None -> failwith "Loading unknown code"
  | Some af -> af
  
let unsafe_load_code (aid:asm_id) : int64 =
  match aid with
  | Call_id fid ->
     let asmf = unsafe_load_prog_code fid in
     fst asmf
  | Cont_id (fid, cont_lbl) ->
     let asmf = unsafe_load_prog_code fid in
     match (PTree.get cont_lbl (snd asmf)) with
     | None -> failwith "Can't find this continuation"
     | Some cont -> cont
     

(* We could avoid using Obj.magic if Coq extraction could generate GADTs (see gadt.ml) *)
let nm_exec_prim (p:'x primitive) : Obj.t =
  match p with
  | Prim_Save (i) -> Obj.magic (save i)
  | Prim_Load -> Obj.magic (load())
  | Prim_MemSet (i,j) -> Obj.magic (memset i j)
  | Prim_MemGet (i) -> Obj.magic (memget i)
  | Prim_CloseSF (caller, cont, retreg) -> Obj.magic (close_sf caller cont retreg)
  | Prim_OpenSF -> Obj.magic (open_sf())
  | Prim_PushIRSF (irsf) -> Obj.magic (push_irsf irsf)
  | Prim_Install_Code (funid, asmf) -> Obj.magic (install_code funid asmf)
  | Prim_Load_Code (asmid) -> Obj.magic (safe_load_code asmid)
  | Prim_Check_Compiled (fid) -> Obj.magic (check_compiled fid)
     
  
(* executing free monads *)
let rec nm_exec (f:'A free) : 'A =
  match f with
  | Coq_pure (a) -> a
  | Coq_ferror (e) -> print_error e; failwith "JIT crashed"
  | Coq_impure (prim, cont) ->  (* no bind here, a let in *)
     let x = nm_exec_prim prim in
     nm_exec (cont x)


(* executing loops (to run the x86 spec, no needed in the final version) *)
let rec nm_loop (f:'A -> (trace * ('B , 'A) itret) free) (a:'A): 'B =
  match (nm_exec (f a)) with
  | (t, Done r) -> print_trace' true t; r
  | (t, Halt s) -> print_trace' true t; nm_loop f s
     
(* actually returns a function pointer *)
let nm_load (state:jit_state) : int64 =
  match state with
  | EXE_NAT (jd, id) ->
     unsafe_load_code id
  | _ -> failwith "Wrong Call State"

let nm_run (addr:int64) : int64 =
  run_code addr
  
(* creates the next jit_state *)
let nm_return (state:jit_state) (i:int64) : jit_state =
  match state with
  | EXE_NAT (jd, id) -> begin
     let cp = get_checkpoint (coqint_of_int64 i) in
     match cp with
     | Errors.OK chk -> PROF (jd, chk)
     | _ -> failwith "Wring Check Point"
    end
  | _ -> failwith "Wrong Call State"
  
(* executing non-atomic state machines *)
let rec nm_run_nasm  (nas: 'state nasm_prog) (s:'state) : unit =
  match (jit_final_value s) with (* checking if execution is finished *)
  | Some v ->
     print_final_value v
  | None ->
     if !debug_stk then print_stack(); 
     match (nas s) with
     | Ato free ->                 (* Atomic steps *)
        let (t, next) = nm_exec free in
        print_trace t;
        nm_run_nasm nas next       (* tailcall *)
     | LoadAndRun ->               (* Non-atomic steps *)
        if !safe_mode then begin
            let asmstate = nm_exec (native_load_spec s) in      (* load *)
            let retint = nm_loop native_step_spec asmstate in   (* step *)
            let next = nm_exec (native_return_spec s retint) in (* return *)
            nm_run_nasm nas next                                (* tailcall *)
          end else
          let fp = nm_load s in       (* load *)
          let r = nm_run fp in        (* step *)
          let next = nm_return s r in (* return *)
          nm_run_nasm nas next        (* tailcall *)


let main =
  let path = ref "" in
  let cmd_args = [
      ("-s", Arg.Set Flags.debug_stk, "Prints the Stack at every step");
      ("-u", Arg.Set Flags.safe_mode, "Disable Unsafe mode: interpret the ASM code");
      ("-a", Arg.Set Flags.print_asm_end, "Print the native codes at the end of the execution");
      ("-c", Arg.Set Flags.print_chkpts, "Print the Checkpoints during execution");
      ("-i", Arg.Clear Flags.allow_opt, "Interpreter only, disable generation of native codes")
    ] in
  let usage () =
    Printf.printf "%s" "\027[91mPlease use the jit executable on exactly one argument: the program to execute\027[0m\n\027[33m  Example: \027[0m ./jit progs_IR/prime.ir\n";
    Arg.usage cmd_args "Options:"
  in
  Arg.parse cmd_args (fun s ->
    if !path <> "" then raise (Arg.Bad ("Invalid argument "^s));
    path := s) "Options:";
  if !path = "" then (
    usage ();
    exit 1);

  Printf.printf "=== Parsing the Program ===\n\n";
  let p = get_program Sys.argv.(1) in
  Printf.printf "OK\n\n";
  init();
  Printf.printf "=== Starting the JIT ===\n\n";
  
  let js = Jit.initial_jit_state p in
  nm_run_nasm (Jit.jit_prog) js;
  if !print_asm_end then
    print_nat_codes !safe_native_codes;
  clean()
