(* The profiler gathers information and chooses when to optimize the program *)
(* It sends optimizing information: which function to optimize, with which values... *)
(* This info is not relevant to the correctness proof *)
open Common
open BinNums
open Maps
open Values
open IR
open Interpreter
open List
open Printf
open Camlcoq
open Printer
open Monad
open Monad_impl
open Flags

(* Converting values to OCaml int *)
let rec int64_of_positive = function
  | Coq_xI p -> Int64.add (Int64.shift_left (int64_of_positive p) 1) 1L
  | Coq_xO p -> Int64.shift_left (int64_of_positive p) 1
  | Coq_xH -> 1L

let rec int_of_positive = function
  | Coq_xI p -> ((int_of_positive p) lsl 1) + 1
  | Coq_xO p -> (int_of_positive p) lsl 1
  | Coq_xH -> 1

   
type optim_id = fun_id
   
(* So far, the profiler associates to each function its number of calls *)
type profiler_state =
  { fun_map : int PMap.t;
    status : jit_status;
    already: fun_id list;       (* already optimized functions *)
    fidoptim : optim_id; }
(* In already, we put functions that we already ASKED to optimize *)
(* Maybe these suggestions weren't followed by the JIT, and the functions weren't actually optimized *)

(* Initially, each function has been called 0 times, with no arguments *)
let initial_profiler_state =
  { fun_map = PMap.init 0;      (* initially no functions have been called *)
    status = Exe;
    already = [];               (* no optimized functions *)
    fidoptim = Coq_xH; }

(* The number of calls to a function before optimization *)
let nb_calls_optim = 2

(* Keep the same profiler state information, but with Exe status *)
let exe_ps (ps:profiler_state) =
  {fun_map = ps.fun_map; status = Exe; already = ps.already; fidoptim = ps.fidoptim }
  
let print_stacktop s : unit =
  Printf.printf "stacktop {";
  List.fold_left (fun _ i -> Printf.printf "%Ld " (camlint64_of_coqint i)) () ((mut s).state_stacktop);
  Printf.printf "} "

let print_asm_sf asf : unit =
  match asf with
  | (((caller, cont), retreg), live) ->
     Printf.printf "(%ld , [" (camlint_of_coqint caller);
     List.fold_left (fun _ i -> Printf.printf "%ld " (camlint_of_coqint i)) () live;
     Printf.printf "]) "
  
let print_stackframe sf : unit =
  match sf with
  | IR_SF _ -> Printf.printf "IR "
  | ASM_SF asf -> print_asm_sf asf; Printf.printf " "

let print_stack s : unit =
  List.fold_left (fun _ sf -> print_stackframe sf) () ((mut s).state_stack)

let print_monad_state' s : unit =
  Printf.printf "[Monad State] ";
  (* print_argbuf s; *)
  print_stacktop s;
  Printf.printf "\n[Stack] ";
  print_stack s;
  Printf.printf "\n"
  
let print_monad_state =
  fun s ->
  if false then print_monad_state' s;
  SOK ((),s)

let print_call_loc cl : unit =
  match cl with
  | Coq_ir_call (fid,l) -> Printf.printf "Call to Fun %Ld ( " (int64_of_positive fid);
                           List.fold_left (fun _ i -> Printf.printf "%ld " (camlint_of_coqint i)) () l;
                           Printf.printf ")\n"
  | Coq_nat_call -> Printf.printf "CALL FROM NATIVE\n"

let print_ret_loc rl : unit =
  match rl with
  | Coq_ir_ret i -> Printf.printf "Return with value %Ld\n" (camlint64_of_coqint i)
  | Coq_nat_ret -> Printf.printf "RETURN FROM NATIVE\n"

let print_deopt_loc dl : unit =
  match dl with
  | Coq_ir_deopt (fid, lbl, rm) -> Printf.printf "Deopt to Fun %Ld\n" (int64_of_positive fid)
  | Coq_nat_deopt -> Printf.printf "DEOPT FROM NATIVE\n"
                  
(* Printing the current synchro state *)
let print_debug (s:synchro_state) : unit =
  Printf.printf "SYNCHRO: ";
  begin match s with
  | S_Call cl ->
     print_call_loc cl
  | S_Return rl ->
     print_ret_loc rl
  | S_Deopt dl ->
     print_deopt_loc dl
  | Halt_IR (i) ->
     Printf.printf "Created Interpreter state\n"
  | Halt_ASM(_,a) ->
     Printf.printf "Created ASM state\n"
  | Halt_RTL(_,_) ->
     Printf.printf "Created RTL state\n"
  | Halt_Block(_) ->
     Printf.printf "Created RTLblock state\n"
  | EOE (v) ->
     Printf.printf "EOE\n"
  end

let print_debug_cp (cp:checkpoint) : unit =
  Printf.printf "\027[32mCHKPT:\027[0m ";
  begin match cp with
  | C_Call cl ->
     print_call_loc cl
  | C_Return rl ->
     print_ret_loc rl
  | C_Deopt dl ->
     print_deopt_loc dl
  end;
  Printf.printf "%!"

  
(* The function that analyzes the current synchronization state *)
let profiler (ps:profiler_state) (cp:checkpoint) =
  if !print_chkpts then print_debug_cp (cp);
  match !allow_opt with        (* if this is false, the profiler will never suggest optimizing *)
  | false -> exe_ps ps
  | true -> 
     match cp with
     | C_Call (Coq_ir_call (fid,val_list)) ->  (* Just before a Call *)
        (* TODO: also increase the counter when we call from native? *)
        let psmap = ps.fun_map in
        let newpsmap = PMap.set fid ((PMap.get fid psmap)+1) psmap in (* updating the number of executions *)
        begin match (PMap.get fid newpsmap > nb_calls_optim && not(List.mem fid ps.already)) with
        (* The profiler suggests optimizing the called function *)
        | true ->
           if !print_chkpts then (Printf.printf ("\027[95mPROFILER:\027[0m Optimizing Fun%d\n%!") (int_of_positive fid));
           {fun_map = newpsmap; status = Opt; already = fid::ps.already; fidoptim = fid}
        (* Either already optimized or not been called enough: we keep executing *)
        | false -> {fun_map = newpsmap; status = Exe; already = ps.already; fidoptim = ps.fidoptim }
        end
     | _ -> exe_ps ps              (* On all other states, we simply keep executing *)
       
    
let optim_policy (ps:profiler_state) = ps.status

let backend_suggestion (ps:profiler_state) = ps.fidoptim

