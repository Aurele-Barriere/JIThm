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

(* Predicting call arguments values *)
type predict =
  | Top                         (* we have seen different values *)
  | Seen of Integers.Int.int    (* we have only seen this value *)
  | Bot                         (* we have not seen anything yet *)

let update_predict (i:Integers.Int.int) (p:predict) =
  match p with
  | Top -> Top
  | Bot -> Seen i
  | Seen x -> if (i = x) then Seen i else Top

let rec update_predict_list (l:Integers.Int.int list) (pl:predict list) =
  match l, pl with
  | [], [] -> []
  | i::l', p::pl' -> (update_predict i p)::(update_predict_list l' pl')
  | _, _ -> []                  (* allows to predict even if we don't know the nb of args *)

let initial_pl : predict list =
  List.init 10 (fun _ -> Bot)
  
   
(* So far, the profiler associates to each function its number of calls *)
(* and speculate on the first argument of the compiled function *)
type profiler_state =
  { fun_map : int PMap.t;       (* number of seen calls for each function *)
    status : jit_status;        (* where we put our suggestion of optimization *)
    already: fun_id list;       (* already optimized functions *)
    fidoptim : optim_id;        (* function that we are thinking about optimizing *)
    args_pred: (predict list) PMap.t; (* predicting the values of args of each function *)
    prog: program;                    (* the initial program. can be useful to inspect *)
  }
(* In already, we put functions that we already ASKED to optimize *)
(* Maybe these suggestions weren't followed by the JIT, and the functions weren't actually optimized *)

(* Initially, each function has been called 0 times, with no arguments *)
let initial_profiler_state (p:program) =
  { fun_map = PMap.init 0;      (* initially no functions have been called *)
    status = Exe;
    already = [];               (* no optimized functions *)
    fidoptim = Coq_xH;
    args_pred = PMap.init initial_pl;
    prog = p;
  }

(* The number of calls to a function before optimization *)
let nb_calls_optim = 2

(* Keep the same profiler state information, but with Exe status *)
let exe_ps (ps:profiler_state) =
  {fun_map = ps.fun_map; status = Exe; already = ps.already; fidoptim = ps.fidoptim; args_pred = ps.args_pred; prog = ps.prog }
  
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



(* attempts to find the entry label of a function *)
let get_fun_entry (fid:fun_id) (p:program) : label =
  match (find_function_ir fid p) with
  | None -> Coq_xH
  | Some f -> (f.fn_base).ver_entry

let get_first_param (fid:fun_id) (p:program) : reg  =
  match (find_function_ir fid p) with
  | None -> Coq_xH
  | Some f -> hd (f.fn_params)
    
let optim_policy (ps:profiler_state) = ps.status

let backend_suggestion (ps:profiler_state) =
  if !allow_compile then (Some ps.fidoptim) else None

(* speculating on the first argument *)
let middle_end_suggestion (ps:profiler_state) : (fun_id * middle_wish) list =
  if !allow_spec then
    let fid = ps.fidoptim in
    let p = ps.prog in
    match (PMap.get fid ps.args_pred) with
    | (Seen (i))::l -> [fid, AS_INS (UNA(Coq_ueq i,get_first_param fid p), get_fun_entry fid p)]
    | _ -> []
  else []

(* inserting an anchor at the function entry IF  *)
let anchors_to_insert (ps:profiler_state): (fun_id * (label list)) list =
  if !allow_spec then
    match (PMap.get ps.fidoptim ps.args_pred) with
    | (Seen (i))::l -> [ps.fidoptim, [get_fun_entry ps.fidoptim ps.prog]]
    | _ -> []
  else []

let print_anchors (ps:profiler_state) : unit =
  match (anchors_to_insert ps) with
  | [fid, [entry]] ->  Printf.printf ("\027[95mPROFILER:\027[0m Anchor + Assume: %d@%d\n%!") (int_of_positive fid) (int_of_positive entry)
  | _ -> ()


(* The function that analyzes the current synchronization state *)
let profiler (ps:profiler_state) (cp:checkpoint) =
  if !print_chkpts then print_debug_cp (cp);
  match !allow_opts with        (* if this is false, the profiler will never suggest optimizing *)
  | false -> exe_ps ps
  | true -> 
     match cp with
     | C_Call (Coq_ir_call (fid,val_list)) ->  (* Just before a Call *)
        (* TODO: also increase the counter when we call from native? *)
        let psmap = ps.fun_map in
        let newpsmap = PMap.set fid ((PMap.get fid psmap)+1) psmap in (* updating the number of executions *)
        let pred = ps.args_pred in
        let newpred = PMap.set fid (update_predict_list val_list (PMap.get fid pred)) pred in (* updating our argument prediction *)
        begin match (PMap.get fid newpsmap > nb_calls_optim && not(List.mem fid ps.already)) with
        (* The profiler suggests optimizing the called function *)
        | true ->
           if !print_chkpts then (Printf.printf ("\027[95mPROFILER:\027[0m Optimizing Fun%d\n%!") (int_of_positive fid));
           let newps = {fun_map = newpsmap; status = Opt; already = fid::ps.already; fidoptim = fid; args_pred = newpred; prog=ps.prog} in
           if !print_chkpts then (print_anchors newps);
           newps
           
        (* Either already optimized or not been called enough: we keep executing *)
        | false -> {fun_map = newpsmap; status = Exe; already = ps.already; fidoptim = ps.fidoptim; args_pred = newpred; prog=ps.prog }
        end
     | _ -> exe_ps ps              (* On all other states, we simply keep executing *)
