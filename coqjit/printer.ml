open Events
open PrintRTL
open PrintAsm
open Flags
open Camlcoq
open BinNums
open Maps


let int64_of_coqint (n:Integers.Int.int) : int64 =
  camlint64_of_coqint n

let coqint_of_int64 (n:int64) : Integers.Int.int =
  coqint_of_camlint64 n
   
(** * Printing Events  *)
(* our prints only generate (print_event i) for some integers i *)
(* so we know what kind of events are possible *)
   
let print_trace' is_nat t =
  match t with
  | [] -> ()
  | [e] ->
     begin match e with
     | Event_annot (cl, [EVint i]) ->
        if is_nat then 
          Printf.printf "\027[36mOUTPUT:\027[0m \027[31m%Ld\027[0m\n%!" (int64_of_coqint i)
        else
          Printf.printf "\027[36mOUTPUT:\027[0m %Ld\n%!" (int64_of_coqint i)
     | _ -> failwith "Unexpected event"
     end
  | _ -> failwith "Unexpected multi-event trace" (* our language is proved to be single-events *)
         

let print_trace = print_trace' false

let print_final_value v = 
  Printf.printf "\027[33mFINAL:\027[0m %Ld\n\n" (int64_of_coqint v)
                   
(** * Printing of error messages *)
let print_error msg =
  let print_one_error = function
  | Errors.MSG s -> Printf.printf "%s" (Camlcoq.camlstring_of_coqstring s)
  | Errors.CTX i -> Printf.printf "%s" (Camlcoq.extern_atom i)
  | Errors.POS i -> Printf.printf "%ld" (Camlcoq.P.to_int32 i)
  in
  List.iter print_one_error msg

(** * RTL printing *)
let print_single_rtl rtl_graph entry =
  Printf.printf ">>>With entry: %ld<<<\n" (Camlcoq.P.to_int32 entry);
  PrintRTL.print_function stdout Coq_xH (Renumber.transf_function (Backend.make_fun rtl_graph entry));
  Printf.printf "\n"

let rec print_rtl_list rtl_graph (l:(positive * positive) list) =
  match l with
  | [] -> ()
  | (orig_l, new_l)::l' ->
     print_single_rtl rtl_graph new_l;
     print_rtl_list rtl_graph l'
  
let print_all_rtl rtl_graph entry ci =
  print_single_rtl rtl_graph entry;
  print_rtl_list rtl_graph ci


(** * ASM printing *)
let print_single_asm (ap: Asm.program) (chan) =
  match (Asmexpand.expand_program ap) with
  | OK p ->
     PrintAsm.print_program chan p;
  | Error s -> print_error s

let print_cont_asm (l: Asm.program PTree.t) : unit =
  PTree.fold
    (fun _ orig_l asmp ->
      Printf.printf ">>>Continuation of Call %ld<<<\n" (Camlcoq.P.to_int32 orig_l);
      print_single_asm asmp stdout; Printf.printf "\n")
  l ()

let print_all_asm asm_f =
  match asm_f with
  | (entryp, contp) ->
     Printf.printf ">>>Entry<<<\n";
     print_single_asm entryp stdout;
     Printf.printf "\n";
     print_cont_asm contp

let print_nat_codes ac : unit =
  PTree.fold (fun _ id a ->
      Printf.printf "\n:::Function %ld:::\n" (Camlcoq.P.to_int32 id);
      print_all_asm a) ac ()
