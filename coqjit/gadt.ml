(* This is not an executable file *)
(* This file is not needed by the JIT either *)
(* This is just some notes on how we could avoid using Obj.magic if the Coq extraction was able to generate GADTs *)


(* The extraction of the primitive type is incomplete. *)
(* Their return type is entirely forgotten by the extraction *)
(* If the Coq extraction generated the following GADT: *)
type _ primitive =
| Prim_Save: Int.int -> unit primitive
| Prim_Load : Int.int primitive
| Prim_MemSet : (Int.int * Int.int) -> unit primitive
| Prim_MemGet : Int.int -> Int.int primitive
| Prim_CloseSF : (Int.int * Int.int * Int.int) -> unit primitive
| Prim_OpenSF : open_sf primitive
| Prim_PushIRSF : coq_IR_stackframe -> unit primitive
| Prim_Install_Code : (fun_id * asm_fun) -> unit primitive
| Prim_Load_Code : asm_id -> Asm.program primitive
| Prim_Check_Compiled : fun_id -> compiled_status primitive

type _ free =
| Coq_pure : 't -> 't free
| Coq_impure : ('r primitive * ('r -> 't free)) -> 't free
| Coq_ferror : errmsg -> 't free

(* Then we could avoid Obj.magic by writing our functions as follows *)
let nm_exec_prim : type x. (x primitive) -> x =
  function
  | Prim_Save (i) ->  (save i)
  | Prim_Load ->  (load())
  | Prim_MemSet (i,j) ->  (memset i j)
  | Prim_MemGet (i) ->  (memget i)
  | Prim_CloseSF (caller, cont, retreg) ->  (close_sf caller cont retreg)
  | Prim_OpenSF ->  (open_sf())
  | Prim_PushIRSF (irsf) ->  (push_irsf irsf)
  | Prim_Install_Code (funid, asmf) ->  (install_code funid asmf)
  | Prim_Load_Code (asmid) ->  (load_code asmid)
  | Prim_Check_Compiled (fid) ->  (check_compiled fid)
     
  
(* executing free monads *)
let rec nm_exec (f:'A free) : 'A =
  match f with
  | Coq_pure (a) -> a
  | Coq_ferror (e) -> print_error e; failwith "JIT crashed"
  | Coq_impure (prim, cont) ->  (* no bind here, a let in *)
     let x = nm_exec_prim prim in
     nm_exec (cont x)


(* As said here: https://coq.inria.fr/refman/addendum/extraction.html *)
(* Coq extraction does not generate GADTs yet *)
(* So we stick to Obj.magic. *)
(* Another solution would have been to have one "impure" constructor per primitive in the free monad type *)
(* We avoid this solution for now to have a more readable Coq code *)


       
