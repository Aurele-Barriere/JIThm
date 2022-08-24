(* AST of a program and transformation to an IR program *)
open Common
open Values
open IR
open BinNums
open BinPos
open Camlcoq
open Maps
open Integers
   
(* AST is just like IR, except it uses int instead of Coq positive, and no records *)
(* And using lists instead of PTrees *)
type abinop =
  | Abplus
  | Abneg
  | Abmul
  | Abeq
  | Ablt
  | Abmod

type aunop =
  | Auneg
  | Aueqzero
  | Auplus of int
  | Aumul of int
   
type acst = int
  
type areg = int

type aexpr =
  | ABIN of abinop * areg * areg
  | AUNA of aunop * areg
  | AZAR of acst
          
type alabel = int

type afun_id = int

type adeopt_target = afun_id * alabel

(* type amovelist = (areg * aexpr) list *)
                   
type avarmap = (areg * aexpr) list

(* type asynth_frame = adeopt_target * areg * avarmap *)

type ainstruction =
  | Anop of alabel
  | Aprint of areg * alabel
  | Acall of afun_id * areg list * areg * alabel
  | Acond of areg * alabel * alabel
  | Areturn of areg
  | Aop of areg * aexpr * alabel
  | Amemset of areg * areg * alabel
  | Amemget of areg * areg * alabel
  | Aassume of areg * adeopt_target * avarmap * alabel
       
type anode = alabel * ainstruction

type aversion_decl =  alabel * anode list

type afun_decl = afun_id * areg list * aversion_decl * aversion_decl option

type aprogram = afun_id * afun_decl list

(* Convert Ocaml int to Coq positive *)
(* We assume that the argument is a strictly positive integer *)
let pos_of_int (i:int): positive = 
  P.of_int i

let z_of_int (i:int) =
  Z.of_sint i

let convert_binop (ab:abinop): bin_op =
  match ab with
  | Abplus -> Coq_bplus
  | Abneg -> Coq_bneg
  | Abmul -> Coq_bmul
  | Abeq -> Coq_beq
  | Ablt -> Coq_blt
  | Abmod -> Coq_bmod

let convert_unop (au:aunop): un_op =
  match au with
  | Auneg -> Coq_uneg
  | Aueqzero -> Coq_ueqzero
  | Auplus i -> Coq_uplus (z_of_int i)
  | Aumul i -> Coq_umul (z_of_int i)

let convert_lbl = pos_of_int
let convert_reg = pos_of_int
             
let convert_expr (ae:aexpr): expr =
  match ae with
  | ABIN (b, r1, r2) -> BIN (convert_binop b, convert_reg r1, convert_reg r2)
  | AUNA (u, r) -> UNA (convert_unop u, convert_reg r)
  | AZAR i -> ZAR (z_of_int i)

let convert_exprlist (el:aexpr list): expr list =
  List.map convert_expr el

let convert_reglist (rl:areg list): reg list =
  List.map convert_reg rl

let convert_varmap (vm:avarmap): varmap =
  List.map (fun (r,e) -> ((convert_reg r),(convert_expr e))) vm

(* let convert_movelist (ml:amovelist): movelist =
 *   List.map (fun (r,e) -> ((convert_reg r),(convert_expr e))) ml *)

let convert_target (at:adeopt_target): deopt_target =
  match at with
  | (afid, albl) -> (pos_of_int afid, convert_lbl albl)
  
(* let convert_frame ((tgt,r,vm):asynth_frame) =
 *   ((convert_target tgt, convert_reg r), convert_varmap vm)
 * 
 * let convert_synthlist (sl:asynth_frame list) =
 *   List.map convert_frame sl *)

let convert_instr (ai:ainstruction): instruction =
  match ai with
  | Anop l -> Nop (convert_lbl l)
  | Aprint (r, l) -> IPrint (convert_reg r, convert_lbl l)
  | Acall (f, rl, r, l) -> Call (pos_of_int f, convert_reglist rl, convert_reg r, convert_lbl l)
  | Acond (r, l1, l2) -> Cond (convert_reg r, convert_lbl l1, convert_lbl l2)
  | Areturn (r) -> Return (convert_reg r)
  | Aop (r, e, l) -> Op (convert_reg r, convert_expr e, convert_lbl l)
  | Amemset (r1, r2, l) -> MemSet (convert_reg r1, convert_reg r2, convert_lbl l)
  | Amemget (r1, r2, l) -> MemGet (convert_reg r1, convert_reg r2, convert_lbl l)
  | Aassume (r, tgt, vm, l) -> Assume (convert_reg r, convert_target tgt, convert_varmap vm, convert_lbl l)


let rec convert_code (anl:anode list): code =
  match anl with
  | [] -> PTree.empty
  | (l,i)::anl' -> PTree.set (convert_lbl l) (convert_instr i) (convert_code anl')

let convert_version ((lbl,anl):aversion_decl): version =
  { ver_code = convert_code anl; ver_entry = convert_lbl lbl }

let convert_version_option (verop:aversion_decl option): version option=
  match verop with
  | None -> None
  | Some v -> Some (convert_version v)
  
let convert_function ((f,rl,base,optop):afun_decl): coq_function =
  { fn_params = List.map convert_reg rl;
    fn_base = convert_version base;
    fn_opt = convert_version_option optop
  }

let id_function ((f,rl,vid,avl):afun_decl): fun_id =
  pos_of_int f
                 
(* Transform an AST into a program *)
let convert_program ((main,funlist):aprogram) : program =
  { prog_main = pos_of_int main;
    prog_funlist = List.fold_left
                     (fun t af -> PTree.set (id_function af) (convert_function af) t)
                     PTree.empty funlist }
