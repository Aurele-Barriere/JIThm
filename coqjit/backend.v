(* Going from RTL code to native programs *)
Require Import RTL.
Require Import RTLblock.
Require Import AST.
Require Import Coqlib.
Require Import Compiler.
Require Import Errors.
Require Import IRtoRTLblock.
Require Import flattenRTL.
Require Import IR.
Require Import Maps.
Require Import monad.
Require Import primitives.

(** * The CompCert Backend *)
Definition transf_rtl_program_ (f: RTL.program) : res Asm.program :=
   OK f
   @@ total_if Compopts.optim_tailcalls (time "Tail calls" Tailcall.transf_program)
   @@ time "Renumbering" Renumber.transf_program
   @@ total_if Compopts.optim_constprop (time "Constant propagation" Constprop.transf_program)
   @@ total_if Compopts.optim_constprop (time "Renumbering" Renumber.transf_program)
  @@@ partial_if Compopts.optim_CSE (time "CSE" CSE.transf_program)
  @@@ partial_if Compopts.optim_redundancy (time "Redundancy elimination" Deadcode.transf_program)
  @@@ time "Register allocation" Allocation.transf_program
   @@ time "Branch tunneling" Tunneling.tunnel_program
  @@@ time "CFG linearization" Linearize.transf_program
   @@ time "Label cleanup" CleanupLabels.transf_program
  @@@ partial_if Compopts.debug (time "Debugging info for local variables" Debugvar.transf_program)
  @@@ time "Mach generation" Stacking.transf_program
  @@@ time "Asm generation" Asmgen.transf_program.
(* We have disable the optional "Unusedglob" pass, which checks that there is no unknown global defintion for the linker *)
(* The only globals are our ptimitives here *)
(* We also deactivate inlining *)


(** * Primitive defs *)
(* primitives must be defined in the programs we are compiling *)
Definition prim_defs {F:Type} : list (ident * globdef (fundef F) unit) :=
  (EF_ident EF_save, Gfun (External (EF EF_save)))::
  (EF_ident EF_load, Gfun (External (EF EF_load)))::
  (EF_ident EF_memset, Gfun (External (EF EF_memset)))::
  (EF_ident EF_memget, Gfun (External (EF EF_memget)))::
  (EF_ident EF_close, Gfun (External (EF EF_close)))::
  (EF_ident EF_print, Gfun (External (EF EF_print)))::
  nil.

Definition prim_id_defs: list ident :=
(EF_ident EF_save)::(EF_ident EF_load)::(EF_ident EF_memset)::(EF_ident EF_memget)::(EF_ident EF_close)::(EF_ident EF_print)::nil.

(** * Constructing whole RTL programs  *)
Definition main_id : positive := xH.

Definition main_sig: signature :=
  mksignature nil Tint cc_default.

Definition main_stacksize: Z :=
  0.                            (* This is stack pre-allocation, no space needed *)

Definition make_fun (rtlc:RTL.code) (entry:positive) : RTL.function :=
  mkfunction main_sig nil main_stacksize rtlc entry.

Definition make_prog (rtlc:RTL.code) (entry:positive) : RTL.program :=
  mkprogram ((main_id, Gfun (Internal (make_fun rtlc entry)))::prim_defs) prim_id_defs main_id.

(* Compiles a single function *)
Definition fun_backend (rtlc:RTL.code) (entry:positive): res Asm.program :=
  transf_rtl_program_ (make_prog rtlc entry). (* using CompCert backend *)


Definition cont_backend (rtlc:RTL.code) (l:cont_idx) : res (PTree.t Asm.program) :=
  PTree.fold
    (fun res_asms p entry =>
       do asms <- res_asms;
         do prog <- fun_backend rtlc entry;
         OK (PTree.set p prog asms))
    l (OK (PTree.empty Asm.program)).


Definition rtl_backend (rtl:RTLfun) : res asm_fun :=
  match rtl with
  | (rtlfid, rtlcode, rtlentry, rtlidx) =>
    do call_prog <- fun_backend rtlcode rtlentry;
      do prog_tree <- cont_backend rtlcode rtlidx;
      OK (call_prog, prog_tree)
  end.

Definition backend (v:IR.version) (fid:positive) (params:list reg): res asm_fun :=
  do (block_graph, new_entry, cont_idx) <- IRtoRTLblock.rtlgen fid v params;
    do rtlfun <- flattenRTL.flatten (fid, block_graph, new_entry, cont_idx);
    rtl_backend rtlfun.
      
(* If compilation fails, we do nothing but do not propagate the error *)
(* In the end, we only have an error if installation fails *)
(* State Monad errors cannot be caught *)
Definition backend_and_install (v:IR.version) (fid:positive) (params:list reg): free unit :=
  match (backend v fid params) with
  | OK asm_f => fprim(Prim_Install_Code fid asm_f)
  | Error _ => nothing
  end.
 
