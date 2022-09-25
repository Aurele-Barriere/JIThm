(* Full optimizer *)
(* Middle-end then backend *)
(* We use the information from the profiler to choose optimizations *)

Require Import RTL.
Require Import IR.
Require Import monad.
Require Import common.
Require Import Coqlib.
Require Import backend.
Require Import primitives.
Require Import profiler_types.
Require Import middle_end.

(** * The Full Backend Compiler  *)
(* If the profiler suggests a wrong function to optimize, we catch the error and do nothing *)
Definition backend_optimize (ps:profiler_state) (p:program): free unit :=
  do fid <<- fret (backend_suggestion ps);
    do status <<- fprim(Prim_Check_Compiled fid);
    match status with
    | Installed _ => nothing     (* function has already been compiled *)
    | Not_compiled =>
      match ((prog_funlist p) # fid) with
      | Some func =>
        do current_ver <<- fret (current_version func);
          do params <<- fret (fn_params func);
          backend_and_install current_ver fid params (* catching errors that may happen during compilation *)
      | None => nothing            (* Can't find the function to optimize *)
      end
    end.

(** * The Full Optimizer, Middle-end + Backend  *)
(* returns a program: the one that has been modified by the middle-end *)
(* but the native code are installed in the executable memory  *)
Definition optimize (ps:profiler_state) (p:program) : free program :=
  do newp <<- fret (safe_middle_end ps p);
  do _ <<- backend_optimize ps newp;
  fret (newp).
