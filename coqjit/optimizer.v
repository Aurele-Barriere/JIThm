(* Full optimizer *)
(* Here, only the backend part *)
(* We use the information from the profiler to generate and install some code *)

Require Import RTL.
Require Import IR.
Require Import monad.
Require Import common.
Require Import Coqlib.
Require Import backend.
Require Import primitives.

(* The state of the profiler *)
Parameter profiler_state: Type.
(* Suggest a function to use the backend on *)
Parameter backend_suggestion: profiler_state -> fun_id.

(* If the profiler suggests a wrong function to optimize, we catch the error and do nothing *)
Definition optimize (ps:profiler_state) (p:program): free unit :=
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

