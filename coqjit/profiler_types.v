(* The profiler types and parameters *)
(* The JIT correctness does not depend on their implementation *)
Require Import IR.
Require Import common.



(* The state of the profiler *)
Parameter profiler_state: Type.

(** * Optimization Suggestions  *)

(* the locations where the profiler wants to insert anchors *)
Parameter anchors_to_insert : profiler_state -> list (fun_id * (list label)).

(* The middle-end optimizations suggestions for the middle-end *)
Parameter middle_end_suggestion: profiler_state -> list (fun_id * middle_wish).

(* Suggest a function to use the backend on *)
Parameter backend_suggestion: profiler_state -> fun_id.


(** * Interface - External Heuristics  *)

Parameter initial_profiler_state: program -> profiler_state.
Parameter profiler: profiler_state -> checkpoint -> profiler_state.
Parameter optim_policy: profiler_state -> jit_status.
