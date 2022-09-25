(* The profiler types and parameters *)

Require Import IR.
Require Import common.



(* The state of the profiler *)
Parameter profiler_state: Type.
(* Suggest a function to use the backend on *)
Parameter backend_suggestion: profiler_state -> fun_id.

(* the locations where the profiler wants to insert anchors *)
Parameter anchors_to_insert : profiler_state -> list (fun_id * (list label)).

(* The different kinds of middle-end Optimizations passes the profiler wishes to make *)
Inductive middle_wish : Type :=
| AS_INS: expr -> label -> middle_wish.
(* later, we could add constprop, delayed assume insertion and inlining from CoreJIT *)

(* The middle-end optimizations suggestions for the middle-end *)
Parameter middle_end_suggestion: profiler_state -> list (fun_id * middle_wish).


