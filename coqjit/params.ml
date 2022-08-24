(* Realizing a JIT parameters that are not part of the profiler *)
open Datatypes
open BinPos
open BinNums
open Values
open Int64
open Camlcoq

(* don't use on negative numbers *)
let rec make_nat (x:int) : Datatypes.nat =
  if x = 0 then O else S (make_nat (x-1))
   
(* JIT Parameters *)
let max_optim = make_nat 10
let interpreter_fuel = make_nat 100

let mem_size = coqint_of_camlint64 (Int64.of_int 1000000)
