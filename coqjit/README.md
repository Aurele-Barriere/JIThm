# Coq Development for Formally Verified Native Code Generation in an Effectful JIT Compiler

This directory contains the Coq development presented in the submission.

## Contents
- this `coqjit` directory contains the code and proofs that has been written for the JIT compiler
- files ending in `_proof.v` contain the various proofs presented in the submission
- `../c_primitives` is the C library of primitive implementations
- `compcert_coq` is taken as is from CompCert 3.8. Coq definitions and proofs
- `compcert_ocaml` is similarly the OCaml development from the same CompCert 3.8
- `flocq` and `MenhirLib` are Coq libraries, also from CompCert 3.8
- `parsing` contains a custom unverified parser for this version of CoreIR
- `progs_IR` contains a few example CoreIR programs, that can be parsed and executed


## Requirements
- coq 8.15.2 
- coqdep
- menhir 20220210
- ocaml 4.14.0
- ocamlbuild 0.14.1
- CompCert 3.11. Installed in such a way that it can be invoked using the `ccomp` command. This is used to compile the C library
- bash and sed
- This requires an x86-64 compatible machine, as the code we generate is specialized to that architecture


## Usage
Put yourself in the `coqjit` directory (for now, it only works from there).
Run `make`. It should compile the Coq definitions (interleaved with the CompCert ones). Then extract the Coq code to an `extraction` folder. Then build the OCaml JIT in a `_build` folder, and creating a `jit` executable. Then build the Coq proofs.

Note: there will be warnings during compilation, because we reuse some of the names already used in CompCert for our custom libraries (inspired by the CompCert ones, but changing by very little bits). 

You can now run the JIT with:
`./jit progs_IR/prime.ir` for instance.

Compare that execution to a similar one that only uses the interpreter:
`./jit progs_IR/prime.ir -i`

These two commands can also be run by typing `./RunTests.sh`.

The complete list of JIT options can be seen by typing `./jit -help`.

## Renamings
A few things have different names between the submission and the development.
We list them here:

- Monad specifications are called monad implementations (eg `monad_impl`)
- Reference specification is called `naive_impl`
- Primitive specification `prim_spec` is called `array_impl`
- Theorem `jit_correctness_simulation` is `jit_correctness_array`
- Theorem `jit_correctness` is `jit_preservation_array`
- `CoreIR_sem` is `input_sem`
- `Prim_Pop` and `Prim_Push` are `Prim_Save` and `Prim_Load`
- `Prim_HeapSet` and `Prim_HeapGet` are `Prim_MemSet` and `Prim_MemGet`
- `get_prim` is `exec_prim`
- `free_to_state` is `exec`
- `start_` and `end_` are `load_` and `return_`
- `free_interpreter` is `nm_exec`

The three axioms discussed in the submission are 
- `no_builtin` in `backend_proof.v`
- `ext_prim_axiom` in `primitives.v`
- `external_in_memory` in `flattenRTL_proof.v`

Other axioms that may appear during a `Print Assumptions` are either parameters realized during extraction, or axioms from the CompCert development.
