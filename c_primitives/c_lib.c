#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>		/* to return 64bits integers to OCaml */
#include <string.h>

#include "stack.h"
#include "heap.h"
#include "codes.h"
#include "prims.h"

/* STUBS */
/* For OCaml */
CAMLprim value caml_init_stk (value unit) {
  init_stack();
  return Val_unit;
}

CAMLprim value caml_init_heap (value unit) {
  init_heap();
  return Val_unit;
}

CAMLprim value caml_free_stack (value unit) {
  free_stack ();
  return Val_unit;
}

CAMLprim value caml_free_heap (value unit) {
  free_heap ();
  return Val_unit;
}

CAMLprim value caml_stack_push (value arg) {
  int64_t x = Int64_val (arg);
  stack_push(x);
  return Val_unit;
}

CAMLprim value caml_stack_pop (value unit) {
  int64_t x = stack_pop();
  return caml_copy_int64(x);
}

CAMLprim value caml_push_ir_id (value unit) {
  push_ir_sf();
  return Val_unit;
}

CAMLprim value caml_close_sf (value caller, value cont, value retreg) {
  int64_t ca = Int64_val(caller);
  int64_t co = Int64_val(cont);
  int64_t re = Int64_val(retreg);
  close_sf(ca, co, re);
  return Val_unit;
}

CAMLprim value caml_heap_set (value addr, value val) {
  int64_t ad = Int64_val(addr);
  int64_t va = Int64_val(val);
  heap_set(ad, va);
  return Val_unit;
}

CAMLprim value caml_heap_get (value addr) {
  int64_t ad = Int64_val(addr);
  int64_t res = heap_get(ad);
  return caml_copy_int64(res);
}

CAMLprim value caml_print_stack (value unit) {
  print_stack();
  return Val_unit;
}


CAMLprim value caml_install (value unit) {
  JittedFunc func = link_assemble_and_install();
  int64_t addr = (int64_t) func;
  return caml_copy_int64(addr);
}

CAMLprim value caml_run_code (value addr) {
  int64_t int_addr = Int64_val (addr);
  JittedFunc func = (JittedFunc) int_addr;
  int64_t result = run_code (func);
  return caml_copy_int64(result);
}
