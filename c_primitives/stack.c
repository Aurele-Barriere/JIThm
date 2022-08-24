#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include "stack.h"


#define STACK_SIZE 10000
#define EMPTY 0
#define IR_ID 1
#define NAT_ID 2

/* Creating and initializing Global stack */
struct JITstack {  
  int64_t stack[STACK_SIZE];
  int sp;
};				/* just a counter for now */

/* The global stack used by these primitives */
static struct JITstack * jit_stack = NULL;

void init_stack() {
  struct JITstack *stk = malloc (sizeof(struct JITstack));
  stk->sp = 0;
  stk->stack[0] = EMPTY;
  jit_stack = stk;
  return;
}

void stack_push(int64_t arg) {
  int sp = (jit_stack->sp) + 1;
  jit_stack->stack[sp] = arg;
  jit_stack->sp = sp;
  return;
}

int64_t stack_pop() {
  int sp = (jit_stack->sp);
  int64_t val = jit_stack->stack[sp];
  jit_stack->sp = sp - 1;
  return val;
}

void push_ir_sf() {
  stack_push(IR_ID);
  return;
}

void close_sf(int64_t caller, int64_t cont, int64_t retreg) {
  stack_push(retreg);
  stack_push(cont);
  stack_push(caller);
  stack_push(NAT_ID);
  return;
}

void print_stack() {
  int sp = jit_stack->sp;
  printf ("STACK POINTER: %d\n", sp);
  fflush(stdout);
}

void free_stack() {
  free(jit_stack);
  jit_stack = NULL;
  return;
}
