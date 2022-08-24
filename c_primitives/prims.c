#include <stdio.h>
#include <stdint.h>
#include "stack.h"
#include "heap.h"
#include "prims.h"

#define OUTPUT "\x1B[36m"
#define RESET  "\x1B[0m"

/* PRIMITIVES */
/* Called by the dynamically generated native code */
int64_t _PRINT (int64_t arg) {
  printf (OUTPUT "NATIVE OUTPUT: " RESET "%ld\n", arg);
  return 0;
}

int64_t _POP() {
  int64_t val = stack_pop();
  return val;
}

int64_t _PUSH (int64_t arg) {
  stack_push(arg);
  return 0;
}

int64_t _CLOSE (int64_t caller, int64_t cont, int64_t retreg) {
  close_sf(caller, cont, retreg);
  return 0;
}

int64_t _SET (int64_t addr, int64_t val) {
  heap_set (addr, val);
  return 0;
}

int64_t _GET (int64_t addr) {
  int64_t val = heap_get (addr);
  return val;
}

