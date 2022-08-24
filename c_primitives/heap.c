#include <stdlib.h>
#include <assert.h>
#include "heap.h"

#define HEAP_SIZE 1000000

struct JITheap {
  int64_t heap[HEAP_SIZE];
};

/* The global heap used by these primitives */
static struct JITheap * jit_heap = NULL;

void init_heap () {
  struct JITheap *hp = malloc (sizeof(struct JITheap));
  jit_heap = hp;
  return;
}

void heap_set (int64_t addr, int64_t val) {
  assert (addr < HEAP_SIZE);
  jit_heap->heap[addr] = val;
  return;
}

int64_t heap_get (int64_t addr) {
  assert (addr < HEAP_SIZE);
  int64_t val = jit_heap->heap[addr];
  return val;
}


void free_heap() {
  free(jit_heap);
  jit_heap = NULL;
}
