/* Primitives for the JIT heap */
#include <stdint.h>

struct JITheap;

/* Initializes the JIT heap */
void init_heap (void);

/* Sets a value in the heap */
void heap_set (int64_t addr, int64_t val);

/* Gets a value in the heap */
int64_t heap_get (int64_t addr);

/* Frees the allocated JIT heap */
void free_heap(void);
