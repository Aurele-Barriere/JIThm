/* Primitives for the JIT stack */
/* This doesn't include the IR stackframes themselves, in another OCaml stack */
#include <stdint.h>

struct JITstack;

/* Initializes the JIT stack */
void init_stack(void);

/* Pushes a value on top of the stack */
void stack_push(int64_t arg);

/* Pops the top value of the stack */
int64_t stack_pop(void);

/* Pushes an IR stackframe Identifier */
void push_ir_sf(void);

/* Closes a Native stackframe */
void close_sf(int64_t caller, int64_t cont, int64_t retreg);

/* Frees the allocated JIT stack */
void free_stack(void);

/* For now, only prints the sp */
void print_stack(void);
