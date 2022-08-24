/* Primitives that can be called from the native code */
#include <stdint.h>

int64_t _PRINT (int64_t arg);

int64_t _POP(void);

int64_t _PUSH (int64_t arg);

int64_t _CLOSE (int64_t caller, int64_t cont, int64_t retreg);

int64_t _SET (int64_t addr, int64_t val);

int64_t _GET (int64_t addr);
