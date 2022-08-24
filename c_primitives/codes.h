#include <stdint.h>

/* Type of the Jitted functions */
typedef int64_t (*JittedFunc)();

/* Links the file at "tmp.s" into "linked.s"
   Assembles it into "linked.o"
   Installs it into memory & make executable
   Returns the corresponding function pointer */
JittedFunc link_assemble_and_install(void);

/* Runs the code installed at address func */
int64_t run_code (JittedFunc func);
