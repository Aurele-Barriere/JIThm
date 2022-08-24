#!/bin/bash
# This linker replaces calls to primitives by call to their addresses
# We do indirect calls because this is a 64bit address we're calling
# We use %rax because its value will be replaced with the return value of the call

# 1st argument: the .s file to link
# 2nd argument: address for the $400 call (SAVE)
# 3rd argument: address for the $401 call (LOAD)
# 4th argument: address for the $402 call (MEMSET)
# 5th argument: address for the $403 call (MEMGET)
# 6th argument: address for the $404 call (CLOSE)
# 7th argument: address for the $405 call (PRINT)

sed -e 's/call\t\$400/mov\t$'$2', %rax\n\tcall\t*%rax/g' \
-e 's/call\t\$401/mov\t$'$3', %rax\n\tcall\t*%rax/g' \
-e 's/call\t\$402/mov\t$'$4', %rax\n\tcall\t*%rax/g' \
-e 's/call\t\$403/mov\t$'$5', %rax\n\tcall\t*%rax/g' \
-e 's/call\t\$404/mov\t$'$6', %rax\n\tcall\t*%rax/g' \
-e 's/call\t\$405/mov\t$'$7', %rax\n\tcall\t*%rax/g' \
$1 > linked.s
