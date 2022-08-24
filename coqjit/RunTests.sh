#!/bin/bash

echo "Running the JIT, with native code execution"
read -p "Press any key to resume ..."
./jit progs_IR/prime.ir

echo "Now Running the JIT on the same program, but interpretation only"
read -p "Press any key to resume ..."
./jit progs_IR/prime.ir -i
