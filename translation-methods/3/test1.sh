#!/bin/bash
echo "$1"
set -e

awk 'NF' $1 | clang-format > /tmp/a.c
cabal -v0 run parser -- --id < $1 | clang-format > /tmp/b.c
git diff /tmp/a.c /tmp/b.c
cabal -v0 run parser < $1 > /tmp/b.c
GCC="gcc -Wno-implicit-function-declaration -Wno-builtin-declaration-mismatch"
$GCC /tmp/a.c -o /tmp/a.o
$GCC /tmp/b.c -o /tmp/b.o
diff <(/tmp/a.o) <(/tmp/b.o)
echo "	ok"
