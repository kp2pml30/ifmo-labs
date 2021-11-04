#!/bin/bash
set -e
# g++ my.cpp -m32 --std=c++2a -O3 -fpic -shared -o libmy.so
# export LD_PRELOAD="$(readlink -f ./libmy.so)"
gdb-multiarch cube.elf
