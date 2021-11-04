set -e
export LD_PRELOAD="$(readlink -f ./libmy.so)"
g++ my.cpp --std=c++2a -O3 -fpic -shared -o libmy.so
gdb basic.elf
