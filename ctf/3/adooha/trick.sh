set -e
export LD_PRELOAD="$(readlink -f ./libmy.so)"
gcc my.c -g -fpic -shared -o libmy.so
gdb adooha64.elf
