#!/bin/bash
set -e

echo "-= tests desctiption =-"
function showinfo {
	echo "minify -- no obfuscation"
	echo "!rand -- obfuscation for constant seed"
	echo "rand != !rand-- random seed produces different output"
	echo "lines rand != lines !rand-- random seed produces different amount of lines (has obfuscation lines)"
	echo "exec -- same output"
}
showinfo | column -s '--' -t

echo ""
echo "-= testing =-"

for f in test/*.c
do
	./test1.sh "$f"
done

