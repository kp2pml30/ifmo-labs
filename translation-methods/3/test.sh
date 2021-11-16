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

# SCRIPT_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
SCRIPT_DIR="$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"

for f in $(find "$SCRIPT_DIR/test/" -name '*.c')
do
	"$SCRIPT_DIR/test1.sh" "$f"
done

