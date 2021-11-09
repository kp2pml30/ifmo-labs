#!/bin/bash
set -e

function fail {
	echo "$@"
	exit 1
}

DIR="$(mktemp -d)"
if [ "$1" = "--keep" ]
then
	echo "saving to $DIR"
	shift
else
	trap 'rm -rf -- "$DIR"' EXIT
fi

echo "> test $1"

CABAL="cabal -v0 run parser --"

echo "		minify"
awk 'NF' $1 | clang-format > $DIR/nonl.c
cabal -v0 run parser -- --id < $1 | clang-format > $DIR/minified.c
git diff $DIR/nonl.c $DIR/minified.c

echo "		!rand"
$CABAL --no-random < $1 > $DIR/nrand.c
$CABAL --no-random < $DIR/nrand.c > $DIR/nrand2.c
git diff $DIR/nrand.c $DIR/nrand2.c

echo "		rand != !rand"
$CABAL < $1 > $DIR/obf.c
git diff $DIR/nrand.c $DIR/obf.c > /dev/null && fail "	fail: no random" || true

echo "		lines rand != lines !rand"
diff <(clang-format < $DIR/obf.c | wc -l) <(clang-format < $DIR/nrand.c | wc -l) > /dev/null && fail "	fail: same amount of lines" || true

echo "		exec"
GCC="gcc -Wno-implicit-function-declaration -Wno-builtin-declaration-mismatch -Wno-pointer-to-int-cast -Wno-trigraphs -Wno-overflow -m32"
$GCC "$1" -o $DIR/original.o
$GCC $DIR/obf.c -o $DIR/obf.o
diff <($DIR/original.o) <($DIR/obf.o)

echo "	passed"
