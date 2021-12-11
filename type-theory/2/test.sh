#!/bin/bash

set -e

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

cabal build

failed=""

function test {
	tmpfile=$(mktemp /tmp/lab2.XXXXXX)
	trap "rm $tmpfile" EXIT
	for i in $1
	do
		res=$(cat $i | cabal -v0 run 2> "$tmpfile")
		printf "%s\t" "$i"
		if [[ "$res" == *"$2"* ]]
		then
			printf "${GREEN}ok${NC}\n"
		else
			printf "${RED}failed${NC}\n"
			failed="$i $failed"
		fi
		err=$(cat "$tmpfile")
		if [[ ! "$err" == '' ]]
		then
			printf "\t%s\n" "$err"
		fi
	done
}

test 'test/*.corr' 'Correct'
test 'test/*.incr' 'Incorrect'

if [[ "$failed" == "" ]]
then
	echo "[OK]"
else
	echo "[FAIL]"
	printf '\t%s\n' "$failed"
	exit 1
fi
