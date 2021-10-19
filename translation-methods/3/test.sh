#!/bin/bash
set -e

function test {
	./test1.sh "test/$1.c"
}

test simple
test adv
test test
