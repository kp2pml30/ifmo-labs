#!/bin/bash
set -e

for f in test/*.c
do
	./test1.sh "$f"
done

