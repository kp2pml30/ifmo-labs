#!/bin/bash
set -e

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
cd "$SCRIPT_DIR"

rm -rf test-build 2> /dev/null || true

mkdir -p test-build

for i in $(find tests -name '*.ts' | sort)
do
    echo "$i"
    fname="$(basename -- "$i")"
    fname="${fname%.*}"
    npx ts-node src/index.ts "$i" "test-build/$fname"
done

for i in $(find test-build -name '*.dot')
do
    dot -Tpng -o"$i.png" "$i"
done
