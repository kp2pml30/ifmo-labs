#!/bin/bash

set -e

cabal build yadagenpar
cabal build yadagenlex

echo "== calculator =="
cat calc/grammar.ylex | cabal -v0 run yadagenlex > calc/Lex.hs
cat calc/grammar.ypar | cabal -v0 run yadagenpar > calc/Par.hs
cabal run testcalc

echo "== inh =="
cat inh/grammar.ylex | cabal -v0 run yadagenlex > inh/Lex.hs
cat inh/grammar.ypar | cabal -v0 run yadagenpar > inh/Par.hs
cabal run testinh

echo "== task2 =="
cat task2/grammar.ylex | cabal -v0 run yadagenlex > task2/Lex.hs
cat task2/grammar.ypar | cabal -v0 run yadagenpar > task2/Par.hs
cabal run test2

echo "== task3 =="
cat task3/grammar.ylex | cabal -v0 run yadagenlex > task3/Obfuscation/Lex.hs
cat task3/grammar.ypar | cabal -v0 run yadagenpar > task3/Obfuscation/ParGen.hs
cabal build task3
export CABAL="cabal -v0 run task3 --"
task3/test.sh

echo "All tests passed [OK]"
