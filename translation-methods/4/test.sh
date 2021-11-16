#!/bin/bash

cabal build ygrammar

cat task2/grammar.ypar | cabal -v0 run ygrammar > task2/Par.hs
cabal run test2

cat task3/grammar.ypar | cabal -v0 run ygrammar > task3/Obfuscation/ParGen.hs
cabal build task3
export CABAL="cabal -v0 run task3 --"
task3/test.sh
