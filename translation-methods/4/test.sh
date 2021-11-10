#!/bin/bash

cabal build ygrammar
cat task2/grammar.ypar | cabal -v0 run ygrammar > task2/Par.hs
cabal run test2
