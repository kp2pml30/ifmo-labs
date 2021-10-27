#!/bin/bash
cabal -v0 run parser | clang-format
