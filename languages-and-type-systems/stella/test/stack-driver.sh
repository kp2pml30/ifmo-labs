#!/bin/bash

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

stack --silent exec --cwd="$SCRIPT_DIR" stella-exe "$@"
