#!/bin/bash
cd build/output
java -cp solution.jar rmi.Client "$@"
