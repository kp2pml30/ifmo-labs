#!/bin/bash
source findK.sh

# echo running javac -g -cp "$JARS" ./*.java -d build

javac -g -cp "$JARS" ./*.java -d build
cd build
mkdir -p output
jar -cvf output/solution.jar rmi > /dev/null
#rmic -d $CLASSPATH examples.rmi.RemoteAccount examples.rmi.RemoteBank
