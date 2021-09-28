#!/bin/bash
cd build
source ../findK.sh

if ! pgrep -x "rmiregistry" > /dev/null
then
	echo "no registry found"
	nohup rmiregistry -J-Djava.class.path=solution.jar &
	serverPID=$!
fi

echo "rmiregistry started"

JARS=$JARS:$(readlink -f .)/output/solution.jar

java -cp "$JARS" rmi.TestRunner
echo "exitcode :: $?"

if ! [ -z ${serverPID+x} ]
then
	echo "killing rmiregistry..."
	kill $serverPID
fi
