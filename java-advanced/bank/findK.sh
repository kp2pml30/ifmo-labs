#!/bin/bash

set -e
SRCDIR=$(readlink -f .)
CLASSMODULEPATH="$SRCDIR"
while true
do
	if [ -d "$CLASSMODULEPATH/java-advanced-2021" ]
	then
		break
	fi
	if [ "$CLASSMODULEPATH" == "/" ]
	then
		echo "can't find java-advanced-2021, specify classpath"
		exit 1
	fi
	CLASSMODULEPATH="$CLASSMODULEPATH/.."
	CLASSMODULEPATH=$(readlink -f $CLASSMODULEPATH)
done
KORN="$CLASSMODULEPATH"
echo "found at $KORN"

function join() {
	local IFS=$1
	shift
	echo "$*"
}

JARS=$(join ':' $(find "$KORN" -name '*.jar'))
