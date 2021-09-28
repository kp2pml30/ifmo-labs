#!/bin/bash
set -e
shopt -s nullglob

JARNAME="info.kgeorgiy.ja.prokopenko.implementor.jar"

help() {
	echo -e "help for ${BASH_SOURCE[0]}"
	echo -e "cd into directory where you plan to leave that jar. if it is a final destination run with (jar), otherwise run (jar-there)"
	echo -e '\tdoc <classpath>\t-- generate docs'
	echo -e '\tjar <classpath>\t-- create jar to be placed into same dir'
	echo -e '\tjar-abs\t-- create jar to place anywhere (absolute classpaths)'
	echo -e '\trun <classpath> <fw-args>\t-- run jar'
	echo -e 'where <classpath> is a ':' separeted list of *directories* with all external jars'
	exit 2
}
if [ $# \< 1 ]; then
	help
fi

ACTION="$1"
shift

splitpath() {
	local IFS=:
	local foo
	set -f
	foo=( $@ )
	set +f
	#printf '%d\n' "${#foo[@]}"
	printf '%s\n' "${foo[@]}"
}

jarinplace() {
	local ret=""
	for line in $(splitpath "$2")
	do
		ret="$ret\n  $($1 $line)"
	done
	echo "$ret"
}

SRCDIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" &> /dev/null && pwd)"
if [ $# \< 1 ] || [ "$1" = "" ]; then
	echo "trying to find java-advanced-2021"
	CLASSMODULEPATH="$SRCDIR"
	while true
	do
		echo "checking $CLASSMODULEPATH"
		if [ -d "$CLASSMODULEPATH/java-advanced-2021" ]
		then
			break
		fi
		if [ "$CLASSMODULEPATH" == "/" ]
		then
			echo "can't find java-advanced-2021, specify classpath"
			help
		fi
		CLASSMODULEPATH="$CLASSMODULEPATH/.."
		CLASSMODULEPATH=$(readlink -f $CLASSMODULEPATH)
	done
	echo "Found"
	KORN="$CLASSMODULEPATH"
	CLASSMODULEPATH=".:$CLASSMODULEPATH/java-advanced-2021/artifacts:$CLASSMODULEPATH/java-advanced-2021/lib"
	echo "reading classpath from $CLASSMODULEPATH"
else
	KORN="$1"
	CLASSMODULEPATH="$1"
	shift
fi

if [ "$ACTION" = run ]
then
	echo "running..."
	java -cp "$CLASSMODULEPATH" -p "$CLASSMODULEPATH" -m info.kgeorgiy.ja.prokopenko.implementor/info.kgeorgiy.ja.prokopenko.implementor.Implementor "$@"
	exit 0
fi

ALLJARS="."
NEWMP="."
for dir in $(splitpath $CLASSMODULEPATH)
do
	expandeddir="${dir//\~/$HOME}"
	NEWMP="$NEWMP:$expandeddir"
	for jar in $expandeddir/*.jar
	do
		ALLJARS="$ALLJARS:$(readlink -f $jar)"
	done
done

case $ACTION in
doc)
		echo "building javadoc"
		find "$KORN/java-advanced-2021/modules/info.kgeorgiy.java.advanced.implementor" -name '*Impler*.java' -not -name '*Test*' | \
		xargs javadoc -link https://docs.oracle.com/en/java/javase/11/docs/api/ \
			-private \
			-cp "$ALLJARS" \
			-d javadoc \
			-tag "implSpec:a:Implementation Requirements:" \
			"$SRCDIR/info/kgeorgiy/ja/prokopenko/implementor/Implementor.java" \
			"$SRCDIR/info/kgeorgiy/ja/prokopenko/implementor/package-info.java"
	;;
jar|jar-abs)
		BDIR=/tmp/kp2pml30
		BDIREXT=info.kgeorgiy.ja.prokopenko.implementor
		ME=info/kgeorgiy/ja/prokopenko
		echo "compiling to $BDIR"
		mkdir -p "$BDIR/$BDIREXT/$ME"
		cp -r "$SRCDIR/$ME/implementor" "$BDIR/$BDIREXT/$ME"
		cp "$SRCDIR/module-info.java.in" "$BDIR/$BDIREXT/module-info.java"
		javac -d "$BDIR" -p "$NEWMP" -cp "$ALLJARS" --module-source-path "$BDIR" --module $BDIREXT

		echo "making jar"
		cp "$SRCDIR/manifest.in" "$BDIR/manifest"
		if [ "$ACTION" = "jar" ]
		then
			CLASSPATHJAR=$(jarinplace basename "$ALLJARS")
		else
			CLASSPATHJAR=$(jarinplace echo "$ALLJARS")
		fi
		sed -i "s:@CLASSPATH@:$CLASSPATHJAR:" "$BDIR/manifest"
		jar cfm "$JARNAME" "$BDIR/manifest" -C "$BDIR/$BDIREXT" .

		echo "clean up"
		rm -rf "$BDIR"
	;;
*)
	help
esac
echo "done"
