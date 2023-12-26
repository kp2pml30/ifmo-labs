set -x
for i in "./main.smv" "./main.3.smv"
do
    echo "!!!!!!!!!!!!!!!!!!!!!!!"
    nuXmv -int <<-EOF
        read_model -i $i
        go
        build_model
        check_ltlspec
        quit
EOF
done
# go_msat
