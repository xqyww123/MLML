#!/bin/bash

host=$1
numprocs=$2
port1=6666
port2=7777

set -e
mkdir -p ./cache/repl_tmps/${host}_${port1}
mkdir -p ./cache/repl_tmps/${host}_${port2}
source ./envir.sh
fuser -n tcp -k $port1 || true
fuser -n tcp -k $port2 || true

# Make cache directory path absolute
dir1="$(realpath ./cache/repl_tmps/${host}_${port1})"
dir2="$(realpath ./cache/repl_tmps/${host}_${port2})"

./contrib/Isa-REPL/repl_server.sh 0.0.0.0:$port1 AFP-1-PISA $dir1 -o threads=$numprocs > $dir1/log.txt 2>&1 &
./contrib/Isa-REPL/repl_server.sh 0.0.0.0:$port2 AFP-1-PISA $dir2 -o threads=$numprocs > $dir2/log.txt 2>&1 &

wait -n