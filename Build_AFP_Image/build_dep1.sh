#!/bin/bash
./init.sh

PATH=./contrib/Isabelle2024/bin:$PATH
rm -f  $(isabelle getenv -b ISABELLE_HOME_USER)/etc/components 2>/dev/null
isabelle components -u ./contrib/afp-2025-02-12/thys

NPROC=$(nproc)

echo "Building AFP-DEP1. This can take 30+ hours"
isabelle build -b -D ./Build_AFP_Image/AFP-DEP1 -o threads=$NPROC AFP-DEP1

