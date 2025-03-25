#!/bin/bash
./init.sh

source envir.sh
rm -f  $(isabelle getenv -b ISABELLE_HOME_USER)/etc/components 2>/dev/null
isabelle components -u ./contrib/afp-2025-02-12/thys

NPROC=$(nproc)

isabelle components -u ./tools/Build_AFP_Image/AFP-DEP1
echo "Building AFP-DEP1. This can take 30+ hours"
isabelle build -b -o threads=$NPROC AFP-DEP1

