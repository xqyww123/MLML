#!/bin/bash
./init.sh

PATH=./contrib/Isabelle2024/bin:$PATH
rm -f  $(isabelle getenv -b ISABELLE_HOME_USER)/etc/components 2>/dev/null
isabelle components -u ./contrib/afp-2025-02-12/thys

NPROC=$(nproc)

echo "Building AFP-DEP1. This can take 30+ hours"
export ISABELLE_TOOL_JAVA_OPTIONS="-Xms4g -Xmx32g -Xss16m"
isabelle build -b -D ./tools/Build_AFP_Image/AFP-DEP1 -o threads=$NPROC AFP-DEP1

