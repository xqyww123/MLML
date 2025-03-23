#!/bin/bash

git submodule update --init --recursive --remote
pip install -q gdown
mkdir -p ./cache/downloads
mkdir -p ./translation/results

# Check if current directory is in PYTHONPATH and add if not
if [[ ":$PYTHONPATH:" != *":$(pwd):"* ]]; then
    export PYTHONPATH="$PYTHONPATH:$(pwd)"
fi


if [ ! -d "./contrib/Isabelle2024" ]; then
    echo "Downloading Isabelle2024"
    gdown --fuzzy https://drive.google.com/file/d/1-cdF3SZoqtlhWTbqlgMT9h4S5T8LRvLK/view?usp=sharing -O ./cache/downloads/Isabelle2024_linux.tar.gz
    echo "Unpacking Isabelle2024"
    tar -xzf ./cache/downloads/Isabelle2024_linux.tar.gz -C ./contrib
fi

if [ ! -d "./contrib/afp-2025-02-12" ]; then
    echo "Downloading AFP"
    gdown --fuzzy https://drive.google.com/file/d/1_iuUpTg-AsahixhIJkmBOlFGsnzvoovx/view?usp=sharing -O ./cache/downloads/afp-2025-02-12.tar.gz
    echo "Unpacking AFP"
    tar -xzf ./cache/downloads/afp-2025-02-12.tar.gz -C ./contrib
fi

PATH=./contrib/Isabelle2024/bin:$PATH
rm -f  $(isabelle getenv -b ISABELLE_HOME_USER)/etc/components 2>/dev/null
isabelle components -u ./contrib/afp-2025-02-12/thys || exit 1
isabelle components -u ./contrib/Isa-REPL || exit 1
isabelle components -u ./contrib/Isa-Mini || exit 1
isabelle components -u ./contrib/auto_sledgehammer || exit 1

echo "System initialized"
