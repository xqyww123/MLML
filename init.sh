#!/bin/bash
set -e

echo "Initializing system..."
git pull
git submodule update --init --recursive --remote
pip install -q gdown
pip install -q isarepl --upgrade
mkdir -p ./cache/downloads
mkdir -p ./translation/results
mkdir -p ./cache/translation/tmp

source ./envir.sh

if [ ! -d "./contrib/Isabelle2024" ] || [ ! -d "./contrib/afp-2025-02-12" ]; then
    echo "Downloading Isabelle2024 and AFP"
    gdown --fuzzy https://drive.google.com/file/d/176tufd_eHxzpAHdVV5-XMJSRy8NVaGq9/view?usp=sharing -O ./cache/downloads/Isabelle2024_and_afp-2025-02-12.tar.gz
    echo "Unpacking Isabelle2024 and AFP"
    tar -xzf ./cache/downloads/Isabelle2024_and_afp-2025-02-12.tar.gz -C ./contrib
fi

rm -f  $(isabelle getenv -b ISABELLE_HOME_USER)/etc/components 2>/dev/null
isabelle components -u ./contrib/afp-2025-02-12/thys || exit 1
isabelle components -u ./contrib/Isa-REPL || exit 1
isabelle components -u ./contrib/Isa-Mini || exit 1
isabelle components -u ./contrib/auto_sledgehammer || exit 1

isabelle ocaml_setup
isabelle ghc_setup

echo "System initialized"
