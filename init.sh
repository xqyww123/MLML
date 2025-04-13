#!/bin/bash
set -e

echo "Initializing system..."
git pull
git submodule update --init --recursive --remote
pip install -q gdown sqlitedict
pip install -q isarepl isamini --upgrade
mkdir -p ./cache/downloads
mkdir -p ./translation/results
mkdir -p ./cache/translation/tmp

# Check if md5sum file exists and verify database integrity
if [ -f "./data/md5sum" ]; then
    echo "Verifying database integrity..."
    if md5sum --status -c ./data/md5sum; then
        echo "Database integrity verified."
    else
        echo "Database files are out-of-date. Reinstalling..."
        gunzip -k ./data/translation/declarations.db.gz
        gunzip -k ./data/translation/results.db.gz
        md5sum ./data/translation/declarations.db ./data/translation/results.db > ./data/md5sum
    fi
else
    echo "Unpacking database files..."
    gunzip -k ./data/translation/declarations.db.gz
    gunzip -k ./data/translation/results.db.gz
    md5sum ./data/translation/declarations.db ./data/translation/results.db > ./data/md5sum
fi


source ./envir.sh

# Check if reinstall flag is provided as command line argument
reinstall_isabelle="n"
for arg in "$@"; do
    if [[ "$arg" == "--reinstall" ]]; then
        reinstall_isabelle="y"
    fi
done

if [[ "$reinstall_isabelle" == "y" ]]; then
    echo "Removing existing Isabelle and AFP installations..."
    rm -rf ./contrib/Isabelle2024 ./contrib/afp-2025-02-12
    rm -f ./cache/downloads/Isabelle2024_and_afp-2025-02-12.tar.gz
    if [ -d "$USER/.isabelle/Isabelle2024/heaps" ]; then
        mv $USER/.isabelle/Isabelle2024/heaps $USER/.isabelle/Isabelle2024/heaps.$(date +%Y%m%d%H%M%S)
    fi
    echo "Isabelle and AFP will be reinstalled."
fi


if [ ! -d "./contrib/Isabelle2024" ] || [ ! -d "./contrib/afp-2025-02-12" ]; then
    echo "Downloading Isabelle2024 and AFP"
    gdown --fuzzy https://drive.google.com/file/d/176tufd_eHxzpAHdVV5-XMJSRy8NVaGq9/view?usp=sharing -O ./cache/downloads/Isabelle2024_and_afp-2025-02-12.tar.gz
    echo "Unpacking Isabelle2024 and AFP"
    tar -xzf ./cache/downloads/Isabelle2024_and_afp-2025-02-12.tar.gz -C ./contrib
fi

# Ask user for maximum memory allocation for Isabelle
read -p "Enter memory limit (in GB) for Isabelle (default: 50): " isabelle_memory
isabelle_memory=${isabelle_memory:-50}

# Validate that isabelle_memory is a positive integer and not less than 30
if ! [[ "$isabelle_memory" =~ ^[0-9]+$ ]] || [ "$isabelle_memory" -lt 30 ]; then
    echo "Error: Memory limit must be a positive integer greater or equal than 30GB"
    exit 1
fi

mkdir -p $(isabelle getenv -b ISABELLE_HOME_USER)/etc
printf "ML_OPTIONS='--minheap 4G --maxheap ${isabelle_memory}G'\nML_MAX_HEAP=${isabelle_memory}" > $(isabelle getenv -b ISABELLE_HOME_USER)/etc/settings
echo "Setting Isabelle memory limit to ${isabelle_memory}GB"


rm -f  $(isabelle getenv -b ISABELLE_HOME_USER)/etc/components 2>/dev/null
isabelle components -u ./contrib/afp-2025-02-12/thys || exit 1
isabelle components -u ./contrib/Isa-REPL || exit 1
isabelle components -u ./contrib/Isa-Mini || exit 1
isabelle components -u ./contrib/auto_sledgehammer || exit 1

isabelle ocaml_setup
isabelle ghc_setup

echo "System initialized"
