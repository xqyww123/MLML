#!/bin/bash
set -e

echo "Initializing system..."
git pull
git submodule update --init --recursive --remote
git lfs install
git lfs pull
pip install -q sqlitedict
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
        gunzip -f -k ./data/translation/declarations.db.gz
        gunzip -f -k ./data/translation/results.db.gz
        unzstd -f -k data/proof_context.db.zst
        unzstd -f -k data/premise_selection/SH.pretty.db.zst
        md5sum ./data/translation/declarations.db ./data/translation/results.db data/proof_context.db data/premise_selection/SH.pretty.db > ./data/md5sum
    fi
else
    echo "Unpacking database files..."
    gunzip -f -k ./data/translation/declarations.db.gz
    gunzip -f -k ./data/translation/results.db.gz
    unzstd -f -k data/proof_context.db.zst
    unzstd -f -k data/premise_selection/SH.pretty.db.zst
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


if md5sum --status -c ./contrib/Isabelle2024.md5sum; then
    echo "Isabelle2024 is up to date."
else
    echo "Isabelle2024 is out of date. Reinstalling..."
    rm -rf ./contrib/Isabelle2024
    rm -rf ./contrib/afp-2025-02-12
    tar --zstd -xf ./contrib/Isabelle2024_and_afp-2025-02-12.tar.zst -C ./contrib
    echo "Isabelle2024 and AFP reinstalled."
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


#rm -f  $(isabelle getenv -b ISABELLE_HOME_USER)/etc/components 2>/dev/null
isabelle components -u . || exit 1

isabelle ocaml_setup || echo "Fail to activate OCaml support for Isabelle. Some files may fail to be evaluated"
isabelle ghc_setup || echo "Fail to activate GHC support for Isabelle. Some files may fail to be evaluated"

echo "System initialized"
