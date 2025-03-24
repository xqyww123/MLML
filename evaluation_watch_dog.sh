#!/bin/bash

source ./tools/envir.sh

BASE_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

while true; do
    $BASE_DIR/evaluation/evaluator.py "$@"
    exit_status=$?

    if [ $exit_status -eq 0 ]; then
        break
    fi

    echo "The evaluator crahses with code $exit_status. Now rebooting it..."
    sleep 1
done

echo "Evaluation finished!"

