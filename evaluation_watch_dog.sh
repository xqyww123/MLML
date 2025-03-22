#!/bin/bash

BASE_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

while true; do
    $BASE_DIR/evaluation/lib_test.py "$@"
    exit_status=$?

    if [ $exit_status -eq 0 ]; then
        break
    fi

    echo "The evaluator crahses with code $exit_status. Now rebooting it..."
    sleep 1
done

echo "Evaluation finished!"

