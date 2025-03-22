#!/bin/bash

if [ $# -ne 1 ]; then
    echo "Usage: $0 <the number of tasks>"
    exit 1
fi

number=$1

# Create tasks directory if it doesn't exist
mkdir -p ./translation/tasks

# Get total number of lines
total_lines=$(wc -l < "./translation/targets")

# Calculate lines per part (rounded up)
lines_per_part=$(( (total_lines + number - 1) / number ))

# Split the file with numerical suffixes
split -l "$lines_per_part" -d "./translation/targets" "./translation/tasks/targets."

