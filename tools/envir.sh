# Check if current directory is in PYTHONPATH and add if not
if [[ ":$PYTHONPATH:" != *":$(pwd):"* ]]; then
    export PYTHONPATH="$PYTHONPATH:$(pwd)"
fi