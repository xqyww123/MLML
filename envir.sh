# Check if current directory is in PYTHONPATH and add if not
if [[ ":$PYTHONPATH:" != *":$(pwd):"* ]]; then
    export PYTHONPATH="$PYTHONPATH:$(pwd)"
fi

# Check if Isabelle is not in PATH and add if not
if [[ ":$PATH:" != *":$(pwd)/contrib/Isabelle2024/bin:"* ]]; then
    export PATH="$(pwd)/contrib/Isabelle2024/bin:$PATH"
fi