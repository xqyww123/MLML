# Check if current directory is in PYTHONPATH and add if not
if [[ ":$PYTHONPATH:" != *":$(pwd):"* ]]; then
    export PYTHONPATH="$PYTHONPATH:$(pwd)"
fi

# Ensure Isabelle is the first entry in PATH
if [[ "$PATH" != "$(pwd)/contrib/Isabelle2024/bin"* ]]; then
    # Remove Isabelle from current PATH if it exists
    PATH=$(echo "$PATH" | sed "s|:$(pwd)/contrib/Isabelle2024/bin||g")
    # Add Isabelle as the first entry
    export PATH="$(pwd)/contrib/Isabelle2024/bin:$PATH"
fi

export CVC5_SOLVER=$(pwd)/contrib/cvc5-Linux-x86_64-static-gpl/bin/cvc5
export LEO3_HOME=$(pwd)/contrib
