MLML_ROOT="$(dirname "$(realpath "${BASH_SOURCE[0]:-$0}")")"

# Check if current directory is in PYTHONPATH and add if not
if [[ ":$PYTHONPATH:" != *":$MLML_ROOT:"* ]]; then
    export PYTHONPATH="$PYTHONPATH:$MLML_ROOT"
fi

# Add contrib/Isa-Mini so IsaMini_AoA is importable
if [[ ":$PYTHONPATH:" != *":$MLML_ROOT/contrib/Isa-Mini:"* ]]; then
    export PYTHONPATH="$PYTHONPATH:$MLML_ROOT/contrib/Isa-Mini"
fi

# Ensure Isabelle is the first entry in PATH
if [[ "$PATH" != "$MLML_ROOT/contrib/Isabelle2024/bin"* ]]; then
    # Remove Isabelle from current PATH if it exists
    PATH=$(echo "$PATH" | sed "s|:$MLML_ROOT/contrib/Isabelle2024/bin||g")
    # Add Isabelle as the first entry
    export PATH="$MLML_ROOT/contrib/Isabelle2024/bin:$PATH"
fi

export CVC5_SOLVER=$MLML_ROOT/contrib/cvc5-Linux-x86_64-static-gpl/bin/cvc5
export LEO3_HOME=$MLML_ROOT/contrib
