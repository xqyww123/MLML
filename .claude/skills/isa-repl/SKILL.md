---
name: isa-repl
description: Locate and understand the Isa-REPL project providing REPL interface for Isabelle in contrib/Isa-REPL
---

# Isa-REPL Project

Isa-REPL provides a programmatic REPL (Read-Eval-Print-Loop) interface for Isabelle, enabling Python clients to interact with Isabelle over sockets. Designed for machine learning applications and automated theorem proving.

## Project Location

**Path:** `contrib/Isa-REPL`

## Directory Structure

### `contrib/Isa-REPL/IsaREPL/` - Python Client Library
Python client for communicating with Isabelle REPL server:
- `IsaREPL.py` - Main Python client (MessagePack-based communication)
- Socket-based communication protocol
- Session management and state tracking

### `contrib/Isa-REPL/library/` - ML Server Implementation
Core Isabelle/ML server-side components:
- `REPL.ML` - REPL signature and main implementation
- `Server.ML` - Socket server implementation
- `REPL_serializer.ML` - Serialization of Isabelle objects (terms, theorems, states)
- `sledgehammer.ML` - Sledgehammer automation integration
- `premise_selection.ML` - Premise selection support for proof search
- `utils.ML` - Utility functions

### `contrib/Isa-REPL/examples/` - Usage Examples
Example Python scripts demonstrating various REPL features:
- **`example_eval.py`** - Basic REPL usage (evaluating commands)
- **`example_context.py`** - Retrieve proof context (facts, assumptions, fixed variables, goals)
- **`example_parse.py`** - Parse terms and retrieve lemmas
- **`example_lex.py`** - Split scripts into command sequences (lexical analysis)
- **`example_plugin.py`** - Install/uninstall plugins to access Isabelle internals
- **`example_rollback.py`** - State rollback and history management
- **`example_sledgehammer.py`** - Use Sledgehammer for automated proving
- **`example_watcher.py`** - Monitor client status (alive/errors)
- **`example_pretty_unicode.py`** - Unicode/ASCII symbol conversion
- **`eval_file.py`** - Evaluate entire theory files
- **`test_file.py`** - Evaluate theory files with error checking
- **`lex_file.py`** - Lexical analysis of files
- **`parse_thy_header.py`** - Parse theory headers (imports, keywords)
- **`path_of.py`** - Get file path of a theory
- **`session_of.py`** - Get session name of a file
- **`premise_selection.py`** - Premise selection for proof search

### `contrib/Isa-REPL/tools/` - Utilities
- Unicode/ASCII conversion tools for Isabelle symbols

### `contrib/Isa-REPL/contrib/mlmsgpack/` - Serialization
MessagePack library for ML (binary serialization format)

## Key Files

### Entry Point
- **`Isa_REPL.thy`** - Main theory file loading all ML components
- **`repl_server.sh`** - Shell script to start REPL server

### Python Interface
- **`IsaREPL/IsaREPL.py`** - Client API for sending commands and receiving results

### ML Core
- **`library/REPL.ML`** - Core REPL logic, command execution, state management

## Usage Pattern

1. **Start server:** Run `repl_server.sh` to launch Isabelle REPL server
2. **Connect from Python:** Use `IsaREPL.Client` to connect

## Common Use Cases

For concrete usage examples, see the scripts in `contrib/Isa-REPL/examples/`:
- **Basic REPL usage:** Start with `example_eval.py`
- **Data collection for ML:** Use `example_context.py` and `example_plugin.py` to extract proof state and internal data
- **Automated theorem proving:** See `example_sledgehammer.py` for Sledgehammer integration
- **Theory file evaluation:** Use `eval_file.py` or `test_file.py` to process complete theory files
- **State management:** Check `example_rollback.py` for state rollback and checkpointing
- **Parsing and analysis:** Use `example_parse.py`, `example_lex.py`, and `parse_thy_header.py`

## Finding Your Way

### To understand the protocol:
- Read `IsaREPL/IsaREPL.py` (Python client)
- Check `library/REPL.ML` (ML server)

### To extend functionality:
- Add ML functions in `library/`
- Create plugins for custom data extraction
- Modify `Isa_REPL.thy` to load new ML files

### To debug:
- Check server logs from `repl_server.sh`
- Enable debug mode in Python client
- Trace ML execution in `library/REPL.ML`
