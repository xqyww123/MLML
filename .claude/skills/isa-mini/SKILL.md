---
name: isa-mini
description: Locate and understand the Isa-Mini project providing simplified AI-friendly proof language in contrib/Isa-Mini
---

# Isa-Mini Project

Isa-Mini provides a minimal, AI-friendly proof language (Minilang) that simplifies Isabelle's complex Isar language. It reduces dozens of proof commands to few essential ones, using Sledgehammer for automation. Designed for machine learning agents to generate proofs more easily.

## Project Location

**Path:** `contrib/Isa-Mini`

## Directory Structure

### `contrib/Isa-Mini/IsaMini/` - Python Package
The Python side of Minilang (importable as `IsaMini`):
- `__init__.py` - Package initialization
- `main.py` - Command-line interface
- `REPL.py` - Python client wrapping IsaREPL
- `AoA/` - the **AoA (All over Abstraction) agent framework** (see below)

### `contrib/Isa-Mini/IsaMini/AoA/` - AoA Agent Framework
The live AI-agent framework that drives Minilang proofs (planner + worker sub-agents):
- `model.py` - core: proof tree, nodes, `Session`/`Role`, `Minilang_State`, rendering
- `toplevel.py` - RPC entry `IsaMini.AoA`, caching, test dispatch
- `mcp_http_server.py` - MCP server + tool→operation logic
- `language_model_driver.py`, `driver_*.py` - driver base + concrete drivers (`driver_claude_code.py` is default)
- `test.py` + `Tests/` - test framework and golden YAMLs; runner is `../../test_AoA.py`
- `docs/DEVELOP.md` - **AoA developer guide** (architecture, status semantics, gotchas)

> For working *on* AoA, read `IsaMini/AoA/CLAUDE.md` (auto-loaded when working in that directory) and the longer-form `IsaMini/AoA/docs/DEVELOP.md`.
> (Note: the stray top-level `IsaMini_AoA/` is NOT the live code — only `IsaMini/AoA/` is.)

### `contrib/Isa-Mini/library/` - Core ML Implementation
Isabelle/ML implementation of Minilang:
- `proof.ML` - Proof state machine implementation
- `aux.ML` - Auxiliary functions and utilities

### `contrib/Isa-Mini/REPL/` - Integration with Isa-REPL
REPL interface for Minilang:
- `Minilang_Top.thy` - Top-level integration theory
- Connects Minilang with Isa-REPL communication infrastructure

### `contrib/Isa-Mini/Agent/` - Agent Framework (Isabelle/ML side)
The ML wiring that exposes AoA to Isabelle:
- `Minilang_Agent.thy` - defines the `by aoa` proof method (`method_setup aoa`)
- `agent_server.ML` - the `IsaMini.AoA` RPC command, ML↔Python callbacks, Isa-REPL app registration

### `contrib/Isa-Mini/translator/` - Isar-to-Minilang Translator
Tools for translating Isar proofs to Minilang:
- `translator.py` - Main translation script
- Successfully translated ~260K proofs from AFP (Archive of Formal Proofs)

### `contrib/Isa-Mini/Test/` - Test Theories
Test cases and example theories

### `contrib/Isa-Mini/doc/` - Documentation
- `Readme.md` - Project overview and getting started
- `Language and Protocol.md` - Detailed Minilang language specification and protocol

## Key Files

### Entry Points
- **`Minilang.thy`** - Core language theory defining attributes (OF, of, where)
- **`Minilang_Base.thy`** - Base definitions and setup
- **`REPL/Minilang_Top.thy`** - REPL integration entry point

### Python Interface
- **`IsaMini/REPL.py`** - Python client API (wraps IsaREPL)
- **`IsaMini/main.py`** - CLI tool for running Minilang
- **`IsaMini/AoA/`** - AoA agent framework (see its `CLAUDE.md`)

### ML Core
- **`library/proof.ML`** - Proof state machine and command implementation
- **`library/aux.ML`** - Helper functions

### Translation
- **`translator.py`** - Isar-to-Minilang translator

## Minilang Commands

Simplified proof commands (see `doc/Language and Protocol.md` for details):

### Proof Structure
- **`GOAL`** - Start a proof
- **`NEXT`** - Move to next subgoal, apply Sledgehammer if the goal unproven yet
- **`END`** - Close proof block, apply Sledgehammer if the goal unproven yet

### Proof Steps
- **`INTRO`** - Introduce variables/assumptions
- **`HAVE`** - Prove intermediate fact
- **`OBTAIN`** - Existential elimination
- **`LET`** - Local syntactic abbreviation

### Tactics
- **`CRUSH`** - Automatic solving with Isabelle's auto
- **`APPLY`** - Apply tactics
- **`SIMP`** - Simplification
- **`UNFOLD`** - Unfold definitions

### Structural
- **`INDUCT`** - Induction
- **`CASE_SPLIT`** - Case analysis

## Relationship with Other Projects

- Depends on Isa-REPL

## Documentation

For detailed language specification and usage:
- **`doc/Readme.md`** - Getting started guide
- **`doc/Language and Protocol.md`** - Complete language reference and protocol specification
- **Example theories** - Check `Test/` directory for test cases
- **Translation examples** - See `translator/` for Isar-to-Minilang conversion

## Finding Your Way

### To understand implementation:
- Read `library/proof.ML` for proof state machine
- Check `library/aux.ML` for helper functions
- See `REPL/Minilang_Top.thy` for REPL integration

### To translate existing Isar proofs:
- Use `translator.py` for Isar-to-Minilang conversion
- Check `translator/` directory for tools and utilities

### To develop agents:
- The live agent framework is `IsaMini/AoA/` (Python). Read `IsaMini/AoA/CLAUDE.md` (auto-loaded in that directory) and `IsaMini/AoA/docs/DEVELOP.md`.
- `Agent/` holds the Isabelle/ML side (`Minilang_Agent.thy` for `by aoa`, `agent_server.ML` for the RPC bridge).
- Review `IsaMini/AoA/test.py` + `test_AoA.py` for the test framework and usage examples.
