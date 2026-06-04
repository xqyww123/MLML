---
name: isabelle-ML
description: Essential reference for all Isabelle/ML development — system library, data structures, exception handling, and coding patterns. Load this skill whenever writing or modifying Isabelle/ML code.
---

# Isabelle/ML System Library (Pure)

**System Library Location:** contrib/Isabelle2024/src/Pure

This is the Isabelle/ML standard library - analogous to Python's standard library or Java's JDK. All your ML code in this project ultimately depends on and uses components from here.

When writing Isabelle/ML code, the **Pure** directory contains the core system library with all fundamental ML modules, signatures, and structures you need.

## Key Directories for ML Development

### Pure/General/ - General Utilities
Common data structures and utilities:
- table.ML - Efficient tables (maps)
- graph.ML - Graph data structures
- ord_list.ML - Ordered lists
- buffer.ML - Efficient string buffers
- pretty.ML - Pretty printing infrastructure
- position.ML - Source positions for error reporting

### Pure/ML/ - ML Environment
ML compiler integration and environment:
- ml_context.ML - ML compilation context
- ml_antiquotation.ML - Antiquotations in ML

### Pure/ - Core Types and Operations
Fundamental term and theorem manipulation:
- context.ML - **Context infrastructure and data functors** (Theory_Data, Proof_Data, Generic_Data)
- term.ML - **Terms and types** (types, terms, matching, substitution)
- thm.ML - **Theorems** (proof kernel, primitive inferences)
- type.ML - Type operations
- envir.ML - Unification environments
- logic.ML - Meta-logic operations

### Pure/Proof/ - Proof State
Proof state machine and proof construction:
- proof.ML - Proof state structure
- proof_context.ML - Local proof contexts
- variable.ML - Variable naming management and name conflict resolution
- facts.ML - Facts storage and visibility management

### Pure/Isar/ - Theory and Context
Theory infrastructure and command processing:
- local_theory.ML - Local theory targets
- named_target.ML - Named theory targets
- specification.ML - Definitions and specifications
- attrib.ML - Attributes
- method.ML - Proof methods
- proof_display.ML - Proof state display

### Pure/Thy/ - Theory Management
Theory loading and dependencies:
- thy_info.ML - Theory database
- thy_output.ML - Theory output
- export.ML - Theory exports

### Pure/Syntax/ - Parsing and Printing
Syntax processing:
- syntax.ML - Syntax operations

### Pure/Concurrent/ - Concurrency
Thread-safe operations:
- synchronized.ML - Synchronized references
- mailbox.ML - Thread-safe mailboxes
- future.ML - Parallel futures
- counter.ML - Synchronized counter for unique identifiers
- cache.ML - Concurrent value caching with lazy evaluation
- unsynchronized.ML - Raw ML references (unsynchronized state variables)
- isabelle_thread.ML - Isabelle-specific thread management
- lazy.ML - Lazy evaluation with memoization and exception handling
- task_queue.ML - Ordered queue of grouped tasks

### Pure/System/ - System Integration
File system, processes, and I/O:
- isabelle_system.ML - System commands
- bash.ML - Bash script execution
- file.ML - File operations
- path.ML - File paths

## Essential Entry Points

### Pure/ROOT.ML
Bootstrap file that loads all Pure components in the correct order. Read this to understand the loading sequence.

### Pure/Pure.thy
The main theory file defining all Isabelle commands and keywords.

## How to Find What You Need

### Finding ML Signatures
```bash
grep -r "signature [A-Z_]*" contrib/Isabelle2024/src/Pure/*.ML
```

Common signatures: TERM, THM, CONTEXT, PROOF, SYNTAX, TYPE

### Finding ML Structures
```bash
grep -r "structure [A-Z][a-z_]* *:" contrib/Isabelle2024/src/Pure/*.ML
```

Common structures: Term, Thm, Context, Proof, Syntax, Type

### Understanding a Module
1. Look for the `signature` definition first
2. Find the corresponding `structure` implementation
3. Check usage examples in `Pure/` or your project's ML code

## Common Use Cases

### Working with Terms
- **Location:** Pure/term.ML
- **Signatures:** TERM, TYPE
- Functions: Term.map_types, Term.add_vars, Term.subst_atomic

### Manipulating Theorems
- **Location:** Pure/thm.ML
- **Signature:** THM
- Functions: Thm.assume, Thm.implies_elim, Thm.forall_intr

### Context Operations
- **Location:** Pure/context.ML, Pure/Proof/proof_context.ML, Pure/Proof/variable.ML, Pure/Proof/facts.ML
- **Signature:** CONTEXT, PROOF_CONTEXT, VARIABLE, FACTS
- Functions: Proof_Context.read_term_pattern, Context.proof_of, Variable.import, Facts.retrieve

### Facts Access
- `Proof_Context.facts_of : Proof.context -> Facts.T` — all facts visible in the context (local + global + ancestors)
- `Global_Theory.facts_of : theory -> Facts.T` — global facts of a theory and its ancestors (no local facts)
- `Facts.dest_static : bool -> Facts.T list -> Facts.T -> (string * thm list) list` — enumerate facts, excluding those in the parent Facts.T list

### Parsing Terms and Props
- **Location:** Pure/Syntax/syntax.ML
- **Signature:** SYNTAX
- Functions: Syntax.read_term, Syntax.read_prop, Syntax.read_terms, Syntax.read_props, Syntax.parse_term, Syntax.check_term, Syntax.check_terms

**Batch Parsing:** When reading multiple terms or props, prefer using Syntax.read_terms or Syntax.read_props over repeatedly calling the singular versions. These batch functions parse all frees and variables together in one context, ensuring that identical variables are parsed with consistent types across all terms/props.

**read_term vs read_prop:** When given a boolean expression, Syntax.read_prop automatically wraps it with HOL.Trueprop, ensuring the result is a prop-typed term suitable for theorems. Syntax.read_term leaves the expression as-is with type bool.

**Parsing Pipeline - parse_term and check_term:**
- Syntax.read_term equals Syntax.parse_term first then Syntax.check_term
- Syntax.parse_term parses syntax without type checking, produces terms with potentially incomplete type information
- Syntax.check_term performs type inference and type checking on parsed terms
- Syntax.check_terms: Batch version for checking multiple terms together, ensuring consistent variable types
- Type wildcards: Syntax.check_term accepts Term.dummyT as a type wildcard and automatically infers it

### Reading Schematic Patterns (for Pattern.matches)

`Proof_Context.read_term_pattern` reads terms in "pattern mode" where term-level identifiers become **Frees** (not Vars) and type variables become **TFrees** (not TVars). This is NOT directly usable with `Pattern.matches`, which requires schematic Vars/TVars.

To produce fully schematic patterns, replicate what `Simplifier.make_simproc` does (simplifier.ML:130-137):

```sml
fun read_schematic_pat ctxt s =
  let
    val t = Proof_Context.read_term_pattern ctxt s
    val ctxt' = Proof_Context.augment t ctxt
    val [t'] = Variable.export_terms ctxt' ctxt [t]
  in t' end
```

**How it works:**
1. `read_term_pattern` parses the string, producing Frees (`Free ("x", TFree ("'a", ...))`)
2. `Proof_Context.augment t ctxt` registers the Frees as **fixed variables** in an augmented context `ctxt'` (calls `Variable.add_fixes_implicit` + `Variable.declare_term`)
3. `Variable.export_terms ctxt' ctxt [t]` generalizes everything fixed in `ctxt'` but not in `ctxt`: Frees become Vars, TFrees become TVars (via `Term_Subst.generalize`)

**Common mistake:** Using `read_term_pattern` directly and expecting `Pattern.matches` to work. It won't — Frees are rigid (match only themselves), Vars are flexible (match anything).

### Tactics and Methods
- **Location:** Pure/tactic.ML, Pure/goal.ML
- **Signature:** TACTIC
- Functions: resolve_tac, eresolve_tac, ALLGOALS

### Theory Extensions
- **Location:** Pure/Isar/local_theory.ML
- **Signature:** LOCAL_THEORY
- Functions: Local_Theory.define, Local_Theory.note

### Runtime ML Compilation
- **Location:** Pure/ML/ml_context.ML
- **Signature:** ML_CONTEXT

Compile and execute ML code at runtime:

```sml
fun define_constant ctxt pos =
  ML_Context.expression pos
    (ML_Lex.read "val my_constant = 42")
    ctxt
```

Key functions:
- `ML_Context.expression: Position.T -> ML_Lex.token Antiquote.antiquote list -> Context.generic -> Context.generic`
  - Returns updated context preserving all effects from execution
  - Use when effects need to be captured in the returned context
- `ML_Context.eval_source: ML_Compiler.flags -> Input.source -> unit`
  - Takes `Input.source` instead of tokens, returns unit
  - For quick testing only - modifications persist in thread-local context but are not returned

## Data Storage Mechanisms

Isabelle/ML provides two distinct approaches for storing persistent data:

### Context-Managed Data (Stateless)

**Functors:** Theory_Data, Proof_Data, Generic_Data
**Location:** Pure/context.ML

Data bound to Isabelle contexts (theory, Proof.context, Context.generic). The Isabelle system automatically manages lifecycle:
- Changes tracked with context
- Automatically reverted when users edit files (e.g., delete lines)
- Stateless: context system handles all state management
- Requires `empty`/`init` and `merge` operations

**Declaration example:**
```sml
structure MyData = Theory_Data(
  type T = int Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge (K true);
);

(* Usage *)
val table = MyData.get thy;
val thy' = MyData.put new_table thy;
val thy'' = MyData.map (Symtab.update ("key", 42)) thy;
```

**Common uses:** Type-checking data, definitions, facts, proof state - anything that should follow theory/proof context evolution.

**Available functors:**
- `Theory_Data`: Data bound to `theory` contexts
- `Proof_Data`: Data bound to `Proof.context`, requires `init: theory -> T`
- `Generic_Data`: Data bound to `Context.generic` (both theory and proof)

### Persistent References (Stateful)

**Types:** Synchronized.var, Unsynchronized.ref
**Location:** Pure/Concurrent/synchronized.ML, Pure/Concurrent/unsynchronized.ML

Data independent of Isabelle contexts:
- Changes persist regardless of context changes
- NOT reverted when users edit files
- Stateful: changes accumulate globally
- `Synchronized.var`: Thread-safe with mutex locks
- `Unsynchronized.ref`: Raw ML references (not thread-safe)

**Declaration example:**
```sml
(* Thread-safe *)
val global_counter = Synchronized.var "my_counter" 0;
val n = Synchronized.value global_counter;
val _ = Synchronized.change global_counter (fn x => x + 1);

(* Not thread-safe *)
val cache = Unsynchronized.ref NONE;
val _ = cache := SOME value;
```

**Common uses:** Global caches, theory database (thy_info.ML), random seeds, output modes - anything requiring true global mutable state independent of context.

### When to Use Which

- **Use Context-Managed Data** when data should follow theory/proof evolution and be reversible (definitions, types, facts, proof obligations)
- **Use Persistent References** when data must survive context changes (caches, session-wide state, theory loading state, resource pools)

## Type Conventions

### String vs XString
- `string` - Internal names (kernel)
- `xstring` - External names (user interface)

Example: A fixed variable `x` may have external name `x` but internal name `x__` to avoid conflicts.

### prop vs bool
- `prop` - Meta-logic propositions (Pure level), represents an individual premise or proof goal
- `bool` - Object-logic boolean values (HOL level)
- `HOL.Trueprop : bool ⇒ prop` - Embeds bool into prop

Syntax.read_prop wraps boolean expressions with Trueprop automatically; Syntax.read_term does not.

## Exception Handling

Isabelle/ML **forbids** catching all exceptions with `handle`:

```sml
(* COMPILE ERROR: "Handler catches all exceptions." *)
val x = expr handle e => fallback
```

To catch all exceptions, use the `\<^try>` antiquotation:

```sml
val x = \<^try>\<open>expr catch exn => fallback\<close>
```

Catching **specific** exception patterns with `handle` is fine:

```sml
val x = expr handle ERROR _ => fallback | THM _ => fallback2
```

## Tips for ML Development

1. **Check signature first:** Understand the interface before reading implementation
2. **Use grep:** Pure is large; targeted searches are more efficient than browsing
3. **Consult examples:** Other files in Pure/ show usage patterns
4. **String concatenation:** Use String.concat instead of `^` for better performance, especially when concatenating multiple strings
