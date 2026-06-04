---
name: isabelle-ml-style
description: Isabelle/ML coding style guide and conventions based on official implementation documentation
---

# Isabelle/ML Style Guide

Coding style conventions for writing Isabelle/ML code.

## Core Principles

1. **Consistency** - The main principle. Choose your style and stick to it
2. **Readability** - Code should tell an informed reader what is really going on
3. **Maintainability** - Optimized for long-term system development
4. **Compositionality** - Layout should not change when expressions are refined

## Naming Conventions

### Three Variants by Case

- **lower-case** (e.g., `foo_bar`) - values, types, record fields
- **Capitalized** (e.g., `Foo_Bar`) - datatype constructors, structures, functors
- **UPPER-CASE** (e.g., `FOO_BAR`) - special values, exception constructors, signatures

### Rules

- Names consist of 1-3 words (rarely 4), separated by underscore
- **Never** use camelCase (e.g., `FooBar` → use `Foo_Bar`)
- Single capital letter doesn't count as word: `foo_barT` is OK
- Name variants: use 1-3 primes (`foo'`, `foo''`, `foo'''`) or digits (`foo0`, `foo42`)

### Scopes

- **Always** use explicit qualification: `Syntax.string_of_term` (not `open`)
- **Avoid** aliases of well-known library functions
- Local names can be shorter, but **never** use `helper`, `aux`, or `f`

### Standard Naming Patterns

**Conversion functions:**
- `foo_to_bar` or `bar_of_foo`
- **Never** `foo2bar`, `bar_from_foo`, `bar_for_foo`, `bar4foo`

**Context types:**
- theories: `thy` (rarely `theory`, **never** `thry`)
- proof contexts: `ctxt` (rarely `context`, **never** `ctx`)
- generic contexts: `context`
- local theories: `lthy`

**Logical entities:**
- sorts: `S`
- types: `T`, `U`, or `ty` (**never** `t`)
- terms: `t`, `u`, or `tm` (**never** `trm`)
- certified types: `cT` (rarely `T`)
- certified terms: `ct` (rarely `t`, **never** `ctrm`)
- theorems: `th` or `thm`

**Tactics:**
- Always have `_tac` suffix
- Subgoal index: `i`
- Goal state: `st` (not `thm`)
- Pattern: `fun my_tac ctxt arg1 arg2 i st = ...`

## Source Layout

### Line Length

- Limit: 80 characters (max 100 for qualified names)

### Indentation

- **Use spaces only, never tabs**
- Each nesting level: 2 spaces (sometimes 1, rarely 4, **never** 8)
- Follow logical nesting depth, not accidental text length

### White-space

Follow mathematical typesetting conventions:

```sml
val x = y + z * (a + b);
val pair = (a, b);
val record = {foo = 1, bar = 2};
```

### Line Breaking

Break **after** infix operator or punctuation:

```sml
(* RIGHT *)
val x =
  a +
  b +
  c;

(* RIGHT *)
val tuple =
  (a,
   b,
   c);
```

### Function Application

- Curried: `f a b`
- Tupled: `g (a, b)` — note the space between `g` and `(`

### Multiple Clauses

Add extra indentation for `fun`, `fn`, `handle`, `case`:

```sml
(* RIGHT *)
fun foo p1 =
    expr1
  | foo p2 =
    expr2
```

### Complex Expressions

For `case` in function body, use extra parentheses for clarity:

```sml
(* RIGHT *)
fun foo p1 =
    (case e of
      q1 => ...
    | q2 => ...)
  | foo p2 =
    let
      ...
    in
      ...
    end
```

**Exceptions to compositionality:**

1. **Multi-branch if:**
   ```sml
   if b1 then e1
   else if b2 then e2
   else e3
   ```

2. **fn with combinators** (use with care):
   ```sml
   fun foo x y = fold (fn z =>
     expr)
   ```

### What to Avoid

- **Never** use let expressions inline without proper structure
- **Never** create two-dimensional layouts or ASCII-art
- **Never** align code based on accidental text length

## File Structure

### Header Format

Standard header (see `~~/src/Pure/thm.ML`):
- Title entry
- Author entry
- Prose description (1 line to several paragraphs)

### Sectioning via Comments

```sml
(**** chapter ****)

(*** section ***)

(** subsection **)

(* subsubsection *)

(*short paragraph*)

(*
  long paragraph,
  with more text
*)
```

## Special Name Components

- `legacy` - Operation to be discontinued soon
- `global` - Works with background theory instead of local context (migrate away from this)
