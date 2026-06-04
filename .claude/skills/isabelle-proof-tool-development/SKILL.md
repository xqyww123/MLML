---
name: isabelle-proof-tool-development
description: Techniques for developing proof tools in Isabelle, including understanding HHF (Hereditary Harrop Formula) proof state representation
---

# Isabelle Proof Tool Development: HHF Proof State Techniques

This skill provides essential techniques for implementing proof tools in Isabelle, with a focus on understanding how Isabelle represents proof states using HHF (Hereditary Harrop Formula) format. This knowledge is fundamental to building tactics, automated provers, and other proof automation tools in Isabelle.

## What is HHF (Hereditary Harrop Formula)?

HHF has the general form:
```
⋀x₁...xₘ. H₁ ⟹ ... ⟹ Hₙ ⟹ A
```

Where m, n ≥ 0; A is atomic or recursively HHF; H₁, ..., Hₙ are recursively HHF.

**CRITICAL: HHF MUST use meta-logic operators ⋀ and ⟹, NOT object-logic operators ∀ and →**

## HHF as Proof State

**IMPORTANT:** When an HHF sequent represents a proof state, it encodes **subgoals** in a specific way.

**Example:**
```
(⋀x y. A ⟹ B ⟹ C) ⟹ (⋀z. D ⟹ E) ⟹ F
```

This represents a proof state where:
- **Ultimate goal:** F (the rightmost element)
- **Subgoal 1:**
  - Local variables: x, y (arbitrary but fixed)
  - Premises: A, B
  - Goal to show: C
- **Subgoal 2:**
  - Local variable: z (arbitrary but fixed)
  - Premise: D
  - Goal to show: E

**How to read:** At the top level, each `(⋀vars. premises ⟹ goal)` structure before the rightmost element represents one subgoal. Within each subgoal, the meta-quantifiers (⋀) bind local variables, and the nested `⟹` separate premises from the subgoal's conclusion. The rightmost element is the ultimate goal, shown once all subgoals are solved.

## The Pure.prop Protector

The ultimate goal is actually wrapped by an invisible operator `Pure.prop :: prop ⇒ prop` (not printed). This distinguishes the ultimate goal from intermediate subgoals.

**Why needed:** Consider these two different proof states:

1. `... ⟹ Pure.prop (A ⟹ B)` - Ultimate goal is `A ⟹ B`; no subgoals remain
2. `... ⟹ A ⟹ Pure.prop B` - Ultimate goal is B; one subgoal remains (premise A → show B)

Without Pure.prop, these would be ambiguous.

## Normal Form

Isabelle maintains HHF in **normal form** where:
- Quantifiers are pulled to the front at each nesting level
- Implications are right-associative: `A ⟹ B ⟹ C` means `A ⟹ (B ⟹ C)`

## Related ML Code

Key modules in `contrib/Isabelle2024/src/Pure/`:
- `Pure/logic.ML` - Meta-logic operations including HHF manipulation
- `Pure/term.ML` - Term structure (handles ⋀ and ⟹)
- `Pure/thm.ML` - Theorem representation
- `Pure/goal.ML` - Goal/subgoal operations
- `Pure/Proof/proof.ML` - Proof state structure

