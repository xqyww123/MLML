---
name: isabelle-intro-elim-rules
description: How to read Isabelle introduction and elimination rules
---

# Reading Isabelle Introduction and Elimination Rules

## Operators

Inference rules are expressed in HHF (Hereditary Harrop Formula).
Meta implication `⟹` structures formulas in an inference rule, while `⟶` is the implication operator used **inside** formulas. For example, the typical natural deduction
```
P ⟶ Q    P
---------- (Modus Ponens)
Q
```
is written as `P ⟶ Q ⟹ P ⟹ Q` (⟹ binds weaker than ⟶; both are right-associative).

Meta quantifier `⋀` binds local variables. The typical natural deduction
```
P x
---- for arbitrary x
∀x. P x
```
is written as `(⋀x. P x) ⟹ ∀x. P x` (⋀ binds weaker than ∀).

Notation: `⟦P; Q⟧ ⟹ R` syntactically equals `P ⟹ Q ⟹ R`.

## Introduction Rules — Decomposing Goals

An introduction rule decomposes a goal into simpler subgoals. For example, `notI: (P ⟹ False) ⟹ ¬P` decomposes `¬P` into showing `False` from `P` (proof by contradiction). `conjI: P ⟹ Q ⟹ P ∧ Q` splits `P ∧ Q` into subgoals `P` and `Q`.

Generally, a rule of the form
```
(A₁₁ ⟹ ... ⟹ A₁ₙ ⟹ C₁) ⟹ ... ⟹ (Aₘ₁ ⟹ ... ⟹ Aₘₙ ⟹ Cₘ) ⟹ C
```
decomposes goal `C` into `m` subgoals, where the i-th subgoal assumes `Aᵢ₁, ...` and shows `Cᵢ`.

`⋀` in a subgoal introduces locally fixed variables, e.g. in `exE: ∃x. P x ⟹ (⋀x. P x ⟹ Q) ⟹ Q`, `⋀x` fixes a local witness `x`.

## Elimination Rules — Decomposing Assumptions

An elimination rule decomposes an **assumption** into more usable parts. For example, `conjE: P ∧ Q ⟹ (P ⟹ Q ⟹ R) ⟹ R` decomposes `P ∧ Q` into separate assumptions `P` and `Q`. `disjE: P ∨ Q ⟹ (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R` does case analysis on `P ∨ Q`.

Generally, an elimination rule of the form
```
H ⟹ (B₁₁ ⟹ ... ⟹ B₁ₙ ⟹ R) ⟹ ... ⟹ (Bₘ₁ ⟹ ... ⟹ Bₘₙ ⟹ R) ⟹ R
```
decomposes assumption `H` into `m` cases, where the i-th provides `Bᵢ₁, ...` as new assumptions, each showing goal `R`.

**Why this form?** `R` is the goal to be proved. The rule says: given `H`, if we can show `R` from each set of decomposed cases, then `R` holds. This is how `H` is "eliminated" — replaced by simpler pieces that suffice to reach the goal.

## Reading Guide

- **Intro rule:** "To prove [conclusion], it suffices to show [subgoals]."
- **Elim rule:** "Given [hypothesis], one obtains [decomposed cases]."

