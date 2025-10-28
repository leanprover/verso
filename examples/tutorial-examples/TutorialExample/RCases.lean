import VersoTutorial

import TutorialExample.Data

open Verso.Genre
open Verso.Genre.Manual InlineLean

#doc (Tutorial) "RCases" =>
%%%
slug := "rcases"
summary := "is a tactic for case analysis"
%%%

This is a machine-generated tutorial used for testing the feature. Please don't attempt to learn from it.  Think of it as more-realistic Lorem Ipsum.

The {tactic}`rcases` tactic is used for case analysis and destructuring in Lean proofs. It recursively breaks down inductive types, existential statements, and conjunctions into their components.

# Basic Case Analysis

## Simple Inductive Types

Use {tactic}`rcases` to perform case analysis on an inductive type:

```lean
example (n : Nat) : n = 0 ∨ n > 0 := by
  rcases n with _ | n'
  · -- Case: n = 0
    left
    rfl
  · -- Case: n = succ n'
    right
    omega
```

The pattern `_ | n'` corresponds to the constructors of {name}`Nat`:
- `_` matches `Nat.zero` (underscore discards the name)
- `n'` matches `Nat.succ n'`

## Destructuring Options

```lean
example (opt : Option Nat) :
    opt = none ∨ ∃ n, opt = some n := by
  rcases opt with _ | n
  · -- Case: none
    left
    rfl
  · -- Case: some n
    right
    exact ⟨n, rfl⟩
```

## Destructuring Lists

```lean
theorem list_cases {α : Type} (xs : List α) :
    xs = [] ∨ ∃ head tail, xs = head :: tail := by
  rcases xs with _ | ⟨head, tail⟩
  · left; rfl
  · right; exact ⟨head, tail, rfl⟩
```

# Destructuring Compound Structures

## Conjunctions

`rcases` automatically destructures conjunctions:

```lean
example (h : P ∧ Q) : Q ∧ P := by
  rcases h with ⟨hp, hq⟩
  exact ⟨hq, hp⟩
```

Nested conjunctions are destructured recursively:

```lean
example (h : P ∧ Q ∧ R) : R ∧ P := by
  rcases h with ⟨hp, hq, hr⟩
  exact ⟨hr, hp⟩
```

## Existential Quantifiers

```lean
example (h : ∃ n : Nat, n > 5 ∧ Even n) : ∃ m, m > 3 := by
  rcases h with ⟨n, hn, heven⟩
  exact ⟨n, by omega⟩
```

## Disjunctions

```lean
example {R : Prop}
    (h : P ∨ Q) (hpq : P → R) (hqr : Q → R) : R := by
  rcases h with hp | hq
  · exact hpq hp
  · exact hqr hq
```

Multiple disjunctions:

```lean
example (h : P ∨ Q ∨ R) : R ∨ Q ∨ P := by
  rcases h with hp | hq | hr
  · right; right; exact hp
  · right; left; exact hq
  · left; exact hr
```

# Complex Patterns

## Nested Destructuring

Combine patterns to destructure complex hypotheses in one step:

```lean
example (h : ∃ n : Nat, n > 0 ∧ (∃ m, m < n ∧ Even m)) :
    ∃ k, Even k := by
  rcases h with ⟨n, hn, m, hm, heven⟩
  exact ⟨m, heven⟩
```

## Destructuring Pairs

```lean
example (p : Nat × Nat) : p.1 + p.2 = p.2 + p.1 := by
  rcases p with ⟨a, b⟩
  omega
```

Nested pairs:

```lean
example (p : Nat × (Nat × Nat)) : True := by
  rcases p with ⟨a, b, c⟩
  trivial
```

## Combining Cases and Destructuring

```lean
example (xs : List Nat) (h : xs ≠ []) : ∃ n, n ∈ xs := by
  rcases xs with _ | ⟨head, tail⟩
  · contradiction
  · exact ⟨head, List.Mem.head tail⟩
```

# Pattern Syntax

## Naming Patterns

- Use identifiers to bind variables: `n`, `m`, `hp`
- Use `_` to discard a component
- Use `rfl` to substitute with reflexivity immediately

```lean
example (h : ∃ n, n = 5) : ∃ m, m + 0 = 5 := by
  rcases h with ⟨n, rfl⟩  -- substitutes n = 5 immediately
  exact ⟨5, rfl⟩
```

## Angle Bracket Notation

Use `⟨p₁, p₂, ..., pₙ⟩` for:
- Conjunctions
- Existentials
- Pairs/tuples
- Any structure with a single constructor

```lean
example (h : ∃ n m : Nat, n < m ∧ Even n ∧ Even m) :
    ∃ k, Even k := by
  rcases h with ⟨n, m, _, heven_n, _⟩
  exact ⟨n, heven_n⟩
```

## Vertical Bar for Disjunctions

Use `|` to separate cases:

```lean
example (h : P ∨ Q ∨ R ∨ S) : True := by
  rcases h with hp | hq | hr | hs
  all_goals trivial
```

## Nested Patterns

Patterns can be arbitrarily nested:

```lean
example {P Q : α → Prop}
    (h : (∃ n, P n) ∨ (∃ m, Q m)) : True := by
  rcases h with ⟨n, hp⟩ | ⟨m, hq⟩
  · trivial
  · trivial
```

# Advanced Usage

## The `with` Clause for Induction

While `rcases` does case analysis, you can use it with custom induction principles:

```lean
example (xs : List Nat) : True := by
  rcases xs with _ | ⟨head, tail⟩
  -- Only case analysis, no induction hypothesis
  all_goals trivial
```

For induction, use `induction ... with` instead:

```lean
example (xs : List Nat) :
    xs.length = xs.reverse.length := by
  induction xs with
  | nil =>
    rfl
  | cons head tail ih =>
    grind
```

## The `obtain` Alternative

`obtain` is syntax sugar for `rcases` with existentials:

```lean
-- These are equivalent:
example (h : ∃ n, n > 5) : True := by
  rcases h with ⟨n, hn⟩
  trivial

example (h : ∃ n, n > 5) : True := by
  obtain ⟨n, hn⟩ := h
  trivial
```

`obtain` can also create new existentials:

```lean
example : ∃ n : Nat, n = 5 := by
  obtain ⟨n, hn⟩ : ∃ n, n = 5 := ⟨5, rfl⟩
  exact ⟨n, hn⟩
```

## Using `rcases` with Custom Types

```lean
inductive Colour where
  | red
  | green
  | blue

example (c : Colour) :
    c = Colour.red ∨
    c = Colour.green ∨
    c = Colour.blue := by
  rcases c with _ | _ | _
  · left; rfl
  · right; left; rfl
  · right; right; rfl
```

## Generalizing with `rcases`

Use `rcases` to introduce variables while generalizing:

```lean
example : ∀ n : Nat, n + 0 = n := by
  intro n
  rcases n with _ | n'
  · rfl
  · grind
```

# Common Patterns and Idioms

## Destructuring Hypotheses About Constructors

```lean
example (xs : List Nat) (h : xs = y :: ys) : xs ≠ [] := by
  intro contra
  rcases xs with _ | ⟨head, tail⟩
  · -- xs = []
    simp at h
  · -- xs = head :: tail
    contradiction
```

## Extracting Information from Decidable Propositions

```lean
example (n : Nat) (h : n < 10 ∨ n ≥ 10) : True := by
  rcases h with hlt | hge
  · trivial
  · trivial
```

## Working with Subtypes

```lean
example (n : {n : Nat // n > 5}) : n.val > 5 := by
  rcases n with ⟨val, proof⟩
  exact proof
```

## Multiple Hypotheses

You can use `rcases` on multiple hypotheses sequentially:

```lean
example (h₁ : P ∨ Q) (h₂ : ∃ n, n > 5) : True := by
  rcases h₁ with hp | hq
  · rcases h₂ with ⟨n, hn⟩
    trivial
  · rcases h₂ with ⟨n, hn⟩
    trivial
```

# Comparison with Related Tactics

## `rcases` vs `cases`

- `cases` does basic case analysis
- `rcases` recursively destructs nested structures

```lean
-- With cases, need multiple steps:
example (h : ∃ n : Nat, n > 0 ∧ Even n) : True := by
  cases h with
  | intro n h' =>
    cases h' with
    | intro hn heven =>
      trivial

-- With rcases, one step:
example (h : ∃ n : Nat, n > 0 ∧ Even n) : True := by
  rcases h with ⟨n, hn, heven⟩
  trivial
```

## `rcases` vs `obtain`

- `rcases` is more general
- `obtain` is specialized for existentials and is more readable

```lean
section
variable {P : α → Prop}
-- rcases style:
example (h : ∃ n, P n) : True := by
  rcases h with ⟨n, hp⟩
  trivial

-- obtain style (equivalent):
example (h : ∃ n, P n) : True := by
  obtain ⟨n, hp⟩ := h
  trivial
end
```

## `rcases` vs `match`

In term mode, use `match`; in tactic mode, use `rcases`:

```lean
-- Term mode:
def natToString (n : Nat) : String :=
  match n with
  | 0 => "zero"
  | n' + 1 => s!"successor of {natToString n'}"

-- Tactic mode:
example (n : Nat) : n = 0 ∨ n > 0 := by
  rcases n with _ | n'
  · left; rfl
  · right; omega
```

# Practical Examples

## Proof by Cases on List Structure

```lean
theorem list_append_assoc {α : Type} (xs ys zs : List α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil => rfl
  | cons head tail ih => simp [ih]
```

## Working with Inequalities

```lean
theorem nat_trichotomy (n m : Nat) :
    n < m ∨ n = m ∨ n > m := by
  rcases Nat.lt_trichotomy n m with h | h | h
  · left; exact h
  · right; left; exact h
  · right; right; exact h
```

## Destructuring Membership Proofs

```lean
theorem mem_append_iff {α : Type} (x : α) (xs ys : List α) :
    x ∈ xs ++ ys ↔ x ∈ xs ∨ x ∈ ys := by
  constructor
  · intro h
    induction xs with
    | nil => right; exact h
    | cons head tail ih  =>
      rcases h with h | h
      · left; exact List.Mem.head tail
      · rcases ih (by assumption) with h' | h'
        · left; exact List.Mem.tail head h'
        · right; exact h'
  · intro h
    rcases h with h | h
    · induction h with
      | head => exact List.Mem.head _
      | tail _ ih ih' => exact List.Mem.tail _ ih'
    · induction xs with
      | nil => exact h
      | cons _ _ ih => exact List.Mem.tail _ ih
```

## Working with Sigma Types

```lean
example (s : Σ n : Nat, Fin n) : True := by
  rcases s with ⟨n, i⟩
  trivial
```

## Combining with Other Tactics

```lean
section
open Mut
theorem even_or_odd (n : Nat) : Mut.Even n ∨ Odd n := by
  induction n with
  | zero => left; exact .zero
  | succ n ih =>
    rcases ih with heven | hodd
    · right; exact .succ heven
    · left; exact .succ hodd
end
```

# Common Pitfalls

## Forgetting to Handle All Cases

```lean
-- Error: missing cases
example (n : Nat) (h : n < 3) : n = 0 ∨ n = 1 ∨ n = 2 := by
  rcases n with _ | n'
  · left; rfl
  -- Need to handle the successor case!
  sorry
```

## Over-destructuring

Sometimes you don't need to fully destruct:

```lean
section
variable {P : α → Prop}

-- Over-destructuring:
example (h : ∃ n, P n) : True := by
  rcases h with ⟨n, hp⟩  -- hp not needed
  trivial

-- Better:
example (h : ∃ n, P n) : True := by
  rcases h with ⟨_, _⟩
  trivial

-- Or just:
example (h : ∃ n, P n) : True := by
  trivial  -- h not needed at all
end
```

## More `rcases` Pattern Syntax

```lean +error (name := ctorNames)
-- Wrong: trying to use constructor names
example (opt : Option Nat) : True := by
  rcases opt with none | some n  -- Error: 'none' is not a pattern
```
```leanOutput ctorNames
unexpected identifier; expected command
```
```lean
-- Correct: use patterns that match constructor structure
example (opt : Option Nat) : True := by
  rcases opt with _ | n
  . trivial
  . trivial
```

# Tips

1. *Use `_` for unused components* to make intent clear
2. *Use the `rfl` pattern* when you want immediate substitution
3. *Prefer {tactic}`obtain` for existentials* when it reads more naturally
4. *Break complex patterns* across multiple {tactic}`rcases` if it aids readability
5. *Name variables meaningfully* rather than using default names
6. *Use {tactic}`all_goals` or `· ` syntax* to handle similar cases uniformly

    ```lean
    example (h : P ∨ Q ∨ R) : True := by
      rcases h with hp | hq | hr
      all_goals trivial  -- handles all three cases at once
    ```
