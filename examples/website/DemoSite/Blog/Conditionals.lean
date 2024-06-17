/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Genre.Blog
import DemoSite.Categories
open Verso Genre Blog
open DemoSite

set_option trace.Elab.reuse true
set_option pp.rawOnError true
--set_option trace.Elab.command true
-- set_option trace.profiler true
-- set_option trace.profiler.threshold 1
-- set_option trace.Elab.Verso true
-- set_option trace.SubVerso.Highlighting.Code true

#doc (Post) "Conditional Expressions in Lean" =>

%%%
authors := ["Fictional Author", "Another Fictional Author"]
date := {year := 2024, month := 1, day := 15}
categories := [examples, other]
%%%


Finally started blogging!
This post describes the syntax and semantics of conditional expressions in Lean.
Here are some examples:

```leanInit demo
-- This block initializes a Lean context
```


```lean demo
example := if true then 1 else 2
example := if True then 1 else 2
example : Int := if True then 1 else 2
```

```lean demo
/-- A recursive function -/
def slowId : Nat → Nat
  | 0 => 0
  | n + 1 => slowId n + 1

#eval slowId 5

/-- An array literal -/
example := #[1, 2, 3]

example := 33
```

I can also prove things about conditionals!
```lean demo
theorem lt_4 (b : Bool) : (if b then 1 else 2) < 4 := by
  split
  . skip; decide
  . decide
```

It's also nice to write normal proofs sometimes.

```lean demo
def rev : List α → List α
  | [] => []
  | x :: xs => rev xs ++ [x]

def revAcc (acc : List α) : List α → List α
  | [] => acc
  | x :: xs => revAcc (x :: acc) xs

theorem rev_append_eq_revAcc (acc xs : List α) :
    rev xs ++ acc = revAcc acc xs := by
  induction xs generalizing acc with
  | nil => simp [rev, revAcc]
  | cons x xs ih =>
    unfold rev
    unfold revAcc
    rw [List.append_assoc]
    apply ih
```

Here are some uses of various constructors:
```lean demo
def squish (n : Option Nat) : Nat :=
  match n with
  | none => 0
  | some k => .succ k

def squish' (n : Option Nat) : Nat :=
  match n with
  | .none => 0
  | .some k => k.succ

open Nat in
def squish'' (n : Option Nat) : Nat :=
  match n with
  | none => 0
  | some k => succ k

```

Here is a mutual block:
```lean demo
mutual
  def f : Nat → Nat
    | 0 => 1
    | n + 1 => g n

  def g : Nat → Nat
    | 0 => 0
    | n + 1 => f n
end
```

```lean demo
--- foo
example := 99
```


Here is a proof with some lambdas and big terms in it, to check highlighting:
```lean demo
def grow : Nat → α → α
  | 0 | 1 => fun x => x
  | n + 2 =>
    let f1 := grow n
    let f2 := grow (n + 1)
    f1 f2

theorem grow_10_id {α} : grow (α := α) 6 = id := by
  repeat unfold grow
  sleep 10
  all_goals sorry

```


Here is a proof with big terms in the context:
```lean demo

open Lean in
def quotedStx [Monad m] [MonadQuotation m] [MonadRef m] (str : String) : m Syntax := do
  let s ← `(a b c #[x, $(quote str), z])
  pure s

open Lean in
example [Monad m] [MonadQuotation m] [MonadRef m] : ¬(quotedStx (m := m) = fun (x : String) => pure .missing) := by
  unfold quotedStx
  intro h
  let g : String → m Syntax := fun str => do
    let s ← `(a b c #[x, $(quote str), z])
    pure s
  have : g "hello" ≠ pure .missing := by skip; sorry
  sorry
```

It's possible to render a lot of info on one example:
```lean demo
elab "%much_info(" t:term ")" : term => open Lean Elab Term in do
  for i in [0:20] do
    logInfoAt t m!"Hello! ({i})"
  logInfoAt t "Some multi-line\ninfo too"
  elabTerm t none

elab "%more_info(" t:term ")" : term => open Lean Elab Term in do
  for i in [0:20] do
    logInfoAt t m!"Hello again! ({i})"
  logErrorAt t "And a great big error, much wider than the other info!"
  elabTerm t none
```

````lean demo error:=true
example := %much_info(22)

example := %more_info(25)
````

The info gets stacked up, with the greatest severity highlighting the range in question.

Thank you for looking at my test/demo post.
