/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoGen.Random.Basic
public import VersoGen.Text.Lorem

set_option doc.verso true

/-!
Lorem ipsum text for generated documents. Generators of text use the monad {lit}`LoremGen`, which
also tracks how much of the canonical lorem ipsum passage the text has used.
-/

namespace VersoGen.Random

open Plausible VersoGen.Text

public structure LoremState where
  /-- How many words of the canonical lorem ipsum passage the generated text has used. -/
  canonicalUsed : Nat := 0
deriving Inhabited

/-- Plausible's generator monad, with the state of the generated text. -/
public abbrev LoremGen := StateT LoremState Gen

/-- Runs a generator of text from a seed, starting at the canonical lorem ipsum passage. -/
public def LoremGen.runWithSeed [Inhabited α] (g : LoremGen α) (seed : Nat) : α :=
  Random.runWithSeed (g.run' {}) seed

/--
Runs a generator of text from given states of its text and its random source, with size 0, as
{name}`Random.runWithSeed` does.
-/
public def LoremGen.runFrom (g : LoremGen α) (s : LoremState × StdGen) :
    Except GenError (α × LoremState × StdGen) :=
  match (StateT.run (g.run s.1) (ULift.up s.2)).run (ULift.up 0) with
  | .ok ((x, lorem), rng) => .ok (x, lorem, rng.down)
  | .error e => .error e

/--
A generator of text made from a function. The function receives the states of the text and the
random source, and it returns a value and the new states.
-/
public def LoremGen.ofStateFn (f : LoremState × StdGen → α × LoremState × StdGen) :
    LoremGen α := do
  let ⟨rng⟩ ← getThe (ULift StdGen)
  let (x, lorem, rng) := f (← get, rng)
  set lorem
  set (ULift.up rng)
  return x

/-- The next word of the generated text. -/
public def Lorem.word : LoremGen String := do
  let s ← get
  if h : s.canonicalUsed < canonicalWords.size then
    set { s with canonicalUsed := s.canonicalUsed + 1 }
    return canonicalWords[s.canonicalUsed]
  else
    let ⟨i, _, hi⟩ ← Gen.chooseNatLt 0 latinWords.size (by decide)
    return latinWords[i]

/-- The next {name}`n` words of the generated text. -/
public def Lorem.words (n : Nat) : LoremGen (Array String) := do
  let mut out := #[]
  for _ in [0:n] do
    out := out.push (← Lorem.word)
  return out

/-- The next {name}`n` words of the generated text, separated by spaces. -/
public def words (n : Nat) : LoremGen String := do
  let mut out := ""
  for i in [0:n] do
    let w ← Lorem.word
    out := if i == 0 then w else out ++ " " ++ w
  return out

/--
The words of a sentence of between {name}`min` and {name}`max` words, the first capitalized and the
last ending in a period.
-/
public def Lorem.sentenceWords (min : Nat := 4) (max : Nat := 12) : LoremGen (Array String) := do
  let lo := Nat.max min 1
  let n := (← Gen.choose Nat lo (Nat.max lo max) (Nat.le_max_left ..)).val
  let ws ← Lorem.words n
  if h : ws.size = 0 then return ws
  else
    let ws := ws.set 0 (ws[0].capitalize)
    let last := ws.back!
    let last := if last.endsWith "," || last.endsWith "." then (last.dropEnd 1).copy else last
    return ws.pop.push (last ++ ".")

/-- A sentence of between {name}`min` and {name}`max` words, capitalized and ending in a period. -/
public def sentence (min : Nat := 4) (max : Nat := 12) : LoremGen String := do
  return (← Lorem.sentenceWords min max).foldl (init := "") fun out w =>
    if out.isEmpty then w else out ++ " " ++ w

/-- A title of between one and four words, without punctuation. -/
public def Lorem.title : LoremGen String := do
  let n := (← Gen.choose Nat 1 4 (by decide)).val
  let title := (bareWords (← Lorem.words n)).capitalize
  return if title.isEmpty then "lorem" else title

/--
A label for a link or footnote definition: a word and a random number, which make clashes rare.
-/
public def Lorem.label : LoremGen String := do
  let w := bareWord (← Lorem.word) |>.toLower
  let w := if w.isEmpty then "lorem" else w
  return s!"{w}-{(← Gen.choose Nat 1 99999 (by decide)).val}"
