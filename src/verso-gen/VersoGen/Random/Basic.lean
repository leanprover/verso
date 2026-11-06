/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Plausible.Gen

set_option doc.verso true

namespace VersoGen.Random

open Plausible

/--
Runs a generator from a seed, with size 0. The generators of this library don't read Plausible's
size.

The Plausible operations that can fail are {name}`Gen.backtrack`, through the exhaustion of its fuel
or of its options, and the {lit}`Inhabited` instance of {name}`Gen`. The library doesn't use them,
so its generators don't fail. If a generator fails, the function panics.
-/
public def runWithSeed [Inhabited α] (g : Gen α) (seed : Nat) : α :=
  match ((runRandWith seed g).run ⟨0⟩ : Except GenError α) with
  | .ok x => x
  | .error (.genError msg) => panic! s!"the document generator failed: {msg}"

/-- Chooses true with a chance of {name}`percent` percent and false otherwise. -/
public def chance (percent : Nat) : Gen Bool :=
  return (← Gen.choose Nat 0 99 (by decide)).val < percent

/--
One bubble pass over the elements {name}`x` followed by {name}`rest`, which moves each element
forward past the elements that {name}`place` puts before it. The result is the elements after the
pass and the index of the first element of each exchange of consecutive elements that the pass
makes.
-/
def bubblePass (place : Array Nat) (x : Nat) : (rest : List Nat) → List Nat × List Nat
  | [] => ([x], [])
  | y :: rest =>
    if place[y]! < place[x]! then
      let (moved, swaps) := bubblePass place x rest
      (y :: moved, 0 :: swaps.map (· + 1))
    else
      let (moved, swaps) := bubblePass place y rest
      (x :: moved, swaps.map (· + 1))

/-- The exchanges of at most {name}`n` bubble passes, which stop after a pass without exchanges. -/
def bubblePasses (place : Array Nat) : (n : Nat) → List Nat → List Nat
  | 0, _ | _ + 1, [] => []
  | n + 1, x :: rest =>
    let (moved, swaps) := bubblePass place x rest
    if swaps.isEmpty then [] else swaps ++ bubblePasses place n moved

/--
Draws a random order of {name}`n` elements and gives the exchanges of consecutive elements that
bubble passes toward that order would make, starting from the original order. Each exchange is the
index of its first element, in the order that the passes make the exchanges. The passes assume
that every exchange happens, so when an exchange is refused where the instructions are applied,
the later instructions still apply and the result differs from the drawn order.
-/
public def swapsToRandomOrder (n : Nat) : Gen (List Nat) := do
  let target := (← Gen.permutationOf (List.range n)).val
  -- The place of each element, by its original index, in the random order
  let place := target.zipIdx.foldl (init := Array.replicate n 0) fun place (e, k) => place.set! e k
  return bubblePasses place n (List.range n)
