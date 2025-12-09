/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Plausible
import Plausible.ArbitraryFueled
import VersoBlog
import Tests.Arbitrary

open Lean
open Verso Genre Blog
open Verso.Multi
open Verso.NameMap
open Plausible Gen Arbitrary


def freshIdOk (hint : LetterString) (path : Path) (howMany : Nat) : Bool := Id.run do
  let mut st : TraverseState := { remoteContent := {} }
  let mut ids := #[]
  for _ in 0...howMany do
    let i := st.freshId path hint.sluggify
    st := { st with usedIds := st.usedIds.alter path (fun used? => used?.getD {} |>.insert i) }
    ids := ids.push i
  ids.size == howMany && ids.all (ids.count · == 1)

def freshId_first_is_hint (hint : LetterString) (path : Path) : Bool := Id.run do
  let st : TraverseState := { remoteContent := {} }
  let i := st.freshId path hint.sluggify
  hint.isEmpty || i == hint.sluggify

def freshId_second_is_hint_with_1 (hint : LetterString) (path : Path) : Bool := Id.run do
  let mut st : TraverseState := { remoteContent := {} }
  let i := st.freshId path hint.sluggify
  st := { st with usedIds := st.usedIds.alter path (fun used? => used?.getD {} |>.insert i) }
  let i' := st.freshId path hint.sluggify
  i != i' && (hint.isEmpty || (i == hint.sluggify && i' == (s!"{hint}1").sluggify))


open scoped Plausible.Decorations in
private def testProp
    (p : Prop) (cfg : Configuration := {})
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] :
    IO (TestResult p') :=
  Testable.checkIO p' (cfg := cfg)

def blogTests : List (Name × (Σ p, IO <| TestResult p)) := [
  (`freshIdOk, ⟨_, testProp <| ∀ h p n, freshIdOk h p n⟩),
  (`freshId_first_is_hint, ⟨_, testProp <| ∀ h p, freshId_first_is_hint h p⟩),
  (`freshId_second_is_hint_with_1, ⟨_, testProp <| ∀ h p, freshId_second_is_hint_with_1 h p⟩),
]

public def runBlogTests : IO Nat := do
  let mut failures := 0
  for (name, test) in blogTests do
    IO.print s!"{name}: "
    let res ← test.2
    IO.println res
    unless res matches .success .. do
      failures := failures + 1
  return failures
