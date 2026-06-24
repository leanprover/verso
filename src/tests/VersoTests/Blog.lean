/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen

Property tests for blog identifier generation. This is a non-`module` file because `VersoBlog`
itself is not part of the module system; the Errata runner imports it through its non-module main.
-/
import VersoBlog
import VersoBlog.LiterateLeanPage
import Tests.Arbitrary
import Errata

open Lean
open Verso Genre Blog
open Verso.Multi
open Verso.NameMap
open Plausible Gen Arbitrary
open Errata

def freshIdOk (hint : LetterString) (path : Path) (howMany : Nat) : Bool := Id.run do
  let mut st : TraverseState := { remoteContent := {} }
  let mut ids := #[]
  for _ in 0...howMany do
    let i := st.freshId path hint.sluggify
    st := { st with usedIds := st.usedIds.alter path (fun used? => used?.getD {} |>.insert i) }
    ids := ids.push i
  ids.size == howMany && ids.all (ids.count · == 1)

def freshIdFirstIsHint (hint : LetterString) (path : Path) : Bool := Id.run do
  let st : TraverseState := { remoteContent := {} }
  let i := st.freshId path hint.sluggify
  hint.isEmpty || i == hint.sluggify

def freshIdSecondIsHintWith1 (hint : LetterString) (path : Path) : Bool := Id.run do
  let mut st : TraverseState := { remoteContent := {} }
  let i := st.freshId path hint.sluggify
  st := { st with usedIds := st.usedIds.alter path (fun used? => used?.getD {} |>.insert i) }
  let i' := st.freshId path hint.sluggify
  i != i' && (hint.isEmpty || (i == hint.sluggify && i' == (s!"{hint}1").sluggify))

/-- Identifiers freshly generated within a path are unique. -/
@[test]
def freshIdsAreUnique : Test := property (∀ h p n, freshIdOk h p n)

/-- The first identifier generated for a hint is the hint itself. -/
@[test]
def freshIdFirst : Test := property (∀ h p, freshIdFirstIsHint h p)

/-- The second identifier generated for a hint is the hint with `1` appended. -/
@[test]
def freshIdSecond : Test := property (∀ h p, freshIdSecondIsHintWith1 h p)
