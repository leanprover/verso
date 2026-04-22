/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoSearch
public import VersoSearch.DomainSearch

/-!
Tests for the JavaScript wire format produced by `Verso.Search.DomainMapper.toJs` and
`Verso.Search.DomainMappers.toJs`. These are structural checks against the emitted JS source: they
assert that priority fields and global priority exports appear with the configured values, so the
browser-side combining code in `search-box.js` has the data it expects.
-/

namespace Verso.Tests.SearchJs

open Std
open Verso.Search

private def hasSub (haystack : String) (needle : String) : Bool :=
  haystack.find? needle |>.isSome

private def assertContains (label : String) (haystack : String) (needle : String) : IO Unit := do
  unless hasSub haystack needle do
    throw <| IO.userError s!"expected {label} output to contain {repr needle}, got:\n{haystack}"

/-- Verifies that `DomainMapper.toJs` emits the display/class/data fields without a priority. -/
def testMapperToJs : IO Unit := do
  let mapper : DomainMapper :=
    { displayName := "Term"
      className := "term"
      dataToSearchables := "x => []" }
  let rendered := (DomainMapper.toJs mapper).pretty (width := 70)
  assertContains "DomainMapper" rendered "displayName:"
  assertContains "DomainMapper" rendered "\"Term\""
  assertContains "DomainMapper" rendered "className:"
  assertContains "DomainMapper" rendered "\"term\""
  assertContains "DomainMapper" rendered "dataToSearchables:"
  if hasSub rendered "searchPriority" then
    throw <| IO.userError
      s!"DomainMapper output should not contain `searchPriority` (it lives in SearchPriorities now):\n{rendered}"

/--
Verifies that `DomainMappers.toJs` emits both the `domainMappers` constant and the
`searchPriorities` constant with the correct semantic / fullText values plus the per-domain
priorities map.
-/
def testMappersToJs : IO Unit := do
  let mapper : DomainMapper :=
    { displayName := "Term"
      className := "term"
      dataToSearchables := "x => []" }
  let mappers : DomainMappers := HashMap.ofList [("Verso.Test", mapper)]
  let priorities : SearchPriorities :=
    { semantic := 60, fullText := 40, domains := ({} : Verso.NameMap _).insert `Verso.Test 73 }
  let rendered := (mappers.toJs priorities).pretty (width := 70)
  assertContains "DomainMappers" rendered "export const domainMappers"
  assertContains "DomainMappers" rendered "export const searchPriorities"
  assertContains "DomainMappers" rendered "semantic:"
  assertContains "DomainMappers" rendered "60"
  assertContains "DomainMappers" rendered "fullText:"
  assertContains "DomainMappers" rendered "40"
  assertContains "DomainMappers" rendered "domains:"
  assertContains "DomainMappers" rendered "\"Verso.Test\""
  assertContains "DomainMappers" rendered "73"

/--
Verifies `Verso.Search.priorityMapJson` produces a keyed map of only the documents that have a
priority set, using the same centered-at-50 integer convention as `Searchable.priority`.
-/
def testPriorityMap : IO Unit := do
  let docs : Array IndexDoc := #[
    { id := "boosted", header := "", context := #[], content := "", priority := some 80 },
    { id := "neutral", header := "", context := #[], content := "", priority := none },
    { id := "suppressed", header := "", context := #[], content := "", priority := some 10 },
    -- Ancestor-summed priorities can fall outside [0, 99]:
    { id := "deep-subsection", header := "", context := #[], content := "", priority := some (-20) }
  ]
  let rendered := (priorityMapJson docs).compress
  assertContains "priorityMapJson" rendered "\"boosted\":80"
  assertContains "priorityMapJson" rendered "\"suppressed\":10"
  assertContains "priorityMapJson" rendered "\"deep-subsection\":-20"
  -- Docs without a priority must be omitted, not serialized as null.
  if hasSub rendered "neutral" then
    throw <| IO.userError
      s!"priorityMapJson should omit docs without a priority, but emitted:\n{rendered}"

/-- Defaults for `SearchPriorities` are `semantic := 50` and `fullText := 50`. -/
def testMappersToJsDefaults : IO Unit := do
  let mappers : DomainMappers := {}
  let rendered := (mappers.toJs).pretty (width := 70)
  assertContains "DomainMappers defaults" rendered "export const searchPriorities"
  assertContains "DomainMappers defaults" rendered "semantic:"
  assertContains "DomainMappers defaults" rendered "fullText:"
  assertContains "DomainMappers defaults" rendered "50"

public def runSearchJsTests : IO Nat := do
  let tests : List (Lean.Name × IO Unit) :=
    [ (`testMapperToJs, testMapperToJs)
    , (`testMappersToJs, testMappersToJs)
    , (`testMappersToJsDefaults, testMappersToJsDefaults)
    , (`testPriorityMap, testPriorityMap)
    ]
  let mut failures := 0
  for (name, test) in tests do
    try
      test
      IO.println s!"{name}: passed"
    catch e =>
      IO.println s!"{name}: FAILED - {e}"
      failures := failures + 1
  return failures
