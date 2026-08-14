/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen

Tests for the JavaScript wire format produced by the search domain mappers. These are structural
checks against the emitted JS source, confirming that priority fields and global priority exports
appear with their configured values.
-/
module

public import VersoSearch
public import VersoSearch.DomainSearch
import Errata

open Std
open Verso Search
open Errata

/-- Whether `needle` occurs in `haystack`. -/
private def omits (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length == 1

/-- A domain mapper emits its display, class, and data fields, and no priority. -/
@[test]
def mapperToJs : Test := do
  let mapper : DomainMapper :=
    { displayName := "Term", className := "term", dataToSearchables := "x => []" }
  let rendered := (DomainMapper.toJs mapper).pretty (width := 70)
  assertContains "displayName:" rendered
  assertContains "\"Term\"" rendered
  assertContains "className:" rendered
  assertContains "\"term\"" rendered
  assertContains "dataToSearchables:" rendered
  -- The priority lives in `SearchPriorities` now, not on the mapper.
  assert (omits rendered "searchPriority") "mapper output should not contain `searchPriority`"

/-- A mapper collection emits the mappers and the search priorities with the configured values. -/
@[test]
def mappersToJs : Test := do
  let mapper : DomainMapper :=
    { displayName := "Term", className := "term", dataToSearchables := "x => []" }
  let mappers : DomainMappers := HashMap.ofList [("Verso.Test", mapper)]
  let priorities : SearchPriorities :=
    { semantic := 60, fullText := 40, domains := ({} : Verso.NameMap _).insert `Verso.Test 73 }
  let rendered := (mappers.toJs priorities).pretty (width := 70)
  assertContains "export const domainMappers" rendered
  assertContains "export const searchPriorities" rendered
  assertContains "semantic:" rendered
  assertContains "60" rendered
  assertContains "fullText:" rendered
  assertContains "40" rendered
  assertContains "domains:" rendered
  assertContains "\"Verso.Test\"" rendered
  assertContains "73" rendered

/-- An empty mapper collection emits the neutral default priorities of `50`. -/
@[test]
def mappersToJsDefaults : Test := do
  let mappers : DomainMappers := {}
  let rendered := (mappers.toJs).pretty (width := 70)
  assertContains "export const searchPriorities" rendered
  assertContains "semantic:" rendered
  assertContains "fullText:" rendered
  assertContains "50" rendered

/-- The priority map keys only the documents whose priority differs from neutral. -/
@[test]
def priorityMap : Test := do
  let docs : Array IndexDoc := #[
    { id := "boosted", header := "", context := #[], content := "", priority := some 80 },
    { id := "no-priority", header := "", context := #[], content := "", priority := none },
    { id := "explicit-neutral", header := "", context := #[], content := "", priority := some 50 },
    { id := "suppressed", header := "", context := #[], content := "", priority := some 10 },
    { id := "deep-subsection", header := "", context := #[], content := "", priority := some (-20) }]
  let rendered := (priorityMapJson docs).compress
  assertContains "\"boosted\":80" rendered
  assertContains "\"suppressed\":10" rendered
  assertContains "\"deep-subsection\":-20" rendered
  -- Neutral docs (`none` or `some 50`) are omitted entirely.
  for omitted in ["no-priority", "explicit-neutral"] do
    assert (omits rendered omitted) s!"priorityMapJson should omit the neutral doc {omitted}"
