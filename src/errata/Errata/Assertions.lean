/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.TestM
public import Errata.Here

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/-- Asserts that a condition holds. -/
def assert (cond : Bool) (message : String := "assertion failed")
    (loc : Location := by exact here%) : TestM Unit :=
  unless cond do fail message (location? := some loc)

/-- Asserts that the actual value equals the expected value, reporting both when they differ. -/
def assertEq {α} [BEq α] [Repr α] (expected actual : α)
    (loc : Location := by exact here%) : TestM Unit :=
  unless actual == expected do
    fail "values are not equal"
      (detail? := some s!"expected: {repr expected}\nactual:   {repr actual}")
      (location? := some loc)

/-- Asserts that the actual value differs from the unexpected value. -/
def assertNe {α} [BEq α] [Repr α] (unexpected actual : α)
    (loc : Location := by exact here%) : TestM Unit := do
  if actual == unexpected then
    fail "values are equal but should differ"
      (detail? := some s!"both: {repr actual}") (location? := some loc)

/-- Asserts that the actual string contains the expected substring. -/
def assertContains (expected actual : String)
    (loc : Location := by exact here%) : TestM Unit :=
  unless (actual.splitOn expected).length > 1 do
    fail "substring not found"
      (detail? := some s!"expected to contain: {expected}\nactual: {actual}")
      (location? := some loc)

/-- Asserts that a file exists. -/
def assertFileExists (path : System.FilePath)
    (loc : Location := by exact here%) : TestM Unit := do
  unless ← path.pathExists do
    fail s!"file does not exist: {path}" (location? := some loc)
