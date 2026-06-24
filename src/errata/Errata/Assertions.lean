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
  unless cond do failAt loc message

/-- Asserts that the actual value equals the expected value, reporting both when they differ. -/
def assertEq {α} [BEq α] [Repr α] (expected actual : α)
    (loc : Location := by exact here%) : TestM Unit :=
  unless actual == expected do
    failAt loc "values are not equal" (detail? := some s!"expected: {repr expected}\nactual:   {repr actual}")

/-- Asserts that the actual value differs from the unexpected value. -/
def assertNe {α} [BEq α] [Repr α] (unexpected actual : α)
    (loc : Location := by exact here%) : TestM Unit := do
  if actual == unexpected then
    failAt loc "values are equal but should differ" (detail? := some s!"both: {repr actual}")

/-- Asserts that the actual string contains the expected substring. -/
def assertContains (expected actual : String)
    (loc : Location := by exact here%) : TestM Unit :=
  unless (actual.splitOn expected).length > 1 do
    failAt loc "substring not found" (detail? := some s!"expected to contain: {expected}\nactual: {actual}")

/-- Asserts that a file exists. -/
def assertFileExists (path : System.FilePath)
    (loc : Location := by exact here%) : TestM Unit := do
  unless ← path.pathExists do
    failAt loc s!"file does not exist: {path}"

/-- Asserts that an option is absent. -/
def assertNone {α} [Repr α] (value : Option α)
    (loc : Location := by exact here%) : Test := do
  if let some v := value then
    failAt loc s!"expected none, got {repr v}"

/-- Asserts that an option is present, returning its contents. -/
def assertSome {α} (value : Option α)
    (loc : Location := by exact here%) : TestM α :=
  match value with
  | some v => pure v
  | none => throw { message := "expected some, got none", location? := some loc }

/-- Asserts that an option is present, without inspecting its contents. -/
def assertIsSome {α} (value : Option α)
    (loc : Location := by exact here%) : Test :=
  discard (assertSome value loc)
