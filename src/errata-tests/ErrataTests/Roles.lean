/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Tests that the conformance suite runs through this library's own test executable, each playing a part
that the suite's checks ask of every test executable: one that fails or throws when a setting asks it
to, and one that takes a setting without a default. `errata.toml` gives that setting a value, so the
tests pass in an ordinary run.
-/
module

public import Errata

open Errata

public section

namespace ErrataTests.Roles

/-- How a test ends: {lit}`fail` fails an assertion, {lit}`error` throws, and anything else passes. -/
@[setting, expose]
def outcome : Setting where
  type := String
  fromString s := some s

/-- A value that a test needs, with no default. -/
@[setting, expose]
def required : Setting where
  type := String
  fromString s := some s

/-- Passes, unless its setting asks it to fail an assertion or to throw. -/
@[test]
def endsAsAsked (how? : Option outcome) : Test := do
  match how? with
  | some "fail" => assertBEq 3 4
  | some "error" => throwThe IO.Error (IO.userError "thrown on request")
  | _ => pure ()

/-- Passes once it has the value it needs, which it prints. -/
@[test]
def needsSetting (value : required) : Test := do
  IO.println s!"received {value}"

end ErrataTests.Roles
