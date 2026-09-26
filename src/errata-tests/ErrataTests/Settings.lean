/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Settings and tests that take them, for checks of `@[setting]` and of how `@[test]` reads a test's
parameters.
-/
module

public import Errata

open Errata

public section

namespace ErrataTests.Settings

/-- The word that a test greets with. -/
@[setting, expose]
def greeting : Setting where
  type := String
  fromString s := some s
  default? := some "hello"

/-- How many times a test repeats itself. -/
@[setting, expose]
def repeats : Setting where
  type := Nat
  fromString s := s.toNat?
  default? := some "2"

/-- Whether a test keeps quiet. -/
@[setting, expose]
def quiet : Setting where
  type := Bool
  fromString
    | "true" => some true
    | "false" => some false
    | _ => none
  default? := some "false"

/-- Prints the greeting as often as it is told to, unless told to keep quiet. -/
@[test (tags := slow, chatty)]
def greets (word : greeting) (n : repeats) (quiet : quiet) : Test := do
  unless quiet do
    for _ in [0 : n] do
      IO.println word
  -- The setting's value has the setting's type.
  assertTrue (n + 0 == n)

/-- A test without settings or tags. -/
@[test]
def plain : Bool := true

end ErrataTests.Settings
