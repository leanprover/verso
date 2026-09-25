/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Settings whose defaults `@[setting]` may be unable to evaluate where it is applied, and tests that
take them: a default that calls a function of another module, a default that reads a value an
`initialize` declaration holds, and a setting of another module marked here. Both products of the
Lean harness list and run them alike.
-/
module

public import Errata
public import ErrataTests.Defaults.Helper

open Errata

public section

namespace ErrataTests.Defaults

/-- A setting whose default calls a function of another module. -/
@[setting, expose]
def imported : Setting where
  type := String
  fromString s := some s
  default? := some (helperDefault 3)

/-- The value behind {name}`initialized`'s default. -/
initialize initialRef : IO.Ref String ← IO.mkRef "initial"

/-- A setting whose default reads the value that an `initialize` declaration holds. -/
@[setting, expose]
def initialized : Setting where
  type := String
  fromString s := some s
  default? := some (unsafe (unsafeBaseIO initialRef.get))

attribute [setting] markedElsewhere

/-- Receives the default that calls a function of another module. -/
@[test]
def receivesImported (s : imported) : Test := assertBEq "n3" s

/-- Receives the default that an `initialize` declaration holds. -/
@[test]
def receivesInitialized (s : initialized) : Test := assertBEq "initial" s

/-- Receives the default of the setting that this module marks. -/
@[test]
def receivesMarkedElsewhere (s : markedElsewhere) : Test := assertBEq "d" s
