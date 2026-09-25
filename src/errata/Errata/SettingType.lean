/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The type of settings, which `@[setting]` checks declarations against.
-/
module

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/--
A setting: a value that the configuration file or the command line gives as a string, and that a
test takes as a parameter of the setting's {name (full := Setting.type)}`type`. Declarations of this
type marked {lit}`@[setting]` declare settings, and their docstrings describe them.

A setting's {name (full := Setting.default?)}`default?` is a constant expression: it gives the same
value wherever and whenever it is evaluated. Test executables list it, and the interpreted product
lists the value that {lit}`@[setting]` recorded, so a default that reads the environment, a file,
or the clock would make the two disagree.
-/
structure Setting where
  /-- The type of the value that a test receives. -/
  type : Type
  /-- Parses a value from the string that the configuration gives, or rejects it. -/
  fromString : String → Option type
  /--
  The value that a test receives when neither the command line nor the configuration gives one,
  parsed by {name (full := Setting.fromString)}`fromString` like any other value.
  -/
  default? : Option String := none

/--
Settings stand for the types of their values, so a parameter {lit}`(x : S)` has the type
{lit}`S.type`.
-/
instance : CoeSort Setting Type := ⟨Setting.type⟩
