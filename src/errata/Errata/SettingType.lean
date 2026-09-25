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

Settings' {name (full := Setting.default?)}`default?` values are constant expressions, which give
the same value wherever and whenever they are evaluated. Test executables evaluate the default when
they list it, and the interpreted product lists the value that {lit}`@[setting]` recorded; defaults
that read the environment, a file, or the clock make the two listings disagree.
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
