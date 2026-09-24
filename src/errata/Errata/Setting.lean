/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Settings: named values that the configuration and the command line give as strings, and that tests
take as parameters of the setting's type.
-/
module

public import Errata.TestM
public import Errata.SettingAttribute

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/--
A setting: a value that the configuration file or the command line gives as a string, and that a test
takes as a parameter of the setting's {name (full := Setting.type)}`type`. A declaration of this type
marked {lit}`@[setting]` declares one, and its docstring describes it.
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

/-- A setting stands for the type of its values, so a parameter {lit}`(x : S)` has the type `S.type`. -/
instance : CoeSort Setting Type := ⟨Setting.type⟩

/-- A setting that a test takes, as a test executable lists it. -/
structure SettingRef where
  /-- The setting's name. -/
  name : String
  /-- Whether the test takes the setting as an {name}`Option`, and so runs without a value. -/
  optional : Bool
  /-- The setting's docstring. -/
  description? : Option String := none
  /-- The setting's declared default value. -/
  default? : Option String := none
deriving Repr, Inhabited, BEq

/--
The value of the setting {name}`S`, named {name}`name`, among {name}`settings`: the last value given
for the name, parsed by the setting's parser. With no value, or a value that the parser rejects, the
test ends with an error that names the setting.
-/
def Setting.withValue (S : Setting) (name : String) (settings : Array (String × String))
    (k : S.type → TestM Unit) : TestM Unit := do
  let some raw := (settings.findRev? (·.1 == name)).map (·.2)
    | throwThe IO.Error <| .userError s!"the mandatory setting {name} has no value"
  let some value := S.fromString raw
    | throwThe IO.Error <| .userError s!"the setting {name} has the value {raw.quote}, which its \
        parser rejects"
  k value

/--
The value of the optional setting {name}`S`, named {name}`name`, among {name}`settings`:
{lean}`none` when no value is given, and otherwise the last value given, parsed by the setting's
parser. A value that the parser rejects ends the test with an error that names the setting.
-/
def Setting.withOptional (S : Setting) (name : String) (settings : Array (String × String))
    (k : Option S.type → TestM Unit) : TestM Unit := do
  match (settings.findRev? (·.1 == name)).map (·.2) with
  | none => k none
  | some raw =>
    let some value := S.fromString raw
      | throwThe IO.Error <| .userError s!"the setting {name} has the value {raw.quote}, which its \
          parser rejects"
    k (some value)

/--
The seed for property tests, a natural number. The runner derives each test's seed from the run's
seed, the test executable's name, and the test's name, unless the configuration or the command line
gives one.

A setting's name is the last component of its declaration's name, and by convention it begins with a
lowercase letter, as a definition's name does.
-/
@[setting, expose]
def seed : Setting where
  type := Nat
  fromString s := s.toNat?
