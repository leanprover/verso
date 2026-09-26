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
public import Errata.SettingType
public import Errata.SettingAttribute

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/-- A setting that a test takes, as a test executable lists it. -/
structure SettingRef where
  /-- The setting's name: its fully qualified declaration name. -/
  name : String
  /-- The setting's docstring. -/
  description? : Option String := none
  /-- The setting's declared default value. -/
  default? : Option String := none
deriving Repr, Inhabited, BEq

/--
The value of the setting {name}`S`, named {name}`name`, among {name}`settings`: the last value given
for the name, parsed by the setting's parser. With no value, or a value that the parser rejects, the
test or fixture phase ends with an error that names the setting.
-/
def Setting.withValue {m : Type → Type} {α : Type} [Monad m] [MonadExceptOf IO.Error m]
    (S : Setting) (name : String)
    (settings : Array (String × String)) (k : S.type → m α) : m α := do
  let some raw := (settings.findRev? (·.1 == name)).map (·.2)
    | throwThe IO.Error <| .userError s!"the mandatory setting {name} has no value"
  let some value := S.fromString raw
    | throwThe IO.Error <| .userError s!"the setting {name} has the value {raw.quote}, which its \
        parser rejects"
  k value

-- Settings' names are their fully qualified declaration names, here `Errata.seed`. By convention,
-- settings' declarations begin with a lowercase letter, as definitions' names do.
/--
The seed for property tests, a natural number. The runner derives each test's seed from the run's
seed, the test executable's name, and the test's name, unless the configuration or the command line
gives one.
-/
@[setting, expose]
def seed : Setting where
  type := Nat
  fromString s := s.toNat?

/--
The setting that the Lean harness reads to rewrite golden files: when it is {lit}`true`, golden
checks write what they found over their expected files. The runner gives it the value {lit}`true`
under {lit}`--update-golden`.
-/
@[setting]
abbrev updateGolden : Setting where
  type := Bool
  fromString
    | "true" => some true
    | "false" => some false
    | _ => none
  default? := some "false"
