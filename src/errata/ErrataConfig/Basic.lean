/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
What `errata.toml` says once it is validated, and the monad that validates it: each reader records
the problems it finds, each at the syntax of the value it concerns, and goes on reading.
-/
module

public import Lake.Toml
public import Lean.Data.Json

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace ErrataConfig

/-- A problem with the configuration file, at the value that it concerns. -/
structure Problem where
  /-- The syntax of the value. -/
  ref : Lean.Syntax
  /-- What is wrong. -/
  msg : String

/--
Validation of the configuration file: it reads the file's positions and gathers every problem that
it finds.
-/
abbrev CheckM := ReaderT Lean.FileMap (StateM (Array Problem))

/-- Records a problem at the value {name}`ref`. -/
def problem (ref : Lean.Syntax) (msg : String) : CheckM Unit :=
  modify (·.push ⟨ref, msg⟩)

/--
The line and column where {name}`ref` starts, with lines counted from one and columns from zero, or
{lean}`(0, 0)` when it has no position.
-/
def positionOf (ref : Lean.Syntax) : CheckM (Nat × Nat) := do
  match ref.getPos? with
  | some pos =>
    let p := (← read).toPosition pos
    return (p.line, p.column)
  | none => return (0, 0)

/-- A key of a table as the file writes it. -/
def keyName (k : Lean.Name) : String := k.toString (escape := false)

/-- What kind of TOML value a value is, for messages. -/
def kindOf : Lake.Toml.Value → String
  | .string .. => "a string"
  | .integer .. => "an integer"
  | .float .. => "a float"
  | .boolean .. => "a boolean"
  | .dateTime .. => "a date-time"
  | .array .. => "an array"
  | .table .. => "a table"

/-- Records a problem for every key of {name}`t` outside {name}`known`. -/
def checkKeys (context : String) (known : List String) (t : Lake.Toml.Table) : CheckM Unit := do
  for (k, v) in t.items do
    unless known.contains (keyName k) do
      problem v.ref s!"unknown key '{keyName k}' in {context}"

/--
A filter's text and the position of its string's opening delimiter in the file. When the string's
token decodes to the text, {name}`FilterString.positions?` holds the line and column of each of the
text's characters, then of the closing delimiter.
-/
structure FilterString where
  /-- The filter's text. -/
  text : String
  /-- The line of the string's opening delimiter, counted from one. -/
  line : Nat
  /-- The column of the string's opening delimiter, counted from zero. -/
  col : Nat
  /-- The line and column of each character, then of the closing delimiter. -/
  positions? : Option (Array (Nat × Nat)) := none
deriving Repr, Inhabited, BEq

/-- The value of a setting: a string, or the Lake target whose result is its value. -/
inductive SettingValue where
  /-- A string that the file gives. -/
  | value (s : String)
  /-- The Lake target named by {name}`target`, written at {name}`line` and {name}`col`. -/
  | needs (target : String) (line col : Nat)
deriving Repr, Inhabited, BEq

/-- A per-test override of a profile. -/
structure Override where
  /-- The tests that the override applies to. -/
  filter : FilterString
  /-- How long a test may run, in milliseconds. -/
  timeoutMs? : Option Nat := none
  /-- How long a fixture's phase may run, in milliseconds. -/
  fixtureTimeoutMs? : Option Nat := none
  /-- How long a terminated test has before it is killed, in milliseconds. -/
  gracePeriodMs? : Option Nat := none
  /-- How long a test runs before the report marks it slow, in milliseconds. -/
  slowAfterMs? : Option Nat := none
  /-- Whether golden checks rewrite their expected files. -/
  updateGolden? : Option Bool := none
  /-- Values of settings, by name. -/
  settings : Array (String × SettingValue) := #[]
deriving Inhabited

/-- A profile, as the file gives it and, after inheritance, with its ancestors' values merged. -/
structure Profile where
  /-- The profile's name. -/
  name : String
  /-- The syntax of the profile's table. -/
  ref : Lean.Syntax := .missing
  /-- The profile that it names in {lit}`inherits`, with the syntax of that name. -/
  inherits? : Option (String × Lean.Syntax) := none
  /-- How long a test may run, in milliseconds. -/
  timeoutMs? : Option Nat := none
  /-- How long a fixture's phase may run, in milliseconds. -/
  fixtureTimeoutMs? : Option Nat := none
  /-- How long a terminated test has before it is killed, in milliseconds. -/
  gracePeriodMs? : Option Nat := none
  /-- How long a test runs before the report marks it slow, in milliseconds. -/
  slowAfterMs? : Option Nat := none
  /-- How many tests may run at once. -/
  jobs? : Option Nat := none
  /-- Whether golden checks rewrite their expected files. -/
  updateGolden? : Option Bool := none
  /-- Values of settings, by name. -/
  settings : Array (String × SettingValue) := #[]
  /-- The per-test overrides, in order. -/
  overrides : Array Override := #[]
  /-- The filter that the tests to run are drawn from, unless the command line ignores it. -/
  defaultFilter? : Option FilterString := none
  /-- The path of the JUnit XML report, relative to the package's directory. -/
  junit? : Option String := none
  /-- The path of the JSON report, relative to the package's directory. -/
  json? : Option String := none
  /-- The path of the Markdown report, relative to the package's directory. -/
  markdown? : Option String := none
deriving Inhabited

/-- A test executable that {lit}`[[executable]]` adds. -/
structure Executable where
  /-- The executable's name. -/
  name : String
  /-- The syntax of the executable's table. -/
  ref : Lean.Syntax
  /-- The line of the executable's table, counted from one. -/
  line : Nat
  /-- The column of the executable's table, counted from zero. -/
  col : Nat
  /-- The command that starts the executable. -/
  command : Array String
  /-- The directory to start it in, relative to the configuration file's directory. -/
  cwd? : Option String
deriving Inhabited

/-- What the configuration file says, validated. -/
structure File where
  /-- The filter that selects the tests to run when neither a profile nor the command line does. -/
  defaultFilter? : Option FilterString := none
  /-- The test executables that the file adds. -/
  executables : Array Executable := #[]
  /-- The profiles, with inheritance applied. -/
  profiles : Array Profile := #[]
deriving Inhabited

end ErrataConfig
