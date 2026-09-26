/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Tests that the conformance suite runs through this library's own test executable, each playing a part
that the suite's checks ask of every test executable: one that fails or throws when a setting asks it
to, one that takes a setting without a default, and one that leaves a process running when a
setting names it. `errata.toml` gives the setting without a default a value, so the tests pass in an
ordinary run.
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
  default? := some "pass"

/-- A value that a test needs, with no default. -/
@[setting, expose]
def required : Setting where
  type := String
  fromString s := some s

/-- Passes, unless its setting asks it to fail an assertion or to throw. -/
@[test]
def endsAsAsked (how : outcome) : Test := do
  match how with
  | "fail" => assertBEq 3 4
  | "error" => throwThe IO.Error (IO.userError "thrown on request")
  | _ => pure ()

/--
Prints the run's identifier, which the runner gives every test executable, and the thread grant it
received.
-/
@[test]
def printsRunId : Test := do
  IO.println s!"run id: {(← IO.getEnv "ERRATA_RUN_ID").getD ""}"
  IO.println s!"threads: {(← read).threads}; LEAN_NUM_THREADS: \
    {(← IO.getEnv "LEAN_NUM_THREADS").getD ""}"

/-- Passes once it has the value it needs, which it prints. -/
@[test]
def needsSetting (value : required) : Test := do
  IO.println s!"received {value}"

/--
A text that names the processes that a test leaves running, so that a check can find them; empty by
default.
-/
@[setting, expose]
def marker : Setting where
  type := String
  fromString s := some s
  default? := some ""

/--
With a marker, starts a process whose command line holds the marker and that runs for five minutes,
and waits for it; with the empty marker, passes at once.
-/
@[test]
def lingers (m : marker) : Test := do
  if m.isEmpty then return
  let child ← IO.Process.spawn
    { cmd := "sh", args := #["-c", s!"sleep 300; : errata-conformance-{m}"] }
  discard child.wait

/-- A golden file for a test to check its output against; empty by default, for no file. -/
@[setting, expose]
def goldenPath : Setting where
  type := String
  fromString s := some s
  default? := some ""

/--
With a golden file, checks the text {lit}`golden contents` against it, which rewrites the file when
golden checks update their expected files; with the empty path, passes at once.
-/
@[test]
def checksGolden (path : goldenPath) : Test := do
  if path.isEmpty then return
  goldenFile path "golden contents\n"

/--
A choice that may be left open: {lit}`true` or {lit}`false`, or the empty default for no choice. Its
absence is a value of its own type.
-/
@[setting, expose]
def choice : Setting where
  type := Option Bool
  fromString
    | "" => some none
    | "true" => some (some true)
    | "false" => some (some false)
    | _ => none
  default? := some ""

/-- Prints the choice that it received. -/
@[test]
def printsChoice (c : choice) : Test := do
  IO.println s!"choice: {match c with | none => "open" | some b => toString b}"

end ErrataTests.Roles
