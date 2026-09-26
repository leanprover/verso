/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Fixtures and the tests that use them, which the conformance suite runs through this library's own
test executable. Each fixture plays a part that the suite's checks ask of every test executable: one
stamps a shared file as its users run, one fails in each phase when a setting asks it to, one depends
on a setting and on another fixture, one sleeps in its setup when a setting asks it to, and one asks
for threads. Without those settings every fixture and test here passes, so the tests pass in an
ordinary run.
-/
module

public import Errata
public import ErrataTests.Settings

open Errata

public section

namespace ErrataTests.Resources

/--
A file that the fixture `stamped` and its users append lines to, one per event; empty by default,
for no file.
-/
@[setting, expose]
def stampFile : Setting where
  type := String
  fromString s := some s
  default? := some ""

/-- Makes the fixtures `setupFails`, `prepareFails`, and `teardownFails` fail, when it is `true`. -/
@[setting, expose]
def failing : Setting where
  type := Bool
  fromString
    | "true" => some true
    | "false" => some false
    | _ => none
  default? := some "false"

/-- How long the fixture `slowSetup` sleeps in its setup, in milliseconds. -/
@[setting, expose]
def sleepMs : Setting where
  type := Nat
  fromString s := s.toNat?
  default? := some "0"

/-- Appends a line to a file, when a file is given. -/
def stamp (file : String) (line : String) : IO Unit := do
  unless file.isEmpty do
    let h ← IO.FS.Handle.mk file .append
    h.putStrLn line
    h.flush

/--
A fixture whose value is the stamp file: its setup, each prepare, and its teardown append a line to
the file, and each prepare takes a moment between its two lines.
-/
@[fixture, expose]
def stamped (file : stampFile) : Fixture where
  type := String
  toString := id
  fromString := some
  setup := do
    stamp file "setup"
    return file
  prepare file := do
    stamp file "prepare start"
    IO.sleep 100
    stamp file "prepare end"
  teardown file? := stamp (file?.getD "") s!"teardown {file?.isSome}"

/-- Stamps the file with its name as it starts and as it ends, a moment later. -/
def stampedUse (name : String) (file : String) : Test := do
  stamp file s!"start {name}"
  IO.sleep 400
  stamp file s!"end {name}"

/-- A user of `stamped` alone among its users. -/
@[test] def exclusiveA (file : stamped) : Test := stampedUse "exclusiveA" file

/-- Another user of `stamped` alone among its users. -/
@[test] def exclusiveB (file : stamped) : Test := stampedUse "exclusiveB" file

/-- A user of `stamped` that may run beside other shared users. -/
@[test] def sharedA (file : shared stamped) : Test := stampedUse "sharedA" file

/-- Another user of `stamped` that may run beside other shared users. -/
@[test] def sharedB (file : shared stamped) : Test := stampedUse "sharedB" file

/-- A user of `stamped` that fails when `failing` is `true`. -/
@[test] def failsWithFixture (_ : stamped) (failing : failing) : Test := do
  if failing then fail "it failed with its fixture"

/-- Prints whether the teardown received a value, which it does when the setup produced one. -/
def reportTeardown (value? : Option String) : FixtureM Unit :=
  IO.println s!"teardown received {value?.getD "no value"}"

/-- A fixture whose setup fails when `failing` is `true`. -/
@[fixture, expose]
def setupFails (failing : failing) : Fixture where
  type := String
  toString := id
  fromString := some
  setup := do
    if failing then fail "the setup failed on request"
    return "ready"
  teardown := reportTeardown

/-- A test that uses `setupFails`. -/
@[test] def afterSetupFailure (value : setupFails) : Test := IO.println s!"received {value}"

/--
A fixture whose prepare fails the first time it runs when `failing` is `true`, and succeeds after
that. Its value is a directory where it notes that it has failed.
-/
@[fixture, expose]
def prepareFails (failing : failing) : Fixture where
  type := String
  toString := id
  fromString := some
  setup := do
    let dir ← IO.FS.createTempDir
    return dir.toString
  prepare dir := do
    let mark : System.FilePath := dir / "failed-once"
    if failing && !(← mark.pathExists) then
      IO.FS.writeFile mark ""
      fail "the prepare failed on request"
  teardown dir? := do
    if let some dir := dir? then IO.FS.removeDirAll dir

/-- The first of two tests that use `prepareFails`. -/
@[test] def afterPrepareFailureA (_ : prepareFails) : Test := IO.println "ran A"

/-- The second of two tests that use `prepareFails`. -/
@[test] def afterPrepareFailureB (_ : prepareFails) : Test := IO.println "ran B"

/-- A fixture whose teardown fails when `failing` is `true`. -/
@[fixture, expose]
def teardownFails (failing : failing) : Fixture where
  type := String
  toString := id
  fromString := some
  setup := return "ready"
  teardown _ := do
    if failing then fail "the teardown failed on request"

/-- A test that uses `teardownFails`. -/
@[test] def beforeTeardownFailure (_ : teardownFails) : Test := pure ()

/-- A fixture whose value joins a greeting, from a setting, and the value of `stamped`. -/
@[fixture, expose]
def dependent (word : ErrataTests.Settings.greeting) (file : stamped) : Fixture where
  type := String
  toString := id
  fromString := some
  setup := return s!"{word} and {file}"

/-- Prints the value of `dependent`. -/
@[test] def usesDependent (value : dependent) : Test := IO.println s!"received {value}"

/-- A fixture whose setup sleeps for `sleepMs` milliseconds, and whose teardown says what it got. -/
@[fixture, expose]
def slowSetup (ms : sleepMs) : Fixture where
  type := String
  toString := id
  fromString := some
  setup := do
    IO.println "setting up"
    IO.sleep ms.toUInt32
    return "slept"
  teardown := reportTeardown

/-- A test that uses `slowSetup`. -/
@[test] def afterSlowSetup (_ : slowSetup) : Test := pure ()

/--
A fixture whose phases ask for three threads, and whose setup prints its thread grant and
`LEAN_NUM_THREADS`.
-/
@[fixture (threads := 3), expose]
def threaded : Fixture where
  type := Nat
  toString := toString
  fromString := String.toNat?
  setup := do
    let n := (← read).threads
    IO.println s!"threads: {n}; LEAN_NUM_THREADS: {(← IO.getEnv "LEAN_NUM_THREADS").getD ""}"
    return n

/-- A test that uses `threaded`, and receives its grant as the value. -/
@[test] def usesThreaded (n : threaded) : Test := assertTrue (n ≥ 1)

end ErrataTests.Resources
