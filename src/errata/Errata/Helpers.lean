/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Helpers: functions in a test library that a test runs as a subprocess of its own test executable,
for behavior that only a separate process shows.
-/
module

public import Errata.TestM
import Errata.ProcessControl

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/--
A helper that a test executable runs by name in its {lit}`errata-helper` mode: its fully qualified
declaration name and the function that {lit}`@[test_helper]` marks.
-/
structure Helper where
  /-- The helper's fully qualified declaration name. -/
  name : String
  /-- The helper itself, which receives the arguments after its name and returns the exit code. -/
  run : List String → IO UInt32

/--
Runs the helper {name}`helper` as a subprocess of the test executable, with {name}`args` as its
arguments, and returns its exit code and what it wrote to standard output and standard error.
{name}`env` adds variables to the environment the subprocess inherits, or removes them when their
value is {lean}`none`. {name}`stdin` is written to the subprocess's standard input, which is then
closed.

The exit code is the helper's result modulo 256, as the operating system reports it. The output is
decoded as UTF-8; when it is not valid UTF-8, each byte of {lit}`0x80` or above becomes
{lit}`U+FFFD`.

The helper is named by a name literal with two backquotes, so a name that refers to no declaration
is an error at elaboration time. A test that runs a helper must run under the test
executable that the Lean harness builds, which sets how helpers are reached; elsewhere the test ends
with an error.
-/
def runHelper (helper : Lean.Name) (args : List String)
    (env : Array (String × Option String) := #[]) (stdin : String := "") :
    TestM IO.Process.Output := do
  let some command := (← read).helperCommand
    | throwThe IO.Error <| .userError s!"the helper {helper} cannot run: helpers run only under \
        the compiled test executable"
  let some cmd := command[0]?
    | throwThe IO.Error <| .userError s!"the helper {helper} cannot run: the command that runs \
        helpers is empty"
  let child ← IO.Process.spawn {
    cmd
    args := command.extract 1 command.size ++ #[helper.toString] ++ args.toArray
    env
    stdin := .piped, stdout := .piped, stderr := .piped
  }
  let (input, child) ← child.takeStdin
  -- Both streams are read as bytes on threads of their own, so neither pipe fills while the other is
  -- read or while standard input is written.
  let outTask ← IO.asTask (prio := .dedicated) child.stdout.readBinToEnd
  let errTask ← IO.asTask (prio := .dedicated) child.stderr.readBinToEnd
  -- A write to a helper that exits without reading all of its input fails with a broken pipe. The
  -- failure is dropped, and the helper's exit code and output are returned as for any other helper.
  let write : IO Unit := do
    unless stdin.isEmpty do
      input.putStr stdin
      input.flush
  let writeQuietly : IO Unit := tryCatch write fun _ => pure ()
  writeQuietly
  -- The helper's standard input closes when its handle is released after its last use above, so a
  -- helper that reads to the end of its input finishes.
  let text (task : Task (Except IO.Error ByteArray)) : IO String := do
    match ← IO.wait task with
    | .ok bytes => return ProcessControl.decodeLine bytes
    | .error e => return s!"<the stream could not be read: {e}>"
  let stdout ← text outTask
  let stderr ← text errTask
  let exitCode ← child.wait
  return { exitCode, stdout, stderr }
