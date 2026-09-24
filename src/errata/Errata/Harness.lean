/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The Lean harness: the main of a library's test executable, which lists the library's tests and runs
one of them by name, writing the protocol's records to the file the runner names.
-/
module

public import Errata.Runner
public import Errata.Protocol
public import Errata.ProcessControl
public import Std.Data.HashMap

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata.Harness

open Protocol

/-- The usage message of a test executable. -/
def usage : String :=
  "usage:\n  \
    <test-executable> errata-list <out>\n  \
    <test-executable> errata-run <out> <test-name> [setting:NAME=VALUE]...\n\n\
    The Errata runner starts test executables. To run the tests, run the Errata driver, \
    which is usually `lake test`."

/--
The settings among a test executable's arguments: each {lit}`setting:NAME=VALUE`, split at the first
{lit}`=`, in order. Arguments of any other form are ignored.
-/
def settingsOf (args : List String) : Array (String × String) :=
  args.toArray.filterMap fun arg => do
    let rest ← arg.dropPrefix? "setting:"
    match rest.copy.splitOn "=" with
    | [] => none
    | [name] => some (name, "")
    | name :: value => some (name, "=".intercalate value)

/--
The settings that the Lean harness itself reads: {lit}`seed`, the seed for property tests;
{lit}`updateGolden`, which rewrites golden files when it is {lit}`true`; and {lit}`ignorePanics`,
which keeps a check's status unchanged when the check panics, when it is {lit}`true`.
-/
def harnessSettings : List String := ["seed", "updateGolden", "ignorePanics"]

/--
The context for a test run with the given settings. The harness's own settings configure it, and
every other setting becomes a test option, read with {name}`option?` and {name}`flag`. Without a
seed, one is chosen at random.
-/
def contextOf (settings : Array (String × String)) : IO (Except String Context) := do
  let lookup (name : String) : Option String := (settings.findRev? (·.1 == name)).map (·.2)
  let seed? ← match lookup "seed" with
    | none => pure (Except.ok none)
    | some s => match s.toNat? with
      | some n => pure (.ok (some n))
      | none => pure (.error s!"the setting seed={s} is not a natural number")
  let seed? ← match seed? with
    | .ok s => pure s
    | .error e => return .error e
  let options : OptionMap := settings.foldl (init := {}) fun acc (name, value) =>
    if harnessSettings.contains name then acc
    else acc.insert name ((acc.getD name #[]).push value)
  let ctx ← mkContext (updateGolden := lookup "updateGolden" == some "true")
    (options := options) (seed := seed?) (ignorePanics := lookup "ignorePanics" == some "true")
  return .ok ctx

/-- Writes the inventory: the protocol record, then a test record for each entry. -/
def writeInventory (entries : Array TestEntry) (out : IO.FS.Handle) : IO Unit := do
  writeRecord out (.protocol (some version))
  for e in entries do
    writeRecord out <| .test {
      name? := some e.name, path? := some e.path, file? := some e.location.file
      line? := some e.location.startPos.line, col? := some e.location.startPos.column
      description? := e.docstring?
    }

/-- The record fields for the status of a finished check. -/
private def statusInfo : Errata.Status → Protocol.Status × Option String × Option String × Option Span
  | .pass => (.pass, none, none, none)
  | .fail f => (.fail, some f.message, f.detail?, f.location?.map Span.ofLocation)
  | .error m => (.error, some m, none, none)

/--
Runs one test, writing its records to {name}`out`: {lit}`start` as its body begins, an
{lit}`output` record for each fragment it writes, a {lit}`result` record as each named result starts
and again as it finishes, and a {lit}`verdict` at the end. Each output record names the named result
that was open when the fragment was written, {lit}`0` for the test itself. A named result that failed
within an {name (scope := "Errata.TestM")}`expectFail` that expected it is reported again with the
status {lit}`expectedFailure`. The result is the exit code: {lit}`0` for a pass and {lit}`1`
otherwise.
-/
def runTest (entry : TestEntry) (ctx : Context) (out : IO.FS.Handle) : IO UInt32 := do
  writeRecord out (.start (some (← nowMs)))
  -- The results that are open, innermost last, and the identifier of the next one. Output and
  -- result events arrive in the order the test produced them, so the result that wrote a fragment
  -- is the innermost one open when it arrives.
  let openResults ← IO.mkRef #[0]
  let nextResult ← IO.mkRef 1
  let innermost : IO Nat := return (← openResults.get).back?.getD 0
  -- For each `expectFail` whose action is running, innermost last, the reports of the named results
  -- that failed within it so far.
  let expecting ← IO.mkRef (#[] : Array (Array ResultInfo))
  let report (info : ResultInfo) : IO Unit := writeRecord out (.result info)
  let saveOutput (o : Output) : IO Unit := do
    let (stream, text) := match o with
      | .stdout s => ("stdout", s)
      | .stderr s => ("stderr", s)
    writeRecord out (.output (some stream) (some text) (some (← nowMs)) (some (← innermost)))
  let watch (ev : ResultEvent) : IO Unit := do
    match ev with
    | .started path =>
      let parent ← innermost
      let id ← nextResult.modifyGet fun n => (n, n + 1)
      openResults.modify (·.push id)
      report { id? := some id, parent? := some parent, name? := path.back? }
    | .finished r =>
      let id ← innermost
      openResults.modify (·.pop)
      let (status, message?, detail?, location?) := statusInfo r.status
      let info : ResultInfo := {
        id? := some id, parent? := some (← innermost), name? := r.resultPath.back?
        status? := some status, message?, detail?, location?, durationMs? := some r.durationMs
      }
      if status == .fail then
        expecting.modify fun frames =>
          if frames.isEmpty then frames else frames.modify (frames.size - 1) (·.push info)
      report info
    | .expectFailStarted => expecting.modify (·.push #[])
    | .expectFailFinished failuresExpected =>
      let failed ← expecting.modifyGet fun frames => (frames.back?.getD #[], frames.pop)
      if failuresExpected then
        for info in failed do
          report { info with status? := some .expectedFailure }
      else
        -- An error escaped the action, so its failures stay in the test's results, where an
        -- enclosing `expectFail` can still expect them.
        expecting.modify fun frames =>
          if frames.isEmpty then frames else frames.modify (frames.size - 1) (· ++ failed)
  let ctx := { ctx with writeOutput := some saveOutput, watchResults := some watch }
  let start ← IO.monoMsNow
  let results ← runEntry ctx entry
  let durationMs := (← IO.monoMsNow) - start
  let status := (results[0]?.map (·.status)).getD .pass
  let (st, message?, detail?, location?) := statusInfo status
  writeRecord out <|
    .verdict { status? := some st, message?, detail?, location?, durationMs? := some durationMs }
  return if status.isSuccess then 0 else 1

/-- The position of each entry, by its name. -/
def indexByName (entries : Array TestEntry) : Std.HashMap String Nat := Id.run do
  let mut index := {}
  for h : i in [0 : entries.size] do
    index := index.insert entries[i].name i
  return index

/--
Carries out one invocation of a test executable, and returns its exit code. {lit}`errata-list`
writes the inventory; {lit}`errata-run` runs the named test, with the settings that follow its name;
anything else prints the usage message.
-/
def dispatch (entries : Array TestEntry) (args : List String) : IO UInt32 := do
  match args with
  | ["errata-list", outPath] =>
    let out ← IO.FS.Handle.mk outPath .append
    writeInventory entries out
    return 0
  | "errata-run" :: outPath :: name :: rest =>
    let out ← IO.FS.Handle.mk outPath .append
    writeRecord out (.protocol (some version))
    let some entry := (indexByName entries).get? name |>.bind (entries[·]?)
      | writeRecord out (.verdict { status? := some .error, message? := some s!"no test is named {name}" })
        return 1
    match ← contextOf (settingsOf rest) with
    | .error msg =>
      writeRecord out (.verdict { status? := some .error, message? := some msg })
      return 1
    | .ok ctx => runTest entry ctx out
  | _ =>
    IO.eprintln usage
    return 2

/-- Flushes the standard streams and ends the process with {name}`code`. -/
def exitNow (code : UInt8) : IO α := do
  try (← IO.getStdout).flush catch _ => pure ()
  try (← IO.getStderr).flush catch _ => pure ()
  -- `forceExit` skips the C library's cleanup of its streams, which can wait on the lock that a
  -- blocked read of standard input holds.
  IO.Process.forceExit code

/--
Ends the process group of this test executable, and exits with {lit}`1`, once its lifeline closes.
The lifeline is the executable's standard input. The process that started the executable holds the
other end of that pipe, which closes when that process exits, however it exits.
-/
def exitWhenStdinCloses (parentIn : IO.FS.Stream) : IO Unit := do
  -- Each read blocks until a line arrives or the pipe closes, so the thread sleeps for the length of
  -- the run. The process that starts the test executable leaves the pipe empty, so the first read
  -- returns when the pipe closes; a line that arrives anyway is skipped.
  repeat
    if (← parentIn.getLine).isEmpty then break
  try ProcessControl.killOwnGroup catch _ => pure ()
  exitNow 1

/--
The main of a test executable made by the Lean harness, over the tests in {name}`entries`.

{lit}`errata-list <out>` writes the inventory to the file {lit}`out`: the {lit}`protocol` record,
then a {lit}`test` record per test with its fully qualified name, the name's components as its path,
its file, line, and column, and its docstring as its description.

{lit}`errata-run <out> <name> [setting:NAME=VALUE]...` runs the test with that name and writes its
records to {lit}`out`. It exits with {lit}`0` when the test passes and {lit}`1` otherwise. The runner
passes its own options to the test as settings: {lit}`setting:seed=N` is the seed for property tests,
{lit}`setting:updateGolden=true` rewrites golden files, and {lit}`setting:ignorePanics=true` leaves
a check's status unchanged when the check panics. Every other setting is a test option, read with
{name}`option?` and {name}`flag`. When the environment variable {lit}`ERRATA_LIFELINE` is {lit}`1`,
as the runner sets it, the executable's standard input is its lifeline: when the pipe closes, the
executable ends its own process group and exits. Otherwise the command runs by hand with any
standard input, {lit}`/dev/null` included. The test itself reads an empty standard input.

With any other arguments, the executable prints its usage and exits with {lit}`2`.
-/
def main (entries : Array TestEntry) (args : List String) : IO UInt32 := do
  match args with
  | "errata-run" :: _ =>
    -- The read blocks on a thread of its own, which it holds for the length of the run.
    if (← IO.getEnv "ERRATA_LIFELINE") == some "1" then
      let _ ← IO.asTask (prio := .dedicated) (exitWhenStdinCloses (← IO.getStdin))
    -- The main thread, where the test runs, reads an empty standard input from here on.
    discard <| IO.setStdin (IO.FS.Stream.ofBuffer (← IO.mkRef {}))
    let code ← try dispatch entries args catch e => do
      IO.eprintln s!"uncaught exception: {e}"
      pure 1
    -- The thread that reads standard input runs until the pipe closes, and a Lean program that
    -- returns from `main` waits for its threads, so the process is ended here.
    exitNow code.toUInt8
  | _ => dispatch entries args
