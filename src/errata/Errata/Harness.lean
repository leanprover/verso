/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The Lean harness: the main of a library's test executable. It lists the library's tests, runs one of
them by name and writes the protocol's records to the file the runner names, and runs the helpers
that its tests start.
-/
module

public import Errata.Runner
public import Errata.Helpers
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
    <test-executable> errata-run <out> <test-name> [setting:NAME=VALUE]...\n  \
    <test-executable> errata-helper <helper-name> [ARG]...\n\n\
    Several errata-list and errata-run invocations may be chained, each separated by a ';' \
    argument. The Errata runner starts test executables, and tests start their helpers. To run the tests, \
    run the Errata driver, which is usually `lake test`."

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
The setting that the Lean harness reads itself, which no test declares: {lit}`updateGolden`, which
rewrites golden files when it is {lit}`true`. The runner passes it for {lit}`--update-golden`.
-/
def harnessSettings : List String := ["updateGolden"]

/--
The context for a test run with the given settings. The harness's own setting configures it. Tests
reach their helpers through this test executable's {lit}`errata-helper` mode.
-/
def contextOf (settings : Array (String × String)) : IO TestContext := do
  let lookup (name : String) : Option String := (settings.findRev? (·.1 == name)).map (·.2)
  let ctx ← mkContext (updateGolden := lookup "updateGolden" == some "true")
  return { ctx with helperCommand := some #[(← IO.appPath).toString, "errata-helper"] }

/--
The settings that the tests in {name}`entries` take, each once, in the order in which the entries
first name them.
-/
def reachedSettings (entries : Array TestEntry) : Array SettingRef := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut out := #[]
  for e in entries do
    for s in e.settings do
      unless seen.contains s.name do
        seen := seen.insert s.name
        out := out.push s
  return out

/--
Writes the inventory: the protocol record, a setting record for each setting that the tests take,
with its description and its declared default, and then a test record for each entry, with its
tags and the settings it takes.
-/
def writeInventory (entries : Array TestEntry) (out : IO.FS.Handle) : IO Unit := do
  writeRecord out (.protocol (some version))
  for s in reachedSettings entries do
    writeRecord out (.setting (some s.name) s.description? s.default?)
  for e in entries do
    writeRecord out <| .test {
      name? := some e.name, path? := some e.path, file? := some e.location.file
      line? := some e.location.startPos.line, col? := some e.location.startPos.column
      description? := e.docstring?
      tags? := if e.tags.isEmpty then none else some e.tags
      settings? := if e.settings.isEmpty then none
        else some (e.settings.map fun s => { name := s.name, optional := s.optional })
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
status {lit}`expectedFailure`. The test receives {name}`settings`. The result is the exit code:
{lit}`0` for a pass and {lit}`1` otherwise.
-/
def runTest (entry : TestEntry) (ctx : TestContext) (settings : Array (String × String))
    (out : IO.FS.Handle) : IO UInt32 := do
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
  let results ← runEntry ctx entry settings
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

/-- The helpers, indexed by name. -/
def helpersByName (helpers : Array Helper) : Std.HashMap String Helper :=
  helpers.foldl (init := {}) fun m h => m.insert h.name h

/--
Runs the helper named {name}`name` from {name}`helpers` with {name}`args`, with the process's own
standard streams, and returns its exit code. For an unknown name, it writes a message to standard
error and returns {lit}`2`.
-/
def runHelperNamed (helpers : Array Helper) (name : String) (args : List String) : IO UInt32 := do
  match (helpersByName helpers).get? name with
  | some helper => helper.run args
  | none =>
    IO.eprintln s!"no helper is named {name}"
    return 2

/--
Carries out one invocation of a test executable, and returns its exit code. {lit}`errata-list`
writes the inventory; {lit}`errata-run` runs the named test, with the settings that follow its name;
{lit}`errata-helper` runs the named helper from {name}`helpers` with the arguments that follow its
name; anything else prints the usage message.
-/
def dispatch (entries : Array TestEntry) (args : List String) (helpers : Array Helper := #[]) :
    IO UInt32 := do
  match args with
  | "errata-helper" :: name :: rest => runHelperNamed helpers name rest
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
    let settings := settingsOf rest
    let ctx ← contextOf settings
    runTest entry ctx (settings.filter (!harnessSettings.contains ·.1)) out
  | _ =>
    IO.eprintln usage
    return 2

/-- The invocations of a chain: the arguments, split at each {lit}`;` argument. -/
def chainLinks (args : List String) : List (List String) :=
  let (last, done) := args.foldl (init := ([], [])) fun (cur, done) a =>
    if a == ";" then ([], done ++ [cur]) else (cur ++ [a], done)
  done ++ [last]

/--
Performs the invocations of a chain in order with {name}`dispatch`, stopping at the first that
exits non-zero, and returns the exit code of the last that ran.
-/
def dispatchChain (entries : Array TestEntry) (links : List (List String))
    (helpers : Array Helper := #[]) : IO UInt32 := do
  let mut code := 0
  for link in links do
    code ← dispatch entries link helpers
    unless code == 0 do break
  return code

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
then a {lit}`setting` record for each setting that the tests take, with its docstring as its
description and its declared default, then a {lit}`test` record per test with its fully qualified
name, the name's components as its path, its file, line, and column, its docstring as its
description, its tags, and the settings it takes.

{lit}`errata-run <out> <name> [setting:NAME=VALUE]...` runs the test with that name and writes its
records to {lit}`out`. It exits with {lit}`0` when the test passes and {lit}`1` otherwise. The test
receives the settings, and parses the values of those it takes; a missing mandatory setting or a
value that a setting's parser rejects ends the test with an error. The runner passes
{lit}`setting:updateGolden=true` for {lit}`--update-golden`, which the harness reads itself, with no
declaration, to rewrite golden files. When the environment variable {lit}`ERRATA_LIFELINE` is
{lit}`1`, as the runner sets it, the executable's standard input is its lifeline: when the pipe
closes, the executable ends its own process group and exits. Otherwise the command runs by hand with
any standard input, {lit}`/dev/null` included. The test itself reads an empty standard input.

The runner also sets {lit}`ERRATA_DIR` to the directory of Errata's sources, where the shell
harness lives, and {lit}`ERRATA_RUN_ID` to the run's identifier, which is the same for every process
of one run and differs between runs, so that tests can do work once per run. Tests read both from
their environments.

{lit}`errata-helper <name> [ARG]...` runs the helper in {name}`helpers` with that name, passing it the
arguments that follow, and exits with the helper's exit code, which the process that started it sees
modulo 256, as the operating system reports it. The helper runs with the process's own standard
input, output, and error. This mode belongs to the Lean harness, and
{name (scope := "Errata")}`runHelper` starts it from inside a test. For an unknown name, the
executable writes a message to standard error and exits with {lit}`2`.

Several {lit}`errata-list` and {lit}`errata-run` invocations may be chained, each separated by a
{lit}`;` argument. The executable performs them in order, stops at the first that exits non-zero,
and exits with the status of the last that ran.

With any other arguments, the executable prints its usage and exits with {lit}`2`.
-/
def main (entries : Array TestEntry) (args : List String) (helpers : Array Helper := #[]) :
    IO UInt32 := do
  match args with
  | "errata-helper" :: _ => dispatch entries args helpers
  | _ =>
    let links := chainLinks args
    unless links.any (·.head? == some "errata-run") do
      return ← dispatchChain entries links helpers
    -- The read blocks on a thread of its own, which it holds for the length of the run.
    if (← IO.getEnv "ERRATA_LIFELINE") == some "1" then
      let _ ← IO.asTask (prio := .dedicated) (exitWhenStdinCloses (← IO.getStdin))
    -- The main thread, where the test runs, reads an empty standard input from here on.
    discard <| IO.setStdin (IO.FS.Stream.ofBuffer (← IO.mkRef {}))
    let code ← try dispatchChain entries links catch e => do
      IO.eprintln s!"uncaught exception: {e}"
      pure 1
    -- The thread that reads standard input runs until the pipe closes, and a Lean program that
    -- returns from `main` waits for its threads, so the process is ended here.
    exitNow code.toUInt8
