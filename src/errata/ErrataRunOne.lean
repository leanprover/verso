/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata
public import Errata.WidgetRunner
public meta import Lean

open Lean Meta
open Errata.Widget
open Errata.Widget.Runner (nowMs)

/--
Evaluates the test named by {lean}`declName`, defined in {lean}`module`, to a test entry, as test
discovery builds one.

The entry's action is the definition that {lit}`@[test]` compiled beside the test, reached through
{lit}`import all` of its module so a module-private test is still reachable. The runner has no
package name to give the entry, so that field is empty.
-/
unsafe def evalTestEntry (module declName : Name) : CoreM Errata.TestEntry :=
  MetaM.run' do
    let env ← getEnv
    let some idx := env.getModuleIdx? module
      | throwError "module `{module}` is not imported"
    -- The widget passes the declaration's real name, but a module-private test is mangled, so fall
    -- back to matching the user-facing name when the exact name is absent.
    let some test := (Errata.testExt.getModuleEntries env idx).find? fun t =>
        t.name == declName || privateToUserName t.name == declName
      | throwError "`{declName}` is not a test in `{module}`"
    let ty := mkApp (mkConst ``Errata.TestM) (mkConst ``Unit)
    let act ← evalExpr (Errata.TestM Unit) ty (mkConst test.run) (safety := .unsafe)
    let location ← Errata.testLocation test
    return {
      package := "", moduleName := module.toString
      test := Errata.testNameBelow module (privateToUserName test.name)
      location, docstring? := test.docstring?, run := act
    }

/-- Writes one JSON protocol line to the protocol file and flushes it for prompt streaming. -/
private def emitLine (out : IO.FS.Handle) (key : String) (value : Json) : IO Unit := do
  out.putStr ((Json.mkObj [(key, value)]).compress ++ "\n")
  out.flush

/-- Flushes the runner's standard output and standard error, then ends the process with `code`. -/
private def exitNow (code : UInt8) : IO α := do
  try (← IO.getStdout).flush catch _ => pure ()
  try (← IO.getStderr).flush catch _ => pure ()
  -- `forceExit` skips the C library's cleanup of its streams, which can wait on the lock that a
  -- blocked read of standard input holds.
  IO.Process.forceExit code

/--
Ends the runner once its standard input reaches its end, and says so on standard error. The process
that starts the runner holds the other end of that pipe, which closes when that process exits,
however it exits.
-/
private def exitWhenStdinCloses (parentIn : IO.FS.Stream) : IO Unit := do
  -- Each read blocks until a line arrives or the pipe closes, so the thread sleeps for the length of
  -- the run. The process that starts the runner leaves the pipe empty, so the first read returns
  -- when the pipe closes; a line that arrives anyway is skipped.
  repeat
    if (← parentIn.getLine).isEmpty then break
  try IO.eprintln "errata-run-one: standard input closed, so the run ends" catch _ => pure ()
  exitNow 1

/--
Imports the test's module, runs the test, and appends its output and results to the protocol file as
JSON lines. The usage message lists the arguments. The runner exits when its standard input closes,
which happens when the file worker that started it exits.
-/
unsafe def runImpl (args : List String) : IO UInt32 := do
  let usage : IO UInt32 := do
    IO.eprintln
      "usage: errata-run-one <protocol-file> <module-json> <decl-json> <options-json> [seed] < pipe"
    return 2
  let (protocolPath, modStr, declStr, optionsStr, seed?) ←
    match args with
    | [protocolPath, modStr, declStr, optionsStr] =>
      pure (protocolPath, modStr, declStr, optionsStr, none)
    | [protocolPath, modStr, declStr, optionsStr, seedStr] =>
      match seedStr.toNat? with
      | some seed => pure (protocolPath, modStr, declStr, optionsStr, some seed)
      | none => return ← usage
    | _ => return ← usage
  let optionList ←
    match Json.parse optionsStr >>= fromJson? (α := Array Runner.TestOption) with
    | .ok optionList => pure optionList
    | .error e =>
      IO.eprintln s!"errata-run-one: the options could not be read: {e}"
      return 2
  let options : Errata.OptionMap := optionList.foldl (init := {}) fun acc opt =>
    acc.insert opt.name ((acc.getD opt.name #[]).push opt.value)
  -- The read blocks on a thread of its own, which it holds for the length of the run.
  let _ ← IO.asTask (prio := .dedicated) (exitWhenStdinCloses (← IO.getStdin))
  -- The main thread, where the test runs, reads an empty standard input from here on.
  discard <| IO.setStdin (IO.FS.Stream.ofBuffer (← IO.mkRef {}))
  -- A name is either encoded by `nameToJson` or given in its dotted form.
  let parseName (s : String) : IO Name :=
    match Json.parse s with
    | .ok j => IO.ofExcept (Errata.nameOfJson? j)
    | .error _ => pure s.toName
  let targetModule ← parseName modStr
  let declName ← parseName declStr
  -- The test's own output is captured by `runEntryOutcome` and forwarded as chunk lines. Anything
  -- else written to stdout, such as a subprocess's output, goes to the runner's real stdout.
  let out ← IO.FS.Handle.mk protocolPath .append
  -- The search path includes the directories in `LEAN_PATH`.
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules
    #[{ module := targetModule, importAll := true }, { module := `Errata }] {} (loadExts := true)
  let coreCtx : Core.Context := { fileName := "<errata-run-one>", fileMap := default }
  let (entry, _) ← (evalTestEntry targetModule declName).toIO coreCtx { env }
  -- Mark when the test body starts, so the widget shows output offsets within the test itself,
  -- excluding the build and module-import time before this point.
  emitLine out "exec" (toJson (← nowMs))
  -- The results that are open, innermost last, and the identifier of the next one.
  -- Output and result events arrive in the order the test produced them, so the result that wrote
  -- a chunk is the innermost one open when it arrives.
  let openResults ← IO.mkRef #[Runner.ResultNode.root]
  let nextResult ← IO.mkRef (Runner.ResultNode.root + 1)
  let innermost : IO Nat := return (← openResults.get).back?.getD Runner.ResultNode.root
  -- For each `expectFail` whose action is running, innermost last, the reports of the named results
  -- that failed within it so far.
  let expecting ← IO.mkRef (#[] : Array (Array Runner.ResultNode))
  -- The lines of each source file that a location points into, read once for the run. The editor
  -- counts columns in UTF-16 code units, so every location the widget gets is counted that way.
  let sourceLines ← IO.mkRef (#[] : Array (System.FilePath × Option (Array String)))
  let linesOf (path : System.FilePath) : IO (Option (Array String)) := do
    if let some (_, lines) := (← sourceLines.get).find? (·.1 == path) then return lines
    let lines ←
      try some <$> IO.FS.lines path
      catch _ => pure none
    sourceLines.modify (·.push (path, lines))
    return lines
  -- The latest report of each result, by identifier. The results' output goes out as chunks, so the
  -- reports leave it out.
  let rootReport : Runner.ResultNode :=
    { id := Runner.ResultNode.root, parent := Runner.ResultNode.root, name := "" }
  let reports ← IO.mkRef #[rootReport]
  let report (node : Runner.ResultNode) : IO Unit := do
    reports.modify fun nodes =>
      if node.id < nodes.size then nodes.set! node.id node else nodes.push node
    emitLine out "result" (toJson node)
  let saveOutput := fun (o : Errata.Output) => do
    let chunk := { Runner.OutputChunk.ofOutput o with time := ← nowMs, result := ← innermost }
    emitLine out "chunk" (toJson chunk)
  let watch := fun (ev : Errata.ResultEvent) => do
    match ev with
    | .started path =>
      let parent ← innermost
      let id ← nextResult.modifyGet fun n => (n, n + 1)
      openResults.modify (·.push id)
      report { id, parent, name := path.back?.getD "" }
    | .finished r =>
      let id ← innermost
      openResults.modify (·.pop)
      let node := Runner.ResultNode.ofResult id (← innermost) entry.location r (withOutput := false)
      let node ← node.withUtf16Columns linesOf
      if node.status? == some .failed then
        expecting.modify fun frames =>
          if frames.isEmpty then frames else frames.modify (frames.size - 1) (·.push node)
      report node
    | .expectFailStarted => expecting.modify (·.push #[])
    | .expectFailFinished failuresExpected =>
      let failed ← expecting.modifyGet fun frames => (frames.back?.getD #[], frames.pop)
      if failuresExpected then
        -- The failures within the action were expected, so they are reported again as such.
        for node in failed do
          report { node with status? := some .expectedFailure }
      else
        -- An error escaped the action, so its failures stay in the test's results, where an
        -- enclosing `expectFail` can still expect them.
        expecting.modify fun frames =>
          if frames.isEmpty then frames else frames.modify (frames.size - 1) (· ++ failed)
  let outcome ← Runner.runEntryOutcome entry (seed? := seed?) (saveOutput := saveOutput) (watch := watch)
    (onlyOwnResult := true) (options := options)
  let outcome ← outcome.withUtf16Columns linesOf
  -- The test's own result is reported once the test ends, with its verdict and message.
  if let some root := outcome.root? then
    report { root with output := #[] }
  -- The outcome's results are the reports the widget was sent, with the identifiers and parents that
  -- the results were given as they started.
  emitLine out "outcome" (toJson { outcome with results := ← reports.get, options := optionList })
  return 0

@[implemented_by runImpl]
opaque run (args : List String) : IO UInt32

/--
Runs a single Errata test, streaming its output and final outcome as JSON lines to the protocol
file, and ends the process with the run's exit code.
-/
public def main (args : List String) : IO UInt32 := do
  let code ← try run args catch e => do
    IO.eprintln s!"uncaught exception: {e}"
    pure 1
  -- The thread that reads standard input runs until the pipe closes, and a Lean program that
  -- returns from `main` waits for its threads, so the runner ends the process itself.
  exitNow code.toUInt8
