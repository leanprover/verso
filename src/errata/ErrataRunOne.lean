/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata
public import Std.Time
public meta import Lean

open Lean Meta

/-- The current wall-clock time in milliseconds since the Unix epoch. -/
def nowMs : IO Nat :=
  return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.toInt.toNat

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
    -- The test's own source range, which a failure with no more specific place is reported at.
    let range ← findDeclarationRanges? test.name
    let location : Errata.Location := {
      file := test.file
      startPos := (range.map (·.range.pos)).getD ⟨0, 0⟩
      endPos := (range.map (·.range.endPos)).getD ⟨0, 0⟩
    }
    return {
      package := "", moduleName := module.toString
      test := Errata.testNameBelow module (privateToUserName test.name)
      location, docstring? := test.docstring?, run := act
    }

/-- Writes one JSON protocol line to the runner's real stdout and flushes it for prompt streaming. -/
private def emitLine (out : IO.FS.Stream) (key : String) (value : Json) : IO Unit := do
  out.putStr ((Json.mkObj [(key, value)]).compress ++ "\n")
  out.flush

/--
Imports the module, runs the test named by the declaration, and streams its result. The seed for
property tests is the third argument, or is drawn when there is none.
-/
unsafe def runImpl (args : List String) : IO UInt32 := do
  let usage : IO UInt32 := do
    IO.eprintln "usage: errata-run-one <module-json> <decl-json> [seed]"
    return 2
  let (modStr, declStr, seed?) ←
    match args with
    | [modStr, declStr] => pure (modStr, declStr, none)
    | [modStr, declStr, seedStr] =>
      match seedStr.toNat? with
      | some seed => pure (modStr, declStr, some seed)
      | none => return ← usage
    | _ => return ← usage
  -- A name is either encoded by `nameToJson` or given in its dotted form.
  let parseName (s : String) : IO Name :=
    match Json.parse s with
    | .ok j => IO.ofExcept (Errata.nameOfJson? j)
    | .error _ => pure s.toName
  let targetModule ← parseName modStr
  let declName ← parseName declStr
  -- The runner's real stdout carries the JSON protocol; the test's own output is captured by
  -- `runEntryOutcome` and forwarded as chunk lines, so this handle is taken before that redirection.
  let out ← IO.getStdout
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
  let openResults ← IO.mkRef #[Errata.ResultNode.root]
  let nextResult ← IO.mkRef (Errata.ResultNode.root + 1)
  let innermost : IO Nat := return (← openResults.get).back?.getD Errata.ResultNode.root
  let sink := fun (o : Errata.Output) => do
    let chunk := { Errata.OutputChunk.ofOutput o with time := ← nowMs, result := ← innermost }
    emitLine out "chunk" (toJson chunk)
  let watch := fun (ev : Errata.ResultEvent) => do
    match ev with
    | .started path =>
      let parent ← innermost
      let id ← nextResult.modifyGet fun n => (n, n + 1)
      openResults.modify (·.push id)
      let started : Errata.ResultNode := { id, parent, name := path.back?.getD "" }
      emitLine out "result" (toJson started)
    | .finished r =>
      let id ← innermost
      openResults.modify (·.pop)
      -- The result's output already went out as chunks while it ran, so the report of the finished
      -- result leaves it out.
      let node := { Errata.ResultNode.ofResult id (← innermost) entry.location r with output := #[] }
      emitLine out "result" (toJson node)
  let outcome ← Errata.runEntryOutcome entry (seed? := seed?) (sink := sink) (watch := watch)
  -- The test's own result is reported once the test ends, with its verdict and message.
  if let some root := outcome.root? then
    emitLine out "result" (toJson { root with output := #[] })
  emitLine out "outcome" (toJson outcome)
  return 0

@[implemented_by runImpl]
opaque run (args : List String) : IO UInt32

/-- Runs a single Errata test, streaming its output and final outcome as JSON lines to stdout. -/
public def main (args : List String) : IO UInt32 := run args
