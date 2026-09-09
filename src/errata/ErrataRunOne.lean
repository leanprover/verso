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
Evaluates the test named by {lean}`declName`, defined in {lean}`module`, to a runnable action.

The action is the definition that {lit}`@[test]` compiled beside the test, reached through
{lit}`import all` of its module so a module-private test is still reachable.
-/
unsafe def evalTestM (module declName : Name) : CoreM (Errata.TestM Unit × Option String) :=
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
    return (act, ← findDocString? env test.name)

/-- Writes one JSON protocol line to the runner's real stdout and flushes it for prompt streaming. -/
private def emitLine (out : IO.FS.Stream) (key : String) (value : Json) : IO Unit := do
  out.putStr ((Json.mkObj [(key, value)]).compress ++ "\n")
  out.flush

/-- Imports {lean}`targetModule`, runs the test named by {lean}`declName`, and streams its result. -/
unsafe def runImpl (args : List String) : IO UInt32 := do
  let [modStr, declStr] := args
    | IO.eprintln "usage: errata-run-one <module> <decl-json>"; return 2
  let targetModule := modStr.toName
  let declName ←
    match Json.parse declStr with
    | .ok j => IO.ofExcept (Errata.nameOfJson? j)
    | .error _ => pure declStr.toName
  -- The runner's real stdout carries the JSON protocol; the test's own output is captured by
  -- `runValue` and forwarded as chunk lines, so this handle is taken before that redirection.
  let out ← IO.getStdout
  initSearchPath (← findSysroot)
  if let some leanPath ← IO.getEnv "LEAN_PATH" then
    searchPathRef.modify (· ++ System.SearchPath.parse leanPath)
  enableInitializersExecution
  let env ← importModules
    #[{ module := targetModule, importAll := true }, { module := `Errata }] {} (loadExts := true)
  let coreCtx : Core.Context := { fileName := "<errata-run-one>", fileMap := default }
  let ((act, doc?), _) ← (evalTestM targetModule declName).toIO coreCtx { env }
  -- Mark when the test body starts, so the widget shows output offsets within the test itself,
  -- excluding the build and module-import time before this point.
  emitLine out "exec" (toJson (← nowMs))
  let sink := fun (o : Errata.Output) => do
    let chunk := { Errata.OutputChunk.ofOutput o with time := ← nowMs }
    emitLine out "chunk" (toJson chunk)
  let outcome ← Errata.runValue default act (sink := sink)
  emitLine out "outcome" (toJson { outcome with description? := doc? })
  return 0

@[implemented_by runImpl]
opaque run (args : List String) : IO UInt32

/-- Runs a single Errata test, streaming its output and final outcome as JSON lines to stdout. -/
public def main (args : List String) : IO UInt32 := run args
