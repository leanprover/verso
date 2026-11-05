/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso

/-!
Helpers for tests that elaborate a {lit}`#doc` command from a string with Lean's command loop. They
show each message with the number of the command that reported it. Command 0 is the {lit}`#doc`
command itself, and command {lit}`k` is the document's {lit}`k`-th top-level block.
-/

namespace Verso.Tests.DocCommandInput

open Lean Elab Command
open Verso.Doc

/-- Renders a message with its position. -/
def showMessage (m : Message) : IO String := do
  let severity := match m.severity with
    | .error => "error"
    | .warning => "warning"
    | .information => "info"
  return s!"{m.pos.line}:{m.pos.column}: {severity}: {← m.data.toString}"

/--
Elaborates {lit}`input` as the rest of a module, in the current environment. Returns the resulting
environment, and the snapshot of each command in order.
-/
def elabModuleCommands (input : String) :
    CommandElabM (Environment × Array Language.Lean.CommandParsedSnapshot) := do
  let inputCtx := Parser.mkInputContext input "Input.lean"
  let st ← IO.processCommandsIncrementally inputCtx {}
    (Command.mkState (← getEnv) {} (← getOptions)) none
  let mut snaps := #[]
  let mut snap := st.initialSnap
  repeat
    snaps := snaps.push snap
    match snap.nextCmdSnap? with
    | some next => snap := next.task.get
    | none => break
  return (st.commandState.env, snaps)

/-- The messages of the command whose snapshot is {lit}`snap`. -/
def commandMessages (snap : Language.Lean.CommandParsedSnapshot) : MessageLog :=
  Language.toSnapshotTree snap.elabSnap |>.getAll
    |>.map (·.diagnostics.msgLog) |>.foldl (· ++ ·) MessageLog.empty

/-- The info trees of the command whose snapshot is {lit}`snap`. -/
def commandInfoTrees (snap : Language.Lean.CommandParsedSnapshot) : Array InfoTree :=
  Language.toSnapshotTree snap.elabSnap |>.getAll |>.filterMap (·.infoTree?)

/--
Elaborates {lit}`input` as the rest of a module, in the current environment. Returns the resulting
environment, and each command's messages rendered with the command's number.
-/
def elabModuleRest (input : String) : CommandElabM (Environment × String) := do
  let (env, snaps) ← elabModuleCommands input
  let mut out := #[]
  for h : i in [0:snaps.size] do
    for m in (commandMessages snaps[i]).toArray do
      out := out.push s!"command {i}: {← showMessage m}"
  return (env, "\n".intercalate out.toList)

unsafe def evalDocUnsafe (env : Environment) (opts : Options) (n : Name) : IO (VersoDoc Genre.none) :=
  IO.ofExcept <| env.evalConst (VersoDoc Genre.none) opts n

/-- Evaluates the document constant {lit}`n` of {lit}`env`. -/
@[implemented_by evalDocUnsafe]
opaque evalDoc (env : Environment) (opts : Options) (n : Name) : IO (VersoDoc Genre.none)

/--
Elaborates {lit}`input`, which ends with a {lit}`#doc` command, and logs its messages and its
document.
-/
def checkDocInput (input : String) : CommandElabM Unit := do
  let (env, msgs) ← elabModuleRest input
  logInfo msgs
  let docName := Verso.Doc.docName (← getMainModule)
  if env.contains docName then
    match ← (evalDoc env (← getOptions) docName).toBaseIO with
    | .ok doc => logInfo m!"{repr doc.toPart}"
    | .error _ => logInfo m!"The document is defined, and it contains errors, so it can't be evaluated."
  else
    logInfo m!"The document {docName} is not defined."
