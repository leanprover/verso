/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.Result
import Errata.Discovery
public meta import Errata.CompileTime.Helpers
public import Lean.Elab.Command
public import Lean.Data.Options
import Lean.Meta.Hint
import Lean

open Lean Elab Command Errata.CompileTime

public section

set_option doc.verso true

/--
When true, a failing Errata compile-time test is an elaboration error rather than a warning.
-/
register_option Errata.failOnError : Bool := {
  defValue := false
  descr := "Make a failing Errata compile-time test an elaboration error rather than a warning."
}

namespace Errata

/-- Checks that the command below produces the messages given in the preceding doc comment. -/
syntax (name := testMsgsCmd) (plainDocComment)? "#test_msgs" "in" command : command

@[command_elab testMsgsCmd]
meta def elabTestMsgs : Command.CommandElab
  | `($[$dc?:docComment]? #test_msgs%$tk in $cmd) => do
    let expected := ((← dc?.mapM (getDocStringText ·)).getD "").trimAscii.copy
    -- Elaborate the command, capturing its messages instead of letting them surface. Both the
    -- synchronous log and the asynchronous snapshot tasks are collected, so messages from linters
    -- (which run after elaboration) are included, as `#guard_msgs` does.
    let saved := (← get).messages
    modify ({ · with messages := {} })
    withReader ({ · with snap? := none }) do
      elabCommandTopLevel cmd #[]
    let produced := (← get).messages ++
      (← get).snapshotTasks.foldl (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) .empty) .empty
    modify ({ · with messages := saved, snapshotTasks := #[] })
    let visible := produced.toList.filter (!·.isSilent)
    let strings ← (visible.mapM formatMessage : IO (List String))
    -- Multiple messages are separated by `---`, matching the block `#guard_msgs` compares against.
    let actual := ("---\n".intercalate strings).trimAscii.copy
    let passed := messagesMatch expected actual
    -- Reify the verdict into a discovered test, named after the source position. The module name
    -- qualifies it so that two modules with a `#test_msgs` at the same position do not collide.
    let fileMap ← getFileMap
    let startPos := fileMap.toPosition (tk.getPos?.getD 0)
    let endPos := fileMap.toPosition (tk.getTailPos?.getD 0)
    let declName := `_root_ ++ (← getMainModule) ++
      Name.mkSimple s!"errataMsgTest_L{startPos.line}_C{startPos.column}"
    let verdict ←
      if passed then
        `(Errata.TestResult.pass)
      else
        `(Errata.TestResult.mismatch "compile-time messages do not match" $(quote actual)
            $(quote (← getFileName))
            $(quote startPos.line) $(quote startPos.column)
            $(quote endPos.line) $(quote endPos.column))
    elabCommand (← `(@[test] def $(mkIdent declName) : Errata.TestResult := $verdict))
    -- Report a mismatch at build time, offering the corrected expected block as a fix.
    unless passed do
      let fixRef := (dc?.map (·.raw)).getD tk
      let hint ← liftCoreM <| MessageData.hint m!"Update the expected output:"
        #[{ suggestion := suggestedDoc actual }] (ref? := some fixRef)
      let body := m!"Errata #test_msgs: the messages do not match.\n\n\
        Expected:\n{expected}\n\nActual:\n{actual}"
      if (← getOptions).getBool `Errata.failOnError false then
        logErrorAt tk (body ++ hint)
      else
        logWarningAt tk (body ++ hint)
  | _ => throwUnsupportedSyntax
