/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Log
import Lean.Elab.Command
import Lean.Elab.InfoTree
public import Lean.Util.Diff
public import Lean.Meta.Hint
-- For doc xrefs
import SubVerso.Examples.Messages.NormalizeLineNum
import SubVerso.Examples.Messages.NormalizeMetavars

public section

set_option doc.verso true

open Lean Elab

namespace Verso.ExpectString

variable {m : Type → Type} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
variable [MonadInfoTree m] [MonadLiftT CoreM m]

def abbreviateString (what : String) (maxLength : Nat := 30) : String :=
  if what.length > maxLength then
    what.take maxLength ++ "…"
  else
    what

/--
Expects that a string matches some expected form from the document, returning {name}`MessageData` for further processing.

No errors are logged.

If the strings don't match, then a diff is displayed as an error, and a code action to replace the
expected string with the actual one is offered. Strings are compared one line at a time, and only
strings that match {name}`useLine` are considered (by default, all are considered). Lines are compared
modulo {name}`preEq`.

{name}`SubVerso.Examples.Messages.normalizeMetavars` and {name}`SubVerso.Examples.Messages.normalizeLineNums`
are good candidates for {name}`preEq`.

Errors are logged, not thrown; the returned {name}`Bool` indicates whether an error was logged.
-/
def expectStringOrDiff (expected : StrLit) (actual : String)
    (preEq : String → String := id)
    (useLine : String → Bool := fun _ => true) : m (Option MessageData) := do
  let expectedLines := expected.getString.splitOn "\n" |>.filter useLine |>.toArray
  let actualLines := actual.splitOn "\n" |>.filter useLine |>.toArray

  unless expectedLines.map preEq == actualLines.map preEq do
    let diff := Diff.diff expectedLines actualLines
    return some m!"{Diff.linesToString diff}"

  return none

/--
Expects that a string matches some expected form from the document.

If the strings don't match, then a diff is displayed as an error, and a code action to replace the
expected string with the actual one is offered. Strings are compared one line at a time, and only
strings that match {name}`useLine` are considered (by default, all are considered). Lines are compared
modulo {name}`preEq`. The parameter {name}`what` is used in the error message header, in a context "Mismatched
{name}`what` output:".

{name}`SubVerso.Examples.Messages.normalizeMetavars` and {name}`SubVerso.Examples.Messages.normalizeLineNums`
are good candidates for {name}`preEq`.

Errors are logged, not thrown; the returned {name}`Bool` indicates whether an error was logged.
-/
def expectString (what : String) (expected : StrLit) (actual : String)
    (preEq : String → String := id)
    (useLine : String → Bool := fun _ => true) : m Bool := do
  let expectedLines := expected.getString.splitOn "\n" |>.filter useLine |>.toArray
  let actualLines := actual.splitOn "\n" |>.filter useLine |>.toArray

  unless expectedLines.map preEq == actualLines.map preEq do
    let diff := Diff.diff expectedLines actualLines

    let h : MessageData ← MessageData.hint "Replace with actual value" #[{suggestion := .string actual}] (ref? := some expected)
    logErrorAt expected m!"Mismatched {what} output:\n{Diff.linesToString diff}{h}"
    return false

  return true
