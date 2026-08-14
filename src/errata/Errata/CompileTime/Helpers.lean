/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen

Non-meta helpers for the `#test_msgs` command, kept separate so the command elaborator is the
only meta definition.
-/
module

public import Lean.Message
public import Lean.Elab.GuardMsgs

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata.CompileTime

/-- Renders a message with a severity prefix, in the form the expected block is compared against. -/
def formatMessage (msg : Lean.Message) : IO String := do
  let mut str ← msg.data.toString
  unless msg.caption == "" do
    str := msg.caption ++ ":\n" ++ str
  -- The severity is followed by a space only when the body stays on the same line, matching the
  -- rendering that `#guard_msgs` compares against.
  unless str.startsWith "\n" do str := " " ++ str
  str :=
    if msg.isTrace then "trace:" ++ str
    else match msg.severity with
      | .information => "info:" ++ str
      | .warning => "warning:" ++ str
      | .error => "error:" ++ str
  unless str.endsWith "\n" do str := str ++ "\n"
  return str

open Lean.Elab.Tactic.GuardMsgs (WhitespaceMode) in
/-- Whether the expected and actual message blocks match, normalizing whitespace as `#guard_msgs` does. -/
def messagesMatch (expected actual : String) : Bool :=
  let norm := fun s => (WhitespaceMode.normalized.apply s).trimAscii.copy
  norm expected == norm actual

/-- The doc comment that would make the expected block match the actual output. -/
def suggestedDoc (actual : String) : String :=
  if actual.isEmpty then ""
  else if actual.contains '\n' then s!"/--\n{actual}\n-/\n"
  else s!"/-- {actual} -/\n"
