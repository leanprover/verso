/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Lean.Data.Lsp.Utf16
public import Lean.DocString.View
public import Lean.Data.Options
public import Lean.Data.Position
public import Lean.Log

public section

open Lean MonadOptions
open Lean.Doc

register_option verso.code.warnLineLength : Nat := {
  defValue := 60
  descr := "The example code line length at which to issue warnings. Set to 0 for no warnings."
}

namespace Verso.Genre.Manual

def getWarnLineLength [Monad m] [MonadOptions m] : m (Option Nat) := do
  let val := (← getOptions).get verso.code.warnLineLength.name verso.code.warnLineLength.defValue
  if val = 0 then return none else return some val

/--
Warns about the lines of `code` that are too long to render in a narrow context.

A code block's own indentation is whitespace between its line tokens, so a line's width is the width
of its token's contents.
-/
def warnLongLines [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (code : VersoCodeBlock) : m Unit := do
  let some maxCodeColumns ← getWarnLineLength
    | pure ()
  let lines := code.getVersoCodeBlockLines
  for h : i in [0:lines.size] do
    let line := lines[i]
    let width := line.getVersoCodeLine.trimAsciiEnd.positions.length
    if width > maxCodeColumns then
      let note :=
        MessageData.note m!"Example code is shown on mobile devices and other narrow contexts. \
          Long lines are likely to be truncated in the rendered output."
      let hint :=
        MessageData.hint' m!"The limit of this linter can be changed with the option \
          `{.ofConstName ``verso.code.warnLineLength}`. This linter can be disabled by setting \
          this option to 0."
      logWarningAt line
        m!"Line {i + 1} is too long ({width} columns exceeds {maxCodeColumns}).{note}{hint}"
