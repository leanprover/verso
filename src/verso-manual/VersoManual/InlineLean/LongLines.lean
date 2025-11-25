/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Data.Lsp.Utf16
import Lean.Data.Options
import Lean.Data.Position
import Lean.Log

open Lean MonadOptions

register_option verso.code.warnLineLength : Nat := {
  defValue := 60
  descr := "The example code line length at which to issue warnings. Set to 0 for no warnings."
}

namespace Verso.Genre.Manual

def getWarnLineLength [Monad m] [MonadOptions m] : m (Option Nat) := do
  let val := (← getOptions).get verso.code.warnLineLength.name verso.code.warnLineLength.defValue
  if val = 0 then return none else return some val

def warnLongLines [Monad m] [MonadFileMap m] [MonadLog m] [AddMessageContext m] [MonadOptions m] (indent? : Option Nat) (str : StrLit) : m Unit := do
  let some maxCodeColumns ← getWarnLineLength
    | pure ()
  let fileMap ← getFileMap
  let maxCol := maxCodeColumns + indent?.getD 0
  if let some startPos := str.raw.getPos? then
    if let some stopPos := str.raw.getTailPos? then
      let ⟨startLine, _⟩ := fileMap.toPosition startPos
      let ⟨stopLine, _⟩ := fileMap.toPosition stopPos
      for l in [startLine:stopLine] do
        let nextStart := fileMap.lineStart (l + 1)
        let ⟨_, endCol⟩ := fileMap.utf8PosToLspPos (nextStart.prev fileMap.source)
        if endCol > maxCol then
          let thisStart := fileMap.lineStart l
          let fakeLiteral := Syntax.mkStrLit (thisStart.extract fileMap.source nextStart) (.synthetic thisStart nextStart)
          let msg := m!"Line {l} is too long ({endCol} columns exceeds {maxCol})"
          logWarningAt fakeLiteral msg
