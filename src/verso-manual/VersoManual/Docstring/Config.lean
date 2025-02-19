/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Data.Options

open Lean MonadOptions

register_option verso.docstring.elabMarkdown : Bool := {
  defValue := true
  group := "doc"
  descr := "Whether to heuristically elaborate Lean code in Markdown docstrings in Verso"
}

register_option verso.docstring.allowDeprecated : Bool := {
  defValue := false
  group := "doc"
  descr := "Whether to accept documentation for deprecated names"
}

namespace Verso.Genre.Manual.Docstring

def getElabMarkdown [Monad m] [MonadOptions m] : m Bool := do
  return (← getOptions).get verso.docstring.elabMarkdown.name verso.docstring.elabMarkdown.defValue

def getAllowDeprecated [Monad m] [MonadOptions m] : m Bool := do
  return (← getOptions).get verso.docstring.allowDeprecated.name verso.docstring.allowDeprecated.defValue
