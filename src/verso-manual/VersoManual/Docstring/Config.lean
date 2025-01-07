import Lean.Data.Options

open Lean MonadOptions

register_option verso.docstring.elabMarkdown : Bool := {
  defValue := true
  group := "doc"
  descr := "Whether to heuristically elaborate Lean code in Markdown docstrings in Verso"
}

namespace Verso.Genre.Manual.Docstring

def getElabMarkdown [Monad m] [MonadOptions m] : m Bool := do
  return (← getOptions).get verso.docstring.elabMarkdown.name verso.docstring.elabMarkdown.defValue
