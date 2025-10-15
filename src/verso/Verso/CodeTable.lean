import Lean
import SubVerso.Highlighting
namespace Verso.CodeTable

class CodeTable (name : Lean.Name) where
  is : SubVerso.Highlighting.Export
