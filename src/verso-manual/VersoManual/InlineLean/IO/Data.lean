module
public import Lean.Data.Json.FromToJson.Basic
public import Verso.Instances
meta import Verso.Instances.Deriving

open Lean

namespace Verso.Genre.Manual.InlineLean

public inductive FileType where
  | stdin | stdout | stderr
  | input (file : System.FilePath)
  | output (file : System.FilePath)
  | other (file : System.FilePath)
deriving ToJson, FromJson, Repr, BEq, DecidableEq, Quote
