/-
Copyright (c) 2025-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
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
