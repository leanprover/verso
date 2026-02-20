/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Lean.Data.Json.FromToJson

namespace Verso.Genre.Manual
open Lean

public structure TeXConfig where
  extraFilesTeX : List (System.FilePath × String) := []
deriving ToJson, FromJson
