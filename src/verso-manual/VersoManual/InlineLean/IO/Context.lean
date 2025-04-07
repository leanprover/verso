/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Environment

namespace Verso.Genre.Manual.InlineLean.IOExample

open Lean

structure IOExampleContext where
  leanCodeName : Ident
  code : Option StrLit := none
  inputFiles : Array (System.FilePath × StrLit) := #[]
  outputFiles : Array (System.FilePath × StrLit) := #[]
  stdin : Option StrLit := none
  stdout : Option StrLit := none
  stderr : Option StrLit := none
deriving Repr

initialize ioExampleCtx : EnvExtension (Option IOExampleContext) ←
  Lean.registerEnvExtension (pure none)
