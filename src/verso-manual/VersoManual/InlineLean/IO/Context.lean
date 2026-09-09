/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Lean.DocString.View
public import Lean.Environment

public section

namespace Verso.Genre.Manual.InlineLean.IOExample

open Lean
open Lean.Doc

structure IOExampleContext where
  leanCodeName : Ident
  code : Option VersoCodeBlock := none
  inputFiles : Array (System.FilePath × VersoCodeBlock) := #[]
  outputFiles : Array (System.FilePath × VersoCodeBlock) := #[]
  stdin : Option VersoCodeBlock := none
  stdout : Option VersoCodeBlock := none
  stderr : Option VersoCodeBlock := none
deriving Repr

initialize ioExampleCtx : EnvExtension (Option IOExampleContext) ←
  Lean.registerEnvExtension (pure none)
