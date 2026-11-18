/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
module
public import Lean.Environment

/-!
What we *are* doing: doc finalizer elaborates and stores HTML string in
environment extension, RPC retrieves string from environment extension.
What we *should be* doing:
 - Verso is proactively storing a representation of the document in an
   environment extension
 - The RPC is looking up that representation of the document, incurring the
   cost of elaboration and translation to an HTML string, and returning that
-/

open Lean

namespace Verso

/-! The environment extension in question -/

public inductive VersoDocumentData where
  | success : String → VersoDocumentData
  | errors : Array String → VersoDocumentData
  | noDoc : VersoDocumentData
deriving ToJson, FromJson

public initialize versoDocumentExt : EnvExtension (Option VersoDocumentData) ←
  registerEnvExtension (pure .none)
