/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio Jesus Gallego Arias
-/
module
public import Tests.DocElabExtensions.LocalExtension
public meta import Tests.DocElabExtensions.LocalExtension
public import VersoManual
public meta import VersoManual

public section

namespace Verso.Tests.DocElabExtensions

/-!
This module defines the local entries used by the transitive-import regression.
It registers one test-only local-persistent entry and one custom expander for each document
extension kind. `Middle` imports this module without adding entries, and `Use` imports `Middle`
to check that transitive lookup works without re-exporting `Middle`'s imported entries.
-/

open Verso Genre Manual
open Verso.Doc.Elab
open Lean

#register_inherited_test_local_entry

@[role]
meta def inheritedRole : RoleExpanderOf Unit
  | (), _contents => ``(Doc.Inline.text "inherited role")

@[code_block]
meta def inheritedCode : CodeBlockExpanderOf Unit
  | (), str => ``(Doc.Block.code $(quote str.getString))

@[directive]
meta def inheritedDirective : DirectiveExpanderOf Unit
  | (), blocks => do
    let blocks ← blocks.mapM elabBlock
    ``(Doc.Block.concat #[$blocks,*])

@[block_command]
meta def inheritedCommand : BlockCommandOf Unit
  | () => ``(Doc.Block.para #[Doc.Inline.text "inherited command"])
