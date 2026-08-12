/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 32, 0⟩
  breaking := false
  tag := "extension-descriptor-visibility"
  prs := [909]

#doc (Manual) "Extension Descriptors Are Public" =>

The descriptors that `block_extension` and `inline_extension` generate are public, so a document that uses an extension resolves its implementation under the module system.
