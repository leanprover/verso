/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

set_option linter.verso.manual.headerTags false

release_note
  version := ⟨4, 37, 0⟩
  breaking := false
  tag := "include-license"
  prs := [1127]

#doc (Manual) "Including License Files" =>

Verso's manual genre now includes `include_license`, which is a variant of `include_str` that loads license information from a text file.
The text file must start with a single line of content followed by one or more blank lines.
The first non-blank line of the file becomes the header, with the rest becoming the body.
