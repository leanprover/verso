/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 34, 0⟩
  breaking := false
  tag := "versioned-release-notes"
  prs := [950]

#doc (Manual) "Versioned Release Note Entries" =>

Each change to Verso now describes itself in its own release note entry, and the version sections of this chapter are computed from the Lean toolchain.

An entry is a file under `doc/UsersGuide/Releases/Entries/` that names the version it describes.
The sections of this chapter are derived from those versions, so an entry written before a release and merged after one lands in the section for the version it actually shipped in.
Pull requests are checked for an entry, and for naming the version that is under development.
