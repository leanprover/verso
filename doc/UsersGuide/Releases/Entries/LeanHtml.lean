/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 36, 0⟩
  breaking := true
  tag := "lean-html"
  prs := [974]

#doc (Manual) "Using Lean's HTML Type" =>

Verso now uses the Lean types and custom HTML syntax provided by Lean, rather than its own implementation of a custom HTML syntax.

Users who are using existing Verso genres should not encounter any backwards-incompatible changes, but implementations of individual genres, and code that generates HTML, will generally need updating.
