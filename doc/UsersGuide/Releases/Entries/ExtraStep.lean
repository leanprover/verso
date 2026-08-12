/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 31, 0⟩
  breaking := true
  tag := "feat-build-log-breaking"
  prs := [862]

#doc (Manual) "Breaking Change: `ExtraStep`" =>

There is a {ref "feat-build-log-breaking"}[breaking change] to the signature of {name}`Verso.Genre.Manual.ExtraStep`.

{name}`Verso.Genre.Manual.ExtraStep` no longer takes a `String → IO Unit` error callback.
Instead, it runs in a monad that has an instance of {name}`Verso.MonadBuildLog`, so a step can emit both errors and warnings with {name}`Verso.reportError` and {name}`Verso.reportWarning`.
