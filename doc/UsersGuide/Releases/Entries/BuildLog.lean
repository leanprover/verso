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
  breaking := false
  tag := "feat-build-log"
  prs := [862]

#doc (Manual) "Logging Abstraction" =>

Refactored the build's error reporting into a {ref "feat-build-log"}[logging abstraction] with severities and structured source locations, improving the consistency of Verso's internal APIs and external error reports.

The build pipeline previously threaded a bare `String → IO Unit` error callback through traversal and output generation, and several monads carried their own ad-hoc error loggers.
There was no way to emit a warning.

This release introduces {name}`Verso.MonadBuildLog`, a uniform logging interface shared across the genres.
A message carries a {name}`Verso.Severity` (either {name}`Verso.Severity.error` or {name}`Verso.Severity.warning`) and an optional source location.
