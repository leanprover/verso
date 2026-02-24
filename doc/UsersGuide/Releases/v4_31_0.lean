/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

open Verso.Genre Manual InlineLean


#doc (Manual) "Verso 4.31.0 (unreleased)" =>
%%%
tag := "release-v4.31.0"
file := "v4.31.0"
%%%

* Refactored the build's error reporting into a {ref "feat-build-log"}[logging abstraction] with severities and structured source locations, improving the consistency of Verso's internal APIs and external error reports.
  While this was primarily an internal change, there is a {ref "feat-build-log-breaking"}[breaking change] to the signature of {name}`Verso.Genre.Manual.ExtraStep`.
* Improve role resolution diagnostics with suggestions and actionable registration errors (#763).
* Register legacy inline APIs as roles for compatibility (`today`, `date`, `sectionRef`, `index`, `see`, `seeAlso`) (#763).

# Logging Abstraction
%%%
tag := "feat-build-log"
%%%

The build pipeline previously threaded a bare `String → IO Unit` error callback through traversal and output generation, and several monads carried their own ad-hoc error loggers.
There was no way to emit a warning.

This release introduces {name}`Verso.MonadBuildLog`, a uniform logging interface shared across the genres.
A message carries a {name}`Verso.Severity` (either {name}`Verso.Severity.error` or {name}`Verso.Severity.warning`) and an optional source location.


## Breaking Change: `ExtraStep`
%%%
tag := "feat-build-log-breaking"
%%%

{name}`Verso.Genre.Manual.ExtraStep` no longer takes a `String → IO Unit` error callback.
Instead, it runs in a monad that has an instance of {name}`Verso.MonadBuildLog`, so a step can emit both errors and warnings with {name}`Verso.reportError` and {name}`Verso.reportWarning`.
