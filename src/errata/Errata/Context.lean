/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Std.Data.HashMap
public import Std.Data.HashSet
public import Errata.Result

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

open Std (HashMap HashSet)

/-- A multi-map from option names to all the values supplied for them. -/
abbrev OptionMap := HashMap String (Array String)

/-- The run-wide configuration and per-test state threaded through every test. -/
structure Context where
  /-- The reporting verbosity. -/
  verbosity : Verbosity := .silent
  /-- Whether golden checks rewrite their expected files instead of comparing. -/
  updateGolden : Bool := false
  /-- Project-specific options, as a multi-map so repeated options accumulate. -/
  options : OptionMap := {}
  /-- The seed used for property tests, or {lean}`none` to draw a fresh one. -/
  seed : Option Nat := none
  /-- The package that defines the running test. -/
  package : String := ""
  /-- The module that defines the running test, as a dotted name. -/
  moduleName : String := ""
  /-- The running test declaration's name below its module. -/
  test : String := ""
  /-- The running test's docstring, rendered as Markdown, when it has one. -/
  description? : Option String := none
  /-- The named result currently being recorded, below the test. -/
  resultPath : Array String := #[]
  /--
  The source location reported for the next failure. The runner seeds it with the test's own
  source range; the assertion language refines it to each call site.
  -/
  location : Location := default
  /-- The results collected so far during the current test. -/
  log : IO.Ref (Array Result)
  /-- The option names read during the run, shared across all tests, for reporting unused options. -/
  usedOptions : IO.Ref (HashSet String)
  /--
  Receives each captured output fragment as it is written, in order. The default discards them; a
  live runner sets it to stream output as the test produces it.
  -/
  writeOutput : Output → IO Unit := fun _ => pure ()
