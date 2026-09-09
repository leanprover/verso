/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Std.Data.HashSet
public import Errata.Result

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

open Std (HashMap HashSet)

/-- A multi-map from option names to all the values supplied for them. -/
abbrev OptionMap := HashMap String (Array String)

/-- The standard streams from before a test's output was captured. -/
structure RealStreams where
  /-- The stdout from before the capture. -/
  stdout : IO.FS.Stream
  /-- The stderr from before the capture. -/
  stderr : IO.FS.Stream

/-- The run-wide configuration and per-test state threaded through every test. -/
structure Context where
  /-- Whether golden checks rewrite their expected files instead of comparing. -/
  updateGolden : Bool := false
  /-- Project-specific options, as a multi-map so repeated options accumulate. -/
  options : OptionMap := {}
  /-- The seed used for property tests, or {lean}`none` to draw a fresh one. -/
  seed : Option Nat := none
  /-- Whether a panic message in a check's captured stderr leaves its status as it is. -/
  ignorePanics : Bool := false
  /-- The package that defines the running test. -/
  package : String := ""
  /-- The module that defines the running test, as a dotted name. -/
  moduleName : String := ""
  /-- The running test declaration's name below its module. -/
  test : String := ""
  /--
  The docstring of the current scope, rendered as Markdown: the running test's, when it has one,
  and {lean}`none` inside a named result.
  -/
  description? : Option String := none
  /-- The named result currently being recorded, below the test. -/
  resultPath : Array String := #[]
  /--
  The source location reported for the next failure. The runner seeds it with the test's own
  source range; the assertion language refines it to each call site.
  -/
  location : Location := default
  /--
  The results recorded so far in the current scope. A named result records into a log of its own
  and appends its results to the enclosing scope's log when it finishes.
  -/
  log : IO.Ref (Array Result)
  /-- The option names read during the run, shared across all tests, for reporting unused options. -/
  usedOptions : IO.Ref (HashSet String)
  /--
  Receives each captured output fragment as it is written, in order. A runner that streams a test's
  output as the test produces it, such as one serving an editor widget, needs this. The batch runner
  leaves it {lean}`none`.

  It runs with the streams that were in place before the test's output was redirected, so it can
  reach the runner's own streams from inside the capture.
  -/
  writeOutput : Option (Output → IO Unit) := none
  /--
  Whether a write to the output destination has failed. If true, further attempts are suppressed.
  -/
  outputFailed : IO.Ref Bool
  /--
  The time spent so far in the named results directly inside the current scope, in milliseconds.
  -/
  insideMs : IO.Ref Nat
  /--
  The streams from before the outermost capture, under which the output destination runs. The
  outermost capture records them, and a capture nested inside it reuses them, so a
  {name (full := Errata.Context.writeOutput)}`writeOutput` handler that prints reaches the runner's
  own streams from any nesting depth.
  -/
  realStreams? : Option RealStreams := none
