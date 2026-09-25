/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Std.Data.HashSet
public import Errata.Result
public import Errata.Outcome

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

open Std (HashMap HashSet)

/-- The standard streams from before a test's output was captured. -/
structure RealStreams where
  /-- The stdout from before the capture. -/
  stdout : IO.FS.Stream
  /-- The stderr from before the capture. -/
  stderr : IO.FS.Stream

/--
What a captured, failable action runs under: the parts of a test's context that concern its output,
its place in the source, and how it reaches the rest of its test executable.
-/
structure Context.Common where
  /--
  The source location reported for the next failure. The runner seeds it with the test's own
  source range; the assertion language refines it to each call site.
  -/
  location : Location := default
  /--
  The docstring of the current scope, rendered as Markdown: the running test's, when it has one,
  and {lean}`none` inside a named result.
  -/
  description? : Option String := none
  /-- The number of hardware threads that the runner granted to the test. -/
  threads : Nat := 1
  /--
  The command that runs a helper: the test executable itself in its {lit}`errata-helper` mode.
  {lit}`runHelper` appends the helper's name and arguments. The Lean harness sets it when it runs a
  test.
  -/
  helperCommand : Option (Array String) := none
  /--
  Receives each captured output fragment as it is written, in order. Runners that stream a test's
  output as the test produces it, such as those serving an editor widget, need this.

  It runs with the streams that were in place before the test's output was redirected, so it can
  reach the runner's own streams from inside the capture.
  -/
  writeOutput : Option (Output → IO Unit) := none
  /--
  Whether a write to the output destination has failed. If true, further attempts are suppressed.
  -/
  outputFailed : IO.Ref Bool
  /--
  The streams from before the outermost capture, under which the output destination runs. The
  outermost capture records them, and a capture nested inside it reuses them, so a
  {name (full := Errata.Context.Common.writeOutput)}`writeOutput` handler that prints reaches the
  runner's own streams from any nesting depth.
  -/
  realStreams? : Option RealStreams := none

/-- The context of a running test: the common context, the test's identity, and its result log. -/
structure TestContext extends Context.Common where
  /-- The running test's name. -/
  test : String := ""
  /-- The components of the running test's name. -/
  path : Array String := #[]
  /-- The named result currently being recorded, below the test. -/
  resultPath : Array String := #[]
  /--
  The results recorded so far in the current scope. A named result records into a log of its own
  and appends its results to the enclosing scope's log when it finishes.
  -/
  log : IO.Ref (Array Result)
  /--
  Receives each named result as it starts and as it finishes. A runner that shows a test's results
  while they are produced, such as one serving an editor widget, needs this.

  It runs under the streams from before the test's output was redirected, as
  {name (full := Errata.Context.Common.writeOutput)}`writeOutput` does.
  -/
  watchResults : Option (ResultEvent → IO Unit) := none
  /--
  Whether a call of the result watcher has failed. If true, further calls are suppressed.
  -/
  watchFailed : IO.Ref Bool
  /--
  The time spent so far in the named results directly inside the current scope, in milliseconds.
  -/
  insideMs : IO.Ref Nat
  /-- Whether golden checks write the actual output to their expected files. -/
  updateGolden : Bool := false

/--
The context of a running fixture phase: the common context, the fixture's name, and the phase.
-/
structure FixtureContext extends Context.Common where
  /-- The fixture's name: its fully qualified declaration name. -/
  fixture : String := ""
  /-- The phase that is running. -/
  phase : FixturePhase := .setup

/--
Contexts that hold a common context: a test's and a fixture phase's. The capture of output and the
assertion language reach the common part through this class.
-/
class HasCommonContext (ρ : Type) where
  /-- The common part of the context. -/
  common : ρ → Context.Common
  /-- The context with its common part replaced. -/
  setCommon : ρ → Context.Common → ρ
  /-- Whether golden checks write the actual output to their expected files. -/
  updateGolden : ρ → Bool

instance : HasCommonContext TestContext where
  common := TestContext.toCommon
  setCommon ctx common := { ctx with toCommon := common }
  updateGolden := TestContext.updateGolden

instance : HasCommonContext FixtureContext where
  common := FixtureContext.toCommon
  setCommon ctx common := { ctx with toCommon := common }
  updateGolden _ := false
