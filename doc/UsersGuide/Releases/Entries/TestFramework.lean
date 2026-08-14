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
  tag := "feat-test-framework"
  prs := [956]

#doc (Manual) "Test Framework" =>

Added `Errata`, a testing framework with test discovery, uniform failure reporting, and CI-friendly report formats.

Previously, Verso's tests were all essentially _ad hoc_ IO actions that were run in sequence or elaborations that would fail.
Each item was tested with the appropriate tool for the job (random testing, golden testing, traditional unit tests, etc), but there was no overarching test code.
In particular, there were no universal conventions about output or failure reporting, and it could be difficult to see which test had actually failed at a glance.
`Errata` unifies reporting and eliminates the need to plumb lists of tests through the system.

Tests are marked with the `@[test]` attribute, and a test's value can have any type with an `IsTest` instance.
Each test's docstring and source range are saved for failure reporting.
The test runner discovers every test in the package; it can restrict the run to named libraries, rerun property tests with a fixed seed, update golden files, and write JUnit XML, JSON, and Markdown reports.

Elaboration-time tests can be written with `#test_msgs` and `#test_guard`, variants of `#guard_msgs` and `#guard` that run their check at compile time and record the outcome as a test case, reported together with the rest of the suite.

Verso's own test suite runs on Errata: `lake test` discovers and runs every test in the package, and CI publishes the resulting reports.

Tests can also be run interactively from the editor: a panel widget shown on a test's declaration runs it in a separate process, streaming its output as it is produced.
