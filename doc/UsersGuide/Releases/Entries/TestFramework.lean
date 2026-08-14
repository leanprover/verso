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
  prs := []

#doc (Manual) "Test Framework" =>

Added Errata, a test framework with test discovery, uniform failure reporting, and CI-friendly report formats.

Tests are marked with the `@[test]` attribute, and a test's value can have any type with an `IsTest` instance.
Each test's docstring and source range are saved for failure reporting.
The test runner discovers every test in the package; it can restrict the run to named libraries, rerun property tests with a fixed seed, update golden files, and write JUnit XML, JSON, and Markdown reports.

Elaboration-time tests can be written with `#test_msgs` and `#test_guard`, variants of `#guard_msgs` and `#guard` that run their check at compile time and record the outcome as a test case, reported together with the rest of the suite.
