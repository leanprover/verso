/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.TestM
public import Errata.Here

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/-- Asserts that a process exited with the expected code, showing its error output otherwise. -/
def assertExitCode (expected : UInt32) (output : IO.Process.Output)
    (loc : Location := by exact here%) : TestM Unit :=
  unless output.exitCode == expected do
    fail s!"process exited with code {output.exitCode}, expected {expected}"
      (detail? := some s!"stderr:\n{output.stderr}") (location? := some loc)
