/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

import Errata

open Errata

/--
Use a shell harness to test the LSP server.
-/
@[test]
def interactive : Test := do
  -- The child inherits the real stdio so its per-case progress is visible while it runs; a hang in
  -- CI then shows how far the suite got instead of a killed job with no output.
  let child ← IO.Process.spawn { cmd := "src/tests/interactive/run_interactive.sh" }
  let exitCode ← child.wait
  assertTrue (exitCode == 0) s!"interactive LSP tests failed with exit code {exitCode}"
