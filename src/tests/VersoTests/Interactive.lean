/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata

open Errata

public section

/--
Use a shell harness to test the LSP server.
-/
@[test]
def interactive : Test := do
  -- The script writes its progress per case to the test executable's own standard output, which the
  -- runner captures as it arrives, so the report shows how far the suite got even when a case hangs
  -- and the test is stopped at its timeout.
  let child ← IO.Process.spawn { cmd := "src/tests/interactive/run_interactive.sh" }
  let exitCode ← child.wait
  assertTrue (exitCode == 0) s!"interactive LSP tests failed with exit code {exitCode}"
