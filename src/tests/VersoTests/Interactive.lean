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
  -- The script writes its progress per case to the test executable's own standard output. The
  -- runner captures that output as it arrives, and the report shows it, also for a test stopped at
  -- its timeout.
  let child ← IO.Process.spawn { cmd := "src/tests/interactive/run_interactive.sh" }
  let exitCode ← child.wait
  assertTrue (exitCode == 0) s!"interactive LSP tests failed with exit code {exitCode}"
