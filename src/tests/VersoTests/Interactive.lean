/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

import Errata

open Errata

/--
The interactive tests exercise the LSP server through a shell harness. The harness inherits this
process's standard streams, so its own output appears directly; a non-zero exit is the failure.
-/
@[test]
def interactive : Test := do
  let child ← IO.Process.spawn { cmd := "src/tests/interactive/run_interactive.sh" }
  let exitCode ← child.wait
  assert (exitCode == 0) s!"interactive LSP tests failed with exit code {exitCode}"
