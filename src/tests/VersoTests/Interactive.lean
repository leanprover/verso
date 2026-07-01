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
  let out ← IO.Process.output { cmd := "src/tests/interactive/run_interactive.sh" }
  IO.print out.stdout
  IO.eprint out.stderr
  assert (out.exitCode == 0) s!"interactive LSP tests failed with exit code {out.exitCode}"
