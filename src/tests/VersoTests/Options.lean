/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata

open Errata

/--
Reads the `check-tex` option so the runner counts it as recognized on every run. The runner warns
about options it never reads, and `check-tex` is otherwise read only by the TeX golden tests, which a
partial run can leave out.
-/
@[test]
def checkTexRecognized : Test := do
  let _ ← flag "check-tex"
