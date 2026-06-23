/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual

open Lean Elab Command
open Verso.Genre.Manual

set_option guard_msgs.diff true

/-!
The `import all` hint is specific to module documents, where a plain `import` does not load
docstrings. A non-`module` document loads docstrings from a plain `import`, so the
diagnostic omits the hint. This is the non-`module` counterpart of `Tests/DocstringMissing.lean`.
-/

/--
error: 'Verso.Genre.Manual.Signature.mk' is not documented.

Set option 'verso.docstring.allowMissing' to 'true' to allow missing docstrings.
-/
#guard_msgs in
run_cmd do
  discard <| getDocString? (← getEnv) ``Verso.Genre.Manual.Signature.mk
