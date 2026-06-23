/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoManual

open Lean Elab Command
open Verso.Genre.Manual

set_option guard_msgs.diff true

/-!
When a docstring is missing in a module document, the error
message names the declaration's module and suggests `import all` so
the docstrings load in batch mode. `Signature.mk` is an imported,
undocumented constructor, so it exercises this hint.
-/

/--
error: 'Verso.Genre.Manual.Signature.mk' is not documented.

Hint: If `Signature.mk` is documented, add `import all VersoManual.Docstring.Basic` to import docstrings from `VersoManual.Docstring.Basic`.

Set option 'verso.docstring.allowMissing' to 'true' to allow missing docstrings.
-/
#guard_msgs in
run_cmd do
  discard <| getDocString? (← getEnv) ``Verso.Genre.Manual.Signature.mk
