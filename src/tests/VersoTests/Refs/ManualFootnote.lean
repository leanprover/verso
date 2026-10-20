/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual

/-!
Two {lit}`Manual` documents for the tests in `VersoTests.Refs.DocCommand`, each with a
{lit}`{lean}` role inside a footnote. {lit}`#docs` elaborates the first all at once, and
{lit}`#doc` elaborates the second block by block.
-/

open Verso Genre Manual InlineLean

namespace Verso.RefsTest.ManualFootnote

#docs (Manual) allAtOnce "Footnote with Lean code" :=
:::::::
Text.[^note]

[^note]: A note about {lean}`Nat.succ 2`.
:::::::

end Verso.RefsTest.ManualFootnote

#doc (Manual) "Footnote with Lean code" =>

[example]: https://example.com

Text.[^note]

[^note]: A note about {lean}`Nat.succ 2`, with a [link][example].
