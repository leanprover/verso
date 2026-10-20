/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso

/-!
Documents for the tests in `VersoTests.Refs.DocCommand`: three documents in one module that define
the same link and footnote labels with different values.
-/

namespace Verso.RefsTest.SameName

#docs (.none) first "First" :=
:::::::
A [link][shared].[^shared]

[shared]: https://example.com/first
[^shared]: The first footnote.
:::::::

#docs (.none) second "Second" :=
:::::::
[shared]: https://example.com/second
[^shared]: The second footnote.

A [link][shared].[^shared]
:::::::

end Verso.RefsTest.SameName

#doc (.none) "Third" =>

A [link][shared].[^shared]

[shared]: https://example.com/third

[^shared]: The third footnote.
