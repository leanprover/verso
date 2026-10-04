/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso

/-!
A document for the tests in `VersoTests.Refs.DocCommand`. Its links and footnotes are used in
top-level blocks before and after their definitions, and some footnote bodies use earlier links
and footnotes.
-/

#doc (.none) "Across blocks" =>

A [forward link][later] and a forward footnote.[^later]

[earlier]: https://example.com/earlier

[^earlier]: An earlier footnote with a [link][earlier].

# A section with an [earlier link][earlier]

> A quote with a [forward link][later] and a footnote.[^earlier]

* A list item with a [backward link][earlier].

[later]: https://example.com/later

[^later]: A later footnote that uses an earlier one.[^earlier]

A [backward link][later] after the definitions.[^later]
