/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso
import VersoManual
import Illuminate

namespace Verso.Integration.DiagramDoc

open Verso Genre Manual

#docs (Manual) doc "Diagrams in the Manual genre" :=
:::::::

%%%
authors := ["Harry Q. Bovik"]
%%%

A standalone diagram:

```diagram (cssWidth := "10em") (texWidth := "10em")
Illuminate.Diagram.rect 30 20 (fill := Illuminate.Color.white)
```

A pair of diagrams composed inside a row, exercising both the row directive (which lives in
core `VersoManual`) and the `inline` flag on the diagram block:

:::row (align := "middle")
```diagram +inline (cssWidth := "5em") (texWidth := "5em")
Illuminate.Diagram.rect 20 20 (fill := Illuminate.Color.white)
```

```diagram +inline (cssWidth := "5em") (texWidth := "5em")
Illuminate.Diagram.text "hi" {}
```
:::

:::::::
