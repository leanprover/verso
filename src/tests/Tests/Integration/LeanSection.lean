/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Verso
import VersoManual

namespace Verso.Integration.LeanSection

open Verso Genre Manual InlineLean

#docs (Manual) doc "Lean Section Test" :=
:::::::

%%%
authors := ["Test Author"]
%%%

:::leanSection "TestScope"

```lean
variable (n : Nat)
```

The variable {lean}`n` should be in scope here.

:::

After the section, `n` should no longer be in scope.

:::leanSection "MacroScope"

```lean -show
private axiom innerVal : Nat
local macro "myMacroTerm" : term => ``(innerVal)
```

Inside the section, {lean}`myMacroTerm` resolves to `innerVal`.

:::

Right after the section closes, `myMacroTerm` should be unknown: {lean +error}`myMacroTerm`

```lean -show
private axiom outerVal : Nat
local macro "myMacroTerm" : term => ``(outerVal)
```

After the section, {lean}`myMacroTerm` should resolve unambiguously to `outerVal` only.

:::::::

end Verso.Integration.LeanSection
