import Verso
import VersoManual

/-!
Tests semantic highlighting for prose, literal code, and elaborated Lean code in a Verso document.
-/

open Verso Genre Manual InlineLean

#doc (Manual) "Semantic tokens" =>
Ordinary prose and `literal code`.

The term {lean}`List.map` is elaborated Lean code.

```text
literal block
```

```lean
#check List.map
```

--^ sync
--^ textDocument/semanticTokens/full
