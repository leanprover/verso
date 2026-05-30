/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Theme test" =>

# Code samples

A line of prose, followed by code that mixes a keyword, a const, and a literal.

```lean
def hello (name : String) : String := s!"hello, {name}"
```

# Diagnostics

A block that errors, so the rendered HTML carries the `.lean-output.error` rule used by the
theme's error indicator color:

```lean +error (name := badProof)
example : 2 + 2 = 5 := by rfl
```

```leanOutput badProof
Tactic `rfl` failed: The left-hand side
  2 + 2
is not definitionally equal to the right-hand side
  5

⊢ 2 + 2 = 5
```
