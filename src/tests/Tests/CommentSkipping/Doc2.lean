/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso

/-!
This test checks a regression that happened where syntax that contained trailing null nodes wouldn't
have trailing whitespace updated properly, leading to failed parses.
-/



#doc (.none) "Title" =>


>
> [abc](http://example.com)

> C
