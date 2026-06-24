/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso

/-!
This test ensures that Lean's parser doesn't skip Lean comment syntax while parsing Verso blocks as
Lean commands.
-/

#doc (.none) "Title" =>

/-
This text should be in the document.
-/


This text is after the Lean comment that should be skipped.

* abc

/- Also this text should be there -/

def
