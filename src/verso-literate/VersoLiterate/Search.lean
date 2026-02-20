/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoLiterate.Basic
public import VersoSearch

public section

namespace VersoLiterate

instance : Verso.Search.Indexable Literate where
  partId := nofun
  block _ := none
  inline _ := none
