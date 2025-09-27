/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoLiterate.Basic
import VersoSearch

namespace VersoLiterate
open Verso Search

instance : Indexable Literate where
  partId := nofun
  block _ := none
  inline _ := none
