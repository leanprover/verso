/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean

import Verso.Doc

namespace Verso.Build

namespace Traverse
-- In the traverse pass, we propagate information between nodes in the
-- document Additionally, nodes may transform themselves in response
-- to the information that's been gained.

-- A given genre will fix its type of traversal values. Additionally,
-- all genres support dynamically-typed entries to facilitate
-- cross-genre libraries.

structure TraversalState.{u} where
  Value : Type u
  contents : Lean.RBMap String (Value ⊕ Dynamic) compare




end Traverse
