import Lean

import LeanDoc.Doc

namespace LeanDoc.Build

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
