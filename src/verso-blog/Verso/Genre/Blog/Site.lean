/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/



namespace Verso.Genre.Blog

class MonadPath (m : Type → Type u) where
  currentPath : m (List String)

export MonadPath (currentPath)
