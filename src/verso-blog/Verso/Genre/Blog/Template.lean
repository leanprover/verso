/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/


import Verso.Genre.Blog.Site


open Verso.Genre Blog



instance [Monad m] : MonadPath m where
  currentPath := pure []
