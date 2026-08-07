/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Elab.ConfigEval

public section

namespace Verso.Genre.Blog.Literate

structure LitPageConfig where
  header : Bool := false

declare_config_elab litPageConfig LitPageConfig

end Verso.Genre.Blog.Literate
