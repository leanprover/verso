/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lake
open Lake DSL

require subverso from git "https://github.com/leanprover/subverso"@"structured-output"

package «examples» where
  -- add package configuration options here

@[default_target]
lean_lib «AnchorExamples» where
