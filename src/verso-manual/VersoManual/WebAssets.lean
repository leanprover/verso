/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public meta import Init.System.FilePath -- Temporary workaround for https://github.com/leanprover/lean4/issues/13310
namespace Verso.Genre.Manual

public def find.js := include_str "../../../static-web/find.js"
