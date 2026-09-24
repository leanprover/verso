/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The settings of Verso's tests. `errata.toml` at the root of the repository gives them values.
-/
module

public import Errata

open Errata

@[expose] public section

namespace VersoTests

/-- Also runs {lit}`lualatex` on the generated TeX, to confirm that it builds. -/
@[setting]
def checkTeX : Setting where
  type := Bool
  fromString
    | "true" => some true
    | "false" => some false
    | _ => none
  default? := some "false"

/-- The built {lit}`verso` executable. -/
@[setting]
def versoExe : Setting where
  type := System.FilePath
  fromString s := some s

/-- The built {lit}`verso-literate-html` executable. -/
@[setting]
def literateHtmlExe : Setting where
  type := System.FilePath
  fromString s := some s

/-- The built {lit}`verso-literate-plan` executable. -/
@[setting]
def literatePlanExe : Setting where
  type := System.FilePath
  fromString s := some s

end VersoTests
