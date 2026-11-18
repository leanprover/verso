/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import VersoManual

open Verso.Genre.Manual

/-! Enabling a bundled feature brings its license with it, however the feature is enabled. -/

/-- info: true -/
#test_msgs in
#eval ({ features := {.KaTeX} } : HtmlAssets).allLicenseInfo.contains Licenses.KaTeX

/-- info: true -/
#test_msgs in
#eval (({} : HtmlAssets).combine { features := {.KaTeX} }).allLicenseInfo.contains Licenses.KaTeX

/-- info: false -/
#test_msgs in
#eval ({} : HtmlAssets).allLicenseInfo.contains Licenses.KaTeX
