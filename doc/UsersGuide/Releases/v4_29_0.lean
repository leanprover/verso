/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoManual

open Verso.Genre

-- To allow ```` below
set_option linter.verso.markup.codeBlock false

#doc (Manual) "Verso 4.29.0 (unreleased)" =>
%%%
tag := "release-v4.29.0"
file := "v4.29.0"
%%%

* Fix Verso folding ranges / TOC for Lean.Doc syntax and #doc (#768)
* Align Blog inline Lean role naming with Manual; add `{lean}` and deprecate `{leanInline}` (#762)
