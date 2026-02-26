/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoManual

open Verso.Genre Manual


#doc (Manual) "Verso 4.29.0 (unreleased)" =>
%%%
tag := "release-v4.29.0"
file := "v4.29.0"
%%%

* Fix Verso folding ranges / TOC for Lean.Doc syntax and #doc (#768)
* Align Blog inline Lean role naming with Manual; add `{lean}` and deprecate `{leanInline}` (#762)
* A zero-config {ref "literate429"}[literate programming] feature was added in [#809](https://github.com/leanprover/verso/pull/809).

# Literate Programming
%%%
tag := "literate429"
%%%

PR [#809](https://github.com/leanprover/verso/pull/809) added support for a simple literate programming system, in which module docstrings are rendered as the text of a page.
While no configuration is necessary to use it, aside from adding Verso as a dependency, some configuration is possible in order to customize aspects of the display.
See {ref "literate"}[its section in this guide] for more details.
