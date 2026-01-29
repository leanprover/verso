/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoManual

open Verso.Genre

-- To allow ```` below
set_option linter.verso.markup.codeBlock false

#doc (Manual) "Verso 4.28.0 (unreleased)" =>
%%%
tag := "release-v4.28.0"
file := "v4.28.0"
%%%

* Add Release Notes / Changelog to Verso Users guide (@david-christiansen, @ejgallego, #708)
* Add LSP testing infrastructure for Verso documents (@david-christiansen, @ejgallego, #699)
* Fix incorrect elaboration info for "full" Verso documents. This for example prevented inline lean code from displaying in the infoview (@david-christiansen, @ejgallego, #700)
