/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoManual

open Verso.Genre

#doc (Manual) "Verso 4.29.0" =>
%%%
tag := "release-v4.29.0"
file := "v4.29.0"
%%%

* Improve role resolution diagnostics with suggestions and actionable registration errors (@ejgallego, #763)
* Register legacy inline APIs as roles for compatibility (`today`, `date`, `sectionRef`, `index`, `see`, `seeAlso`) (@ejgallego, #763)
