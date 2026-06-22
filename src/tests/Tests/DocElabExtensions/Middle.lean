/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio Jesus Gallego Arias
-/
import Tests.DocElabExtensions.Define

namespace Verso.Tests.DocElabExtensions

/-!
This module is the middle import in the transitive-import regression.
It imports the local entries from `Define` but intentionally adds no new entries itself, so `Use`
can check that this module does not re-export inherited local-persistent entries.
-/

def importedThroughMiddle : Bool := true
