/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jason Reed
-/
module
meta import all Verso.Code.HighlightedToTex

open SubVerso.Highlighting

/-- info: "\\symbol{123}\\symbol{124}\\symbol{125}\\symbol{92}" -/
#guard_msgs in
#eval escapeForVerbatim "{|}\\"
