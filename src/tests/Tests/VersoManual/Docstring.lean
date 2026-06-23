/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
meta import all VersoManual.Docstring

namespace Verso.Tests.VersoManual.Docstring

open Verso.Genre.Manual

/-! ## Tests for `indentColumn`

`indentColumn` finds the smallest indentation of any nonblank line, which is the common indentation
to strip when rendering a docstring's code block.
-/

/-- info: 0 -/
#guard_msgs in
#eval indentColumn ""
/-- info: 0 -/
#guard_msgs in
#eval indentColumn "abc"
/-- info: 3 -/
#guard_msgs in
#eval indentColumn "   abc"
/-- info: 3 -/
#guard_msgs in
#eval indentColumn "   abc\n\n   def"
/-- info: 2 -/
#guard_msgs in
#eval indentColumn "   abc\n\n  def"
/-- info: 2 -/
#guard_msgs in
#eval indentColumn "   abc\n\n  def\n    a"
