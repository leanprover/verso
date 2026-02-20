/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
meta import all VersoManual.License

namespace Verso.Tests.VersoManual.License

open Verso.Genre.Manual

/-! ## Tests for paragraphed function -/

/-- info: #["One paragraph with lines", "and another", "and more more"] -/
#guard_msgs in
#eval paragraphed r#"

One paragraph
with lines

and another

and more
more

"#
