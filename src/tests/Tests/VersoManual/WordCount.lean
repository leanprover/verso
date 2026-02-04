/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
meta import all VersoManual.WordCount

namespace Verso.Tests.VersoManual.WordCount

open Verso.Genre.Manual.WordCount

/-! ## Tests for countWords function -/

/-- info: 4 -/
#guard_msgs in
#eval countWords (fun _ => false) "a b c d"
/-- info: 4 -/
#guard_msgs in
#eval countWords (fun _ => false) "a b c    d"
/-- info: 4 -/
#guard_msgs in
#eval countWords (fun _ => false) "  a b c    d"

/-! ## Tests for separatedNumber function -/

/-- info: "0" -/
#guard_msgs in
#eval separatedNumber 0
/-- info: "55" -/
#guard_msgs in
#eval separatedNumber 55
/-- info: "555" -/
#guard_msgs in
#eval separatedNumber 555
/-- info: "51,535" -/
#guard_msgs in
#eval separatedNumber 51535
/-- info: "8,813,251,535" -/
#guard_msgs in
#eval separatedNumber 8813251535
/-- info: "4,002" -/
#guard_msgs in
#eval separatedNumber 4002
