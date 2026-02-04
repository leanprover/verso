/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
meta import all VersoSearch.PorterStemmer

namespace Verso.Tests.PorterStemmer

open Verso.Search.Stemmer.Porter

/-! ## Tests for measure function -/

/-- info: 0 -/
#guard_msgs in
#eval measure "tr".toSlice
/-- info: 0 -/
#guard_msgs in
#eval measure "ee".toSlice
/-- info: 0 -/
#guard_msgs in
#eval measure "tree".toSlice

/-- info: 2 -/
#guard_msgs in
#eval measure "private".toSlice

/-! ## Tests for step1a -/

/-- info: "abiliti" -/
#guard_msgs in
#eval step1a "abilities".toSlice |>.copy

/-! ## Tests for step1b -/

/-- info: "abiliti" -/
#guard_msgs in
#eval step1b "abiliti".toSlice |>.copy

/-- info: "caress" -/
#guard_msgs in
#eval step1b (step1a "caresses".toSlice) |>.copy
/-- info: "poni" -/
#guard_msgs in
#eval step1b (step1a "ponies".toSlice) |>.copy
/-- info: "ti" -/
#guard_msgs in
#eval step1b (step1a "ties".toSlice) |>.copy
/-- info: "caress" -/
#guard_msgs in
#eval step1b (step1a "caress".toSlice) |>.copy
/-- info: "cat" -/
#guard_msgs in
#eval step1b (step1a "cats".toSlice) |>.copy

/-- info: "feed" -/
#guard_msgs in
#eval step1b (step1a "feed".toSlice) |>.copy
/-- info: "agree" -/
#guard_msgs in
#eval step1b (step1a "agreed".toSlice) |>.copy
/-- info: "disable" -/
#guard_msgs in
#eval step1b (step1a "disabled".toSlice) |>.copy

/-- info: "mat" -/
#guard_msgs in
#eval step1b (step1a "matting".toSlice) |>.copy
/-- info: "mate" -/
#guard_msgs in
#eval step1b (step1a "mating".toSlice) |>.copy
/-- info: "meet" -/
#guard_msgs in
#eval step1b (step1a "meeting".toSlice) |>.copy
/-- info: "mill" -/
#guard_msgs in
#eval step1b (step1a "milling".toSlice) |>.copy
/-- info: "mess" -/
#guard_msgs in
#eval step1b (step1a "messing".toSlice) |>.copy

/-- info: "meet" -/
#guard_msgs in
#eval step1b (step1a "meetings".toSlice) |>.copy

/-! ## Tests for step1c -/

/-- info: "happi" -/
#guard_msgs in
#eval step1c "happy".toSlice |>.copy

/-- info: "abiliti" -/
#guard_msgs in
#eval step1c "abiliti".toSlice |>.copy

/-! ## Tests for step2 -/

/-- info: "sensible" -/
#guard_msgs in
#eval step2 "sensibiliti".toSlice |>.copy

/-- info: "abiliti" -/
#guard_msgs in
#eval step2 "abiliti".toSlice |>.copy

/-! ## Tests for step3 -/

/-- info: "form" -/
#guard_msgs in
#eval step3 "formative".toSlice |>.copy

/-- info: "able" -/
#guard_msgs in
#eval step3 "able".toSlice |>.copy

/-! ## Tests for step5b -/

/-- info: "control" -/
#guard_msgs in
#eval step5b "controll".toSlice |>.copy
/-- info: "roll" -/
#guard_msgs in
#eval step5b "roll".toSlice |>.copy
