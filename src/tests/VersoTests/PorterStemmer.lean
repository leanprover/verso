/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
meta import all VersoSearch.PorterStemmer
import Errata

namespace Verso.Tests.PorterStemmer

open Verso.Search.Stemmer.Porter

/-! ## Tests for measure function -/

/-- info: 0 -/
#test_msgs in
#eval measure "tr".toSlice
/-- info: 0 -/
#test_msgs in
#eval measure "ee".toSlice
/-- info: 0 -/
#test_msgs in
#eval measure "tree".toSlice

/-- info: 2 -/
#test_msgs in
#eval measure "private".toSlice

/-! ## Tests for step1a -/

/-- info: "abiliti" -/
#test_msgs in
#eval step1a "abilities".toSlice |>.copy

/-! ## Tests for step1b -/

/-- info: "abiliti" -/
#test_msgs in
#eval step1b "abiliti".toSlice |>.copy

/-- info: "caress" -/
#test_msgs in
#eval step1b (step1a "caresses".toSlice) |>.copy
/-- info: "poni" -/
#test_msgs in
#eval step1b (step1a "ponies".toSlice) |>.copy
/-- info: "ti" -/
#test_msgs in
#eval step1b (step1a "ties".toSlice) |>.copy
/-- info: "caress" -/
#test_msgs in
#eval step1b (step1a "caress".toSlice) |>.copy
/-- info: "cat" -/
#test_msgs in
#eval step1b (step1a "cats".toSlice) |>.copy

/-- info: "feed" -/
#test_msgs in
#eval step1b (step1a "feed".toSlice) |>.copy
/-- info: "agree" -/
#test_msgs in
#eval step1b (step1a "agreed".toSlice) |>.copy
/-- info: "disable" -/
#test_msgs in
#eval step1b (step1a "disabled".toSlice) |>.copy

/-- info: "mat" -/
#test_msgs in
#eval step1b (step1a "matting".toSlice) |>.copy
/-- info: "mate" -/
#test_msgs in
#eval step1b (step1a "mating".toSlice) |>.copy
/-- info: "meet" -/
#test_msgs in
#eval step1b (step1a "meeting".toSlice) |>.copy
/-- info: "mill" -/
#test_msgs in
#eval step1b (step1a "milling".toSlice) |>.copy
/-- info: "mess" -/
#test_msgs in
#eval step1b (step1a "messing".toSlice) |>.copy

/-- info: "meet" -/
#test_msgs in
#eval step1b (step1a "meetings".toSlice) |>.copy

/-! ## Tests for step1c -/

/-- info: "happi" -/
#test_msgs in
#eval step1c "happy".toSlice |>.copy

/-- info: "abiliti" -/
#test_msgs in
#eval step1c "abiliti".toSlice |>.copy

/-! ## Tests for step2 -/

/-- info: "sensible" -/
#test_msgs in
#eval step2 "sensibiliti".toSlice |>.copy

/-- info: "abiliti" -/
#test_msgs in
#eval step2 "abiliti".toSlice |>.copy

/-! ## Tests for step3 -/

/-- info: "form" -/
#test_msgs in
#eval step3 "formative".toSlice |>.copy

/-- info: "able" -/
#test_msgs in
#eval step3 "able".toSlice |>.copy

/-! ## Tests for step5b -/

/-- info: "control" -/
#test_msgs in
#eval step5b "controll".toSlice |>.copy
/-- info: "roll" -/
#test_msgs in
#eval step5b "roll".toSlice |>.copy
