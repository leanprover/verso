/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import Verso.Output.Html.Entities

open Verso.Output.Html

/-- info: some "&" -/
#test_msgs in
#eval decodeEntity? "&amp;"

/-- info: some "&" -/
#test_msgs in
#eval decodeEntity? "&AMP"

/-- info: some #["&AMP", "&AMP;", "&amp", "&amp;"] -/
#test_msgs in
#eval namedEntity? '&' |>.map (·.toArray |>.qsort)

/-- info: some " " -/
#test_msgs in
#eval decodeEntity? "&#32;"

/-- info: some " " -/
#test_msgs in
#eval decodeEntity? "&#x20;"

/-- info: none -/
#test_msgs in
#eval decodeEntity? "&#;"

/-- info: none -/
#test_msgs in
#eval decodeEntity? "&blah;"
