/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import MultiVerso
import Verso
import VersoLiterateCode
import VersoManual
import VersoUtil

set_option doc.verso true

/-!
This test checks that each {attr}`grind` annotation in Verso keeps the number of theorem instances
that {tactic}`grind` produces small, with {syntax command}`#grind_lint check` once per library that
has such annotations. It matters whenever someone adds or changes a {attr}`grind` attribute.

-/

#test_msgs in
#grind_lint check (min := 10) (detailed := 50) in module MultiVerso

#test_msgs in
#grind_lint check (min := 10) (detailed := 50) in module Verso

#test_msgs in
#grind_lint check (min := 10) (detailed := 50) in module VersoLiterateCode

#test_msgs in
#grind_lint check (min := 10) (detailed := 50) in module VersoManual

#test_msgs in
#grind_lint check (min := 10) (detailed := 50) in module VersoUtil

