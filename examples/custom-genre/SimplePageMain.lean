/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SimplePage
import SimplePage.Demo

open Tutorial

def main (args : List String) := SimplePage.render (%doc SimplePage.Demo)
