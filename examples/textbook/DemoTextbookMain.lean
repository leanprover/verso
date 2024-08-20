/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import DemoTextbook

open Verso.Genre.Manual

def buildExercises (_ctxt : TraverseContext) (_state : TraverseState) : IO Unit :=
  IO.println "Placeholder generator for output exercise and solution Lean code"

def main := manualMain (%doc DemoTextbook) (extraSteps := [buildExercises])
