/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Genre.Manual

import DemoTextbook

open Verso.Genre.Manual

def impls := ExtensionImpls.fromLists inline_extensions% block_extensions%

def buildExercises (_ctxt : TraverseContext) (_state : TraverseState) : IO Unit :=
  IO.println "Placeholder generator for output exercise and solution Lean code"

def main := manualMain impls (%doc DemoTextbook) (extraSteps := [buildExercises])
