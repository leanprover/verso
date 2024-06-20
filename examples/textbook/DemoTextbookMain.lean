/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Genre.Manual

import DemoTextbook

open Verso.Genre.Manual

-- TODO: metaprogram this away
def impls := ExtensionImpls.fromLists
  [(``DemoTextbook.Exts.index, DemoTextbook.Exts.index.descr),
   (``DemoTextbook.Exts.see, DemoTextbook.Exts.see.descr),
   (``DemoTextbook.Exts.seeAlso, DemoTextbook.Exts.seeAlso.descr)]
  [(``Block.paragraph, paragraph.descr),
   (``Block.docstring, docstring.descr),
   (``DemoTextbook.Exts.theIndex, DemoTextbook.Exts.theIndex.descr),
   (``DemoTextbook.Exts.lean, DemoTextbook.Exts.lean.descr)]

def buildExercises (_ctxt : TraverseContext) (_state : TraverseState) : IO Unit :=
  IO.println "Placeholder generator for output exercise and solution Lean code"

def main := manualMain impls (%doc DemoTextbook) (extraSteps := [buildExercises])
