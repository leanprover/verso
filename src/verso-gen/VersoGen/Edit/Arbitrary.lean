/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Plausible.Arbitrary
public import VersoGen.Edit.Construct
public import VersoGen.Genre.Minimal

set_option doc.verso true

namespace VersoGen.Edit

open VersoGen.Doc.SurfaceDoc VersoGen.Genre Plausible

/-- Documents of the minimal genre profile, with as many top-level blocks as the size. -/
public instance : Arbitrary Part where
  arbitrary := Gen.sized fun size =>
    (genDocument minimalProfile { topLevelBlocks := size, parts := size / 5 }).run' {}

/-- Top-level blocks of the minimal genre profile, without link or footnote uses. -/
public instance : Arbitrary Block where
  arbitrary := (newBlock minimalProfile {} false true).run' {}
