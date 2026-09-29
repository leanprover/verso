/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoGen.Doc.Basic

set_option doc.verso true

open VersoGen.Doc.SurfaceDoc

namespace Verso.Tests.VersoGen

def para (s : String) : Block := .para #[.text s]

/-- The reuse benchmark's results, relative to the repository root, where the tests run. -/
def benchResults : System.FilePath := "bench" / "reuse" / "expected"

/-- The reuse benchmark's corpus of edit scripts, relative to the repository root. -/
def benchCorpus : System.FilePath := "bench" / "reuse" / "corpus"
