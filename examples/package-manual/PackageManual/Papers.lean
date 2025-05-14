/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual
open Verso.Genre.Manual

namespace PackageManual


-- Here, `inlines!` is a macro that parses a string constant into Verso inline elements

def someThesis : Thesis where
  title := inlines!"A Great Thesis"
  author := inlines!"A. Great Student"
  year := 2025
  university := inlines!"A University"
  degree := inlines!"Something"

def somePaper : InProceedings where
  title := inlines!"Grommulation of Flying Lambdas"
  authors := #[inlines!"A. Great Student"]
  year := 2025
  booktitle := inlines!"Proceedings of the Best Conference Ever"

def someArXiv : ArXiv where
  title := inlines!"Grommulation of Flying Lambdas"
  authors := #[inlines!"A. Great Student"]
  year := 2025
  id := "...insert arXiv id here..."

def theZipper : Article where
  title := inlines!"The Zipper"
  authors := #[inlines!"Gerard Huet"]
  journal := inlines!"Journal of Functional Programming"
  year := 1997
  month := some inlines!"September"
  volume := inlines!"7"
  number := inlines!"5"
  pages := some (549, 554)
