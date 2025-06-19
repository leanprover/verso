/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual
open Verso.Genre.Manual

-- Here, `inlines!` is a macro that parses a string constant into Verso inline elements

def someThesis : Bibliography.Thesis where
  title := inlines!"A Great Thesis"
  author := inlines!"A. Great Student"
  year := 2025
  university := inlines!"A University"
  degree := inlines!"Something"

def somePaper : Bibliography.InProceedings where
  title := inlines!"Grommulation of Flying Lambdas"
  authors := #[inlines!"A. Great Student"]
  year := 2025
  booktitle := inlines!"Proceedings of the Best Conference Ever"

def someArXiv : Bibliography.ArXiv where
  title := inlines!"Grommulation of Flying Lambdas"
  authors := #[inlines!"A. Great Student"]
  year := 2025
  id := "...insert arXiv id here..."

def someBook : Bibliography.Book where
  title := inlines!"A Good Book"
  authors := #[inlines!"A. Great Student"]
  year := 2025
  publisher := inlines!"Oxford University Press"
  series := some (inlines!"Series Books", 42)
  isbn := some "978-0-19-853779-3"
