/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import VersoSearch.PorterStemmer
import Errata

open Verso.Search.Stemmer.Porter Errata

/-!
Tests the Porter stemmer against the standard vocabulary and its expected output.
-/

/-- The Porter stemmer reproduces the reference output for every word in the standard vocabulary. -/
@[test]
def porterStemmer : Test := do
  let vocabulary := (include_str "../stemmer/voc.txt").splitOn "\n"
  let expected := (include_str "../stemmer/output.txt").splitOn "\n"
  let mut mismatches : Array String := #[]
  for word in vocabulary, want in expected do
    let got := porterStem word
    unless got == want do
      mismatches := mismatches.push s!"{word} --> {got} (wanted '{want}')"
  unless mismatches.isEmpty do
    fail s!"{mismatches.size} stemmer mismatches"
      (detail? := some ("\n".intercalate mismatches.toList))
