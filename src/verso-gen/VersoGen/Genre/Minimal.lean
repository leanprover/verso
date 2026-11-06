/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoGen.Genre.Basic

set_option doc.verso true

namespace VersoGen.Genre

open VersoGen.Doc.SurfaceDoc VersoGen.Random VersoGen.Text Plausible

/-- A line of lorem ipsum text. -/
private def textLine : LoremGen String := do words (← Gen.choose Nat 3 8 (by decide)).val

/-- Contents that are lines of lorem ipsum text. Any line may be inserted, removed or changed. -/
def plainContent : CodeBlockContent where
  generate _ := do
    let mut out := #[]
    for _ in [0:(← Gen.choose Nat 1 4 (by decide)).val] do
      out := out.push (← textLine)
    return out
  edits _ lines := [
    do
      let start := (← Gen.choose Nat 0 lines.size (Nat.zero_le _)).val
      return some { label := "insert line", start, count := 0, lines := #[← textLine] },
    do
      if h : 1 < lines.size then
        let start := (← Gen.chooseNatLt 0 lines.size (by grind)).val
        return some { label := "remove line", start, count := 1, lines := #[] }
      else return none,
    do
      if h : 0 < lines.size then
        let start := (← Gen.chooseNatLt 0 lines.size h).val
        return some { label := "change line", start, count := 1, lines := #[← textLine] }
      else return none
  ]

/-- The minimal genre profile: Verso core with the small genre {lit}`TestGenre`. -/
public def minimalProfile : GenreProfile where
  name := "minimal"
  imports := ["VersoGen.Genre.Test"]
  opens := ["VersoGen.Genre"]
  genre := "TestGenre"
  directives := [
    { name := "note",
      contains := BlockKind.exceptDefinitions },
    { name := "aside", args := quoted Lorem.title, contains := [.para, .ul, .ol, .code],
      mayNest := false }
  ]
  codeBlocks := [{ name := "plain", content := plainContent }]
  commands := [{ name := "separator" }]
  roles := [
    { name := "highlight" },
    { name := "term", inlineContent := false, code := do return bareWord (← Lorem.word) |>.toLower }
  ]
  metadata := [
    { name := "tag", value := quoted Lorem.label },
    { name := "draft", value := Gen.elements ["true", "false"] (by decide) },
    { name := "shortTitle", value := quoted Lorem.title }
  ]
