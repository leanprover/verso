/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso.Font

/-!
Compile-time tests for `Verso.Font`: the `define_font_face` command embeds file bytes, `Weight`
literals clamp into range, and `Typeface.cssFamily` renders (and escapes) as expected. There is no
general font file to bundle yet, so an existing KaTeX font stands in for the embedding test.
-/

open Verso

-- `define_font_face` embeds the file's bytes at compile time.
define_font_face katexMono where
  format := .woff2
  file := "../../../vendored-js/katex/fonts/KaTeX_Typewriter-Regular.woff2"

/-- info: true -/
#guard_msgs in #eval decide (katexMono.bytes.size > 1000)
/-- info: Verso.FontFormat.woff2 -/
#guard_msgs in #eval katexMono.format
/-- info: Verso.FontStyle.normal -/
#guard_msgs in #eval katexMono.style

-- `weight :=` is sugar for `weights := .fixed _`; `style` and the file format are honored.
define_font_face boldItalicFace where
  weight := .bold
  style := .italic
  format := .ttf
  file := "../../../vendored-js/katex/fonts/KaTeX_Typewriter-Regular.ttf"

/-- info: some 700 -/
#guard_msgs in
#eval match boldItalicFace.weights with
  | .fixed w => some w.val
  | _ => none
/-- info: true -/
#guard_msgs in #eval boldItalicFace.style = .italic

-- Named weights and the clamping `OfNat`.
/-- info: 400 -/
#guard_msgs in #eval Weight.regular.val
/-- info: 600 -/
#guard_msgs in #eval Weight.semibold.val
/-- info: 1000 -/
#guard_msgs in #eval (1500 : Weight).val
/-- info: 1 -/
#guard_msgs in #eval (0 : Weight).val

-- Default typefaces expand to system stacks; a custom family is quoted and escaped.
/-- info: "ui-sans-serif, system-ui, sans-serif" -/
#guard_msgs in #eval Typeface.sans.cssFamily
/-- info: "\"Fancy\"" -/
#guard_msgs in #eval (Typeface.files "Fancy" #[]).cssFamily
/-- info: "\"a\\\"b\"" -/
#guard_msgs in #eval (Typeface.files "a\"b" #[]).cssFamily

-- A missing required field is an error.
/-- error: `define_font_face` requires a `format` field -/
#guard_msgs in
define_font_face noFormat where
  file := "x.woff2"

/-- error: `define_font_face` requires a `file` field -/
#guard_msgs in
define_font_face noFile where
  format := .ttf
