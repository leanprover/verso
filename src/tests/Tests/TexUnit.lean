/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jason Reed
-/
import Tests.TexUtil

/-!
Unit tests covering TeX output given given concrete Verso structures.
-/

open Verso Genre.Manual

/-- info: before\LeanVerb|verb|after -/
#guard_msgs in
#eval do
  let b : Doc.Block Genre.Manual := .concat #[
    .para #[
      .text "before",
      .other (Inline.leanFromMarkdown default) #[.code "verb"],
      .text "after"
    ]
  ]
  IO.println (← toTex b).asString

/-- info: before\LeanVerb|verb|after -/
#guard_msgs in
#eval do
  let b : Doc.Block Genre.Manual := .concat #[
    .para #[
      .text "before",
      .code "verb",
      .text "after"
    ]
  ]
  IO.println (← toTex b).asString
