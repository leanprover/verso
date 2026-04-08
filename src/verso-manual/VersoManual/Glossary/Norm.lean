/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Verso.Doc
public import VersoManual.Basic

open Verso.Genre

namespace Verso.Genre.Manual

public partial def techString (text : Doc.Inline Manual) : String :=
  match text with
  | .code str | .math _ str | .text str | .linebreak str => str
  | .image .. | .footnote .. => ""
  | .other _ txt
  | .concat txt
  | .bold txt
  | .emph txt
  | .link txt _href => String.join <| txt.toList.map techString

-- Implements the normalization procedure used in Scribble
public partial def normString (term : String) : String := Id.run do
  let mut str := term.toLower
  if str.endsWith "ies" then
    str := (str.dropEnd 3).copy ++ "y"
  if str.endsWith "s" then
    str := str.dropEnd 1 |>.copy
  str := str.replace "‑" "-"
  String.intercalate " " (str.splitToList (fun c => c.isWhitespace || c == '-') |>.filter (!·.isEmpty))
