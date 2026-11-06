/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jason Reed
-/
import Errata
import VersoTests.TexUtil

/-!
Unit tests covering TeX output given given concrete Verso structures.
-/

open Verso Genre.Manual

/-- info: before\LeanVerb|verb|after -/
#test_msgs in
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
#test_msgs in
#eval do
  let b : Doc.Block Genre.Manual := .concat #[
    .para #[
      .text "before",
      .code "verb",
      .text "after"
    ]
  ]
  IO.println (← toTex b).asString

/--
Returns the {lit}`\title` line of the Manual's TeX preamble for a root part, or throws an error if
the preamble has none. The title is rendered as {lit}`emitTeX` renders it.
-/
def preambleTitleLine (part : Doc.Part Genre.Manual) : IO String := do
  let logger ← Verso.Logger.new
  let options : Doc.TeX.Options Genre.Manual := { headerLevel := none }
  let title ← part.titleToTeX (m := EmitM)
    |>.run (options, {}, .initialize {}, {}) |>.run' {}
    |>.run extension_impls% |>.run logger
  let preamble := TeX.preamble (title := title.asString) (authors := []) (date := "")
    (packages := []) (extraPreamble := []) (twoside := false)
  for line in preamble.lines do
    if line.startsWith "\\title{" then return line.toString
  throw <| .userError "The preamble has no \\title line."

#docs (Genre.Manual) mathRootTitle "$`x_1^2`" :=
:::::::
Text.
:::::::

/-
Manuals whose root titles are inline math have that math, typeset as math, as their TeX titles.
-/
/-- info: \title{\sffamily $x_1^2$} -/
#test_msgs in
#eval do IO.println (← preambleTitleLine mathRootTitle.toPart)

#docs (Genre.Manual) codeRootTitle "`a_b^c & d % e # f`" :=
:::::::
Text.
:::::::

/-
Manuals whose root titles are inline code have that code as their TeX titles, in typewriter type
and with TeX's special characters escaped, so that LaTeX accepts it in a command argument.
-/
/--
info: \title{\sffamily \texttt{a\symbol{95}b\symbol{94}c \symbol{38} d \symbol{37} e \symbol{35} f}}
-/
#test_msgs in
#eval do IO.println (← preambleTitleLine codeRootTitle.toPart)

#docs (Genre.Manual) plainRootTitle "A Plain Title" :=
:::::::
Text.
:::::::

/-
Root titles without characters that are special in TeX appear unchanged in Manuals' TeX titles.
-/
/-- info: \title{\sffamily A Plain Title} -/
#test_msgs in
#eval do IO.println (← preambleTitleLine plainRootTitle.toPart)
