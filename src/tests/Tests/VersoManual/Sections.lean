/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/
import VersoManual

namespace DocstringSectionRegression

open Verso Output Genre Manual

/-- A fixture for Manual docstring subsection HTML rendering. -/
structure SectionFixture where
  /-- Field documentation. -/
  field : Nat

/-- A fixture for Manual docstring constructor subsection HTML rendering. -/
inductive ConstructorFixture where
  /-- Constructor documentation. -/
  | intro : ConstructorFixture

#docs (Manual) doc "Docstring section labels" :=
:::::::

{docstring SectionFixture}

{docstring ConstructorFixture}

:::::::

private def hasSubstring (s sub : String) : Bool :=
  s.find? sub |>.isSome

private def compactHtml (s : String) : String :=
  s.foldl (init := "") fun out c =>
    if c.isWhitespace then out else out.push c

private def renderDoc : IO String := do
  let rendered ← IO.mkRef ""
  let exitCode ← withLogger fun logger => do
    let cfg : RenderConfig := {}
    let (part, state) ← (traverseHtmlSingle cfg doc.toPart).run extension_impls% |>.run logger
    let ctxt : Manual.TraverseContext := {}
    let definitionIds := state.definitionIds ctxt
    let remotes : Multi.AllRemotes := {}
    let linkTargets := cfg.linkTargets state remotes
    let (html, _) ←
      (Manual.toHtml (m := ReaderT Multi.AllRemotes (ReaderT ExtensionImpls (BuildLogT IO)))
          {} ctxt state definitionIds linkTargets {} part).run {}
        |>.run remotes
        |>.run extension_impls%
        |>.run logger
    rendered.set html.asString
  unless exitCode == 0 do
    throw <| IO.userError "Manual docstring HTML rendering logged errors"
  rendered.get

private def assertLabeledSection (compact label : String) : IO Unit := do
  let id := s!"docstring-section-{label}"
  let group := s!"<divclass=\"docstring-section\"role=\"group\"aria-labelledby=\"{id}\">"
  unless hasSubstring compact group do
    throw <| IO.userError s!"{label} section should render as a named group"
  let labelHtml := s!"<pclass=\"docstring-section-label\"id=\"{id}\">{label}</p>"
  unless hasSubstring compact labelHtml do
    throw <| IO.userError s!"{label} section should use a paragraph label with the group's ID"
  if hasSubstring compact s!"<h1>{label}</h1>" then
    throw <| IO.userError s!"{label} section label should not render as h1"

/--
info: docstring section labels render as labeled groups
-/
#guard_msgs in
#eval show IO Unit from do
  let compact := compactHtml (← renderDoc)
  assertLabeledSection compact "Fields"
  assertLabeledSection compact "Constructors"
  IO.println "docstring section labels render as labeled groups"
