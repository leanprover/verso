/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual.Html
import VersoManual

namespace Verso.Genre.Manual.Html

open Verso.Output.Html

section
open Toc Zipper

/--
Specification for the preorder traversal implemented by the local navigation buttons.

Use this for testing!
-/
def Toc.preorder (toc : Toc) : List Toc :=
  toc :: toc.children.attach.flatMap fun ⟨t, h⟩ =>
    have := List.sizeOf_lt_of_mem h
    have : sizeOf toc.children < sizeOf toc := by
      cases toc
      simp +arith
    preorder t
termination_by toc


private def testToc : Toc where
  title := "ROOT"
  path := #[]
  id := none
  sectionNum := none
  children := [
    {title := "A", path := #["A"], id := none, sectionNum := none, children := []},
    { title := "B", path := #["B"], id := none, sectionNum := none,
      children := [
        {title := "B1", path := #["B", "1"], id := none, sectionNum := none, children := []},
        { title := "B2", path := #["B", "2"], id := none, sectionNum := none, children := [
            {title := "B2a", path := #["B", "2", "a"], id := none, sectionNum := none, children := []}
          ]
        }
      ]
    },
    {title := "C", path := #["C"], id := none, sectionNum := none, children := [
        {title := "C1", path := #["C", "1"], id := none, sectionNum := none, children := []},
        {title := "C2", path := #["C", "2"], id := none, sectionNum := none, children := []}
      ]
    },
    {title := "D", path := #["D"], id := none, sectionNum := none, children := []},
  ]


/--
info: Expected #[], seeing #[]
	Prev: none
	Up: none
	Next: (some #[A])
Expected #[A], seeing #[A]
	Prev: (some #[])
	Up: (some #[])
	Next: (some #[B])
Expected #[B], seeing #[B]
	Prev: (some #[A])
	Up: (some #[])
	Next: (some #[B, 1])
Expected #[B, 1], seeing #[B, 1]
	Prev: (some #[B])
	Up: (some #[B])
	Next: (some #[B, 2])
Expected #[B, 2], seeing #[B, 2]
	Prev: (some #[B, 1])
	Up: (some #[B])
	Next: (some #[B, 2, a])
Expected #[B, 2, a], seeing #[B, 2, a]
	Prev: (some #[B, 2])
	Up: (some #[B, 2])
	Next: (some #[C])
Expected #[C], seeing #[C]
	Prev: (some #[B, 2, a])
	Up: (some #[])
	Next: (some #[C, 1])
Expected #[C, 1], seeing #[C, 1]
	Prev: (some #[C])
	Up: (some #[C])
	Next: (some #[C, 2])
Expected #[C, 2], seeing #[C, 2]
	Prev: (some #[C, 1])
	Up: (some #[C])
	Next: (some #[D])
Expected #[D], seeing #[D]
	Prev: (some #[C, 2])
	Up: (some #[])
	Next: none
Done
-/
#guard_msgs in
#eval show IO Unit from do
  let mut here : Zipper := ⟨[], testToc⟩
  let spec := testToc.preorder

  for s in spec do
    IO.println s!"Expected {s.path}, seeing {here.focus.path}"
    IO.println s!"\tPrev: {here.prev |>.map (fun (z : Zipper) => z.focus.path)}"
    IO.println s!"\tUp: {here.up? |>.map (fun (z : Zipper) => z.focus.path)}"
    IO.println s!"\tNext: {here.next |>.map (fun (z : Zipper) => z.focus.path)}"
    if let some n := here.next then
      here := n
    else
      IO.println "Done"
      break

end

namespace DocstringSectionRegression

open Verso
open Verso.Output
open Verso.Genre.Manual

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
