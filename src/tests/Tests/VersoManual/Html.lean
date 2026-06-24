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

#docs (Manual) doc "Docstring section labels" :=
:::::::

{docstring SectionFixture}

:::::::

private def hasSubstring (s sub : String) : Bool :=
  s.find? sub |>.isSome

private def compactHtml (s : String) : String :=
  String.ofList <| s.toList.filter (fun c => !c.isWhitespace)

private def renderDoc : IO String := do
  let cfg : RenderConfig := {}
  let logger ← Logger.new
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
  unless (← logger.exitCode) == 0 do
    throw <| IO.userError "Manual docstring HTML rendering logged errors"
  pure html.asString

/--
info: docstring section labels render as labeled groups
-/
#guard_msgs in
#eval show IO Unit from do
  let compact := compactHtml (← renderDoc)
  let group :=
    "<divclass=\"docstring-section\"role=\"group\"aria-labelledby=\"docstring-section-Fields\">"
  unless hasSubstring compact group do
    throw <| IO.userError "Fields section should render as a named group"
  let label :=
    "<pclass=\"docstring-section-label\"id=\"docstring-section-Fields\">Fields</p>"
  unless hasSubstring compact label do
    throw <| IO.userError "Fields section should use a paragraph label with the group's ID"
  if hasSubstring compact "<h1>Fields</h1>" then
    throw <| IO.userError "Fields section label should not render as h1"
  IO.println "docstring section labels render as labeled groups"

end DocstringSectionRegression
