/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual.Html

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
