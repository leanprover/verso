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

/-- A Lean name that ends with random hexadecimal digits. -/
private def leanName : LoremGen String := do
  let w := bareWord (← Lorem.word) |>.toLower
  let w := if w.isEmpty then "lorem" else w
  let n := (← Gen.choose Nat 0 (2 ^ 32 - 1) (Nat.zero_le _)).val
  return s!"{w}_{(BitVec.ofNat 32 n).toHex}"

/-- The tactics that close the goals of generated theorems. -/
def closingTactics : List String := ["decide", "omega", "simp", "rfl"]

/-- Generates a Lean command, as lines. -/
private def leanCommand (params : Params) : LoremGen (Array String) := do
  let a := (← Gen.choose Nat 0 50 (by decide)).val
  let b := (← Gen.choose Nat 0 50 (by decide)).val
  match (← Gen.choose Nat 0 2 (by decide)).val with
  | 0 => return #[s!"def {← leanName} : Nat := {a}"]
  | 1 =>
    let sleep := if params.proofWeight > 0 then #[s!"  sleep {params.proofWeight}"] else #[]
    return #[s!"theorem {← leanName} : {a} + {b} = {a + b} := by"] ++ sleep ++
      #["  " ++ (← Gen.elements closingTactics (by decide))]
  | _ => return #[s!"example : {a} < {a + b + 1} := by decide"]

/-- The commands of some Lean code, as their first line and number of lines. -/
def leanCommands (lines : Array String) : Array (Nat × Nat) := Id.run do
  let mut out := #[]
  let mut start? : Option Nat := none
  for (l, i) in lines.zipIdx do
    if l.isEmpty then
      if let some s := start? then out := out.push (s, i - s)
      start? := none
    else if start?.isNone then start? := some i
  if let some s := start? then out := out.push (s, lines.size - s)
  return out

/--
Contents that are Lean commands separated by blank lines: definitions, examples and theorems. Each
theorem's proof sleeps for {name}`Params.proofWeight` milliseconds. Commands may be added or
removed, and proof steps may change.
-/
def leanContent : CodeBlockContent where
  generate params := do
    let mut out := #[]
    for i in [0:(← Gen.choose Nat 1 3 (by decide)).val] do
      out := out ++ (if i > 0 then #[""] else #[]) ++ (← leanCommand params)
    return out
  edits params lines :=
    let cmds := leanCommands lines
    [ do
        let cmd ← leanCommand params
        if h : 0 < cmds.size then
          let ⟨i, _, hi⟩ ← Gen.chooseNatLt 0 cmds.size h
          let (s, _) := cmds[i]
          return some { label := "add command", start := s, count := 0, lines := cmd ++ #[""] }
        else
          return some { label := "add command", start := lines.size, count := 0, lines := cmd },
      do
        if h : 1 < cmds.size then
          let ⟨i, _, hi⟩ ← Gen.chooseNatLt 0 cmds.size (by grind)
          let (s, n) := cmds[i]
          -- The command goes with the blank line that follows it, or else the one before it.
          if s + n < lines.size then
            return some { label := "remove command", start := s, count := n + 1, lines := #[] }
          else
            return some { label := "remove command", start := s - 1, count := n + 1, lines := #[] }
        else return none,
      do
        let proofs := cmds.filter fun (s, n) => n ≥ 2 && lines[s]!.startsWith "theorem"
        if h : 0 < proofs.size then
          let ⟨i, _, hi⟩ ← Gen.chooseNatLt 0 proofs.size h
          let (s, n) := proofs[i]
          let last := s + n - 1
          let current := lines[last]!.trimAscii
          let others := closingTactics.filter (·.toSlice != current)
          if h : 0 < others.length then
            let tac ← Gen.elements others h
            return some
              { label := "change proof step", start := last, count := 1, lines := #["  " ++ tac] }
          else return none
        else return none
    ]

/--
The manual genre profile: the {lit}`Manual` genre with {lit}`verso-manual`'s directives, roles and
metadata.
-/
public def manualProfile : GenreProfile where
  name := "manual"
  imports := ["VersoManual"]
  opens := ["Verso.Genre", "Manual", "InlineLean"]
  genre := "Manual"
  directives := [
    { name := "paragraph", contains := [.para, .ul, .ol, .code] },
    { name := "draft",
      contains := BlockKind.exceptDefinitions }
  ]
  codeBlocks :=
    [{ name := "lean", args := Gen.elements ["", "-show"] (by decide), content := leanContent }]
  commands :=
    [{ name := "docstring",
       args := Gen.elements ["Nat.add", "List.map", "Array.push", "Option.map"] (by decide) }]
  roles := [
    { name := "draft" },
    { name := "margin" },
    { name := "lean", inlineContent := false,
      code := Gen.elements ["1 + 1", "Nat.succ 2", "[1, 2, 3]", "(3 : Nat)"] (by decide) },
    { name := "name", inlineContent := false,
      code := Gen.elements ["Nat", "List.map", "Nat.add", "Array"] (by decide) }
  ]
  metadata := [
    { name := "tag", value := quoted Lorem.label },
    { name := "shortTitle", value := quoted Lorem.title },
    { name := "number", value := Gen.elements ["true", "false"] (by decide) },
    { name := "draft", value := Gen.elements ["true", "false"] (by decide) }
  ]
