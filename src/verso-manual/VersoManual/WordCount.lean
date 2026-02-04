/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Verso.Doc
import Verso.Method
public import VersoManual.Basic

open Verso.Doc
open Lean (Name)

public section

namespace Verso.Genre.Manual
namespace WordCount

class WordCount (α) where
  countWords (skip : Name → Bool) : α → Nat

export WordCount (countWords)

instance [WordCount α] : WordCount (Array α) where
  countWords skip xs := Id.run do
    let mut c := 0
    for x in xs do
      c := c + countWords skip x
    return c

instance : WordCount String where
  countWords _ (str : String) := Id.run do
    let mut wc := 0
    let mut iter := str.startPos
    let mut state := false
    while h : iter ≠ str.endPos do
      let curr := iter.get h
      iter := iter.next h
      match state with
      | false => -- not in a word
        if !curr.isWhitespace then
          state := true
          wc := wc + 1
      | true => -- in a word
        if curr.isWhitespace then
          state := false
    return wc

partial instance : WordCount (Verso.Doc.Inline Manual) where
  countWords skip i := inlineWordCount skip i
where
  inlineWordCount skip (i : Verso.Doc.Inline Manual) : Nat :=
    let _ : WordCount (Verso.Doc.Inline Manual) := ⟨inlineWordCount⟩
    match i with
    | .text content
    | .concat content
    | .image content _ -- alt text
    | .link content _ -- link text
    | .footnote _ content
    | .bold content
    | .emph content
    | .code content
    | .math _ content => countWords skip content
    | .other i content =>
      if skip i.name then 0 else countWords skip content
    | .linebreak .. => 0


instance [WordCount α] [WordCount β] : WordCount (DescItem α β) where
  countWords skip | ⟨dt, dd⟩ => countWords skip dt + countWords skip dd

instance [WordCount α] : WordCount (ListItem α) where
  countWords skip | ⟨item⟩ => countWords skip item

partial instance : WordCount (Verso.Doc.Block Manual) where
  countWords skip b := blockWordCount skip b
where
  blockWordCount skip (b : Verso.Doc.Block Manual) : Nat :=
    let _ : WordCount (Verso.Doc.Block Manual) := ⟨blockWordCount⟩
    match b with
    | .para content
    | .concat content
    | .blockquote content
    | .code content
    | .dl content
    | .ol _ content
    | .ul content => countWords skip content
    | .other k content =>
      if skip k.name then 0 else countWords skip content

def separatedNumber (n : Nat) : String :=
  if n > 999 then
    let before := n / 1000
    let after := n % 1000 |> toString
    let padding := (3 - after.length).repeat ("0" ++ ·) ""
    s!"{separatedNumber before},{padding}{after}"
  else
    s!"{n}"

partial def wordCountReport (skip : Name → Bool) (indent : String) (depth : Nat) (p : Part Manual) : Nat × String := Id.run do
  let subReports := p.subParts.mapIdx fun i p =>
    wordCountReport skip s!"{indent}{i+1}." (depth - 1) p
  let subCount := subReports.foldr (init := 0) (·.1 + ·)
  let (here, str) := partLine p subCount
  let mut out := s!"{indent} {str}"
  unless subReports.isEmpty do
    for (_, txt) in subReports do
      if depth > 0 then
        out := out ++ txt
    let spaced := indent.length.repeat (·.push ' ') ""
    if depth > 0 then
      out := out ++ s!"{spaced}----------------\n"
      let total := if indent.isEmpty then "Total" else "Subtotal"
      out := out ++ s!"{spaced}{total} ({p.titleString}): {separatedNumber <| here + subCount}\n"
  -- Blank line between chapters
  if isChapter then
    out := out ++ "\n"
  (here + subCount, out)
where
  isChapter : Bool :=
    indent.foldl (init := 0) (· + if · == '.' then 1 else 0) == 1

  partLine (p : Part Manual) (subCount : Nat) : Nat × String :=
    let count := countWords skip p.content
    (countWords skip p.content, p.titleString ++ s!" ({separatedNumber <| count + subCount})\n")
