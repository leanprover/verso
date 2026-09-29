/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoGen.Genre.Basic

set_option doc.verso true

namespace VersoGen.Edit

open VersoGen.Doc.SurfaceDoc VersoGen.Genre VersoGen.Random VersoGen.Text Plausible

/-- A generated block, with the definitions of the link and footnote labels that it uses. -/
public structure Generated where
  block : Block
  defs : Array Block := #[]
deriving Inhabited

/-- The words as one text inline, separated by spaces, or no inlines for no words. -/
private def textOf (ws : Array String) : Array Inline :=
  if ws.isEmpty then #[]
  else #[.text (ws.foldl (init := "") fun out w => if out.isEmpty then w else out ++ " " ++ w)]

/--
Generates an inline element around a sequence of a sentence's words, or next to it. It returns the
inlines that replace the sequence and the definitions of the labels that they use. With
{name}`refs`, the inline may be a link or footnote use with a new definition.
-/
def genInline (p : GenreProfile) (params : Params) (words : Array String) (refs : Bool) :
    LoremGen (Array Inline × Array Block) := do
  let text := textOf words
  let useRef := refs && (← chance params.referenceChance)
  if useRef && (p.linkDefs || p.footnoteDefs) then
    if p.linkDefs && (!p.footnoteDefs || (← chance 50)) then
      let n ← Lorem.label
      let url := s!"https://example.com/{bareWord (← Lorem.word) |>.toLower}"
      return (#[.link text (.ref n)], #[.linkDef n url])
    else
      let n ← Lorem.label
      let content ← sentence
      return (text.push (.footnote n), #[.footnoteDef n #[.text content]])
  let url := s!"https://example.com/{bareWord (← Lorem.word) |>.toLower}"
  let which := (← Gen.choose Nat 0 (if p.roles.isEmpty then 4 else 6) (Nat.zero_le _)).val
  match which with
  | 0 => return (#[.emph text], #[])
  | 1 => return (#[.bold text], #[])
  | 2 => return (#[.link text (.url url)], #[])
  | 3 =>
    let code := bareWords words
    return (#[.code (if code.isEmpty then "lorem" else code)], #[])
  | 4 => return (text.push (.image (bareWord (← Lorem.word)) (url ++ ".png")), #[])
  | _ =>
    if h : p.roles = [] then return (text, #[]) else
    let spec ← Gen.elements p.roles (List.length_pos_iff.mpr h)
    let args ← spec.args
    if spec.inlineContent then return (#[.role spec.name args text], #[])
    else return (#[.role spec.name args #[.code (← spec.code)]] ++ text, #[])

/--
Generates a paragraph's inlines and the definitions of the labels that they use. With {name}`refs`,
the inlines may include link and footnote uses with new definitions.
-/
public def genInlines (p : GenreProfile) (params : Params) (refs : Bool) :
    LoremGen (Array Inline × Array Block) := do
  let n := (← Gen.choose Nat 1 (Nat.max 1 params.paragraphLength) (Nat.le_max_left ..)).val
  let mut out : Array Inline := #[]
  let mut defs : Array Block := #[]
  for _ in [0:n] do
    let ws ← Lorem.sentenceWords
    if (← chance params.inlineChance) && ws.size ≥ 3 then
      let sequenceStart := (← Gen.choose Nat 0 (ws.size - 2) (Nat.zero_le _)).val
      let sequenceLength :=
        (← Gen.choose Nat 1 (Nat.max 1 (Nat.min 3 (ws.size - sequenceStart)))
          (Nat.le_max_left ..)).val
      let sequenceStop := sequenceStart + sequenceLength
      let (inlines, ds) ← genInline p params (ws.extract sequenceStart sequenceStop) refs
      out := out ++ textOf (ws.extract 0 sequenceStart) ++ inlines ++
        textOf (ws.extract sequenceStop)
      defs := defs ++ ds
    else
      out := out ++ textOf ws
  return (out, defs)

/--
The profile's directives that may occur at a position. {name}`inDirective` says whether the
position is inside a directive.
-/
public def usableDirectives (p : GenreProfile) (inDirective : Bool) : List DirectiveSpec :=
  p.directives.filter fun d => !inDirective || d.mayNest

/--
Generates a block. {name}`dirDepth` is the number of enclosing directives, {name}`depth` is the
number of enclosing blocks, and {name}`allowed` lists the kinds of surface document blocks allowed
here. With {name}`afterDescriptionList`, the block is not a description list, since two neighboring
description lists are concretized as one.
-/
public partial def genBlock (p : GenreProfile) (params : Params) (dirDepth depth : Nat)
    (allowed : List BlockKind) (refs : Bool := true) (afterDescriptionList : Bool := false) :
    LoremGen Generated := do
  let inDirective := dirDepth > 0
  let mix := if depth == 0 then params.topLevelMix else params.nestedMix
  let feasible (k : BlockKind) : Bool :=
    allowed.contains k &&
    match k with
    | .directive => dirDepth < params.directiveDepth && !(usableDirectives p inDirective).isEmpty
    | .dl => depth < 3 && !afterDescriptionList
    | .ul | .ol | .blockquote => depth < 3
    | .code => !p.codeBlocks.isEmpty
    | .command => !p.commands.isEmpty
    | .linkDef | .footnoteDef => false
    | .para => true
  let kind ←
    if feasible .code && (← chance params.codeBlockChance) then pure BlockKind.code
    else Gen.frequency (pure .para) ((mix.filter (feasible ·.1)).map fun (k, w) => (w, pure k))
  let children (count : Nat) (allowed : List BlockKind) (dirDepth : Nat) :
      LoremGen (Array Block × Array Block) := do
    let mut out := #[]
    let mut defs := #[]
    for _ in [0:count] do
      let afterDl := out.back?.any (· matches .dl ..)
      let g ← genBlock p params dirDepth (depth + 1) allowed refs afterDl
      out := out.push g.block
      defs := defs ++ g.defs
    return (out, defs)
  let allBlocks := BlockKind.exceptDefinitions
  let paragraph : LoremGen Generated := do
    let (content, defs) ← genInlines p params refs
    return { block := .para content, defs }
  match kind with
  | .ul | .ol =>
    let mut items := #[]
    let mut defs := #[]
    for _ in [0:(← Gen.choose Nat 1 3 (by decide)).val] do
      let (cs, ds) ← children (← Gen.choose Nat 1 2 (by decide)).val allBlocks dirDepth
      items := items.push cs
      defs := defs ++ ds
    return { block := if kind == .ul then .ul items else .ol items, defs }
  | .dl =>
    let mut items := #[]
    let mut defs := #[]
    for _ in [0:(← Gen.choose Nat 1 3 (by decide)).val] do
      let term ← Lorem.words (← Gen.choose Nat 1 3 (by decide)).val
      let term := bareWords term
      let term := if term.isEmpty then "lorem" else term
      let (cs, ds) ← children (← Gen.choose Nat 1 2 (by decide)).val allBlocks dirDepth
      items := items.push (#[.text term], cs)
      defs := defs ++ ds
    return { block := .dl items, defs }
  | .blockquote =>
    let (cs, defs) ← children (← Gen.choose Nat 1 2 (by decide)).val allBlocks dirDepth
    return { block := .blockquote cs, defs }
  | .directive =>
    let dirs := usableDirectives p inDirective
    if h : dirs = [] then paragraph else
    let spec ← Gen.elements dirs (List.length_pos_iff.mpr h)
    let args ← spec.args
    let (cs, defs) ← children (← Gen.choose Nat 1 4 (by decide)).val spec.contains (dirDepth + 1)
    return { block := .directive spec.name args cs, defs }
  | .code =>
    if h : p.codeBlocks = [] then paragraph else
    let spec ← Gen.elements p.codeBlocks (List.length_pos_iff.mpr h)
    return { block := .code spec.name (← spec.args) (← spec.content.generate params) }
  | .command =>
    if h : p.commands = [] then paragraph else
    let spec ← Gen.elements p.commands (List.length_pos_iff.mpr h)
    return { block := .command spec.name (← spec.args) }
  | _ => paragraph

public def genMetadata (p : GenreProfile) : LoremGen (Array (String × String)) := do
  let fields := (← Gen.permutationOf p.metadata).val
  let n := (← Gen.choose Nat 1 (Nat.max 1 (Nat.min 2 fields.length)) (Nat.le_max_left ..)).val
  let mut out := #[]
  for f in fields.take n do
    out := out.push (f.name, ← f.value)
  return out
