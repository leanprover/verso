/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json
import Lean.DocString.Extension
import Verso.Doc
import Verso.Doc.Reconstruct
import SubVerso.Highlighting
import SubVerso.Module
import VersoLiterate.Basic


open Verso.Doc
open Lean
open SubVerso.Highlighting
open SubVerso.Module

namespace VersoLiterate


structure LitVersoDocString where
  text : Array (Doc.Block Ext Ext)
  subsections : Array (Doc.Part Ext Ext Empty)
deriving ToJson, FromJson, Repr

open Verso.BEq in
instance : BEq LitVersoDocString where
  beq := ptrEqThen fun
    | ⟨text1, sub1⟩, ⟨text2, sub2⟩ =>
      ptrEqThen' text1 text2 (· == ·) &&
      ptrEqThen' sub1 sub2 (· == ·)

structure LitVersoModuleDocs.Snippet where
  /-- Text to be inserted after the prior snippet's ending text. -/
  text : Array (Doc.Block Ext Ext) := #[]
  /--
  A sequence of parts with their absolute document nesting levels. None of these parts may contain
  sub-parts.
  -/
  sections : Array (Nat × Doc.Part Ext Ext Empty) := #[]
deriving ToJson, FromJson, Repr

open Verso.BEq in
instance : BEq LitVersoModuleDocs.Snippet where
  beq := ptrEqThen fun
    | ⟨text1, sections1⟩, ⟨text2, sections2⟩ =>
      ptrEqThen' text1 text2 (· == ·) &&
      ptrEqThen' sections1 sections2 (· == ·)

instance : ToJson Char where
  toJson c := c.toString

instance : FromJson Char where
  fromJson? v := do
    let v ← v.getStr?
    if h : v.length = 1 then
      return v.startPos.get <| by simp_all; intro hv; subst_eqs
    else throw s!"Expected singleton string for `Char`, but got {v.quote}"

deriving instance ToJson, FromJson for MD4Lean.AttrText, MD4Lean.Text, MD4Lean.Li, MD4Lean.Block, MD4Lean.Document

deriving instance ToJson, FromJson for LitVersoModuleDocs.Snippet

inductive Code where
  | highlighted : Highlighted → Code
  | markdown (indent : Nat) (declName? : Option Name) : MD4Lean.Document → Code
  | verso (indent : Nat) (declName? : Option Name) : LitVersoDocString → Code
  | modDoc : LitVersoModuleDocs.Snippet → Code
  | markdownModDoc : MD4Lean.Document → Code
deriving ToJson, FromJson, Repr

open Verso.BEq in
instance : BEq Code where
  beq := ptrEqThen fun
    | .highlighted hl1, .highlighted hl2 =>
      ptrEqThen' hl1 hl2 (· == ·)
    | .markdown i1 d1? doc1 , .markdown i2 d2? doc2 =>
      i1 == i2 && d1? == d2? &&
      ptrEqThen' doc1 doc2 (· == ·)
    | .verso i1 d1? doc1 , .verso i2 d2? doc2 =>
      i1 == i2 && d1? == d2? &&
      ptrEqThen' doc1 doc2 (· == ·)
    | .modDoc d1, .modDoc d2 => d1 == d2
    | .markdownModDoc d1, .markdownModDoc d2 =>
      ptrEqThen' d1 d2 (· == ·)
    | _, _ => false

structure ModuleItem' where
  range : Option (Lean.Position × Lean.Position)
  kind : SyntaxNodeKind
  defines : Array Name
  code : Array Code
deriving Inhabited, Repr

open Verso.BEq in
instance : BEq ModuleItem' where
  beq := ptrEqThen fun
    | ⟨r1, k1, d1, c1⟩, ⟨r2, k2, d2, c2⟩ =>
      r1 == r2 && k1 == k2 && d1 == d2 && ptrEqThen' c1 c2 (· == ·)

structure LitMod where
  name : Name
  contents : Array ModuleItem'
deriving Inhabited, Repr

open Verso.BEq in
instance : BEq LitMod where
  beq := ptrEqThen fun
    | ⟨name1, contents1⟩, ⟨name2, contents2⟩ =>
      name1 == name2 && contents1 == contents2


section
open SubVerso.Highlighting Export

inductive ExportedCode where
  | highlighted : Key → ExportedCode
  | markdown (indent : Nat) (declName? : Option Name) : MD4Lean.Document → ExportedCode
  | verso (indent : Nat) (declName? : Option Name) : LitVersoDocString → ExportedCode
  | modDoc : LitVersoModuleDocs.Snippet → ExportedCode
  | markdownModDoc : MD4Lean.Document → ExportedCode
deriving ToJson, FromJson

structure ExportedModuleItem where
  range : Option (Lean.Position × Lean.Position)
  kind : SyntaxNodeKind
  defines : Array Name
  code : Array ExportedCode
deriving ToJson, FromJson

def ModuleItem'.export (item : ModuleItem') : ExportM ExportedModuleItem := do
  let code ← item.code.mapM fun
    | .highlighted hl => .highlighted <$> hl.export
    | .markdown i declName? s => pure (.markdown i declName? s)
    | .verso i declName? v => pure (.verso i declName? v)
    | .modDoc doc => pure (.modDoc doc)
    | .markdownModDoc doc => pure (.markdownModDoc doc)
  return {item with code}

def getModuleItem' (e : Export) (item : ExportedModuleItem) : Except String ModuleItem' := do
  let code : Array Code ← item.code.mapM fun
    | .highlighted k => .highlighted <$> e.toHighlighted k
    | .markdown i declName? s => pure (.markdown i declName? s)
    | .verso i declName? v => pure (.verso i declName? v)
    | .modDoc doc => pure (.modDoc doc)
    | .markdownModDoc doc => pure (.markdownModDoc doc)
  return {item with code}

structure ExportedModuleItems extends Export where
  items : Array ExportedModuleItem

instance : ToJson ExportedModuleItems where
  toJson v :=
    let basic := v.toExport.toJson
    basic.setObjVal! "items" (.arr (v.items.map ToJson.toJson))

instance : FromJson ExportedModuleItems where
  fromJson? json := do
    let e : Export ← FromJson.fromJson? json
    let items ← json.getObjVal? "items" >>= (·.getArr?)
    let items ← items.mapM FromJson.fromJson?
    return ⟨e, items⟩

def exportItems (items : Array ModuleItem') : ExportedModuleItems :=
  let (items, st) := items.mapM (ModuleItem'.export) |>.run {}
  {st with items}

def ExportedModuleItems.toModuleItems (e : ExportedModuleItems) : Except String (Array ModuleItem') := do
  let e' := e.toExport
  e.items.mapM (getModuleItem' e')


end

section
variable [LoadLiterate g]

partial def pushBlock (part : Part g) (block : Block g) : Part g :=
  if part.subParts.isEmpty then
    { part with content := part.content.push block }
  else
    { part with subParts := part.subParts.modify (part.subParts.size - 1) (pushBlock · block)}

def pushPart (parent child : Part g) : Part g :=
  { parent with subParts := parent.subParts.push child}

def loadInline : Inline Literate → Inline g :=
  Inline.rewriteOther LoadLiterate.inline

def loadBlock : Block Literate → Block g :=
  Block.rewriteOther LoadLiterate.inline LoadLiterate.block

partial def loadPart (p : Part Literate) : Part g :=
  let title := p.title.map loadInline
  let content := p.content.map loadBlock
  let subParts := p.subParts.map loadPart
  {p with title, metadata := none, content, subParts}

end


section
open Verso.Output.Html

private partial def attrText : MD4Lean.AttrText → String
  | .normal s => s
  | .nullchar => ""
  | .entity e => decodeEntity? e |>.getD e -- leave invalid entities alone

private partial def attr (str : Array MD4Lean.AttrText) : String :=
  str.map attrText |>.toList |> String.join

private partial def mdTextString : MD4Lean.Text → String
  | .normal s => s
  | .nullchar | .img .. | .latexMath .. | .latexMathDisplay .. | .br .. | .softbr .. =>  ""
  | .code s => s.toList |> String.join
  | .a _ _ _ txt | .em txt | .strong txt | .wikiLink _ txt | .u txt | .del txt => txt.map mdTextString |>.toList |> String.join
  | .entity e => decodeEntity? e |>.getD e -- leave invalid entities alone

private partial def mdText : MD4Lean.Text → Except String (Inline g)
  | .normal s => pure <| .text s
  | .nullchar => pure .empty
  | .softbr .. | .br .. => pure .empty
  | .a href _title _ txt => (.link · (attr href)) <$> txt.mapM mdText
  | .img src _title alt => pure <| .image (alt.map mdTextString |>.toList |> String.join) (attr src)
  | .em txt => .emph <$> txt.mapM mdText
  | .strong txt => .bold <$> txt.mapM mdText
  | .entity e => pure <| .text (decodeEntity? e |>.getD e) -- leave invalid entities alone
  | .code s => pure <| .code (s.toList |> String.join)
  | .latexMath s => pure <| .math .inline (s.toList |> String.join)
  | .latexMathDisplay s => pure <| .math .display (s.toList |> String.join)
  | .wikiLink .. => throw "Wiki-style links not supported"
  | .u .. => throw "Underline not supported"
  | .del .. => throw "Strikethrough not supported"
end

private partial def mdBlock : MD4Lean.Block → Except String (Block g)
  | .p xs => .para <$> xs.mapM mdText
  | .ul _ _ items => .ul <$> items.mapM fun ⟨_, _, _, content⟩ => (⟨·⟩) <$> content.mapM mdBlock
  | .ol _ n _ items => .ol n <$> items.mapM fun ⟨_, _, _, content⟩ => (⟨·⟩) <$> content.mapM mdBlock
  | .blockquote bs => .blockquote <$> bs.mapM mdBlock
  | .code _ _ _ s => pure <| .code <| String.join s.toList
  | .header .. => throw "Headers may not be nested under other blocks"
  | .table .. => throw "Markdown tables not supported"
  | .html .. => throw "Literal HTML in Markdown not supported"
  | .hr => throw "Thematic break (horizontal rule) in Markdown not supported"

partial def modToPage [LoadLiterate g] (mod : LitMod) (title : Array (Inline g)) (titleString : String) : Except String (DocThunk g) := do
  let mut stack : Array (Part g) := #[]
  let mut p : Part g := {title, titleString, metadata := none, content := #[], subParts := #[]}

  let mut mdLevels := #[] -- Header nesting for legacy Markdown moduledocs

  for item in mod.contents do
    for c in item.code do
      match c with
      | .highlighted hl =>
        p := pushBlock p <| loadBlock (.other (.highlighted hl) #[])
      | .markdownModDoc doc =>
        for b in doc.blocks do
          match b with
          | .header lvl title =>
            let mdLevel := mdLevels.back? |>.getD 0
              let titleString := String.join <| Array.toList <| title.map mdTextString
              let title ← title.mapM mdText
              let newPart := {title, titleString, metadata := none, content := #[], subParts := #[]}

            if lvl > mdLevel then
              stack := stack.push p
              mdLevels := mdLevels.push lvl
              p := newPart
            else
              while h : stack.size > 0 ∧ mdLevels.size > 0 ∧ lvl < mdLevels.back?.getD 0 do
                let p' := stack.back
                stack := stack.pop
                mdLevels := mdLevels.pop
                p := pushPart p' p
              p := pushPart p newPart
          | other =>
            match mdBlock other with
            | .error e => throw e
            | .ok b' => p := pushBlock p b'
      | .modDoc doc =>
        for b in doc.text do
          p := pushBlock p (loadBlock b)
        for (lvl, sec) in doc.sections do
          if lvl > stack.size then
            stack := stack.push p
            p := loadPart sec
          else
            while h : lvl < stack.size do
              let p' := stack.back
              stack := stack.pop
              p := pushPart p' p
            stack := stack.push p
            p := loadPart sec
      | .verso i declName? docstring =>
        p := pushBlock p <| LoadLiterate.docstring i declName? <| docstringBlock docstring
      | .markdown i declName? docstring =>
        p := pushBlock p <| LoadLiterate.docstring i declName? <| ← mdDocstringBlock docstring.blocks

  while h : stack.size > 0 do
    let p' := stack.back
    stack := stack.pop
    p := pushPart p' p
  return DocThunk.value p
where
  docstringBlock (doc : LitVersoDocString) : Array (Block g) :=
    let parts := doc.subsections.map loadPart
    doc.text.map loadBlock ++ parts.map (LoadLiterate.part 0)

  mdDocstringBlock (blocks : Array MD4Lean.Block) : Except String (Array (Block g)) := do
    let mut stack : Array (Nat × Array (Inline g) × Array (Block g)) := #[]
    let mut current := #[]
    for b in blocks do
      if let .header lvl title := b then
        let title ← title.mapM mdText
        let outerLvl := stack.back?.map (·.1) |>.getD 0
        while h : stack.size > 0 ∧ lvl ≤ (stack.back?.map (·.1) |>.getD 0) do
          let (lvl', title', current') := stack.back
          stack := stack.pop
          current := current'.push <| LoadLiterate.docstringPart stack.size title' current
        stack := stack.push (lvl, title, current)
        current := #[]
      else
        current := current.push (← mdBlock b)
    while h : stack.size > 0 do
      let (lvl', title', current') := stack.back
      stack := stack.pop
      current := current'.push <| LoadLiterate.docstringPart stack.size title' current
    return current
