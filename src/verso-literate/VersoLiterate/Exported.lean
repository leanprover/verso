/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json
import Lean.DocString.Extension
import Verso.Doc
import SubVerso.Highlighting
import SubVerso.Module
import VersoLiterate.Basic

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
    if v.length = 1 then
      return v.get 0
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
deriving Inhabited

open Verso.BEq in
instance : BEq ModuleItem' where
  beq := ptrEqThen fun
    | ⟨r1, k1, d1, c1⟩, ⟨r2, k2, d2, c2⟩ =>
      r1 == r2 && k1 == k2 && d1 == d2 && ptrEqThen' c1 c2 (· == ·)

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
