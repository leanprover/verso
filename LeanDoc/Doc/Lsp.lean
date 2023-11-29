/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean
import Lean.Data.Lsp
import Std.CodeAction.Basic

import LeanDoc.Doc.Elab
import LeanDoc.Syntax

open LeanDoc.Doc.Elab (DocListInfo TOC)

open Lean

open Lean Server in
def withFallbackResponse (resp : RequestTask α) (act : RequestM (RequestTask α)) : RequestM (RequestTask α) :=
  try
    act
  catch e =>
    (← read).hLog.putStrLn s!"Doc LSP request failed: {e.message}"
    return resp

defmethod Syntax.containsPos (s : Syntax) (p : String.Pos) : Bool :=
  match s.getHeadInfo with
  | .original (pos := start) (endPos := stop) .. => p >= start && p < stop
  | .synthetic (pos := start) (endPos := stop) .. => p >= start && p < stop
  | _ => false

defmethod Syntax.lspRange (text : FileMap) (s : Syntax) : Option Lsp.Range :=
  match s.getHeadInfo with
  | .original (pos := start) (endPos := stop) .. => some ⟨text.utf8PosToLspPos start, text.utf8PosToLspPos stop⟩
  | .synthetic (pos := start) (endPos := stop) .. => some ⟨text.utf8PosToLspPos start, text.utf8PosToLspPos stop⟩
  | _ => none




open Lean.Lsp in
instance : FromJson DocumentHighlightKind where
  fromJson?
    | 1 => pure DocumentHighlightKind.text
    | 2 => pure DocumentHighlightKind.read
    | 3 => pure DocumentHighlightKind.write
    | n => throw s!"Expected 1, 2, or 3, got {n}"


deriving instance FromJson for Lean.Lsp.DocumentHighlight

instance : FromJson Lean.Lsp.SymbolKind where
  fromJson? v := open Lean.Lsp in do
    let .num i := v | throw "expected number"
    match i with
    | 1 => pure SymbolKind.file
    | 2 => pure SymbolKind.module
    | 3 => pure SymbolKind.namespace
    | 4 => pure SymbolKind.package
    | 5 => pure SymbolKind.class
    | 6 => pure SymbolKind.method
    | 7 => pure SymbolKind.property
    | 8 => pure SymbolKind.field
    | 9 => pure SymbolKind.constructor
    | 10 => pure SymbolKind.enum
    | 11 => pure SymbolKind.interface
    | 12 => pure SymbolKind.function
    | 13 => pure SymbolKind.variable
    | 14 => pure SymbolKind.constant
    | 15 => pure SymbolKind.string
    | 16 => pure SymbolKind.number
    | 17 => pure SymbolKind.boolean
    | 18 => pure SymbolKind.array
    | 19 => pure SymbolKind.object
    | 20 => pure SymbolKind.key
    | 21 => pure SymbolKind.null
    | 22 => pure SymbolKind.enumMember
    | 23 => pure SymbolKind.struct
    | 24 => pure SymbolKind.event
    | 25 => pure SymbolKind.operator
    | 26 => pure SymbolKind.typeParameter
    | _ => throw s!"didn't understand {i}"

deriving instance FromJson for Lean.Lsp.DocumentSymbolAux
open Lean Lsp in
partial def symFromJson? (j : Json) : Except String DocumentSymbol := do
  let fromJ : {α : _} → [inst : FromJson α] → FromJson (Lean.Lsp.DocumentSymbolAux α) := inferInstance
  DocumentSymbol.mk <$> @FromJson.fromJson? _ (fromJ (inst:=⟨symFromJson?⟩)) j

instance : FromJson Lean.Lsp.DocumentSymbol where
  fromJson? := symFromJson?

partial instance : FromJson Lean.Lsp.DocumentSymbolResult where
  fromJson? j := do
    let .arr elts := j
      | throw "expected array"
    let syms ← elts.mapM fromJson?
    pure ⟨syms⟩

open Lean Server Lsp RequestM in
def handleHl (params : DocumentHighlightParams) (prev : RequestTask DocumentHighlightResult) : RequestM (RequestTask DocumentHighlightResult) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos params.position
  bindWaitFindSnap doc (·.endPos + ' ' >= pos) (notFoundX := pure prev) fun snap => do
    withFallbackResponse prev <| pure <| Task.spawn <| fun () => do
      let nodes := snap.infoTree.deepestNodes fun _ctxt info _arr =>
        match info with
        | .ofCustomInfo ⟨stx, data⟩ =>
          if stx.containsPos pos then
            data.get? DocListInfo
          else none
        | _ => none
      if nodes.isEmpty then prev.get
      else
        let mut hls := #[]
        for node in nodes do
          let ⟨stxs⟩ := node
          for s in stxs do
            if let some r := s.lspRange text then
              hls := hls.push ⟨r, none⟩
        pure hls

open Lean Lsp

def rangeContains (outer inner : Lsp.Range) :=
  outer.start < inner.start && inner.«end» ≤ outer.«end» ||
  outer.start == inner.start && inner.«end» < outer.«end»

mutual
  partial def graftSymbolOnto (inner outer : DocumentSymbol) : Option DocumentSymbol :=
    match outer, inner with
    | .mk s1, .mk s2 =>
      if rangeContains s1.range s2.range then
        -- add as child
        some <| .mk {s1 with children? := some (graftSymbolInto inner (s1.children?.getD #[])) }
      else
        -- signal peer
        none

  partial def graftSymbolInto (inner : DocumentSymbol) (outer : Array DocumentSymbol) : Array DocumentSymbol := Id.run do
    let mut i := 0
    while h : i < outer.size do
      let sym := outer[i]
      if let some sym' := graftSymbolOnto inner sym then
        return outer.set ⟨i, h⟩ sym'
      i := i + 1
    return outer.push inner
end

def graftSymbols (inner outer : Array DocumentSymbol) : Array DocumentSymbol :=
  inner.foldr graftSymbolInto outer

open Lean Server Lsp RequestM in
def mergeResponses (docTask : RequestTask α) (leanTask : RequestTask β) (f : Option α → Option β → γ) : RequestM (RequestTask γ) := do
  bindTask docTask fun
  | .ok docResult =>
    bindTask leanTask fun
    | .ok leanResult =>
      pure <| Task.pure <| pure <| f (some docResult) (some leanResult)
    | .error _ => pure <| Task.pure <| pure <| f (some docResult) none
  | .error _ =>
    bindTask leanTask fun
    | .ok leanResult => pure <| Task.pure <| pure <| f none (some leanResult)
    | .error e => throw e

open Lean Server Lsp RequestM in
partial def handleSyms (_params : DocumentSymbolParams) (prev : RequestTask DocumentSymbolResult) : RequestM (RequestTask DocumentSymbolResult) := do
  let doc ← readDoc
  let text := doc.meta.text
  -- bad: we have to wait on elaboration of the entire file before we can report document symbols
  let t := doc.cmdSnaps.waitAll
  let syms ← mapTask t fun (snaps, _) => do
      return { syms := getSections text snaps : DocumentSymbolResult }
  mergeResponses syms prev combineAnswers
  --pure syms
  where
    combineAnswers (x y : Option DocumentSymbolResult) : DocumentSymbolResult := ⟨graftSymbols (x.getD ⟨{}⟩).syms (y.getD ⟨{}⟩).syms⟩
    tocSym (text : FileMap) : TOC → Option DocumentSymbol
      | .mk title titleStx endPos children => Id.run do
        let some selRange@⟨start, _⟩ := titleStx.lspRange text
          | return none
        let mut kids := #[]
        for c in children do
          if let some s := tocSym text c then kids := kids.push s
        return some <| DocumentSymbol.mk {
          name := title,
          kind := SymbolKind.string,
          range := ⟨start, text.utf8PosToLspPos endPos⟩,
          selectionRange := selRange,
          children? := kids
        }
    getSections text ss : Array DocumentSymbol := Id.run do
      let mut syms := #[]
      for snap in ss do
        let info := snap.infoTree.deepestNodes fun _ctxt info _arr =>
          match info with
          | .ofCustomInfo ⟨_stx, data⟩ =>
            data.get? TOC
          | _ => none
        for i in info do
          if let some x := tocSym text i then syms := syms.push x
      pure syms

-- Shamelessly cribbed from https://github.com/tydeu/lean4-alloy/blob/57792f4e8a9674f8b4b8b17742607a1db142d60e/Alloy/C/Server/SemanticTokens.lean
structure SemanticTokenEntry where
  line : Nat
  startChar : Nat
  length : Nat
  type : Nat
  modifierMask : Nat
deriving Inhabited, Repr

protected def SemanticTokenEntry.ordLt (a b : SemanticTokenEntry) : Bool :=
  a.line < b.line ∨ (a.line = b.line ∧ a.startChar < b.startChar)

def encodeTokenEntries (entries : Array SemanticTokenEntry) : Array Nat := Id.run do
  let mut data := #[]
  let mut lastLine := 0
  let mut lastChar := 0
  for ⟨line, char, len, type, modMask⟩ in entries do
    let deltaLine := line - lastLine
    let deltaStart := if line = lastLine then char - lastChar else char
    data := data ++ #[deltaLine, deltaStart, len, type, modMask]
    lastLine := line; lastChar := char
  return data

def decodeLeanTokens (data : Array Nat) : Array SemanticTokenEntry := Id.run do
  let mut line := 0
  let mut char := 0
  let mut entries : Array SemanticTokenEntry := #[]
  for i in [0:data.size:5] do
    let #[deltaLine, deltaStart, len, type, modMask] := data[i:i+5].toArray
      | return entries -- If this happens, something is wrong with Lean, but we don't really care
    line := line + deltaLine
    char := if deltaLine = 0 then char + deltaStart else deltaStart
    entries := entries.push ⟨line, char, len, type, modMask⟩
  return entries

deriving instance Repr, BEq for SemanticTokenType

open Lean Server Lsp RequestM in
partial def handleTokens (prev : RequestTask SemanticTokens) (beginPos endPos : String.Pos) : RequestM (RequestTask SemanticTokens) := do
  let doc ← readDoc
  let text := doc.meta.text
  let t := doc.cmdSnaps.waitUntil (·.endPos >= endPos)
  let toks ←
    mapTask t fun (snaps, _) => do
      let mut toks := #[]
      for s in snaps do
        if s.endPos <= beginPos then continue
        toks := toks ++ go s text s.stx
      pure toks

  mergeResponses toks prev fun
    | none, none => SemanticTokens.mk none #[]
    | some xs, none => SemanticTokens.mk none <| encodeTokenEntries <| xs.qsort (·.ordLt ·)
    | none, some r => r
    | some mine, some leans =>
      let toks := decodeLeanTokens leans.data
      {leans with data := encodeTokenEntries (toks ++ mine |>.qsort (·.ordLt ·))}

where
  mkTok (text : FileMap) (type : SemanticTokenType) (stx : Syntax) : Array SemanticTokenEntry := Id.run do
    let (some startPos, some endPos) := (stx.getPos?, stx.getTailPos?)
      | return #[]
    let startLspPos := text.utf8PosToLspPos startPos
    let endLspPos := text.utf8PosToLspPos endPos
    -- VS Code has a limitation where tokens can't span lines The
    -- parser obeys an invariant that nothing spans a line, so we can
    -- bail, rather than resorting to workarounds.
    if startLspPos.line == endLspPos.line then #[{
        line := startLspPos.line,
        startChar := startLspPos.character,
        length := endLspPos.character - startLspPos.character,
        type := type.toNat,
        modifierMask := 0
      }]
    else #[]

  go (snap : Snapshots.Snapshot) (text : FileMap) (stx : Syntax) : Array SemanticTokenEntry := Id.run do
    match stx.getKind with
    | ``LeanDoc.Syntax.text =>
      mkTok text .string stx
    | ``LeanDoc.Syntax.emph | ``LeanDoc.Syntax.bold =>
      mkTok text .keyword stx[0] ++ go snap text stx[1] ++ mkTok text .keyword stx[2]
    | ``LeanDoc.Syntax.header =>
      mkTok text .keyword stx[0] ++ go snap text stx[1]
    | ``LeanDoc.Syntax.link =>
      mkTok text .keyword stx[0] ++ go snap text stx[1] ++ mkTok text .keyword stx[2] ++
      mkTok text .keyword stx[3][0] ++ mkTok text .keyword stx[3][2]
    | ``LeanDoc.Syntax.role =>
      mkTok text .keyword stx[0] ++ -- {
      mkTok text .function stx[1] ++ -- roleName
      go snap text stx[2] ++  -- args
      mkTok text .keyword stx[3] ++ -- }
      mkTok text .keyword stx[4] ++ -- [
      go snap text stx[5] ++
      mkTok text .keyword stx[6] -- ]
    | ``LeanDoc.Syntax.named =>
      mkTok text .keyword stx[1] -- :=
    | ``LeanDoc.Syntax.li =>
      mkTok text .keyword stx[0][1] ++
      go snap text stx[1]
    | ``LeanDoc.Syntax.desc =>
      mkTok text .keyword stx[0] ++ go snap text stx[1] ++
      mkTok text .keyword stx[2] ++ go snap text stx[3]
    | _ =>
      let mut out := #[]
      for arg in stx.getArgs do
        out := out ++ go snap text arg
      return out

open Lean Server Lsp RequestM in
def handleTokensRange (params : SemanticTokensRangeParams) (prev : RequestTask SemanticTokens) : RequestM (RequestTask SemanticTokens) := do
  let doc ← readDoc
  let text := doc.meta.text
  let beginPos := text.lspPosToUtf8Pos params.range.start
  let endPos := text.lspPosToUtf8Pos params.range.end
  handleTokens prev beginPos endPos

open Lean Server Lsp RequestM in
def handleTokensFull (_params : SemanticTokensParams) (prev : RequestTask SemanticTokens) : RequestM (RequestTask SemanticTokens) := handleTokens prev 0 ⟨1 <<< 31⟩


open Lean Server Lsp in
initialize
  chainLspRequestHandler "textDocument/documentHighlight" DocumentHighlightParams DocumentHighlightResult handleHl
  chainLspRequestHandler "textDocument/documentSymbol" DocumentSymbolParams DocumentSymbolResult handleSyms
  chainLspRequestHandler "textDocument/semanticTokens/full" SemanticTokensParams SemanticTokens handleTokensFull
  chainLspRequestHandler "textDocument/semanticTokens/range" SemanticTokensRangeParams SemanticTokens handleTokensRange
