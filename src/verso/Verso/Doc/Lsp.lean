/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean
import Lean.Data.Lsp
import Std.CodeAction.Basic

import Verso.Doc.Elab
import Verso.Syntax

open Verso.Doc.Elab (DocListInfo DocRefInfo TOC)

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
def handleDef (params : TextDocumentPositionParams) (prev : RequestTask (Array LocationLink)) : RequestM (RequestTask (Array LocationLink)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos params.position
  bindWaitFindSnap doc (·.endPos + ' ' >= pos) (notFoundX := pure prev) fun snap => do
    withFallbackResponse prev <| pure <| Task.spawn <| fun () => do
      let nodes := snap.infoTree.deepestNodes fun _ctxt info _arr =>
        match info with
        | .ofCustomInfo ⟨stx, data⟩ =>
          if stx.containsPos pos then
            data.get? DocRefInfo
          else none
        | _ => none
      let mut locs := #[]
      for node in nodes do
        match node with
        | ⟨some defSite, _⟩ =>
          let mut origin : Option Range := none
          for stx in node.syntax do
            if let some ⟨head, tail⟩ := stx.getRange? then
              if pos ≥ head && pos ≤ tail then
                origin := stx.lspRange text
                break
          let some target := defSite.lspRange text
            | continue
          locs := locs.push {originSelectionRange? := origin, targetRange := target, targetUri := params.textDocument.uri, targetSelectionRange := target}
        | _ => continue
      pure (locs ++ (← prev.get))

open Lean Server Lsp RequestM in
def handleRefs (params : ReferenceParams) (prev : RequestTask (Array Location)) : RequestM (RequestTask (Array Location)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos params.position
  bindWaitFindSnap doc (·.endPos + ' ' >= pos) (notFoundX := pure prev) fun snap => do
    withFallbackResponse prev <| pure <| Task.spawn <| fun () => do
      let nodes := snap.infoTree.deepestNodes fun _ctxt info _arr =>
        match info with
        | .ofCustomInfo ⟨stx, data⟩ =>
          if stx.containsPos pos then
            data.get? DocRefInfo
          else none
        | _ => none
      if nodes.isEmpty then prev.get
      else
        let mut locs := #[]
        for node in nodes do
          for stx in node.syntax do
            if let some range := stx.lspRange text then
              locs := locs.push {uri := params.textDocument.uri, range := range}
        pure locs

open Lean Server Lsp RequestM in
def handleHl (params : DocumentHighlightParams) (prev : RequestTask DocumentHighlightResult) : RequestM (RequestTask DocumentHighlightResult) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos params.position
  bindWaitFindSnap doc (·.endPos + ' ' >= pos) (notFoundX := pure prev) fun snap => do
    withFallbackResponse prev <| pure <| Task.spawn <| fun () => do
      let nodes : List (_ ⊕ _) := snap.infoTree.deepestNodes fun _ctxt info _arr =>
        match info with
        | .ofCustomInfo ⟨stx, data⟩ =>
          if stx.containsPos pos then
            (.inl <$> data.get? DocListInfo) <|> (.inr <$> data.get? DocRefInfo)
          else none
        | _ => none
      if nodes.isEmpty then prev.get
      else
        let mut hls := #[]
        for node in nodes do
          match node with
          | .inl ⟨bulletStxs, _⟩ =>
            for s in bulletStxs do
              if let some r := s.lspRange text then
                hls := hls.push ⟨r, none⟩
          | .inr ⟨defSite, useSites⟩ =>
            if let some s := defSite then
              if let some r := s.lspRange text then
                hls := hls.push ⟨r, none⟩
            for s in useSites do
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
    tocSym (text : FileMap) : TOC → Id (Option DocumentSymbol)
      | .mk title titleStx endPos children => do
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
      | .included name => do
        -- TODO Evaluate the name to find the actual included title
        let some rng := name.raw.lspRange text
          | return none
        return some <| DocumentSymbol.mk {
          name := toString name,
          kind := SymbolKind.property,
          range := rng
          selectionRange := rng
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
          if let some x ← tocSym text i then syms := syms.push x
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
    | ``Verso.Syntax.text =>
      mkTok text .string stx
    | ``Verso.Syntax.emph | ``Verso.Syntax.bold =>
      mkTok text .keyword stx[0] ++ go snap text stx[1] ++ mkTok text .keyword stx[2]
    | ``Verso.Syntax.header =>
      mkTok text .keyword stx[0] ++ go snap text stx[1]
    | ``Verso.Syntax.link =>
      mkTok text .keyword stx[0] ++ go snap text stx[1] ++ mkTok text .keyword stx[2] ++
      mkTok text .keyword stx[3][0] ++ mkTok text .keyword stx[3][2]
    | ``Verso.Syntax.role =>
      mkTok text .keyword stx[0] ++ -- {
      mkTok text .function stx[1] ++ -- roleName
      go snap text stx[2] ++  -- args
      mkTok text .keyword stx[3] ++ -- }
      mkTok text .keyword stx[4] ++ -- [
      go snap text stx[5] ++
      mkTok text .keyword stx[6] -- ]
    | ``Verso.Syntax.named =>
      mkTok text .keyword stx[1] -- :=
    | ``Verso.Syntax.li =>
      mkTok text .keyword stx[0][1] ++
      go snap text stx[1]
    | ``Verso.Syntax.desc =>
      mkTok text .keyword stx[0] ++ go snap text stx[1] ++
      mkTok text .keyword stx[2] ++ go snap text stx[3]
    | ``Verso.Syntax.directive =>
      mkTok text .keyword stx[0] ++ -- :::
      mkTok text .function stx[1] ++ -- name
      go snap text stx[2] ++  -- args
      mkTok text .keyword stx[4] ++ -- only in meta code
      mkTok text .keyword stx[4] ++ -- only in meta code
      go snap text stx[5] ++
      mkTok text .keyword stx[6] -- :::
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

open Lean Server Lsp RequestM in
@[code_action_provider]
def renumberLists : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let startPos := text.lspPosToUtf8Pos params.range.start
  let endPos := text.lspPosToUtf8Pos params.range.end
  let lists := snap.infoTree.foldInfo (init := #[]) fun ctx info result => Id.run do
    let .ofCustomInfo ⟨stx, data⟩ := info | result
    let some listInfo := data.get? DocListInfo | result
    let (some head, some tail) := (stx.getPos? true, stx.getTailPos? true) | result
    unless head ≤ endPos && startPos ≤ tail do return result
    result.push (ctx, listInfo)
  pure <| lists.map fun (_, ⟨bulletStxs, _⟩) => {
      eager := {
        title := "Number from 1",
        kind? := some "quickfix",
        edit? := some <| .ofTextDocumentEdit {
          textDocument := doc.versionedIdentifier,
          edits := Id.run do
            let mut counter := 1
            let mut edits := #[]
            for stx in bulletStxs do
              let some r := stx.lspRange text | continue
              edits := edits.push {range := r, newText := s!"{counter}."}
              counter := counter + 1
            edits
        }
      }
    }

deriving instance FromJson for FoldingRangeKind
deriving instance FromJson for FoldingRange

open Lean Server Lsp RequestM in
def handleFolding (_params : FoldingRangeParams) (prev : RequestTask (Array FoldingRange)) : RequestM (RequestTask (Array FoldingRange)) := do
  let doc ← readDoc
  let text := doc.meta.text
  -- bad: we have to wait on elaboration of the entire file before we can report document symbols
  let t := doc.cmdSnaps.waitAll
  let folds ← mapTask t fun (snaps, _) => pure <| getSections text snaps ++ getLists text snaps
  combine folds prev
where
    combine := (mergeResponses · · (·.getD #[] ++ ·.getD #[]))
    getLists text ss : Array FoldingRange := Id.run do
      let mut lists := #[]
      for snap in ss do
        let snapLists := snap.infoTree.foldInfo (init := #[]) fun _ctx info result => Id.run do
          let .ofCustomInfo ⟨_stx, data⟩ := info | result
          let some listInfo := data.get? DocListInfo | result
          if h : listInfo.items.size > 0 then
            let some {start := {line := startLine, ..}, ..} := text.rangeOfStx? listInfo.items[0]
              | result
            let some {«end» := {line := endLine, ..}, ..} := text.rangeOfStx? listInfo.items.back
              | result
            result.push {startLine := startLine, endLine := endLine}
          else result
        lists := lists ++ snapLists
      pure lists
    getSections text ss : Array FoldingRange := Id.run do
      let mut regions := #[]
      for snap in ss do
        let mut info := snap.infoTree.deepestNodes fun _ctxt info _arr =>
          match info with
          | .ofCustomInfo ⟨_stx, data⟩ =>
            data.get? TOC
          | _ => none
        repeat
          match info with
          | .included _  :: more =>
            info := more
          | (.mk _ titleStx endPos children) :: more =>
            if let some {start := {line := startLine, ..}, ..} := text.rangeOfStx? titleStx then
              let {line := endLine, ..} := text.utf8PosToLspPos endPos
              if endLine - 1 > startLine then
                regions := regions.push {startLine := startLine, endLine := endLine - 1}
            info := children.toList ++ more
          | [] => break
      pure regions


open Lean Server Lsp in
initialize
  chainLspRequestHandler "textDocument/definition" TextDocumentPositionParams (Array LocationLink) handleDef
  -- chainLspRequestHandler "textDocument/references" ReferenceParams (Array Location) handleRefs -- TODO make this work - right now it goes through the watchdog so we can't chain it
  chainLspRequestHandler "textDocument/documentHighlight" DocumentHighlightParams DocumentHighlightResult handleHl
  chainLspRequestHandler "textDocument/documentSymbol" DocumentSymbolParams DocumentSymbolResult handleSyms
  chainLspRequestHandler "textDocument/semanticTokens/full" SemanticTokensParams SemanticTokens handleTokensFull
  chainLspRequestHandler "textDocument/semanticTokens/range" SemanticTokensRangeParams SemanticTokens handleTokensRange
  chainLspRequestHandler "textDocument/foldingRange" FoldingRangeParams (Array FoldingRange) handleFolding
