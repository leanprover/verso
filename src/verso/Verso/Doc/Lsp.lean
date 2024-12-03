/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Lsp
import Lean.Server

import Verso.Doc.Elab
import Verso.Syntax
import Verso.Hover

namespace Verso.Lsp

open Verso.Doc.Elab (DocListInfo DocRefInfo TOC)
open Verso.Hover

open Lean

open Lean Server in
def withFallbackResponse (resp : RequestTask α) (act : RequestM (RequestTask α)) : RequestM (RequestTask α) :=
  try
    act
  catch e =>
    (← read).hLog.putStrLn s!"Doc LSP request failed: {e.message}"
    return resp

defmethod Syntax.containsPos (s : Syntax) (p : String.Pos) : Bool :=
  match span s.getHeadInfo, span s.getTailInfo with
  | some (start, _), some (_, stop) => p >= start && p < stop
  | _, _ => false
where
  span : SourceInfo → Option (String.Pos × String.Pos)
    | .original (pos := start) (endPos := stop) .. => some (start, stop)
    | .synthetic (pos := start) (endPos := stop) .. => some (start, stop)
    | _ => none


defmethod Syntax.lspRange (text : FileMap) (s : Syntax) : Option Lsp.Range :=
  match span s.getHeadInfo, span s.getTailInfo with
  | some (start, _), some (_, stop) => some ⟨text.utf8PosToLspPos start, text.utf8PosToLspPos stop⟩
  | _, _ => none
where
  span : SourceInfo → Option (String.Pos × String.Pos)
    | .original (pos := start) (endPos := stop) .. => some (start, stop)
    | .synthetic (pos := start) (endPos := stop) .. => some (start, stop)
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
set_option linter.unusedVariables false in -- it doesn't like the `inst` name here
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
partial def handleHl (params : DocumentHighlightParams) (prev : RequestTask DocumentHighlightResult) : RequestM (RequestTask DocumentHighlightResult) := do
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
      if nodes.isEmpty then
        if let some hls := syntactic text pos snap.stx then
          let hls := hls.filterMap (·.lspRange text) |>.map (⟨·, none⟩)
          if hls.isEmpty then prev.get
          else pure hls
        else
          prev.get
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
where
  -- Unfortunately, VS Code doesn't do the right thing, so many of these highlights don't work there:
  --   https://github.com/microsoft/vscode/issues/127007
  -- Tested in Emacs and the problem isn't server side.
  syntactic (text : FileMap) (pos : String.Pos) (stx : Syntax) : Option (Array Syntax) := do
    if includes stx pos |>.getD true then
      match stx with
        | `<low|(Verso.Syntax.directive  ~opener ~_name ~_args ~_fake ~_fake' ~_contents ~closer )>
        | `<low|(Verso.Syntax.codeblock ~_ ~opener ~_ ~_ ~closer )> =>
          if (includes opener pos).getD false || (includes closer pos).getD false then
            return #[opener, closer]
        | _ =>
          match stx with
          | `(inline| ${%$opener1 code{%$opener2 $_ }%$closer1 }%$closer2)
          | `(inline| $${%$opener1 code{%$opener2 $_ }%$closer1 }%$closer2)
          | `(inline| link[%$opener1 $_* ]%$closer1 (%$opener2 $_ )%$closer2)
          | `(inline| link[%$opener1 $_* ]%$closer1 [%$opener2 $_ ]%$closer2) =>
            if (includes opener1 pos).getD false || (includes closer1 pos).getD false || (includes opener2 pos).getD false || (includes closer2 pos).getD false then
              return #[opener1, closer1, opener2, closer2]
          |  `(inline| code{%$opener $_ }%$closer) =>
            if (includes opener pos).getD false || (includes closer pos).getD false then
              return #[opener, closer]
          | `(inline| role{%$opener1 $name $_* }%$closer1 [%$opener2 $subjects ]%$closer2) =>
            if (includes opener1 pos).getD false || (includes closer1 pos).getD false ||
               (includes opener2 pos).getD false || (includes closer2 pos).getD false ||
               (includes name pos).getD false then
              return #[opener1, closer1, opener2, closer2, subjects.raw]
          | _ => pure ()
      if let .node _ _ contents := stx then
        for s in contents do
          if let some r := syntactic text pos s then return r
    failure

  includes (stx : Syntax) (pos : String.Pos) : Option Bool :=
    stx.getRange?.map (fun r => pos ≥ r.start && pos < r.stop)

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
        return outer.set i sym'
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
  mkTok (text : FileMap) (tokenType : SemanticTokenType) (stx : Syntax) : Array SemanticTokenEntry := Id.run do
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
        type := tokenType.toNat,
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

partial def directiveResizings (startPos endPos : String.Pos) (text : FileMap) (parents : Array (Syntax × Syntax)) (subject : Syntax) : StateM (Array (Bool × Syntax × Syntax × TextEditBatch)) Unit := do
  match subject with
  | `<low|(Verso.Syntax.directive  ~opener ~_name ~_args ~_fake ~_fake' ~(.node _ `null contents) ~closer )> =>
    let parents := parents.push (opener, closer)
    if inRange opener || inRange closer then
      if let some edit := parents.flatMapM getIncreases then
        modify (·.push (true, opener, closer, edit))
      if let some edit := getDecreases (opener, closer) contents then
        modify (·.push (false, opener, closer, edit))
    else
      for s in contents do directiveResizings startPos endPos text parents s
  | stx@(.node _ _ contents) =>
    if inRange stx then
      for s in contents do
        directiveResizings startPos endPos text parents s
  | _ => pure ()
where
  inRange (stx : Syntax) : Bool :=
    if let some ⟨stxStart, stxEnd⟩ := stx.getRange? then
      -- if the syntax starts before the selection, then it should end after the selection begins
      if stxStart ≤ startPos then stxEnd ≥ startPos
      -- otherwise there's only an overlap if it starts within the selection
      else stxStart ≤ endPos
    else false

  getIncreases (stxs : Syntax × Syntax) : Option TextEditBatch := do
    return #[← getIncrease stxs.1, ← getIncrease stxs.2]
  getIncrease : Syntax → Option TextEdit
  | stx@(.atom _ colons) =>
    if let some r := stx.lspRange text then
      some {range := r, newText := colons.push ':'}
    else none
  | _ => none

  getDecreases (stxs : Syntax × Syntax) (children : Array Syntax) : Option TextEditBatch := do
    let outer := #[← getDecrease stxs.1, ← getDecrease stxs.2]
    let inner ← children.flatMapM getDecreasesIn
    pure (outer ++ inner)

  getDecreasesIn : Syntax → Option TextEditBatch
    | `<low|(Verso.Syntax.directive  ~opener ~_name ~_args ~_fake ~_fake' ~(.node _ `null contents) ~closer )> => do
      getDecreases (opener, closer) contents
    | .node _ _ children => children.flatMapM getDecreasesIn
    | _ => pure #[]

  getDecrease : Syntax → Option TextEdit
  | stx@(.atom _ colons) => do
    if let some r := stx.lspRange text then
      if colons.length > 3 then
        return {range := r, newText := colons.drop 1}
    failure
  | _ => none


open Lean Server Lsp RequestM in
@[code_action_provider]
def resizeDirectives : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let startPos := text.lspPosToUtf8Pos params.range.start
  let endPos := text.lspPosToUtf8Pos params.range.end
  let ((), directives) := directiveResizings startPos endPos text #[] snap.stx |>.run #[]
  pure <| directives.map fun (which, _, _, edits) => {
    eager := {
      title := (if which then "More" else "Less") ++ " Colons",
      kind? := some "refactor.rewrite",
      isPreferred? := some true,
      edit? :=
        some <| .ofTextDocumentEdit {
          textDocument := doc.versionedIdentifier,
          edits := edits
        }
    }
  }


deriving instance FromJson for FoldingRangeKind
deriving instance FromJson for FoldingRange

private def rangeOfStx? (text : FileMap) (stx : Syntax) :=
  Lean.FileMap.utf8RangeToLspRange text <$> Lean.Syntax.getRange? stx

open Lean Server Lsp RequestM in
partial def handleFolding (_params : FoldingRangeParams) (prev : RequestTask (Array FoldingRange)) : RequestM (RequestTask (Array FoldingRange)) := do
  let doc ← readDoc
  let text := doc.meta.text
  -- bad: we have to wait on elaboration of the entire file before we can report folding
  let t := doc.cmdSnaps.waitAll
  let folds ← mapTask t fun (snaps, _) => pure <| getSections text snaps ++ getSyntactic text snaps
  combine folds prev
where
    combine := (mergeResponses · · (·.getD #[] ++ ·.getD #[]))
    getLists (text : FileMap) (ss : List Snapshots.Snapshot) : Array FoldingRange := Id.run do
      let mut lists := #[]
      for snap in ss do
        let snapLists := snap.infoTree.foldInfo (init := #[]) fun _ctx info result => Id.run do
          let .ofCustomInfo ⟨_stx, data⟩ := info | result
          let some listInfo := data.get? DocListInfo | result
          if h : listInfo.items.size > 0 then
            let some {start := {line := startLine, ..}, ..} := rangeOfStx? text listInfo.items[0]
              | result
            let some {«end» := {line := endLine, ..}, ..} := rangeOfStx? text listInfo.items.back!
              | result
            result.push {startLine := startLine, endLine := endLine}
          else result
        lists := lists ++ snapLists
      pure lists

    getSyntactic text ss : Array FoldingRange :=
      ss.foldl (init := #[]) (· ++ getFromSyntax text ·.stx)

    getFromSyntax text (stx : Syntax) : Array FoldingRange :=
      match stx with
      | .node _ k children =>
        let here :=
          if isFoldable k then
            if let some {start := {line:=startLine, ..}, «end» := {line := endLine, ..}} := rangeOfStx? text stx then
              #[{startLine, endLine}]
            else #[]
          else #[]
        children.flatMap (getFromSyntax text) ++ here
      | _ => #[]
    isFoldable : Name → Bool
      | `Verso.Syntax.codeblock | `Verso.Syntax.directive | `Verso.Syntax.metadata_block | `Verso.Syntax.blockquote
      | `Verso.Syntax.ol | `Verso.Syntax.ul | `Verso.Syntax.dl => true
      | _ => false
    getSections (text : FileMap) (ss : List Snapshots.Snapshot) : Array FoldingRange := Id.run do
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
            if let some {start := {line := startLine, ..}, ..} := rangeOfStx? text titleStx then
              let {line := endLine, ..} := text.utf8PosToLspPos endPos
              if endLine - 1 > startLine then
                regions := regions.push {startLine := startLine, endLine := endLine - 1}
            info := children.toList ++ more
          | [] => break
      pure regions

open Lean Server Lsp RequestM in
def handleHover (params : HoverParams) (prev : RequestTask (Option Hover)) : RequestM (RequestTask (Option Hover)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos params.position
  bindWaitFindSnap doc (·.endPos + ' ' >= pos) (notFoundX := pure prev) fun snap => do
    withFallbackResponse prev <| pure <| Task.spawn <| fun () => do
      let nodes : List (Syntax × CustomHover) := snap.infoTree.deepestNodes fun _ctxt info _arr =>
        match info with
        | .ofCustomInfo ⟨stx, data⟩ =>
          if stx.containsPos pos then
            (stx, ·) <$> data.get? CustomHover
          else none
        | _ => none
      match nodes with
      | [] => prev.get
      | h :: hs =>
        let mut best := h
        for node@(stx, _) in hs do
          if contains text best.fst stx then
            best := node
        pure <| some {
          contents := {kind := .markdown, value := best.snd.markedString},
          range? := best.fst.lspRange text
        }
  where
    contains (text : FileMap) (stx1 stx2 : Syntax) : Bool :=
      match stx1.lspRange text, stx2.lspRange text with
      | none, none => false
      | none, some _ => true
      | some _, none => false
      | some r1, some r2 => rangeContains r1 r2


open Lean Server Lsp in
initialize
  chainLspRequestHandler "textDocument/definition" TextDocumentPositionParams (Array LocationLink) handleDef
  -- chainLspRequestHandler "textDocument/references" ReferenceParams (Array Location) handleRefs -- TODO make this work - right now it goes through the watchdog so we can't chain it
  chainLspRequestHandler "textDocument/documentHighlight" DocumentHighlightParams DocumentHighlightResult handleHl
  chainLspRequestHandler "textDocument/documentSymbol" DocumentSymbolParams DocumentSymbolResult handleSyms
  chainLspRequestHandler "textDocument/semanticTokens/full" SemanticTokensParams SemanticTokens handleTokensFull
  chainLspRequestHandler "textDocument/semanticTokens/range" SemanticTokensRangeParams SemanticTokens handleTokensRange
  chainLspRequestHandler "textDocument/foldingRange" FoldingRangeParams (Array FoldingRange) handleFolding
  chainLspRequestHandler "textDocument/hover" HoverParams (Option Hover) handleHover
