/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Json.Basic
public import Lean.Data.Lsp.LanguageFeatures
public import Lean.Server.CodeActions.Basic
public meta import Lean.Server.FileWorker.SemanticHighlighting
import Lean.Data.Lsp
import Lean.Server

public meta import Verso.Doc.Elab.Basic
import Verso.Method
import Verso.Doc.Elab.Monad
import Lean.DocString.Syntax
public meta import Verso.Hover
public meta import Verso.Doc.PointOfInterest
public meta import Verso.Doc.Name

namespace Verso.Lsp

open Verso.Doc.Elab (DocListInfo DocRefInfo TOC)
open Verso.Doc (PointOfInterest)
open Verso.Hover
open Lean.Doc.Syntax

open Lean


open Lean Server in
/--
Runs `act` to handle a request. If the result satisfies `accept`, then it is returned.

If the result does not satisfy request, then it is handled by the prior response `resp`. If it
fails, then the error is logged and `resp` is used.
-/
meta def withFallbackAs (accept : α → Bool) (resp : RequestTask α) (act : RequestM α) : RequestM (RequestTask α) := do
  RequestM.bindTaskCostly (← act.asTask) fun
    | .error e => do
      (← read).hLog.putStrLn s!"Doc LSP request failed: {e.message}"
      pure resp
    | .ok v =>
      if accept v then pure (.pure v)
      else pure resp

meta defmethod Syntax.containsPos (s : Syntax) (p : String.Pos.Raw) : Bool :=
  match span s.getHeadInfo, span s.getTailInfo with
  | some (start, _), some (_, stop) => p >= start && p < stop
  | _, _ => false
where
  span : SourceInfo → Option (String.Pos.Raw × String.Pos.Raw)
    | .original (pos := start) (endPos := stop) .. => some (start, stop)
    | .synthetic (pos := start) (endPos := stop) .. => some (start, stop)
    | _ => none

meta defmethod Syntax.lspRange (text : FileMap) (s : Syntax) : Option Lsp.Range :=
  match span s.getHeadInfo, span s.getTailInfo with
  | some (start, _), some (_, stop) => some ⟨text.utf8PosToLspPos start, text.utf8PosToLspPos stop⟩
  | _, _ => none
where
  span : SourceInfo → Option (String.Pos.Raw × String.Pos.Raw)
    | .original (pos := start) (endPos := stop) .. => some (start, stop)
    | .synthetic (pos := start) (endPos := stop) .. => some (start, stop)
    | _ => none


open Lean.Lsp in
meta instance : FromJson DocumentHighlightKind where
  fromJson?
    | 1 => pure DocumentHighlightKind.text
    | 2 => pure DocumentHighlightKind.read
    | 3 => pure DocumentHighlightKind.write
    | n => throw s!"Expected 1, 2, or 3, got {n}"

meta section
deriving instance FromJson for Lean.Lsp.DocumentHighlight
end

meta instance : FromJson Lean.Lsp.SymbolKind where
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

meta section
deriving instance FromJson for Lean.Lsp.DocumentSymbolAux
end

open Lean Lsp in
set_option linter.unusedVariables false in -- it doesn't like the `inst` name here
meta partial def symFromJson? (j : Json) : Except String DocumentSymbol := do
  let fromJ : {α : _} → [inst : FromJson α] → FromJson (Lean.Lsp.DocumentSymbolAux α) := inferInstance
  DocumentSymbol.mk <$> @FromJson.fromJson? _ (fromJ (inst:=⟨symFromJson?⟩)) j

meta instance : FromJson Lean.Lsp.DocumentSymbol where
  fromJson? := symFromJson?

meta partial instance : FromJson Lean.Lsp.DocumentSymbolResult where
  fromJson? j := do
    let .arr elts := j
      | throw "expected array"
    let syms ← elts.mapM fromJson?
    pure ⟨syms⟩


open Lean Server Lsp RequestM in
meta def handleRefs (params : ReferenceParams) (prev : RequestTask (Array Location)) : RequestM (RequestTask (Array Location)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos params.position
  bindWaitFindSnap doc (·.endPos + ' ' >= pos) (notFoundX := pure prev) fun snap => do
    withFallbackAs (!·.isEmpty) prev <| do
      let nodes := snap.infoTree.deepestNodes fun _ctxt info _arr =>
        match info with
        | .ofCustomInfo ⟨stx, data⟩ =>
          if stx.containsPos pos then
            data.get? DocRefInfo
          else none
        | _ => none
      if nodes.isEmpty then return #[]
      else
        let mut locs : Array Location := #[]
        for node in nodes do
          for stx in node.syntax do
            if let some range := stx.lspRange text then
              locs := locs.push {uri := params.textDocument.uri, range := range}
        pure <| locs

open Lean Server Lsp RequestM in
meta partial def handleHl (params : DocumentHighlightParams) (prev : RequestTask DocumentHighlightResult) : RequestM (RequestTask DocumentHighlightResult) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos params.position
  bindWaitFindSnap doc (·.endPos + ' ' >= pos) (notFoundX := pure prev) fun snap =>
    withFallbackAs (!·.isEmpty) prev <| do
      let nodes : List (_ ⊕ _) := snap.infoTree.deepestNodes fun _ctxt info _arr =>
        match info with
        | .ofCustomInfo ⟨stx, data⟩ =>
          if stx.containsPos pos then
            (Sum.inl <$> data.get? DocListInfo) <|> (Sum.inr <$> data.get? DocRefInfo)
          else none
        | _ => none
      if nodes.isEmpty then
        if let some hls := syntactic text pos snap.stx then
          return hls.filterMap (fun stx : Syntax => stx.lspRange text) |>.map ({range := · : DocumentHighlight})
        else
          return #[]
      else
        let mut hls := #[]
        for node in nodes do
          match node with
          | .inl ⟨bulletStxs, _⟩ =>
            for s in bulletStxs do
              if let some range := s.lspRange text then
                hls := hls.push {range : DocumentHighlight}
          | .inr ⟨defSite, useSites⟩ =>
            if let some s := defSite then
              if let some range := s.lspRange text then
                hls := hls.push {range : DocumentHighlight}
            for s in useSites do
              if let some range := s.lspRange text then
                hls := hls.push {range : DocumentHighlight}
        pure hls
where
  -- Unfortunately, VS Code doesn't do the right thing, so many of these highlights don't work there:
  --   https://github.com/microsoft/vscode/issues/127007
  -- Tested in Emacs and the problem isn't server side.
  syntactic (text : FileMap) (pos : String.Pos.Raw) (stx : Syntax) : Option (Array Syntax) := do
    if includes stx pos |>.getD true then
      match stx with
        | `(block|:::%$opener $_name $_args* {$_contents*}%$closer )
        | `(block|```%$opener | $_contents ```%$closer)
        | `(block|```%$opener $_name $_args* | $_contents ```%$closer) =>
          if (includes opener pos).getD false || (includes closer pos).getD false then
            return #[opener, closer]
        | _ =>
          match stx with
          | `(inline| \math%$opener1 code(%$opener2 $_ )%$closer1)
          | `(inline| \displaymath%$opener1 code(%$opener2 $_ )%$closer1) =>
            if (includes opener1 pos).getD false || (includes closer1 pos).getD false || (includes opener2 pos).getD false then
              return #[opener1, closer1, opener2]
          | `(inline| link[%$opener1 $_* ]%$closer1 (%$opener2 $_ )%$closer2)
          | `(inline| link[%$opener1 $_* ]%$closer1 [%$opener2 $_ ]%$closer2) =>
            if (includes opener1 pos).getD false || (includes closer1 pos).getD false || (includes opener2 pos).getD false || (includes closer2 pos).getD false then
              return #[opener1, closer1, opener2, closer2]
          |  `(inline| code(%$opener $_ )%$closer) =>
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

  includes (stx : Syntax) (pos : String.Pos.Raw) : Option Bool :=
    stx.getRange?.map (fun r => pos ≥ r.start && pos < r.stop)

open Lean Lsp

meta def rangeContains (outer inner : Lsp.Range) :=
  outer.start < inner.start && inner.«end» ≤ outer.«end» ||
  outer.start == inner.start && inner.«end» < outer.«end»

meta partial def mergeInto (sym : DocumentSymbol) (existing : Array DocumentSymbol) : Array DocumentSymbol := Id.run do
  let ⟨sym⟩ := sym
  for h : i in [0:existing.size] do
    let ⟨e⟩ := existing[i]
    have : i < existing.size := by get_elem_tactic
    have : i ≤ existing.size := by omega
    let children := e.children?.getD #[]

    -- the symbol to be inserted belongs before the current symbol
    if sym.range.end ≤ e.range.start then
      return existing.insertIdx i ⟨sym⟩
    -- the symbol to be inserted intersects the current symbol but neither contains the other
    else if sym.range.start < e.range.start && sym.range.end ≤ e.range.end then
      return existing.insertIdx i ⟨sym⟩
    else if sym.range.start ≥ e.range.start && sym.range.start < e.range.end && sym.range.end > e.range.end then
      return existing.insertIdx (i + 1) ⟨sym⟩
    -- The symbol to be inserted is inside the existing one
    else if sym.range.start ≥ e.range.start && sym.range.end ≤ e.range.end then
      return existing.set i ⟨{e with children? := some (mergeInto ⟨sym⟩ children)}⟩
    -- The symbol to be inserted encompasses the existing one
    else if sym.range.start ≤ e.range.start && sym.range.end ≥ e.range.end then
      let (inside, outside) := existing.partition (fun ⟨e⟩ => sym.range.start ≤ e.range.start && sym.range.end ≥ e.range.end)
      let (pre, post) := outside.partition (fun ⟨e⟩ => sym.range.end ≤ e.range.start)
      return pre ++ inside.foldr (init := #[⟨sym⟩]) mergeInto ++ post
    -- The symbol to be inserted is after the existing one
    else
      continue
  -- If we got through the loop, then the new symbol belongs at the end
  return existing.push ⟨sym⟩

meta def mergeManyInto (syms : Array DocumentSymbol) (existing : Array DocumentSymbol) : Array DocumentSymbol :=
  syms.foldr (init := existing) mergeInto

/--
The Lean VS Code mode can't deal with symbols whose names are "falsy" - this recovers more
robustly, removing empty strings and arrays.
-/
meta partial def removeFalsy (sym : DocumentSymbol) : DocumentSymbol :=
  match sym with
  | ⟨sym'⟩ =>
    ⟨{sym' with
        name := if sym'.name.trim.isEmpty then "<no name>" else sym'.name,
        detail? := do
          let detail ← sym'.detail?
          if detail.trim.isEmpty then
            none
          else
            pure detail
        children? :=
          match sym'.children? with
          | none | some #[] => none
          | some more => some (more.map removeFalsy)
      }⟩

open Lean Server Lsp RequestM in
meta def mergeResponses (docTask : RequestTask α) (leanTask : RequestTask β) (f : Option α → Option β → γ) : RequestM (RequestTask γ) := do
  pure <| docTask.bindCostly fun
  | .ok docResult =>
    leanTask.bindCostly fun
    | .ok leanResult =>
      .mk <| .pure <| pure <| f (some docResult) (some leanResult)
    | .error _ => .mk <| .pure <| pure <| f (some docResult) none
  | .error _ =>
    leanTask.bindCostly fun
    | .ok leanResult => .mk <| .pure <| pure <| f none (some leanResult)
    | .error e => .pure <| throw e

-- In Lean 4.18.0, this function has type IO, but we need a BaseIO version here. TODO: modify the
-- type upstream, then delete this shim.
meta def findSimpleDocStringCompat? (env : Environment) (declName : Name) : BaseIO (Option String) :=
  pure <| docStringExt.find? env declName

open Lean Server Lsp RequestM in
meta partial def handleSyms (_params : DocumentSymbolParams) (prev : RequestTask DocumentSymbolResult) : RequestM (RequestTask DocumentSymbolResult) := do
  let doc ← readDoc
  let t := doc.cmdSnaps.waitAll
  bindTaskCostly t fun (snaps, _) => do
    let text := doc.meta.text
    let syms : DocumentSymbolResult := { syms := ← getSections text snaps }
    let syms' : DocumentSymbolResult := { syms := ofInterest text snaps }
    let out ← mergeResponses (.pure <| combineAnswers' syms syms') prev combineAnswers
    pure <| out.mapCostly (·.map fun ⟨vs⟩ => ⟨vs.map removeFalsy⟩)

  where
    combineAnswers (x y : Option DocumentSymbolResult) : DocumentSymbolResult :=
      ⟨mergeManyInto (x.getD ⟨{}⟩).syms (y.getD ⟨{}⟩).syms⟩
    combineAnswers' (x y : DocumentSymbolResult) : DocumentSymbolResult :=
      ⟨mergeManyInto x.syms y.syms⟩
    tocSym (env) (text : FileMap) : TOC → BaseIO (Option DocumentSymbol)
      | .mk title titleStx endPos children => do
        let some selRange@⟨start, _⟩ := titleStx.lspRange text
          | return none
        let mut kids := #[]
        for c in children do
          if let some s ← tocSym env text c then kids := kids.push s
        return some <| DocumentSymbol.mk {
          name := title,
          kind := SymbolKind.string,
          range := ⟨start, text.utf8PosToLspPos endPos⟩,
          selectionRange := selRange,
          children? := kids
        }
      | .included name => do
        let title := (← findSimpleDocStringCompat? env name.getId).getD (toString <| Verso.Doc.unDocName name.getId)
        let some rng := name.raw.lspRange text
          | return none
        return some <| DocumentSymbol.mk {
          name := title,
          kind := SymbolKind.property,
          range := rng,
          selectionRange := rng,
          detail? := some s!"Included from {name.getId}"
        }
    getSections text (ss : List Snapshots.Snapshot) : BaseIO (Array DocumentSymbol) := do
      let mut syms : Array DocumentSymbol := #[]
      for snap in ss do
        let info := snap.infoTree.deepestNodes fun _ctxt info _arr =>
          match info with
          | .ofCustomInfo ⟨_stx, data⟩ =>
            data.get? TOC
          | _ => none
        for i in info do
          if let some x ← tocSym snap.env text i then syms := syms.push x
      pure syms
    ofInterest (text : FileMap) (ss : List Snapshots.Snapshot) : Array DocumentSymbol := Id.run do
      let mut syms := #[]
      for snap in ss do
        let info := snap.infoTree.deepestNodes fun _ctxt info _arr =>
          match info with
          | .ofCustomInfo ⟨stx, data⟩ =>
            data.get? PointOfInterest |>.map (stx, ·)
          | _ => none
        for (stx, {title, selectionRange, kind, detail?}) in info do
          if let some rng := stx.lspRange text then
            -- Truncate the inner to the outer if the user made a mistake with it
            let selectionRange := truncate rng (selectionRange.map text.utf8RangeToLspRange |>.getD rng)
            let sym := .mk {
              name := title,
              range := rng,
              selectionRange,
              detail?,
              kind
            }
            -- mergeInto is needed here to keep the tree invariant
            syms := mergeInto sym syms
      pure syms
    truncate (outer inner : Range) : Range :=
      if inner.start < outer.start && inner.end < outer.end then outer
      else if inner.start > outer.end then outer
      else
        let start := if outer.start > inner.start then outer.start else inner.start
        let «end» := if outer.start < inner.start then outer.start else inner.start
        ⟨start, «end»⟩

-- Shamelessly cribbed from https://github.com/tydeu/lean4-alloy/blob/57792f4e8a9674f8b4b8b17742607a1db142d60e/Alloy/C/Server/SemanticTokens.lean
structure SemanticTokenEntry where
  line : Nat
  startChar : Nat
  length : Nat
  type : Nat
  modifierMask : Nat
deriving Inhabited, Repr

protected meta def SemanticTokenEntry.ordLt (a b : SemanticTokenEntry) : Bool :=
  a.line < b.line ∨ (a.line = b.line ∧ a.startChar < b.startChar)

meta def encodeTokenEntries (entries : Array SemanticTokenEntry) : Array Nat := Id.run do
  let mut data := #[]
  let mut lastLine := 0
  let mut lastChar := 0
  for ⟨line, char, len, type, modMask⟩ in entries do
    let deltaLine := line - lastLine
    let deltaStart := if line = lastLine then char - lastChar else char
    data := data ++ #[deltaLine, deltaStart, len, type, modMask]
    lastLine := line; lastChar := char
  return data

meta def decodeLeanTokens (data : Array Nat) : Array SemanticTokenEntry := Id.run do
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

meta partial def versoTokens (text : FileMap) (stx : Syntax) : Array SemanticTokenEntry := Id.run do
  match stx with
  | `(inline|$_s:str) =>
    mkTok text .string stx
  | `(inline|_[%$s $inlines* ]%$e) | `(inline|*[%$s $inlines* ]%$e) =>
    mkTok text .keyword s ++ versoTokens text (mkNullNode inlines) ++ mkTok text .keyword e
  | `(inline|role{%$s $f $args*}%$e [%$s' $inlines* ]%$e') =>
    mkTok text .keyword s ++
    mkTok text .function f ++
    versoTokens text (mkNullNode args) ++
    mkTok text .keyword e ++
    mkTok text .keyword s' ++
    versoTokens text (mkNullNode inlines) ++
    mkTok text .keyword e'
  | `(inline|link[%$s $inlines* ]%$e (%$s' $tgt )%$e')
  | `(inline|link[%$s $inlines* ]%$e [%$s' $tgt ]%$e') =>
    mkTok text .keyword s ++
    versoTokens text (mkNullNode inlines) ++
    mkTok text .keyword e ++
    mkTok text .keyword s' ++
    mkTok text .parameter tgt ++
    mkTok text .keyword e'
  | `(inline|image(%$s $alt )%$e (%$s' $tgt )%$e')
  | `(inline|image(%$s $alt )%$e [%$s' $tgt ]%$e') =>
    mkTok text .keyword s ++
    versoTokens text alt ++
    mkTok text .keyword e ++
    mkTok text .keyword s' ++
    mkTok text .parameter tgt ++
    mkTok text .keyword e'
  | `(inline|footnote(%$s $note )%$e) =>
    mkTok text .keyword s ++
    mkTok text .parameter note ++
    mkTok text .keyword e
  | `(inline|code(%$s $_str )%$e) =>
    mkTok text .keyword s ++
    -- None for str, so Lean's can pass through
    mkTok text .keyword e
  | `(inline|\math%$m code(%$s $str )%$e)
  | `(inline|\displaymath%$m code(%$s $str )%$e) =>
    mkTok text .keyword m ++
    mkTok text .keyword s ++
     -- Enum member arbitrarily chosen for uniqueness
    mkTok text .enumMember str ++
    mkTok text .keyword e
  | `(desc_item| :%$s $inlines* =>%$e $blocks*) =>
    mkTok text .keyword s ++
    versoTokens text (mkNullNode inlines) ++
    mkTok text .keyword e ++
    versoTokens text (mkNullNode blocks)
  | `(list_item| *%$bulletOrNum $contents*) =>
    mkTok text .keyword bulletOrNum ++
    versoTokens text (mkNullNode contents)
  | `(block| :::%$s $f $args* {%$s' $body* }%$e) =>
    mkTok text .keyword s ++
    mkTok text .function f ++
    versoTokens text (mkNullNode args) ++
    mkTok text .keyword s' ++
    versoTokens text (mkNullNode body) ++
    mkTok text .keyword e
  | `(block| ```%$s $f $args* |%$s' $_code ```%$e) =>
    mkTok text .keyword s ++
    mkTok text .function f ++
    versoTokens text (mkNullNode args) ++
    mkTok text .keyword s' ++
    -- No token for the code, because we want Lean's tokens to shine through
    mkTok text .keyword e
  | `(block| >%$s $blocks*) =>
    mkTok text .keyword s ++ versoTokens text (mkNullNode blocks)
  | `(block|header(%$s $n )%$e {%$s' $txt* }%$e') =>
    mkTok text .keyword s ++
    versoTokens text n ++
    mkTok text .keyword e ++
    mkTok text .keyword s' ++
    versoTokens text (mkNullNode txt) ++
    mkTok text .keyword e'
  | `(block|[^%$s $n ]:%$e $txt*) =>
    mkTok text .keyword s ++
    mkTok text .parameter n ++
    mkTok text .keyword e ++
    versoTokens text (mkNullNode txt)
  | `(block|[%$s $n ]:%$e $url) =>
    mkTok text .keyword s ++
    mkTok text .parameter n ++
    mkTok text .keyword e ++
    mkTok text .parameter url
  | `(block| %%%%$s $_defs* %%%%$e) =>
    mkTok text .keyword s ++
    -- No tokens for defs, because Lean should supply them
    mkTok text .keyword e
  | `(block| command{%$s $f $args* }%$e) =>
    mkTok text .keyword s ++
    mkTok text .function f ++
    versoTokens text (mkNullNode args) ++
    mkTok text .keyword e
  | `(doc_arg| $x:ident :=%$eq $v:arg_val) =>
    mkTok text .parameter x ++
    mkTok text .keyword eq ++
    versoTokens text v
  | `(doc_arg| $v:arg_val) =>
    versoTokens text v
  -- In the next three cases, no token is returned. This is to allow Lean's to shine through, if
  -- there are any. It would be nice to add a priority mechanism to fall back to these defaults if
  -- Lean didn't provide any.
  | `(arg_val| $_v:num) =>
    --mkTok text .number v
    #[]
  | `(arg_val| $_v:ident) =>
    -- mkTok text .variable v
    #[]
  | `(arg_val| $_v:str) =>
    -- mkTok text .string v
    #[]
  | _ =>
    let mut out := #[]
    for arg in stx.getArgs do
      out := out ++ versoTokens text arg
    return out
where
  mkTok (text : FileMap) (tokenType : SemanticTokenType) (stx : Syntax) : Array SemanticTokenEntry := Id.run do
    let (some startPos, some endPos) := (stx.getPos?, stx.getTailPos?)
      | return #[]
    let startLspPos := text.utf8PosToLspPos startPos
    let endLspPos := text.utf8PosToLspPos endPos
    -- VS Code has a limitation where tokens can't span lines. The
    -- parser obeys an invariant that no token spans a line, so we can
    -- bail, rather than resorting to workarounds.
    if startLspPos.line == endLspPos.line then #[{
        line := startLspPos.line,
        startChar := startLspPos.character,
        length := endLspPos.character - startLspPos.character,
        type := tokenType.toNat,
        modifierMask := 0
      }]
    else #[]

meta def mergeTokens (mine : Array SemanticTokenEntry) (leans : SemanticTokens) : Array Nat:=
  let toks := decodeLeanTokens leans.data
  encodeTokenEntries (toks ++ mine |>.qsort (·.ordLt ·))

open Lean Server Lsp RequestM in
meta def snapshotTokens (beginPos : String.Pos.Raw) (text : FileMap) (snap : Snapshots.Snapshot) : Array SemanticTokenEntry :=
  if snap.endPos <= beginPos then #[] else versoTokens text snap.stx

open Lean Server Lsp RequestM in
meta def snapshotsTokens (beginPos : String.Pos.Raw) (text : FileMap) (snaps : List Snapshots.Snapshot) : Array SemanticTokenEntry :=
  snaps.foldl (init := #[]) fun toks snap => toks ++ snapshotTokens beginPos text snap

open Lean Server Lsp IO in
partial def getFinishedPrefixWithTimeout' (xs : AsyncList ε α) (timeoutMs : UInt32)
    (cancelTks : List (ServerTask Unit) := []) : BaseIO (ServerTask (List α × Option ε × Bool)) := do
  let timeoutTask : ServerTask (Unit ⊕ Except ε (AsyncList ε α)) ←
    if timeoutMs == 0 then
      pure <| ServerTask.pure (Sum.inl ())
    else
      ServerTask.BaseIO.asTask do
        IO.sleep timeoutMs
        return .inl ()
  go timeoutTask xs
where
  go (timeoutTask : ServerTask (Unit ⊕ Except ε (AsyncList ε α)))
      (xs : AsyncList ε α) : BaseIO (ServerTask (List α × Option ε × Bool)) := do
    match xs with
    | .cons hd tl =>
      let tlTask ← go timeoutTask tl
      pure <| tlTask.mapCheap fun ⟨tl, e?, isComplete⟩ => ⟨hd :: tl, e?, isComplete⟩
    | .nil => return .pure ⟨[], none, true⟩
    | .delayed tl =>
      let tl : ServerTask (Except ε (AsyncList ε α)) := tl
      let tl := tl.mapCheap .inr
      let cancelTks := cancelTks.map (·.mapCheap .inl)
      let r ← ServerTask.waitAny (tl :: cancelTks ++ [timeoutTask])
      match r with
      | .inl _ => return ⟨[], none, false⟩ -- Timeout or cancellation - stop waiting
      | .inr (.ok tl) => go timeoutTask tl
      | .inr (.error e) => return ⟨[], some e, true⟩

open Lean Server Lsp RequestM in
meta def handleDef (params : TextDocumentPositionParams) (prev : RequestTask (Array LeanLocationLink)) : RequestM (RequestTask (Array LeanLocationLink)) := do
  let ctx ← read
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos params.position
  let locTask ← RequestM.asTask do
    let (snaps, _, _) ← doc.cmdSnaps.getFinishedPrefixWithTimeout 300 (cancelTks := ctx.cancelTk.cancellationTasks)
    let nodes := snaps.flatMap fun snap =>
      snap.infoTree.collectNodesBottomUp fun _ctxt info _arr xs =>
          match info with
          | .ofCustomInfo ⟨stx, data⟩ =>
            if stx.containsPos pos then
              if let some i := data.get? DocRefInfo then i :: xs else xs
            else xs
          | _ => xs

    let mut locs : Array LeanLocationLink := #[]
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
        locs := locs.push {
          originSelectionRange? := origin,
          targetRange := target,
          targetUri := params.textDocument.uri,
          targetSelectionRange := target,
          -- Because this is `none`, the watchdog will not keep this up to date as files are
          -- edited. This seems to be OK, because this feature is currently only used for
          -- references valid the current file. Adding the field would be useful in the future,
          -- but it would require actually defining each footnote/link ref as its own name in the
          -- environment and tracking this in Verso.
          ident? := none,
          isDefault := true
        }
      | _ => continue
    pure locs
  mergeResponses prev locTask fun xs ys =>
    xs.getD #[] ++ ys.getD #[]

open Lean Server Lsp RequestM in
meta partial def handleTokens (prev : RequestTask SemanticTokens)
    (beginPos : String.Pos.Raw) (endPos? : Option String.Pos.Raw) :
    RequestM (RequestTask (LspResponse SemanticTokens)) := do
  let ctx ← read
  let doc ← readDoc
  let text := doc.meta.text
  if let some endPos := endPos? then
    let t := doc.cmdSnaps.waitUntil (·.endPos >= endPos)
    let toks : RequestTask (Array SemanticTokenEntry) :=
      t.mapCostly fun (snaps, _) => pure <| snapshotsTokens beginPos text snaps
    let response ← mergeIntoPrev toks
    return response.mapCheap fun t =>
      t.map ({ response := ·, isComplete := true })
  else
    let (snaps, _, isComplete) ← doc.cmdSnaps.getFinishedPrefixWithTimeout 2000 (cancelTks := ctx.cancelTk.cancellationTasks)
    let toks : Array SemanticTokenEntry := snapshotsTokens beginPos text snaps
    let response ← mergeIntoPrev (.pure toks)
    pure <| response.mapCheap fun t => t.map ({ response := ·, isComplete := isComplete })

where
  mergeIntoPrev (toks : RequestTask (Array SemanticTokenEntry)) :=
    mergeResponses toks prev fun
      | none, none => SemanticTokens.mk none #[]
      | some xs, none => SemanticTokens.mk none <| encodeTokenEntries <| xs.qsort (·.ordLt ·)
      | none, some r => r
      | some mine, some leans => {leans with data := mergeTokens mine leans}

open Lean Server Lsp RequestM in
meta def handleTokensRange (params : SemanticTokensRangeParams) (prev : RequestTask SemanticTokens) : RequestM (RequestTask SemanticTokens) := do
  let doc ← readDoc
  let text := doc.meta.text
  let beginPos := text.lspPosToUtf8Pos params.range.start
  let endPos := text.lspPosToUtf8Pos params.range.end
  handleTokens prev beginPos endPos <&> fun t => t.mapCheap (LspResponse.response <$> ·)

open Lean Server Lsp RequestM in
meta def handleTokensFull (_params : SemanticTokensParams) (prev : RequestTask SemanticTokens) : RequestM (RequestTask SemanticTokens) :=
  handleTokens prev 0 none <&> fun t => t.mapCheap (LspResponse.response <$> ·)

open Lean.Server in


open Lean Server Lsp RequestM in
open Lean.Server.FileWorker in
meta def handleTokensFullStateful
    (_params : SemanticTokensParams) (prev : LspResponse SemanticTokens) (st : SemanticTokensState) :
    RequestM (LspResponse SemanticTokens × SemanticTokensState) := do
  let doc ← readDoc
  let text := doc.meta.text
  let (snaps, _, isComplete) ← doc.cmdSnaps.getFinishedPrefixWithTimeout 2000
  RequestM.checkCancelled
  let toks : Array SemanticTokenEntry := snapshotsTokens 0 text snaps
  RequestM.checkCancelled
  let response := {prev with data := mergeTokens toks prev.response}
  RequestM.checkCancelled
  return ({response, isComplete}, st)


open Lean Server Lsp RequestM in
@[code_action_provider]
public meta def renumberLists : CodeActionProvider := fun params snap => do
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

meta partial def directiveResizings
    (startPos endPos : String.Pos.Raw)
    (startLine endLine : Nat)
    (text : FileMap)
    (parents : Array (Syntax × Syntax))
    (subject : Syntax) :
    StateM (Array (Bool × Syntax × Syntax × TextEditBatch)) Unit := do
  if let `(block|:::%$opener $_name $_args* { $contents* }%$closer ) := subject then
    let parents := parents.push (opener, closer)
    if onLine opener || onLine closer then
      if let some edit := parents.flatMapM getIncreases then
        modify (·.push (true, opener, closer, edit))
      if let some edit := getDecreases (opener, closer) contents then
        modify (·.push (false, opener, closer, edit))
    else
      for s in contents do directiveResizings startPos endPos startLine endLine text parents s
  else if let .node _ _ contents := subject then
    if inRange subject then
      for s in contents do
        directiveResizings startPos endPos startLine endLine text parents s
  else pure ()
where
  onLine (stx : Syntax) : Bool := Id.run do
    if startLine != endLine then return false
    let some stxPos := stx.getPos?
      | false
    let some stxTailPos := stx.getTailPos?
      | false
    let ⟨{line := stxStartLine, ..}, {line := stxEndLine, ..}⟩ :=
      text.utf8RangeToLspRange ⟨stxPos, stxTailPos⟩
    if stxStartLine != stxEndLine then return false
    startLine == stxStartLine
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

  getDecreasesIn (stx : Syntax) : Option TextEditBatch :=
    if let `(block|:::%$opener $_name $_args* {$contents*}%$closer) := stx then
      getDecreases (opener, closer) contents
    else if let .node _ _ children := stx then children.flatMapM getDecreasesIn
    else pure #[]

  getDecrease : Syntax → Option TextEdit
  | stx@(.atom _ colons) => do
    if let some r := stx.lspRange text then
      if colons.length > 3 then
        return {range := r, newText := colons.drop 1}
    failure
  | _ => none


open Lean Server Lsp RequestM in
@[code_action_provider]
public meta def resizeDirectives : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let startPos := text.lspPosToUtf8Pos params.range.start
  let endPos := text.lspPosToUtf8Pos params.range.end
  let ((), directives) :=
    (directiveResizings startPos endPos
      params.range.start.line params.range.end.line
      text #[] snap.stx).run #[]
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


meta section
deriving instance FromJson for FoldingRangeKind
deriving instance FromJson for FoldingRange
end

private meta def rangeOfStx? (text : FileMap) (stx : Syntax) :=
  Lean.FileMap.utf8RangeToLspRange text <$> Lean.Syntax.getRange? stx

open Lean Server Lsp RequestM in
meta partial def handleFolding (_params : FoldingRangeParams) (prev : RequestTask (Array FoldingRange)) : RequestM (RequestTask (Array FoldingRange)) := do
  let doc ← readDoc
  let text := doc.meta.text
  -- bad: we have to wait on elaboration of the entire file before we can report folding
  let t := doc.cmdSnaps.waitAll
  let folds := t.mapCostly fun (snaps, _) =>
    pure <| getSections text snaps ++ getSyntactic text snaps ++ getLists text snaps
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
meta def handleHover (params : HoverParams) (prev : RequestTask (Option Hover)) : RequestM (RequestTask (Option Hover)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos params.position
  bindWaitFindSnap doc (·.endPos + ' ' >= pos) (notFoundX := pure prev) fun snap => do
    withFallbackAs (·.isSome) prev <| do
      let nodes : List (Syntax × CustomHover) := snap.infoTree.deepestNodes fun _ctxt info _arr =>
        match info with
        | .ofCustomInfo ⟨stx, data⟩ =>
          if stx.containsPos pos then
            (stx, ·) <$> data.get? CustomHover
          else none
        | _ => none
      match nodes with
      | [] => pure none
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

section handlers

open Lean Server Lsp

open Lean.Server.FileWorker



open Lean Server Lsp in
meta initialize
  chainLspRequestHandler "textDocument/definition" TextDocumentPositionParams (Array LeanLocationLink) handleDef
  -- chainLspRequestHandler "textDocument/references" ReferenceParams (Array Location) handleRefs -- TODO make this work - right now it goes through the watchdog so we can't chain it
  chainLspRequestHandler "textDocument/documentHighlight" DocumentHighlightParams DocumentHighlightResult handleHl
  chainLspRequestHandler "textDocument/documentSymbol" DocumentSymbolParams DocumentSymbolResult handleSyms
  chainLspRequestHandler "textDocument/foldingRange" FoldingRangeParams (Array FoldingRange) handleFolding
  chainLspRequestHandler "textDocument/hover" HoverParams (Option Hover) handleHover
  chainLspRequestHandler "textDocument/semanticTokens/range" SemanticTokensRangeParams SemanticTokens handleTokensRange
  chainStatefulLspRequestHandler "textDocument/semanticTokens/full" SemanticTokensParams SemanticTokens SemanticTokensState handleTokensFullStateful handleSemanticTokensDidChange

end handlers
