import Lean
import Lean.Data.Lsp
import Std.CodeAction.Basic

import LeanDoc.Doc.Elab

open Std.CodeAction (findInfoTree?)
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
    -- let some (ctxt, tree) := findInfoTree? (Name.mkSimple "*") ⟨pos, pos⟩ none snap.infoTree (canonicalOnly := false) (fun _ info => info matches .ofCustomInfo _)
    --   | dbg_trace "none"; pure prev
    withFallbackResponse prev <| pure <| Task.spawn <| fun () => do
      let nodes := snap.infoTree.deepestNodes fun ctxt info arr =>
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

def combine (f : α → α → α) (g : ε → ε → ε) : Except ε α → Except ε α → Except ε α
  | .ok x, .ok y => .ok (f x y)
  | .error _, .ok y => .ok y
  | .ok x, .error _ => .ok x
  | .error x, .error y => .error (g x y)


open Lean Server Lsp RequestM in
partial def handleSyms (params : DocumentSymbolParams) (prev : RequestTask DocumentSymbolResult) : RequestM (RequestTask DocumentSymbolResult) := do
  dbg_trace "hey"
  let doc ← readDoc
  let text := doc.meta.text
  -- bad: we have to wait on elaboration of the entire file before we can report document symbols
  let t := doc.cmdSnaps.waitAll
  let syms ←
    mapTask t fun (snaps, _) => do
      return { syms := getSections text snaps }
  bindTask syms fun r1 =>
    bindTask prev fun r2 =>
      pure <| Task.spawn fun () => (combine (combineAnswers) (fun x _ => x) r1 r2)
  where
    combineAnswers (x y : DocumentSymbolResult) : DocumentSymbolResult := ⟨x.syms ++ y.syms⟩
    tocSym (text : _) : TOC → Option DocumentSymbol
      | .mk title titleStx endPos children => Id.run do
        let some selRange@⟨start, stop⟩ := titleStx.lspRange text
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
    getSections text ss := Id.run do
      let mut syms := #[]
      for snap in ss do
        let info := snap.infoTree.deepestNodes fun ctxt info arr =>
          match info with
          | .ofCustomInfo ⟨stx, data⟩ =>
            data.get? TOC
          | _ => none
        for i in info do
          if let some x := tocSym text i then syms := syms.push x
      dbg_trace (toJson syms)
      pure syms

open Lean Server Lsp in
initialize
  chainLspRequestHandler "textDocument/documentHighlight" DocumentHighlightParams DocumentHighlightResult handleHl
  chainLspRequestHandler "textDocument/documentSymbol" DocumentSymbolParams DocumentSymbolResult handleSyms
