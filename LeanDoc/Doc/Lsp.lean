import Lean
import Lean.Data.Lsp
import Std.CodeAction.Basic

import LeanDoc.Doc.Elab

open Std.CodeAction (findInfoTree?)
open LeanDoc.Doc.Elab (DocListInfo)

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


open Lean.Lsp in
instance : FromJson DocumentHighlightKind where
  fromJson?
    | 1 => pure DocumentHighlightKind.text
    | 2 => pure DocumentHighlightKind.read
    | 3 => pure DocumentHighlightKind.write
    | n => throw s!"Expected 1, 2, or 3, got {n}"


deriving instance FromJson for Lean.Lsp.DocumentHighlight


open Lean Server Lsp in
initialize
  chainLspRequestHandler "textDocument/documentHighlight" DocumentHighlightParams DocumentHighlightResult handleHl
