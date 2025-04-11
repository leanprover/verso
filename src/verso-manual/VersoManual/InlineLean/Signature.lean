/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Elab.InfoTree.Types

import Verso
import VersoManual.Basic
import SubVerso.Examples

open SubVerso.Highlighting

open Verso Genre Manual ArgParse Doc Elab
open Verso Output Html
open Verso Code Highlighted WebAssets
open Verso.SyntaxUtils
open Lean Elab

namespace Verso.Genre.Manual.InlineLean

block_extension Block.signature where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML signature: " ++ err ++ "\n" ++ toString data
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.blockHtml "examples"


declare_syntax_cat signature_spec
syntax ("def" <|> "theorem")? declId declSig : signature_spec

structure SignatureConfig where
  «show» : Bool := true

def SignatureConfig.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m SignatureConfig :=
  SignatureConfig.mk <$>
    ((·.getD true) <$> .named `show .bool true)


@[code_block_expander signature]
def signature : CodeBlockExpander
  | args, str => withoutAsync do
    let {«show»} ← SignatureConfig.parse.run args
    let altStr ← parserInputString str
    let col? := (← getRef).getPos? |>.map (← getFileMap).utf8PosToLspPos |>.map (·.character)


    match Parser.runParserCategory (← getEnv) `signature_spec altStr (← getFileName) with
    | .error e => throwError e
    | .ok stx =>
      let `(signature_spec|$[$kw]? $name:declId $sig:declSig) := stx
        | throwError m!"Didn't understand parsed signature: {indentD stx}"

      PointOfInterest.save (← getRef) (toString name.raw)
        (kind := Lsp.SymbolKind.file)
        (detail? := some "Signature")

      let cmdCtx : Command.Context := {
        fileName := ← getFileName,
        fileMap := ← getFileMap,
        snap? := none,
        cancelTk? := none
      }
      let cmdState : Command.State := {env := ← getEnv, maxRecDepth := ← MonadRecDepth.getMaxRecDepth, infoState := ← getInfoState}
      let hls ←
        try
          let ((hls, _, _, _), st') ← ((SubVerso.Examples.checkSignature name sig).run cmdCtx).run cmdState
          setInfoState st'.infoState
          pure (Highlighted.seq hls)
        catch e =>
          let fmt ← PrettyPrinter.ppSignature (TSyntax.mk name.raw[0]).getId
          Suggestion.saveSuggestion str (fmt.fmt.pretty 60) (fmt.fmt.pretty 30 ++ "\n")
          throw e

      let hls :=
        if let some col := col? then
          hls.deIndent col
        else hls

      if «show» then
        pure #[← `(Block.other {Block.signature with data := ToJson.toJson $(quote hls)} #[Block.code $(quote str.getString)])]
      else
        pure #[]
