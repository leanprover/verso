/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json.Basic
import VersoManual.Basic
import Verso.Code.Highlighted.WebAssets

import SubVerso.Highlighting

open Verso Genre Manual
open Verso Code Highlighted WebAssets
open Verso Doc Output Html
open Lean
open SubVerso.Highlighting

namespace Verso.Genre.Manual.InlineLean

block_extension Block.lean (hls : Highlighted) (file : Option System.FilePath := none) (range : Option Lsp.Range := none) where
  data :=
    let defined := hls.definedNames.toArray
    Json.arr #[ToJson.toJson hls, ToJson.toJson defined, ToJson.toJson file, ToJson.toJson range]
  traverse id data _ := do
    let .arr #[_, defined, _, _] := data
      | logError "Expected two-element JSON for Lean code" *> pure none
    match FromJson.fromJson? defined with
    | .error err =>
      logError <| "Couldn't deserialize Lean code while traversing block example: " ++ err
      pure none
    | .ok (defs : Array Name) =>
      let path ← (·.path) <$> read
      for n in defs do
        let _ ← externalTag id path n.toString
        modify (·.saveDomainObject exampleDomain n.toString id)
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
      let .arr #[hlJson, _, _, _] := data
        | HtmlT.logError "Expected four-element JSON for Lean code" *> pure .empty
      match FromJson.fromJson? hlJson with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.blockHtml "examples"
