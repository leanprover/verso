/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json.Basic
import VersoManual.Basic
import VersoManual.HighlightedCode
import Verso.Code.Highlighted.WebAssets

import SubVerso.Highlighting

open Verso Genre Manual
open Verso Code Highlighted WebAssets
open Verso Doc Output Html
open Lean
open SubVerso.Highlighting

namespace Verso.Genre.Manual.InlineLean

block_extension Block.lean
    (hls : Highlighted) (file : Option System.FilePath := none) (range : Option Lsp.Range := none)
    via withHighlighting where
  init s := s.addQuickJumpMapper exampleDomain exampleDomainMapper
  data :=
    let defined := definedNames hls
    Json.arr #[ToJson.toJson hls, ToJson.toJson defined, ToJson.toJson file, ToJson.toJson range]

  traverse id data _ := do
    let .arr #[_, defined, _, _] := data
      | logError "Expected two-element JSON for Lean code" *> pure none
    match FromJson.fromJson? defined with
    | .error err =>
      logError <| "Couldn't deserialize Lean code while traversing block example: " ++ err
      pure none
    | .ok (defs : Array (Name × String)) =>
      saveExampleDefs id defs
      pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .arr #[hlJson, _ds, _, _] := data
        | HtmlT.logError "Expected four-element JSON for Lean code" *> pure .empty
      match FromJson.fromJson? hlJson with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        --if hl.toString.startsWith "namespace A" then
          -- dbg_trace hl.toString
          -- dbg_trace ds
          -- have : Ord (Name × String) := Ord.lex ⟨fun x y => compare x.toString y.toString⟩ inferInstance
          -- for (x, y) in (← HtmlT.definitionIds).toArray.qsortOrd do
          --   dbg_trace "{x}\t=>\t{y}"
        hl.blockHtml (g := Manual) "examples"
