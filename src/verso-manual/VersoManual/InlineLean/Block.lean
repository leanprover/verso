/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Lean.Data.Json.Basic
public import VersoManual.Basic
public import VersoManual.HighlightedCode
public import Verso.Code.Highlighted.WebAssets
public import Verso.Code.HighlightedToTex

public import SubVerso.Highlighting

public section

open Verso Genre Manual
open Verso Code Highlighted WebAssets
open Verso Doc Output Html
open Lean
open SubVerso.Highlighting

namespace Verso.Genre.Manual.InlineLean

block_extension Block.lean
    (hls : Highlighted) (file : Option System.FilePath := none) (range : Option Lsp.Range := none)
    via withHighlighting where
  metadata := Highlighted × Array (Name × String) × Option System.FilePath × Option Lsp.Range
  decode := fun data =>
    match data with
    | .arr #[hl, defined, file, range] => do
      pure (← FromJson.fromJson? hl, ← FromJson.fromJson? defined, ← FromJson.fromJson? file, ← FromJson.fromJson? range)
    | _ => .error "Expected four-element JSON for Lean code"
  init s := s.addQuickJumpMapper exampleDomain exampleDomainMapper
  data :=
    let defined := definedNames hls
    Json.arr #[ToJson.toJson hls, ToJson.toJson defined, ToJson.toJson file, ToJson.toJson range]

  traverse metadata id _ := do
    let (_, defs, _, _) := metadata
    saveExampleDefs id defs
    pure none
  toTeX :=
    some <| fun (hl, _, _, _) _ _ _ _ => do
      hl.toTeX (g := Manual) (m := ReaderT ExtensionImpls (BuildLogT IO))
  toHtml :=
    open Verso.Output.Html in
    some <| fun (hl, _, _, _) _ _ _ _ => do
      hl.blockHtml (g := Manual) "examples"
