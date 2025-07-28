/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso
import VersoManual.Basic
import Verso.Code.External
import SubVerso.Examples.Messages

set_option linter.missingDocs true

open Lean
open Lean.Meta.Hint

open Verso Log Doc Elab ArgParse Genre.Manual Code Output Html Highlighted WebAssets
open SubVerso.Highlighting
open SubVerso.Examples.Messages

open Std

open Verso.Code.External

namespace Verso.Genre.Manual

private def hlJsDeps : List JsFile :=
  [{filename := "popper.js", contents := popper}, {filename := "tippy.js", contents := tippy}]

block_extension Block.lean (hls : Highlighted) (cfg : CodeConfig) where
  init st :=
    st.addQuickJumpMapper exampleDomain exampleDomainMapper
  data :=
    let defined := definedNames hls
    Json.arr #[ToJson.toJson cfg, ToJson.toJson hls, ToJson.toJson defined]
  traverse id data _ := do
    let .arr #[cfgJson, _hlJson, definesJson] := data
      | logError s!"Expected array for Lean block, got {data.compress}"; return none
    match FromJson.fromJson? cfgJson with
    | .error err =>
      logError <| "Failed to deserialize code config during traversal:" ++ err
      return none
    | .ok (cfg : CodeConfig) =>
      if cfg.defSite.isEqSome false then return none
      match FromJson.fromJson? definesJson with
      | .error err =>
        logError <| "Failed to deserialize code config during traversal:" ++ err
        return none
      | .ok (defines : Array (Name × String)) =>
        saveExampleDefs id defines
        pure none
  toTeX := none
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := hlJsDeps
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .arr #[cfgJson, hlJson, _definesJson] := data
        | HtmlT.logError "Expected four-element JSON for Lean code"
          pure .empty
      match FromJson.fromJson? hlJson with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        match FromJson.fromJson? cfgJson with
        | .error err =>
          HtmlT.logError <| "Couldn't deserialize Lean code block config while rendering HTML: " ++ err
          pure .empty
        | .ok (cfg : CodeConfig) =>
          let i := hl.indentation
          let hl := hl.deIndent i
          withReader ({ · with codeOptions.inlineProofStates := cfg.showProofStates, codeOptions.definitionsAsTargets := cfg.defSite.getD true }) <|
            hl.blockHtml (g := Manual) "examples"

inline_extension Inline.lean (hls : Highlighted) (cfg : CodeConfig) where
  data :=
    let defined := definedNames hls
    Json.arr #[ToJson.toJson cfg, ToJson.toJson hls, ToJson.toJson defined]
  traverse id data _ := do
    let .arr #[cfgJson, _hlJson, definesJson] := data
      | logError s!"Expected array for Lean block, got {data.compress}"; return none
    match FromJson.fromJson? cfgJson with
    | .error err =>
      logError <| "Failed to deserialize code config during traversal:" ++ err
      return none
    | .ok (cfg : CodeConfig) =>
      unless cfg.defSite.isEqSome true do return none
      match FromJson.fromJson? definesJson with
      | .error err =>
        logError <| "Failed to deserialize code config during traversal:" ++ err
        return none
      | .ok (defines : Array (Name × String)) =>
        saveExampleDefs id defines
        pure none
  toTeX := none
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := hlJsDeps
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      let .arr #[cfgJson, hlJson, _] := data
        | HtmlT.logError "Expected four-element JSON for Lean code"
          pure .empty
      match FromJson.fromJson? hlJson with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        match FromJson.fromJson? cfgJson with
        | .error err =>
          HtmlT.logError <| "Couldn't deserialize Lean code block config while rendering HTML: " ++ err
          pure .empty
        | .ok (cfg : CodeConfig) =>
          let i := hl.indentation
          let hl := hl.deIndent i
          withReader
            ({ · with
              codeOptions.inlineProofStates := cfg.showProofStates, codeOptions.definitionsAsTargets := cfg.defSite.getD false }) <|
            hl.inlineHtml (g := Manual) "examples"

block_extension Block.leanOutput (message : Highlighted.Message) (summarize : Bool := false) where
  data := ToJson.toJson (message, summarize)
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := hlJsDeps
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok ((msg, summarize) : Highlighted.Message × Bool) =>
        msg.blockHtml summarize (g := Manual)


inline_extension Inline.leanOutput (message : Highlighted.Message) (plain : Bool) where
  data := ToJson.toJson (message, plain)
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun go _ _  content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := hlJsDeps
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok ((txt, plain) : Highlighted.Message × Bool) =>
        let plainHtml := {{<code>{{txt.toString}}</code>}}
        if plain then pure plainHtml
        else txt.toHtml (g := Manual)

open Verso.Code.External

instance : ExternalCode Manual where
  leanInline hl cfg := Inline.other (Inline.lean hl cfg) #[]
  leanBlock hl cfg := Block.other (Block.lean hl cfg) #[]
  leanOutputInline message plain := Inline.other (Inline.leanOutput message plain) #[]
  leanOutputBlock message (summarize : Bool := false) :=
    Block.other (Block.leanOutput message (summarize := summarize)) #[]
