/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso
import VersoManual.Basic
import SubVerso.Examples.Messages

set_option linter.missingDocs true

open Lean
open Lean.Meta.Hint

open Verso Log Doc Elab ArgParse Genre.Manual Code Output Html Highlighted WebAssets
open SubVerso.Highlighting
open SubVerso.Examples.Messages

open Std

namespace Verso.Genre.Manual

block_extension Block.lean (hls : Highlighted) where
  data :=
    let defined := hls.definedNames.toArray
    Json.arr #[ToJson.toJson hls, ToJson.toJson defined]
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .arr #[hlJson, _] := data
        | HtmlT.logError "Expected four-element JSON for Lean code"
          pure .empty
      match FromJson.fromJson? hlJson with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        let i := hl.indentation
        let hl := hl.deIndent i
        hl.blockHtml "examples"

inline_extension Inline.lean (hls : Highlighted) where
  data :=
    let defined := hls.definedNames.toArray
    Json.arr #[ToJson.toJson hls, ToJson.toJson defined]
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      let .arr #[hlJson, _] := data
        | HtmlT.logError "Expected four-element JSON for Lean code"
          pure .empty
      match FromJson.fromJson? hlJson with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        let i := hl.indentation
        let hl := hl.deIndent i
        hl.inlineHtml "examples"

block_extension Block.leanOutput (severity : MessageSeverity) (message : String) (summarize : Bool := false) where
  data := ToJson.toJson (severity, message, summarize)
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
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok ((sev, txt, summarize) : MessageSeverity × String × Bool) =>
        let wrap html :=
          if summarize then {{<details><summary>"Expand..."</summary>{{html}}</details>}}
          else html
        pure <| wrap {{<div class={{sev.class}}><pre>{{txt}}</pre></div>}}

inline_extension Inline.leanOutput (severity : MessageSeverity) (message : String) (plain : Bool) where
  data := ToJson.toJson (severity, message, plain)
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun go _ _  content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok ((sev, txt, plain) : MessageSeverity × String × Bool) =>
        let plainHtml := {{<code>{{txt}}</code>}}
        if plain then pure plainHtml
        else pure {{<span class={{sev.class}}>{{plainHtml}}</span>}}

open Verso.Code.External

instance : ExternalCode Manual where
  leanInline hl := Inline.other (Inline.lean hl) #[]
  leanBlock hl := Block.other (Block.lean hl) #[]
  leanOutputInline severity message plain := Inline.other (Inline.leanOutput severity message plain) #[]
  leanOutputBlock severity message (summarize : Bool := false) :=
    Block.other (Block.leanOutput severity message (summarize := summarize)) #[]
