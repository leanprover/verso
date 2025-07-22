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

open Verso.Search in
/--
Quick jump configuration for definitions in examples
-/
def exampleDomainMapper : DomainMapper := {
  displayName := "Example Definition",
  className := "example-def",
  -- This is a bit of a hack. Examples with repeated names should really get differing canonical
  -- names, but it's unclear what to use for them. Perhaps it should be the concatenated tags of the
  -- containing sections, with a sequence number in case of further duplication? For now, this
  -- fairly complicated mapper does the job. It'd also be good to have a way to show metadata in the
  -- quick-jump box, with different styling.
  dataToSearchables :=
    "(domainData) => {
  const byName = Object.entries(domainData.contents).flatMap(([key, value]) =>
    value.map(v => ({
      context: v.data[`${v.address}#${v.id}`].context,
      name: v.data[`${v.address}#${v.id}`].display,
      address: `${v.address}#${v.id}`
    }))).reduce((acc, obj) => {
      const key = obj.name;
      acc[key] = acc[key] || [];
      acc[key].push(obj);
      return acc;
    }, {})
  return Object.entries(byName).flatMap(([key, value]) => {
    if (value.length === 0) { return []; }
    const firstCtxt = value[0].context;
    let prefixLength = 0;
    for (let i = 0; i < firstCtxt.length; i++) {
      if (value.every(v => i < v.context.length && v.context[i] === firstCtxt[i])) {
        prefixLength++;
      } else break;
    }
    return value.map((v) => ({
      searchKey: v.context.slice(prefixLength).concat(v.name).join(' › '),
      address: v.address,
      domainId: 'Verso.Genre.Manual.example',
      ref: value
    }));
  });
}"
  : DomainMapper}

/--
Extracts all names that are marked as definition sites, with both their occurrence in the source and
the underlying name.
-/
partial def definedNames : Highlighted → Array (Name × String)
  | .token ⟨.const n _ _ true, s⟩ => #[(n, s)]
  | .token _ => #[]
  | .span _ hl | .tactics _ _ _ hl => definedNames hl
  | .seq hls => hls.map definedNames |>.foldl (· ++ ·) #[]
  | .text .. | .point .. | .unparsed .. => #[]

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
        for (d, s) in defines do
          if d.isAnonymous then continue
          let d := d.toString
          let path ← (·.path) <$> read
          let _ ← externalTag id path d
          let context := (← read).headers.map (·.titleString)
          modify (·.saveDomainObject exampleDomain d id)
          if let some link := (← get).externalTags[id]? then
            modify (·.modifyDomainObjectData exampleDomain d fun v =>
              let v := if let .obj _ := v then v else .obj {}
              v.setObjVal! link.link (json%{"context": $context, "display": $s}))
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
            hl.blockHtml "examples"

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
        for (d, s) in defines do
          if d.isAnonymous then continue
          let d := d.toString
          let path ← (·.path) <$> read
          let _ ← externalTag id path d
          let context := (← read).headers.map (·.titleString)
          modify (·.saveDomainObject exampleDomain d id)
          if let some link := (← get).externalTags[id]? then
            modify (·.modifyDomainObjectData exampleDomain d fun v =>
              let v := if let .obj _ := v then v else .obj {}
              v.setObjVal! link.link (json%{"context": $context, "display": $s}))
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
  extraJsFiles := hlJsDeps
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
  extraJsFiles := hlJsDeps
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
  leanInline hl cfg := Inline.other (Inline.lean hl cfg) #[]
  leanBlock hl cfg := Block.other (Block.lean hl cfg) #[]
  leanOutputInline severity message plain := Inline.other (Inline.leanOutput severity message plain) #[]
  leanOutputBlock severity message (summarize : Bool := false) :=
    Block.other (Block.leanOutput severity message (summarize := summarize)) #[]
