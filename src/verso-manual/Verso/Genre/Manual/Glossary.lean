/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json
import Lean.Data.Json.FromToJson

import Verso
import Verso.Genre.Manual.Basic

open Verso Genre Manual
open Verso.Doc.Elab
open Lean (Json ToJson FromJson HashSet)

namespace Verso.Genre.Manual


private def glossaryState := `Verso.Genre.Manual.glossary

def Inline.deftech : Inline where
  name := `Verso.Genre.Manual.deftech

private partial def techString (text : Doc.Inline Manual) : String :=
  match text with
  | .code str | .math _ str | .text str | .linebreak str => str
  | .image .. | .footnote .. => ""
  | .other _ txt
  | .concat txt
  | .bold txt
  | .emph txt
  | .link txt _href => String.join <| txt.toList.map techString

-- Implements the normalization procedure used in Scribble
private partial def normString (term : String) : String := Id.run do
  let mut str := term.toLower
  if str.endsWith "ies" then str := str.dropRight 3 ++ "y"
  if str.endsWith "s" then str := str.dropRight 1
  String.intercalate " " (str.split (fun c => c.isWhitespace || c == '-') |>.filter (!·.isEmpty))

def deftech (args : Array (Doc.Inline Manual))
    (key : Option String := none) (normalize : Bool := true)
    : Doc.Inline Manual :=
  let k := key.getD (techString (.concat args))
  Doc.Inline.other {Inline.deftech with data := if normalize then normString k else k} args

/-- Adds an internal identifier as a target for a given glossary entry -/
def Glossary.addEntry [Monad m] [MonadState TraverseState m] [MonadLiftT IO m] [MonadReaderOf TraverseContext m]
    (id : InternalId) (key : String) : m Unit := do
  match (← get).get? glossaryState with
  | none =>
    modify (TraverseState.set · glossaryState <| Lean.Json.mkObj [(key, ToJson.toJson id)])
  | some (.error err) => logError err
  | some (.ok (v : Json)) =>
    modify (TraverseState.set · glossaryState <| v.setObjVal! key (ToJson.toJson id))

@[inline_extension deftech]
def deftech.descr : InlineDescr where
  traverse id data _contents := do
    -- TODO use internal tags in the first round to respect users' assignments (cf part tag assignment)
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path "--tech"
    match FromJson.fromJson? data with
    | .error err =>
      logError err
      return none
    | .ok (key : String) =>
      Glossary.addEntry id key
      pure none
  toTeX :=
    some <| fun go _id _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun go id inl content => do
      let some (_, t) := (← read).2.2.externalTags.find? id
        | panic! s!"Untagged index target with data {inl}"
      return {{<span id={{t}}>{{← content.mapM go}}</span>}}

def Inline.tech : Inline where
  name := `Verso.Genre.Manual.tech


def tech (args : Array (Doc.Inline Manual))
    (key : Option String := none) (normalize : Bool := true)
    : Doc.Inline Manual :=
  let k := key.getD (techString (.concat args))
  Doc.Inline.other {Inline.tech with data := if normalize then normString k else k} args

@[inline_extension tech]
def tech.descr : InlineDescr where
  traverse _id _data _contents := pure none
  toTeX :=
    some <| fun go _id _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Output.Html in
    open Doc.Html in
    some <| fun go _id info content => do
      let .ok (key : String) := FromJson.fromJson? info
        | HtmlT.logError s!"Failed to decode glossary key from {info}"
          content.mapM go
      match (← Doc.Html.HtmlT.state).get? glossaryState with
      | none =>
        HtmlT.logError s!"No glossary entries defined (looking up {info})"
        content.mapM go
      | some (.error e) => HtmlT.logError e; content.mapM go
      | some (.ok (tech : Json)) =>
        match tech.getObjValD key with
        | .null =>
          HtmlT.logError s!"No term def with key {key}"
          content.mapM go
        | v =>
          match FromJson.fromJson? v with
          | .error e => HtmlT.logError e; content.mapM go
          | .ok id =>
            let xref ← Doc.Html.HtmlT.state
            if let some (path, htmlId) := xref.externalTags.find? id then
              let addr := String.join (path.map ("/" ++ ·) |>.toList)
              pure {{<a class="technical-term" href=s!"{addr}#{htmlId}">{{← content.mapM go}}</a>}}
            else
              Doc.Html.HtmlT.logError s!"No external tag for {id}"
              content.mapM go
  extraCss := [
    r#"
a.technical-term {
  color: inherit;
  text-decoration: currentcolor underline dotted;
}
a.technical-term:hover {
  text-decoration: currentcolor underline solid;
}

"#
  ]
