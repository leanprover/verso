/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json
import Lean.Data.Json.FromToJson

import VersoManual.Basic
import Verso.Doc.ArgParse

open Verso Genre Manual ArgParse
open Verso.Doc.Elab
open Lean (Json ToJson FromJson)

namespace Verso.Genre.Manual

structure TechArgs where
  key : Option String
  normalize : Bool

section
variable [Monad m] [Lean.MonadError m] [MonadLiftT Lean.CoreM m]

def TechArgs.parse  : ArgParse m TechArgs :=
  TechArgs.mk <$> .named `key .string true <*> .flag `normalize true

instance : FromArgs TechArgs m := ⟨TechArgs.parse⟩

end

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
  str := str.replace "‑" "-"
  String.intercalate " " (str.split (fun c => c.isWhitespace || c == '-') |>.filter (!·.isEmpty))


open Lean in
/--
Defines a technical term.

Internally, these definitions are saved according to a key that is derived by stripping formatting
information from the arguments in `args`, and then normalizing the resulting string by:

 1. lowercasing it
 2. replacing trailing `"ies"` with `"y"`
 3. replacing consecutive runs of whitespace and/or hyphens with a single space

Call with `(normalize := false)` to disable normalization, and `(key := some k)` to use `k` instead
of the automatically-derived key.

Uses of `tech` use the same process to derive a key, and the key is matched against the `deftech` table.
-/
@[role]
def deftech : RoleExpanderOf TechArgs
  | {key, normalize}, content => do

    -- Heuristically guess at the string and key (usually works)
    let str := inlineToString (← getEnv) <| mkNullNode content
    let k := key.getD str
    let k := if normalize then normString k else k
    Doc.PointOfInterest.save (← getRef) str
      (detail? := some s!"Def (key {k})")
      (kind := .key)

    let content ← content.mapM elabInline

    `(let content : Array (Doc.Inline Verso.Genre.Manual) := #[$content,*]
      let asString : String := techString (Doc.Inline.concat content)
      let k : String := ($(quote key) : Option String).getD asString
      Doc.Inline.other {Inline.deftech with data := ToJson.toJson (if $(quote normalize) then normString k else k, asString)} content)


/-- Adds an internal identifier as a target for a given glossary entry -/
def Glossary.addEntry [Monad m] [MonadState TraverseState m] [MonadLiftT IO m] [MonadReaderOf TraverseContext m]
    (id : InternalId) (key : String) : m Unit := do
  match (← get).get? glossaryState with
  | none =>
    modify (TraverseState.set · glossaryState <| Lean.Json.mkObj [(key, ToJson.toJson id)])
  | some (.error err) => logError err
  | some (.ok (v : Json)) =>
    modify (TraverseState.set · glossaryState <| v.setObjVal! key (ToJson.toJson id))

open Verso.Search in
def technicalTermDomainMapper : DomainMapper := {
  displayName := "Terminology",
  className := "tech-term-domain",
  dataToSearchables :=
    "(domainData) =>
  Object.entries(domainData.contents).map(([key, value]) => ({
    searchKey: value[0].data.term,
    address: `${value[0].address}#${value[0].id}`,
    domainId: 'Verso.Genre.Manual.doc.tech',
    ref: value,
  }))"
  : DomainMapper }.setFont { family := .text }

@[inline_extension deftech]
def deftech.descr : InlineDescr where
  init st := st
    |>.setDomainTitle technicalTermDomain "Terminology"
    |>.setDomainDescription technicalTermDomain "Definitions of technical terms"
    |>.addQuickJumpMapper technicalTermDomain technicalTermDomainMapper

  traverse id data _contents := do
    -- A round with internal tags is not needed here because users's don't get to pick IDs
    let path ← (·.path) <$> read
    match FromJson.fromJson? data with
    | .error err =>
      logError err
      return none
    | .ok ((key, term) : (String × String) ) =>
      let termSlug := term.sluggify.toString
      let _ ← Verso.Genre.Manual.externalTag id path s!"--tech-term-{termSlug}"
      Glossary.addEntry id key
      modify fun st =>
        st
          |>.saveDomainObject technicalTermDomain key id
          |>.saveDomainObjectData technicalTermDomain key (json%{"term": $term})

      pure none

  toTeX :=
    some <| fun go _id _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Output.Html Doc.Html.HtmlT in
    some <| fun go id inl content => do
      let some link := (← state).externalTags[id]?
        | panic! s!"Untagged index target with data {inl}"
      return {{<span id={{link.htmlId.toString}} class="def-technical-term">{{← content.mapM go}}</span>}}

def Inline.tech : Inline where
  name := `Verso.Genre.Manual.tech

open Lean in
/--
Emits a reference to a technical term defined with `deftech.`

Internally, these terms are found according to a key that is derived by stripping formatting
information from the arguments in `args`, and then normalizing the resulting string by:

 1. lowercasing it
 2. replacing trailing `"ies"` with `"y"`
 3. replacing consecutive runs of whitespace and/or hyphens with a single space

Call with `(normalize := false)` to disable normalization, and `(key := some k)` to use `k` instead
of the automatically-derived key.
-/
@[role]
def tech : RoleExpanderOf TechArgs
  | {key, normalize}, content => do

    -- Heuristically guess at the string and key (usually works)
    let str := inlineToString (← getEnv) <| mkNullNode content
    let k := key.getD str
    let k := if normalize then normString k else k
    Doc.PointOfInterest.save (← getRef) str
      (detail? := some s!"Use (key {k})")
      (kind := .key)

    let filename ← getFileName
    let line := (← getFileMap).utf8PosToLspPos <$> (← getRef).getPos?
    let loc : String := filename ++ (line.map (fun ⟨line, col⟩ => s!":{line}:{col}")).getD ""

    let content ← content.mapM elabInline


    `(let content : Array (Doc.Inline Verso.Genre.Manual) := #[$content,*]
      let k := ($(quote key) : Option String).getD (techString (Doc.Inline.concat content))
      Doc.Inline.other {Inline.tech with data := Json.arr #[Json.str (if $(quote normalize) then normString k else k), Json.str $(quote loc)]} content)


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
      let Json.arr #[.str key, .str loc] := info
        | HtmlT.logError s!"Failed to decode glossary key and location from {info}"
          content.mapM go
      match (← Doc.Html.HtmlT.state).get? glossaryState with
      | none =>
        HtmlT.logError s!"{loc}: No glossary entries defined (looking up {info})"
        content.mapM go
      | some (.error e) => HtmlT.logError e; content.mapM go
      | some (.ok (tech : Json)) =>
        match tech.getObjValD key with
        | .null =>
          HtmlT.logError s!"{loc}: No term def with key \"{key}\""
          content.mapM go
        | v =>
          match FromJson.fromJson? v with
          | .error e => HtmlT.logError e; content.mapM go
          | .ok id =>
            let xref ← Doc.Html.HtmlT.state
            if let some link := xref.externalTags.get? id then
              let addr := link.link
              pure {{<a class="technical-term" href={{addr}}>{{← content.mapM go}}</a>}}
            else
              Doc.Html.HtmlT.logError s!"{loc}: No external tag for {id}"
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
/* Highlight the clicked term */
.def-technical-term:target {
  background-color: var(--verso-selected-color);
  outline: auto;
}
"#
  ]
