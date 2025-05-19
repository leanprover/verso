/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json
import Lean.Elab.InfoTree.Types

import Verso.Output.Html
import Verso.Output.TeX
import VersoManual.Basic
import VersoManual.Marginalia


open Lean Elab
open Verso Doc Elab Html
open Verso.Output Html
open Verso.Genre Manual
open Verso.ArgParse


namespace Verso.Genre.Manual.Bibliography

inductive Style where
  | textual
  | parenthetical
  | here
deriving ToJson, FromJson, Repr

inductive Month where
  | january | february | march | april
  | may | june | july | august
  | september | october | november | december
deriving ToJson, FromJson, DecidableEq, Ord, Repr

structure InProceedings where
  title : Doc.Inline Manual
  authors : Array (Doc.Inline Manual)
  year : Int
  booktitle : Doc.Inline Manual
  editors : Option (Array (Doc.Inline Manual)) := none
  series : Option (Doc.Inline Manual) := none
  url : Option String := none
deriving ToJson, FromJson, BEq, Hashable, Ord

structure Thesis where
  title : Doc.Inline Manual
  author : Doc.Inline Manual
  year : Int
  university : Doc.Inline Manual
  degree : Doc.Inline Manual
  url : Option String := none
deriving ToJson, FromJson, BEq, Hashable, Ord

structure ArXiv where
  title : Doc.Inline Manual
  authors : Array (Doc.Inline Manual)
  year : Int
  id : String
deriving ToJson, FromJson, BEq, Hashable, Ord

structure Article where
  title : Doc.Inline Manual
  authors : Array (Doc.Inline Manual)
  journal : Doc.Inline Manual
  year : Int
  month : Option (Doc.Inline Manual)
  volume : Doc.Inline Manual
  number : Doc.Inline Manual
  pages : Option (Nat × Nat) := none
  url : Option String := none
deriving ToJson, FromJson, BEq, Hashable, Ord

inductive Citable where
  | inProceedings : InProceedings → Citable
  | thesis : Thesis → Citable
  | arXiv : ArXiv → Citable
  | article : Article → Citable
deriving ToJson, FromJson, BEq, Hashable, Ord

instance : Coe InProceedings Citable where
  coe := .inProceedings

instance : Coe Thesis Citable where
  coe := .thesis

instance : Coe ArXiv Citable where
  coe := .arXiv

instance : Coe Article Citable where
  coe := .article

def Citable.authors : Citable → Array (Doc.Inline Manual)
  | .inProceedings p | .arXiv p | .article p => p.authors
  | .thesis p => #[p.author]

def Citable.title : Citable → Doc.Inline Manual
  | .inProceedings p | .arXiv p | .thesis p | .article p => p.title

def Citable.year : Citable → Int
  | .inProceedings p | .arXiv p | .thesis p | .article p => p.year

def Citable.url : Citable → Option String
  | .inProceedings p => p.url
  | .thesis p => p.url
  | .arXiv p => some s!"https://arxiv.org/abs/{p.id}"
  | .article p => p.url


private def slugString : Doc.Inline Manual → String
  | .text s | .code s | .math _ s => s
  | .bold i | .emph i | .concat i | .other _ i | .link i _ =>
    i.attach.map (fun ⟨x, _⟩ => slugString x) |>.foldr (init := "") (· ++ ·)
  | .linebreak .. | .image .. | .footnote .. => ""


def Citable.tag (c : Citable) : Slug :=
  c.authors.map (slugString) |>.foldr (init := s!"-{c.year}") (· ++ ·) |> .ofString

def Citable.sortKey (c : Citable) := c.authors.map slugString |>.foldr (init := s!" {c.year}") (· ++ ", " ++ ·)

private def andList (xs : Array Html) : Html :=
  if h : xs.size = 1 then xs[0]
  else if h : xs.size = 2 then xs[0] ++ " and " ++ xs[1]
  else
    open Html in
    (xs.extract 0 (xs.size - 1)).foldr (init := {{" and " {{xs.back!}} }}) (· ++ ", " ++ ·)

partial def Bibliography.lastName (inl : Doc.Inline Manual) : Doc.Inline Manual :=
  let ws := words inl
  if _ : ws.size = 0 then inl
  else if _ : ws.size = 1 then ws[0]
  else Id.run do
    let mut lst := #[ws.back!]
    let mut rest := ws.pop
    while rest.back?.isSome do
      let w := rest.back!
      rest := rest.pop
      if parts.contains w then
        lst := lst.push (.text " ") -- Non-breaking space is important so as to not split names
        lst := lst.push w
        continue
      else
        break
    return .concat lst.reverse

where
  parts : List (Doc.Inline Manual) := ["de", "van", "la"].map .text

  words : Doc.Inline Manual → Array (Doc.Inline Manual)
  | .text str => str.splitOn " " |>.filter (· ≠ "") |>.toArray |>.map (.text)
  | .concat xs => xs.map words |>.foldl (init := #[]) (· ++ ·)
  | .linebreak .. => #[]
  | other => #[other]

def Citable.bibHtml (go : Doc.Inline Genre.Manual → HtmlT Manual (ReaderT ExtensionImpls IO) Html) (c : Citable) : HtmlT Manual (ReaderT ExtensionImpls IO) Html :=   wrap <$> open Html in do
  match c with
  | .inProceedings p =>
    let authors ← andList <$> p.authors.mapM go
    return {{ {{authors}} s!", {p.year}. " {{ link {{"“" {{← go p.title}} "”"}} }} ". In " <em>{{← go p.booktitle}}"."</em>{{(← p.series.mapM go).map ({{" (" {{·}} ")" }}) |>.getD .empty}} }}
  | .article p =>
    let authors ← andList <$> p.authors.mapM go
    return {{ {{authors}} " (" {{(← p.month.mapM go).map (· ++ {{" "}}) |>.getD .empty}}s!"{p.year}" "). " {{ link {{"“" {{← go p.title}} "”"}} }} ". " <em>{{← go p.journal}}"."</em> <strong>{{← go p.volume}}</strong>" "{{← go p.number}} {{p.pages.map (fun (x, y) => s!"pp. {x}–{y}") |>.getD .empty }}  "."}}
  | .thesis p =>
    return {{ {{← go p.author}} s!", {p.year}. " <em>{{link (← go p.title)}}</em> ". " {{← go p.degree}} ", " {{← go p.university}} }}
  | .arXiv p =>
    let authors ← andList <$> p.authors.mapM go
    return {{ {{authors}} s!", {p.year}. " {{ link {{"“" {{← go p.title}} "”"}} }} ". arXiv:" {{p.id}} }}
where
  wrap (content : Html) : Html := {{<span class="citation">{{content}}</span>}}
  link (title : Html) : Html :=
    match c.url with
    | none => title
    | some u => {{<a href={{u}}>{{title}}</a>}}

def Citable.inlineHtml
    (go : Doc.Inline Genre.Manual → HtmlT Manual (ReaderT ExtensionImpls IO) Html)
    (ps : List Citable)
    (fmt : Style) :
    HtmlT Manual (ReaderT ExtensionImpls IO) Html := open Html in do
  match fmt with
  | .textual =>
    let out : Array Html ← ps.toArray.mapM fun p => do
      let m ← p.bibHtml go
      pure <| {{ {{← authorHtml p}} s!" ({p.year})"}} ++ Marginalia.html m
    pure <| andList out
  | .parenthetical =>
    let out : Array Html ← ps.toArray.mapM fun p => do
      let m ← p.bibHtml go
      pure <| {{" (" {{← authorHtml p}} s!", {p.year})"}} ++ Marginalia.html m
    pure <| andList out
  | .here => do
    pure <| andList (← ps.toArray.mapM (·.bibHtml go))
where
  authorHtml p := open Html in do
    if p.authors.size = 0 then
      pure {{""}}
    else if h : p.authors.size = 1 then
      go <| Bibliography.lastName p.authors[0]
    else if h : p.authors.size > 3 then
      (· ++ {{<em>"et al"</em>}}) <$> go (Bibliography.lastName p.authors[0])
    else andList <$> p.authors.mapM (go ∘ Bibliography.lastName)

private def arrayOrd (ord : Ord α) : Ord (Array α) := inferInstance

private partial def cmpCite : Json → Json → Ordering
  | .null, .null => .eq
  | .null, _ => .lt
  | _, .null => .gt
  | .str s1, .str s2 => Ord.compare s1 s2
  | .str _, _ => .lt
  | _, .str _ => .gt
  | .num n1, .num n2 => Ord.compare n1 n2
  | .num _, _ => .lt
  | _, .num _ => .gt
  | .bool b1, .bool b2 => Ord.compare b1 b2
  | .bool _, _ => .lt
  | _, .bool _ => .gt
  | .arr a1, .arr a2 =>
    arrayOrd ⟨cmpCite⟩ |>.compare a1 a2
  | .arr _, _ => .lt
  | _, .arr _ => .gt
  | .obj o1, .obj o2 =>
    let inst1 : Ord String := inferInstance
    let inst2 : Ord Json := ⟨cmpCite⟩
    let inst : Ord (String × Json) := Ord.lex inst1 inst2
    let a1 := o1.toArray.map (fun x => (x.1, x.2)) |>.qsort (inst.compare · · == .lt)
    let a2 := o2.toArray.map (fun x => (x.1, x.2)) |>.qsort (inst.compare · · == .lt)
    (arrayOrd inst).compare a1 a2


inline_extension Inline.cite (citations : List Citable) (style : Style := .parenthetical) where
   -- The nested bit here _should_ be a no-op, but it's to avoid deserialization overhead during the traverse pass
  data := ToJson.toJson (ToJson.toJson citations, style)
  traverse _ data _ := do
    match FromJson.fromJson? data with
    | .error e => logError s!"Failed to deserialize citation: {e}"; return none
    | .ok (v : Json × Style) =>
      let cited : Option (Except String (Array Json)) := (← get).get? `Manual.Bibliography
      match cited with
      | .none =>
        modify (·.set `Manual.Bibliography (Json.arr #[v.1]))
      | .some (.error e) => logError e
      | .some (.ok citedSet) =>
        if citedSet.binSearchContains v.1 (cmpCite · · == .lt) then pure ()
        else modify (·.set `Manual.Bibliography <| citedSet.binInsert (cmpCite · · == .lt) v.1)
      pure none -- TODO disambiguate years
  toTeX := none
  extraCss := [Marginalia.css]
  toHtml :=
    open Verso.Output.Html in
    some <| fun go _ data _content => do -- TODO repurpose "content" for e.g. "page 5"
      match FromJson.fromJson? data with
      | .error e => HtmlT.logError s!"Failed to deserialize citation/style: {e}"; return {{""}}
      | .ok (v : Json × Style) =>
        match FromJson.fromJson? v.1 with
        | .error e => HtmlT.logError s!"Failed to deserialize citation: {e}"; return {{""}}
        | .ok (v' : List Citable) =>
          Citable.inlineHtml go v' v.2

structure CiteConfig where
  citations : List Name

partial def CiteConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m] : ArgParse m CiteConfig :=
  CiteConfig.mk <$> many1 (.positional `citation .resolvedName)
where
  many1 p := (· :: ·) <$> p <*> many p
  many p := (· :: ·) <$> p <*> many p <|> pure []

end Bibliography

export Verso.Genre.Manual.Bibliography (InProceedings Thesis ArXiv Article)

open Bibliography

@[role_expander citep]
def citep : RoleExpander
  | args, extra => do
    let config ← CiteConfig.parse.run args
    let xs := config.citations.map mkIdent |>.toArray
    return #[← ``(Doc.Inline.other (Inline.cite ([$xs,*] : List Citable) Style.parenthetical) #[$(← extra.mapM elabInline),*])]

@[role_expander citet]
def citet : RoleExpander
  | args, extra => do
    let config ← CiteConfig.parse.run args
    let xs := config.citations.map mkIdent |>.toArray
    return #[← ``(Doc.Inline.other (Inline.cite ([$xs,*] : List Citable) Style.textual) #[$(← extra.mapM elabInline),*])]

@[role_expander citehere]
def citehere : RoleExpander
  | args, extra => do
    let config ← CiteConfig.parse.run args
    let xs := config.citations.map mkIdent |>.toArray
    return #[← ``(Doc.Inline.other (Inline.cite ([$xs,*] : List Citable) Style.here) #[$(← extra.mapM elabInline),*])]
