/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean

import SubVerso.Highlighting

import Verso.Doc
import Verso.Doc.Html
import Verso.Genre.Blog.Basic
import Verso.Genre.Blog.Site
import Verso.Output.Html
import Verso.Code

open Lean (RBMap)

open Verso Doc Output Html
open Verso.Genre Blog
open SubVerso.Highlighting

private def next (xs : Array α) : Option (α × Array α) :=
  if _ : 0 < xs.size then
    some (xs[0], xs.extract 1 xs.size)
  else
    none

instance [Monad m] : MonadPath (HtmlT Post m) where
  currentPath := do
    let (_, ctxt, _) ← read
    pure ctxt.path

instance [Monad m] : MonadPath (HtmlT Page m) where
  currentPath := do
    let (_, ctxt, _) ← read
    pure ctxt.path

instance [Monad m] : MonadConfig (HtmlT Post m) where
  currentConfig := do
    let (_, ctxt, _) ← read
    pure ctxt.config

instance [Monad m] : MonadConfig (HtmlT Page m) where
  currentConfig := do
    let (_, ctxt, _) ← read
    pure ctxt.config

open HtmlT

defmethod LexedText.toHtml (text : LexedText) : Html :=
  text.content.map fun
    | (none, txt) => (txt : Html)
    | (some cls, txt) => {{ <span class={{cls}}>{{txt}}</span>}}

def blockHtml (g : Genre) (_goI : Inline g → HtmlT g IO Html) (goB : Block g → HtmlT g IO Html) : Blog.BlockExt → Array (Block g) → HtmlT g IO Html
  | .lexedText content, _contents => do
    pure {{ <pre class=s!"lexed {content.name}"> {{ content.toHtml }} </pre> }}
  | .highlightedCode contextName hls, _contents => pure <| hls.blockHtml (toString contextName)
  | .htmlDetails classes summary, contents => do
    pure {{ <details class={{classes}}><summary>{{summary}}</summary> {{← contents.mapM goB}}</details>}}
  | .htmlWrapper name attrs, contents => do
    Html.tag name attrs <$> contents.mapM goB
  | .htmlDiv classes, contents => do
    pure {{ <div class={{classes}}> {{← contents.mapM goB}} </div> }}
  | .blob html, _ => pure html

def inlineHtml (g : Genre) [MonadConfig (HtmlT g IO)] [MonadPath (HtmlT g IO)]
    (stateEq : g.TraverseState = Blog.TraverseState)
    (go : Inline g → HtmlT g IO Html) : Blog.InlineExt → Array (Inline g) → HtmlT g IO Html
  | .highlightedCode contextName hls, _contents => pure <| hls.inlineHtml (some <| toString contextName)
  | .customHighlight hls, _contents => pure <| hls.inlineHtml none
  | .label x, contents => do
    let contentHtml ← contents.mapM go
    let st ← stateEq ▸ state
    let some tgt := st.targets.find? x
      | panic! "No label for {x}"
    pure {{ <span id={{tgt.htmlId}}> {{ contentHtml }} </span>}}
  | .ref x, contents => do
    let st ← stateEq ▸ state
    match st.targets.find? x with
    | none =>
      HtmlT.logError "Can't find target {x}"
      pure {{<strong class="internal-error">s!"Can't find target {x}"</strong>}}
    | some tgt =>
      let addr := s!"{String.join ((← relative tgt.path).intersperse "/")}#{tgt.htmlId}"
      go <| .link contents addr
  | .pageref x, contents => do
    let st ← stateEq ▸ state
    match st.pageIds.find? x with
    | none =>
      HtmlT.logError "Can't find target {x}"
      pure {{<strong class="internal-error">s!"Can't find target {x}"</strong>}}
    | some meta =>
      let addr := String.join ((← relative meta.path).intersperse "/")
      go <| .link contents addr
  | .htmlSpan classes, contents => do
    pure {{ <span class={{classes}}> {{← contents.mapM go}} </span> }}
  | .blob html, _ => pure html

def blogGenreHtml (g : Genre) [MonadConfig (HtmlT g IO)] [MonadPath (HtmlT g IO)]
    (eq1 : g.Block = Blog.BlockExt) (eq2 : g.Inline = Blog.InlineExt) (eq3 : g.TraverseState = Blog.TraverseState)
    (partMeta : (Part g → Array (String × String) → HtmlT g IO Html) → g.PartMetadata → Part g → HtmlT g IO Html) : GenreHtml g IO where
  part f m := partMeta f m
  block := eq1 ▸ blockHtml g
  inline := eq2 ▸ inlineHtml g eq3

instance : GenreHtml Page IO := blogGenreHtml Page rfl rfl rfl fun go _metadata part => go part #[]
instance : GenreHtml Post IO := blogGenreHtml Post rfl rfl rfl fun go _metadata part => go part #[]

namespace Verso.Genre.Blog.Template

structure Params.Val where
  value : Dynamic
  fallback : Array Dynamic

namespace Params.Val

def get? [TypeName α] (value : Val) : Option α :=
  value.value.get? α <|> do
    for v in value.fallback do
      if let some x := v.get? α then return x
    none

def getD [TypeName α] (value : Val) (default : α) : α :=
  value.get? |>.getD default

end Params.Val

deriving instance TypeName for String


instance : Coe String Template.Params.Val where
  coe str := ⟨.mk str, #[.mk <| Html.text true str]⟩

instance : Coe Html Template.Params.Val where
  coe
   | .text true str => ↑str
   | other => ⟨.mk other, #[]⟩


def Params := RBMap String Params.Val compare

instance : EmptyCollection Params := inferInstanceAs <| EmptyCollection (RBMap _ _ _)

namespace Params

def ofList (params : List (String × Val)) : Params :=
  Lean.RBMap.ofList params

def toList (params : Params) : List (String × Val) :=
  Lean.RBMap.toList params

def insert (params : Params) (key : String) (val : Val) : Params :=
  Lean.RBMap.insert params key val

def erase (params : Params) (key : String) : Params :=
  Lean.RBMap.erase params key


end Params

inductive Error where
  | missingParam (param : String)
  | wrongParamType (param : String) (type : Lean.Name)

structure Context where
  site : Site
  config : Config
  path : List String
  params : Params
  builtInStyles : Lean.HashSet String
  builtInScripts : Lean.HashSet String

end Template

abbrev TemplateM (α : Type) : Type := ReaderT Template.Context (Except Template.Error) α

abbrev Template := TemplateM Html

instance : MonadPath TemplateM where
  currentPath := Template.Context.path <$> read

instance : MonadConfig TemplateM where
  currentConfig := Template.Context.config <$> read

namespace Template

def param? [TypeName α] (key : String) : TemplateM (Option α) := do
  match (← read).params.find? key with
  | none => return none
  | some val =>
    if let some v := val.get? (α := α) then return (some v)
    else throw <| .wrongParamType key (TypeName.typeName α)


def param [TypeName α] (key : String) : TemplateM α := do
  match (← read).params.find? key with
  | none => throw <| .missingParam key
  | some val =>
    if let some v := val.get? (α := α) then return v
    else throw <| .wrongParamType key (TypeName.typeName α)

def builtinHeader : TemplateM Html := do
  let mut out := .empty
  for style in (← read).builtInStyles do
    out := out ++ {{<style>"\n"{{.text false style}}"\n"</style>"\n"}}
  for script in (← read).builtInScripts do
    out := out ++ {{<script>"\n"{{.text false script}}"\n"</script>"\n"}}
  out := out ++ {{
    <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.css" integrity="sha384-n8MVd4RsNIU0tAv4ct0nTaAbDJwPJzDEaqSD1odI+WdtXRGWt2kTvGFasHpSy3SV" crossorigin="anonymous"/>
    <script defer="defer" src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.js" integrity="sha384-XjKyOOlGwcjNTAIQHIpgOno0Hl1YQqzUOEleOLALmuqehneUG+vnGctmUb0ZY0l8" crossorigin="anonymous"></script>
    <script src="https://cdn.jsdelivr.net/npm/marked@11.1.1/marked.min.js" integrity="sha384-zbcZAIxlvJtNE3Dp5nxLXdXtXyxwOdnILY1TDPVmKFhl4r4nSUG1r8bcFXGVa4Te" crossorigin="anonymous"></script>
  }}

  pure out

namespace Params

end Params
