/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Std.Data.HashSet

import SubVerso.Highlighting

import Verso.Doc
import Verso.Doc.Html
import VersoBlog.Basic
import VersoBlog.Site
import VersoBlog.Component
import Verso.Output.Html
import Verso.Output.Html.CssVars
import Verso.Code

open Std (HashSet TreeMap)

open Verso Doc Output Html HtmlT
open Verso.Genre Blog
open SubVerso.Highlighting

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

instance : Coe String Template.Params.Val where
  coe str := ⟨.mk str, #[.mk <| Html.text true str]⟩

instance : Coe Html Template.Params.Val where
  coe
   | .text true str => ↑str
   | other => ⟨.mk other, #[]⟩


def Params := TreeMap String Params.Val

instance : EmptyCollection Params := inferInstanceAs <| EmptyCollection (TreeMap _ _ _)

inductive Error where
  | missingParam (param : String)
  | wrongParamType (param : String) (type : Lean.Name)

def saveJs [Monad m] [MonadStateOf Component.State m] (js : String) : m Unit := do
  modify fun s => {s with headerJs := s.headerJs.insert js}

def saveCss [Monad m] [MonadStateOf Component.State m] (css : String) : m Unit := do
  modify fun s => {s with headerCss := s.headerCss.insert css}


open Lean Elab Term in
scoped macro "%registered_components" : term => do
  ``(Components.fromLists %registered_block_components %registered_inline_components)

class MonadComponents (m : Type → Type) where
  componentImpls : m Components
  saveJs : String → m Unit
  saveCss : String → m Unit


instance [MonadReaderOf Components m] [MonadStateOf Component.State m] : MonadComponents m where
  componentImpls := read
  saveJs js := modify fun s => { s with headerJs := s.headerJs.insert js }
  saveCss css := modify fun s => { s with headerCss := s.headerCss.insert css }

structure Context where
  site : Site
  config : Config
  path : List String
  params : Params
  builtInStyles : HashSet String
  builtInScripts : HashSet String
  jsFiles : Array String
  cssFiles : Array String
  components : Components

end Template

abbrev TemplateT (m : Type → Type) (α : Type) : Type :=
  ReaderT Template.Context (StateT Component.State m) α

instance [Monad m] : Template.MonadComponents (TemplateT m) where
  componentImpls := do return (← read).components
  saveJs js := modifyThe Component.State fun s => { s with headerJs := s.headerJs.insert js }
  saveCss css := modifyThe Component.State fun s => { s with headerCss := s.headerCss.insert css }

/--
A monad that provides template instantiation via dynamically-typed parameters.
-/
abbrev TemplateM (α : Type) : Type := TemplateT (Except Template.Error) α

end Verso.Genre.Blog

private def next (xs : Array α) : Option (α × Array α) :=
  if _ : 0 < xs.size then
    some (xs[0], xs.extract 1 xs.size)
  else
    none

instance [Monad m] : MonadPath (HtmlT Post m) where
  currentPath := do
    return (← context).path

instance [Monad m] : MonadPath (HtmlT Page m) where
  currentPath := do
    return (← context).path

instance [Monad m] : MonadConfig (HtmlT Post m) where
  currentConfig := do
    return (← context).config

instance [Monad m] : MonadConfig (HtmlT Page m) where
  currentConfig := do
    return (← context).config

open HtmlT

defmethod LexedText.toHtml (text : LexedText) : Html :=
  text.content.map fun
    | (none, txt) => (txt : Html)
    | (some cls, txt) => {{ <span class={{cls}}>{{txt}}</span>}}

instance [Pure m] : MonadLift Id m where
  monadLift x := pure x

def blockHtml (g : Genre)
    [bg : BlogGenre g]
    (goI : Inline g → HtmlM g Html)
    (goB : Block g → HtmlM g Html) :
    Blog.BlockExt → Array (Block g) → HtmlM g Html
  | .lexedText content, _contents => do
    pure {{ <pre class=s!"lexed {content.name}"> {{ content.toHtml }} </pre> }}
  | .highlightedCode { contextName, showProofStates } hls, _contents =>
    withReader (fun ρ => { ρ with codeOptions.inlineProofStates := showProofStates }) <|
    hls.blockHtml (toString contextName) (g := g)
  | .message summarize msg expandTraces, _contents => do
    return {{<pre class=s!"lean-output hl lean {msg.severity.class}">{{← msg.toHtml (expandTraces := expandTraces) (g := g)}}</pre>}}
  | .htmlDetails classes summary, contents => do
    pure {{ <details class={{classes}}><summary>{{summary}}</summary> {{← contents.mapM goB}}</details>}}
  | .htmlWrapper name attrs, contents => do
    Html.tag name attrs <$> contents.mapM goB
  | .htmlDiv classes, contents => do
    pure {{ <div class={{classes}}> {{← contents.mapM goB}} </div> }}
  | .blob html, _ => pure html
  | .component name json, contents => do
    let ⟨_, _, _, _⟩ := bg
    match (← readThe Components).blocks.find? name with
    | none =>
      HtmlT.logError s!"No component implementation found for '{name}' in {(← readThe Components).blocks.toList.map (·.fst)}"
      pure .empty
    | some dyn =>
      let some {toHtml := impl, ..} := dyn.get? BlockComponent
        | HtmlT.logError s!"Wrong type for block components: {dyn.typeName}"; pure .empty
      let id ← modifyGetThe Component.State fun s => s.freshId
      impl ⟨id⟩ json
        (fun x => goI (x.cast bg.inline_eq.symm) |>.cast)
        (fun x => goB (x.cast bg.inline_eq.symm bg.block_eq.symm) |>.cast)
        (contents.map (·.cast bg.inline_eq bg.block_eq)) |>.cast (by simp [Page, *]) (by simp [Page, *])

def inlineHtml (g : Genre) [bg : BlogGenre g]
    [MonadConfig (HtmlM g)] [MonadPath (HtmlM g)]
    (go : Inline g → HtmlM g Html) :
    Blog.InlineExt → Array (Inline g) → HtmlM g Html
  | .highlightedCode { contextName, showProofStates } hls, _contents =>
    withReader (fun ρ => { ρ with codeOptions.inlineProofStates := showProofStates }) <|
    hls.inlineHtml (some <| toString contextName) (g := g)
  | .message msg expandTraces, _contents => do
    return {{<code class="lean-output hl lean">{{← msg.toHtml expandTraces (g := g)}}</code>}}
  | .lexedText content, _contents => do
    pure {{ <code class=s!"lexed {content.name}"> {{ content.toHtml }} </code> }}
  | .customHighlight hls, _contents => do
    hls.inlineHtml none (g := g)
  | .label x, contents => do
    let contentHtml ← contents.mapM go
    let st ← bg.state_eq ▸ state
    let some tgt := st.targets.find? x
      | panic! "No label for {x}"
    pure {{ <span id={{tgt.htmlId}}> {{ contentHtml }} </span>}}
  | .ref x, contents => do
    let st ← bg.state_eq ▸ state
    match st.targets.find? x with
    | none =>
      HtmlT.logError s!"Can't find target {x}"
      pure {{<strong class="internal-error">s!"Can't find target {x}"</strong>}}
    | some tgt =>
      let addr := s!"{String.join ((← relative tgt.path).intersperse "/")}#{tgt.htmlId}"
      go <| .link contents addr
  | .pageref x id?, contents => do
    let st ← bg.state_eq ▸ state
    match st.pageIds.find? x <|> st.pageIds.find? (docName x) with
    | none =>
      HtmlT.logError s!"Can't find target {x} - options are {st.pageIds.toList.map (·.fst)}"
      pure {{<strong class="internal-error">s!"Can't find target {x}"</strong>}}
    | some «meta» =>
      let addr := String.join ((← relative meta.path).intersperse "/") ++ (id?.map ("#" ++ ·) |>.getD "")
      go <| .link contents addr
  | .htmlSpan classes, contents => do
    pure {{ <span class={{classes}}> {{← contents.mapM go}} </span> }}
  | .blob html, _ => pure html
  | .component name json, contents => do
    let ⟨_, _, _, _⟩ := bg
    match (← readThe Components).inlines.find? name with
    | none =>
      HtmlT.logError s!"No component implementation found for '{name}' in {(← readThe Components).inlines.toList.map (·.fst)}"
      pure .empty
    | some dyn =>
      let some {toHtml := impl, ..} := dyn.get? InlineComponent
        | HtmlT.logError s!"Wrong type for block components: {dyn.typeName}"; pure .empty
      let id ← modifyGetThe Component.State fun s => s.freshId
      impl ⟨id⟩ json
        (fun x => go (x.cast bg.inline_eq.symm) |>.cast)
        (contents.map (·.cast bg.inline_eq)) |>.cast bg.context_eq.symm bg.state_eq.symm


open Verso.Genre.Blog (TemplateT)

def blogGenreHtml
    (g : Genre) [bg : BlogGenre g]
    [MonadConfig (HtmlM g)] [MonadPath (HtmlM g)]
    (partMeta :
      (Part g → (mkHeader : Nat → Html → Html := mkPartHeader) →
        HtmlM g Html) →
      g.PartMetadata → Part g →
      HtmlM g Html) :
    GenreHtml g ComponentM where
  part f := partMeta (fun p mkHd => f p mkHd)
  block := bg.block_eq ▸ blockHtml g
  inline := bg.inline_eq ▸ inlineHtml g


private def mkHd (htmlId : Option String) (lvl : Nat) (contents : Html)  : Html :=
  mkPartHeader lvl contents (htmlId.map (fun x => #[("id", x)]) |>.getD #[])

instance : GenreHtml Page ComponentM := blogGenreHtml Page fun go metadata part =>
   go part (mkHd metadata.htmlId)

instance : GenreHtml Post ComponentM := blogGenreHtml Post fun go metadata part =>
   go part (mkHd metadata.htmlId)

namespace Verso.Genre.Blog.Template

namespace Params

def ofList (params : List (String × Val)) : Params :=
  Std.TreeMap.ofList params _

def toList (params : Params) : List (String × Val) :=
  Std.TreeMap.toList params

def insert (params : Params) (key : String) (val : Val) : Params :=
  Std.TreeMap.insert params key val

def erase (params : Params) (key : String) : Params :=
  Std.TreeMap.erase params key


end Params

end Template


/--
A procedure for producing HTML from parameters. An abbreviation for `TemplateM Html`
-/
abbrev Template := TemplateM Html

instance : MonadPath TemplateM where
  currentPath := Template.Context.path <$> read

instance : MonadConfig TemplateM where
  currentConfig := Template.Context.config <$> read

namespace Template

/--
Returns the value of the given template, if it exists.
If it exists but has the wrong type, an exception is thrown.
-/
def param? [TypeName α] (key : String) : TemplateM (Option α) := do
  let ctx ← readThe Context
  match ctx.params.get? key with
  | none => return none
  | some val =>
    if let some v := val.get? (α := α) then return (some v)
    else throw <| .wrongParamType key (TypeName.typeName α)

/--
Returns the value of the given template, if it exists. If it does not exist or if it exists but has
the wrong type, an exception is thrown.
-/
def param [TypeName α] (key : String) : TemplateM α := do
  match (← read).params.get? key with
  | none => throw <| .missingParam key
  | some val =>
    if let some v := val.get? (α := α) then return v
    else throw <| .wrongParamType key (TypeName.typeName α)

/--
Contains the contents of `<head>` that are needed for proper functioning of the site.
-/
def builtinHeader : TemplateM Html := do
  let siteRoot := String.join ((← currentPath).map fun _ => "../") ++ "./"
  let mut out := .empty
  -- Other scripts need this
  out := out ++ {{<script>s!"var __versoSiteRoot = {siteRoot.quote};"</script>}}
  -- These should come first so later stylesheets can easily override them.
  out := out ++ {{<style>{{«verso-vars.css»}}</style>}}
  for style in (← read).builtInStyles do
    out := out ++ {{<style>"\n"{{.text false style}}"\n"</style>"\n"}}
  for script in (← read).builtInScripts do
    out := out ++ {{<script>"\n"{{.text false script}}"\n"</script>"\n"}}
  for js in (← read).jsFiles do
    out := out ++ {{<script src=s!"/-verso-js/{js}"></script>}}
  for css in (← read).cssFiles do
    out := out ++ {{<link rel="stylesheet" href=s!"/-verso-css/{css}"/>}}
  out := out ++ {{
    <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.css" integrity="sha384-n8MVd4RsNIU0tAv4ct0nTaAbDJwPJzDEaqSD1odI+WdtXRGWt2kTvGFasHpSy3SV" crossorigin="anonymous"/>
    <script defer="defer" src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.js" integrity="sha384-XjKyOOlGwcjNTAIQHIpgOno0Hl1YQqzUOEleOLALmuqehneUG+vnGctmUb0ZY0l8" crossorigin="anonymous"></script>
    <script src="https://cdn.jsdelivr.net/npm/marked@11.1.1/marked.min.js" integrity="sha384-zbcZAIxlvJtNE3Dp5nxLXdXtXyxwOdnILY1TDPVmKFhl4r4nSUG1r8bcFXGVa4Te" crossorigin="anonymous"></script>
  }}

  -- Components
  for style in (← get).headerCss do
    out := out ++ {{<style>"\n"{{.text false style}}"\n"</style>"\n"}}
  for script in (← get).headerJs do
    out := out ++ {{<script>"\n"{{.text false script}}"\n"</script>"\n"}}
  pure out


namespace Params

end Params
