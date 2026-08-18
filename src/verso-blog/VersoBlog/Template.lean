/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Std.Data.HashSet

public import SubVerso.Highlighting

public import Verso.Doc
public import Verso.Doc.Html
public import VersoBlog.Basic
public import VersoBlog.Site
public import VersoBlog.Component
public import Verso.Output.Html
public import Verso.Output.Html.CssVars
public import Verso.Output.Html.Files
public import Verso.Output.Html.KaTeX
public import Verso.Code
public import Verso.Instances
public import Verso.Doc.DocName

public section

open Std (HashSet TreeMap)

open Verso Doc Output Html HtmlT
open Verso.Output.Html.Files
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


@[expose] def Params := TreeMap String Params.Val

instance : EmptyCollection Params := inferInstanceAs <| EmptyCollection (TreeMap _ _ _)

instance : Append Params where
  append xs ys := ys.foldl (init := xs) fun params k v => params.insert k v

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

/-- The contents of a file that should be emitted with a page. -/
inductive AssetContents where
  /-- A text file. -/
  | text (contents : String)
  /-- A binary file. -/
  | binary (contents : ByteArray)

/--
The files that a page's `<head>` needs beyond `builtinAssets`.

Stylesheets are in cascade order and scripts are in load order, so neither is ever sorted by name.
-/
structure HeadAssets where
  /-- The stylesheets. -/
  css : Array CssFile := #[]
  /-- The scripts. -/
  js : Array JsFile := #[]

instance : Append HeadAssets where
  append x y := { css := x.css ++ y.css, js := x.js ++ y.js }

instance : EmptyCollection HeadAssets := ⟨{}⟩

/--
Names assets that carry no name of their own by a hash of their contents, and puts them in the order
of that hash, so that adding one leaves the order of the others unchanged.
-/
def hashNames (kind : String) (extension : String) (contents : HashSet String) :
    Array (String × String) :=
  contents.toArray.map (fun c => (s!"{kind}-{c.hash}{extension}", c)) |>.qsort (·.1 < ·.1)

@[inherit_doc hashNames]
def hashNamedCss (kind : String) (contents : HashSet String) : Array CssFile :=
  (hashNames kind ".css" contents).map fun (filename, contents) => {filename, contents := ⟨contents⟩}

@[inherit_doc hashNames]
def hashNamedJs (kind : String) (contents : HashSet String) : Array JsFile :=
  (hashNames kind ".js" contents).map fun (filename, contents) =>
    {filename, contents := ⟨contents⟩, sourceMap? := none}

/--
The stylesheets and scripts that a mounted directory of rendered HTML content contributes to one
page.

The paths are already resolved against the mount point, and `builtinHeader` places them, so a theme
that calls it needs nothing more. They are empty on a page that mounts nothing.
-/
structure MountedAssets where
  /--
  The mounted stylesheets that define `--verso-*` custom properties.

  The header emits these ahead of its own definitions and everything after them, so that the site's
  values win for every property it defines and the content's values stand for the rest.
  -/
  variableStyles : Array String := #[]
  /-- The mounted stylesheets that style the content's markup. -/
  contentStyles : Array String := #[]
  /-- The mounted scripts, with their `defer` flags. -/
  scripts : Array (String × Bool) := #[]
deriving Inhabited

structure Context where
  site : Site
  config : Config
  path : Multi.Path
  params : Params
  /--
  The files that the page's `<head>` needs, given the components that have been rendered so far.
  -/
  headAssets : Component.State → HeadAssets
  /-- What the directories mounted on this page contribute to its `<head>`. -/
  mounted : MountedAssets := {}
  components : Components

/--
The parameter keys used while rendering a template.
-/
structure RenderTrace where
  /-- The parameter keys that were used. -/
  params : HashSet String := {}
deriving Inhabited

instance : Append RenderTrace where
  append x y := { params := x.params ∪ y.params }

end Template

abbrev TemplateT (m : Type → Type) (α : Type) : Type :=
  ReaderT Template.Context (StateT Template.RenderTrace (StateT Component.State m)) α

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
      reportError s!"No component implementation found for block '{name}' in {(← readThe Components).blocks.toList.map (·.fst)}"
      pure .empty
    | some dyn =>
      let some {toHtml := impl, ..} := dyn.get? BlockComponent
        | reportError s!"Wrong type for block components: {dyn.typeName}"; pure .empty
      let id ← modifyGetThe Component.State fun s => s.freshId
      impl ⟨id⟩ json
        (fun x => goI (x.cast bg.inline_eq.symm) |>.cast)
        (fun x => goB (x.cast bg.inline_eq.symm bg.block_eq.symm) |>.cast)
        (contents.map (·.cast bg.inline_eq bg.block_eq)) |>.cast (by simp [Page, *]) (by simp [Page, *])
  | .docstring indent declName?, contents => do
    return {{
      <div class="docstring" {{declName?.map ("data-docstring-for", ·.toString) |>.toArray}} style=s!"--indent: {indent}">
        {{← contents.mapM goB}}
      </div>
    }}
  | .docstringSection lvl, contents => do
    if lvl > 5 then
      reportError s!"Docstring header level {lvl + 1} is greater than the allowed HTML nesting of `<h6>`"
    if let some (Block.para first) := contents[0]? then
      let contents := contents.extract 1
      return {{
        <section>
          {{ .tag s!"h{lvl + 1}" #[] (← first.mapM goI) }}
          {{ ← contents.mapM goB }}
        </section>
      }}
    else
      reportError "Internal error: docstring section missing leading paragraph as title"
      contents.mapM goB


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
    pure {{ <span id={{tgt.htmlId.toString}}> {{ contentHtml }} </span>}}
  | .ref x, contents => do
    let st ← bg.state_eq ▸ state
    match st.targets.find? x with
    | none =>
      reportError s!"Can't find target {x}"
      pure {{<strong class="internal-error">s!"Can't find target {x}"</strong>}}
    | some tgt =>
      let addr := tgt.relativeLink
      go <| .link contents addr
  | .pageref x id?, contents => do
    let st ← bg.state_eq ▸ state
    match st.pageIds.find? x <|> st.pageIds.find? (docName x) with
    | none =>
      reportError s!"Can't find target {x} - options are {st.pageIds.toList.map (·.fst)}"
      pure {{<strong class="internal-error">s!"Can't find target {x}"</strong>}}
    | some «meta» =>
      let addr := meta.path.relativeLink ++ (id?.map ("#" ++ ·) |>.getD "")
      go <| .link contents addr
  | .htmlSpan classes, contents => do
    pure {{ <span class={{classes}}> {{← contents.mapM go}} </span> }}
  | .blob html, _ => pure html
  | .component name json, contents => do
    let ⟨_, _, _, _⟩ := bg
    match (← readThe Components).inlines.find? name with
    | none =>
      reportError s!"No component implementation found for inline '{name}' in {(← readThe Components).inlines.toList.map (·.fst)}"
      pure .empty
    | some dyn =>
      let some {toHtml := impl, ..} := dyn.get? InlineComponent
        | reportError s!"Wrong type for block components: {dyn.typeName}"; pure .empty
      let id ← modifyGetThe Component.State fun s => s.freshId
      impl ⟨id⟩ json
        (fun x => go (x.cast bg.inline_eq.symm) |>.cast)
        (contents.map (·.cast bg.inline_eq)) |>.cast bg.context_eq.symm bg.state_eq.symm


open Verso.Genre.Blog (TemplateT)

@[implicit_reducible]
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


def mkHd (htmlId : Option String) (lvl : Nat) (contents : Html)  : Html :=
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

def addTrace [MonadStateOf RenderTrace m] (key : String) : m Unit :=
  modifyThe RenderTrace fun trace => { trace with params := trace.params.insert key }
/--
Returns the value of the given template, if it exists.
If it exists but has the wrong type, an exception is thrown.
-/
def param? [TypeName α] (key : String) : TemplateM (Option α) := do
  addTrace key
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
  addTrace key
  match (← read).params.get? key with
  | none => throw <| .missingParam key
  | some val =>
    if let some v := val.get? (α := α) then return v
    else throw <| .wrongParamType key (TypeName.typeName α)

open Verso.Code.Highlighted.WebAssets in
/--
The files that `builtinHeader` references, relative to the data directory.

Everything that a page needs is served by the site itself, so a page depends on nothing on the
network.
-/
def builtinAssets (selector : String) : Array (String × AssetContents) :=
  #[("verso-vars.css", AssetContents.text «verso-vars.css»),
    ("katex/katex.css", .text katex.css),
    ("katex/katex.js", .text katex.js),
    ("marked.js", .text marked),
    ("marked.umd.min.js.map", .text marked.map),
    ("math.js", .text (mathJs selector))] ++
  katexFonts.map (fun (name, contents) => (name, .binary contents))

/--
Writes a file that a site's pages reference into the site's data directory.
-/
def writeAsset (root : System.FilePath) (name : String) (contents : AssetContents) : IO Unit := do
  let path := root / dataDirName / name
  path.parent.forM IO.FS.createDirAll
  match contents with
  | .text txt => IO.FS.writeFile path txt
  | .binary bytes => IO.FS.writeBinFile path bytes

/--
Writes the files that `builtinHeader` references into a site's data directory.
-/
def writeBuiltinAssets (root : System.FilePath)
    (selector : String) : IO Unit := do
  for (name, contents) in builtinAssets selector do
    writeAsset root name contents

/--
Writes the files that a page's `<head>` references into a site's data directory.
-/
def writeHeadAssets (root : System.FilePath) (assets : HeadAssets) : IO Unit := do
  for css in assets.css do
    writeAsset root css.filename (.text css.contents.css)
  for js in assets.js do
    writeAsset root js.filename (.text js.contents.js)
    if let some sourceMap := js.sourceMap? then
      writeAsset root sourceMap.filename (.text sourceMap.contents)

/--
Contains the contents of `<head>` that are needed for proper functioning of the site.

A theme invokes this before defining its own custom properties, so that its definitions override the
ones that the content ships with.
-/
def builtinHeader : TemplateM Html := do
  let siteRoot := String.join ((← currentPath).toList.map fun _ => "../") ++ "./"
  let assets := (← read).headAssets (← getThe Component.State)
  let mut out := .empty
  let mounted := (← read).mounted
  -- Establish that all relative paths should be relative to siteRoot
  out := out ++ {{<base href={{siteRoot}}/>}}
  -- The custom properties come first so that later stylesheets can easily override them. A mount's
  -- own definitions come first of all, so the site's values win for every property it defines and
  -- the mount's values stand for the rest.
  for css in mounted.variableStyles do
    out := out ++ {{<link rel="stylesheet" href={{css}}/>}}
  out := out ++ {{<link rel="stylesheet" href=s!"{dataDirName}/verso-vars.css"/>}}
  out := out ++ {{<link rel="stylesheet" href=s!"{dataDirName}/katex/katex.css"/>}}
  for css in assets.css do
    out := out ++ {{<link rel="stylesheet" href=s!"{dataDirName}/{css.filename}"/>}}
  out := out ++ {{<script defer="defer" src=s!"{dataDirName}/katex/katex.js"></script>}}
  out := out ++ {{<script src=s!"{dataDirName}/marked.js"></script>}}
  out := out ++ {{<script src=s!"{dataDirName}/math.js"></script>}}
  for css in mounted.contentStyles do
    out := out ++ {{<link rel="stylesheet" href={{css}}/>}}
  for js in assets.js do
    if js.defer then
      out := out ++ {{<script defer="defer" src=s!"{dataDirName}/{js.filename}"></script>}}
    else
      out := out ++ {{<script src=s!"{dataDirName}/{js.filename}"></script>}}
  for (js, defer) in mounted.scripts do
    if defer then
      out := out ++ {{<script defer="defer" src={{js}}></script>}}
    else
      out := out ++ {{<script src={{js}}></script>}}
  pure out


namespace Params

end Params
