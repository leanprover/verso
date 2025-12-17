/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import MultiVerso
import Verso.Doc
import VersoManual.Basic
import VersoManual
import Lean.Data.Json
import VersoUtil.LzCompress
import VersoUtil.Zip
import VersoBlog.Basic
import VersoBlog.Component
import VersoBlog.Template
import VersoBlog.Generate

namespace Verso.Genre
open Lean

open Verso.Doc (Genre)
open Verso.Multi

private def defaultToolchain := "leanprover/lean4:" ++ Lean.versionString
private def defaultLive := "lean-v" ++ Lean.versionString

inductive ExampleCodeStyle where
  /--
  The example code should be extracted to a Lean project from the tutorial.
  -/
  | inlineLean (moduleName : Lean.Name) (toolchain := defaultToolchain) (liveProject := some defaultLive)
deriving BEq, DecidableEq, Inhabited, Repr, ToJson, FromJson

open Manual (Tag InternalId) in
structure Tutorial.PartMetadata where
  /-- The main tag for the part, used for cross-references. -/
  tag : Option Tag := none
  /-- Use this filename component in the URL. -/
  slug : String
  /-- The internal unique ID, which is automatically assigned during traversal. -/
  id : Option InternalId := none
  /-- A summary to show on the overview page. -/
  summary : String
  /-- How should the code samples in this tutorial be extracted to a downloadable tarball? -/
  exampleStyle : ExampleCodeStyle
deriving BEq, DecidableEq, Inhabited, Repr, ToJson, FromJson

def Tutorial.TraverseContext := Manual.TraverseContext

def Tutorial : Genre :=
  { Manual with
    TraverseContext := Tutorial.TraverseContext
    PartMetadata := Tutorial.PartMetadata
  }

instance : Inhabited (Genre.PartMetadata Tutorial) :=
  inferInstanceAs <| Inhabited Tutorial.PartMetadata
instance : BEq (Genre.PartMetadata Tutorial) := inferInstanceAs (BEq Tutorial.PartMetadata)
instance : BEq (Genre.Block Tutorial) := inferInstanceAs (BEq Manual.Block)
instance : BEq (Genre.Inline Tutorial) := inferInstanceAs (BEq Manual.Inline)

instance : Repr (Genre.PartMetadata Tutorial) := inferInstanceAs (Repr Tutorial.PartMetadata)
instance : Repr (Genre.Block Tutorial) := inferInstanceAs (Repr Manual.Block)
instance : Repr (Genre.Inline Tutorial) := inferInstanceAs (Repr Manual.Inline)

instance : ToJson (Genre.PartMetadata Tutorial) := inferInstanceAs (ToJson Tutorial.PartMetadata)
instance : ToJson (Genre.Block Tutorial) := inferInstanceAs (ToJson Manual.Block)
instance : ToJson (Genre.Inline Tutorial) := inferInstanceAs (ToJson Manual.Inline)

instance : FromJson (Genre.PartMetadata Tutorial) := inferInstanceAs (FromJson Tutorial.PartMetadata)
instance : FromJson (Genre.Block Tutorial) := inferInstanceAs (FromJson Manual.Block)
instance : FromJson (Genre.Inline Tutorial) := inferInstanceAs (FromJson Manual.Inline)

instance : VersoLiterate.LoadLiterate Tutorial where
  inline := inst.inline
  block := inst.block
  docstring := inst.docstring
  docstringPart := inst.docstringPart

where
  inst := inferInstanceAs <| VersoLiterate.LoadLiterate Manual

namespace Tutorial

open Verso.Doc
open Manual (ExtensionImpls)

def defaultMetadata (p : Part Tutorial) : Tutorial.PartMetadata :=
  { slug := p.titleString.sluggify.toString, summary := "", exampleStyle := .inlineLean `Main }


instance : TraversePart Tutorial where
  inPart p ctx :=
    let metadata := p.metadata.getD (defaultMetadata p)
    let properties := if ctx.headers.isEmpty then
      NameMap.insert {} `Verso.Genre.Manual.exampleDefContext metadata.slug
    else
      {}
    let path := if ctx.path.isEmpty then #[metadata.slug] else ctx.path
    { ctx with
      path
      headers := ctx.headers.push {
        titleString := p.titleString, metadata := none, properties
      }
    }

instance : TraverseBlock Tutorial where
  inBlock b := (·.inBlock b)

def savePartXref (slug : Slug) (id : InternalId) (part : Part Tutorial) : Manual.TraverseM Unit := do
  let jsonMetadata :=
    Json.arr (TraversePart.inPart part (← read) |>.headers.map (fun h => json%{
      "title": $h.titleString
    }))
  let title := TraversePart.inPart part (← read) |>.headers |>.back? |>.map (·.titleString)

  modify fun (st : Manual.TraverseState) =>
    st.saveDomainObject Manual.sectionDomain slug.toString id
      |>.saveDomainObjectData Manual.sectionDomain slug.toString (json%{
        "context": $jsonMetadata,
        "title": $title,
        "shortTitle": null,
        "sectionNum": null
      })

block_extension Block.displayOnly where
  traverse _ _ _ _ := pure none
  toHtml := some <| fun _ goB _ _ content => content.mapM goB
  toTeX := some <| fun _ goB _ _ content => content.mapM goB

@[directive]
def displayOnly : Elab.DirectiveExpanderOf Unit
  | (), contents => do
    ``(Block.other Block.displayOnly #[$(← contents.mapM Elab.elabBlock),*])

block_extension Block.codeOnly where
  traverse _ _ _ _ := pure none
  toHtml := some <| fun _ _ _ _ _ => pure .empty
  toTeX := some <| fun _ _ _ _ _ => pure .empty

@[directive]
def codeOnly : Elab.DirectiveExpanderOf Unit
  | (), contents => do
    ``(Block.other Block.codeOnly #[$(← contents.mapM Elab.elabBlock),*])


section
open Verso.Code.External
instance : ExternalCode Tutorial :=
  let inst : ExternalCode Manual := inferInstance
  { inst with }
end

open Manual in
instance : Traverse Tutorial TraverseM where
  part p := do
    if p.metadata.isNone then
      pure (some (defaultMetadata p))
    else pure none
  block _ := pure ()
  inline _ := pure ()
  genrePart startMeta part := do
    let mut «meta» : Tutorial.PartMetadata := startMeta

    -- First, assign a unique ID if there is none
    let id ← if let some i := meta.id then pure i else freshId
    «meta» := { «meta» with id := some id }

    -- Next, assign a tag, prioritizing user-chosen external IDs
    «meta» := { «meta» with tag := ← withReader (TraversePart.inPart part) <| tagPart part «meta» (·.id) (·.tag) savePartXref }

    pure <|
      if «meta» == startMeta then none
      else pure { part with metadata := some «meta» }

  genreBlock := Traverse.genreBlock (g := Manual)
  genreInline := Traverse.genreInline (g := Manual)

structure Topic where
  title : Array (Inline Blog.Page)
  titleString : String
  description : Array (Block Blog.Page)
  tutorials : Array (Part Tutorial)
deriving BEq, ToJson, FromJson

structure Tutorials : Type where
  content : Part Blog.Page
  topics : Array Topic
deriving BEq, ToJson, FromJson

def Tutorials.traverse1  (traversal : Part Tutorial → Manual.TraverseM (Part Tutorial)) (tutorials : Tutorials) : Manual.TraverseM Tutorials := do
  let { content, topics } := tutorials
  return {
    content,
    topics := ← topics.mapM fun topic => do
      return { topic with
        tutorials := ← topic.tutorials.mapM fun tut => do
          let tut := { tut with metadata := tut.metadata.getD (defaultMetadata tut) }
          withReader (TraversePart.inPart tut) <| traversal tut
      }
  }

open Manual in
def traverse (logError : String → IO Unit) (tutorials : Tutorials) (config : Manual.Config) : ReaderT ExtensionImpls IO (Tutorials × Manual.TraverseState) := do
  let topCtxt : Manual.TraverseContext := {logError, draft := config.draft}
  let mut state : Manual.TraverseState := .ofConfig config.toHtmlConfig
  let mut tutorials := tutorials
  if config.verbose then
    IO.println "Initializing extensions"
  let extensionImpls ← readThe ExtensionImpls
  state := state
    |>.setDomainTitle sectionDomain "Sections or chapters of the manual"
    |>.addQuickJumpMapper sectionDomain Manual.sectionDomainMapper
  for ⟨_, b⟩ in extensionImpls.blockDescrs do
    if let some descr := b.get? BlockDescr then
      state := descr.init state
  for ⟨_, i⟩ in extensionImpls.inlineDescrs do
    if let some descr := i.get? InlineDescr then
      state := descr.init state
  for i in [0:config.maxTraversals] do
    if config.verbose then
      IO.println s!"Traversal pass {i}"
    let startTime ← IO.monoMsNow
    let (tutorials', state') ← tutorials.traverse1 (Genre.traverse Tutorial) |>.run extensionImpls topCtxt state

    let endTime ← IO.monoMsNow
    if config.verbose then
      IO.println s!"  ... pass {i} completed in {endTime - startTime} ms"
    if tutorials' == tutorials && state' == state then
      return (tutorials', state')
    else
      state := state'
      tutorials := tutorials'
  return (tutorials, state)

section
open SubVerso Highlighting
open Std

partial def getCode (text : Part Tutorial) : Array (String × String) :=
  if let some metadata := text.metadata then
    StateT.run (go metadata.exampleStyle text) {} |>.2.toArray
  else
    #[]
where
  go (style : ExampleCodeStyle) (p : Part Tutorial) : StateM (HashMap String String) Unit := do
    fromPart style p
    extras style

  extras : ExampleCodeStyle → StateM (HashMap String String) Unit
    | .inlineLean modName toolchain _live => do
      let mut lakeToml := "name = " ++ modName.toString.toLower.quote ++ "\n"
      lakeToml := lakeToml ++ "defaultTargets = [" ++ modName.toString.quote ++ "]\n\n"
      lakeToml := lakeToml ++ "[[lean_lib]]\n"
      lakeToml := lakeToml ++ "name = " ++ modName.toString.quote ++ "\n"
      modify fun s => s.insert "lakefile.toml" lakeToml
      modify fun s => s.insert "lean-toolchain" (withNl toolchain)

  withNl (s : String) := if s.endsWith "\n" then s else s ++ "\n"

  fromPart (style : ExampleCodeStyle) (p : Part Tutorial) : StateM (HashMap String String) Unit := do
    p.content.forM <| fromBlock style
    p.subParts.forM <| fromPart style

  fromBlock (style : ExampleCodeStyle) : Block Tutorial → StateM (HashMap String String) Unit
    | .concat xs | .blockquote xs => xs.forM <| fromBlock style
    | .ol _ items | .ul items => items.forM (·.contents.forM <| fromBlock style)
    | .dl items => items.forM (·.desc.forM <| fromBlock style)
    | .para .. | .code .. => pure ()
    | .other {name, data, ..} contents => do
      if name = ``Manual.InlineLean.Block.lean then
        let .arr #[hl, _, _, _] := data
          | panic! "Malformed metadata"
        codeFromHl style hl
      else if name = ``Manual.Block.lean then
        let .arr #[_, hl, _] := data
          | panic! "Malformed metadata"
        codeFromHl style hl
      else if name = ``Tutorial.Block.displayOnly then
        pure ()
      else
        contents.forM (fromBlock style)

  codeFromHl (style : ExampleCodeStyle) hl : StateM (HashMap String String) Unit := do
    match FromJson.fromJson? hl with
    | .error e => panic! s!"Malformed metadata: {e}"
    | .ok (hl : Highlighted) =>
      match style with
      | .inlineLean m _ _live =>
        let str :=
          if hasErrors hl then addComment hl.toString else hl.toString
        modify fun s =>
          -- TODO directories/dots in module name?
          s.alter s!"{m}.lean" fun
          | none => some str
          | some s => some <| s ++ "\n" ++ str

  addComment (str : String) : String :=
    str.toSlice.splitInclusive "\n"
      |>.map ("-- " ++ ·.copy)
      |>.toList
      |> String.join

  hasErrors : Highlighted → Bool
  | .point .error _ => true
  | .point .. => false
  | .span msgs hl =>
    msgs.any (·.1 matches .error) || hasErrors hl
  | .tactics _ _ _ hl => hasErrors hl
  | .seq xs => xs.any hasErrors
  | .text .. | .token .. | .unparsed .. => false

end

section
open Verso.Output Html

instance [GenreHtml Manual m] : GenreHtml Tutorial m where
  part go metadata txt :=
    go txt
  block goI goB container content :=
    HtmlT.cast <| inst.block (HtmlT.cast <| goI ·) (HtmlT.cast <| goB ·) container content
  inline go container content :=
    HtmlT.cast <| inst.inline (HtmlT.cast <| go ·) container content

where
  inst := (inferInstanceAs (GenreHtml Manual m))



variable [Monad m] [MonadReaderOf Manual.TraverseState m]

structure PageContent where
  /-- The contents of the `<title>` tag and the top `<h1>` -/
  title : String
  /-- The `<base>` tag, to be inserted at the beginning of `<head>` -/
  base : Html
  /-- Content to include in `<head>` -/
  head : Html
  /-- Main content -/
  content : Html

structure TutorialSummary where
  title : String
  link : Link
  summary : Html

structure TopicContent where
  title : String
  description : Html
  tutorials : Array TutorialSummary

structure LocalToC where
  title : String
  link : Link
  children : Array LocalToC
deriving ToJson, FromJson, BEq, Hashable, Inhabited

structure LiveConfig where
  /-- The location of the editor -/
  root : String := "https://live.lean-lang.org/"
  /-- The project to use for the link -/
  project : String
  /-- The text to use for the link -/
  content : String
deriving ToJson, FromJson, Hashable, BEq, Repr

open Verso.LzCompress in
def LiveConfig.url (config : LiveConfig) : String :=
  s!"{config.root}#project={config.project}&codez={lzCompress config.content}"

structure Theme where
  page : PageContent → IO Html
  topic : TopicContent → IO Html
  tutorialToC : Option (String × String) → Option LiveConfig → LocalToC → IO Html
  cssFiles : Array Manual.CssFile := #[]
  jsFiles : Array Manual.JsFile := #[]

private def defaultCss : Manual.CSS := include_str "default.css"

def Theme.default : Theme where
  page content := pure {{
    <html>
      <head>
        {{ content.base }}
        <meta charset="utf-8" />
        <title>{{ content.title }}</title>
        <link rel="stylesheet" href="default.css" />
        {{ content.head }}
      </head>
      <body>
        {{ content.content }}
      </body>
    </html>
  }}
  topic content := pure {{
      <div class="topic">
        <h2>{{ content.title }}</h2>
        {{ content.description }}
        <div class="tutorials">
          {{ content.tutorials.map fun tut => {{
            <a class="tutorial-summary" href={{tut.link.relativeLink}}>
              <strong>{{tut.title}}</strong>
              " "
              {{ tut.summary }}
              <footer>"READ NOW"</footer>
            </a>
            }}
          }}
        </div>
      </div>
    }}
  tutorialToC code? live? toc :=
    if toc.children.isEmpty && live?.isNone && code?.isNone then pure .empty
    else pure {{
      <nav class="local-toc">
        <div> <!-- This is for scroll prevention -->
          <h1>{{toc.title}}</h1>
          {{ if live?.isSome || code?.isSome then {{
              <div class="code-links">
                {{if let some live := live? then
                  {{ <a href={{live.url}} class="live code-link">"Live"</a> }}
                  else .empty}}
                {{if let some (url, _file) := code? then {{ <a href={{url}} class="download code-link"><code>".zip"</code></a> }} else .empty}}
              </div>
            }}
            else .empty
          }}
        </div>
        {{if toc.children.isEmpty then .empty
          else {{<ol>{{toc.children.map defaultLocalToC}}</ol>}} }}
      </nav>
    }}
  cssFiles := #[{ filename := "default.css", contents := defaultCss }]
where
  defaultLocalToC (toc : LocalToC) : Html := {{
    <li>
      <a href={{toc.link.relativeLink}}>{{toc.title}}</a>
      {{ if toc.children.isEmpty then .empty
          else {{<ol>{{toc.children.map defaultLocalToC}}</ol>}} }}
    </li>
  }}
  termination_by toc
  decreasing_by
    rename_i toc' h
    have : sizeOf toc.children < sizeOf toc := by
      cases toc; simp +arith
    have : sizeOf toc' < sizeOf toc.children := by
      simp_all [Array.sizeOf_lt_of_mem]
    grind

open Verso.FS

open Verso.Genre.Blog.Template in
structure EmitContext where
  components : Blog.Components
  theme : Theme
  config : Manual.Config
  logError : String → IO Unit

def EmitContext.toBlogContext (ctxt : EmitContext) : Blog.TraverseContext where
  config := { logError := ctxt.logError }
  components := ctxt.components

abbrev EmitM :=
  ReaderT EmitContext <|
  ReaderT Manual.TraverseState <|
  ReaderT ExtensionImpls <|
  StateRefT Blog.Component.State (StateRefT (Code.Hover.State Html) IO)

def EmitM.run
    (theme : Theme) (config : Manual.Config) (logError : String → IO Unit)
    (state : Manual.TraverseState) (extensionImpls : ExtensionImpls)
    (componentState : Blog.Component.State)
    (hoverState : Code.Hover.State Html)
    (components : Blog.Components)
    (act : EmitM α) : IO (α × Blog.Component.State × Code.Hover.State Html) := do
  let ((v, st), st') ← ReaderT.run act {theme, config, logError, components} |>.run state |>.run extensionImpls |>.run componentState |>.run hoverState
  return (v, st, st')

def EmitM.config : EmitM Manual.Config := do
  return (← readThe EmitContext).config

def EmitM.logError : EmitM ((message : String) → IO Unit) := do
  return (← readThe EmitContext).logError

def EmitM.htmlOptions [MonadLiftT IO m] : EmitM (Html.Options m) := do
  return { logError := ((← EmitM.logError) ·) }

def EmitM.writeFile (path : System.FilePath) (content : String) : EmitM Unit := do
  if (← readThe EmitContext).config.verbose then
    IO.println s!"Writing {path}"
  IO.FS.writeFile path content

def EmitM.writeHtmlFile (path : System.FilePath) (content : Html) : EmitM Unit := do
  if (← readThe EmitContext).config.verbose then
    IO.println s!"Writing {path}"
  IO.FS.writeFile path <| doctype ++ "\n" ++ content.asString

def EmitM.theme : EmitM Theme := do
  return (← readThe EmitContext).theme


def LocalToC.ofPage (path : Path) (text : Part Blog.Page) : EmitM LocalToC := do
  let title := text.titleString
  let htmlId := text.metadata.bind (·.htmlId) |>.get! |>.sluggify
  let link := .mk path htmlId
  let children ← text.subParts.attach.mapM fun ⟨child, _⟩ => ofPage path child
  return {
    title,
    link,
    children
  }
termination_by text
decreasing_by
  let {subParts, ..} := text
  have : sizeOf child < sizeOf subParts := by
    simp_all [Array.sizeOf_lt_of_mem]
  grind [Doc.Part.mk.sizeOf_spec]


open Output Html in
def EmitM.page (path : Path) (title : String) (content : Html) : EmitM Html := do
  let state ← readThe Manual.TraverseState
  let extraJsFiles :=
    Manual.sortJs <|
      state.extraJsFiles.toArray.map (false, ·.toStaticJsFile)
  let extraJsFiles := extraJsFiles.map fun
    | (true, f) => (f.filename, f.defer)
    | (false, f) => ("-verso-data/" ++ f.filename, f.defer)


  (← theme).page {
    title := title,
    base := {{ <base href={{ path.map (fun _ => "../") |>.foldl (init := "./") (· ++ ·) }} /> }},
    head := .seq #[
      extraJsFiles.map fun (fn, defer) =>
        {{<script src={{fn}} {{if defer then #[("defer", "defer")] else #[]}}></script>}},
      state.extraCssFiles.toArray.map fun cssFile =>
        {{<link rel="stylesheet" href=s!"-verso-data/{cssFile.filename}" />}},
      state.extraJs.toArray.map fun ⟨js⟩ =>
        {{<script>{{.text false js}}</script>}},
      state.extraCss.toArray.map fun ⟨css⟩ =>
        {{<style>{{.text false css}}</style>}}
    ],
    content
  }
--set_option trace.Meta.synthInstance true in

open scoped Verso.Genre.Blog.Template in
def EmitM.tutorialList (topics : Array Topic) : Array (Part Blog.Page) :=
  topics.map fun { title, titleString, description, tutorials } => {
    title, titleString,
    metadata := none,
    content := description,
    subParts := #[]
  }




open Verso.Genre.Manual in
def tutorialLocalTargets (state : TraverseState) : Code.LinkTargets ctxt where
  const := fun x _ctxt? =>
    state.linksFromDomain docstringDomain x.toString "doc" s!"Documentation for {x}" ++
    state.linksFromDomain exampleDomain x.toString "def" s!"Definition of example"

  option := fun x _ctxt? =>
    state.linksFromDomain optionDomain x.toString "doc" s!"Documentation for option {x}"
  keyword := fun k _ctxt? =>
    state.linksFromDomain tacticDomain k.toString "doc" "Documentation for tactic" ++
    state.linksFromDomain syntaxKindDomain k.toString "doc" "Documentation for syntax"

partial def inlineToPage (i : Inline Tutorial) : EmitM (Inline Blog.Page) := do
  match i with
  | .text s => return .text s
  | .linebreak s => return .linebreak s
  | .code s => return .code s
  | .math m s => return .math m s
  | .concat xs => .concat <$> xs.mapM inlineToPage
  | .image alt url => return .image alt url
  | .bold xs => .bold <$> xs.mapM inlineToPage
  | .emph xs => .emph <$> xs.mapM inlineToPage
  | .link xs url => (.link · url) <$> xs.mapM inlineToPage
  | .footnote name xs => .footnote name <$> xs.mapM inlineToPage
  | .other .. =>
    let hoverSt ← getThe (Code.Hover.State Html)
    let (html, hoverSt) ← Tutorial.toHtml (m := ReaderT AllRemotes (ReaderT ExtensionImpls IO)) (← EmitM.htmlOptions) { logError := (← read).logError } (← readThe Manual.TraverseState) {} {} {} i |>.run hoverSt {} (← readThe ExtensionImpls)
    set hoverSt
    return .other (.blob html) #[]

partial def blockToPage (b : Block Tutorial) : EmitM (Block Blog.Page) := do
  match b with
  | .para xs => .para <$> xs.mapM inlineToPage
  | .concat xs => .concat <$> xs.mapM blockToPage
  | .blockquote xs => .blockquote <$> xs.mapM blockToPage
  | .ol n xs => .ol n <$> xs.mapM fun ⟨i⟩ => .mk <$> i.mapM blockToPage
  | .ul xs => .ul <$> xs.mapM fun ⟨i⟩ => .mk <$> i.mapM blockToPage
  | .dl xs => .dl <$> xs.mapM fun ⟨t, d⟩ => .mk <$> t.mapM inlineToPage <*> d.mapM blockToPage
  | .code s => return .code s
  | .other .. =>
    let hoverSt ← getThe (Code.Hover.State Html)
    let (html, hoverSt) ← Tutorial.toHtml (m := ReaderT AllRemotes (ReaderT ExtensionImpls IO)) (← EmitM.htmlOptions) { logError := (← read).logError } (← readThe Manual.TraverseState) {} {} {} b |>.run hoverSt {} (← readThe ExtensionImpls)
    set hoverSt
    return .other (.blob html) #[]

def defaultLocalToC (toc : LocalToC) : Html := {{
    <li>
      <a href={{toc.link.relativeLink}}>{{toc.title}}</a>
      {{ if toc.children.isEmpty then .empty
          else {{<ol>{{toc.children.map defaultLocalToC}}</ol>}} }}
    </li>
  }}
termination_by toc
decreasing_by
  rename_i toc' h
  have : sizeOf toc.children < sizeOf toc := by
    cases toc; simp +arith
  have : sizeOf toc' < sizeOf toc.children := by
    simp_all [Array.sizeOf_lt_of_mem]
  grind

private def localToCStyle := r#"
nav.local-toc {
  position: fixed;
  top: 1rem;
  right: calc((100vw - var(--max-width)) / 2 - 15rem - 2rem);
  width: 15rem;
  font-size: 0.875rem;
  max-height: calc(100vh - 2rem);
  overflow-y: auto;
}

nav.local-toc ol {
  list-style: none;
  margin: 0;
  padding: 0;
}

nav.local-toc li {
  margin: 0.5rem 0;
}

nav.local-toc a {
  color: var(--verso-text-color);
  text-decoration: none;
}

nav.local-toc a:hover {
  color: var(--color-accent);
}

/* On smaller screens, display normally */
@media (max-width: 90rem) {
  nav.local-toc {
    position: static;
    right: auto;
    width: auto;
    max-height: none;
    border-left: 3px solid var(--color-border);
    padding-left: 1rem;
    margin-bottom: 1rem;
  }
}

nav.local-toc ol ol {
  padding-left: 1rem;
  margin-top: 0.25rem;
}

nav.local-toc ol ol li {
  margin: 0.25rem 0;
}

/*******/
nav.local-toc > div:first-child {
  margin-bottom: 1rem;
}

nav.local-toc h1 {
  font-size: 1rem;
  margin: 0 0 0.5rem 0;
  font-weight: 600;
}

nav.local-toc .code-links {
  display: flex;
  gap: 0.5rem;
  flex-wrap: wrap;
}

nav.local-toc .code-link {
  font-size: 0.8125rem;
  padding: 0.25rem 0.5rem;
  border: 1px solid var(--color-border);
  border-radius: 6px;
  color: var(--verso-text-color);
  text-decoration: none;
  display: inline-block;
}

nav.local-toc .code-link:hover {
  background: var(--verso-selected-color);
  border-color: var(--color-accent);
}

nav.local-toc .code-link code {
  background: none;
  padding: 0;
  font-size: inherit;
}

nav.local-toc .code-link.live::before {
  content: "↪ ";
  margin-right: 0.25rem;
}

nav.local-toc .code-link.download::before {
  content: "📦 ";
  margin-right: 0.25rem;
}
"#

block_component tutorialNav (code? : Option (String × String)) (live? : Option LiveConfig) (toc : LocalToC) where
  traverse _ _ := pure none
  toHtml id _json goI goB contents := do
    if toc.children.isEmpty && live?.isNone && code?.isNone then pure .empty
    else pure {{
      <nav class="local-toc">
        <div> <!-- This is for scroll prevention -->
          <h1>{{toc.title}}</h1>
          {{ if live?.isSome || code?.isSome then {{
              <div class="code-links">
                {{if let some live := live? then
                  {{ <a href={{live.url}} class="live code-link">"Live"</a> }}
                  else .empty}}
                {{if let some (url, _file) := code? then {{ <a href={{url}} class="download code-link"><code>".zip"</code></a> }} else .empty}}
              </div>
            }}
            else .empty
          }}
        </div>
        {{if toc.children.isEmpty then .empty
          else {{<ol>{{toc.children.map defaultLocalToC}}</ol>}} }}
      </nav>
    }}
  cssFiles := #[("local-toc.css", localToCStyle)]

partial def partToPage (tut : Part Tutorial) : EmitM (Part Blog.Page) := do
  let title ← tut.title.mapM inlineToPage
  let content ← tut.content.mapM blockToPage
  let subParts ← tut.subParts.mapM partToPage

  let htmlMeta ← do
    let some id := tut.metadata.bind (·.id)
      | pure none
    let st ← readThe Manual.TraverseState
    let some link := st.externalTags[id]?
      | pure none
    pure <| some { htmlId := some link.htmlId.toString }


  return { tut with title, metadata := htmlMeta, content, subParts }

def addLocalToC (path : Path) (metadata : Tutorial.PartMetadata) (tut : Part Tutorial) (part : Part Blog.Page) : EmitM (Part Blog.Page) := do
  let code := getCode tut
  let toc ← LocalToC.ofPage path part
  let sampleCode := do
    match metadata.exampleStyle with
    | .inlineLean .. => pure (metadata.slug ++ "/" ++ metadata.slug ++ ".zip", metadata.slug ++ ".zip")
  let live? := do
    match metadata.exampleStyle with
    | .inlineLean _ _ (some project) =>
      let content ←
        match code.filter (fun (name, _) => name.endsWith ".lean") with
        | #[(_, code)] => pure code
        | _ => none
      pure { project, content }
    | _ => none
  return { part with
    content := #[tutorialNav sampleCode live? toc #[]] ++ part.content
  }

def toSite (tuts : Tutorials) : EmitM Blog.Site := do
  let contentPages : Array Blog.Dir ← tuts.topics.flatMap (·.tutorials) |>.filterMapM fun t => do
    let some metadata := t.metadata
      | return none
    let slug := metadata.slug
    let path := #[slug]
    let page ← partToPage t
    let page ← addLocalToC path metadata t page
    return Blog.Dir.page slug slug.toName page #[]
  let topicParts ← tuts.topics.mapM fun t => do
    let tutList ← Block.dl <$> t.tutorials.filterMapM fun tut => do
      let some m := tut.metadata
        | return none
      return some {
        term := #[.link (← tut.title.mapM inlineToPage) s!"./{m.slug}"],
        desc := tut.metadata.map (.para #[.text <| ·.summary]) |>.toArray
      }
    return { t with
      metadata := none,
      content := t.description ++ #[tutList],
      subParts := #[]
    }
  return .page `tutorials { tuts.content with subParts := topicParts } contentPages

def EmitM.blogConfig : EmitM Blog.Config := do
  return { logError := (← read).logError, verbose := (← EmitM.config).verbose }

def liftGenerate (act : Blog.GenerateM α) (site : Blog.Site) (state : Blog.TraverseState) : EmitM α := do
  let st ← getThe (Code.Hover.State _)
  let st' ← getThe Blog.Component.State
  let mSt ← readThe Manual.TraverseState
  let ctxt := {
    site
    ctxt := (← read).toBlogContext
    xref := { state with
      scripts := state.scripts.insertMany (mSt.extraJs |>.toArray |>.map (·.js)),
      stylesheets := state.stylesheets.insertMany (mSt.extraCss |>.toArray |>.map (·.css)),
      cssFiles := state.cssFiles ++ (mSt.extraCssFiles |>.toArray |>.map fun css => (css.filename, css.contents.css)),
      jsFiles := state.jsFiles ++ (mSt.extraJsFiles |>.toArray |>.map fun js => (js.filename, js.contents.js, js.sourceMap?.map (fun m => (m.filename, m.contents)))),
      remoteContent := {}
    }
    linkTargets := {} -- TODO
    dir := (← read).config.destination
    config := (← EmitM.blogConfig)
    header := Html.doctype
    components := (← read).components
  }
  let ((v, st), st') ← act.run ctxt st st'
  set st
  set st'
  return v

open EmitM in
def emit (tutorials : Tutorials) (blogTheme : Blog.Theme) : EmitM Unit := do
  let config ← EmitM.config
  if config.verbose then IO.println "Updating remote data"
  let remoteContent ← updateRemotes false config.remoteConfigFile (if config.verbose then IO.println else fun _ => pure ())

  let targets : Code.LinkTargets Tutorial.TraverseContext := tutorialLocalTargets (← readThe Manual.TraverseState) ++ remoteContent.remoteTargets

  let dir := (← read).config.destination
  ensureDir dir
  (← readThe Manual.TraverseState).writeFiles (dir / "-verso-data")

  let site ← toSite tutorials
  let (site, blogState) ← site.traverse (← blogConfig) (← read).components


  let state ← readThe Manual.TraverseState

  state.writeFiles dir

  liftGenerate (site.generate blogTheme) site blogState

  let logError : String → IO Unit := (← read).logError
  -- for sec in tutorials.topics do
  --   for tut in sec.tutorials do
  --     let some metadata := tut.metadata
  --       | logError s!"No metadata for {tut.titleString}"
  --     let dir := dir / metadata.slug
  --     let code := getCode tut
  --     ensureDir dir
  --     Zip.zipToFile (dir / (metadata.slug ++ ".zip")) (method := .store) <| code.map fun (fn, txt) => (metadata.slug ++ "/" ++ fn, txt.toByteArray)

  --     let ctxt := { logError }
  --     let ctxt := TraversePart.inPart tut ctxt

  --     let definitionIds := (← readThe Manual.TraverseState).definitionIds ctxt

  --     let (html, hlState') ←
  --       Genre.toHtml (m := ReaderT AllRemotes (ReaderT ExtensionImpls IO)) Tutorial { logError := (logError ·) } ctxt (← readThe Manual.TraverseState) definitionIds targets {} tut hlState remoteContent

  --     let toc ← LocalToC.ofPart tut
  --     let sampleCode := do
  --       match metadata.exampleStyle with
  --       | .inlineLean .. => pure (metadata.slug ++ "/" ++ metadata.slug ++ ".zip", metadata.slug ++ ".zip")
  --     let live? := do
  --       match metadata.exampleStyle with
  --       | .inlineLean _ _ (some project) =>
  --         let content ←
  --           match code.filter (·.1.endsWith ".lean") with
  --           | #[(_, code)] => pure code
  --           | _ => none
  --         pure { project, content }
  --       | _ => none
  --     let html := html ++ (← (← theme).tutorialToC sampleCode live? toc)
  --     let html := {{<main class="tutorial-text">{{html}}</main>}}
  --     let html ← page (Path.root / metadata.slug) tut.titleString html
  --     writeHtmlFile (dir / "index.html") html


  writeFile (dir / "-verso-docs.json") (toString (← getThe <| Code.Hover.State _).dedup.docJson)

  for (filename, contents, srcMap?) in blogState.jsFiles do
    let filename := (dir / "-verso-data" / filename)
    filename.parent.forM (IO.FS.createDirAll ·)
    writeFile filename contents
    if let some m := srcMap? then
      let filename := (dir / "-verso-data" / m.1)
      filename.parent.forM (IO.FS.createDirAll ·)
      writeFile filename m.2
  for (filename, contents) in blogState.cssFiles do
    let filename := (dir / "-verso-data" / filename)
    filename.parent.forM (IO.FS.createDirAll ·)
    writeFile filename contents


  for themeJs in (← theme).jsFiles do
    let filename := (dir / themeJs.filename)
    filename.parent.forM (IO.FS.createDirAll ·)
    writeFile filename themeJs.contents.js
    if let some m := themeJs.sourceMap? then
      let filename := (dir / m.filename)
      filename.parent.forM (IO.FS.createDirAll ·)
      writeFile filename m.contents
  for themeCss in (← theme).cssFiles do
    let filename := (dir / themeCss.filename)
    filename.parent.forM (IO.FS.createDirAll ·)
    writeFile filename themeCss.contents.css

end

inductive EmitTutorial where
  | immediately
  | delay (savedState : System.FilePath)
  | resumeFrom (savedState : System.FilePath)

structure Config extends Manual.Config where
  emit : EmitTutorial := .immediately

structure SavedState where
  tutorials : Tutorials
  traverseState : Manual.TraverseState
deriving ToJson, FromJson

def SavedState.save (file : System.FilePath) (state : SavedState) : IO Unit := do
  IO.FS.writeFile file (toJson state).compress

def SavedState.load (file : System.FilePath) : IO SavedState := do
  let json ← IO.FS.readFile file
  match Json.parse json with
  | .error e => throw <| .userError s!"Error parsing {file}: {e}"
  | .ok json =>
    match FromJson.fromJson? json with
    | .error e => throw <| .userError s!"Error deserializing tutorials from {file}: {e}"
    | .ok st => return st

open Verso.CLI

open scoped Verso.Genre.Blog.Template in
def tutorialsMain (tutorials : Tutorials) (args : List String)
    (config : Config := {})
    (theme : Theme := .default)
    (extensionImpls : ExtensionImpls := by exact extension_impls%)
    (components : Blog.Components := by exact %registered_components) :
    IO UInt32 :=
  ReaderT.run go extensionImpls

where
  go : ReaderT ExtensionImpls IO UInt32 := do
    let config ← opts config args
    let errorCount : IO.Ref Nat ← IO.mkRef 0
    let logError msg := do errorCount.modify (· + 1); IO.eprintln msg

    IO.FS.createDirAll config.destination

    -- Traversal
    let (tutorials, state) ←
      match config.emit with
      | .immediately =>
        let (tutorials, state) ← traverse logError tutorials config.toConfig
        let json := xrefJson state.domains state.externalTags

        IO.FS.writeFile (config.destination / "xref.json") <| toString json
        pure (tutorials, state)
      | .delay f =>
        let (tutorials, state) ← traverse logError tutorials config.toConfig
        SavedState.mk tutorials state |>.save f
        let json := xrefJson state.domains state.externalTags
        IO.FS.writeFile (config.destination / "xref.json") <| toString json
        return 0
      | .resumeFrom f =>
          try
            let ⟨tutorials, state⟩ ← SavedState.load f
            pure (tutorials, state)
          catch
            | .userError e => logError e; return (1 : UInt32)
            | other => throw other

    -- Emit HTML
    let ((), _) ← (emit tutorials .default).run theme config.toConfig logError state extensionImpls {} {} components

    match ← errorCount.get with
    | 0 => return 0
    | 1 => IO.eprintln "An error was encountered!"; return 1
    | n => IO.eprintln s!"{n} errors were encountered!"; return 1

  opts (cfg : Config) : List String → ReaderT ExtensionImpls IO Config
    | ("--output"::dir::more) => opts { cfg with destination := dir } more
    | ("--verbose"::more) => opts { cfg with verbose := true } more
    | ("--now"::more) => opts { cfg with emit := .immediately } more
    | ("--delay"::more) =>
      match requireFilename "--delay" more with
      | .ok file more' _ => opts { cfg with emit := .delay file } more'
      | .error e => throw (↑ e)
    | ("--resume"::more) =>
      match requireFilename "--resume" more with
      | .ok file more' _ => opts { cfg with emit := .resumeFrom file } more'
      | .error e => throw (↑ e)
    | ("--remote-config"::more) =>
      match requireFilename "--remote-config" more with
      | .ok file more' _ => opts { cfg with remoteConfigFile := some file } more'
      | .error e => throw (↑ e)
    | (other :: _) => throw (↑ s!"Unknown option {other}")
    | [] => pure cfg
  termination_by args => args
