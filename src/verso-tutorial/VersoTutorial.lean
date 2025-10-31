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

namespace Verso.Genre

open Verso.Doc (Genre)
open Verso.Multi

private def defaultToolchain := "leanprover/lean4:" ++ Lean.versionString
private def defaultLive := "lean-v" ++ Lean.versionString

inductive ExampleCodeStyle where
  /--
  The example code should be extracted to a Lean project from the tutorial.
  -/
  | inlineLean (moduleName : Lean.Name) (toolchain := defaultToolchain) (liveProject := some defaultLive)
deriving BEq, DecidableEq, Inhabited, Repr

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
deriving BEq, DecidableEq, Inhabited, Repr

def Tutorial : Genre :=
  { Manual with
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
open Lean

instance : TraversePart Tutorial where
  inPart p ctx := { ctx with
    headers := ctx.headers.push { titleString := p.titleString, metadata := none },
    path := if let some metadata := p.metadata then ctx.path.push metadata.slug else ctx.path
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


open Manual in
instance : Traverse Tutorial TraverseM where
  part p := do
    if p.metadata.isNone then
      pure (some { slug := p.titleString.sluggify.toString, summary := "", exampleStyle := .inlineLean `Main })
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
  title : String -- TODO inlines
  description : Array (Block .none) -- TODO page from blog genre?
  tutorials : Array (Part Tutorial)
deriving BEq

structure Tutorials : Type where
  content : Part .none -- TODO Page from blog genre?
  topics : Array Topic
deriving BEq

def Tutorials.traverse1 [Monad m] (traversal : Part Tutorial → m (Part Tutorial)) (tutorials : Tutorials) : m Tutorials := do
  let { content, topics } := tutorials
  return {
    content,
    topics := ← topics.mapM fun topic => do
      return { topic with
        tutorials := ← topic.tutorials.mapM traversal
      }
  }

open Manual in
def traverse (logError : String → IO Unit) (tutorials : Tutorials) (config : Manual.Config) : ReaderT ExtensionImpls IO (Tutorials × Manual.TraverseState) := do
  let topCtxt : Manual.TraverseContext := {logError, draft := config.draft}
  if config.verbose then IO.println "Updating remote data"
  let remoteContent ← updateRemotes false config.remoteConfigFile (if config.verbose then IO.println else fun _ => pure ())
  let mut state : Manual.TraverseState := {
    licenseInfo := .ofList config.licenseInfo,
    extraCss := .insertMany {} config.extraJs
    extraJs := .insertMany {} config.extraJs
    extraCssFiles := config.extraCssFiles,
    extraJsFiles := config.extraJsFiles,
    remoteContent
  }
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
      |>.allowNontermination.toList
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

instance : GenreHtml Tutorial (ReaderT ExtensionImpls IO) where
  part go metadata txt :=
    go txt
  block goI goB container content :=
    HtmlT.cast <| inst.block (HtmlT.cast <| goI ·) (HtmlT.cast <| goB ·) container content
  inline go container content :=
    HtmlT.cast <| inst.inline (HtmlT.cast <| go ·) container content

where
  inst := (inferInstanceAs (GenreHtml Manual (ReaderT ExtensionImpls IO)))

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

structure LiveConfig where
  /-- The location of the editor -/
  root : String := "https://live.lean-lang.org/"
  /-- The project to use for the link -/
  project : String
  /-- The text to use for the link -/
  content : String

open Verso.LzCompress in
def LiveConfig.url (config : LiveConfig) : String :=
  s!"{config.root}#project={config.project}&codez={lzCompress config.content}"

structure Theme where
  page : PageContent → Html
  topic : TopicContent → Html
  tutorialToC : Option (String × String) → Option LiveConfig → LocalToC → Html
  cssFiles : Array (String × String) := #[]
  jsFiles : Array Manual.JsFile := #[]

private def defaultCss := include_str "default.css"

def Theme.default : Theme where
  page content := {{
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
  topic content := {{
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
  tutorialToC code? live? toc := if toc.children.isEmpty then .empty else {{
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
      <ol>{{toc.children.map defaultLocalToC}}</ol>
    </nav>
  }}
  cssFiles := #[("default.css", defaultCss)]
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

structure EmitContext where
  theme : Theme
  config : Manual.Config
  logError : String → IO Unit

abbrev EmitM :=
  ReaderT EmitContext <|
  ReaderT Manual.TraverseState <|
  ReaderT ExtensionImpls <|
  IO

def EmitM.run
    (theme : Theme) (config : Manual.Config) (logError : String → IO Unit)
    (state : Manual.TraverseState) (extensionImpls : ExtensionImpls)
    (act : EmitM α) : IO α :=
  ReaderT.run act {theme, config, logError} |>.run state |>.run extensionImpls

def EmitM.logError (message : String) : EmitM Unit := do
  (← readThe EmitContext).logError message

def EmitM.htmlOptions : EmitM (Html.Options EmitM) := do
  return { logError := EmitM.logError }

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

def LocalToC.ofPart (text : Part Tutorial) : EmitM LocalToC := do
  let title := text.titleString
  let id := text.metadata.bind (·.id) |>.get!
  let link := (← readThe Manual.TraverseState).externalTags[id]!
  let children ← text.subParts.attach.mapM fun ⟨child, _⟩ => ofPart child
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
      state.extraJsFiles.map (false, ·.toStaticJsFile)
  let extraJsFiles := extraJsFiles.map fun
    | (true, f) => (f.filename, f.defer)
    | (false, f) => ("/-verso-data/" ++ f.filename, f.defer)


  return (← theme).page {
    title := title,
    base := {{ <base href={{ path.map (fun _ => "../") |>.foldl (init := "./") (· ++ ·) }} /> }},
    head := .seq #[
      extraJsFiles.map fun (fn, defer) =>
        {{<script src={{fn}} {{if defer then #[("defer", "defer")] else #[]}}></script>}},
      state.extraJs.toArray.map fun js =>
        {{ <script>{{.text false js}}</script>}},
      state.extraCss.toArray.map fun css =>
        {{<style>{{.text false css}}</style>}}
    ],
    content
  }

def EmitM.tutorialList (topics : Array Topic) : EmitM Html :=
  topics.mapM topicHtml
where
  topicHtml (topic : Topic) := do
    let description ← topic.description.mapM (Genre.toHtml .none (← htmlOptions) () () {} {} {} · {})
    let description := description.map Prod.fst
    return (← theme).topic {
      title := topic.title,
      description,
      tutorials := ← topic.tutorials.filterMapM fun tut : Part Tutorial => do
        let some {id := id?, summary, ..} := tut.metadata
          | logError s!"No metadata for tutorial '{tut.titleString}'"
            return none
        let some id := id?
          | logError s!"No ID assigned for tutorial '{tut.titleString}'"
            return none
        let some link := (← readThe Manual.TraverseState).externalTags[id]?
          | logError s!"No link found for tutorial '{tut.titleString}'"
            return none
        return some { title := tut.titleString, link, summary : TutorialSummary }
    }

open EmitM in
def emit (tutorials : Tutorials) : EmitM Unit := do
  let dir := (← read).config.destination
  ensureDir dir
  let mut hlState := {}
  for f in (← readThe Manual.TraverseState).extraJsFiles do
    ensureDir (dir / "-verso-data")
    (dir / "-verso-data" / f.filename).parent |>.forM fun d => ensureDir d
    writeFile (dir / "-verso-data" / f.filename) f.contents
    if let some m := f.sourceMap? then
      writeFile (dir / "-verso-data" / m.filename) m.contents
  -- TODO cross-link to manual even here
  let (rootHtml, hlState') ← Genre.toHtml .none (← EmitM.htmlOptions) () () {} {} {} tutorials.content hlState
  hlState := hlState'
  writeHtmlFile (dir / "index.html") (← page .root "Tutorials" (rootHtml ++ (← tutorialList tutorials.topics)))

  let logError : String → IO Unit := (← read).logError
  for sec in tutorials.topics do
    for tut in sec.tutorials do
      let some metadata := tut.metadata
        | logError s!"No metadata for {tut.titleString}"
      let dir := dir / metadata.slug
      let code := getCode tut
      ensureDir dir
      Zip.zipToFile (dir / (metadata.slug ++ ".zip")) (method := .store) <| code.map fun (fn, txt) => (metadata.slug ++ "/" ++ fn, txt.bytes)
      let (html, hlState') ← Genre.toHtml (m := ReaderT ExtensionImpls IO) Tutorial { logError := (logError ·) } { logError } (← readThe Manual.TraverseState) {} {} {} tut hlState
      hlState := hlState'
      let toc ← LocalToC.ofPart tut
      let sampleCode := do
        match metadata.exampleStyle with
        | .inlineLean .. => pure (metadata.slug ++ "/" ++ metadata.slug ++ ".zip", metadata.slug ++ ".zip")
      let live? := do
        match metadata.exampleStyle with
        | .inlineLean _ _ (some project) =>
          let content ←
            match code.filter (·.1.endsWith ".lean") with
            | #[(_, code)] => pure code
            | _ => none
          pure { project, content }
        | _ => none
      let html := html ++ (← theme).tutorialToC sampleCode live? toc
      let html := {{<main class="tutorial-text">{{html}}</main>}}
      let html ← page (Path.root / metadata.slug) tut.titleString html
      writeHtmlFile (dir / "index.html") html

  writeFile (dir / "-verso-docs.json") (toString hlState.dedup.docJson)

  for themeJs in (← theme).jsFiles do
    writeFile (dir / themeJs.filename) themeJs.contents
    if let some m := themeJs.sourceMap? then
      writeFile (dir / m.filename) m.contents
  for themeCss in (← theme).cssFiles do
    writeFile (dir / themeCss.1) themeCss.2

  let json := xrefJson (← readThe Manual.TraverseState).domains (← readThe Manual.TraverseState).externalTags
  writeFile (dir / "xref.json") <| toString json


end


def tutorialsMain (tutorials : Tutorials) (args : List String)
    (config : Manual.Config := Manual.Config.addKaTeX {})
    (theme : Theme := .default)
    (extensionImpls : ExtensionImpls := by exact extension_impls%) :
    IO UInt32 :=
  ReaderT.run go extensionImpls

where
  go : ReaderT ExtensionImpls IO UInt32 := do
    let config ← opts config args
    let hasError ← IO.mkRef false
    let logError msg := do hasError.set true; IO.eprintln msg

    -- Traversal
    let (tutorials, state) ← traverse logError tutorials config

    -- Emit HTML
    (emit tutorials).run theme config logError state extensionImpls

    -- Extract code/convert
    if (← hasError.get) then
      IO.eprintln "Errors were encountered!"
      return 1
    else
      return 0

  opts (cfg : Manual.Config) : List String → ReaderT ExtensionImpls IO Manual.Config
    | ("--output"::dir::more) => opts {cfg with destination := dir} more
    | ("--verbose"::more) => opts {cfg with verbose := true} more
    | (other :: _) => throw (↑ s!"Unknown option {other}")
    | [] => pure cfg
