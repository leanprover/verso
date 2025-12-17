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
import VersoTutorial.Basic

open Lean
open Std
open Verso.Doc
open SubVerso.Highlighting
open Verso.Multi
open Verso.Genre.Manual

namespace Verso.Genre.Tutorial


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

open Verso.FS

open Verso.Genre.Blog.Template in
structure EmitContext where
  components : Blog.Components
  config : Manual.Config
  logError : String → IO Unit
  theme : Blog.Theme
  remoteContent : AllRemotes

def EmitContext.toBlogContext (ctxt : EmitContext) : Blog.TraverseContext where
  config := { logError := ctxt.logError }
  components := ctxt.components

abbrev EmitM :=
  ReaderT EmitContext <|
  ReaderT Manual.TraverseState <|
  ReaderT ExtensionImpls <|
  StateRefT Blog.Component.State (StateRefT (Code.Hover.State Html) IO)

def EmitM.run
    (config : Manual.Config) (logError : String → IO Unit)
    (state : Manual.TraverseState) (extensionImpls : ExtensionImpls)
    (componentState : Blog.Component.State)
    (hoverState : Code.Hover.State Html)
    (components : Blog.Components)
    (theme : Blog.Theme)
    (remoteContent : AllRemotes)
    (act : EmitM α) : IO (α × Blog.Component.State × Code.Hover.State Html) := do
  let ((v, st), st') ←
    ReaderT.run act { config, logError, components, theme, remoteContent }
      |>.run state
      |>.run extensionImpls
      |>.run componentState
      |>.run hoverState
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

open scoped Verso.Genre.Blog.Template in
def EmitM.tutorialList (topics : Array Topic) : Array (Part Blog.Page) :=
  topics.map fun { title, titleString, description, .. } => {
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
    let (html, hoverSt) ←
      Tutorial.toHtml (m := ReaderT AllRemotes (ReaderT ExtensionImpls IO)) (← EmitM.htmlOptions)
        { logError := (← read).logError }
        (← readThe Manual.TraverseState)
        {} {} {} i
        |>.run hoverSt
        |>.run (← read).remoteContent
        |>.run (← readThe ExtensionImpls)
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
    let (html, hoverSt) ←
      Tutorial.toHtml (m := ReaderT AllRemotes (ReaderT ExtensionImpls IO)) (← EmitM.htmlOptions)
        { logError := (← read).logError }
        (← readThe Manual.TraverseState)
        {} {} {} b
        |>.run hoverSt
        |>.run (← read).remoteContent
        |>.run (← readThe ExtensionImpls)
    set hoverSt
    return .other (.blob html) #[]

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

def tutorialNavHtml (code? : Option (String × String)) (live? : Option LiveConfig) (toc : LocalToC) : Html :=
  if toc.children.isEmpty && live?.isNone && code?.isNone then .empty
    else {{
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

def toSite (tuts : Tutorials) : EmitM Blog.Site := do
  let contentPages : Array Blog.Dir ← tuts.topics.flatMap (·.tutorials) |>.filterMapM fun t => do
    let some metadata := t.metadata
      | return none
    let slug := metadata.slug
    let page ← partToPage t
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

def liftGenerate (act : Blog.GenerateM α) (site : Blog.Site) (state : Blog.TraverseState) (extraParams : Path → Blog.Template.Params:= fun _ => {}) : EmitM α := do
  let st ← getThe (Code.Hover.State _)
  let st' ← getThe Blog.Component.State
  let mSt ← readThe Manual.TraverseState
  let remoteContent := (← read).remoteContent

  let linkTargets : Code.LinkTargets Blog.TraverseContext :=
    tutorialLocalTargets (← readThe Manual.TraverseState) ++ remoteContent.remoteTargets

  let theme := (← read).theme
  let ctxt := {
    site,
    theme,
    ctxt := (← read).toBlogContext,
    xref := { state with
      scripts := state.scripts.insertMany (mSt.extraJs |>.toArray |>.map (·.js)),
      stylesheets := state.stylesheets.insertMany (mSt.extraCss |>.toArray |>.map (·.css)),
      cssFiles := state.cssFiles ++ (mSt.extraCssFiles |>.toArray |>.map fun css => (css.filename, css.contents.css)),
      jsFiles := state.jsFiles ++ (mSt.extraJsFiles |>.toArray |>.map fun js => (js.filename, js.contents.js, js.sourceMap?.map (fun m => (m.filename, m.contents)))),
      remoteContent := remoteContent
    },
    linkTargets,
    dir := (← read).config.destination,
    config := (← EmitM.blogConfig),
    header := Html.doctype,
    components := (← read).components,
    extraParams
  }
  let ((v, st), st') ← act.run ctxt st st'
  set st
  set st'
  return v

open EmitM in
def emit (tutorials : Tutorials) : EmitM Unit := do
  let remoteContent := (← read).remoteContent

  let dir := (← read).config.destination
  ensureDir dir
  (← readThe Manual.TraverseState).writeFiles (dir / "-verso-data")

  let site ← toSite tutorials
  let (site, blogState) ← site.traverse (← blogConfig) (← read).components

  let state ← readThe Manual.TraverseState

  state.writeFiles dir

  let mut tutorialCode : HashMap String ((String × String) × Option LiveConfig) := {}

  for sec in tutorials.topics do
    for tut in sec.tutorials do
      let some metadata := tut.metadata
        | continue
      let dir := dir / metadata.slug
      let code := getCode tut
      ensureDir dir

      Zip.zipToFile (dir / (metadata.slug ++ ".zip")) (method := .deflate) <|
        code.map fun (fn, txt) => (metadata.slug ++ "/" ++ fn, txt.toByteArray)

      let live? := do
        match metadata.exampleStyle with
        | .inlineLean _ _ (some project) =>
          let content ←
            match code.filter (fun ((name, _) : String × String) => name.endsWith ".lean") with
            | #[(_, code)] => pure code
            | _ => none
          pure { project, content }
        | _ => none

      tutorialCode := tutorialCode.insert metadata.slug ((s!"{metadata.slug}/{metadata.slug}.zip", s!"{metadata.slug}.zip"), live?)

  let tutorialTocs : HashMap String LocalToC ←
    if let .page _ _ subs := site then
      HashMap.ofArray <$> (subs.filterMapM fun s => do
        if let .page p _ x _ := s then
          if tutorialCode.contains p then
            pure <| some (p, ← LocalToC.ofPage #[p] x)
          else pure none
        else pure none)
    else pure {}

  let extraParams := fun
    | #[p] =>
      if let some (zipFile, live?) := tutorialCode[p]? then
        if let some toc := tutorialTocs[p]? then
          Blog.Template.Params.ofList [("tutorialNav", tutorialNavHtml zipFile live? toc)]
        else {}
      else {}
    | _ => {}

  let theme := (← read).theme
  liftGenerate (site.generate theme) site blogState (extraParams := extraParams)


  writeFile (dir / "-verso-docs.json") (toString (← getThe <| Code.Hover.State _).dedup.docJson)

  for (filename, contents, srcMap?) in blogState.jsFiles do
    let filename := (dir / "-verso-data" / filename)
    filename.parent.forM (IO.FS.createDirAll ·)
    writeFile filename contents
    if let some m := srcMap? then
      let filename := (dir / "-verso-data" / m.1)
      filename.parent.forM (IO.FS.createDirAll ·)
      writeFile filename m.2
  for (filename, contents) in theme.cssFiles ++ blogState.cssFiles  do
    let filename := (dir / "-verso-data" / filename)
    filename.parent.forM (IO.FS.createDirAll ·)
    writeFile filename contents

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

open Verso.Output.Html in
open Verso.Genre.Blog.Template in
def defaultTheme := { Blog.Theme.default with
  pageTemplate :=  do
    pure {{
      {{(← param? "tutorialNav").getD .empty}}
      <article>
        <h1>{{← param "title"}}</h1>
        {{← param "content"}}
      </article>
    }}
  cssFiles := #[("local-toc.css", localToCStyle)]
}

open scoped Verso.Genre.Blog.Template in
/--
Generates a tutorials site in HTML, based on `tutorials`.

* `args` should be the command-line arguments provided to `main`
* `theme` should be a theme for the blog genre. Tutorial pages are provided with an additional
  template parameter `"tutorialNav"` with local navigation and code links.
-/
def tutorialsMain (tutorials : Tutorials) (args : List String)
    (config : Config := {})
    (theme : Blog.Theme := defaultTheme)
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

    if config.verbose then IO.println "Updating remote data"
    let remoteContent ← updateRemotes false config.remoteConfigFile (if config.verbose then IO.println else fun _ => pure ())

    -- Emit HTML
    let ((), _) ← (emit tutorials).run config.toConfig logError state extensionImpls {} {} components theme remoteContent

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
