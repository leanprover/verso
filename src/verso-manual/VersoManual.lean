/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Doc
import Verso.Doc.Concrete
import Verso.Doc.TeX
import Verso.Doc.Html
import Verso.Output.TeX
import Verso.Output.Html
import Verso.Doc.Lsp
import Verso.Doc.Elab
import Verso.FS

import VersoManual.Basic
import VersoManual.Slug
import VersoManual.TeX
import VersoManual.Html
import VersoManual.Html.Style
import VersoManual.Draft
import VersoManual.Index
import VersoManual.Glossary
import VersoManual.Docstring
import VersoManual.WebAssets
import VersoManual.WordCount

open Lean (Name NameMap Json ToJson FromJson)

open Verso.FS

open Verso.Doc Elab

open Verso.Genre.Manual.TeX
open Verso.Genre.Manual.WordCount

open Verso.Code (LinkTargets)
open Verso.Code.Hover (Dedup State)

namespace Verso.Genre

namespace Manual

defmethod Part.htmlSplit (part : Part Manual) : HtmlSplitMode :=
  part.metadata.map (·.htmlSplit) |>.getD .default


def Inline.ref : Inline where
  name := `Verso.Genre.Manual.Inline.ref

@[inline_extension Inline.ref]
def ref.descr : InlineDescr where
  traverse := fun _ info content => do

    match FromJson.fromJson? (α := String × Option Name × Option String) info with
    | .error e =>
      logError e; pure none
    | .ok (name, domain, none) =>
      let domain := domain.getD sectionDomain
      match (← get).resolveDomainObject domain name with
      | .error _ => return none
      | .ok (path, htmlId) =>
        let dest := path.link (some htmlId.toString)
        return some <| .other {Inline.ref with data := ToJson.toJson (name, some domain, some dest)} content
    | .ok (_, domain, some (dest : String)) =>
      pure none

  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun go _ info content => do
      match FromJson.fromJson? (α := String × Option Name × Option String) info with
      | .error e =>
        Html.HtmlT.logError e; content.mapM go
      | .ok (name, domain, none) =>
        Html.HtmlT.logError ("No destination found for tag '" ++ name ++ "' in " ++ toString domain); content.mapM go
      | .ok (_, _, some dest) =>
        pure {{<a href={{dest}}>{{← content.mapM go}}</a>}}

def ref (content : Array (Doc.Inline Manual)) (canonicalName : String) (domain : Option Name := none) : Doc.Inline Manual :=
  let data : (String × Option Name × Option String) := (canonicalName, domain, none)
  .other {Inline.ref with data := ToJson.toJson data} content

def Block.paragraph : Block where
  name := `Verso.Genre.Manual.Block.paragraph

@[block_extension Block.paragraph]
def paragraph.descr : BlockDescr where
  traverse := fun _ _ _ => pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ go _ _ content => do
      pure <| {{<div class="paragraph">{{← content.mapM go}}</div>}}

@[directive_expander paragraph]
def paragraph : DirectiveExpander
  | #[], stxs => do
    let args ← stxs.mapM elabBlock
    let val ← ``(Block.other Block.paragraph #[ $[ $args ],* ])
    pure #[val]
  | _, _ => Lean.Elab.throwUnsupportedSyntax


structure Config where
  destination : System.FilePath := "_out"
  maxTraversals : Nat := 20
  htmlDepth := 0
  emitTeX : Bool := true
  emitHtmlSingle : Bool := true
  emitHtmlMulti : Bool := true
  wordCount : Option System.FilePath := none
  extraFiles : List (System.FilePath × String) := []
  extraCss : List String := []
  extraJs : List String := []
  draft : Bool := false
  /-- The URL from which to draw the logo to show, if any -/
  logo : Option String := none

def ensureDir (dir : System.FilePath) : IO Unit := do
  if !(← dir.pathExists) then
    IO.FS.createDirAll dir
  if !(← dir.isDir) then
    throw (↑ s!"Not a directory: {dir}")

def traverseMulti (depth : Nat) (path : Path) (part : Part Manual) : TraverseM (Part Manual) :=
  match depth with
  | 0 => Genre.traverse Manual part
  | d + 1 =>
    if part.htmlSplit == .never then
      Genre.traverse Manual part
    else
      withReader ({· with path := path : TraverseContext}) do
        let meta' ← Verso.Doc.Traverse.part (g := Manual) part
        let mut p := meta'.map part.withMetadata |>.getD part
        if let some md := p.metadata then
          if let some p' ← Traverse.genrePart md p then
            p := p'
        let .mk title titleString meta content subParts := p
        let content' ← withReader (·.inPart p) <| content.mapM traverseBlock
        let subParts' ← withReader (·.inPart p) <| subParts.mapM fun p => do
          let path' := path.push (p.metadata.bind (·.file) |>.getD (p.titleString.sluggify.toString))
          withReader ({· with path := path' : TraverseContext}) (traverseMulti d path' p)
        pure <| .mk (← title.mapM traverseInline) titleString meta content' subParts'
where
  traverseInline := Verso.Doc.Genre.traverse.inline Manual
  traverseBlock := Verso.Doc.Genre.traverse.block Manual

def traverse (logError : String → IO Unit) (text : Part Manual) (config : Config) : ReaderT ExtensionImpls IO (Part Manual × TraverseState) := do
  let topCtxt : Manual.TraverseContext := {logError, draft := config.draft}
  let mut state : Manual.TraverseState := {}
  let mut text := text
  let extensionImpls ← readThe ExtensionImpls
  state := state.setDomainTitle sectionDomain "Sections or chapters of the manual"
  for ⟨_, b⟩ in extensionImpls.blockDescrs do
    if let some descr := b.get? BlockDescr then
      state := descr.init state
  for ⟨_, i⟩ in extensionImpls.inlineDescrs do
    if let some descr := i.get? InlineDescr then
      state := descr.init state
  for _ in [0:config.maxTraversals] do
    let (text', state') ← traverseMulti config.htmlDepth #[] text |>.run extensionImpls topCtxt state
    if text' == text && state' == state then
      return (text', state')
    else
      state := state'
      text := text'
  return (text, state)



open IO.FS in
def emitTeX (logError : String → IO Unit) (config : Config) (text : Part Manual) : ReaderT ExtensionImpls IO Unit := do
  let (text, state) ← traverse logError text config
  let opts : TeX.Options Manual (ReaderT ExtensionImpls IO) := {
    headerLevels := #["chapter", "section", "subsection", "subsubsection", "paragraph"],
    headerLevel := some ⟨0, by simp_arith [Array.size, List.length]⟩,
    logError := fun msg => logError msg
  }
  let authors := text.metadata.map (·.authors) |>.getD []
  let date := text.metadata.bind (·.date) |>.getD ""
  let ctxt := {logError}
  let frontMatter ← text.content.mapM (·.toTeX (opts, ctxt, state))
  let chapters ← text.subParts.mapM (·.toTeX (opts, ctxt, state))
  let dir := config.destination.join "tex"
  ensureDir dir
  withFile (dir.join "main.tex") .write fun h => do
    h.putStrLn (preamble text.titleString authors date)
    if frontMatter.size > 0 then
      h.putStrLn "\\chapter*{Introduction}"
    for b in frontMatter do
      h.putStrLn b.asString
    for c in chapters do
      h.putStrLn c.asString
    h.putStrLn postamble

open Verso.Output (Html)

instance : Inhabited (StateT (State Html) (ReaderT ExtensionImpls IO) Html.Toc) where
  default := fun _ => default


/--
Generate a ToC structure for a document.

Here, `depth` is the current depth at which pages no longer recieve their own HTML files, not the
depth of the table of contents in the document (which is controlled by a parameter to `Toc.html`).
-/
partial def toc (depth : Nat) (opts : Html.Options Manual IO)
    (ctxt : TraverseContext)
    (state : TraverseState)
    (linkTargets : LinkTargets) :
    Part Manual → StateT (State Html) (ReaderT ExtensionImpls IO) Html.Toc
  | .mk title sTitle meta _ sub => do
    let titleHtml ← Html.seq <$> title.mapM (Manual.toHtml (m := ReaderT ExtensionImpls IO) opts.lift ctxt state linkTargets {} ·)
    let some {id := some id, ..} := meta
      | throw <| .userError s!"No ID for {sTitle} - {repr meta}"
    let some (_, v) := state.externalTags[id]?
      | throw <| .userError s!"No external ID for {sTitle}"

    let ctxt' :=
      -- When depth is 0 or we reach an unsplittable part, no more HTML files will be generated
      if depth > 0 then
        {ctxt with path := ctxt.path.push (meta.bind (·.file) |>.getD (sTitle.sluggify.toString))}
      else ctxt

    let splitPolicy := meta.map (·.htmlSplit) |>.getD .default
    let depth' := match splitPolicy with
      | .default => depth - 1
      | .never => 0

    let children ← sub.mapM (fun p => toc depth' opts (ctxt'.inPart p) state linkTargets p)
    pure <| .entry titleHtml ctxt'.path v.toString (ctxt.sectionNumber.mapM _root_.id) children

def page (toc : Array Html.Toc) (path : Path) (textTitle : String) (htmlTitle contents : Html) (state : TraverseState) (config : Config) (extraJs : List String := []) : Html :=
  let toc := .entry htmlTitle #[] "" (some #[]) toc
  Html.page toc path textTitle htmlTitle contents
    state.extraCss (state.extraJs.insertMany extraJs)
    (logo := config.logo)
    (extraStylesheets := config.extraCss ++ state.extraCssFiles.toList.map ("/-verso-css/" ++ ·.1))
    (extraJsFiles := config.extraJs.toArray ++ state.extraJsFiles.map ("/-verso-js/" ++ ·.1))

open Output.Html in
def xref (toc : Array Html.Toc) (xrefJson : String) (findJs : String) (state : TraverseState) (config : Config) : Html :=
  page toc #["find"] "Cross-Reference Redirection" "Cross-Reference Redirection" {{
    <section>
      <h1 id="title"></h1>
      <div id="message"></div>
    </section>
  }}
  state
  config
  (extraJs := [s!"let xref = {xrefJson};\n" ++ findJs])

def emitXrefs (toc : Array Html.Toc) (dir : System.FilePath) (state : TraverseState) (config : Config) : IO Unit := do
  let mut out : Json := Json.mkObj []
  for (n, dom) in state.domains do
    out := out.setObjVal! n.toString <| Json.mkObj [
      ("title", Json.str <| dom.title.getD n.toString),
      ("description", dom.description.map Json.str |>.getD Json.null),
      ("contents", Json.mkObj <| dom.objects.toList.map fun (x, y) =>
        (x, ToJson.toJson <| y.ids.toList.filterMap (jsonRef y.data <$> state.externalTags[·]?)))]
  ensureDir dir
  let xrefJson := toString out
  IO.FS.writeFile (dir.join "xref.json") xrefJson
  ensureDir (dir / "find")
  IO.FS.writeFile (dir / "find" / "index.html") (Html.doctype ++ (Html.relativize #["find"] <| xref toc xrefJson find.js state config).asString)
where
  jsonRef (data : Json) (ref : Path × Slug) : Json :=
    Json.mkObj [("address", String.join (ref.1.map ("/" ++ ·)).toList), ("id", ref.2.toString), ("data", data)]

def wordCount
    (wcPath : System.FilePath)
    (logError : String → IO Unit) (config : Config)
    (text : Part Manual) : ReaderT ExtensionImpls IO Unit := do
  let (text, _) ← traverse logError text config
  IO.FS.writeFile wcPath (wordCountReport skip "" 2 text |>.snd)
where
  -- Skip included docstrings for word count purposes
  skip n := [`Verso.Genre.Manual.Block.docstring].contains n

def emitHtmlSingle
    (logError : String → IO Unit) (config : Config)
    (text : Part Manual) : ReaderT ExtensionImpls IO Unit := do
  let dir := config.destination.join "html-single"
  ensureDir dir
  let ((), st) ← emitContent dir .empty
  IO.FS.writeFile (dir.join "-verso-docs.json") (toString st.dedup.docJson)
where
  emitContent (dir : System.FilePath) : StateT (State Html) (ReaderT ExtensionImpls IO) Unit := do
    let (text, state) ← traverse logError text {config with htmlDepth := 0}
    let authors := text.metadata.map (·.authors) |>.getD []
    let date := text.metadata.bind (·.date) |>.getD ""
    let opts : Html.Options Manual IO := {logError := fun msg => logError msg}
    let ctxt := {logError}
    let titleHtml ← Html.seq <$> text.title.mapM (Manual.toHtml opts.lift ctxt state state.linkTargets {})
    let introHtml ← Html.seq <$> text.content.mapM (Manual.toHtml opts.lift ctxt state state.linkTargets {})
    let contents ← Html.seq <$> text.subParts.mapM (Manual.toHtml {opts.lift with headerLevel := 2} ctxt state state.linkTargets {} ·)
    let pageContent := open Verso.Output.Html in
      {{<section>{{Html.titlePage titleHtml authors introHtml ++ contents}}</section>}}
    let toc ← text.subParts.mapM (toc 0 opts ctxt state state.linkTargets)
    emitXrefs toc dir state config
    IO.FS.withFile (dir.join "book.css") .write fun h => do
      h.putStrLn Html.Css.pageStyle
    for (src, dest) in config.extraFiles do
      copyRecursively logError src (dir.join dest)
    for (name, contents) in state.extraJsFiles do
      ensureDir (dir.join "-verso-js")
      IO.FS.withFile (dir.join "-verso-js" |>.join name) .write fun h => do
        h.putStr contents
    for (name, contents) in state.extraCssFiles do
      ensureDir (dir.join "-verso-css")
      IO.FS.withFile (dir.join "-verso-css" |>.join name) .write fun h => do
        h.putStr contents
    IO.FS.withFile (dir.join "index.html") .write fun h => do
      h.putStrLn Html.doctype
      h.putStrLn (page toc ctxt.path text.titleString titleHtml pageContent state config).asString

open Verso.Output.Html in
def emitHtmlMulti (logError : String → IO Unit) (config : Config)
    (text : Part Manual) : ReaderT ExtensionImpls IO Unit := do
  let root := config.destination.join "html-multi"
  ensureDir root
  let ((), st) ← emitContent root {}
  IO.FS.writeFile (root.join "-verso-docs.json") (toString st.dedup.docJson)
where
  emitContent (root : System.FilePath) : StateT (State Html) (ReaderT ExtensionImpls IO) Unit := do
    let (text, state) ← traverse logError text config
    let authors := text.metadata.map (·.authors) |>.getD []
    let date := text.metadata.bind (·.date) |>.getD ""
    let opts : Html.Options _ IO := {logError := fun msg => logError msg}
    let ctxt := {logError}
    let toc ← text.subParts.mapM (fun p => toc config.htmlDepth opts (ctxt.inPart p) state state.linkTargets p)
    let titleHtml ← Html.seq <$> text.title.mapM (Manual.toHtml opts.lift ctxt state state.linkTargets {} ·)
    IO.FS.withFile (root.join "book.css") .write fun h => do
      h.putStrLn Html.Css.pageStyle
    for (src, dest) in config.extraFiles do
      copyRecursively logError src (root.join dest)
    for (name, contents) in state.extraJsFiles do
      ensureDir (root.join "-verso-js")
      IO.FS.withFile (root.join "-verso-js" |>.join name) .write fun h => do
        h.putStr contents
    for (name, contents) in state.extraCssFiles do
      ensureDir (root.join "-verso-css")
      IO.FS.withFile (root.join "-verso-css" |>.join name) .write fun h => do
        h.putStr contents
    emitPart titleHtml authors toc opts.lift ctxt state state.linkTargets {} true config.htmlDepth root text
    emitXrefs toc root state config
  emitPart (bookTitle : Html) (authors : List String) (bookContents)
      (opts ctxt state linkTargets codeOptions)
      (root : Bool) (depth : Nat) (dir : System.FilePath) (part : Part Manual) : StateT (State Html) (ReaderT ExtensionImpls IO) Unit := do
    let thisFile := part.metadata.bind (·.file) |>.getD (part.titleString.sluggify.toString)
    let dir := if root then dir else dir.join thisFile
    let sectionNum := sectionHtml ctxt
    let titleHtml := sectionNum ++ (← Html.seq <$> part.title.mapM (Manual.toHtml opts.lift ctxt state linkTargets codeOptions))
    let introHtml ← Html.seq <$> part.content.mapM (Manual.toHtml opts.lift ctxt state linkTargets codeOptions)
    let contents ←
      if depth == 0 || part.htmlSplit == .never then
        Html.seq <$> part.subParts.mapM (fun p => Manual.toHtml {opts.lift with headerLevel := 2} (ctxt.inPart p) state linkTargets codeOptions p)
      else pure .empty
    let subToc ← part.subParts.mapM (fun p => toc depth opts (ctxt.inPart p) state linkTargets p)
    let pageContent :=
      if root then
        let subTocHtml := if subToc.size > 0 then {{<ol class="section-toc">{{subToc.map (·.html (some 2))}}</ol>}} else .empty
        {{<section>{{Html.titlePage titleHtml authors introHtml ++ contents}} {{subTocHtml}}</section>}}
      else
        let subTocHtml := if (depth > 0 && part.htmlSplit != .never) && subToc.size > 0 then {{<ol class="section-toc">{{subToc.map (·.html none)}}</ol>}} else .empty
        {{<section><h1>{{titleHtml}}</h1> {{introHtml}} {{contents}} {{subTocHtml}}</section>}}

    let pageTitle := if root then bookTitle else {{<a href="/">{{bookTitle}}</a>}}
    ensureDir dir
    IO.FS.withFile (dir.join "index.html") .write fun h => do
      h.putStrLn Html.doctype
      h.putStrLn (Html.relativize ctxt.path <| page bookContents ctxt.path part.titleString pageTitle pageContent state config).asString
    if depth > 0 ∧ part.htmlSplit != .never then
      for p in part.subParts do
        let nextFile := p.metadata.bind (·.file) |>.getD (p.titleString.sluggify.toString)
        emitPart bookTitle authors bookContents opts ({ctxt with path := ctxt.path.push nextFile}.inPart p) state linkTargets {} false (depth - 1) dir p
  termination_by depth



abbrev ExtraStep := TraverseContext → TraverseState → IO Unit


def manualMain (text : Part Manual)
    (extensionImpls : ExtensionImpls := by exact extension_impls%)
    (options : List String)
    (config : Config := {})
    (extraSteps : List ExtraStep := []) : IO UInt32 :=
  ReaderT.run go extensionImpls

where
  opts (cfg : Config)
    | ("--output"::dir::more) => opts {cfg with destination := dir} more
    | ("--depth"::n::more) => opts {cfg with htmlDepth := n.toNat!} more
    | ("--with-tex"::more) => opts {cfg with emitTeX := true} more
    | ("--without-tex"::more) => opts {cfg with emitTeX := false} more
    | ("--with-html-single"::more) => opts {cfg with emitHtmlSingle := true} more
    | ("--without-html-single"::more) => opts {cfg with emitHtmlSingle := false} more
    | ("--with-html-multi"::more) => opts {cfg with emitHtmlMulti := true} more
    | ("--without-html-multi"::more) => opts {cfg with emitHtmlMulti := false} more
    | ("--with-word-count"::file::more) => opts {cfg with wordCount := some file} more
    | ("--without-word-count"::more) => opts {cfg with wordCount := none} more
    | ("--draft"::more) => opts {cfg with draft := true} more
    | (other :: _) => throw (↑ s!"Unknown option {other}")
    | [] => pure cfg

  go : ReaderT ExtensionImpls IO UInt32 := do
    let hasError ← IO.mkRef false
    let logError msg := do hasError.set true; IO.eprintln msg
    let cfg ← opts config options

    if cfg.emitTeX then emitTeX logError cfg text
    if cfg.emitHtmlSingle then emitHtmlSingle logError cfg text
    if cfg.emitHtmlMulti then emitHtmlMulti logError cfg text
    if let some wcFile := cfg.wordCount then
      wordCount wcFile logError cfg text

    if (← hasError.get) then
      IO.eprintln "Errors were encountered!"
      return 1
    else
      return 0
