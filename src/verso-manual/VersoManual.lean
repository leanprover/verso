/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Doc
import Verso.Doc.Concrete
import Verso.Doc.TeX
import Verso.Doc.Html
import Verso.Output.TeX
import Verso.Output.Html
import Verso.Output.Html.CssVars
import Verso.Output.Html.KaTeX
import Verso.Output.Html.ElasticLunr
import Verso.Doc.Lsp
import Verso.Doc.Elab
import Verso.FS

import VersoSearch

import MultiVerso

import VersoManual.Basic
import VersoManual.TeX
import VersoManual.Html
import VersoManual.Html.Style
import VersoManual.Draft
import VersoManual.Index
import VersoManual.License
import VersoManual.Glossary
import VersoManual.Docstring
import VersoManual.WebAssets
import VersoManual.WordCount
import VersoManual.Linters
import VersoManual.LocalContents
import VersoManual.InlineLean
import VersoManual.ExternalLean
import VersoManual.Marginalia
import VersoManual.Bibliography
import VersoManual.Table

open Lean (Name NameMap Json ToJson FromJson quote)

open Std (HashMap)

open Verso.FS

open Verso.Doc Elab
open Verso.Multi
open Verso.Genre.Manual.TeX
open Verso.Genre.Manual.WordCount

open Verso.Code (LinkTargets)
open Verso.Code.Hover (Dedup State)
open Verso.ArgParse

namespace Verso.Genre

namespace Manual

defmethod Part.htmlSplit (part : Part Manual) : HtmlSplitMode :=
  part.metadata.map (·.htmlSplit) |>.getD .default

private structure RefInfo where
  canonicalName : String
  domain : Option Name
  remote : Option String
  resolvedDestination : Option String := none
deriving BEq, ToJson, FromJson

defmethod Part.htmlToc (part : Part Manual) : Bool :=
  part.metadata.map (·.htmlToc) |>.getD true

inline_extension Inline.ref (canonicalName : String) (domain : Option Name) (remote : Option String) (resolvedDestination : Option String := none) where
  data := ToJson.toJson (RefInfo.mk canonicalName domain remote resolvedDestination)
  traverse := fun _ info content => do
    match FromJson.fromJson? (α := RefInfo) info with
    | .error e =>
      logError e; pure none
    | .ok { canonicalName := name, domain, remote := none, resolvedDestination := none } =>
      let domain := domain.getD sectionDomain
      match (← get).resolveDomainObject domain name with
      | .error _ => return none
      | .ok dest =>
        return some <| .other (Inline.ref name (some domain) none (some dest.link)) content
    | .ok { canonicalName := name, domain, remote := some remote, resolvedDestination := none } =>
      let domain := domain.getD sectionDomain
      match (← get).resolveRemoteObject domain name remote with
      | .error _ => return none
      | .ok dest =>
        return some <| .other (Inline.ref name (some domain) (some remote) (some dest.link)) content
    | .ok {resolvedDestination := some _, ..} =>
      pure none
  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun go _ info content => do
      match FromJson.fromJson? (α := RefInfo) info with
      | .error e =>
        Html.HtmlT.logError e; content.mapM go
      | .ok { canonicalName := name, domain, remote := none, resolvedDestination := none } =>
        Html.HtmlT.logError ("No destination found for tag '" ++ name ++ "' in " ++ toString domain); content.mapM go
      | .ok { canonicalName := name, domain, remote := some remote, resolvedDestination := none } =>
        Html.HtmlT.logError ("No destination found for remote '" ++ remote ++ "' tag '" ++ name ++ "' in " ++ toString domain); content.mapM go
      | .ok {resolvedDestination := some dest, ..} =>
        pure {{<a href={{dest}}>{{← content.mapM go}}</a>}}

section
open Lean
variable {m} [Monad m] [MonadError m]

structure RoleArgs where
  canonicalName : String
  domain : Option Name
  remote : Option String := none

instance : FromArgs RoleArgs m where
  fromArgs :=
    RoleArgs.mk <$>
      .positional `canonicalName (ValDesc.string.as "canonical name (string literal)") <*>
      .named' `domain true <*>
      .named `remote stringOrName true
where
  stringOrName : ValDesc m String := {
    description := "remote name (string or identifier)"
    signature := .String ∪ .Ident
    get
      | .str s => pure s.getString
      | .name n => pure n.getId.toString
      | .num n => throwErrorAt n "Expected name or string literal, got {n.getNat}"
  }
end
/--
Inserts a reference to the provided tag.
-/
@[role]
def ref : RoleExpanderOf RoleArgs
  | {canonicalName, domain, remote}, content => do
    let content ← content.mapM elabInline
    ``(Inline.other (Inline.ref $(quote canonicalName) $(quote domain) $(quote remote)) #[$content,*])

block_extension Block.paragraph where
  traverse := fun _ _ _ => pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ go _ _ content => do
      pure <| {{<div class="paragraph">{{← content.mapM go}}</div>}}

/--
Indicates that all the block-level elements contained within the directive are a single logical
paragraph. In HTML output, they are rendered with less space between them, and LaTeX renders them as
a single paragraph (e.g. without extraneous indentation).
-/
@[directive]
def paragraph : DirectiveExpanderOf Unit
  | (), stxs => do
    let args ← stxs.mapM elabBlock
    ``(Block.other Block.paragraph #[ $[ $args ],* ])

structure Config where
  destination : System.FilePath := "_out"
  maxTraversals : Nat := 20
  htmlDepth := 2
  emitTeX : Bool := false
  emitHtmlSingle : Bool := false
  emitHtmlMulti : Bool := true
  wordCount : Option System.FilePath := none
  extraFiles : List (System.FilePath × String) := []
  /-- Extra CSS to be included inline into every `<head>` via `<script>` tags -/
  extraCss : List String := []
  /-- Extra JS to be included inline into every `<head>` via `<style>` tags -/
  extraJs : List String := []
  /-- Extra CSS to be written to the filesystem in the Verso data directory and loaded by each `<head>` -/
  extraCssFiles : Array (String × String) := #[]
  /-- Extra JS to be written to the filesystem in the Verso data directory and loaded by each `<head>` -/
  extraJsFiles : Array JsFile := #[]
  /-- Extra files to be placed in the Verso data directory -/
  extraDataFiles : Array (String × ByteArray) := #[]
  licenseInfo : List LicenseInfo := []
  /-- Extra elements to add to every page's `head` tag -/
  extraHead : Array Output.Html := #[]
  /-- Extra elements to add to every page's contents -/
  extraContents : Array Output.Html := #[]
  draft : Bool := false
  /-- The URL from which to draw the logo to show, if any -/
  logo : Option String := none
  /-- The URL that the logo should link to, if any (default is site root) -/
  logoLink : Option String := none
  /-- URL for source link -/
  sourceLink : Option String := none
  /-- URL for issue reports -/
  issueLink : Option String := none
  /-- Be verbose while generating output -/
  verbose : Bool := false
  /--
  How deep should the local table of contents on each non-leaf HTML page?
  `none` means "unlimited".
  -/
  sectionTocDepth : Option Nat := some 1
  /--
  How deep should the local table of contents on the root HTML page?
  `none` means "unlimited".
  -/
  rootTocDepth : Option Nat := some 1
  /--
  Location of the remote config file.
  -/
  remoteConfigFile : Option System.FilePath := none
  /--
  How to insert links in rendered code
  -/
  linkTargets : TraverseState → LinkTargets Manual.TraverseContext := TraverseState.localTargets


def ensureDir (dir : System.FilePath) : IO Unit := do
  if !(← dir.pathExists) then
    IO.FS.createDirAll dir
  if !(← dir.isDir) then
    throw (↑ s!"Not a directory: {dir}")

/--
Removes all parts that are specified as draft-only.
-/
partial def removeDraftParts (part : Part Manual) : Part Manual :=
  let sub := part.subParts.filter fun p =>
    if let some «meta» := p.metadata then
      !meta.draft
    else true
  {part with subParts := sub.map removeDraftParts }

def traverseMulti (depth : Nat) (path : Path) (part : Part Manual) : TraverseM (Part Manual) :=
  match depth with
  | 0 => Genre.traverse Manual part
  | d + 1 =>
    if part.htmlSplit == .never then
      Genre.traverse Manual part
    else
      withReader ({· with path := path : TraverseContext}) do
        let meta' ← Verso.Doc.Traverse.part (g := Manual) part
        let mut p := meta'.map ({ part with metadata := · }) |>.getD part
        if let some md := p.metadata then
          if let some p' ← Traverse.genrePart md p then
            p := p'
        let .mk title titleString «meta» content subParts := p
        let content' ← withReader (·.inPart p) <| content.mapM traverseBlock
        let subParts' ← withReader (·.inPart p) <| subParts.mapM fun p => do
          let path' := path.push (p.metadata.bind (·.file) |>.getD (p.titleString.sluggify.toString))
          withReader ({· with path := path' : TraverseContext}) (traverseMulti d path' p)
        pure <| .mk (← title.mapM traverseInline) titleString «meta» content' subParts'
where
  traverseInline := Verso.Doc.Genre.traverse.inline Manual
  traverseBlock := Verso.Doc.Genre.traverse.block Manual

def traverse (logError : String → IO Unit) (text : Part Manual) (config : Config) : ReaderT ExtensionImpls IO (Part Manual × TraverseState) := do
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
  let mut text := text
  if !config.draft then
    text := removeDraftParts text
  if config.verbose then
    IO.println "Initializing extensions"
  let extensionImpls ← readThe ExtensionImpls
  state := state
    |>.setDomainTitle sectionDomain "Sections or chapters of the manual"
    |>.addQuickJumpMapper sectionDomain sectionDomainMapper
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
    let (text', state') ← traverseMulti config.htmlDepth #[] text |>.run extensionImpls topCtxt state
    let endTime ← IO.monoMsNow
    if config.verbose then
      IO.println s!"  ... pass {i} completed in {endTime - startTime} ms"
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
    headerLevel := some ⟨0, by simp +arith [Array.size, List.length]⟩,
    logError := fun msg => logError msg
  }
  let authors := text.metadata.map (·.authors) |>.getD []
  let date := text.metadata.bind (·.date) |>.getD ""
  let ctxt := {logError}
  let frontMatter ← text.content.mapM (·.toTeX (opts, ctxt, state))
  let chapters ← text.subParts.mapM (·.toTeX (opts, ctxt, state))
  let dir := config.destination.join "tex"
  ensureDir dir
  let mut packages : Std.HashSet String := {}
  let mut preambleItems : Std.HashSet String := {}
  for (_, d) in (← read).blockDescrs do
    let some d := d.get? BlockDescr
      | continue
    packages := packages.insertMany d.usePackages
    preambleItems := preambleItems.insertMany d.preamble
  for (_, d) in (← read).inlineDescrs do
    let some d := d.get? InlineDescr
      | continue
    packages := packages.insertMany d.usePackages
    preambleItems := preambleItems.insertMany d.preamble
  withFile (dir.join "main.tex") .write fun h => do
    if config.verbose then
      IO.println s!"Saving {dir.join "main.tex"}"
    h.putStrLn (preamble text.titleString authors date packages.toList preambleItems.toList)
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
partial def toc (depth : Nat) (opts : Html.Options IO)
    (ctxt : TraverseContext)
    (state : TraverseState)
    (definitionIds : NameMap String)
    (linkTargets : LinkTargets Manual.TraverseContext) :
    Part Manual → StateT (State Html) (ReaderT ExtensionImpls IO) Html.Toc
  | .mk title sTitle «meta» _ sub => do
    let titleHtml ← Html.seq <$> title.mapM (Manual.toHtml (m := ReaderT ExtensionImpls IO) opts.lift ctxt state definitionIds linkTargets {} ·)

    let some {id := some id, ..} := «meta»
      | throw <| .userError s!"No ID for {sTitle} - {repr «meta»}"
    let some {htmlId := v, ..} := state.externalTags[id]?
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

    let children ← sub.mapM (fun p => toc depth' opts (ctxt'.inPart p) state definitionIds linkTargets p)
    pure {
      title := titleHtml,
      shortTitle := meta.bind (·.shortTitle) |>.map Html.ofString,
      path := ctxt'.path,
      id := v.toString,
      sectionNum := ctxt.sectionNumber.mapM _root_.id,
      children := children.toList
    }

partial def sortJs (extraJs : Array (Bool × StaticJsFile)) : Array (Bool × StaticJsFile) :=
  helper #[] extraJs
where
  -- partial because library doesn't include that the sum of the size of the partitions is the size
  -- of the original
  helper (acc todo : Array (Bool × StaticJsFile)) : Array (Bool × StaticJsFile) :=
    if todo.isEmpty then acc
    else
      let (ok, notYet) := todo.partition (fun f => f.2.after.all (fun f' => acc.any (·.2.filename == f')))
      if ok.isEmpty then acc ++ todo
      else
        helper (acc ++ ok) notYet

def page (toc : List Html.Toc)
    (path : Path) (textTitle : String) (htmlBookTitle contents : Html)
    (state : TraverseState) (config : Config)
    (localItems : Array Html)
    (showNavButtons : Bool := true) (extraJs : List String := []) : Html :=
  let toc := {
    title := htmlBookTitle, path := #[], id := "" , sectionNum := some #[], children := toc
  }
  let extraJsFiles :=
    sortJs <|
      state.extraJsFiles.map (false, ·.toStaticJsFile)
  let extraJsFiles := extraJsFiles.map fun
    | (true, f) => (f.filename, f.defer)
    | (false, f) => ("/-verso-data/" ++ f.filename, f.defer)
  Html.page toc path textTitle htmlBookTitle contents
    -- The extraCss, extraJs, extraCssFiles, and extraJsFiles in the config are absent here
    -- because they are included in the traverse state when it is initialized
    state.extraCss (state.extraJs.insertMany extraJs)
    (showNavButtons := showNavButtons)
    (logo := config.logo)
    (logoLink := config.logoLink)
    (repoLink := config.sourceLink)
    (issueLink := config.issueLink)
    (localItems := localItems)
    (extraStylesheets := state.extraCssFiles.toList.map ("/-verso-data/" ++ ·.1))
    (extraJsFiles := extraJsFiles)
    (extraHead := config.extraHead)
    (extraContents := config.extraContents)

def relativizeLinks (html : Html) : Html :=
    -- Make all absolute URLS be relative to the site root, because that'll make them `<base>`-relative
    Html.relativize #[] html

open Output.Html in
def xref (toc : List Html.Toc) (xrefJson : String) (findJs : String) (state : TraverseState) (config : Config) : Html :=
  page toc #["find"] "Cross-Reference Redirection" "Cross-Reference Redirection" {{
    <section>
      <h1 id="title"></h1>
      <div id="message"></div>
    </section>
  }}
  state
  config
  (localItems := #[])
  (extraJs := [s!"let xref = {xrefJson};\n" ++ findJs])

def emitXrefs (toc : List Html.Toc) (dir : System.FilePath) (state : TraverseState) (config : Config) : IO Unit := do
  let out := xrefJson state.domains state.externalTags
  ensureDir dir
  let xrefJson := toString out
  IO.FS.writeFile (dir.join "xref.json") xrefJson
  ensureDir (dir / "find")
  IO.FS.writeFile (dir / "find" / "index.html") (Html.doctype ++ (relativizeLinks <| xref toc xrefJson find.js state config).asString)

section
open Search

def emitSearchIndex (dir : System.FilePath) (state : TraverseState) (ctx : TraverseContext) (logError : String → IO Unit) (doc : Part Manual) : IO Unit := do
  have : Indexable Manual := {
    partHeader p := do
      let ctxt ← IndexM.traverseContext
      let num :=  (← IndexM.traverseContext).inPart p |>.headers |>.map (·.metadata.bind (·.assignedNumber))
      let num :=
        if h : num.size > 1 then
          if num[0].isNone then num.extract 1 else num
        else num
      let num := num.mapM id
      let num := num.map sectionNumberString
      pure <| num.map (· ++ " " ++ p.titleString)
    partShortContextName p := return p.metadata.bind (·.shortContextTitle)
    partId m := do
      let id ← m.id
      let link ← state.resolveId id
      pure link.link,
    block _ := none,
    inline _ := none
  }

  match Verso.Search.mkIndex doc ctx with
  | .error e => logError e; return ()
  | .ok index =>
    -- Split the index into roughly 150k chunks for faster loading
    let (index, docs) := index.extractDocs
    let size := docs.foldl (init := 0) (fun s _ v => s + v.size)
    let mut docBuckets : HashMap UInt8 (HashMap String Doc) := {}
    for (ref, content) in docs do
      let h := bucket ref
      docBuckets := docBuckets.alter h fun v =>
        v.getD {} |>.insert ref content

    for (bucket, docs) in docBuckets do
      let docJson := docs.fold (init := Json.mkObj []) fun json k v => json.setObjVal! k (v.foldr (init := Json.mkObj []) fun k v js => js.setObjVal! k (Json.str v))
      IO.FS.writeFile (dir / s!"searchIndex_{bucket}.js") s!"window.docContents[{bucket}].resolve({docJson.compress});"

    let indexJs := "const __verso_searchIndexData = " ++ index.toJson.compress ++ ";\n\n"
    let indexJs := indexJs ++ "const __versoSearchIndex = elasticlunr ? elasticlunr.Index.load(__verso_searchIndexData) : null;\n"
    let indexJs := indexJs ++ "window.docContents = {};\n"
    let indexJs := indexJs ++ "window.searchIndex = elasticlunr ? __versoSearchIndex : null;\n"
    IO.FS.writeFile (dir / "searchIndex.js") indexJs

    IO.FS.writeFile (dir / "elasticlunr.min.js") Verso.Output.Html.elasticlunr.js

where
  -- Not using a proper hash because this needs to be implemented identically in JS
  bucket (s : String) : UInt8 := Id.run do
    let mut hash := 0
    let mut n := 0
    while h : n < s.utf8ByteSize do
      hash := hash + s.getUtf8Byte n h
      n := n + 1
    return hash


def emitSearchBox (dir : System.FilePath) (domains : DomainMappers) : IO Unit := do
  ensureDir dir
  for (file, contents) in searchBoxCode do
    IO.FS.writeBinFile (dir / file) contents
  IO.FS.writeFile (dir / "domain-mappers.js") (domains.toJs.pretty (width := 70))
  IO.FS.writeFile (dir / "domain-display.css") domains.quickJumpCss

end

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
    (text : Part Manual) : ReaderT ExtensionImpls IO (Part Manual × TraverseState) := do
  let dir := config.destination.join "html-single"
  ensureDir dir
  let ((text, state), htmlState) ← emitContent dir .empty
  IO.FS.writeFile (dir.join "-verso-docs.json") (toString htmlState.dedup.docJson)
  emitSearchBox (dir / "-verso-search") state.quickJump
  emitSearchIndex (dir / "-verso-search") state {logError, draft := config.draft} logError text
  pure (text, state)
where
  emitContent (dir : System.FilePath) : StateT (State Html) (ReaderT ExtensionImpls IO) (Part Manual × TraverseState) := do
    let (text, state) ← traverse logError text {config with htmlDepth := 0}
    let authors := text.metadata.map (·.authors) |>.getD []
    let authorshipNote := text.metadata.bind (·.authorshipNote)
    let _date := text.metadata.bind (·.date) |>.getD "" -- TODO
    let opts : Html.Options IO := {logError := fun msg => logError msg}
    let ctxt := {logError}
    let definitionIds := state.definitionIds ctxt
    let linkTargets := config.linkTargets state
    let titleHtml ← Html.seq <$> text.title.mapM (Manual.toHtml opts.lift ctxt state definitionIds linkTargets {})
    let introHtml ← Html.seq <$> text.content.mapM (Manual.toHtml opts.lift ctxt state definitionIds linkTargets {})
    let bookToc ← text.subParts.mapM (fun p => toc 0 opts (ctxt.inPart p) state definitionIds linkTargets p)
    let bookTocHtml := open Verso.Output.Html in
      if bookToc.size > 0 then {{
        <section>
        <h2>"Table of Contents"</h2>
        <ol class="section-toc">{{bookToc.map (·.html config.rootTocDepth)}}</ol>
        </section>
      }} else .empty
    let contents ←
      Html.seq <$>
      text.subParts.mapM fun p =>
        Manual.toHtml {opts.lift with headerLevel := 2} (ctxt.inPart p) state definitionIds linkTargets {} p
    let pageContent := open Verso.Output.Html in
      {{<section>
          {{Html.titlePage titleHtml authors authorshipNote introHtml}}
          {{bookTocHtml}}
          {{contents}}
        </section>}}
    let toc := (← text.subParts.mapM (toc 0 opts ctxt state definitionIds linkTargets)).toList
    let thisPageToc : Array Html ← do
      let (errs, items) ← localContents opts.lift ctxt state text
      for e in errs do logError e
      pure <| items.map (·.toHtml)
    emitXrefs toc dir state config
    IO.FS.withFile (dir.join "verso-vars.css") .write fun h => do
      h.putStrLn Html.«verso-vars.css»
    IO.FS.withFile (dir.join "book.css") .write fun h => do
      h.putStrLn Html.Css.pageStyle
    for (src, dest) in config.extraFiles do
      copyRecursively logError src (dir.join dest)
    for f in state.extraJsFiles do
      ensureDir (dir.join "-verso-data")
      (dir / "-verso-data" / f.filename).parent |>.forM fun d => ensureDir d
      IO.FS.writeFile (dir / "-verso-data" / f.filename) f.contents
      if let some m := f.sourceMap? then
        IO.FS.writeFile (dir / "-verso-data" / m.filename) m.contents
    let titleToShow : Html :=
      open Verso.Output.Html in
      if let some alt := text.metadata.bind (·.shortTitle) then
        alt
      else titleHtml
    for (name, contents) in state.extraCssFiles do
      ensureDir (dir.join "-verso-data")
      (dir / "-verso-data" / name).parent |>.forM fun d => ensureDir d
      IO.FS.withFile (dir.join "-verso-data" |>.join name) .write fun h => do
        h.putStr contents
    for (name, contents) in config.extraDataFiles do
      ensureDir (dir.join "-verso-data")
      (dir / "-verso-data" / name).parent |>.forM fun d => ensureDir d
      IO.FS.writeBinFile (dir.join "-verso-data" |>.join name) contents

    IO.FS.withFile (dir.join "index.html") .write fun h => do
      if config.verbose then
        IO.println s!"Saving {dir.join "index.html"}"
      h.putStrLn Html.doctype
      h.putStrLn <| Html.asString <| relativizeLinks <|
        page toc ctxt.path text.titleString titleToShow pageContent state config thisPageToc (showNavButtons := false)
    pure (text, state)

open Verso.Output.Html in
def emitHtmlMulti (logError : String → IO Unit) (config : Config)
    (text : Part Manual) : ReaderT ExtensionImpls IO (Part Manual × TraverseState) := do
  let root := config.destination.join "html-multi"
  ensureDir root
  let ((text, state), htmlState) ← emitContent root {}
  IO.FS.writeFile (root.join "-verso-docs.json") (toString htmlState.dedup.docJson)
  emitSearchBox (root / "-verso-search") state.quickJump
  emitSearchIndex (root / "-verso-search") state {logError, draft := config.draft} logError text
  pure (text, state)
where
  /--
  Emits the data used by all pages in the site, such as JS and CSS, and then emits the root page
  (and thus its children).
  -/
  emitContent (root : System.FilePath) : StateT (State Html) (ReaderT ExtensionImpls IO) (Part Manual × TraverseState) := do
    let (text, state) ← traverse logError text config
    let authors := text.metadata.map (·.authors) |>.getD []
    let authorshipNote := text.metadata >>= (·.authorshipNote)
    let _date := text.metadata.bind (·.date) |>.getD "" -- TODO
    let opts : Html.Options IO := {logError := fun msg => logError msg}
    let ctxt := {logError}
    let definitionIds := state.definitionIds ctxt
    let linkTargets := config.linkTargets state
    let toc ← text.subParts.toList.mapM fun p =>
      toc config.htmlDepth opts (ctxt.inPart p) state definitionIds linkTargets p
    let titleHtml ← Html.seq <$> text.title.mapM (Manual.toHtml opts.lift ctxt state definitionIds linkTargets {} ·)
    let titleToShow : Html :=
      open Verso.Output.Html in
      if let some alt := text.metadata.bind (·.shortTitle) then
        alt
      else titleHtml
    IO.FS.withFile (root.join "verso-vars.css") .write fun h => do
      h.putStrLn Html.«verso-vars.css»
    IO.FS.withFile (root.join "book.css") .write fun h => do
      h.putStrLn Html.Css.pageStyle
    for (src, dest) in config.extraFiles do
      copyRecursively logError src (root.join dest)
    for f in state.extraJsFiles do
      ensureDir (root.join "-verso-data")
      (root / "-verso-data" / f.filename).parent |>.forM fun d => ensureDir d
      IO.FS.writeFile (root.join "-verso-data" |>.join f.filename) f.contents
      if let some m := f.sourceMap? then
        IO.FS.writeFile (root.join "-verso-data" |>.join m.filename) m.contents
    for (name, contents) in state.extraCssFiles do
      ensureDir (root.join "-verso-data")
      (root / "-verso-data" / name).parent |>.forM fun d => ensureDir d
      IO.FS.withFile (root.join "-verso-data" |>.join name) .write fun h => do
        h.putStr contents
    for (name, contents) in config.extraDataFiles do
      ensureDir (root.join "-verso-data")
      (root / "-verso-data" / name).parent |>.forM fun d => ensureDir d
      IO.FS.writeBinFile (root.join "-verso-data" |>.join name) contents

    emitPart titleToShow authors authorshipNote toc opts.lift ctxt state definitionIds linkTargets {} true config.htmlDepth root text
    emitXrefs toc root state config
    pure (text, state)
  /--
  Emits HTML for a given part, and its children if the splitting threshold is not yet reached.
  -/
  emitPart (bookTitle : Html) (authors : List String) (authorshipNote : Option String) (bookContents)
      (opts ctxt state definitionIds linkTargets codeOptions)
      (root : Bool) (depth : Nat) (dir : System.FilePath) (part : Part Manual) : StateT (State Html) (ReaderT ExtensionImpls IO) Unit := do
    let thisFile := part.metadata.bind (·.file) |>.getD (part.titleString.sluggify.toString)
    let dir := if root then dir else dir.join thisFile
    let sectionNum := sectionHtml ctxt
    let pageTitleHtml := sectionNum ++ (← Html.seq <$> part.title.mapM (Manual.toHtml opts.lift ctxt state definitionIds linkTargets codeOptions))
    let titleHtml :=
      pageTitleHtml ++
      if let some id := part.metadata.bind (·.id) then
        permalink id state
      else .empty
    let introHtml ← Html.seq <$> part.content.mapM (Manual.toHtml opts.lift ctxt state definitionIds linkTargets codeOptions)
    let contents ←
      if depth == 0 || part.htmlSplit == .never then
        Html.seq <$> part.subParts.mapM (fun p => Manual.toHtml {opts.lift with headerLevel := 2} (ctxt.inPart p) state definitionIds linkTargets codeOptions p)
      else pure .empty

    let includeSubparts := if (depth == 0 || part.htmlSplit == .never) then .all else .depth 0
    let thisPageToc : Array LocalContentItem ← do
      let (errs, items) ← localContents opts.lift ctxt state (includeTitle := false) (includeSubparts := includeSubparts) part
      for e in errs do logError e
      pure items

    -- If there's no elements, then get rid of the contents entirely. This causes the ToC generation code in the HTML to fall back to the ordinary collapsible ones.
    -- These look inconsistent if there's no non-section elements.
    let thisPageToc := if thisPageToc.filter (·.header?.isNone) |>.isEmpty then #[] else thisPageToc

    let thisPageToc : Array Html := thisPageToc.map (·.toHtml)

    let subToc ← part.subParts.mapM (fun p => toc depth opts (ctxt.inPart p) state definitionIds linkTargets p)
    let pageContent :=
      if root then
        let subTocHtml := if subToc.size > 0 then {{
            <section>
            <h2>"Contents"</h2>
            <ol class="section-toc">{{subToc.map (·.html config.rootTocDepth)}}</ol>
            </section>
          }}
        else .empty
        {{<section>{{Html.titlePage titleHtml authors authorshipNote introHtml ++ contents}} {{subTocHtml}}</section>}}
      else
        let subTocHtml :=
          if (depth > 0 && part.htmlSplit != .never) && subToc.size > 0 && part.htmlToc then
            {{<ol class="section-toc">{{subToc.map (·.html config.sectionTocDepth)}}</ol>}}
          else .empty
        {{<section><h1>{{titleHtml}}</h1> {{introHtml}} {{contents}} {{subTocHtml}}</section>}}

    ensureDir dir
    IO.FS.withFile (dir.join "index.html") .write fun h => do
      if config.verbose then
        IO.println s!"Saving {dir.join "index.html"}"
      h.putStrLn Html.doctype
      h.putStrLn <| Html.asString <| relativizeLinks <|
        page bookContents ctxt.path part.titleString bookTitle pageContent state config thisPageToc
    if depth > 0 ∧ part.htmlSplit != .never then
      for p in part.subParts do
        let nextFile := p.metadata.bind (·.file) |>.getD (p.titleString.sluggify.toString)
        emitPart bookTitle authors authorshipNote bookContents opts ({ctxt with path := ctxt.path.push nextFile}.inPart p) state definitionIds linkTargets {} false (depth - 1) dir p
  termination_by depth


open Verso.Output.Html in
/--
Adds a bundled version of KaTeX to the document
-/
def Config.addKaTeX (config : Config) : Config :=
  {config with
    extraCssFiles := config.extraCssFiles.push ("katex/katex.css", katex.css),
    extraJsFiles :=
      config.extraJsFiles
        |>.push {filename := "katex/katex.js", contents := katex.js, sourceMap? := none}
        |>.push {filename := "katex/math.js", contents := math.js, sourceMap? := none},
    extraDataFiles := config.extraDataFiles ++ katexFonts,
    licenseInfo := Licenses.KaTeX :: config.licenseInfo
  }


/--
Adds search dependencies to the configuration
-/
def Config.addSearch (config : Config) : Config :=
  { config with
    licenseInfo := [Licenses.fuzzysort, Licenses.w3Combobox, Licenses.elasticlunr.js] ++ config.licenseInfo
  }


inductive Mode where | single | multi

/--
Extra steps to be performed after building the manual.

`ExtraStep` is short for `Mode → (String → IO Unit) → Config → TraverseState → Part Manual → IO Unit`.

The parameters are:
 * A mode, which is whether the HTML was generated in one or multiple files
 * An error logger
 * The configuration, as determined from the initial value passed to `manualMain` and modified via the command line
 * The final state of the traversal pass
 * The final text, post-traversal
-/
abbrev ExtraStep := Mode → (String → IO Unit) → Config → TraverseState → Part Manual → IO Unit


def manualMain (text : Part Manual)
    (extensionImpls : ExtensionImpls := by exact extension_impls%)
    (options : List String)
    (config : Config := Config.addKaTeX (Config.addSearch {}))
    (extraSteps : List ExtraStep := []) : IO UInt32 :=
  ReaderT.run go extensionImpls

where
  opts (cfg : Config) : List String → ReaderT ExtensionImpls IO Config
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
    | ("--verbose"::more) => opts {cfg with verbose := true} more
    | (other :: _) => throw (↑ s!"Unknown option {other}")
    | [] => pure cfg

  fixBase (base : String) : String :=
    if base.takeRight 1 != "/" then base ++ "/" else base

  go : ReaderT ExtensionImpls IO UInt32 := do
    let hasError ← IO.mkRef false
    let logError msg := do hasError.set true; IO.eprintln msg
    let cfg ← opts config options

    if cfg.emitTeX then
      if cfg.verbose then
        IO.println s!"Saving TeX"
      emitTeX logError cfg text
    if cfg.emitHtmlSingle then
      if cfg.verbose then
        IO.println s!"Saving single-page HTML"
      let (text', traverseState) ← emitHtmlSingle logError cfg text
      for step in extraSteps do
        step .single logError config traverseState text'
    if cfg.emitHtmlMulti then
      if cfg.verbose then
        IO.println s!"Saving multi-page HTML"
      let (text', traverseState) ← emitHtmlMulti logError cfg text
      if cfg.verbose then IO.println s!"Executing {extraSteps.length} extra steps"
      for step in extraSteps do
        step .multi logError config traverseState text'
    if let some wcFile := cfg.wordCount then
      if cfg.verbose then
        IO.println s!"Saving word counts to {wcFile}"
      wordCount wcFile logError cfg text

    if (← hasError.get) then
      IO.eprintln "Errors were encountered!"
      return 1
    else
      return 0
