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
import Verso.Theme.Code
import Verso.Theme.Code.Defaults
import VersoManual.Theme
import VersoManual.Theme.Defaults
import VersoManual.Theme.Emit
import VersoManual.Theme.Assets
import Verso.Output.Html.KaTeX
import Verso.Output.Html.ElasticLunr
import Verso.Doc.Lsp
import Verso.Doc.Elab
import Verso.FS

import VersoSearch

import MultiVerso

import VersoManual.Basic
import VersoManual.TeX
import VersoManual.TeX.Config
import VersoManual.Html
import VersoManual.Html.Style
import VersoManual.Draft
import VersoManual.Imports
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
import VersoManual.Literate
import VersoManual.Marginalia
import VersoManual.Bibliography
import VersoManual.Row
import VersoManual.Diagrams
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
open Verso (Logger Severity withLogger BuildLogT)
open Verso.Theme (ThemeRegistry)

namespace Verso.Genre

namespace Manual

defmethod Part.htmlSplit (part : Part Manual) : HtmlSplitMode :=
  part.metadata.map (·.htmlSplit) |>.getD .default

private structure RefInfo where
  canonicalName : String
  domain : Option Name
  remote : Option String
  resolvedDestination : Option Link := none
deriving BEq, ToJson, FromJson

defmethod Part.htmlToc (part : Part Manual) : Bool :=
  part.metadata.map (·.htmlToc) |>.getD true

inline_extension Inline.ref (canonicalName : String) (domain : Option Name) (remote : Option String) (resolvedDestination : Option Link := none) where
  data := ToJson.toJson (RefInfo.mk canonicalName domain remote resolvedDestination)
  traverse := fun _ info content => do
    match FromJson.fromJson? (α := RefInfo) info with
    | .error e =>
      reportError e; pure none
    | .ok { canonicalName := name, domain, remote := none, resolvedDestination := none } =>
      let domain := domain.getD sectionDomain
      match (← get).resolveDomainObject domain name with
      | .error _ => return none
      | .ok dest =>
        return some <| .other (Inline.ref name (some domain) none (some dest)) content
    | .ok { canonicalName := name, domain := none, remote := some remote, resolvedDestination := none } =>
      return some <| .other (Inline.ref name (some sectionDomain) (some remote) none) content
    | .ok { resolvedDestination := some _, .. } | .ok { remote := some _, .. } =>
      pure none
  toTeX :=
    open Verso.Output.TeX in
    open Verso.Doc.TeX in
    some <| fun go _ info content => do
      match FromJson.fromJson? (α := RefInfo) info with
      | .error e =>
        reportError e; content.mapM go
      | .ok { canonicalName := name, domain, remote := none, resolvedDestination := none } =>
        reportError ("No destination found for tag '" ++ name ++ "' in " ++ toString domain); content.mapM go
      | .ok { canonicalName := name, domain, remote := some remote, resolvedDestination := none } =>
        reportError ("No destination found for remote '" ++ remote ++ "' tag '" ++ name ++ "' in " ++ toString domain); content.mapM go
      | .ok {resolvedDestination := some dest, remote, ..} =>
        if remote.isSome then
          -- Inter-document links should be URLs
          pure <| makeLink dest.link (← content.mapM go)
        else
          -- Intra-document links should be page references
          let label := labelForTeX dest.htmlId
          pure \TeX{\autoref{\Lean{label}}" (p."~\pageref{\Lean{label}} ")"}

  toHtml :=
    open Verso.Output.Html in
    some <| fun go _ info content => do
      match FromJson.fromJson? (α := RefInfo) info with
      | .error e =>
        reportError e; content.mapM go
      | .ok { canonicalName := name, domain, remote := none, resolvedDestination := none } =>
        reportError ("No destination found for tag '" ++ name ++ "' in " ++ toString domain); content.mapM go
      | .ok { canonicalName := name, domain, remote := some remote, resolvedDestination := _ } =>
        let domain := domain |>.getD sectionDomain
        let remoteData ← readThe AllRemotes
        if let some r := remoteData[remote]? then
          if let some dom := r.domains[domain]? then
            if let some objs := dom[name]? then
              if h : objs.size = 1 then
                let obj := objs[0]
                let dest := obj.link.link
                return {{<a href={{dest}} data-verso-remote={{remote}}>{{← content.mapM go}}</a>}}
              else
                let dests := objs.map (s!" * {·.link.link}") |>.toList |> "\n".intercalate
                reportError s!"Remote '{remote}' domain '{domain}' contains multiple destinations for '{name}':\n{dests}"
            else reportError s!"Remote '{remote}' contains domain '{domain}, but it not item '{name}'"
          else reportError s!"Remote '{remote}' does not contain domain '{domain}' (looking up '{name}')"
        else reportError s!"Remote '{remote}' not found for tag '{name}' in domain '{domain}'"
        -- If any error was logged, just don't emit a link
        content.mapM go
      | .ok {resolvedDestination := some dest, ..} =>
        pure {{<a href={{dest.link}}>{{← content.mapM go}}</a>}}

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


inductive EmitHtml where
  | no
  | immediately
  | delay (path : System.FilePath)
  | resumeFrom (path : System.FilePath)
deriving ToJson, FromJson

structure OutputConfig where
  destination : System.FilePath := "_out"
  emitTeX : Bool := false
  emitHtmlSingle : EmitHtml := .no
  emitHtmlMulti : EmitHtml := .immediately
  wordCount : Option System.FilePath := none
  draft : Bool := false
  /-- Be verbose while generating output -/
  verbose : Bool := false
deriving ToJson, FromJson

open Verso.Search in
structure Config extends HtmlConfig, TeXConfig, OutputConfig where
  extraFiles : List (System.FilePath × String) := []

  maxTraversals : Nat := 20

  /--
  Location of the remote config file.
  -/
  remoteConfigFile : Option System.FilePath := none

  /--
  Global priorities that control the relative ranking of the semantic (quick-jump) and full-text
  search result streams, each on a scale from `0` to `99`. Defaults are `50` on
  both sides.
  -/
  searchPriorities : SearchPriorities := {}

  /--
  When true (the default), it is an error if no theme is accessible. When false the same problems
  become warnings.

  A theme counts as "accessible" if its `ManualTheme.checkAccessibility` returns no
  issues. In other words:
   * Every checked color pair meets the WCAG AA contrast threshold
   * Every pair of token colors stays mutually distinguishable under each of the three dichromacies
     (`protanopia`, `deuteranopia`, `tritanopia`).

  With a single registered theme, that theme must be accessible. With multiple themes, there must be
  at least one accessible light theme and one accessible dark theme so a reader on either appearance
  can pick a usable theme.
  -/
  strictThemeCoverage : Bool := true

  /--
  When `true` (the default), the build errors if the configured `defaultLightTheme` or
  `defaultDarkTheme` has any accessibility issues. When false the same problems become build-log
  warnings and the build proceeds.
  -/
  strictDefaultThemeAccessibility : Bool := true

  /--
  When `true` (the default), every registered theme that has accessibility issues emits a build-log
  warning that names the theme and the specific issues. Setting this to `false` silences these
  per-theme warnings — useful when shipping a documented trade-off (for example the canonical
  Solarized palette, whose token colors are below WCAG AA's 4.5:1 contrast threshold for normal text
  by design).
  -/
  warnPerThemeAccessibility : Bool := true
deriving ToJson, FromJson

open Lean in
open Verso.Theme in
structure RenderConfig extends Config where
  /--
  How to insert links in rendered code
  -/
  linkTargets : TraverseState → Multi.AllRemotes → LinkTargets Manual.TraverseContext := (·.localTargets ++ ·.remoteTargets)
  /--
  The manual themes that should be available in the picker. When `none` (the default), every
  theme registered with `@[manual_theme]` is available.
  -/
  availableThemes : Option NameSet := none
  /--
  The default light-appearance theme. Its registration name must be a registered
  `ManualTheme` whose appearance is `.light`.
  -/
  defaultLightTheme : Name := ``Verso.Theme.ManualTheme.ink
  /--
  The default dark-appearance theme. Its registration name must be a registered
  `ManualTheme` whose appearance is `.dark`.
  -/
  defaultDarkTheme : Name := ``Verso.Theme.ManualTheme.argent
  /--
  The default for readers who do not follow the system appearance (the "single" picker mode):
  choose `.light` so single-mode falls back to
  `defaultLightTheme`,
  or `.dark` so it falls back to
  `defaultDarkTheme`.

  Auto-mode behavior is unchanged either way: a reader who keeps "Match system" on still gets
  the light or dark default depending on their OS preference. This setting only governs the
  single-mode fallback (and what the picker marks as ` (default)` in the single-mode
  dropdown).
  -/
  defaultSingleAppearance : Appearance := .light

namespace Config

/--
Adds a bundled version of KaTeX to the document.
-/
@[deprecated "Set the `features` field instead (though KaTeX is enabled by default, so this is probably not needed)" (since := "2025-11-12")]
def addKaTeX (config : Config) : Config := { config with features := config.features.insert .KaTeX }

/--
Adds search dependencies to the configuration.
-/
@[deprecated "Set the `features` field instead (though search is enabled by default, so this is probably not needed)" (since := "2025-11-12")]
def addSearch (config : Config) : Config := { config with features := config.features.insert .search }

end Config

namespace RenderConfig

/--
Adds a bundled version of KaTeX to the document.
-/
@[deprecated "Set the `features` field instead (though KaTeX is enabled by default, so this is probably not needed)" (since := "2025-11-12")]
def addKaTeX (config : Config) : Config := { config with features := config.features.insert .KaTeX }

/--
Adds search dependencies to the configuration.
-/
@[deprecated "Set the `features` field instead (though search is enabled by default, so this is probably not needed)" (since := "2025-11-12")]
def addSearch (config : Config) : Config := { config with features := config.features.insert .search }

end RenderConfig

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
        let content' ← withReader (·.inPart p) <| content.mapM Manual.traverseBlock
        let subParts' ← withReader (·.inPart p) <| subParts.mapM fun p => do
          let path' := path.push (p.metadata.bind (·.file) |>.getD (p.titleString.sluggify.toString))
          withReader ({· with path := path' : TraverseContext}) (traverseMulti d path' p)
        pure <| .mk (← title.mapM Manual.traverseInline) titleString «meta» content' subParts'

open Verso.Output.Html in
def TraverseState.ofConfig (config : HtmlConfig) : TraverseState := Id.run do
  let mut st : TraverseState := .initialize config.toHtmlAssets
  for f in config.features do
    for li in f.licenseInfo do
      st := st.addLicenseInfo li
  return st


def traverse (text : Part Manual) (config : Config) : EmitM (Part Manual × TraverseState) := do
  let topCtxt : Manual.TraverseContext := { draft := config.draft }
  let mut state : Manual.TraverseState := .ofConfig config.toHtmlConfig
  -- Themes contribute their own third-party licenses (color palettes, fonts) on top of the
  -- HtmlFeature ones already collected by `TraverseState.ofConfig`.
  let registry ← readThe ThemeRegistry
  for (_, theme) in registry do
    for li in theme.licenses do
      state := state.addLicenseInfo li
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


structure DividedDoc where
  /-- Start text and leading unnumbered parts -/
  frontMatter : Array (Doc.Block Manual) × Array (Part Manual)
  /-- Numbered and unnumbered parts not at end -/
  mainMatter : Array (Part Manual)
  /-- Trailing unnumbered parts -/
  backMatter : Array (Part Manual)

def DividedDoc.ofPart (part : Part Manual) : DividedDoc :=
  let leading := part.content
  let prefaces := part.subParts.takeWhile isUnnumbered
  let frontMatter := (leading, prefaces)
  let rest := part.subParts.drop prefaces.size
  let backMatter := rest |>.reverse |>.takeWhile isUnnumbered |>.reverse
  let mainMatter := rest.extract 0 (rest.size - backMatter.size)
  { frontMatter, mainMatter, backMatter }
where
  isUnnumbered (p : Part Manual) : Bool := p.metadata.map (·.number) |>.isEqSome false

/--
Resolves the single-mode default theme name from the configured
`Verso.Genre.Manual.RenderConfig.defaultSingleAppearance` — either
`Verso.Genre.Manual.RenderConfig.defaultLightTheme` or
`Verso.Genre.Manual.RenderConfig.defaultDarkTheme`.
-/
def defaultSingleName (config : RenderConfig) : Lean.Name :=
  match config.defaultSingleAppearance with
  | .light => config.defaultLightTheme
  | .dark => config.defaultDarkTheme

/--
The single-default `ManualTheme` resolved from the active
{name}`ThemeRegistry`. This is the theme that drives
`verso-themes.css`'s unscoped `:root` block — what the server-rendered HTML paints on first
visit (before the no-flash script attaches a `data-verso-theme`) — and the TeX code styling.

Falls back to a bare default `ManualTheme.ink` if neither the resolved single-default name
nor either configured default appears in the registry (a defensive case; the validation pass
in `manualMain` rejects unregistered defaults before this is called).
-/
def singleDefaultTheme (registry : ThemeRegistry) (config : RenderConfig) :
    Verso.Theme.ManualTheme :=
  (registry.find? (defaultSingleName config)
    <|> registry.find? config.defaultLightTheme
    <|> registry.find? config.defaultDarkTheme).getD Verso.Theme.ManualTheme.ink

open IO.FS in
/--
Writes every theme-related asset for an output root: the multi-theme `verso-themes.css`, the
picker `.js`/`.css`, the `window.versoThemes` data file, every theme's font bytes and bundled
assets. Content-addressed font filenames in the theme registry ensure that two themes sharing the
same font end up with one byte payload on disk.
-/
def writeThemeAssets (dir : System.FilePath) (config : RenderConfig) : EmitM Unit := do
  let themes ← readThe ThemeRegistry
  ensureDir (dir / "-verso-data")
  let single := singleDefaultTheme themes config
  -- verso-themes.css
  withFile (dir / "verso-themes.css") .write fun h => do
    h.putStrLn (Verso.Theme.«verso-themes.css» single themes
      config.defaultLightTheme config.defaultDarkTheme)
  -- Font bytes, deduplicated by output path: a theme's @font-face rules embed the per-theme
  -- asset-root path, so writing one path and skipping a structurally-identical-bytes path under
  -- a different theme root would leave that rule pointing at a missing file.
  let mut writtenPaths : Std.HashSet String := {}
  for (n, t) in themes do
    let assetRoot := s!"-verso-data/themes/{n.toString}"
    for (path, bytes, _, _) in t.fontAssets assetRoot do
      if writtenPaths.contains path then continue
      writtenPaths := writtenPaths.insert path
      let abs := dir.join path
      if let some p := abs.parent then ensureDir p
      writeBinFile abs bytes
  -- Theme-bundled assets (images, etc.).
  for (n, t) in themes do
    for a in t.assets do
      let path := dir / "-verso-data" / "themes" / n.toString / a.path
      if let some p := path.parent then ensureDir p
      writeBinFile path a.contents
  -- Picker assets + data file.
  writeFile (dir / "-verso-data" / "theme-picker.js") Manual.Theme.«theme-picker.js»
  writeFile (dir / "-verso-data" / "theme-picker.css") Manual.Theme.«theme-picker.css»
  writeFile (dir / "-verso-data" / "verso-themes.js")
    (Verso.Theme.windowVersoThemesJs themes config.defaultLightTheme config.defaultDarkTheme
      (defaultSingleName config) Manual.Theme.codeSampleHtml)

open IO.FS in
def emitTeX (config : RenderConfig) (text : Part Manual) : EmitM Unit := do
  let registry ← readThe ThemeRegistry
  let (text, state) ← traverse text config.toConfig
  let opts : TeX.Options Manual := {
    headerLevels := #["chapter", "section", "subsection", "subsubsection", "paragraph"],
    headerLevel := some ⟨0, by grind⟩
  }
  let authors := text.metadata.map (·.authors) |>.getD []
  let date := text.metadata.bind (·.date) |>.getD ""
  let { frontMatter := (frontText, frontParts), mainMatter, backMatter } := DividedDoc.ofPart text
  let (frontMatter, extra) ← frontText.mapM (·.toTeX (m := EmitM) (opts, {}, state, {})) {}
  -- Passing `none` as the label is fine here because traversal has assigned labels already so
  -- there's no need for a fallback.
  let (frontParts, extra) ← frontParts.mapM (·.toTeX (m := EmitM) none (opts, {}, state, {})) extra
  let frontMatter := frontMatter ++ frontParts
  let (chapters, extra) ← mainMatter.mapM (·.toTeX (m := EmitM) none (opts, {}, state, {})) extra
  let (appendices, extra) ← backMatter.mapM (·.toTeX (m := EmitM) none (opts, {}, state, {})) extra
  let dir := config.destination.join "tex"
  ensureDir dir
  let packages := state.texPackages
  let preambleItems := state.texPreambleItems
  withFile (dir.join "main.tex") .write fun h => do
    if config.verbose then
      IO.println s!"Saving {dir.join "main.tex"}"
    h.putStrLn (preamble text.titleString authors date packages.toList preambleItems.toList (singleDefaultTheme registry config).toCodeTheme)
    -- \frontmatter is inserted by our hardcoded preamble before the ToC, so it doesn't get inserted
    -- here. If there's any text at the start of the front matter, then we need to clear it to a new
    -- recto page after the ToC
    unless frontText.all (·.isEmpty) do
      h.putStrLn "\\cleardoublepage"
    for b in frontMatter do
      h.putStrLn b.asString
    h.putStrLn "\n\\mainmatter"
    for c in chapters do
      h.putStrLn c.asString
    unless appendices.all (·.isWhitespace) do
      h.putStrLn "\n\\backmatter"
      for a in appendices do
        h.putStrLn a.asString
    h.putStrLn postamble
  for (src, dest) in config.extraFiles do
    copyRecursively src (dir.join dest)
  for (src, dest) in config.extraFilesTeX do
    copyRecursively src (dir.join dest)
  for (f, content) in extra.extraFiles do
    IO.FS.writeFile (dir / f) content

open Verso.Output (Html)

instance [Monad m] : Inhabited (StateT (State Html) m Html.Toc) := ⟨pure default⟩

/--
Generate a ToC structure for a document.

Here, `depth` is the current depth at which pages no longer receive their own HTML files, not the
depth of the table of contents in the document (which is controlled by a parameter to `Toc.html`).
-/
partial def toc [Monad m] [Html.ToHtml Manual m (Doc.Inline Manual)] [MonadLiftT IO m]
    (depth : Nat) (opts : Html.Options)
    (ctxt : TraverseContext)
    (state : TraverseState)
    (definitionIds : Lean.NameMap String)
    (linkTargets : LinkTargets Manual.TraverseContext) :
    Part Manual → StateT (State Html) m Html.Toc
  | .mk title sTitle «meta» _ sub => do
    let titleHtml ← Html.seq <$> title.mapM (Manual.toHtml opts ctxt state definitionIds linkTargets {} ·)

    let some {id := some id, ..} := «meta»
      | (throw <| .userError s!"No ID for {sTitle} - {repr «meta»}" : IO _)
    let some {htmlId := v, ..} := state.externalTags[id]?
      | (throw <| .userError s!"No external ID for {sTitle}" : IO _)

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
    (showNavButtons : Bool := true) (extraJs : List JS := [])
    (extraHead : Html := .empty)
    (themeInitScript : String := "") (showThemePicker : Bool := false) : Html :=
  let toc := {
    title := htmlBookTitle, path := #[], id := "" , sectionNum := some #[], children := toc
  }
  let extraJsFiles :=
    sortJs <|
      state.extraJsFiles.toArray.map (false, ·.toStaticJsFile)
  let extraJsFiles := extraJsFiles.map fun
    | (true, f) => (f.filename, f.defer)
    | (false, f) => ("/-verso-data/" ++ f.filename, f.defer)
  let featureJsFiles :=
    state.features.toArray.flatMap fun f =>
      f.jsFilePaths.map fun (name, defer) => ("/-verso-data/" ++ name, defer)
  let cssFiles :=
    state.extraCssFiles.toArray.map (·.filename) ++
    state.features.toArray.flatMap (fun f => f.cssFilePaths)
  Html.page toc path textTitle htmlBookTitle contents
    -- The extraCss, extraJs, extraCssFiles, and extraJsFiles in the config are absent here
    -- because they are included in the traverse state when it is initialized
    state.extraCss (state.extraJs.insertMany extraJs)
    (showNavButtons := showNavButtons)
    (logo := config.logo)
    (logoDark := config.logoDark)
    (logoLink := config.logoLink)
    (repoLink := config.sourceLink)
    (issueLink := config.issueLink)
    (localItems := localItems)
    (extraStylesheets := cssFiles.toList.map ("/-verso-data/" ++ ·))
    (extraJsFiles := featureJsFiles ++ extraJsFiles)
    (extraHead := config.extraHead |>.push extraHead)
    (extraContents := config.extraContents)
    (themeInitScript := themeInitScript)
    (showThemePicker := showThemePicker)

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
  (extraJs := [s!"window.xref = {xrefJson};\n" ++ findJs])

def emitXrefsJson (dir : System.FilePath) (state : TraverseState) : IO Unit := do
  let out := xrefJson state.domains state.externalTags
  ensureDir dir
  let xrefJson := toString out
  IO.FS.writeFile (dir / "xref.json") xrefJson

def emitFindHtml (toc : List Html.Toc) (dir : System.FilePath) (state : TraverseState) (xrefJson : String) (config : Config) : IO Unit := do
  emitXrefsJson dir state
  ensureDir (dir / "find")
  IO.FS.writeFile (dir / "find" / "index.html") (Html.doctype ++ (relativizeLinks <| xref toc xrefJson find.js state config).asString)

open Output.Html in
/--
Renders the shell HTML for the full-page search results view at `search/index.html`.
The page reuses the same `<head>` as every other page (so `searchIndex.js`, the combobox,
and the domain-mappers are loaded) and defers all result rendering to `search-page.js`.
-/
def searchResultsPage (toc : List Html.Toc) (bookTitle : Html) (state : TraverseState) (config : Config) : Html :=
  -- `bookTitle` (fourth arg) becomes the `.header-title` content; the `<h1>"Search"</h1>`
  -- below is the page heading inside the main content. `"Search"` is only the `<title>`.
  --
  page toc #["search"] "Search" bookTitle {{
    <section class="search-page">
      <h1>"Search"</h1>
      <div data-search-host class="search-page-host"></div>
      <noscript><p>"This search feature requires JavaScript."</p></noscript>
      <div id="search-page-results"></div>
      <script type="module" src="-verso-search/search-page.js"></script>
    </section>
  }}
  state config
  (localItems := #[])
  /-
  Start the xref.json download in parallel with script loading. The search page JS can't fetch it
  until it runs, so without the preload the data fetch sits at the tail of the critical path.
  -/
  (extraHead := {{<link rel="preload" href="xref.json" as="fetch"/>}})

def emitSearchResultsHtml
    (toc : List Html.Toc) (dir : System.FilePath) (bookTitle : Html)
    (state : TraverseState) (config : Config) : IO Unit := do
  ensureDir (dir / "search")
  IO.FS.writeFile
    (dir / "search" / "index.html")
    (Html.doctype ++ (relativizeLinks <| searchResultsPage toc bookTitle state config).asString)


section
open Search

def emitSearchIndex [Monad m] [MonadLiftT IO m] [MonadBuildLog m]
    (dir : System.FilePath) (state : TraverseState) (ctx : TraverseContext) (doc : Part Manual) : m Unit := do
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
    partPriority p := do
      let ctxt ← IndexM.traverseContext
      return some (ancestorSearchPriority (ctxt.inPart p).headers)
    block _ := none,
    inline _ := none
  }

  match mkIndexAndDocs doc ctx with
  | .error e => reportError e; return ()
  | .ok (index, indexDocs) =>
    -- `context` (the breadcrumb text) is no longer an indexed field — it's
    -- display-only and its boost was 0.1, so indexing it nearly duplicated
    -- another inverted index for negligible scoring benefit. `bucketDocsToJson`
    -- still merges it into each emitted bucket's per-doc payload so the search
    -- UI can render breadcrumbs.
    let contextMap := refContextMap indexDocs
    -- Split the index into roughly 150k chunks for faster loading
    let (index, docs) := index.extractDocs
    let mut docBuckets : HashMap UInt8 (HashMap String Doc) := {}
    for (ref, content) in docs do
      let h := bucket ref
      docBuckets := docBuckets.alter h fun v =>
        v.getD {} |>.insert ref content

    -- Content-hashed bucket filenames: a 64-bit hash of the inverted index (which
    -- is derived from the same source docs as the buckets) is appended to each
    -- bucket's filename, and exposed via `window.searchIndexVersion` for the
    -- loader to reconstruct the URL. Since the filename changes whenever the
    -- index changes, bucket files can be served with `Cache-Control: immutable`
    -- — no revalidation RTT per bucket on repeat visits.
    let indexData := index.toJson.compress
    let version := hashHex (hash indexData)

    for (bucket, docs) in docBuckets do
      let docJson := bucketDocsToJson docs contextMap
      IO.FS.writeFile (dir / s!"searchIndex_{bucket}.{version}.js")
        s!"window.docContents[{bucket}].resolve({docJson.compress});"

    -- Per-doc priority map, emitted alongside the elasticlunr index inside the eagerly-loaded
    -- searchIndex.js. Kept separate from the lazily-fetched per-bucket content so full-text
    -- scoring can consult it without waiting on bucket loads.
    let priorityJson := priorityMapJson indexDocs

    let indexJs := "const __verso_searchIndexData = " ++ indexData ++ ";\n\n"
    let indexJs := indexJs ++ "const __versoSearchIndex = elasticlunr ? elasticlunr.Index.load(__verso_searchIndexData) : null;\n"
    let indexJs := indexJs ++ "window.docContents = {};\n"
    let indexJs := indexJs ++ "window.searchIndex = elasticlunr ? __versoSearchIndex : null;\n"
    let indexJs := indexJs ++ "window.docPriorities = " ++ priorityJson.compress ++ ";\n"
    let indexJs := indexJs ++ "window.searchIndexVersion = " ++ toString (Json.str version) ++ ";\n"
    IO.FS.writeFile (dir / "searchIndex.js") indexJs

    IO.FS.writeFile (dir / "elasticlunr.min.js") Verso.Output.Html.elasticlunr.js

where
  -- Not using a proper hash because this needs to be implemented identically in JS
  bucket (s : String) : UInt8 := Id.run do
    let mut hash := 0
    let mut n := 0
    while h : n < s.utf8ByteSize do
      hash := hash + s.getUTF8Byte ⟨n⟩ h
      n := n + 1
    return hash


/--
Emits the search box static assets plus a `search-config.js` loaded by every page.
`searchPagePath`, when supplied, is the site-root-relative path of the full-page search
results view. The combobox reads it via `window.searchPagePath` and enables Enter-to-submit.
-/
def emitSearchBox
    (dir : System.FilePath) (domains : DomainMappers)
    (priorities : SearchPriorities := {})
    (searchPagePath : Option String := none) : IO Unit := do
  ensureDir dir
  for (file, contents) in searchBoxCode do
    IO.FS.writeBinFile (dir / file) contents
  IO.FS.writeFile (dir / "domain-mappers.js") ((domains.toJs priorities).pretty (width := 70))
  IO.FS.writeFile (dir / "domain-display.css") domains.quickJumpCss
  let configJs := match searchPagePath with
    | some path => s!"window.searchPagePath = {toString (Json.str path)};\n"
    | none => ""
  IO.FS.writeFile (dir / "search-config.js") configJs

end

def wordCount
    (wcPath : System.FilePath) (config : Config)
    (text : Part Manual) : EmitM Unit := do
  let (text, _) ← traverse text config
  IO.FS.writeFile wcPath (wordCountReport skip "" 2 text |>.snd)
where
  -- Skip included docstrings for word count purposes
  skip n := [`Verso.Genre.Manual.Block.docstring].contains n

/--
Resolves cross-references in a manner suitable for single-page HTML output.
-/
def traverseHtmlSingle (config : RenderConfig)
    (text : Part Manual) : EmitM (Part Manual × TraverseState) := do
  traverse text { config with htmlDepth := 0 }

/--
Emits single-page HTML for the document.

The provided `text` and `state` parameters should be the result of running `traverseHtmlSingle`.
-/
def emitHtmlSingle
    (config : RenderConfig)
    (text : Part Manual) (state : TraverseState) : EmitM Unit := do
  let dir := config.destination.join "html-single"
  ensureDir dir
  let remoteContent ← updateRemotes false config.remoteConfigFile (if config.verbose then IO.println else fun _ => pure ())
  let ((), htmlState) ← emitContent dir |>.run .empty |>.run remoteContent
  IO.FS.writeFile (dir.join "-verso-docs.json") (toString htmlState.dedup.docJson)
  if .search ∈ config.features then
    emitSearchBox (dir / "-verso-search") state.quickJump config.searchPriorities (searchPagePath := some "search/")
    emitSearchIndex (dir / "-verso-search") state { draft := config.draft } text
where
  emitContent (dir : System.FilePath) : StateT (State Html) (ReaderT AllRemotes EmitM) Unit := do
    let registry ← readThe ThemeRegistry
    let authors := text.metadata.map (·.authors) |>.getD []
    let authorshipNote := text.metadata.bind (·.authorshipNote)
    let _date := text.metadata.bind (·.date) |>.getD "" -- TODO
    let opts : Html.Options := { }
    let ctxt : Manual.TraverseContext := {}
    let definitionIds := state.definitionIds ctxt
    let linkTargets := config.linkTargets state (← readThe AllRemotes)
    let titleHtml ← Html.seq <$> text.title.mapM (Manual.toHtml opts ctxt state definitionIds linkTargets {})
    let introHtml ← Html.seq <$> text.content.mapM (Manual.toHtml opts ctxt state definitionIds linkTargets {})
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
        Manual.toHtml { opts with headerLevel := 2 } (ctxt.inPart p) state definitionIds linkTargets {} p
    let pageContent := open Verso.Output.Html in
      {{<section>
          {{Html.titlePage titleHtml authors authorshipNote introHtml}}
          {{bookTocHtml}}
          {{contents}}
        </section>}}
    let toc := (← text.subParts.mapM (toc 0 opts ctxt state definitionIds linkTargets)).toList
    let thisPageToc : Array Html ← do
      let (errs, items) ← localContents opts ctxt state text
      for e in errs do reportError e
      pure <| items.map (·.toHtml)
    let titleToShow : Html :=
      open Verso.Output.Html in
      if let some alt := text.metadata.bind (·.shortTitle) then
        alt
      else titleHtml
    let xrefJson ← IO.FS.readFile (dir / "xref.json")
    emitFindHtml toc dir state xrefJson config.toConfig
    if .search ∈ config.features then
      emitSearchResultsHtml toc dir titleToShow state config.toConfig
    IO.FS.withFile (dir.join "book.css") .write fun h => do
      h.putStrLn Html.Css.pageStyle
    writeThemeAssets dir config
    for (src, dest) in config.extraFiles do
      copyRecursively src (dir.join dest)
    for (src, dest) in config.extraFilesHtml do
      copyRecursively src (dir.join dest)
    for f in state.extraJsFiles do
      ensureDir (dir.join "-verso-data")
      (dir / "-verso-data" / f.filename).parent |>.forM fun d => ensureDir d
      IO.FS.writeFile (dir / "-verso-data" / f.filename) f.contents.js
      if let some m := f.sourceMap? then
        IO.FS.writeFile (dir / "-verso-data" / m.filename) m.contents
    state.writeFiles (dir / "-verso-data")

    IO.FS.withFile (dir.join "index.html") .write fun h => do
      if config.verbose then
        IO.println s!"Saving {dir.join "index.html"}"
      h.putStrLn Html.doctype
      -- Offer the picker only when the reader has a real choice. A registry with one entry
      -- (or none) means the unscoped `:root` block already paints the only available theme.
      let showThemePicker := registry.size > 1
      let themeInitScript :=
        if showThemePicker then
          Verso.Theme.themeInitScript registry
            config.defaultLightTheme config.defaultDarkTheme (defaultSingleName config)
        else ""
      h.putStrLn <| Html.asString <| relativizeLinks <|
        page toc ctxt.path text.titleString titleToShow pageContent state config.toConfig thisPageToc
          (showNavButtons := false)
          (themeInitScript := themeInitScript)
          (showThemePicker := showThemePicker)


/--
Resolves cross-references in a manner suitable for multi-page HTML output.
-/
def traverseHtmlMulti (config : RenderConfig)
    (text : Part Manual) : EmitM (Part Manual × TraverseState) := do
  traverse text config.toConfig

open Verso.Output.Html in
/--
Emits multi-page HTML for the document.

The provided `text` and `state` parameters should be the result of running `traverseHtmlSingle`.
-/
def emitHtmlMulti (config : RenderConfig)
    (text : Part Manual) (state : TraverseState) : EmitM Unit := do
  let remoteContent ← updateRemotes false config.remoteConfigFile (if config.verbose then IO.println else fun _ => pure ())
  let root := config.destination.join "html-multi"
  ensureDir root
  let ((), htmlState) ← emitContent root |>.run .empty |>.run remoteContent
  IO.FS.writeFile (root.join "-verso-docs.json") (toString htmlState.dedup.docJson)
  if .search ∈ config.features then
    emitSearchBox (root / "-verso-search") state.quickJump config.searchPriorities (searchPagePath := some "search/")
    emitSearchIndex (root / "-verso-search") state { draft := config.draft } text
where
  /--
  Emits the data used by all pages in the site, such as JS and CSS, and then emits the root page
  (and thus its children).
  -/
  emitContent (root : System.FilePath) : StateT (State Html) (ReaderT AllRemotes EmitM) Unit := do
    let authors := text.metadata.map (·.authors) |>.getD []
    let authorshipNote := text.metadata >>= (·.authorshipNote)
    let _date := text.metadata.bind (·.date) |>.getD "" -- TODO
    let opts : Html.Options := { }
    let ctxt : Manual.TraverseContext := {}
    let definitionIds := state.definitionIds ctxt
    let linkTargets := config.linkTargets state (← readThe AllRemotes)
    let toc ← text.subParts.toList.mapM fun p =>
      toc config.htmlDepth opts (ctxt.inPart p) state definitionIds linkTargets p
    let titleHtml ← Html.seq <$> text.title.mapM (Manual.toHtml opts ctxt state definitionIds linkTargets {} ·)
    let titleToShow : Html :=
      open Verso.Output.Html in
      if let some alt := text.metadata.bind (·.shortTitle) then
        alt
      else titleHtml
    IO.FS.withFile (root / "book.css") .write fun h => do
      h.putStrLn Html.Css.pageStyle
    writeThemeAssets root config
    for (src, dest) in config.extraFiles do
      copyRecursively src (root.join dest)
    for (src, dest) in config.extraFilesHtml do
      copyRecursively src (root.join dest)
    state.writeFiles (root / "-verso-data")

    emitPart titleToShow authors authorshipNote toc opts ctxt state definitionIds linkTargets {} true config.htmlDepth root text
    let xrefJson ← IO.FS.readFile (root / "xref.json")
    emitFindHtml toc root state xrefJson config.toConfig
    if .search ∈ config.features then
      emitSearchResultsHtml toc root titleToShow state config.toConfig

  /--
  Emits HTML for a given part, and its children if the splitting threshold is not yet reached.
  -/
  emitPart (bookTitle : Html) (authors : List String) (authorshipNote : Option String) (bookContents)
      (opts ctxt state definitionIds linkTargets codeOptions)
      (root : Bool) (depth : Nat) (dir : System.FilePath) (part : Part Manual) : StateT (State Html) (ReaderT AllRemotes EmitM) Unit := do
    let registry ← readThe ThemeRegistry
    let thisFile := part.metadata.bind (·.file) |>.getD (part.titleString.sluggify.toString)
    let dir := if root then dir else dir.join thisFile
    let sectionNum := sectionHtml ctxt
    let pageTitleHtml := sectionNum ++ (← Html.seq <$> part.title.mapM (Manual.toHtml opts ctxt state definitionIds linkTargets codeOptions))
    let titleHtml :=
      pageTitleHtml ++
      if let some id := part.metadata.bind (·.id) then
        permalink id state
      else .empty
    let introHtml ← Html.seq <$> part.content.mapM (Manual.toHtml opts ctxt state definitionIds linkTargets codeOptions)
    let contents ←
      if depth == 0 || part.htmlSplit == .never then
        Html.seq <$> part.subParts.mapM (fun p => Manual.toHtml {opts with headerLevel := 2} (ctxt.inPart p) state definitionIds linkTargets codeOptions p)
      else pure .empty

    let includeSubparts := if (depth == 0 || part.htmlSplit == .never) then .all else .depth 0
    let thisPageToc : Array LocalContentItem ← do
      let (errs, items) ← localContents opts ctxt state (includeTitle := false) (includeSubparts := includeSubparts) part
      for e in errs do reportError e
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
      -- Offer the picker only when the reader has a real choice. A registry with one entry
      -- (or none) means the unscoped `:root` block already paints the only available theme.
      let showThemePicker := registry.size > 1
      let themeInitScript :=
        if showThemePicker then
          Verso.Theme.themeInitScript registry
            config.defaultLightTheme config.defaultDarkTheme (defaultSingleName config)
        else ""
      h.putStrLn <| Html.asString <| relativizeLinks <|
        page bookContents ctxt.path part.titleString bookTitle pageContent state config.toConfig thisPageToc
          (themeInitScript := themeInitScript)
          (showThemePicker := showThemePicker)
    if depth > 0 ∧ part.htmlSplit != .never then
      for p in part.subParts do
        let nextFile := p.metadata.bind (·.file) |>.getD (p.titleString.sluggify.toString)
        emitPart bookTitle authors authorshipNote bookContents opts ({ctxt with path := ctxt.path.push nextFile}.inPart p) state definitionIds linkTargets {} false (depth - 1) dir p
  termination_by depth

structure SavedState where
  text : Part Manual
  traverseState : Manual.TraverseState
deriving ToJson, FromJson

def SavedState.save (file : System.FilePath) (state : SavedState) : IO Unit := do
  IO.FS.writeFile file (ToJson.toJson state).compress

def SavedState.load (file : System.FilePath) : IO SavedState := do
  let json ← IO.FS.readFile file
  match Json.parse json with
  | .error e => throw <| .userError s!"Error parsing {file}: {e}"
  | .ok json =>
    match FromJson.fromJson? json with
    | .error e => throw <| .userError s!"Error deserializing content from {file}: {e}"
    | .ok st => return st


inductive Mode where | single | multi

/--
Extra steps to be performed after building the manual.

`ExtraStep` is short for `Mode → Config → TraverseState → Part Manual → BuildLogT IO Unit`.

The parameters are:
 * A mode, which is whether the HTML was generated in one or multiple files
 * The configuration, as determined from the initial value passed to `manualMain` and modified via the command line
 * The final state of the traversal pass
 * The final text, post-traversal
-/
abbrev ExtraStep := Mode → Config → TraverseState → Part Manual → BuildLogT IO Unit


open Verso.CLI

def manualMain (text : Part Manual)
    (extensionImpls : ExtensionImpls := by exact extension_impls%)
    (codeThemes : Verso.Theme.CodeThemeTable := by exact code_themes%)
    (manualThemes : Verso.Theme.ManualThemeTable := by exact manual_themes%)
    (options : List String)
    (config : RenderConfig := {})
    (extraSteps : List ExtraStep := []) : IO UInt32 :=
  let _ := codeThemes
  go extensionImpls manualThemes

where

  opts (cfg : RenderConfig) : List String → IO RenderConfig
    | ("--output"::dir::more) => opts { cfg with destination := dir } more
    | ("--depth"::n::more) => opts { cfg with htmlDepth := n.toNat! } more

    | ("--with-tex"::more) => opts { cfg with emitTeX := true } more
    | ("--without-tex"::more) => opts { cfg with emitTeX := false } more

    | ("--with-html-single"::more) => opts { cfg with emitHtmlSingle := .immediately } more
    | ("--delay-html-single"::more) =>
      match requireFilename "--delay-html-single" more with
      | .ok f more' _ => opts { cfg with emitHtmlSingle := .delay f } more'
      | .error e => throw (↑ e)
    | ("--resume-html-single"::more) =>
      match requireFilename "--resume-html-single" more with
      | .ok f more' _ => opts { cfg with emitHtmlSingle := .resumeFrom f } more'
      | .error e => throw (↑ e)
    | ("--without-html-single"::more) => opts { cfg with emitHtmlSingle := .no } more

    | ("--with-html-multi"::more) => opts { cfg with emitHtmlMulti := .immediately } more
    | ("--delay-html-multi"::more) =>
      match requireFilename "--delay-html-multi" more with
      | .ok f more' _ => opts { cfg with emitHtmlMulti := .delay f } more'
      | .error e => throw (↑ e)
    | ("--resume-html-multi"::more) =>
      match requireFilename "--resume-html-multi" more with
      | .ok f more' _ => opts { cfg with emitHtmlMulti := .resumeFrom f } more'
      | .error e => throw (↑ e)
    | ("--without-html-multi"::more) => opts { cfg with emitHtmlMulti := .no } more

    | ("--with-word-count"::more) =>
      match requireFilename "--with-word-count" more with
      | .ok file more' _ => opts { cfg with wordCount := some file } more'
      | .error e => throw (↑ e)
    | ("--without-word-count"::more) => opts { cfg with wordCount := none } more
    | ("--draft"::more) => opts { cfg with draft := true } more
    | ("--verbose"::more) => opts { cfg with verbose := true } more
    | ("--remote-config"::more) =>
      match requireFilename "--remote-config" more with
      | .ok file more' _ => opts { cfg with remoteConfigFile := some file } more'
      | .error e => throw (↑ e)
    | (other :: _) => throw (↑ s!"Unknown option {other}")
    | [] => pure cfg


  fixBase (base : String) : String :=
    if base.endsWith "/" then base else base ++ "/"

  /--
  Runs the theme set's accessibility checks at three tiers:

  - **Coverage** (gated by
    `strictThemeCoverage`):
    the build must offer a usable theme. With a single registered theme it must be accessible;
    with multiple themes at least one accessible light *and* one accessible dark must exist.

  - **Default theme** (gated by
    `strictDefaultThemeAccessibility`):
    the configured `defaultLightTheme`
    and `defaultDarkTheme`
    must themselves be accessible.

  - **Per-theme advisory** (gated by
    `warnPerThemeAccessibility`):
    every registered theme with any accessibility issues emits a build-log warning naming the
    theme and the specific issues.

  A theme counts as "accessible" iff its
  `ManualTheme.checkAccessibility` returns no issues.
  -/
  runThemeAccessibilityCheck (cfg : RenderConfig) (registry : ThemeRegistry) :
      ReaderT ExtensionImpls (BuildLogT IO) Unit := do
    let issuesOf (t : Verso.Theme.ManualTheme) := t.checkAccessibility
    let isAccessible (t : Verso.Theme.ManualTheme) : Bool := (issuesOf t).isEmpty
    -- Per-theme advisory.
    if cfg.warnPerThemeAccessibility then
      for (n, t) in registry do
        for issue in issuesOf t do
          let colors := issue.offending.toList.map Verso.Theme.Color.css |> ", ".intercalate
          let suffix := if colors.isEmpty then "" else s!" ({colors})"
          Verso.reportWarning s!"theme '{n.toString}' ({t.name}): {issue.message}{suffix}"
    -- Coverage.
    let routeCoverage (msg : String) : ReaderT ExtensionImpls (BuildLogT IO) Unit :=
      if cfg.strictThemeCoverage then Verso.reportError msg else Verso.reportWarning msg
    let accessible := registry.filter (fun _ t => isAccessible t)
    if accessible.isEmpty then
      routeCoverage "no registered theme is accessible; readers cannot pick a usable theme"
    else if registry.size > 1 then
      let anyLight := accessible.any (fun _ t => t.appearance == Verso.Theme.Appearance.light)
      let anyDark := accessible.any (fun _ t => t.appearance == Verso.Theme.Appearance.dark)
      unless anyLight do
        routeCoverage "no registered light theme is accessible; readers on a light system cannot pick a usable theme"
      unless anyDark do
        routeCoverage "no registered dark theme is accessible; readers on a dark system cannot pick a usable theme"
    -- Default theme accessibility.
    let routeDefault (msg : String) : ReaderT ExtensionImpls (BuildLogT IO) Unit :=
      if cfg.strictDefaultThemeAccessibility then Verso.reportError msg else Verso.reportWarning msg
    let checkDefault (slot : String) (name : Lean.Name) :
        ReaderT ExtensionImpls (BuildLogT IO) Unit := do
      match registry.find? name with
      | none => pure ()  -- already reported by validate
      | some t =>
        let issues := issuesOf t
        unless issues.isEmpty do
          routeDefault s!"{slot} '{name.toString}' ({t.name}) has {issues.size} accessibility issue{if issues.size == 1 then "" else "s"}"
    checkDefault "defaultLightTheme" cfg.defaultLightTheme
    checkDefault "defaultDarkTheme" cfg.defaultDarkTheme

  /--
  Builds the active {name}`ThemeRegistry` from the registered
  `ManualTheme` table, filters it by the configured
  `availableThemes`, and routes every
  `ManualThemeTable.ValidationError` through `MonadBuildLog` as an error.
  -/
  resolveThemeRegistry (cfg : RenderConfig)
      (table : Verso.Theme.ManualThemeTable) :
      ReaderT ExtensionImpls (BuildLogT IO) ThemeRegistry := do
    for e in table.validate cfg.defaultLightTheme cfg.defaultDarkTheme cfg.availableThemes do
      Verso.reportError e.format
    -- `availableThemes` semantics:
    --   `none`        → every registered theme is available
    --   `some [..xs]` → exactly those themes, with `defaultLightTheme` and
    --                   `defaultDarkTheme` implicitly added if missing so the picker always
    --                   contains the resolved default for each appearance.
    -- The result always contains at least `defaultLightTheme` and `defaultDarkTheme` if those
    -- are registered, so `singleDefaultTheme` can always resolve.
    match cfg.availableThemes with
    | none => return table.themes
    | some xs =>
      let withDefaults := xs
        |>.append (if xs.contains cfg.defaultLightTheme then {} else {cfg.defaultLightTheme})
        |>.append (if xs.contains cfg.defaultDarkTheme then {} else {cfg.defaultDarkTheme})
      return withDefaults.foldl (init := ({} : ThemeRegistry)) fun acc n =>
        match table.find? n with
        | some t => acc.insert n t
        | none => acc

  go (extensionImpls : ExtensionImpls) (manualThemes : Verso.Theme.ManualThemeTable) : IO UInt32 := do
    let cfg ← opts config options
    runWithLogger <| flip ReaderT.run extensionImpls do
      let registry ← resolveThemeRegistry cfg manualThemes
      runThemeAccessibilityCheck cfg registry
      let body : EmitM Unit := do
        if cfg.emitTeX then
          if cfg.verbose then
            IO.println s!"Saving TeX"
          emitTeX cfg text

        emitHtml cfg.emitHtmlSingle .single cfg text traverseHtmlSingle emitHtmlSingle
        emitHtml cfg.emitHtmlMulti .multi cfg text traverseHtmlMulti emitHtmlMulti

        if let some wcFile := cfg.wordCount then
          if cfg.verbose then
            IO.println s!"Saving word counts to {wcFile}"
          wordCount wcFile cfg.toConfig text
      body.run registry

  emitHtml
      (how : EmitHtml) (mode : Mode) (cfg : RenderConfig) (text : Part Manual)
      (traverse : RenderConfig → Part Manual → EmitM (Part Manual × TraverseState))
      (emit : RenderConfig → Part Manual → TraverseState → EmitM Unit) :
      EmitM Unit := do
    let outDir :=
      match mode with | .single => "html-single" | .multi => "html-multi"
    match how with
    | .no => pure ()
    | .immediately =>
      if cfg.verbose then
        IO.println s!"Saving {match mode with | .single => "single" | .multi => "multi"}-page HTML"
      let (text', traverseState) ← traverse cfg text
      emitXrefsJson (cfg.destination / outDir) traverseState
      emit cfg text' traverseState
      for step in extraSteps do
        step mode cfg.toConfig traverseState text'
    | .delay f =>
      let (text', traverseState) ← traverse cfg text
      emitXrefsJson (cfg.destination / outDir) traverseState
      SavedState.mk text' traverseState |>.save f
    | .resumeFrom f =>
      let {text, traverseState} ← SavedState.load f
      emit cfg text traverseState
      for step in extraSteps do
        step .single cfg.toConfig traverseState text
