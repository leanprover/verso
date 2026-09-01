/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import VersoRenderedHtml
public import VersoBlog.Generate

public section

set_option linter.missingDocs true

open Verso Doc Output Html
open Verso.Output.Html.Files
open Verso.Code.Hover (State)
open Verso.RenderedHtml (OutputPage OutputFragment)
open Verso.Code (highlightingJs)
open Std (HashSet)

namespace Verso.Genre.Blog.RenderedHtml

/--
The tags that a fragment may not carry, because a fragment holds a page body rather than a page.
-/
def chromeTags : List String := ["html", "head", "body", "base"]

/--
The inline-level elements that a title may hold.

A consumer places a title on pages other than the content's own, where the content's stylesheets and
scripts are absent, so a title must stand alone.
-/
def titleTags : List String := ["em", "strong", "code", "sub", "sup", "span", "br"]

/-- The tags of an HTML value that `allowed` rejects. -/
partial def offendingTags (allowed : String → Bool) (html : Html) : Array String :=
  go html #[]
where
  go : Html → Array String → Array String
    | .text .., acc => acc
    | .tag name _ contents, acc =>
      go contents (if allowed name then acc else acc.push name)
    | .seq xs, acc => xs.foldl (fun acc h => go h acc) acc

/-- The attributes that hold a URL, whether one of them or a list of them. -/
def urlValuedAttributes : List String :=
  Verso.Output.Html.urlAttributes ++
  Verso.Output.Html.srcsetAttributes ++
  Verso.Output.Html.urlListAttributes

/-- The values of the URL-valued attributes that an HTML value carries. -/
partial def urlAttributes (html : Html) : Array String :=
  go html #[]
where
  go : Html → Array String → Array String
    | .text .., acc => acc
    | .tag _ attrs contents, acc =>
      go contents <| attrs.foldl (init := acc) fun acc (name, value) =>
        if name ∈ urlValuedAttributes then acc.push value else acc
    | .seq xs, acc => xs.foldl (fun acc h => go h acc) acc

/--
Whether a URL means the exported site's root.

A URL that carries a scheme, a URL that begins with `/`, a fragment-only URL, and the empty string
are placed as they stand. Everything else is relative to the `<base href>` that a standalone page
carries, which means the exported site's root, so it becomes relative to the fragment's token.
-/
def isSiteRelative (url : String) : Bool :=
  !(url.isEmpty || url.startsWith "/" || url.startsWith "#" || hasScheme url)
where
  hasScheme (url : String) : Bool := Id.run do
    let mut pos := url.startPos
    let mut first := true
    while h : pos ≠ url.endPos do
      let c := pos.get h
      if c == ':' then return !first
      unless c.isAlphanum || c == '+' || c == '.' || c == '-' do return false
      if first && !c.isAlpha then return false
      first := false
      pos := pos.next h
    return false

/-- Rewrites a URL of a standalone page so that it addresses the mounted content. -/
def relocateUrl (rootToken : String) (url : String) : String :=
  if isSiteRelative url then rootToken ++ "/" ++ url else url

/--
The wrapper identifier that the content of one directory carries.

It belongs to the directory rather than to a page: it is chosen once, baked into the scripts that
the directory ships, and placed on every wrapper, so a script reaches its own markup on whatever
page it is loaded into. Deriving it from the generator record and the title keeps two directories on
one page apart and makes a rebuild of unchanged content produce the same identifier.
-/
def wrapperClass (generator : RenderedHtmlContent.Generator) (title : String) : String :=
  let key := s!"{generator.tool} {generator.version} {generator.toolchain} {title}"
  s!"verso-content-{key.hash}"

/-- The name of the fragment that holds a page's body. -/
def contentFragmentName : Multi.Slug := "content".sluggify

/-- The file, within the static directory, that holds the hover text for the content's code. -/
def docsFileName : String := "-verso-docs.json"

private def describe (path : Multi.Path) : String :=
  if path.isEmpty then "the root page" else s!"the page '{Verso.RenderedHtml.pathToString path}'"

private def checkTitle (path : Multi.Path) (html : Html) : GenerateM Unit := do
  let bad := offendingTags (titleTags.contains ·) html
  unless bad.isEmpty do
    reportError <|
      s!"The title of {describe path} needs elements that a title may not hold: " ++
      s!"{", ".intercalate bad.toList}. A title holds {", ".intercalate titleTags} and text."
  let urls := urlAttributes html
  unless urls.isEmpty do
    reportError <|
      s!"The title of {describe path} holds URLs: {", ".intercalate urls.toList}. " ++
      "A consumer places a title without rewriting it."

private def renderFragment
    (wrapper : String) (path : Multi.Path) (name : Multi.Slug) (content : Html) :
    GenerateM OutputFragment := do
  let bad := offendingTags (!chromeTags.contains ·) content
  unless bad.isEmpty do
    reportError <|
      s!"The fragment '{name}' of {describe path} carries page chrome: " ++
      s!"{", ".intercalate bad.toList}. A fragment holds a page body."
  let token := Verso.RenderedHtml.chooseToken content.asString
  let relocated := content.rewriteUrls (relocateUrl token)
  -- Each fragment is a root of its own for this content's scripts, so each names the hover data.
  let attrs :=
    #[("class", s!"{versoContentClass} {name} {wrapper}"),
      ("data-verso-docs", s!"{token}/{docsFileName}")]
  return {
    name, rootToken := token,
    content := (Html.tag "div" attrs relocated).asString
  }

end Verso.Genre.Blog.RenderedHtml

namespace Verso.Genre.Blog

open Verso.Genre.Blog.RenderedHtml

/-- Options that a producer of rendered HTML content supplies. -/
structure RenderedHtmlOptions where
  /-- The tool that produced the content. -/
  generator : RenderedHtmlContent.Generator
  /-- The title of the whole. It defaults to the title of the root page. -/
  title? : Option String := none
  /-- The title of the whole as inline HTML. It defaults to the title of the root page. -/
  titleHtml? : Option String := none
  /--
  Fragments beyond `content`, as a name and the template that renders each.

  Each is rendered with the same parameters as the page template and omitted when it renders to
  nothing.
  -/
  fragments : Array (Multi.Slug × Template) := #[]

/--
The files that a rendered HTML content directory ships, and the manifest entries that reference them.
-/
structure RenderedHtmlAssets where
  /-- The files to write, as paths within the static directory and their contents. -/
  files : Array (String × Template.AssetContents)
  /-- The manifest's stylesheets, in cascade order. -/
  stylesheets : Array RenderedHtmlContent.Stylesheet
  /-- The manifest's scripts, in load order. -/
  scripts : Array RenderedHtmlContent.Script

/--
The code highlighting script as every site that Verso serves emits it.
-/
def wholePageHighlightingJs : String := highlightingJs

/--
A script that looks like the code highlighting script, whatever selector it was made with.
-/
def isHighlightingJs (js : JsFile) : Bool :=
  (js.contents.js.find? "versoInitCode").isSome

/--
Scopes the code highlighting script to the wrappers that this content's fragments carry.

A site that Verso serves scopes it to `"body"`, which reaches everything that no wrapper claims.
Exported content lives inside its wrappers, so it ships a copy that names them.
-/
def rescopeHighlightingJs (selector : String) (js : JsFile) :
    JsFile :=
  if js.contents.js == wholePageHighlightingJs then
    { js with contents := ⟨highlightingJs selector⟩ }
  else js

/--
The libraries that Verso vendors, identified by the contents that it ships.

A genre names these files as it likes, so the name a file carries says nothing about what it holds.
-/
def vendoredLibraries : Array (String × RenderedHtmlContent.Library) :=
  #[(Verso.Output.Html.katex.js, ⟨"katex", Verso.Output.Html.katex.version⟩),
    (Verso.Output.Html.katex.css, ⟨"katex", Verso.Output.Html.katex.version⟩),
    (Verso.Code.Highlighted.WebAssets.marked, ⟨"marked", Verso.Code.Highlighted.WebAssets.marked.version⟩),
    (Verso.Code.Highlighted.WebAssets.popper, ⟨"@popperjs/core", Verso.Code.Highlighted.WebAssets.popper.version⟩),
    (Verso.Code.Highlighted.WebAssets.tippy, ⟨"tippy.js", Verso.Code.Highlighted.WebAssets.tippy.version⟩),
    (Verso.Code.Highlighted.WebAssets.tippy.border.css, ⟨"tippy.js", Verso.Code.Highlighted.WebAssets.tippy.version⟩)]

/-- The library that a file's contents are a copy of, when they are one. -/
def libraryOf (contents : String) : Option RenderedHtmlContent.Library :=
  vendoredLibraries.find? (·.fst == contents) |>.map (·.snd)

/--
Computes the files that a rendered HTML content directory ships.

The library scripts come ahead of the scripts that depend on them, and the rest keeps the order that
the shared head computation produced, which is cascade order for stylesheets and load order for
scripts.
-/
def renderedHtmlAssets (head : Template.HeadAssets) (selector : String) :
    RenderedHtmlAssets := Id.run do
  let dataPath (name : String) : String := s!"{dataDirName}/{name}"
  let manifestPath (name : String) : String :=
    s!"{Verso.RenderedHtml.staticDirName}/{dataPath name}"
  let mut files : Array (String × Template.AssetContents) := #[]
  for (name, contents) in Template.builtinAssets selector do
    files := files.push (dataPath name, contents)
  let mut stylesheets : Array RenderedHtmlContent.Stylesheet := #[]
  let mut scripts : Array RenderedHtmlContent.Script :=
    #[{ path := manifestPath "katex/katex.js", defer := true,
        provides := libraryOf Verso.Output.Html.katex.js },
      { path := manifestPath "marked.js", provides := libraryOf Verso.Code.Highlighted.WebAssets.marked },
      { path := manifestPath "math.js" }]
  let builtinCss : Array (String × String) :=
    #[("verso-vars.css", Verso.Output.Html.«verso-vars.css»),
      ("katex/katex.css", Verso.Output.Html.katex.css)]
  -- A stylesheet that shares a name with one of the builtin ones is served by the builtin, so it
  -- reaches the manifest once.
  let headCss := head.css.filter fun css => !builtinCss.any (·.fst == css.filename)
  for (name, contents) in builtinCss do
    let role := if name == "verso-vars.css" then .variables else .content
    stylesheets := stylesheets.push
      { path := manifestPath name, role, provides := libraryOf contents }
  for cssFile in headCss do
    files := files.push (dataPath cssFile.filename, .text cssFile.contents.css)
    stylesheets := stylesheets.push
      { path := manifestPath cssFile.filename, role := .content,
        provides := libraryOf cssFile.contents.css }
  for jsFile in head.js do
    let jsFile := rescopeHighlightingJs selector jsFile
    files := files.push (dataPath jsFile.filename, .text jsFile.contents.js)
    if let some sourceMap := jsFile.sourceMap? then
      files := files.push (dataPath sourceMap.filename, .text sourceMap.contents)
    scripts := scripts.push
      { path := manifestPath jsFile.filename, defer := jsFile.defer,
        provides := libraryOf jsFile.contents.js }
  return { files, stylesheets, scripts }

/--
The class that this content's fragments carry, and that its scripts select on.

It is derived from the generator and the title of the whole, so a rebuild of unchanged content
produces the same class. Pass it to `Verso.Genre.Blog.Site.writeRenderedHtml`.
-/
def RenderedHtmlOptions.wrapperClass (opts : RenderedHtmlOptions) (site : Site) : String :=
  let txt := match site with | .page _ txt _ => txt | .blog _ txt _ => txt
  RenderedHtml.wrapperClass opts.generator (opts.title?.getD txt.titleString)

private def titleParams (params : Template.Params) (path : Multi.Path) :
    GenerateM (String × String) := do
  let some val := params.get? "title"
    | reportError s!"There is no title for {describe path}"
      return ("", "")
  let plain := val.getD (α := String) ""
  let html : Html := val.getD (α := Html) (Html.text true plain)
  checkTitle path html
  return (plain, html.asString)

private partial def reportMounts (path : Multi.Path) (dir : Dir) : GenerateM Unit := do
  let here := path ++ [dir.name]
  match dir with
  | .mount .. =>
    reportError <|
      s!"The site holds a mount at '{Multi.Path.link here}'. " ++
      "A site that is being exported as rendered HTML content holds no mounts."
  | .page _ _ _ contents => contents.forM (reportMounts here)
  | .blog .. | .static .. => pure ()

private def checkNoMounts (site : Site) : GenerateM Unit :=
  match site with
  | .page _ _ contents => contents.forM (reportMounts #[])
  | .blog .. => pure ()

private def exportEmitter
    (theme : Theme) (opts : RenderedHtmlOptions) (wrapper : String)
    (pages : IO.Ref (Array OutputPage)) : PageEmitter := fun params template => do
  let path ← currentPath
  let ⟨baseTemplate, modParams⟩ := theme.adHocTemplates path |>.getD ⟨template, id⟩
  let params := modParams params
  let (title, titleHtml) ← titleParams params path
  let content ← baseTemplate.render params
  let mut fragments :=
    #[← renderFragment wrapper path contentFragmentName content]
  for (name, extra) in opts.fragments do
    let rendered ← extra.render params
    if rendered.asString.trimAscii.isEmpty then continue
    fragments := fragments.push (← renderFragment wrapper path name rendered)
  pages.modify (·.push { path, title, titleHtml, fragments })
  return {}

/--
Renders a site as rendered HTML content: page bodies, head requirements, and assets, with no page
chrome.

Each page is rendered through the theme's page template alone, honoring the theme's ad hoc
templates, as the `content` fragment; the primary template, which holds a theme's page chrome, is
left aside. Every fragment is checked for page chrome, has its URLs rewritten so that they resolve
under whatever mount point a consumer chooses, and is wrapped in a `<div>` carrying `verso-content`,
the fragment's name, and `wrapper`, the class that the content's scripts select on, as computed by
`RenderedHtmlOptions.wrapperClass`. A title that needs anything beyond the inline elements that a
title may hold fails the build, naming its page.
-/
def Site.toRenderedHtml
    (theme : Theme) (site : Site) (opts : RenderedHtmlOptions) (wrapper : String) :
    GenerateM Verso.RenderedHtml.Output := do
  let pages ← IO.mkRef #[]
  checkNoMounts site
  let rootTitle ← rootTitle site
  let title := opts.title?.getD rootTitle.fst
  let titleHtml := opts.titleHtml?.getD rootTitle.snd
  site.walk (exportEmitter theme opts wrapper pages) theme
  let head := theme.headAssets (← read).xref (← getThe Component.State)
  for js in head.js do
    if isHighlightingJs js && js.contents.js != wholePageHighlightingJs then
      reportError <|
        s!"The script '{js.filename}' is a code highlighting script that this version of Verso " ++
        "did not emit, so it cannot be scoped to this content's wrappers. Hovers on the mounted " ++
        "code would not work."
  let assets := renderedHtmlAssets head s!".{wrapper}"
  return {
    generator := opts.generator,
    title, titleHtml,
    stylesheets := assets.stylesheets,
    scripts := assets.scripts,
    pages := ← pages.get
  }
where
  rootTitle (site : Site) : GenerateM (String × String) := do
    let txt := match site with | .page _ txt _ => txt | .blog _ txt _ => txt
    let html : Html ← txt.title.mapM (GenerateM.toHtml Page)
    checkTitle #[] html
    return (txt.titleString, html.asString)

/--
Writes a site as a rendered HTML content directory.

The site's static directories are written under the content's static directory, at the paths that
they occupy in the site, so links to them change only by the token prefix.
-/
def Site.writeRenderedHtml
    (dir : System.FilePath) (theme : Theme) (site : Site) (opts : RenderedHtmlOptions)
    (wrapper : String) :
    GenerateM RenderedHtmlContent := do
  let output ←
    withReader (fun c => { c with dir := Verso.RenderedHtml.staticDir dir }) <|
      Site.toRenderedHtml theme site opts wrapper
  let head := theme.headAssets (← read).xref (← getThe Component.State)
  for (path, contents) in (renderedHtmlAssets head s!".{wrapper}").files do
    match contents with
    | .text txt => Verso.RenderedHtml.writeStaticFile dir path (.text txt)
    | .binary bytes => Verso.RenderedHtml.writeStaticFile dir path (.binary bytes)
  Verso.RenderedHtml.writeStaticFile dir docsFileName
    (.text (toString (← getThe (State Html)).dedup.docJson))
  Verso.RenderedHtml.write dir output

end Verso.Genre.Blog
