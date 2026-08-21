/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Verso.FS
public import MultiVerso.Path
public import VersoBlog.Basic
public import VersoBlog.Template
public import VersoBlog.Theme

public section

open Verso Doc Output Html HtmlT FS
open Verso.Code.Hover (State)
open Verso.Code (LinkTargets)

namespace Verso.Genre.Blog

instance [Monad m] : MonadConfig (HtmlT Post m) where
  currentConfig := do
    return (← context).config

instance [Monad m] : MonadConfig (HtmlT Page m) where
  currentConfig := do
    return (← context).config

structure Generate.Context where
  site : Site
  ctxt : TraverseContext
  xref : TraverseState
  linkTargets : LinkTargets TraverseContext
  /-- The root directory in which to generate the static site -/
  dir : System.FilePath
  config : Config
  header : String
  rewriteHtml : Option (TraverseContext → Html → BuildLogT IO Html) := none
  components : Components := {}
  theme : Theme
  /-- What the directory mounted at the current path contributes to the page's `<head>`. -/
  mounted : Template.MountedAssets := {}
  extraParams : Multi.Path → Template.Params := fun _ => {}

def Generate.Context.templateContext (ctxt : Generate.Context) (params : Template.Params) : Template.Context :=
  let path := ctxt.ctxt.path
  { site := ctxt.site,
    config := ctxt.config,
    params := params ++ ctxt.extraParams path,
    path,
    headAssets := ctxt.theme.headAssets ctxt.xref,
    mounted := ctxt.mounted,
    components := ctxt.components
  }

abbrev GenerateM := ReaderT Generate.Context (StateT (State Html) (StateT Component.State (BuildLogT IO)))

instance : Template.MonadComponents GenerateM where
  componentImpls := do return (← read).components
  saveJs js := modifyThe Component.State fun s => {s with headerJs := s.headerJs.insert js}
  saveCss css := modifyThe Component.State fun s => {s with headerCss := s.headerCss.insert css}

def Generate.rewriteOutput (html : Html) : GenerateM Html := do
  let {ctxt, rewriteHtml := some rewriter, ..} := (← read)
    | pure html
  rewriter ctxt html

instance : MonadPath GenerateM where
  currentPath := do return (← read).ctxt.path

instance : MonadConfig GenerateM where
  currentConfig := do return (← read).config

open BlogGenre in
def GenerateM.toHtml (g : Genre)
    [bg : BlogGenre g] [ToHtml g ComponentM α]
    (x : α) : GenerateM Html := do
  let {ctxt := ctxt, xref := state, linkTargets, ..} ← read
  let (out, st') ← g.toHtml
    (m := ComponentM)
    { headerLevel := 2 }
    (bg.context_eq ▸ ctxt)
    (bg.state_eq ▸ state)
    {}
    (bg.context_eq ▸ linkTargets)
    {}
    x
    (← get)
    (← Template.MonadComponents.componentImpls)
  set st'
  return out


namespace Template

namespace Params

def forPart [BlogGenre g] [GenreHtml g ComponentM]
    [ToHtml g ComponentM (Part g)]
    [ToHtml g ComponentM (Block g)]
    (txt : Part g) : GenerateM Params := do
  let titleHtml : Html ← txt.title.mapM (GenerateM.toHtml g)
  let preamble ← txt.content.mapM (GenerateM.toHtml g)
  let subParts ← txt.subParts.mapM (GenerateM.toHtml g)
  return ofList [
    ("title", ⟨.mk txt.titleString, #[.mk titleHtml]⟩),
    ("content", preamble ++ subParts)
  ]
end Params

/-- Renders a template, returning what it read while it rendered. -/
def renderTraced (template : Template) (params : Params) : GenerateM (Html × RenderTrace) := do
  match template ((← read).templateContext params) {} (← getThe _) with
  | .error err =>
    let message := match err with
    | .missingParam p => ↑ s!"Missing parameter: '{p}'"
    | .wrongParamType p t => ↑ s!"Parameter '{p}' doesn't have a {t} fallback"
    throw message
  | .ok ((v, trace), st') =>
    set st'
    pure (v, trace)

def render (template : Template) (params : Params) : GenerateM Html :=
  (·.fst) <$> template.renderTraced params

/--
Renders a chain of templates, passing each one's output to the next as the `"content"` parameter,
and returning what they read while they rendered.
-/
def renderManyTraced (templates : List Template) (params : Params) :
    GenerateM (Html × RenderTrace) := do
    let mut params := params
    let mut output := Html.empty
    let mut trace := {}
    for template in templates do
      let (out, t) ← template.renderTraced params
      output := out
      trace := trace ++ t
      params := params.insert "content" ↑output
    pure (output, trace)

@[inherit_doc renderManyTraced]
def renderMany (templates : List Template) (params : Params) : GenerateM Html :=
  (·.fst) <$> renderManyTraced templates params

end Template

namespace Generate


def currentDir : GenerateM System.FilePath := do
  let base := (← read).dir
  let steps ← currentPath
  pure (steps.foldl (·.join ⟨·⟩) base)

def showDrafts : GenerateM Bool := (·.config.showDrafts) <$> read

def inDir (here : Dir) (act : GenerateM α) : GenerateM α :=
  withReader (fun c => {c with ctxt.path := c.ctxt.path ++ [here.name]}) act

def inPost (here : BlogPost) (act : GenerateM α) : GenerateM α := do
  let name ← here.postName'
  withReader (fun c => {c with ctxt.path := c.ctxt.path ++ [name]}) act

end Generate

open Generate


open Template.Params (forPart)

def writePage (theme : Theme) (params : Template.Params) (template : Template := theme.pageTemplate) :
    GenerateM Template.RenderTrace := do
  ensureDir <| (← currentDir)
  let ⟨baseTemplate, modParams⟩ := theme.adHocTemplates (← currentPath) |>.getD ⟨template, id⟩
  let (rendered, trace) ←
    Template.renderManyTraced [baseTemplate, theme.primaryTemplate] (modParams params)
  let output ← rewriteOutput rendered
  let header := (← read).header
  IO.FS.withFile ((← currentDir).join "index.html") .write fun h => do
    h.putStrLn header
    h.putStrLn output.asString
  return trace

/--
How a walk over a site turns one page into output.

The walk hands over the page's template parameters and the template that renders it. Writing a
standalone HTML page is one emitter; collecting rendered HTML content is another.
-/
abbrev PageEmitter := Template.Params → Template → GenerateM Template.RenderTrace

/-- The emitter that writes standalone HTML pages. -/
def writePageEmitter (theme : Theme) : PageEmitter := fun params template =>
  writePage theme params template

def walkBlog (emit : PageEmitter) (theme : Theme) (id : Lean.Name) (txt : Part Page)
    (posts : Array BlogPost) : GenerateM Unit := do
  -- path from site to here
  let pathToBlog := (← currentPath).relativeLink

  for post in posts do
    if post.contents.metadata.map (·.draft) == some true && !(← showDrafts) then continue

    inPost post do
      IO.println s!"Generating post {← currentDir}"
      let postParams : Template.Params ← match post.contents.metadata with
        | none => forPart post.contents
        | some md => (·.insert "metadata" ⟨.mk md, #[]⟩) <$> forPart post.contents
      let postParams := postParams.insert "path" ⟨.mk pathToBlog, #[]⟩
      let _ ← emit postParams theme.postTemplate

  let «meta» ←
    match (← read).xref.blogs.find? id with
    | none => reportError s!"Blog {id} not found in traverse pass!"; pure {}
    | some «meta» => pure «meta»

  for (cat, contents) in meta.categories.toArray.qsort (·.1.name < ·.1.name) do
    withReader (fun c => {c with ctxt.path := c.ctxt.path ++ [cat.slug]}) <| do
      IO.println s!"Generating category page {← currentDir}"
      let catPosts ← contents.toList.filterMapM (m := GenerateM) fun postId => do
        let some addr := (← read).xref.pageIds.find? postId
          | pure none
        let some post := posts.find? (·.id == postId)
          | pure none
        pure <| some (addr, post)
      let postList := {{
        <ul class="post-list">
          {{← catPosts.mapM fun (_addr, p) => do
            theme.archiveEntryTemplate.render (.ofList [("path", ⟨.mk pathToBlog, #[]⟩), ("post", ⟨.mk p, #[]⟩), ("summary", ⟨.mk (← summarize p), #[]⟩)])}}
        </ul>
      }}
      let catParams := Template.Params.ofList [("title", cat.name), ("category", ⟨.mk cat, #[]⟩), ("posts", ⟨.mk postList, #[]⟩)]
      let _ ← emit catParams theme.categoryTemplate

  let postList := {{
    <ul class="post-list">
      {{← posts.mapM fun p => do
        theme.archiveEntryTemplate.render (.ofList [("path", ⟨.mk pathToBlog, #[]⟩), ("post", ⟨.mk p, #[]⟩), ("summary", ⟨.mk (← summarize p), #[]⟩)])}}
    </ul>
  }}
  let path ← currentPath
  let allCats : Post.Categories := .mk <| meta.categories.toArray.map fun (c, _) =>
    ((path / c.slug).relativeLink, c)
  let pageParams : Template.Params := (← forPart txt).insert "posts" ⟨.mk postList, #[]⟩ |>.insert "categories" ⟨.mk allCats, #[]⟩
  let _ ← emit pageParams theme.pageTemplate
where
  summarize (p : BlogPost) : GenerateM Html := do
    Html.seq <$> p.summary.mapM (GenerateM.toHtml Post)


partial def Dir.walk (emit : PageEmitter) (theme : Theme) (dir : Dir) : GenerateM Unit :=
  inDir dir <|
  match dir with
  | .page _ _ txt subPages => do
    IO.println s!"Generating page '{← currentDir}'"
    -- TODO more configurable template context
    let _ ← emit (← forPart txt) theme.pageTemplate
    for p in subPages do
      p.walk emit theme
  | .blog _ id txt posts => do
    IO.println s!"Generating blog section '{← currentDir}'"
    walkBlog emit theme id txt posts
  | .mount name source settings manifest? => do
    let mountPath ← currentPath
    let some manifest := manifest?
      | reportError <|
          s!"The mount '{name}' at '{mountPath.link}' was not resolved. " ++
          "Call `Site.resolveMounts` before building a generation context from a site."
    let dest ← currentDir
    removeTree dest
    let staticFiles := Verso.RenderedHtml.staticDir source
    if ← staticFiles.pathExists then
      IO.println s!"Copying the mounted files of '{name}' to '{dest}'"
      copyRecursively staticFiles dest
    -- The substituted root is the mount path relative to the site root, with no leading slash, so
    -- it resolves against the `<base href>` that `builtinHeader` emits.
    let root := "/".intercalate mountPath.toList
    let mounted : Template.MountedAssets := {
      variableStyles := manifest.stylesheets.filterMap fun css =>
        if css.role.placesAsVariables then some s!"{root}/{css.mountPath}" else none,
      contentStyles := manifest.stylesheets.filterMap fun css =>
        if css.role.placesAsVariables then none else some s!"{root}/{css.mountPath}",
      scripts := manifest.scripts.map fun js => (s!"{root}/{js.mountPath}", js.defer)
    }
    let mut placed : Std.HashSet String := {}
    let mut declared : Std.HashSet String := {}
    for (pagePath, mountedPage) in manifest.pages do
      for (fragmentName, _) in mountedPage.fragments do
        declared := declared.insert fragmentName.toString
      let trace ←
        withReader (fun c => {c with ctxt.path := mountPath ++ pagePath, mounted}) <| do
          IO.println s!"Generating mounted page '{← currentDir}'"
          let mut params : Template.Params := .ofList [
            ("title", ⟨.mk mountedPage.title, #[.mk (Html.text false mountedPage.titleHtml)]⟩)]
          for (fragmentName, fragment) in mountedPage.fragments do
            let text ← IO.FS.readFile (source / fragment.file)
            let text := Verso.RenderedHtml.substitute fragment.rootToken root text
            params := params.insert s!"fragments.{fragmentName}" ⟨.mk (Html.text false text), #[]⟩
          emit params theme.pageTemplate
      placed := placed.insertMany trace.params
    for fragmentName in declared.toArray.qsort (· < ·) do
      if placed.contains s!"fragments.{fragmentName}" then continue
      if settings.droppedFragments.any (·.toString == fragmentName) then continue
      reportWarning <|
        s!"The mount '{name}' at '{mountPath.link}' declares the fragment '{fragmentName}', " ++
        "which no template placed. List it among the mount's dropped fragments to leave it out " ++
        "on purpose."
  | .static _ file => do
    IO.println s!"Copying from static '{file}' to '{(← currentDir)}'"
    replaceTree file (← currentDir)

def Site.walk (emit : PageEmitter) (theme : Theme) (site : Site) : GenerateM Unit := do
  match site with
  | .page _ txt subPages =>
    let _ ← emit (← forPart txt) theme.pageTemplate
    for p in subPages do
      p.walk emit theme
  | .blog id txt posts =>
    walkBlog emit theme id txt posts

def writeBlog (theme : Theme) (id : Lean.Name) (txt : Part Page) (posts : Array BlogPost) :
    GenerateM Unit :=
  walkBlog (writePageEmitter theme) theme id txt posts

def Dir.generate (theme : Theme) (dir : Dir) : GenerateM Unit :=
  dir.walk (writePageEmitter theme) theme

def Site.generate (theme : Theme) (site : Site) : GenerateM Unit :=
  site.walk (writePageEmitter theme) theme
