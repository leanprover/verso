/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.FS
import VersoBlog.Basic
import VersoBlog.Template
import VersoBlog.Theme

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
  linkTargets : LinkTargets
  /-- The root directory in which to generate the static site -/
  dir : System.FilePath
  config : Config
  rewriteHtml : Option ((logError : String → IO Unit) → TraverseContext → Html → IO Html) := none
  components : Components := {}

def Generate.Context.templateContext (ctxt : Generate.Context) (params : Template.Params) : Template.Context where
  site := ctxt.site
  config := ctxt.config
  params := params
  path := ctxt.ctxt.path
  builtInStyles := ctxt.xref.stylesheets
  builtInScripts := ctxt.xref.scripts.insert Traverse.renderMathJs
  jsFiles := ctxt.xref.jsFiles.map (·.1)
  cssFiles := ctxt.xref.cssFiles.map (·.1)
  components := ctxt.components

abbrev GenerateM := ReaderT Generate.Context (StateT (State Html) (StateT Component.State IO))

instance : Template.MonadComponents GenerateM where
  componentImpls := do return (← read).components
  saveJs js := modifyThe Component.State fun s => {s with headerJs := s.headerJs.insert js}
  saveCss css := modifyThe Component.State fun s => {s with headerCss := s.headerCss.insert css}

instance : MonadLift IO GenerateM where
  monadLift act := fun _ st => (·, st) <$> act

def Generate.rewriteOutput (html : Html) : GenerateM Html := do
  let {ctxt, config, rewriteHtml := some rewriter, ..} := (← read)
    | pure html
  rewriter config.logError ctxt html

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
    {logError := fun x => ctxt.config.logError x, headerLevel := 2}
    (bg.context_eq ▸ ctxt)
    (bg.state_eq ▸ state)
    {}
    linkTargets
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
    (txt : Part g) : GenerateM Params := do
  let titleHtml : Html ← txt.title.mapM (GenerateM.toHtml g)
  let preamble ← txt.content.mapM (GenerateM.toHtml g)
  let subParts ← txt.subParts.mapM (GenerateM.toHtml g)
  return ofList [
    ("title", ⟨.mk txt.titleString, #[.mk titleHtml]⟩),
    ("content", preamble ++ subParts)
  ]
end Params

def render (template : Template) (params : Params) : GenerateM Html := do
  match template ((← read).templateContext params) (← getThe _) with
  | .error err =>
    let message := match err with
    | .missingParam p => ↑ s!"Missing parameter: '{p}'"
    | .wrongParamType p t => ↑ s!"Parameter '{p}' doesn't have a {t} fallback"
    throw message
  | .ok (v, st') =>
    set st'
    pure v

def renderMany (templates : List Template) (params : Params) : GenerateM Html := do
    let mut params := params
    let mut output := Html.empty
    for template in templates do
      output ← template.render params
      params := params.insert "content" ↑output
    pure output

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

def writePage (theme : Theme) (params : Template.Params) (template : Template := theme.pageTemplate)
    (header : String := Html.doctype) : GenerateM Unit := do
  ensureDir <| (← currentDir)
  let ⟨baseTemplate, modParams⟩ := theme.adHocTemplates (Array.mk (← currentPath)) |>.getD ⟨template, id⟩
  let output ← rewriteOutput <| ← Template.renderMany [baseTemplate, theme.primaryTemplate] <| modParams <| params
  IO.FS.withFile ((← currentDir).join "index.html") .write fun h => do
    h.putStrLn header
    h.putStrLn output.asString

def writeBlog (theme : Theme) (id : Lean.Name) (txt : Part Page) (posts : Array BlogPost)
    (header : String := Html.doctype) : GenerateM Unit := do
  for post in posts do
    if post.contents.metadata.map (·.draft) == some true && !(← showDrafts) then continue

    inPost post do
      IO.println s!"Generating post {← currentDir}"
      let postParams : Template.Params ← match post.contents.metadata with
        | none => forPart post.contents
        | some md => (·.insert "metadata" ⟨.mk md, #[]⟩) <$> forPart post.contents
      writePage theme postParams (template := theme.postTemplate) (header := header)

  let «meta» ←
    match (← read).xref.blogs.find? id with
    | none => logError s!"Blog {id} not found in traverse pass!"; pure {}
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
            theme.archiveEntryTemplate.render (.ofList [("path", ⟨.mk "..", #[]⟩), ("post", ⟨.mk p, #[]⟩), ("summary", ⟨.mk (← summarize p), #[]⟩)])}}
        </ul>
      }}
      let catParams := Template.Params.ofList [("title", cat.name), ("category", ⟨.mk cat, #[]⟩), ("posts", ⟨.mk postList, #[]⟩)]
      writePage theme catParams (template := theme.categoryTemplate) (header := header)

  let postList := {{
    <ul class="post-list">
      {{← posts.mapM fun p => do
        theme.archiveEntryTemplate.render (.ofList [("post", ⟨.mk p, #[]⟩), ("summary", ⟨.mk (← summarize p), #[]⟩)])}}
    </ul>
  }}
  let allCats : Post.Categories := .mk <| meta.categories.toArray.map fun (c, _) =>
    (c.slug, c)
  let pageParams : Template.Params := (← forPart txt).insert "posts" ⟨.mk postList, #[]⟩ |>.insert "categories" ⟨.mk allCats, #[]⟩
  writePage theme pageParams (header := header)
where
  summarize (p : BlogPost) : GenerateM Html := do
    Html.seq <$> p.summary.mapM (GenerateM.toHtml Post)


partial def Dir.generate (theme : Theme) (dir : Dir) (header : String := Html.doctype) :
    GenerateM Unit :=
  inDir dir <|
  match dir with
  | .page _ _ txt subPages => do
    IO.println s!"Generating page '{← currentDir}'"
    -- TODO more configurable template context
    writePage theme (← forPart txt) (header := header)
    for p in subPages do
      p.generate theme header
  | .blog _ id txt posts => do
    IO.println s!"Generating blog section '{← currentDir}'"
    writeBlog theme id txt posts
  | .static _ file => do
    IO.println s!"Copying from static '{file}' to '{(← currentDir)}'"
    let dest ← currentDir
    if ← dest.pathExists then
      if ← dest.isDir then
        IO.FS.removeDirAll dest
      else
        IO.FS.removeFile dest
    copyRecursively (← currentConfig).logError file dest

def Site.generate (theme : Theme) (site : Site) (header : String := Html.doctype) :
    GenerateM Unit := do
  match site with
  | .page _ txt subPages =>
    writePage theme (← forPart txt) (header := header)
    for p in subPages do
      p.generate theme
  | .blog id txt posts =>
    writeBlog theme id txt posts
