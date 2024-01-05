import LeanDoc.Genre.Blog.Basic
import LeanDoc.Genre.Blog.Template
import LeanDoc.Genre.Blog.Theme

open LeanDoc Doc Output Html HtmlT

namespace LeanDoc.Genre.Blog

instance [Monad m] : MonadConfig (HtmlT Post m) where
  currentConfig := do
    let (_, ctxt, _) ← read
    pure ctxt.config

instance [Monad m] : MonadConfig (HtmlT Page m) where
  currentConfig := do
    let (_, ctxt, _) ← read
    pure ctxt.config

structure Generate.Context where
  site : Site
  ctxt : TraverseContext
  xref : TraverseState
  /-- The root directory in which to generate the static site -/
  dir : System.FilePath
  config : Config

def Generate.Context.templateContext (ctxt : Generate.Context) (params : Template.Params) : Template.Context where
  site := ctxt.site
  config := ctxt.config
  params := params
  path := ctxt.ctxt.path
  builtInStyles := ctxt.xref.stylesheets
  builtInScripts := ctxt.xref.scripts.insert Traverse.renderMathJs

abbrev GenerateM := ReaderT Generate.Context IO

instance : MonadPath GenerateM where
  currentPath := do return (← read).ctxt.path

instance : MonadConfig GenerateM where
  currentConfig := do return (← read).config

open BlogGenre in
def GenerateM.toHtml (g : Genre) [BlogGenre g] [ToHtml g IO α] (x : α) : GenerateM Html := do
  let {ctxt := ctxt, xref := state, ..} ← read
  g.toHtml (m := IO) {logError := fun x => ctxt.config.logError x, headerLevel := 2}
    (BlogGenre.traverseContextEq (genre := g) ▸ ctxt)
    (traverseStateEq (genre := g) ▸ state)
    x

namespace Template

namespace Params
def forPart [BlogGenre g] [GenreHtml g IO] [ToHtml g IO (Part g)] (txt : Part g) : GenerateM Params := do
  let titleHtml := {{ <h1> {{ ← txt.title.mapM (GenerateM.toHtml g) }} </h1>}}
  let preamble ← txt.content.mapM (GenerateM.toHtml g)
  let subParts ← txt.subParts.mapM (GenerateM.toHtml g)
  return ofList [
    ("title", ⟨.mk txt.titleString, #[.mk titleHtml]⟩),
    ("content", preamble ++ subParts)
  ]
end Params

def render (template : Template) (params : Params) : GenerateM Html := do
  match template ((← read).templateContext params) with
  | .error err =>
    let message := match err with
    | .missingParam p => ↑ s!"Missing parameter: '{p}'"
    | .wrongParamType p t => ↑ s!"Parameter '{p}' doesn't have a {t} fallback"
    throw message
  | .ok v => pure v

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

def ensureDir (dir : System.FilePath) : IO Unit := do
  if !(← dir.pathExists) then
    IO.FS.createDirAll dir
  if !(← dir.isDir) then
    throw (↑ s!"Not a directory: {dir}")

def inDir (here : Dir) (act : GenerateM α) : GenerateM α :=
  withReader (fun c => {c with ctxt.path := c.ctxt.path ++ [here.name]}) act

def inPost (here : BlogPost) (act : GenerateM α) : GenerateM α := do
  let name ← here.postName'
  withReader (fun c => {c with ctxt.path := c.ctxt.path ++ [name]}) act

end Generate

open Generate

open IO.FS in
partial def copyRecursively (src tgt : System.FilePath) : IO Unit := do
  if (← src.metadata).type == .symlink then
    pure () -- TODO
  if ← src.isDir then
    ensureDir tgt
    for d in ← src.readDir do
      copyRecursively d.path (tgt.join d.fileName)
  else
    withFile src .read fun h =>
      withFile tgt .write fun h' => do
        let mut buf ← h.read 1024
        while !buf.isEmpty do
          h'.write buf
          buf ← h.read 1024

open Template.Params (forPart)

def writePage (theme : Theme) (params : Template.Params) (template : Template := theme.pageTemplate) : GenerateM Unit := do
  ensureDir <| (← currentDir)
  let ⟨baseTemplate, modParams⟩ := theme.adHocTemplates (Array.mk (← currentPath)) |>.getD ⟨template, id⟩
  let output ← Template.renderMany [baseTemplate, theme.primaryTemplate] <| modParams <| params
  IO.FS.withFile ((← currentDir).join "index.html") .write fun h => do
    h.putStrLn "<!DOCTYPE html>"
    h.putStrLn output.asString

def writeBlog (theme : Theme) (txt : Part Page) (posts : Array BlogPost) : GenerateM Unit := do
  let postList ← posts.mapM fun p =>
      theme.archiveEntryTemplate.render (.ofList [("post", ⟨.mk p, #[]⟩)])
  let pageParams : Template.Params := (← forPart txt).insert "posts" ⟨.mk (Html.seq postList), #[]⟩
  writePage theme pageParams
  for post in posts do
    if post.contents.metadata.map (·.draft) == some true && !(← showDrafts) then continue
    inPost post do
      IO.println s!"Generating post {← currentDir}"
      let postParams : Template.Params ← match post.contents.metadata with
        | none => forPart post.contents
        | some md => (·.insert "metadata" ⟨.mk md, #[]⟩) <$> forPart post.contents
      writePage theme postParams (template := theme.postTemplate)

mutual
  partial def Dir.generate (theme : Theme) (dir : Dir) : GenerateM Unit :=
    inDir dir <|
    match dir with
    | .page _ _ txt subPages => do
      IO.println s!"Generating page {← currentDir}"
      -- TODO more configurable template context
      writePage theme (← forPart txt)
      for p in subPages do
        p.generate theme
    | .blog _ _ txt posts => do
      IO.println s!"Generating blog section {← currentDir}"
      writeBlog theme txt posts
    | .static _ file => do
      IO.println s!"Copying from {file} to {(← currentDir)}"
      let dest ← currentDir
      if ← dest.pathExists then
        if ← dest.isDir then
          IO.FS.removeDirAll dest
        else
          IO.FS.removeFile dest
      copyRecursively file dest


end

def Site.generate (theme : Theme) (site : Site): GenerateM Unit := do
  match site with
  | .page _ txt subPages =>
    writePage theme (← forPart txt)
    for p in subPages do
      p.generate theme
  | .blog _ txt posts =>
    writeBlog theme txt posts
