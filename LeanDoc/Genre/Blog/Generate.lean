import LeanDoc.Genre.Blog.Basic
import LeanDoc.Genre.Blog.Template
import LeanDoc.Genre.Blog.Theme

open LeanDoc Doc Html HtmlM

namespace LeanDoc.Genre.Blog

instance : MonadConfig (HtmlM Blog) where
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

abbrev GenerateM := ReaderT Generate.Context IO

instance : MonadPath GenerateM where
  currentPath := do return (← read).ctxt.path

instance : MonadConfig GenerateM where
  currentConfig := do return (← read).config

namespace Template

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

def inPage (here : Page) (act : GenerateM α) : GenerateM α :=
  withReader (fun c => {c with ctxt.path := c.ctxt.path ++ [here.name]}) act

def inPost (here : Post) (act : GenerateM α) : GenerateM α :=
  withReader (fun c => {c with ctxt.path := c.ctxt.path ++ [c.ctxt.config.postName here.date here.content.titleString ]}) act



end Generate

open Generate

mutual
  partial def Dir.generate (theme : Theme) : Dir Page → GenerateM Unit
    | .pages content => do
      for page in content do
        inPage page <|
          page.generate theme
    | .blog posts => do
      for post in posts do
          if post.draft && !(← showDrafts) then continue
          inPost post <| do
            let output ← Template.renderMany [theme.postTemplate, theme.primaryTemplate] <| .forPart (← read).ctxt (← read).xref post.content
            ensureDir (← currentDir)
            IO.FS.withFile ((← currentDir).join "index.html") .write fun h => do
              h.putStrLn output.asString

  partial def Page.generate (theme : Theme) : Page → GenerateM Unit
    | .page _ txt subPages => do
      ensureDir <| (← currentDir)
      -- TODO more configurable template context
      let postList ←
        if let .blog ps := subPages then
          some <$> ps.mapM fun p =>
            theme.archiveEntryTemplate.render (.ofList [("post", ⟨.mk p, #[]⟩)])
        else pure none
      let pageParams : Template.Params := .forPart (← read).ctxt (← read).xref txt

      let output ← Template.renderMany [theme.pageTemplate, theme.primaryTemplate] <|
        match postList with
        | none => pageParams
        | some ps => pageParams.insert "posts" ⟨.mk (Html.seq ps), #[]⟩

      IO.FS.withFile ((← currentDir).join "index.html") .write fun h =>
        h.putStrLn output.asString
      subPages.generate theme
end

def Site.generate (theme : Theme) (site : Site): GenerateM Unit := do
  let root ← currentDir
  ensureDir root
  let output ← Template.renderMany [theme.pageTemplate, theme.primaryTemplate] <| .forPart (← read).ctxt (← read).xref site.frontPage
  let filename := root.join "index.html"
  IO.FS.withFile filename .write fun h => do
    h.putStrLn output.asString

  site.contents.generate theme
