import LeanDoc.Doc
import LeanDoc.Genre.Blog.Basic

open LeanDoc Doc

namespace LeanDoc.Genre.Blog
inductive Dir α where
  | pages (subPages : Array α)
  | blog (posts : Array Post)
deriving Inhabited

defmethod Post.traverse1 (post : Post) : Blog.TraverseM Post :=
  withReader (fun ctxt => {ctxt with path := ctxt.path ++ [ctxt.config.postName post.date post.content.content.titleString]}) <| do
    let content' ← Blog.traverse post.content
    pure {post with content := content'}

def Dir.traverse1 (dir : Dir α) (sub : α → Blog.TraverseM α) : Blog.TraverseM (Dir α) :=
  match dir with
  | .pages subs => .pages <$> subs.mapM sub
  | .blog posts => .blog <$> posts.mapM Post.traverse1

inductive Page where
  | page (name : String) (id : Lean.Name) (text : Doc Blog) (contents : Dir Page)
  | static (name : String) (files : System.FilePath)

instance : Inhabited Page where
  default := .page default default default default

def Page.name : Page → String
  | .page n .. => n
  | .static n .. => n

partial def Page.traverse1 (nav : Page) : Blog.TraverseM Page := do
  match nav with
  | .page name id txt contents =>
    withReader (fun ctxt => {ctxt with path := ctxt.path ++ [name]}) <| do
      let path ← (·.path) <$> read
      modify (fun st => {st with pageIds := st.pageIds.insert id path})
      let txt' ← Blog.traverse txt
      .page name id txt' <$> contents.traverse1 Page.traverse1
  | .static .. => pure nav

structure Site where
  frontPage : Doc Blog
  contents : Dir Page

def Site.traverse1 (site : Site) : Blog.TraverseM Site := do
    let frontPage' ← Blog.traverse site.frontPage
    let contents' ← site.contents.traverse1 Page.traverse1
    pure ⟨frontPage', contents'⟩


def Site.traverse (site : Site) (config : Config) : IO (Site × Blog.TraverseState) := do
  let topCtxt : Blog.TraverseContext := ⟨[], config⟩
  let mut state : Blog.TraverseState := {}
  let mut site := site
  repeat -- TODO add max iterations
    let (site', state') ← StateT.run (ReaderT.run site.traverse1 topCtxt) state
    if state' == state then
      return (site', state')
    else
      state := state'
      site := site'
  return (site, state)

class MonadPath (m : Type → Type u) where
  currentPath : m (List String)

export MonadPath (currentPath)

def postName [Monad m] [MonadConfig m] (post : Post) : m String := do
  pure <| (← currentConfig).postName post.date post.content.content.titleString

def relative [Monad m] [MonadConfig m] [MonadPath m] (target : List String) : m (List String) := do
  return relativize (← currentPath) target
where
  relativize (me target : List String) : List String :=
    match me, target with
    | [], any => any
    | any, [] => any.map (fun _ => "..")
    | x :: xs, y :: ys =>
      if x == y then
        relativize xs ys
      else
        (x :: xs).map (fun _ => "..") ++ (y :: ys)
