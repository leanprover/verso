/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Verso.Doc
public import VersoBlog.Basic
public import VersoBlog.Traverse
public import VersoRenderedHtml

public section

open Verso Doc

namespace Verso.Genre.Blog

/-- Settings that a site chooses for one mount. -/
structure MountSettings where
  /-- Whether the mount appears in navigation entries. -/
  showInNav : Bool := true
  /--
  The fragments that the site's templates leave out on purpose.

  A fragment that the templates never place is reported unless it is listed here.
  -/
  droppedFragments : Array Multi.Slug := #[]
deriving Inhabited, Repr, BEq

defmethod BlogPost.traverse1 (post : BlogPost) : Blog.TraverseM BlogPost := do
  let name ← post.postName
  withReader (fun ctxt => {ctxt with path := ctxt.path ++ [name]}) <| do
    let path ← (·.path) <$> read
    modify fun st =>
      {st with
        pageIds := st.pageIds.insert post.id ⟨path, post.contents.titleString⟩}
    pure {post with contents := ← Post.traverse post.contents}

/--
A directory within the layout of a site.
-/
inductive Dir where
  /-- The directory's root is the provided page -/
  | page (name : String) (id : Lean.Name) (text : Part Page) (contents : Array Dir)
  /-- The directory's root is a blog -/
  | blog (name : String) (id : Lean.Name) (text : Part Page) (contents : Array BlogPost)
  /-- The directory's root contains static files, copied from `files` when the site is generated -/
  | static (name : String) (files : System.FilePath)
  /--
  The directory's root is a directory of rendered HTML content, mounted from `source`.

  The manifest is read by `Site.resolveMounts`, which traversal calls, and is empty until then.

  The mount's pages and static files are written under the mount point without clearing it first, so
  a build into an output directory that already holds the mount leaves behind any pages that the
  content no longer has.
  -/
  | mount
      (name : Multi.Slug) (source : System.FilePath) (settings : MountSettings)
      (manifest : Option RenderedHtmlContent)
deriving Inhabited, Repr

def Dir.name : Dir → String
  | .page n .. => n
  | .blog n .. => n
  | .static n .. => n
  | .mount n .. => n.toString

/--
Builds a mount, when `name` is a well-formed slug.

A mount's name is a URL segment and the first component of every page ID that the mount registers,
so it must already be a slug; for any other name, the result is `none`.
-/
def Dir.mount? (name : String) (source : System.FilePath) (settings : MountSettings := {}) :
    Option Dir :=
  if name.isEmpty then none
  else (Multi.Slug.isSlug? name).map (Dir.mount · source settings none)

/--
Builds a mount from a name that has already been checked to be a slug.
-/
def Dir.mkMount (name : String) (source : System.FilePath) (settings : MountSettings := {}) : Dir :=
  match Dir.mount? name source settings with
  | some dir => dir
  | none =>
    panic! s!"'{name}' is not a slug, so it cannot name a mount"

/--
The page ID under which a mounted page is registered.

Page IDs are namespaced by the mount, because a site that mounts several versions of the same
content holds every internal page path once per version. The root page of a mount is the mount's
name by itself.
-/
def mountPageId (name : Multi.Slug) (path : Multi.Path) : Lean.Name :=
  path.foldl (fun n seg => n.str seg) (.mkSimple name.toString)

/--
Registers a page ID, reporting a conflict rather than overwriting one that is already present with a
different value.

Traversal runs to a fixed point, so writes must be monotone.
-/
def addPageId (id : Lean.Name) («meta» : Info.PageMeta) : Blog.TraverseM Unit := do
  if let some existing := (← get).pageIds.find? id then
    unless existing == «meta» do
      reportError <|
        s!"Two pages have the ID '{id}': one at '{existing.path.link}' and one at " ++
        s!"'{«meta».path.link}'"
    return
  modify fun st => {st with pageIds := st.pageIds.insert id «meta»}


partial def Dir.traverse1 (dir : Dir) : Blog.TraverseM Dir := do
  match dir with
  | .page name id txt contents =>
    withReader (fun ctxt => {ctxt with path := ctxt.path ++ [name]}) <| do
      let path ← (·.path) <$> read
      modify (fun st => {st with pageIds := st.pageIds.insert id ⟨path, txt.titleString⟩})
      let txt' ← Page.traverse txt
      .page name id txt' <$> contents.mapM Dir.traverse1
  | .blog name id txt posts =>
    withReader (fun ctxt => {ctxt with path := ctxt.path ++ [name]}) <| do
      let path ← (·.path) <$> read
      modify fun st =>
        {st with pageIds := st.pageIds.insert id ⟨path, txt.titleString⟩}
      modify fun st =>
        {st with blogs := st.blogs.insert id <| st.blogs.find? id |>.getD {}}
      -- We have to insert the posts into the categories here, rather than in
      -- BlogPost.traverse1, because the categorization is local to this
      -- particular sub-blog
      for p in posts do
        for cat in p.contents.metadata.map (·.categories) |>.getD [] do
          modify fun st =>
            let ⟨info⟩ := st.blogs.find? id |>.getD {}
            let catPages := info.getD cat {} |>.insert p.id
            {st with blogs := st.blogs.insert id ⟨info.insert cat catPages⟩}
      let txt' ← Page.traverse txt
      .blog name id txt' <$> posts.mapM BlogPost.traverse1
  | .static .. => pure dir
  | .mount name _source _settings manifest? =>
    withReader (fun ctxt => {ctxt with path := ctxt.path ++ [name.toString]}) <| do
      let path ← (·.path) <$> read
      match manifest? with
      | none =>
        reportError <|
          s!"The mount '{name}' at '{path.link}' was not resolved. " ++
          "Call `Site.resolveMounts` before building a generation context from a site."
        pure dir
      | some manifest =>
        for (pagePath, mounted) in manifest.pages do
          addPageId (mountPageId name pagePath) ⟨path ++ pagePath, mounted.title⟩
        pure dir

/-- A specification of the layout of an entire site -/
inductive Site where
  /-- The root of the site is a page -/
  | page (id : Lean.Name) (text : Part Page) (contents : Array Dir)
  /-- The root of the site is a blog with its associated posts -/
  | blog (id : Lean.Name) (text : Part Page) (contents : Array BlogPost)
deriving Repr

/--
Reads the manifest of every mount whose manifest is empty.

It is idempotent, and `Site.traverse` calls it, so a site that is traversed needs no explicit call.
-/
partial def Dir.resolveMounts (dir : Dir) : IO Dir := do
  match dir with
  | .page name id txt contents => return .page name id txt (← contents.mapM Dir.resolveMounts)
  | .blog .. | .static .. => return dir
  | .mount _ _ _ (some _) => return dir
  | .mount name source settings none =>
    let loaded ← Verso.RenderedHtml.load source
    return .mount name source settings (some loaded.manifest)

@[inherit_doc Dir.resolveMounts]
def Site.resolveMounts (site : Site) : IO Site := do
  match site with
  | .page id txt contents => return .page id txt (← contents.mapM Dir.resolveMounts)
  | .blog .. => return site

/--
Inserts a directory into a site at the given path, which names the page that is to hold it.

The empty path is the site's root. A blog, a static directory, and a mount hold no directories, so a
path that names one of them is an error that names the path.
-/
partial def Site.insertDir (site : Site) (path : List String) (dir : Dir) : IO Site := do
  match site with
  | .blog .. =>
    throw <| .userError <|
      s!"The site's root is a blog, so it holds no directories. " ++
      s!"'{"/".intercalate path}' cannot hold '{dir.name}'."
  | .page id txt contents => return .page id txt (← insert contents path)
where
  insert (contents : Array Dir) : List String → IO (Array Dir)
    | [] => do
      if contents.any (·.name == dir.name) then
        throw <| .userError <|
          s!"'{"/".intercalate path}' already holds '{dir.name}'."
      return contents.push dir
    | step :: more => do
      let some i := contents.findIdx? (·.name == step)
        | throw <| .userError s!"There is no page at '{step}' to hold '{dir.name}'"
      match contents[i]! with
      | .page name id txt subs => return contents.set! i (.page name id txt (← insert subs more))
      | _ =>
        throw <| .userError <|
          s!"'{step}' is not a page, so it holds no directories. " ++
          s!"It cannot hold '{dir.name}'."

/--
Inserts a mount into a site at the given path, which names the page that is to hold it.

A name that is not a slug and a path that names something other than a page are errors.
-/
def Site.insertMount
    (site : Site) (path : List String) (name : String) (source : System.FilePath)
    (settings : MountSettings := {}) : IO Site := do
  let some dir := Dir.mount? name source settings
    | throw <| .userError <|
        s!"'{name}' is not a slug, so it cannot name a mount. A mount's name is a URL segment " ++
        "made of English letters, digits, '-', and '_'."
  site.insertDir path dir

/-- Perform a single pass of the traverse step on a site -/
def Site.traverse1 (site : Site) : Blog.TraverseM Site := do
  match site with
  | .page id txt contents =>
    .page id <$> Page.traverse txt <*> contents.mapM Dir.traverse1
  | .blog id txt posts =>
    .blog id <$> Page.traverse txt <*> posts.mapM BlogPost.traverse1

/-- Compute a fixed point of the traverse step on a site -/
def Site.traverse
    (site : Site) (config : Config)
    (components : Components) :
    BuildLogT IO (Site × Blog.TraverseState) := do
  let site ← site.resolveMounts
  let topCtxt : Blog.TraverseContext := {path := .root, config, components}
  let logVerbose := (if config.verbose then (fun _ => pure ()) else IO.println)
  let remoteContent ← Multi.updateRemotes false config.remoteInfoConfigPath logVerbose
  let mut state : Blog.TraverseState := {remoteContent}
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
  currentPath : m Multi.Path

export MonadPath (currentPath)


def relative [Monad m] [MonadConfig m] [MonadPath m] (target : List String) : m (List String) := do
  return relativize (← currentPath).toList target
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
