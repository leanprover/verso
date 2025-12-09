/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Doc
import VersoBlog.Basic
import VersoBlog.Traverse

open Verso Doc

namespace Verso.Genre.Blog

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
deriving Inhabited, Repr

def Dir.name : Dir → String
  | .page n .. => n
  | .blog n .. => n
  | .static n .. => n


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

/-- A specification of the layout of an entire site -/
inductive Site where
  /-- The root of the site is a page -/
  | page (id : Lean.Name) (text : Part Page) (contents : Array Dir)
  /-- The root of the site is a blog with its associated posts -/
  | blog (id : Lean.Name) (text : Part Page) (contents : Array BlogPost)
deriving Repr

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
    IO (Site × Blog.TraverseState) := do
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
