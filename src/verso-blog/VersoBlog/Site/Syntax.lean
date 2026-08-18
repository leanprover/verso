/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Verso.Doc.Concrete
public import Verso.Doc.DocName
public import VersoBlog.Site
meta import MultiVerso.Slug

public section

open Lean Elab Macro Term

open Verso Genre Blog Doc Concrete

namespace Verso.Genre.Blog.Site.Syntax

declare_syntax_cat site_spec
declare_syntax_cat page_spec
declare_syntax_cat post_spec
declare_syntax_cat dir_spec
declare_syntax_cat blog_spec
declare_syntax_cat date

/-- A site with only a single page -/
scoped syntax ident : site_spec
/-- A site with sub-pages -/
scoped syntax withPosition(ident (colGt dir_spec)) : site_spec
/-- A site with a blog at the root -/
scoped syntax withPosition(ident (colGt blog_spec)) : site_spec

/-- A text page may contain either further text pages or be the root of a blog -/
scoped syntax withPosition(str ident (colGt (dir_spec <|> blog_spec))?) : page_spec

/-- Include a static files directory -/
scoped syntax "static" str " ← " str : page_spec
scoped syntax "static" str " <- " str : page_spec

/--
Mount a directory of rendered HTML content.

The optional settings are the fields of `MountSettings`: whether the mount appears in navigation
entries, and the fragments that the site leaves out on purpose.
-/
scoped syntax "mount" str " ← " str (" with " term)? : page_spec
scoped syntax "mount" str " <- " str (" with " term)? : page_spec

/-- A directory of pages -/
scoped syntax "/" withPosition((colEq page_spec)+) : dir_spec

/-- A directory of blog posts -/
scoped syntax "with" withPosition((colEq post_spec)+) : blog_spec

/-- A blog post -/
scoped syntax ident : post_spec

/-- Date: Y-M-D -/
scoped syntax num "-" num "-" num : date

scoped syntax "site" site_spec : term

/--
Checks at elaboration time that a mount's name is a slug, so that the site configuration language
never mangles a URL segment.
-/
meta def checkMountName (name : TSyntax `str) : MacroM Unit := do
  let str := name.getString
  if str.isEmpty || (Verso.Multi.Slug.isSlug? str).isNone then
    Macro.throwErrorAt name <|
      s!"'{str}' is not a slug, so it cannot name a mount. A mount's name is a URL segment made " ++
      "of English letters, digits, '-', and '_'."

namespace Internals
scoped syntax "page" page_spec : term
scoped syntax "post" post_spec : term
end Internals
open Internals

section
variable {m} [Monad m] [MonadResolveName m] [MonadEnv m] [MonadOptions m] [MonadLog m] [AddMessageContext m] [MonadError m]

def resolvedDocName (id : TSyntax `ident) : m (TSyntax `ident) :=
  mkIdentFrom id <$> resolveGlobalConstNoOverload (mkIdentFrom id (docName id.getId))
end

macro_rules
  | `(term| site $id:ident) => do
    ``(Site.page (%docName? $id) (%doc? $id) #[])
  | `(term| site $id:ident / $pages:page_spec*) =>
    ``(Site.page (%docName? $id) (%doc? $id) #[$[page $pages],*])
  | `(term| site $id:ident with $posts:post_spec*) =>
    ``(Site.blog (%docName? $id) (%doc? $id) #[$[post $posts],*])
  | `(term| page $name:str $id:ident) =>
    ``(Dir.page $name (%docName? $id) (%doc? $id) #[])
  | `(term| page $name:str $id:ident / $pages:page_spec*) => do
    ``(Dir.page $name (%docName? $id) (%doc? $id) #[$[page $pages],*])
  | `(term| page $name:str $id:ident with $posts:post_spec*) => do
    ``(Dir.blog $name (%docName? $id) (%doc? $id) #[$[post $posts],*])
  | `(term| post $id:ident) => do
    `({id := (%docName? $id), contents := (%doc? $id) : BlogPost})
  | `(term| page static $name:str ← $d:str) =>
    ``(Dir.static $name $d)
  | `(term| page static $name:str <- $d:str) =>
    ``(Dir.static $name $d)
  | `(term| page mount $name:str ← $d:str) => do
    checkMountName name
    ``(Dir.mkMount $name $d)
  | `(term| page mount $name:str <- $d:str) => do
    checkMountName name
    ``(Dir.mkMount $name $d)
  | `(term| page mount $name:str ← $d:str with $settings) => do
    checkMountName name
    ``(Dir.mkMount $name $d $settings)
  | `(term| page mount $name:str <- $d:str with $settings) => do
    checkMountName name
    ``(Dir.mkMount $name $d $settings)
