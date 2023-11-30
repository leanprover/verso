import Lean

import LeanDoc.Genre.Blog.Site

open Lean Elab Macro Term

open LeanDoc Genre Blog Doc Concrete

namespace LeanDoc.Genre.Blog.Site.Syntax

declare_syntax_cat site_spec
declare_syntax_cat page_spec
declare_syntax_cat post_spec
declare_syntax_cat dir_spec
declare_syntax_cat date

/-- A site with only a single page -/
scoped syntax ident : site_spec
/-- A site with sub-pages -/
scoped syntax withPosition(ident (colGt dir_spec)?) : site_spec

/-- A text page -/
scoped syntax withPosition(str ident (colGt dir_spec)?) : page_spec
/-- Include a static files directory -/
scoped syntax "static" str " => " str : page_spec

/-- A directory of pages -/
scoped syntax "/" withPosition((colEq page_spec)+) : dir_spec
/-- A directory of blog posts -/
scoped syntax "/" withPosition((colEq post_spec)+) : dir_spec

/-- A blog post -/
scoped syntax ident "by" str,+ "on" date ("(" "draft" ")")? : post_spec

/-- Date: Y-M-D -/
scoped syntax num "-" num "-" num : date

scoped syntax "site" site_spec : term
scoped syntax "page" page_spec : term
scoped syntax "post" post_spec : term
scoped syntax "dir" dir_spec : term

def resolvedDocName [Monad m] [MonadResolveName m] [MonadEnv m] [MonadError m] (id : TSyntax `ident) : m (TSyntax `ident) :=
  mkIdentFrom id <$> resolveGlobalConstNoOverload (mkIdentFrom id (docName id.getId))


macro_rules
  | `(term| site $id:ident) => do
    `({frontPage := (%doc $id), contents := .pages #[] : Site})
  | `(term| site $id:ident $contents:dir_spec) =>
    `({frontPage := (%doc $id), contents := (dir $contents) : Site})
  | `(term| page $name:str $id:ident) =>
    `(.page $name (%docName $id) (%doc $id) (.pages #[]))
  | `(term| page $name:str $id:ident $d:dir_spec) => do
    `(.page $name (%docName $id) (%doc $id) (dir $d))
  | `(term| post $id:ident by $authors:str,* on $y:num-$m:num-$d:num) => do
    `({ date := ⟨$y, $m, $d⟩, authors := [$authors,*], content := (%doc $id), «draft» := false : Post})
  | `(term| post $id:ident by $authors:str,* on $y:num-$m:num-$d:num (draft)) => do
    `({ date := ⟨$y, $m, $d⟩, authors := [$authors,*], content := (%doc $id), «draft» := true : Post})
  | `(term| page static $name:str => $d:str) => `(.static $name $d)
  | `(term| dir / $pages:page_spec*) =>
    `(.pages #[$[page $pages],*])
  | `(term| dir / $posts:post_spec*) =>
    `(.blog #[$[post $posts],*])


