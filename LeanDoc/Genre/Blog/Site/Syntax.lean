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

scoped syntax ident : site_spec
scoped syntax withPosition(ident (colGt dir_spec)?) : site_spec

scoped syntax withPosition(str ident (colGt dir_spec)?) : page_spec
scoped syntax "static" str " => " str : page_spec

scoped syntax "/" withPosition((colEq page_spec)+) : dir_spec
scoped syntax "/" withPosition((colEq post_spec)+) : dir_spec

scoped syntax ident "by" str,+ "on" date ("(" "draft" ")")? : post_spec

scoped syntax num "-" num "-" num : date

scoped syntax "site" site_spec : term
scoped syntax "page" page_spec : term
scoped syntax "post" post_spec : term
scoped syntax "dir" dir_spec : term

macro_rules
  | `(term| site $id:ident) =>
    let content := mkIdentFrom id <| docName id.getId
    `({frontPage := $content, contents := .pages #[] : Site})
  | `(term| site $id:ident $contents:dir_spec) =>
    let content := mkIdentFrom id <| docName id.getId
    `({frontPage := $content, contents := (dir $contents) : Site})
  | `(term| page $name:str $id:ident) =>
    let content := mkIdentFrom id <| docName id.getId
    `(.page $name $(quote content.getId) $content (.pages #[]))
  | `(term| page $name:str $id:ident $d:dir_spec) =>
    let content := mkIdentFrom id <| docName id.getId
    `(.page $name $(quote content.getId) $content (dir $d))
  | `(term| page static $name:str => $d:str) => `(.static $name $d)
  | `(term| post $id:ident by $authors:str,* on $y:num-$m:num-$d:num) =>
    let content := mkIdentFrom id <| docName id.getId
    `({ date := ⟨$y, $m, $d⟩, authors := [$authors,*], content := $content, «draft» := false : Post})
  | `(term| post $id:ident by $authors:str,* on $y:num-$m:num-$d:num (draft)) =>
    let content := mkIdentFrom id <| docName id.getId
    `({ date := ⟨$y, $m, $d⟩, authors := [$authors,*], content := $content, «draft» := true : Post})
  | `(term| dir / $pages:page_spec*) =>
    `(.pages #[$[page $pages],*])
  | `(term| dir / $posts:post_spec*) =>
    `(.blog #[$[post $posts],*])


