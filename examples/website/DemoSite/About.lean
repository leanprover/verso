/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoBlog
open Verso Genre Blog

section
open Verso Doc Elab ArgParse
open Lean
open Verso Output Html
open Template
open scoped Lean.Doc.Syntax

@[block_component redBox]
def redBox : BlockComponent where
  toHtml id _data _goI goB contents := do
    saveCss (s!"#{id}:hover " ++ "{ border: 5px solid red; }")
    saveCss ".red-box { border: 2px solid red; }"
    pure {{<div class="red-box" id={{id}}>{{← contents.mapM goB}}</div>}}

@[directive redBox]
def redBoxImpl : DirectiveExpanderOf Unit
  | (), stxs => do
    ``(Block.other (Blog.BlockExt.component $(quote `redBox) Json.null) #[$(← stxs.mapM elabBlock),*])

block_component gallery where
  toHtml id _data _goI goB contents := do
    saveCss (s!"#{id}:hover " ++ "{ border: 5px solid red; }")
    saveCss ".red-box { border: 2px solid red; }"
    pure {{<div class="red-box" id={{id}}>{{← contents.mapM goB}}</div>}}


block_component image where
  toHtml id data _goI goB contents := do
    let .arr #[.str alt, .str url] := data
      | HtmlT.logError s!"Failed to deserialize {data}"
        pure .empty
    pure {{
      <div class="image-item" id={{id}}>
        <img href={{url}} alt={{alt}}/>
        <div class="description">{{← contents.mapM goB}}</div>
      </div>
    }}


@[directive gallery]
def galleryImpl : DirectiveExpanderOf Unit
  | (), stxs => do
    let #[stx] := stxs
      | logErrorAt (mkNullNode stxs) "Expected one block"
        return (← `(sorry))
    let `(block| dl{ $item*}) := stx
      | throwErrorAt stx "Expected definition list"
    let items ← item.mapM getItem
    ``(Block.other (Blog.BlockExt.component $(quote `gallery) Json.null) #[$(items),*])
where
  getItem : TSyntax `desc_item → DocElabM Term
    | `(desc_item|: $inls* => $desc $descs*) => do
      let #[inl] := inls.filter (fun
          | `(inline|$s:str) => s.getString.any (!·.isWhitespace)
          | _ => true)
        | throwErrorAt (mkNullNode inls) "Expected one inline"
      let `(inline|image($alt)($url)) := inl
        | throwErrorAt inl "Expected an image"
      `(Block.other (.component $(quote `image) (.arr #[$alt, $url])) #[$(← elabBlock desc), $(← descs.mapM elabBlock),*])
    | stx => throwErrorAt stx "Expected an image and description, got {stx}"

block_component +directive button' (onclick : String) where
  toHtml id _ _ goB contents := do
    saveJs <| "window.addEventListener('load', () => {" ++
      s!"document.getElementById('{id}')?.addEventListener('click', () => " ++
      "{ alert(" ++ onclick.quote ++ ");})});"
    pure {{
      <button id={{id}}>
        {{← contents.mapM goB}}
      </button>
    }}


inline_component button (onclick : String) where
  toHtml id _ goI contents := do
    saveJs <| "window.addEventListener('load', () => {" ++
      s!"document.getElementById('{id}')?.addEventListener('click', () => " ++
      "{ alert('hello');});});"
    pure {{
      <button id={{id}}>
        {{← contents.mapM goI}}
      </button>
    }}

structure ButtonArgs where
  onClick : String

instance : FromArgs ButtonArgs DocElabM where
  fromArgs := ButtonArgs.mk <$> .positional `onClick .string

@[role button]
def buttonImpl : RoleExpanderOf ButtonArgs
  | {onClick}, contents => do
    ``(button $(quote onClick) #[$(← contents.mapM elabInline),*])

end

#doc (Page) "About Me" =>

I am a hypothetical user of the blog genre, describing my work on my personal site.

This is a red box:

:::redBox

It contains things. {button ""}[like a button! *hooray!*]

:::

:::gallery

: ![abc](abc)

  bar

:::


:::button' "foo"

Here's a button

and a paragraph

:::
