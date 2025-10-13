/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoBlog.Basic
import VersoBlog.Component

open Verso Code Highlighted WebAssets

namespace Verso.Genre.Blog.Traverse

open Doc

def renderMathJs : String :=
"document.addEventListener(\"DOMContentLoaded\", () => {
    for (const m of document.querySelectorAll(\".math.inline\")) {
        katex.render(m.textContent, m, {throwOnError: false, displayMode: false});
    }
    for (const m of document.querySelectorAll(\".math.display\")) {
        katex.render(m.textContent, m, {throwOnError: false, displayMode: true});
    }
});"

def addCssFile (filename contents : String) : TraverseM Unit := do
  for (fn, css) in (← get).cssFiles do
    if filename == fn then
      if contents != css then
        logError s!"Attempted to add different content for CSS file {filename}"
      return

  modify fun s => s.addCssFile filename contents

def addJsFile (filename contents : String) (sourceMap? : Option (String × String) := none) : TraverseM Unit := do
  for (fn, js, map?) in (← get).jsFiles do
    if filename == fn then
      if contents != js then
        logError s!"Attempted to add different content for JS file {filename}"
      if sourceMap? != map? then
        logError s!"Attempted to add different source map for JS file {filename}"
      return

  modify fun s => s.addJsFile filename contents sourceMap?

def genreBlock (g : Genre) [bg : BlogGenre g] : Blog.BlockExt → Array (Block g) → Blog.TraverseM (Option (Block g))
    | .highlightedCode .., _contents | .message .., _contents => do
      modify fun st => {st with
        stylesheets := st.stylesheets.insert highlightingStyle,
        scripts := st.scripts.insert highlightingJs
      } |>.addJsFile "popper.js" popper (some ("popper.min.js.map", popper.map))
        |>.addJsFile "tippy.js" tippy (some ("tippy-bundle.umd.min.js.map", tippy.map))
        |>.addCssFile "tippy-border.css" tippy.border.css
      pure none
    | .component name json, contents => do
      let some blk := (← read).components.blocks.find? name
        | logError s!"No implementation found for block '{name}' during traversal"
          pure none
      let some {traverse, jsFiles, cssFiles, ..} := blk.get? BlockComponent
        | panic! s!"Wrong type for block component! Got {blk.typeName}"

      for (name, contents) in jsFiles do
        modify (·.addJsFile name contents)
      for (name, contents) in cssFiles do
        modify (·.addCssFile name contents)

      traverse json (contents.map (·.cast bg.inline_eq bg.block_eq)) <&>
        Option.map (·.cast bg.inline_eq.symm bg.block_eq.symm)
    | _, _ => pure none

def genreInline (g : Genre) [bg : BlogGenre g] : Blog.InlineExt → Array (Inline g) → Blog.TraverseM (Option (Inline g))
    | .highlightedCode .., _contents | .customHighlight .., _contents | .message .., _contents => do
      modify fun st => {st with
        stylesheets := st.stylesheets.insert highlightingStyle,
        scripts := st.scripts.insert highlightingJs
      } |>.addJsFile "popper.js" popper (some ("popper.min.js.map", popper.map))
        |>.addJsFile "tippy.js" tippy (some ("tippy-bundle.umd.min.js.map", tippy.map))
        |>.addCssFile "tippy-border.css" tippy.border.css
      pure none
    | .label x, _contents => do
      -- Add as target if not already present
      if let none := (← get).targets.find? x then
        let path := (← read).path
        let htmlId := (← get).freshId path x
        modify fun st => {st with targets := st.targets.insert x ⟨path, htmlId⟩}
      pure none
    | .ref _x, _contents =>
      -- TODO backreference
      pure none
    | .pageref _x _id?, _contents =>
      -- TODO backreference
      pure none
    | .htmlSpan .., _ | .blob .., _ | .lexedText .., _ => pure none
    | .component name json, contents => do
      let some inl := (← read).components.inlines.find? name
        | logError s!"No implementation found for inline '{name}' during traversal"
          pure none
      let some {traverse, jsFiles, cssFiles, ..} := inl.get? InlineComponent
        | panic! s!"Wrong type for inline component! Got {inl.typeName}"

      for (name, contents) in jsFiles do
        modify (·.addJsFile name contents)
      for (name, contents) in cssFiles do
        modify (·.addCssFile name contents)

      traverse json (contents.map (·.cast bg.inline_eq)) <&>
        Option.map (·.cast bg.inline_eq.symm)

def traverser (g : Genre) [bg : BlogGenre g] : Traverse g Blog.TraverseM where
  part _ := pure none
  block _ := pure ()
  inline _ := pure ()
  genrePart _ _ := pure none
  genreBlock := bg.block_eq ▸ genreBlock g
  genreInline := bg.inline_eq ▸ genreInline g

instance : TraversePart Page := {}

instance : TraverseBlock Page := {}

instance : Traverse Page Blog.TraverseM := traverser Page

instance : TraversePart Post := {}

instance : TraverseBlock Post := {}

instance : Traverse Post Blog.TraverseM := traverser Post

end Traverse
