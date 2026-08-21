/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoBlog.Basic
public import VersoBlog.Component

public section

open Verso Code Highlighted WebAssets
open Verso.Output.Html.Files

namespace Verso.Genre.Blog.Traverse

open Doc

def addCssFile (filename contents : String) : TraverseM Unit := do
  for css in (← get).cssFiles do
    if filename == css.filename then
      if contents != css.contents.css then
        reportError s!"Attempted to add different content for CSS file {filename}"
      return

  modify fun s => s.addCssFile filename contents

def addJsFile (filename contents : String) (sourceMap? : Option (String × String) := none)
    (defer : Bool := false) (after : Array String := #[]) : TraverseM Unit := do
  let sourceMap? := sourceMap?.map fun (filename, contents) => ({filename, contents} : JsSourceMap)
  for js in (← get).jsFiles do
    if filename == js.filename then
      if contents != js.contents.js then
        reportError s!"Attempted to add different content for JS file {filename}"
      if sourceMap? != js.sourceMap? then
        reportError s!"Attempted to add different source map for JS file {filename}"
      return

  modify fun s => s.addJsFile filename contents (sourceMap?.map (fun m => (m.filename, m.contents))) defer after

/--
Adds the stylesheets and scripts used by rendered Lean code.

The file `"highlighting.js"` includes a specific selector that's used to apply it to a particular
part of the page. Tutorials and blogs use the same traversal, and tutorials support rendering their
content as mountable HTML archives, so the file must be able to support both the whole page and a
specific sub-region.

Traversal emits the standard version of the script. When HTML is bundled, this script is replaced by
one that targets the wrapper elements for the bundled content.
-/
def addCodeAssets : TraverseM Unit :=
  modify fun st => st
    |>.addCssFile "highlighting.css" highlightingStyle
    |>.addCssFile "tippy-border.css" tippy.border.css
    |>.addJsFile "popper.js" popper (some ("popper.min.js.map", popper.map))
    |>.addJsFile "tippy.js" tippy (some ("tippy-bundle.umd.min.js.map", tippy.map))
    |>.addJsFile "highlighting.js" highlightingJs
         (after := #["popper.js", "tippy.js"])

def genreBlock (g : Genre) [bg : BlogGenre g] : Blog.BlockExt → Array (Block g) → Blog.TraverseM (Option (Block g))
    | .highlightedCode .., _contents | .message .., _contents => do
      addCodeAssets
      pure none
    | .component name json, contents => do
      let some blk := (← read).components.blocks.find? name
        | reportError s!"No implementation found for block '{name}' during traversal"
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
      addCodeAssets
      pure none
    | .label x, _contents => do
      -- Add as target if not already present
      if let none := (← get).targets.find? x then
        let path := (← read).path
        let htmlId := (← get).freshId path x.toString.sluggify
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
        | reportError s!"No implementation found for inline '{name}' during traversal"
          pure none
      let some {traverse, jsFiles, cssFiles, ..} := inl.get? InlineComponent
        | panic! s!"Wrong type for inline component! Got {inl.typeName}"

      for (name, contents) in jsFiles do
        modify (·.addJsFile name contents)
      for (name, contents) in cssFiles do
        modify (·.addCssFile name contents)

      traverse json (contents.map (·.cast bg.inline_eq)) <&>
        Option.map (·.cast bg.inline_eq.symm)

@[implicit_reducible]
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
