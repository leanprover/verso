/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual.Basic
import Verso.Doc.ArgParse
import Verso.Doc.Elab

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse
open Lean.Doc.Syntax
open Lean Elab

set_option pp.rawOnError true

namespace Verso.Genre.Manual

block_extension Block.figure (src : String) (alt : String) where
  data := ToJson.toJson (src, alt)

  traverse _id _data _contents := pure none

  toTeX := some <| fun _goI goB _id data blocks =>
    open Verso.Output.TeX in do
    match FromJson.fromJson? data (α := String × String) with
    | .error e =>
      IO.println s!"Error deserializing figure data: {e}"
      return .empty
    | .ok (src, _alt) =>
      let captionParts ← blocks.mapM goB
      let caption := captionParts.foldl (· ++ ·) .empty
      let captionTex : Output.TeX :=
        if blocks.isEmpty then .empty
        else .seq #[.raw "  \\caption{", caption, .raw "}\n"]
      return .seq #[
        .raw "\\begin{figure}[h]\n  \\centering\n  \\includegraphics[width=\\linewidth]{",
        .raw src,
        .raw "}\n",
        captionTex,
        .raw "\\end{figure}\n"
      ]

  toHtml :=
    open Verso.Doc.Html in
    open Verso.Output.Html in
    some <| fun _goI goB _id data blocks => do
      match FromJson.fromJson? data (α := String × String) with
      | .error e =>
        HtmlT.logError s!"Error deserializing figure data: {e}"
        return .empty
      | .ok (src, alt) =>
        if blocks.isEmpty then
          return {{ <figure class="verso-figure"><img src={{src}} alt={{alt}}/></figure> }}
        else
          let parts ← blocks.mapM goB
          let captionHtml := parts.foldl (· ++ ·) .empty
          return {{
            <figure class="verso-figure">
              <img src={{src}} alt={{alt}}/>
              <figcaption>{{captionHtml}}</figcaption>
            </figure>
          }}

  usePackages := ["graphicx"]

  extraCss := [r#"
figure.verso-figure {
  margin: 2rem auto;
  text-align: center;
  max-width: 100%;
}
figure.verso-figure img {
  max-width: 100%;
  height: auto;
  display: block;
  margin: 0 auto;
  border-radius: 4px;
}
figure.verso-figure figcaption {
  margin-top: 0.75rem;
  font-size: 0.9em;
  color: var(--verso-text-color, #444);
  font-style: italic;
}
"#]

/-- Configuration for the `figure` directive. -/
structure FigureConfig where
  /-- Path or URL of the image (positional argument) -/
  src : String
  /-- Alt text for accessibility and non-visual rendering -/
  alt : String := ""

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m]

def FigureConfig.parse : ArgParse m FigureConfig :=
  FigureConfig.mk <$> .positional `src .string <*> .namedD `alt .string ""

instance : FromArgs FigureConfig m := ⟨FigureConfig.parse⟩

end

/--
Includes an image as a block-level figure in the document.

**Syntax:**
```
:::figure "path/to/image.png" (alt := "alt text")
Optional caption text.
:::
```
-/
@[directive]
def figure : DirectiveExpanderOf FigureConfig
  | cfg, contents => do
    ``(Block.other (Block.figure $(quote cfg.src) $(quote cfg.alt))
        #[$[$(← contents.mapM elabBlock)],*])
