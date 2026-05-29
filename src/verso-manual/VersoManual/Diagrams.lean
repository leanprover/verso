/-
Copyright (c) 2024-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual.Basic
import VersoManual.InlineLean.Scopes
import VersoIlluminate

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html
open Verso.Output (Html)
open Verso.Doc.Html (HtmlT)
open Verso.Illuminate (elabAndStoreDiagram)
open Verso.Genre.Manual.InlineLean.Scopes (runWithOpenDecls runWithVariables)

namespace Verso.Genre.Manual

/--
How a diagram's width is specified for HTML output. The three arms make the
otherwise-mutually-exclusive `cssWidth` and `cssScale` author arguments structurally exclusive.
-/
inductive CssWidth where
  /-- Neither `cssWidth` nor `cssScale` was supplied; HTML output uses `100%`. -/
  | full
  /-- The author supplied `cssWidth := "<length>"`; the CSS length string is used verbatim. -/
  | width (length : String)
  /--
  The author supplied `cssScale := <factor>`; the factor is multiplied by the diagram's natural
  viewBox width and emitted as an `em` value. Useful for keeping line widths consistent across
  several diagrams.
  -/
  | scale (factor : Float)
deriving Quote

/--
Author-facing configuration for the Manual genre's `diagram` code block.

* `cssWidth` — the HTML width, populated by either the `cssWidth` or `cssScale` author
  argument. The two are structurally exclusive via the `CssWidth` inductive; omitting both
  yields `CssWidth.full`.
* `texWidth` — the LaTeX width. Authors supply a valid LaTeX length such as `3.5em` or
  `\textwidth`. Defaults to `\textwidth` when omitted.
* `inline` — layout hint: when `true`, the diagram is being placed inside a composite container
  (e.g. the `row` directive) and the renderer omits standalone framing such as centering.
-/
structure DiagramConfig where
  cssWidth : CssWidth
  texWidth : Option String
  inline : Bool
deriving Quote

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

/-- Argument parser for `DiagramConfig`. -/
def DiagramConfig.parse : ArgParse m DiagramConfig :=
  DiagramConfig.mk <$>
    (CssWidth.width <$> .named' `cssWidth false <|>
      CssWidth.scale <$> .named `cssScale .float false <|>
      pure .full)
    <*> .named' `texWidth true
    <*> .flag `inline false

instance : FromArgs DiagramConfig m := ⟨DiagramConfig.parse⟩

end

block_extension Block.diagram
    (svg : String) (cssWidth : String) (texWidth : String) (inline : Bool) where
  data := Json.arr #[.str svg, .str cssWidth, .str texWidth, .bool inline]
  extraCss := [
    r#"
.diagram svg text[font-family="text"] {
  font-family: var(--verso-text-font-family);
}
.diagram svg text[font-family="monospace"] {
  font-family: var(--verso-code-font-family);
}
"#
  ]
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .arr #[.str svgStr, .str css, .str _tex, .bool isInline] := data
        | reportError "Expected four-element JSON for diagram" *> pure .empty
      let style :=
        ";".intercalate <|
          s!"width: {css}" ::
          (if isInline then ["display: inline-block"] else [])
      pure {{
        <div class="diagram" style={{style}}>
          {{Html.text false svgStr}}
        </div>
      }}
  usePackages := ["\\usepackage{svg}"]
  toTeX :=
    some <| fun _ _ _ data _ => do
      let .arr #[.str svgStr, .str _css, .str tex, .bool isInline] := data
        | reportError "Expected four-element JSON for diagram" *> pure .empty
      let filename ← modifyGet fun s =>
        let fn := extraFileName s.extraFiles s!"diagram-{svgStr.hash}" "svg" svgStr
        (fn, { s with extraFiles := s.extraFiles.insert fn svgStr })

      if isInline then
        pure (.raw s!"\\includesvg[width={tex}]\{{filename}}")
      else
        pure (.raw s!"\\begin\{center}\\includesvg[width={tex}]\{{filename}}\\end\{center}\n")


open Verso.Illuminate in
/--
Renders an Illuminate diagram as a block of SVG, with an InfoView widget for interactive
preview.

The source of the code block is elaborated and evaluated as a term of type
`Illuminate.Diagram Illuminate.SVG`; the result is rendered to an SVG string and embedded in
the output. HTML output inlines the SVG; LaTeX output writes the SVG next to `main.tex` and
includes it via `\includesvg{...}`.

````
```diagram (cssWidth := "20em") (texWidth := "20em")
Illuminate.Diagram.rect 30 20
```
````

The available arguments are:

* `cssWidth := "<length>"` — a CSS length used in HTML output.
* `cssScale := <number>` — instead of `cssWidth`, a scale factor multiplied by the diagram's
  natural viewBox width and emitted as an `em` value. Useful for keeping line widths
  consistent across multiple diagrams. Mutually exclusive with `cssWidth`.
* `texWidth := "<length>"` — a valid LaTeX length used in PDF output.
* `+inline` — layout hint that omits standalone framing when the diagram is being composed
  into a larger layout (e.g. inside the `row` directive).

If neither `cssWidth` nor `cssScale` is supplied, HTML output uses `100%`. If `texWidth` is
omitted, LaTeX output uses `\textwidth`.

**LaTeX build requirements.** The `\includesvg` macro needs the `svg` LaTeX package (added
automatically to the preamble), the `inkscape` binary, and `lualatex -shell-escape`. Without
those, the document compiles to HTML but the PDF build will fail when it reaches a diagram.
-/
@[code_block]
def diagram : CodeBlockExpanderOf DiagramConfig
  | cfg, str => do
    let (svg, diagramWidth) ← elabAndStoreDiagram str
      (scope := fun act => runWithOpenDecls <| runWithVariables fun _ => act)
    let cssWidth : String :=
      match cfg.cssWidth with
      | .full => "100%"
      | .width w => w
      | .scale s =>
        if diagramWidth > 0 then s!"{diagramWidth * s}em" else "100%"
    ``(Verso.Doc.Block.other
        (Block.diagram $(quote svg) $(quote cssWidth)
        $(quote <| cfg.texWidth.getD "\\textwidth") $(quote cfg.inline))
        #[Verso.Doc.Block.code $(quote str.getString)])
