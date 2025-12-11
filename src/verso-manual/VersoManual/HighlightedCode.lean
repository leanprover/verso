/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import VersoManual.Basic
public import VersoManual.License
public import VersoManual.LicenseInfo.Licenses
public import VersoManual.Html.JsFile
public import Verso.Code.Highlighted.WebAssets

namespace Verso.Genre.Manual

open Verso.Code
open Verso.Code.Highlighted.WebAssets

open Licenses

public class CanHighlightCode (α : Type) where
  addDependencies : α → α

/--
Add the necessary frontend dependencies for showing Verso-highlighted Lean code
-/
public def withHighlighting [CanHighlightCode α] (blockOrInline : α) : α :=
  CanHighlightCode.addDependencies blockOrInline

public def popperJs : JsFile where
  filename := "popper.min.js"
  contents := Highlighted.WebAssets.popper
  sourceMap? := some {
    filename := "popper.min.js.map"
    contents := popper.map
  }

public def tippyJs : JsFile where
  filename := "tippy-bundle.umd.min.js"
  contents := tippy
  sourceMap? := some {
    filename := "tippy-bundle.umd.min.js.map"
    contents := tippy.map
  }

public def tippyCss : CssFile where
  filename := "tippy-border.css"
  contents := tippy.border.css

public def highlightAssets : HtmlAssets where
  extraCss := { CSS.mk highlightingStyle }
  extraJs := { JS.mk highlightingJs }
  extraJsFiles := { popperJs, tippyJs }
  extraCssFiles := { tippyCss }
  licenseInfo := { tippy.js, popper.js }

public instance : CanHighlightCode BlockDescr where
  addDependencies b :=
    { b with toHtmlAssets := b.toHtmlAssets.combine highlightAssets }

public instance : CanHighlightCode InlineDescr where
  addDependencies i :=
    { i with toHtmlAssets := i.toHtmlAssets.combine highlightAssets }
