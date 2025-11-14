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

public def tippyCss := ("tippy-border.css", tippy.border.css)

public instance : CanHighlightCode BlockDescr where
  addDependencies b :=
    {b with
      extraCss := highlightingStyle :: b.extraCss
      extraJs := highlightingJs :: b.extraJs
      extraJsFiles := popperJs :: tippyJs :: b.extraJsFiles
      extraCssFiles := tippyCss :: b.extraCssFiles
      licenseInfo := b.licenseInfo |>.insert tippy.js |>.insert popper.js
      }

public instance : CanHighlightCode InlineDescr where
  addDependencies i :=
    {i with
      extraCss := highlightingStyle :: i.extraCss
      extraJs := highlightingJs :: i.extraJs
      extraJsFiles := popperJs :: tippyJs :: i.extraJsFiles
      extraCssFiles := tippyCss :: i.extraCssFiles
      licenseInfo := i.licenseInfo |>.insert tippy.js |>.insert popper.js
      }
