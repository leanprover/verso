/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso

import VersoManual.Basic
import VersoManual.License

namespace Verso.Genre.Manual

open Verso.Code
open Verso.Code.Highlighted.WebAssets

open Licenses

class CanHighlightCode (α : Type) where
  addDependencies : α → α

/--
Add the necessary frontend dependencies for showing Verso-highlighted Lean code
-/
def withHighlighting [CanHighlightCode α] (blockOrInline : α) : α :=
  CanHighlightCode.addDependencies blockOrInline

instance : CanHighlightCode BlockDescr where
  addDependencies b :=
    {b with
      extraCss := highlightingStyle :: b.extraCss
      extraJs := highlightingJs :: b.extraJs
      extraJsFiles := {filename := "popper.js", contents := popper} :: {filename := "tippy.js", contents := tippy} :: b.extraJsFiles
      extraCssFiles := ("tippy-border.css", tippy.border.css) :: b.extraCssFiles
      licenseInfo := b.licenseInfo |>.insert tippy.js |>.insert popper.js
      }

instance : CanHighlightCode InlineDescr where
  addDependencies i :=
    {i with
      extraCss := highlightingStyle :: i.extraCss
      extraJs := highlightingJs :: i.extraJs
      extraJsFiles := {filename := "popper.js", contents := popper} :: {filename := "tippy.js", contents := tippy} :: i.extraJsFiles
      extraCssFiles := ("tippy-border.css", tippy.border.css) :: i.extraCssFiles
      licenseInfo := i.licenseInfo |>.insert tippy.js |>.insert popper.js
      }
