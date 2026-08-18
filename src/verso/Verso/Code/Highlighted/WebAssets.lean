/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
meta import Init.System.FilePath

namespace Verso.Code.Highlighted.WebAssets


public section

def popper := include_str "../../../../../vendored-js/popper/popper.min.js"

/-- The version of Popper that Verso vendors. -/
def popper.version : String := "2.11.8"

def popper.map := include_str "../../../../../vendored-js/popper/popper.min.js.map"

def tippy := include_str "../../../../../vendored-js/tippy/tippy-bundle.umd.min.js"

/-- The version of Tippy that Verso vendors. -/
def tippy.version : String := "6.3.7"

def tippy.map := include_str "../../../../../vendored-js/tippy/tippy-bundle.umd.min.js.map.json"

def tippy.border.css := include_str "../../../../../vendored-js/tippy/border.css"

def marked := include_str "../../../../../vendored-js/marked/marked.umd.min.js"

/-- The version of Marked that Verso vendors. -/
def marked.version : String := "17.0.5"

def marked.map := include_str "../../../../../vendored-js/marked/marked.umd.min.js.map"
