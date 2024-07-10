import Lean.Elab.Command

namespace Verso.Code.Highlighted.WebAssets

open Lean Elab Command

def popper := include_str "../../../../../vendored-js/popper/popper.min.js"

def tippy := include_str "../../../../../vendored-js/tippy/tippy-bundle.umd.min.js"

def tippy.border.css := include_str "../../../../../vendored-js/tippy/border.css"
