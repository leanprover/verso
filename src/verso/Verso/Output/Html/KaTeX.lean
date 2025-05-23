/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso.BinFiles

open Verso.BinFiles

set_option linter.missingDocs true

namespace Verso.Output.Html

/--
The minified KaTeX CSS file's contents, to be placed parallel to the JS and fonts, in a file named `katex/katex.min.css`.
-/
def katex.css : String :=
  include_str "../../../../../vendored-js/katex/katex.min.css"

/--
The minified KaTeX JS file's contents, to be placed parallel to the CSS and fonts, in a file named `katex/katex.min.js`.
-/
def katex.js : String :=
  include_str "../../../../../vendored-js/katex/katex.min.js"

/--
The KaTeX font files. Keys are filenames of the form `katex/fonts/...`.
-/
def katexFonts : Array (String × ByteArray):=
  (include_bin_dir "../../../../../vendored-js/katex/fonts").map fun (name, contents) =>
    (name.stripPrefix "../../../../../vendored-js/", contents)

/--
A short script that renders all Verso math using KaTeX.
-/
def math.js := include_str "../../../../../static-web/math.js"
