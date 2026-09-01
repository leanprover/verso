/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import VersoUtil.BinFiles
meta import VersoUtil.BinFiles
public import Verso.Output.Html.Wrappers

open Verso.BinFiles

set_option linter.missingDocs true

namespace Verso.Output.Html

/--
The minified KaTeX CSS file's contents, to be placed parallel to the JS and fonts, in a file named `katex/katex.min.css`.
-/
public def katex.css : String :=
  include_str "../../../../../vendored-js/katex/katex.min.css"

/--
The minified KaTeX JS file's contents, to be placed parallel to the CSS and fonts, in a file named `katex/katex.min.js`.
-/
public def katex.js : String :=
  include_str "../../../../../vendored-js/katex/katex.min.js"

/-- The version of KaTeX that Verso vendors. -/
public def katex.version : String := "0.16.22"

/--
The KaTeX font files. Keys are filenames of the form `katex/fonts/...`.
-/
public def katexFonts : Array (String × ByteArray):=
  (include_bin_dir "../../../../../vendored-js/katex/fonts").map fun (name, contents) =>
    (name.dropPrefix "../../../../../vendored-js/" |>.copy, contents)

private def mathJsTemplate := include_str "../../../../../static-web/math.js"

/--
A short script that renders Verso math using KaTeX within each element that matches `selector`.

The script marks what it has rendered, so a page that carries it from several Verso releases renders
each piece of math once.
-/
public def mathJs (selector : String := "body") : String :=
  mathJsTemplate.replace "\"%%VERSO_WRAPPERS%%\"" selector.quote
