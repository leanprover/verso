/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import VersoUtil.BinFiles
meta import VersoUtil.BinFiles
import Verso.Output.StaticAsset
meta import Verso.Output.StaticAsset

open Verso.BinFiles

set_option linter.missingDocs true

namespace Verso.Output.Html

/--
The minified KaTeX CSS file's contents, to be placed parallel to the JS and fonts, in a file named `katex/katex.min.css`.
-/
public def katex.css : System.FilePath :=
  "katex/katex.min.css"

/--
The minified KaTeX JS file's contents, to be placed parallel to the CSS and fonts, in a file named `katex/katex.min.js`.
-/
public def katex.js : System.FilePath :=
  "katex/katex.min.js"

/--
The KaTeX font files. Keys are filenames of the form `katex/fonts/...`.
-/
public def katexFonts : List System.FilePath :=
  include_asset_dir "../../../../../vendored-js" "katex/fonts"

/--
A short script that renders all Verso math using KaTeX.
-/
public def math.js := include_str "../../../../../static-web/math.js"
