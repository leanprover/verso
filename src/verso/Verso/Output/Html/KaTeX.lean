/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import VersoUtil.BinFiles
meta import VersoUtil.BinFiles

open Verso.BinFiles

set_option linter.missingDocs true

namespace Verso.Output.Html

/--
The minified KaTeX CSS file's contents. The stylesheet loads the fonts in {name}`katexFonts` by relative paths.
-/
public def katex.css : String :=
  include_str "../../../../../vendored-js/katex/katex.min.css"

/--
The minified KaTeX JS file's contents.
-/
public def katex.js : String :=
  include_str "../../../../../vendored-js/katex/katex.min.js"

/--
The KaTeX font files. Keys are filenames of the form `fonts/...`, relative to the KaTeX stylesheet.
-/
public def katexFonts : Array (String × ByteArray):=
  (include_bin_dir "../../../../../vendored-js/katex/fonts").map fun (name, contents) =>
    (name.dropPrefix "../../../../../vendored-js/katex/" |>.copy, contents)

/--
A short script that renders all Verso math using KaTeX.
-/
public def math.js := include_str "../../../../../static-web/math.js"

/--
Writes KaTeX's script, stylesheet, and fonts, along with {name}`math.js`, to {name}`dir`.

The files are {lit}`katex.css`, {lit}`katex.js`, and {lit}`math.js`. The fonts are in the
{lit}`fonts` subdirectory, where the stylesheet expects them.
-/
public def writeKaTeX (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "katex.css") katex.css
  IO.FS.writeFile (dir / "katex.js") katex.js
  IO.FS.writeFile (dir / "math.js") math.js
  for (name, contents) in katexFonts do
    let path := dir / name
    path.parent.forM IO.FS.createDirAll
    IO.FS.writeBinFile path contents
