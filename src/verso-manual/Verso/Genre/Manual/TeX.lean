/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

namespace Verso.Genre.Manual.TeX

def preamble (title : String) (authors : List String) (date : String) : String :=
"
\\documentclass{book}

\\title{" ++ title ++ "}
\\author{" ++ String.join (authors.intersperse " \\and ") ++ "}
\\date{" ++ date ++ "}

\\begin{document}

\\frontmatter

\\maketitle

\\tableofcontents

\\mainmatter
"

def postamble : String := "\\end{document}"
