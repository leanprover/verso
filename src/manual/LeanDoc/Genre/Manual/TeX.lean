namespace LeanDoc.Genre.Manual.TeX

def preamble (title : String) (authors : List String) : String :=
"
\\documentclass{book}

\\title{" ++ title ++ "}
\\author{" ++ String.join (authors.intersperse ",") ++ "}

\\begin{document}

\\maketitle

\\tableofcontents
"

def postamble : String := "\\end{document}"
