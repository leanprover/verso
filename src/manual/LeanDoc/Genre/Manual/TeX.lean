namespace LeanDoc.Genre.Manual.TeX

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
