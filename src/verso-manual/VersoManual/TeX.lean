/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

namespace Verso.Genre.Manual.TeX

def preamble (title : String) (authors : List String) (date : String) : String :=
r##"
\documentclass{memoir}

\usepackage{sourcecodepro}
\usepackage{sourcesanspro}
\usepackage{sourceserifpro}

\usepackage{fancyvrb}
\usepackage{fvextra}

\makechapterstyle{lean}{%
\renewcommand*{\chaptitlefont}{\sffamily\HUGE}
\renewcommand*{\chapnumfont}{\chaptitlefont}
% allow for 99 chapters!
\settowidth{\chapindent}{\chapnumfont 999}
\renewcommand*{\printchaptername}{}
\renewcommand*{\chapternamenum}{}
\renewcommand*{\chapnumfont}{\chaptitlefont}
\renewcommand*{\printchapternum}{%
\noindent\llap{\makebox[\chapindent][l]{%
\chapnumfont \thechapter}}}
\renewcommand*{\afterchapternum}{}
}

\chapterstyle{lean}

\setsecheadstyle{\sffamily\bfseries\Large}
\setsubsecheadstyle{\sffamily\bfseries\large}
\setsubsubsecheadstyle{\sffamily\bfseries}

\renewcommand{\cftchapterfont}{\normalfont\sffamily}
\renewcommand{\cftsectionfont}{\normalfont\sffamily}
\renewcommand{\cftchapterpagefont}{\normalfont\sffamily}
\renewcommand{\cftsectionpagefont}{\normalfont\sffamily}

\title{\sffamily "## ++ title ++ r##"}
\author{\sffamily "## ++ String.join (authors.intersperse r##" \and "##) ++ r##"}
\date{\sffamily "## ++ date ++ r##"}

\begin{document}

\frontmatter

\begin{titlingpage}
\maketitle
\end{titlingpage}

\tableofcontents

\mainmatter
"##

def postamble : String := "\\end{document}"
