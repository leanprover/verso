/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

namespace Verso.Genre.Manual.TeX

def preamble (title : String) (authors : List String) (date : String) (packages : List String) (extraPreamble : List String) : String :=
r##"
\documentclass{memoir}

\usepackage{sourcecodepro}
\usepackage{sourcesanspro}
\usepackage{sourceserifpro}

\usepackage{fancyvrb}
\usepackage{fvextra}

\usepackage[most]{tcolorbox}

\definecolor{bordercolor}{HTML}{98B2C0}
\definecolor{medgray}{HTML}{555555}
\newtcolorbox{docstringBox}[2][]{colback=white,
breakable,
colframe=bordercolor,
colbacktitle=white,
enhanced,
coltitle=medgray,
attach boxed title to top left={xshift=2mm,yshift=-2mm},
boxrule=0.4pt,
fonttitle=\sffamily\fontsize{6pt}{7pt}\selectfont,
boxed title style={top=-0.3mm,bottom=-0.3mm,left=-0.3mm,right=-0.3mm,boxrule=0.4pt},
title={#2},#1}

"## ++
"\n".intercalate packages ++
r##"
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
"## ++
"\n".intercalate extraPreamble ++
r##"
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
