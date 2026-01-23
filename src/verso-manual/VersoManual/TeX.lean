/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
namespace Verso.Genre.Manual.TeX

public def preamble (title : String) (authors : List String) (date : String) (packages : List String) (extraPreamble : List String) : String :=
r##"
\documentclass{memoir}

\usepackage{sourcecodepro}
\usepackage{sourcesanspro}
\usepackage{sourceserifpro}

\usepackage{fancyvrb}
\usepackage{fvextra}
\usepackage{xparse}

\usepackage[most]{tcolorbox}

% Detect whether we're in a footnote. This is used later to avoid \href rendering bugs.
\newif\ifinfootnote
\infootnotefalse

\let\oldfootnote\footnote
\renewcommand{\footnote}[1]{%
  \oldfootnote{\infootnotetrue#1\infootnotefalse}%
}

\let\oldfootnotetext\footnotetext
\renewcommand{\footnotetext}[1]{%
  \oldfootnotetext{\infootnotetrue#1\infootnotefalse}%
}

\usepackage[breaklinks=true, hyperfootnotes=false]{hyperref}

% Redefines \href to show footnotes with URLs instead. This works around a page breaking bug in
% hyperref and also makes the link useful on paper. If already in a footnote, the URL is
% in parentheses instead.
\let\oldhref\href
\RenewDocumentCommand{\href}{mm}{%
  \ifinfootnote%
    #2~(\url{#1})%
  \else%
    #2\footnote{\url{#1}}%
  \fi%
}

\usepackage[normalem]{ulem}
\newcommand{\coloredwave}[2]{\textcolor{#1}{\uwave{\textcolor{black}{#2}}}}
\usepackage{newunicodechar}

% Work around the fact that
% U+271D LATIN CROSS doesn't exist in
% DejaVu Sans Mono Oblique. \textup
% is fontspec for "upright, not italic/oblique".
\newunicodechar{✝}{\textup{✝}}
% Work around missing U+2011 (non-breaking hyphen) in Source Serif Pro
\newunicodechar{‑}{-}

\definecolor{errorColor}{HTML}{ff0000}
\definecolor{infoColor}{HTML}{007f00}
\definecolor{warningColor}{HTML}{0000ff}
\newcommand{\errorDecorate}[1]{\coloredwave{errorColor}{#1}}
\newcommand{\infoDecorate}[1]{\coloredwave{infoColor}{#1}}
\newcommand{\warningDecorate}[1]{\coloredwave{warningColor}{#1}}
\DefineVerbatimEnvironment{LeanVerbatim}{Verbatim}
  {commandchars=\\\{\},fontsize=\small,breaklines=true}
\DefineVerbatimEnvironment{FileVerbatim}{Verbatim}{commandchars=\\\{\},fontsize=\small,breaklines=true,frame=single,framesep=2mm,numbers=left}
\CustomVerbatimCommand{\LeanVerb}{Verb}
  {commandchars=\\\{\},fontsize=\small}
\CustomVerbatimCommand{\FileListingVerb}{Verb}
  {commandchars=\\\{\},fontsize=\small,frame=single,framesep=2mm, numbers=left}

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
\setmonofont{DejaVu Sans Mono}
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

public def postamble : String := "\\end{document}"
