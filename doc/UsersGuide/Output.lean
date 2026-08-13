/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.DocString.Syntax
import VersoManual
import VersoBlog
import UsersGuide.Output.HTML

open Verso Genre Manual

open Verso.Genre.Blog (Page Post)

open InlineLean
open Verso.Doc

open Verso.Output

#doc (Manual) "Output Formats" =>
%%%
tag := "outputs"
htmlSplit := .never
%%%

Verso provides genre authors with tools for generating HTML and TeX code via embedded languages that reduce the syntactic overhead of constructing ASTs.
These libraries may also be used by authors of extensions to the {name}`Manual` genre, who need to define how each new element should be rendered to each supported backend.

{include 0 UsersGuide.Output.HTML}

# TeX
%%%
tag := "output-tex"
%%%


Verso's {name}`TeX` type represents LaTeX documents.
They are typically produced using an embedded DSL that is available when the namespace `Verso.Output.TeX` is opened.

{docstring TeX}

{docstring TeX.empty}

{docstring TeX.asString}

TeX documents are written in `\TeX{...}`, in a syntax very much like LaTeX itself.
The differences are:
 * `\Lean{...}` escapes back to Lean, expecting a value of type {name}`TeX`.
 * Text content is written as Lean string literals to facilitate precise control over whitespace.
 * Interpolated Lean strings (with `s!`) may be used in any context that expects a string.

For example, this definition creates a bulleted list list:
```lean -keep (name := texlist)
open Verso.Output.TeX

def mkList (xs : List TeX) : TeX :=
  \TeX{
    \begin{itemize}
      \Lean{xs.map (\TeX{\item " " \Lean{·} "\n"})}
    \end{itemize}
  }

#eval mkList ["A", \TeX{\emph{"B"}}, "C"]
  |>.asString
  |> IO.println
```

```leanOutput texlist
\begin{itemize}
\item A
\item \emph{B}
\item C

\end{itemize}
```
