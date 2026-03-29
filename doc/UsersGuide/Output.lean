/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Lean.DocString.Syntax
public import VersoManual
import VersoBlog

open Verso Genre Manual DB

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

# HTML
%%%
tag := "output-html"
%%%

Verso's {name}`Html` type represents HTML documents.
They are typically produced using an embedded DSL that is available when the namespace `Verso.Output.Html` is opened.

{dbDocstring Html}

{dbDocstring Html.empty}

{dbDocstring Html.fromArray}

{dbDocstring Html.fromList}

{dbDocstring Html.append}

{dbDocstring Html.visitM}

{dbDocstring Html.format}

{dbDocstring Html.asString}

HTML documents are written in double curly braces, in a syntax very much like HTML itself.
The differences are:
 * Double curly braces escape back to Lean. This can be done for HTML elements, attribute values, or whole sets of attributes.
 * Text content is written as Lean string literals to facilitate precise control over whitespace.
 * Interpolated Lean strings (with `s!`) may be used in any context that expects a string.

For example, this definition creates a `<ul>` list:
```lean -keep (name := htmllist)
open Verso.Output.Html

def mkList (xs : List Html) : Html :=
  {{ <ul> {{ xs.map ({{<li>{{·}}</li>}}) }} </ul>}}

#eval mkList ["A", {{<emph>"B"</emph>}}, "C"]
  |>.asString
  |> IO.println
```

```leanOutput htmllist
<ul>
  <li>
    A</li>
  <li>
    <emph>B</emph></li>
  <li>
    C</li>
  </ul>
```

# TeX
%%%
tag := "output-tex"
%%%


Verso's {name}`TeX` type represents LaTeX documents.
They are typically produced using an embedded DSL that is available when the namespace `Verso.Output.TeX` is opened.

{dbDocstring TeX}

{dbDocstring TeX.empty}

{dbDocstring TeX.asString}

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
