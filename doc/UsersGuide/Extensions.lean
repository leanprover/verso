/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.DocString.Syntax
import VersoManual

open Verso Genre Manual
open InlineLean

#doc (Manual) "Extensions" =>
%%%
tag := "extensions"
htmlSplit := .never
%%%

Verso's markup language features four extension points:
 * {tech}[Roles]
 * {tech}[Directives]
 * {tech}[Code blocks]
 * {tech}[Commands]

These can be used to extend Verso to support new documentation features.

# Syntax
%%%
tag := "extension-syntax"
%%%

All four extension points share a common syntax.
They are invoked by name, with a sequence of arguments.
These arguments may be positional or by name, and their values may be identifiers, string literals, or numbers.
Boolean flags may be passed by preceding their name with `-` or `+` for {lean}`false` or

 {lean}`true`, respectively.

:::paragraph
In this example, the directive `syntax` is invoked with the positional argument `term` and the named argument `title` set to `"Example"`.
The flag `check` is set to `false`.
It contains a descriptive paragraph and the code block `grammar`, which is invoked with no arguments:
````
:::syntax term (title := example) -check
This is an example grammar:
```grammar
term ::= term "<+-+>" term
```
:::
````
:::

:::paragraph
More formally, an invocation of an extension should match this grammar:
```
CALL := IDENT ARG*
ARG := VAL | "(" IDENT ":=" VAL ")" | "+" IDENT | "-" IDENT
VAL := IDENT | STRING | NUM
```
A `CALL` may occur after an opening fence on a code block.
It is mandatory after the opening colons of a directive, in the opening curly braces of a role, or in a command.
:::

# Elaborating Extensions
%%%
tag := "elab-extensions"
%%%

Each kind of extension has a table that maps names to expanders.
An {deftech}_expander_ converts Verso's syntax to Lean terms.
When the elaborator encounters a code block, role, directive, or command invocation, it resolves the name and looks up an expander in the table.
Expanders are attempted until one of them either throws an error or succeeds.
Expanders use the monad {name Verso.Doc.Elab.DocElabM}`DocElabM`, which is an extension of Lean's term elaboration monad {name Lean.Elab.Term.TermElabM}`TermElabM` with document-specific features.
Expanders first {ref "ArgParse"}[parse] their arguments into a suitable configuration type, typically via a {name Verso.ArgParse.FromArgs}`FromArgs` instance, after which they return Lean syntax.

There are two ways to associate an expander with a name: the `@[code_block]`, `@[role]`, `@[directive]`, and `@[block_command]` attributes (preferred) or the `@[code_block_expander]`, `@[role_expander]`, and `@[directive_expander]` attributes.
Using the former attributes results in an expander that invokes the argument parser automatically, and they enable Verso to automatically compute usage information from a {name Verso.ArgParse.FromArgs}`FromArgs` instance.
The latter are lower-level, and require manual parsing of arguments.

## Parsing Arguments
%%%
tag := "ArgParse"
%%%

This grammar is fairly restrictive, so each extension is responsible for parsing their arguments in order to afford sufficient flexibility.
Arguments are parsed via instances of {name Verso.ArgParse.FromArgs}`FromArgs`:

{docstring Verso.ArgParse.FromArgs}

Implementations of {name Verso.ArgParse.FromArgs.fromArgs}`FromArgs.fromArgs` specify parsers written using {name Verso.ArgParse}`ArgParse`:

{docstring Verso.ArgParse}

Individual argument values are matched using {name Verso.ArgParse.ValDesc}`ValDesc`:

{docstring Verso.ArgParse.ValDesc}

A canonical value description for a Lean type can be registered via an instance of {name Verso.ArgParse.FromArgVal}`FromArgVal`:

{docstring Verso.ArgParse.FromArgVal}


In addition to the constructors of {name Verso.ArgParse}`ArgParse`, the {name}`Applicative` and {name}`Functor` instances are important, as well as the following helpers:

{docstring Verso.ArgParse.namedD}

{docstring Verso.ArgParse.positional'}

{docstring Verso.ArgParse.named'}

{docstring Verso.ArgParse.namedD'}
