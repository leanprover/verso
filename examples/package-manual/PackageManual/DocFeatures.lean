/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean



set_option pp.rawOnError true



#doc (Manual) "Documentation Features" =>
%%%
htmlSplit := .never
%%%

The code example utilities used to document external projects have a systematic set of names, whether used as code blocks or roles.
All documentation tools draw their code from an example project:

{optionDocs verso.exampleProject}

The example project must depend on the same version of `subverso` that the document's Verso version uses.

Within the example project, examples are drawn from a module.
Sometimes, the entire module is the example, while other cases use just some part of the module.
To set a default module, use the option {option}`verso.exampleModule`.
When there is no default set, or to override it, the example code features all accept a keyword argument `module`.{index (subterm:="keyword argument")}[`module`]

{optionDocs verso.exampleModule}

# Example Modules

To include a module, use the `module`{index}[`module`] code block:
````
```module (module := M)
...
```
````
The contents of the code block specifies the expected code.
This ensures that documentation doesn't get out of sync with examples and makes it easier to read the documentation source code.
While it's an error if they don't match, a code action can fix the problem.

:::paragraph
To show output from the module, use the `moduleInfo`{index}[`moduleInfo`], `moduleWarning`{index}[`moduleWarning`], or `moduleError`{index}[`moduleError`] code blocks:
````
```moduleInfo (module := M)
...
```
````
The code block serves two purposes: it selects one of the messages with the appropriate severity, and it ensures that the documentation stays in sync with the code.
However, metavariable renumbering does not affect whether the message is considered to match.
:::

For inline contexts, the `moduleName`{index}[`moduleName`] and `moduleTerm`{index}[`moduleTerm`] roles expect a single code element as their parameter and respectively select the first name or token sequence in the indicated module that matches it.
For example, `` {moduleName}`x` `` indicates the first occurrence of `x` in the module, and `` {moduleTerm}`3 + y` `` indicates the first term that matches `3 + y`.
These are included with information such as bindings intact, so correct highlighting depends on using more specific {tech}[anchors] to indicate the appropriate region of the file.


# Anchors

:::paragraph
An {deftech}_anchor_ is a named region of a module.
Anchors can be included by name, rather than by line number.
An anchor is delimited by special comments:
```
-- ANCHOR: anAnchor
def f : Nat → Nat := id
#eval f 2
-- ANCHOR_END: anAnchor
```
The comments themselves are removed, and there is no requirement that anchors be well-nested.
:::

:::paragraph
Anchors can be specified using the `(anchor := anAnchor)`{index (subterm:="keyword agument")}[`anchor`] parameter to each module form.
Additionally, there are macro versions that take anchor names positionally, so for example
````
```anchor anAnchor
...
```
````
is equivalent to
````
```module (anchor := anAnchor)
...
```
````
and `` {anchorName anAnchor}`x` `` is equivalent to `` {moduleName (anchor := anAnchor)}`x` ``.
:::

# Live Link

```lean +liveLink
def foo := 1 + 2
```
