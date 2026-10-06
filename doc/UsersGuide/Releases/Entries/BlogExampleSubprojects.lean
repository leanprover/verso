/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases
open Verso.Code.External

release_note
  version := ⟨4, 35, 0⟩
  breaking := true
  tag := "blog-example-subprojects"
  prs := [1015]

#doc (Manual) "Blog Example Subprojects Removed" =>

The blog genre's `leanExampleProject` and `leanCommand` commands and its `leanTerm` role were removed along with SubVerso's `%example` commands.
These features were not generally used, and the anchors feature in SubVerso supports their use cases better and is already widely used in the {name}`Manual` genre.

When using the anchore feature, code from a separate Lean project should be written in ordinary Lean modules.
This subproject should still require SubVerso, which Verso uses to extract the highlighted code.
Use comments of the form `-- ANCHOR: NAME` and `-- ANCHOR_END: NAME` to mark named regions of a module.
There's no requirement that anchors be well-nested or that the follow the syntax tree.

:::paragraph
To migrate a post:

* In the example code, replace each `%example name` and `%end` pair with `-- ANCHOR: name` and `-- ANCHOR_END: name`, and remove the `SubVerso.Examples` import.
* In the post, `open Verso.Code.External` and set the options {option}`verso.exampleProject` to the project's directory and {option}`verso.exampleModule` to the module's name.
  The named argument `module` selects a different module of the same project.
* Use the {name}`anchor` code block in place of `leanCommand`.
  The code block should contain the code that it's referring to.
  If there's a mismatch, Verso will offer to update it.
* Use the {name}`anchorTerm` and {name}`anchorName` roles in place of `leanTerm`.
  They refer to a named anchor in the file, while the code with the role selects a particular term or name found in the file.
* Use the {name}`anchorInfo`, `anchorWarning`, and `anchorError` code blocks to show an anchor's messages.
:::

A name shown with `%show_name` should be migrated to an anchor around an `example` or `#check` that mentions the name.
In the post, it can be quoted with {name}`anchorName`.
A sub-term example such as `%ex{name}{term}` should be migrated to an anchor around the code, referred to via {name}`anchorTerm`.
To migrate `%signature`, wrap an anchor around a command that restates the declaration's signature, such as Mathlib's `recall`.
