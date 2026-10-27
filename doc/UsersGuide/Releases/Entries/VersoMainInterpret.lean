/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Nawrocki
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 36, 0⟩
  breaking := false
  tag := "verso-main-interpret"
  prs := [1054]

#doc (Manual) "Building Documents in the Interpreter" =>

Verso now provides a Lake script `versoMain` that runs the `main` function of a Lean file.
This can be used to build Verso documents in the Lean interpreter instead of compiling them to native executables.
Use `lake run versoMain MyDoc.lean ARGS...` to build your document, instead of adding a `lake_exe my_doc` to the Lakefile and running `lake exe my_doc`.
This avoids linking the native executable, which can be slow for projects with large dependencies such as mathlib.
Speedups around 10%-30% are observed for rebuilding documents after an edit, depending on the degree of native compilation overhead.

In Verso, the `usersguide`, `demosite`, `demotextbook`, `packagedocs`, `simplepage`, and `tutorial-example` executables have been removed; use `lake run versoMain` with the corresponding `*Main.lean` file instead.
