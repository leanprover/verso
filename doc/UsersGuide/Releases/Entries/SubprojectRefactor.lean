/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 36, 0⟩
  breaking := false
  tag := "subproject-call"
  prs := [1030]

#doc (Manual) "Standardized Elan Invocation" =>

There are more than a half-dozen places where Verso tools need
to invoke `elan run --install <toolchain> <...cmd>` in the context of a specific project, where the `cmd` is some relevant command (usually a lake invocation).

Standardizing the way environment variables are prepared in this event should make this more robust going forward, but users that relied on specific unexpected configurations of environment variables may encounter issues.
