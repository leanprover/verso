/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso
import VersoManual

namespace Verso.Integration.FrontMatter

open Verso Genre Manual

#docs (Manual) doc "Front Matter Test Document" :=
:::::::

%%%
shortTitle := "FrontMatter"
authors := ["Test Author"]
%%%

This is the introduction text that appears before any chapters.
It should be part of the front matter.

# Preface
%%%
tag := "preface"
number := false
%%%

This is an unnumbered preface section.
It should appear in the front matter, before `\mainmatter`.

# Chapter One
%%%
tag := "ch1"
%%%

This is the first numbered chapter.
It should appear after `\mainmatter`.

# Chapter Two
%%%
tag := "ch2"
%%%

This is the second numbered chapter.
It should also appear after `\mainmatter`.

# Acknowledgments
%%%
tag := "ack"
number := false
%%%

This is an unnumbered acknowledgments section at the end.
It should appear in the back matter, after `\backmatter`.

# Index
%%%
tag := "index"
number := false
%%%

This is an unnumbered index section.
It should also appear in the back matter.

:::::::

end Verso.Integration.FrontMatter
