/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import VersoManual

import UsersGuide.Releases.«v4_28_0»

open Verso Genre Manual

#doc (Manual) "Release Notes" =>
%%%
tag := "release-notes"
file := "releases"
number := false
htmlSplit := .never
%%%

This section provides release notes about recent versions of Verso. When updating to a new version, please
read the corresponding release notes. They may contain advice that will help you understand
the differences with the previous version and upgrade your projects.

Note that Verso versioning follows Lean's, that is to say, we release a new version of version each time Lean releases, usually once per month. In particular, note that Verso doesn't follow the [semantic versioning model](https://semver.org/).

{include 0 UsersGuide.Releases.«v4_28_0»}
