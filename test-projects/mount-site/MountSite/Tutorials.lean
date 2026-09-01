/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoBlog
open Verso Genre Blog
open scoped Lean.Doc.Syntax

#doc (Page) "Tutorials" =>

One directory of rendered HTML content per version of the tutorials is mounted beneath this page,
from an assembly function that discovers the directories and runs in `IO` before `main`.
