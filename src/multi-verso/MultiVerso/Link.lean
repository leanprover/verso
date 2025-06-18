/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json
import MultiVerso.Path
import MultiVerso.Slug

open Lean
namespace Verso.Multi

/-- A link to a given piece of content -/
structure Link where
  path : Path
  htmlId : Slug
deriving ToJson, FromJson, BEq, Ord, Repr

/-- Constructs a link URL suitable for an `<a>` tag. -/
def Link.link (link : Link) : String :=
  link.path.link (htmlId := some link.htmlId.toString)
