/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json
import MultiVerso.Path
import MultiVerso.Slug

open Lean

set_option linter.missingDocs true

namespace Verso.Multi

/-- A link to a given piece of content -/
structure Link where
  /--
  The part of the link to be prepended to the path, if present. Only used on links to other sites.
  -/
  root : Option String := none
  /--
  The path from the site root to the current page.
  -/
  path : Path
  /-- The HTML ID on the current page-/
  htmlId : Slug
deriving ToJson, FromJson, BEq, Ord, Repr

/-- Constructs a link URL suitable for an `<a>` tag. -/
def Link.link (link : Link) : String :=
  let addr := link.path.link (htmlId := some link.htmlId.toString)
  if let some root := link.root then
    root.stripSuffix "/" ++ addr
  else addr
