/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Lean.Data.Json
public import MultiVerso.Path
public import MultiVerso.Slug

open Lean

set_option linter.missingDocs true

namespace Verso.Multi

/-- A link to a given piece of content -/
public structure Link where
  /--
  The path from the site root to the current page.
  -/
  path : Path
  /-- The HTML ID on the current page-/
  htmlId : Slug
deriving ToJson, FromJson, BEq, Ord, Repr, Inhabited

/-- Constructs a link URL suitable for an `<a>` tag. -/
public def Link.link (link : Link) : String :=
  link.path.link (htmlId := some link.htmlId.toString)

/--
Constructs a link URL suitable for an `<a>` tag.
Ensures that it is rendered as a relative link.
In situations where we can guarantee a <base> tag,
this is an appropriate choice.
-/
public def Link.relativeLink (link : Link) : String :=
  link.path.relativeLink (htmlId := some link.htmlId.toString)

/-- A link to a piece of content on another site -/
public structure RemoteLink extends Link where
  /--
  The part of the link to be prepended to the path, if present. Only used on links to other sites.
  -/
  root : String
deriving ToJson, FromJson, BEq, Ord, Repr

@[inherit_doc Link.link]
public def RemoteLink.link (link : RemoteLink) : String :=
  (link.root.dropSuffix "/").copy ++ link.toLink.link
