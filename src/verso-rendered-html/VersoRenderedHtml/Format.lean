/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Lean.Data.Json
public import Std.Data.TreeMap
public import MultiVerso.Path
public import MultiVerso.Slug

public section

set_option linter.missingDocs true

open Lean (Json ToJson FromJson toJson fromJson?)
open Std (TreeMap)

namespace Verso

namespace RenderedHtml

/--
The version of the rendered HTML content format that this version of Verso produces, and the newest
version that it can read.
-/
def formatVersion : Nat := 1

/--
The value of a manifest's `format` field.
-/
def formatName : String := "verso-rendered-html"

/--
The name of the manifest file within a rendered HTML content directory.
-/
def manifestFileName : String := "verso-rendered-html.json"

/--
The name of the directory of files that a consumer serves verbatim, relative to a rendered HTML
content directory.
-/
def staticDirName : String := "static"

/--
The name of the directory of HTML fragments, relative to a rendered HTML content directory.
-/
def fragmentsDirName : String := "fragments"

/--
Compares two page paths, ordering them lexicographically by segment.

A page therefore sorts directly before the pages beneath it, whatever characters the segments of
neighboring paths begin with.
-/
def comparePaths (p q : Multi.Path) : Ordering :=
  go p.toList q.toList
where
  go : List String → List String → Ordering
    | [], [] => .eq
    | [], _ :: _ => .lt
    | _ :: _, [] => .gt
    | x :: xs, y :: ys => (compare x y).then (go xs ys)

/--
Writes a page path as a manifest writes it: its segments joined with `/`, with no leading or trailing
slash, and the root page as the empty string.

A page keyed `a/b` is served at `a/b/`, and `Verso.Multi.Path.relativeLink` produces a link to it.
-/
def pathToString (path : Multi.Path) : String :=
  "/".intercalate path.toList

/--
Reads a page path written as its segments joined with `/`. The empty string is the root page.

Each segment must be a nonempty slug, so no segment can be `.` or `..`.
-/
def pathOfString (str : String) : Except String Multi.Path := do
  if str.isEmpty then return #[]
  let mut out : Multi.Path := #[]
  for seg in str.splitOn "/" do
    if seg.isEmpty then
      throw s!"Page path '{str}' has an empty segment"
    if (Multi.Slug.isSlug? seg).isNone then
      throw s!"Segment '{seg}' of page path '{str}' is not a slug"
    out := out.push seg
  return out

end RenderedHtml

namespace RenderedHtmlContent

/--
Identifies the tool that produced a rendered HTML content directory.
-/
structure Generator where
  /-- The name of the generator. -/
  tool : String
  /-- The version of the generator. -/
  version : String
  /-- The Lean toolchain that the generator ran under. -/
  toolchain : String
deriving Repr, BEq, Inhabited, ToJson, FromJson

/--
What a stylesheet is for, which determines where a consumer places it.

A consumer that does not recognize a role places the stylesheet as content.
-/
inductive StylesheetRole where
  /--
  The stylesheet defines `--verso-*` custom properties on `:root`.

  A consumer places every such stylesheet ahead of every other stylesheet in the document, including
  the consumer's own definitions of the same properties. Both sides declare on `:root`, so source
  order decides: a property that the consumer defines takes the consumer's value, and a property
  that the consumer does not define keeps the value that shipped with the content.
  -/
  | variables
  /-- The stylesheet styles the content's markup and reads the custom properties. -/
  | content
  /-- A role that this version of Verso does not define. It is placed as content. -/
  | other (name : String)
deriving Repr, BEq, DecidableEq

instance : Inhabited StylesheetRole := ⟨.content⟩

/--
Whether a consumer places a stylesheet with this role ahead of its own custom property definitions.

A role that this version of Verso does not define is placed as content.
-/
def StylesheetRole.placesAsVariables : StylesheetRole → Bool
  | .variables => true
  | .content | .other _ => false

instance : ToJson StylesheetRole where
  toJson
    | .variables => .str "variables"
    | .content => .str "content"
    | .other n => .str n

instance : FromJson StylesheetRole where
  fromJson? v := do
    match (← v.getStr?) with
    | "variables" => pure .variables
    | "content" => pure .content
    | other => pure (.other other)

/--
The library that a file is a copy of.

A directory ships the libraries its pages need, so a consumer that places several directories at
once holds several copies of one library, under names that need not match. This says which library a
file is, so that a consumer that wants to place one copy can tell them apart.
-/
structure Library where
  /-- The library's name, as its publisher spells it. -/
  name : String
  /-- The library's version. -/
  version : String
deriving Repr, BEq, Inhabited, ToJson, FromJson

/--
A stylesheet that the pages of a rendered HTML content directory need.

The path is relative to the content directory and lies within the static directory, so a consumer
that has copied the static directory to its mount point serves the stylesheet at the mount point
followed by `RenderedHtmlContent.Stylesheet.mountPath`.
-/
structure Stylesheet where
  /-- The stylesheet's path within the content directory. -/
  path : String
  /-- What the stylesheet is for. -/
  role : StylesheetRole
  /-- The library that the stylesheet is a copy of, when it is one. -/
  provides : Option Library := none
deriving Repr, BEq, Inhabited, ToJson, FromJson

/--
A script that the pages of a rendered HTML content directory need.

The path is relative to the content directory and lies within the static directory, so a consumer
that has copied the static directory to its mount point serves the script at the mount point
followed by `RenderedHtmlContent.Script.mountPath`.
-/
structure Script where
  /-- The script's path within the content directory. -/
  path : String
  /-- Whether the reference to the script carries `defer`. -/
  defer : Bool := false
  /-- The library that the script is a copy of, when it is one. -/
  provides : Option Library := none
deriving Repr, BEq, Inhabited, ToJson, FromJson

/--
One HTML fragment of a page.

The fragment's file holds markup rooted at a `<div>` that carries no `<html>`, `<head>`, `<base>`,
`<body>`, or page chrome. A consumer places it in the document body verbatim, after replacing the
root token with a prefix such that the token followed by `/x` resolves to `x` under the mount point.
-/
structure Fragment where
  /-- The fragment's file, relative to the content directory. -/
  file : String
  /-- The token that stands for the root of the mounted content in the fragment's text. -/
  rootToken : String
deriving Repr, BEq, Inhabited, ToJson, FromJson

/--
One page of a rendered HTML content directory.

A page's fragments are separate files, and a consuming template places the ones it knows by name, so
neither side parses HTML. A fragment that the template does not reference is not rendered.
-/
structure Page where
  /-- The page's title as plain text, for `<title>` and anywhere markup cannot go. -/
  title : String
  /--
  The page's title as inline HTML.

  It holds `em`, `strong`, `code`, `sub`, `sup`, `span`, `br`, and text, and contains no URLs, so a
  consumer places it inside a heading, a list item, or a link without rewriting it. A title that
  carries no markup produces the escaped plain text, so a consumer may always use this field.
  -/
  titleHtml : String
  /-- The page's fragments, keyed by fragment name. -/
  fragments : TreeMap Multi.Slug Fragment
deriving Inhabited

/--
The path at which a consumer serves a stylesheet, relative to the mount point.
-/
def Stylesheet.mountPath (css : Stylesheet) : String :=
  match css.path.dropPrefix? (RenderedHtml.staticDirName ++ "/") with
  | some rest => rest.copy
  | none => css.path

/--
The path at which a consumer serves a script, relative to the mount point.
-/
def Script.mountPath (js : Script) : String :=
  match js.path.dropPrefix? (RenderedHtml.staticDirName ++ "/") with
  | some rest => rest.copy
  | none => js.path

instance : ToJson Page where
  toJson p :=
    Json.mkObj [
      ("title", .str p.title),
      ("titleHtml", .str p.titleHtml),
      ("fragments",
        Json.mkObj <| p.fragments.toList.map fun (name, frag) => (name.toString, toJson frag))
    ]

instance : FromJson Page where
  fromJson? v := do
    let title ← v.getObjValAs? String "title"
    let titleHtml ← v.getObjValAs? String "titleHtml"
    let fragmentsJson ← v.getObjVal? "fragments"
    let entries : Array (String × Json) := (← fragmentsJson.getObj?).toArray
    let mut fragments : TreeMap Multi.Slug Fragment := {}
    for (name, fragJson) in entries do
      let some name' := Multi.Slug.isSlug? name
        | throw s!"Fragment name '{name}' is not a slug"
      if name'.toString.isEmpty then
        throw "Fragment names may not be empty"
      fragments := fragments.insert name' (← fromJson? fragJson)
    return { title, titleHtml, fragments }

end RenderedHtmlContent

/--
A directory of rendered HTML content: page bodies, head requirements, and assets, with no page
chrome.

A consumer copies the static directory to its mount point, so `static/foo/bar.xyz` is served at the
mount point followed by `foo/bar.xyz`, and renders one page per entry in the page map. It needs no
knowledge of the genre that produced the content.

Within a format version the manifest only gains fields, and the format version is raised only for a
change that cannot be expressed as an addition. A consumer reads every format version up to and
including its own, ignores unknown fields, and accepts an unrecognized value of an enumerated field.
-/
structure RenderedHtmlContent where
  /-- Identifies the format. It is always `Verso.RenderedHtml.formatName`. -/
  format : String := RenderedHtml.formatName
  /-- The version of the format that this directory is written in. -/
  formatVersion : Nat := RenderedHtml.formatVersion
  /-- The tool that produced the directory. -/
  generator : RenderedHtmlContent.Generator
  /-- The title of the whole, for index pages and breadcrumbs, as plain text. -/
  title : String
  /-- The title of the whole as inline HTML, holding the elements that a page's title holds. -/
  titleHtml : String
  /-- The stylesheets that the pages need, in the order in which they are to be placed. -/
  stylesheets : Array RenderedHtmlContent.Stylesheet := #[]
  /-- The scripts that the pages need, in the order in which they are to be placed. -/
  scripts : Array RenderedHtmlContent.Script := #[]
  /--
  The pages, keyed by path.

  Page paths are dense: every proper prefix of a page path is itself a page path, so a directory
  always has an index and the root page is always present.
  -/
  pages : TreeMap Multi.Path RenderedHtmlContent.Page RenderedHtml.comparePaths := {}
deriving Inhabited

instance : ToJson RenderedHtmlContent where
  toJson c :=
    Json.mkObj [
      ("format", .str c.format),
      ("formatVersion", toJson c.formatVersion),
      ("generator", toJson c.generator),
      ("title", .str c.title),
      ("titleHtml", .str c.titleHtml),
      ("stylesheets", toJson c.stylesheets),
      ("scripts", toJson c.scripts),
      ("pages",
        Json.mkObj <| c.pages.toList.map fun (path, page) =>
          (RenderedHtml.pathToString path, toJson page))
    ]

/--
Reads a field that a manifest may leave out, falling back to `fallback` when it is absent.

Every field of `RenderedHtmlContent` that carries a default is read this way, so that a manifest
written before the field existed still reads. A field that is present but of the wrong type is still
an error.
-/
def optionalField [FromJson α] (v : Json) (key : String) (fallback : α) :
    Except String α :=
  match v.getObjVal? key with
  | .error _ => .ok fallback
  | .ok field => fromJson? field

instance : FromJson RenderedHtmlContent where
  fromJson? v := do
    let format ← v.getObjValAs? String "format"
    let formatVersion ← v.getObjValAs? Nat "formatVersion"
    let generator ← v.getObjValAs? RenderedHtmlContent.Generator "generator"
    let title ← v.getObjValAs? String "title"
    let titleHtml ← v.getObjValAs? String "titleHtml"
    let stylesheets ← optionalField v "stylesheets" (#[] : Array RenderedHtmlContent.Stylesheet)
    let scripts ← optionalField v "scripts" (#[] : Array RenderedHtmlContent.Script)
    let pagesJson := (v.getObjVal? "pages").toOption.getD (Json.mkObj [])
    let entries : Array (String × Json) := (← pagesJson.getObj?).toArray
    let mut pages :
        TreeMap Multi.Path RenderedHtmlContent.Page RenderedHtml.comparePaths := {}
    for (path, pageJson) in entries do
      pages := pages.insert (← RenderedHtml.pathOfString path) (← fromJson? pageJson)
    return {
      format, formatVersion, generator, title, titleHtml,
      stylesheets, scripts, pages
    }

instance : Repr RenderedHtmlContent where
  reprPrec c := Repr.addAppParen <| Std.Format.text ("rendered_html_content% " ++ (toJson c).compress)
