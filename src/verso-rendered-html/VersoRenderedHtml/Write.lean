/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import VersoRenderedHtml.Read

public section

set_option linter.missingDocs true

open Lean (toJson)
open Std (TreeMap)

namespace Verso.RenderedHtml

/--
A file that a consumer serves verbatim.
-/
inductive StaticFile where
  /-- A text file. -/
  | text (contents : String)
  /-- A binary file. -/
  | binary (contents : ByteArray)

/--
Writes a file into a content directory's static directory, at a path relative to it.

The path is checked with `Verso.RenderedHtml.checkFilePath`, so it cannot reach outside the
directory.
-/
def writeStaticFile (dir : System.FilePath) (path : String) (file : StaticFile) : IO Unit := do
  match checkFilePath s!"The static file of '{dir}'" path with
  | .error e => throw <| .userError e
  | .ok _ => pure ()
  let dest := staticDir dir / path
  dest.parent.forM IO.FS.createDirAll
  match file with
  | .text contents => IO.FS.writeFile dest contents
  | .binary contents => IO.FS.writeBinFile dest contents

/--
One fragment of a page that is being written.
-/
structure OutputFragment where
  /-- The fragment's name, which becomes a CSS class name and a template parameter key. -/
  name : Multi.Slug
  /-- The token that stands for the root of the mounted content in the fragment's text. -/
  rootToken : String
  /-- The fragment's markup. -/
  content : String

/--
One page that is being written.
-/
structure OutputPage where
  /-- The page's path. Each segment must be a nonempty slug. -/
  path : Multi.Path
  /-- The page's title as plain text. -/
  title : String
  /-- The page's title as inline HTML. -/
  titleHtml : String
  /-- The page's fragments. -/
  fragments : Array OutputFragment

/--
Everything that a producer hands over in order to write a rendered HTML content directory.

The files that a consumer serves verbatim are written separately, with
`Verso.RenderedHtml.writeStaticFile` or by writing into the static directory directly, because a
producer streams them out as it renders.
-/
structure Output where
  /-- The tool that produced the content. -/
  generator : RenderedHtmlContent.Generator
  /-- The title of the whole, as plain text. -/
  title : String
  /-- The title of the whole, as inline HTML. -/
  titleHtml : String
  /-- The stylesheets that the pages need, in cascade order. -/
  stylesheets : Array RenderedHtmlContent.Stylesheet := #[]
  /-- The scripts that the pages need, in load order. -/
  scripts : Array RenderedHtmlContent.Script := #[]
  /-- The pages. -/
  pages : Array OutputPage := #[]

/--
The file that a page's fragment is written to, relative to the content directory.
-/
def fragmentFile (path : Multi.Path) (name : Multi.Slug) : String :=
  "/".intercalate (fragmentsDirName :: path.toList ++ [name.toString ++ ".html"])

/--
Writes a rendered HTML content directory, returning the manifest that it wrote.

The page path density, path syntax, and destination checks that `Verso.RenderedHtml.load` performs
are applied here as well, so a producer fails where the content can be fixed. The destination check
covers the static directory as it stands on disk, so a producer writes its static files first.

Any existing fragments directory is replaced.
-/
def write (dir : System.FilePath) (out : Output) : IO RenderedHtmlContent := do
  let mut pages : TreeMap Multi.Path RenderedHtmlContent.Page comparePaths := {}
  let mut fragmentFiles : Array (String × String) := #[]

  for page in out.pages do
    let pathText := pathToString page.path
    for seg in page.path do
      if seg.isEmpty then
        throw <| .userError s!"The page path '{pathText}' has an empty segment"
      if (Multi.Slug.isSlug? seg).isNone then
        throw <| .userError s!"Segment '{seg}' of page path '{pathText}' is not a slug"
    if pages.contains page.path then
      throw <| .userError s!"There is more than one page at '{pathText}'"
    let mut fragments : TreeMap Multi.Slug RenderedHtmlContent.Fragment := {}
    for fragment in page.fragments do
      if fragment.name.toString.isEmpty then
        throw <| .userError s!"The page '{pathText}' has a fragment with an empty name"
      if fragments.contains fragment.name then
        throw <| .userError
          s!"The page '{pathText}' has more than one fragment named '{fragment.name}'"
      if fragment.rootToken.isEmpty then
        throw <| .userError
          s!"The fragment '{fragment.name}' of page '{pathText}' declares an empty root token"
      let file := fragmentFile page.path fragment.name
      fragmentFiles := fragmentFiles.push (file, fragment.content)
      fragments := fragments.insert fragment.name { file, rootToken := fragment.rootToken }
    pages := pages.insert page.path {
      title := page.title, titleHtml := page.titleHtml, fragments
    }

  let pagePaths := pages.toArray.map (·.fst)
  match checkDense pagePaths with
  | .ok () => pure ()
  | .error e => throw <| .userError e

  for css in out.stylesheets do
    checkAssetPath dir "A stylesheet" css.path
  for js in out.scripts do
    checkAssetPath dir "A script" js.path

  match checkDestinations pagePaths (← listFiles (staticDir dir)) with
  | .ok () => pure ()
  | .error e => throw <| .userError s!"In '{dir}': {e}"

  let manifest : RenderedHtmlContent := {
    generator := out.generator,
    title := out.title,
    titleHtml := out.titleHtml,
    stylesheets := out.stylesheets,
    scripts := out.scripts,
    pages
  }

  IO.FS.createDirAll dir
  let fragmentRoot := fragmentsDir dir
  if ← fragmentRoot.pathExists then
    IO.FS.removeDirAll fragmentRoot
  for (file, contents) in fragmentFiles do
    let dest := dir / file
    dest.parent.forM IO.FS.createDirAll
    IO.FS.writeFile dest contents
  IO.FS.writeFile (manifestFile dir) ((toJson manifest).pretty ++ "\n")

  return manifest
where
  checkAssetPath (dir : System.FilePath) (what : String) (path : String) : IO Unit := do
    match checkFilePath what path with
    | .error e => throw <| .userError e
    | .ok segments =>
      unless segments[0]? == some staticDirName do
        throw <| .userError s!"{what} is '{path}', which is not within '{staticDirName}/'"
      unless ← (dir / path).pathExists do
        throw <| .userError s!"{what} is '{path}', which does not exist"

end Verso.RenderedHtml
