/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Std.Data.HashMap
public import Std.Data.HashSet
public import VersoRenderedHtml.Format
public import VersoRenderedHtml.Tokens

public section

set_option linter.missingDocs true

open Lean (Json fromJson?)
open Std (HashMap HashSet)

namespace Verso.RenderedHtml

/--
The directory of files that a consumer serves verbatim, within a rendered HTML content directory.
-/
def staticDir (dir : System.FilePath) : System.FilePath := dir / staticDirName

/--
The directory of HTML fragments, within a rendered HTML content directory.
-/
def fragmentsDir (dir : System.FilePath) : System.FilePath := dir / fragmentsDirName

/--
The manifest file of a rendered HTML content directory.
-/
def manifestFile (dir : System.FilePath) : System.FilePath := dir / manifestFileName

/--
A path to a file within a content directory, as its segments.

The checks that a directory is well formed ask what a path's first segment is and which directories
it needs, so they hold a path apart rather than joined.
-/
abbrev PathSegments := Array String

/--
Checks that a path held by a manifest is relative to the content directory, uses `/` as its
separator, and has no `.` or `..` segment, returning its segments.

Reading a directory therefore touches nothing outside it.
-/
def checkFilePath (what : String) (path : String) : Except String PathSegments := do
  if path.isEmpty then
    throw s!"{what} is an empty path"
  if path.startsWith "/" then
    throw s!"{what} is the absolute path '{path}'"
  if path.any (· == '\\') then
    throw s!"{what} is the path '{path}', which contains a backslash"
  let mut segments := #[]
  for seg in path.splitOn "/" do
    if seg.isEmpty then
      throw s!"{what} is the path '{path}', which has an empty segment"
    if seg == "." || seg == ".." then
      throw s!"{what} is the path '{path}', which has a '{seg}' segment"
    segments := segments.push seg
  return segments

/--
Checks that every proper prefix of a page path is itself a page path.

A directory therefore always has an index, and the root page is always present.
-/
def checkDense (pages : Array Multi.Path) : Except String Unit := do
  if pages.isEmpty then
    throw "There are no pages. Page paths must be dense, so the root page is always present."
  let present : HashSet String := pages.foldl (fun acc p => acc.insert (pathToString p)) {}
  for p in pages do
    for i in [0:p.size] do
      let ancestor := pathToString (p.extract 0 i)
      unless present.contains ancestor do
        throw <|
          s!"The page '{pathToString p}' has no page at '{ancestor}'. " ++
          "Page paths must be dense."

/--
Checks that the files that a mounted directory writes have distinct paths.

A page writes an `index.html` beneath its own path, so every prefix of a page's path must be a
directory, and likewise for a static file.
-/
def checkDestinations
    (pages : Array Multi.Path) (staticFiles : Array PathSegments) : Except String Unit := do
  let mut files : HashMap String String := {}
  let mut dirs : HashMap String String := {}
  let mut problems : Array String := #[]
  for p in pages do
    let dir := pathToString p
    dirs := dirs.insert dir s!"the page '{dir}'"
    let file := (if dir.isEmpty then "" else dir ++ "/") ++ "index.html"
    if let some other := files[file]? then
      problems := problems.push s!"Both {other} and the page '{dir}' write '{file}'"
    files := files.insert file s!"the page '{dir}'"
  for segments in staticFiles do
    let file := "/".intercalate segments.toList
    if let some other := files[file]? then
      problems := problems.push
        s!"Both {other} and the static file '{staticDirName}/{file}' write '{file}'"
    files := files.insert file s!"the static file '{staticDirName}/{file}'"
    for i in [0:segments.size] do
      let dir := "/".intercalate (segments.toList.take i)
      unless dirs.contains dir do
        dirs := dirs.insert dir s!"the static directory '{staticDirName}/{dir}'"
  for (file, claimant) in files.toList do
    if let some other := dirs[file]? then
      problems := problems.push
        s!"{claimant} writes the file '{file}', but {other} needs it to be a directory"
  unless problems.isEmpty do
    throw <| "\n".intercalate problems.qsort.toList

/--
Lists the files under a directory, as paths relative to it.
-/
partial def listFiles (root : System.FilePath) : IO (Array PathSegments) := do
  if ← root.pathExists then go root #[] else return #[]
where
  go (dir : System.FilePath) (prefixSegments : Array String) : IO (Array (Array String)) := do
    let entries := (← dir.readDir).qsort (·.fileName < ·.fileName)
    let mut out := #[]
    for entry in entries do
      let segments := prefixSegments.push entry.fileName
      if ← entry.path.isDir then
        out := out ++ (← go entry.path segments)
      else
        out := out.push segments
    return out

/--
A rendered HTML content directory whose manifest has been read and checked.
-/
structure Loaded where
  /-- The content directory. -/
  dir : System.FilePath
  /-- The directory's manifest. -/
  manifest : RenderedHtmlContent
deriving Inhabited

/--
Reads and checks the manifest of a rendered HTML content directory.

A fragment reaches a consumer as text, so its contents are trusted as far as the consumer trusts the
directory it mounts.
-/
def load (dir : System.FilePath) : IO Loaded := do
  let file := manifestFile dir
  unless ← file.pathExists do
    throw <| .userError s!"There is no rendered HTML content manifest at '{file}'"
  let text ← IO.FS.readFile file
  let json ←
    match Json.parse text with
    | .ok json => pure json
    | .error e => throw <| .userError s!"Failed to parse '{file}': {e}"
  let manifest : RenderedHtmlContent ←
    match fromJson? json with
    | .ok manifest => pure manifest
    | .error e => throw <| .userError s!"Failed to read '{file}': {e}"

  unless manifest.format == formatName do
    throw <| .userError
      s!"'{file}' has format '{manifest.format}', but '{formatName}' was expected"
  if manifest.formatVersion > formatVersion then
    throw <| .userError <|
      s!"'{file}' is written in format version {manifest.formatVersion}, but this version of " ++
      s!"Verso understands version {formatVersion}. Build the consuming site with a newer Verso."

  let pagePaths := manifest.pages.toArray.map (·.fst)
  match checkDense pagePaths with
  | .ok () => pure ()
  | .error e => throw <| .userError s!"In '{file}': {e}"

  for css in manifest.stylesheets do
    checkAssetPath file s!"The stylesheet of '{file}'" css.path
  for js in manifest.scripts do
    checkAssetPath file s!"The script of '{file}'" js.path

  for (path, page) in manifest.pages do
    for (name, fragment) in page.fragments do
      let what := s!"The fragment '{name}' of page '{pathToString path}' in '{file}'"
      match checkFilePath what fragment.file with
      | .ok _ => pure ()
      | .error e => throw <| .userError e
      unless ← (dir / fragment.file).pathExists do
        throw <| .userError s!"{what} names '{fragment.file}', which does not exist"

  match checkDestinations pagePaths (← listFiles (staticDir dir)) with
  | .ok () => pure ()
  | .error e => throw <| .userError s!"In '{dir}': {e}"

  return { dir, manifest }
where
  checkAssetPath (file : System.FilePath) (what : String) (path : String) : IO Unit := do
    match checkFilePath what path with
    | .error e => throw <| .userError e
    | .ok segments =>
      unless segments[0]? == some staticDirName do
        throw <| .userError
          s!"{what} is '{path}', which is not within '{staticDirName}/' in '{file}'"
      unless ← (dir / path).pathExists do
        throw <| .userError s!"{what} is '{path}', which does not exist"

/-- The directory of files that this content's consumer serves verbatim. -/
def Loaded.staticDir (loaded : Loaded) : System.FilePath := RenderedHtml.staticDir loaded.dir

/-- The directory of this content's HTML fragments. -/
def Loaded.fragmentsDir (loaded : Loaded) : System.FilePath := RenderedHtml.fragmentsDir loaded.dir

/-- Reads a fragment's text, with its root token left as it stands. -/
def Loaded.readFragmentText
    (loaded : Loaded) (fragment : RenderedHtmlContent.Fragment) : IO String :=
  IO.FS.readFile (loaded.dir / fragment.file)

/--
Reads a fragment, replacing its root token with the prefix at which the mounted content is served.
-/
def Loaded.readFragment
    (loaded : Loaded) (fragment : RenderedHtmlContent.Fragment) (root : String) : IO String := do
  return substitute fragment.rootToken root (← loaded.readFragmentText fragment)

end Verso.RenderedHtml
