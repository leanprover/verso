/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

set_option linter.missingDocs true
set_option doc.verso true

namespace Verso.Multi

/--

A path through the site.

{given (type := "String") -show}`x,y,z` {lean type:="Path"}`#[]` is the root, and {lean}`#[x,y,z]` is
{lean}`s!"/{x}/{y}/{z}/"`. The trailing slash is important here.
-/
public abbrev Path := Array String

namespace Path

/--
The topmost path.
-/
public def root : Path := #[]

/--
Adds {lean}`component` to the end of {name}`path`.
-/
public def Path.join (path : Path) (component : String) : Path :=
  Array.push path component

instance : HDiv Path String Path := ⟨Path.join⟩

/--
Retrieves a string that can be used as a link.
This is a path relative to the site root.
-/
public def relativeLink (path : Path) (htmlId : Option String := none) : String :=
  String.join (path.toList.map (· ++ "/")) ++
  (htmlId.map ("#" ++ ·)).getD ""

/--
Retrieves a string that can be used as an absolute link.
-/
public def link (path : Path) (htmlId : Option String := none) : String :=
  "/" ++ relativeLink path htmlId

/--
Make the URL relative to the path.

This relies on the assumption that the path has only directory-like entries. In particular, the path
{lean}`#["a", "b"]` is `/a/b/`. If the browser is on `/a/b/`, then `../c/` is `/a/c/`, but if it's on
`/a/b`, then `../c/` is `/c/`.
-/
public def relativize (path : Path) (url : String) : String := Id.run do
  if "/".isPrefixOf url then
    let mut path := path.toSubarray
    let mut url := url.toSlice.drop 1
    while h : path.size > 0 do
      -- Get rid of the common prefix of the paths, to avoid unnecessary "../"s
      if let some url' := url.dropPrefix? (path[0] ++ "/") then
        path := path.drop 1
        url := url'
      else break
    String.join (List.replicate path.size "../") ++ url.toString
  else url

end Path
