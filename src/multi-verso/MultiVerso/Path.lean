/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

set_option linter.missingDocs true

namespace Verso.Multi

/-- An absolute path through the site.

#[] is the root, and #[x,y,z] is s!"/{x}/{y}/{z}/". The trailing slash is important here.
-/
abbrev Path := Array String

namespace Path

/--
Retrieves a string that can be used as a link.
-/
def link (path : Path) (htmlId : Option String := none) : String :=
  "/" ++ String.join (path.toList.map (· ++ "/")) ++
  (htmlId.map ("#" ++ ·)).getD ""

/-- info: "/" -/
#guard_msgs in
#eval link #[]

/-- info: "/a/b/" -/
#guard_msgs in
#eval link #["a", "b"]

/-- info: "/a/b/#c" -/
#guard_msgs in
#eval link #["a", "b"] (htmlId := some "c")

/--
Make the URL relative to the path.

This relies on the assumption that the path has only directory-like entries. In particular, the path
`#["a", "b"]` is `/a/b/`. If the browser is on `/a/b/`, then `../c/` is `/a/c/`, but if it's on
`/a/b`, then `../c/` is `/c/`.
-/
def relativize (path : Path) (url : String) : String := Id.run do
  if "/".isPrefixOf url then
    let mut path := path.toSubarray
    let mut url := url.toSubstring.drop 1
    while h : path.size > 0 do
      -- Get rid of the common prefix of the paths, to avoid unnecessary "../"s
      if let some url' := url.dropPrefix? (path[0] ++ "/").toSubstring then
        path := path.drop 1
        url := url'
      else break
    String.join (List.replicate path.size "../") ++ url.toString
  else url

/- Tests for relativization. -/

/-- info: "a/b/c/" -/
#guard_msgs in
#eval Path.relativize #[] "/a/b/c/"
/-- info: "a/b/c/#foo" -/
#guard_msgs in
#eval Path.relativize #[] "/a/b/c/#foo"
/-- info: "a/b/c#foo" -/
#guard_msgs in
#eval Path.relativize #[] "/a/b/c#foo"

/-- info: "b/c/" -/
#guard_msgs in
#eval Path.relativize #["a"] "/a/b/c/"
/-- info: "b/c/#foo" -/
#guard_msgs in
#eval Path.relativize #["a"] "/a/b/c/#foo"
/-- info: "b/c#foo" -/
#guard_msgs in
#eval Path.relativize #["a"] "/a/b/c#foo"

/-- info: "c/" -/
#guard_msgs in
#eval Path.relativize #["a", "b"] "/a/b/c/"
/-- info: "c/#foo" -/
#guard_msgs in
#eval Path.relativize #["a", "b"] "/a/b/c/#foo"
/-- info: "c#foo" -/
#guard_msgs in
#eval Path.relativize #["a", "b"] "/a/b/c#foo"

/-- info: "../../aa/b/c#foo" -/
#guard_msgs in
#eval Path.relativize #["a", "b"] "/aa/b/c#foo"

/-- info: "../" -/
#guard_msgs in
#eval Path.relativize #["a", "b", "c", "d"] "/a/b/c/"
/-- info: "../../c" -/
#guard_msgs in
#eval Path.relativize #["a", "b", "c", "d"] "/a/b/c"

/-- info: "../#foo" -/
#guard_msgs in
#eval Path.relativize #["a", "b", "c", "d"] "/a/b/c/#foo"
/-- info: "../../" -/
#guard_msgs in
#eval Path.relativize #["a", "b", "c", "d", "e"] "/a/b/c/"
/-- info: "../../#foo" -/
#guard_msgs in
#eval Path.relativize #["a", "b", "c", "d", "e"] "/a/b/c/#foo"
/-- info: "../../../c#foo" -/
#guard_msgs in
#eval Path.relativize #["a", "b", "c", "d", "e"] "/a/b/c#foo"

/-- info: "../../../c" -/
#guard_msgs in
#eval Path.relativize #["a", "b", "c", "d", "e"] "/a/b/c"

/-- info: "" -/
#guard_msgs in
#eval Path.relativize #[] "/"

end Path
