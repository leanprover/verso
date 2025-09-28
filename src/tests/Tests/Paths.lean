/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module


import MultiVerso.Path

set_option doc.verso true

namespace Verso.Multi
open Path

/-! Tests for the module MultiVerso.Path -/

-- TODO: adapt to module system. Right now, non-meta imports work in server, but not command line.
/-
/-- info: "/" -/
#guard_msgs in
#eval link #[]

/-- info: "/a/b/" -/
#guard_msgs in
#eval link #["a", "b"]

/-- info: "/a/b/#c" -/
#guard_msgs in
#eval link #["a", "b"] (htmlId := some "c")
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

-/
