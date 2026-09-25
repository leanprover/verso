/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module


import Errata
import MultiVerso.Path

set_option doc.verso true

namespace Verso.Multi
open Path

/-! Tests for the module MultiVerso.Path -/

-- TODO: adapt to module system. Right now, non-meta imports work in server, but not command line.
/-
/-- info: "/" -/
#test_msgs in
#eval link #[]

/-- info: "/a/b/" -/
#test_msgs in
#eval link #["a", "b"]

/-- info: "/a/b/#c" -/
#test_msgs in
#eval link #["a", "b"] (htmlId := some "c")
/- Tests for relativization. -/

/-- info: "a/b/c/" -/
#test_msgs in
#eval Path.relativize #[] "/a/b/c/"
/-- info: "a/b/c/#foo" -/
#test_msgs in
#eval Path.relativize #[] "/a/b/c/#foo"
/-- info: "a/b/c#foo" -/
#test_msgs in
#eval Path.relativize #[] "/a/b/c#foo"

/-- info: "b/c/" -/
#test_msgs in
#eval Path.relativize #["a"] "/a/b/c/"
/-- info: "b/c/#foo" -/
#test_msgs in
#eval Path.relativize #["a"] "/a/b/c/#foo"
/-- info: "b/c#foo" -/
#test_msgs in
#eval Path.relativize #["a"] "/a/b/c#foo"

/-- info: "c/" -/
#test_msgs in
#eval Path.relativize #["a", "b"] "/a/b/c/"
/-- info: "c/#foo" -/
#test_msgs in
#eval Path.relativize #["a", "b"] "/a/b/c/#foo"
/-- info: "c#foo" -/
#test_msgs in
#eval Path.relativize #["a", "b"] "/a/b/c#foo"

/-- info: "../../aa/b/c#foo" -/
#test_msgs in
#eval Path.relativize #["a", "b"] "/aa/b/c#foo"

/-- info: "../" -/
#test_msgs in
#eval Path.relativize #["a", "b", "c", "d"] "/a/b/c/"
/-- info: "../../c" -/
#test_msgs in
#eval Path.relativize #["a", "b", "c", "d"] "/a/b/c"

/-- info: "../#foo" -/
#test_msgs in
#eval Path.relativize #["a", "b", "c", "d"] "/a/b/c/#foo"
/-- info: "../../" -/
#test_msgs in
#eval Path.relativize #["a", "b", "c", "d", "e"] "/a/b/c/"
/-- info: "../../#foo" -/
#test_msgs in
#eval Path.relativize #["a", "b", "c", "d", "e"] "/a/b/c/#foo"
/-- info: "../../../c#foo" -/
#test_msgs in
#eval Path.relativize #["a", "b", "c", "d", "e"] "/a/b/c#foo"

/-- info: "../../../c" -/
#test_msgs in
#eval Path.relativize #["a", "b", "c", "d", "e"] "/a/b/c"

/-- info: "" -/
#test_msgs in
#eval Path.relativize #[] "/"

-/
