/-
Copyright (c) 2025-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoBlog.LiterateLeanPage

open Verso.Genre.Blog.Literate.Internal

/-- info: some (Except.ok "foo/foo/bar/baz/f.png") -/
#guard_msgs in
#eval (url_subst "xy/" z "/static/" pic ".jpg" => "foo/" z "/" pic ".png") "xy/foo/static/bar/baz/f.jpg"
