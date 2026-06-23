/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
meta import all VersoBlog.LiterateLeanPage

namespace Verso.Tests.VersoBlog.LiterateLeanPage

open Verso.Genre.Blog.Literate.Internal

/-! ## Tests for the `url_subst` URL-rewriting macros

`url_subst` builds a function that matches a URL against a pattern and rewrites it from a template.
-/

/-- info: some (Except.ok "foo/foo/bar/baz/f.png") -/
#guard_msgs in
#eval (url_subst "xy/" z "/static/" pic ".jpg" => "foo/" z "/" pic ".png") "xy/foo/static/bar/baz/f.jpg"
