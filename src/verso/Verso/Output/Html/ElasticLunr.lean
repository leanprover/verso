/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
meta import Init

set_option linter.missingDocs true

namespace Verso.Output.Html

/--
The minified elasticlunr JS file's contents.
-/
public def elasticlunr.min.js : String :=
  include_str "../../../../../vendored-js/elasticlunr/elasticlunr.min.js"

/--
The complete elasticlunr JS file's contents.
-/
public def elasticlunr.js : String :=
  include_str "../../../../../vendored-js/elasticlunr/elasticlunr.js"
