/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public section

set_option linter.missingDocs true

namespace Verso.Output.Html

/--
The class that marks a subtree as Verso content.

An element belongs to the nearest enclosing element that carries it, which is how a script confines
itself to the markup of its own Verso release when a page holds wrappers from several.
-/
def versoContentClass : String := "verso-content"

