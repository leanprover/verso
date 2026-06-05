/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

set_option linter.missingDocs true
set_option doc.verso true

/-!
A small reusable hyperlink type used by themes and palettes to point readers at canonical
references (a Solarized homepage, a designer's portfolio, a palette specification, etc.).
Lives in its own module so palette modules can expose a {lit}`SourceLink` value without
depending on the full {lit}`CodeTheme` machinery.
-/

namespace Verso.Theme

/--
A hyperlink: the URL plus the visible link text. Surfaced by the picker UI alongside a theme
or palette so readers can follow the link to its canonical reference.
-/
public structure SourceLink where
  /-- The URL the link points to. -/
  url : String
  /-- The visible link text. -/
  text : String
deriving Repr

end Verso.Theme
