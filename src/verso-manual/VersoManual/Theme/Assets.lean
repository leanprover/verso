/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
meta import Init.System.FilePath

namespace Verso.Genre.Manual.Theme

/-- The picker JavaScript: builds the dialog opened by `#theme-picker-button`. -/
public def «theme-picker.js» : String := include_str "../../../../static-web/manual/theme/theme-picker.js"

/-- The picker styles. -/
public def «theme-picker.css» : String := include_str "../../../../static-web/manual/theme/theme-picker.css"

/--
A small fixed code sample the picker drops into the preview pane so the user can see what each
candidate theme will look like. Rendered as `def greet name := s!"Hello, {name}"` using the
same `.hl.lean` token classes the real highlighter emits, so token colors, weights, and the
font family resolve from the candidate theme.
-/
public def codeSampleHtml : String :=
  "<code class=\"hl lean block\">" ++
  "<span class=\"keyword\">def</span> " ++
  "<span class=\"const\">greet</span> " ++
  "<span class=\"var\">name</span> " ++
  "<span class=\"unknown\">:=</span> " ++
  "<span class=\"keyword\">s!</span>" ++
  "<span class=\"literal\">&quot;Hello, {</span>" ++
  "<span class=\"var\">name</span>" ++
  "<span class=\"literal\">}&quot;</span>" ++
  "</code>"

end Verso.Genre.Manual.Theme
