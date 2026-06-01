/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
meta import Init.System.FilePath
namespace Verso.Genre.Manual.Html.Css

/--
The contents of the manual genre's `book.css`, loaded from `static-web/manual/book.css` so
the CSS can be edited (and reviewed) as CSS rather than as a Lean string literal. Written to
the output root at emit time.
-/
public def pageStyle : String := include_str "../../../../static-web/manual/book.css"
