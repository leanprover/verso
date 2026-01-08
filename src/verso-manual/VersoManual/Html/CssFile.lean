/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Lean.Data.Json.FromToJson
public import VersoManual.Html.Basic


namespace Verso.Genre.Manual

open Lean

/--
An extra CSS file to be included in the header, but not emitted.
-/
public structure StaticCssFile where
  filename : String
deriving BEq, Repr, Hashable, Ord

/--
An extra CSS file to be emitted and added to the page.
-/
public structure CssFile extends StaticCssFile where
  contents : CSS
deriving BEq, ToJson, FromJson, Repr, Hashable, Ord
