/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Lean.Data.Json.FromToJson

namespace Verso.Genre.Manual

open Lean

/--
An extra CSS file to be included in the header, but not emitted.
-/
public structure StaticCssFile where
  filename : String
deriving BEq, Repr, Hashable, Ord

/--
An extra JS file to be emitted and added to the page.
-/
public structure CssFile extends StaticCssFile where
  contents : String
deriving BEq, ToJson, FromJson, Repr, Hashable, Ord
