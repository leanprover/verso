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
An extra JS file to be included in the header, but not emitted.
-/
public structure StaticJsFile where
  filename : String
  defer : Bool := false
  /-- Load after these other named files -/
  after : Array String := #[]
deriving BEq, Repr, Hashable, Ord

/--
A JavaScript source map to be included along with emitted JavaScript.

Many minified JavaScript files contain a reference to a source map. The filename here should match
the one referred to by the minified file; Verso will not validate this.
-/
public structure JsSourceMap where
  filename : String
  contents : String
deriving BEq, ToJson, FromJson, Repr, Hashable, Ord

/--
An extra JS file to be emitted and added to the page.
-/
public structure JsFile extends StaticJsFile where
  contents : String
  sourceMap? : Option JsSourceMap
deriving BEq, ToJson, FromJson, Repr, Hashable, Ord
