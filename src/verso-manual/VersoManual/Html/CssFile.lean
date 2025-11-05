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
