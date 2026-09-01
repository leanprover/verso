/-
Copyright (c) 2025-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Lean.Data.Json.FromToJson

set_option linter.missingDocs true

open Lean

namespace Verso.Output.Html.Files

/-!
Wrappers around strings that prevent different formats from being confused by accident, and the
stylesheets and scripts that a genre collects for a page's `<head>`.
-/

/--
Cascading Stylesheet code.
-/
public structure CSS where
  /-- The CSS code -/
  css : String
deriving BEq, Hashable, Ord, DecidableEq, Repr

public instance : ToString CSS := ⟨CSS.css⟩

public instance : LE CSS where
  le x y := x.css ≤ y.css

public instance : DecidableLE CSS := fun x y => (inferInstance : DecidableLE String) x.css y.css

public instance : LT CSS where
  lt x y := x.css < y.css

public instance : DecidableLT CSS := fun x y => (inferInstance : DecidableLT String) x.css y.css

public instance : Coe String CSS where
  coe := CSS.mk

public instance : ToJson CSS where
  toJson v := .str v.css

public instance : FromJson CSS where
  fromJson? v := do
    CSS.mk <$> v.getStr?

/--
JavaScript code.
-/
public structure JS where
  /-- The JavaScript code -/
  js : String
deriving BEq, Hashable, Ord, DecidableEq, Repr

public instance : ToString JS := ⟨JS.js⟩

public instance : LE JS where
  le x y := x.js ≤ y.js

public instance : DecidableLE JS := fun x y => (inferInstance : DecidableLE String) x.js y.js

public instance : LT JS where
  lt x y := x.js < y.js

public instance : DecidableLT JS := fun x y => (inferInstance : DecidableLT String) x.js y.js

public instance : Coe String JS where
  coe := JS.mk

public instance : ToJson JS where
  toJson v := .str v.js

public instance : FromJson JS where
  fromJson? v := do
    JS.mk <$> v.getStr?

/--
An extra CSS file to be included in the header, but not emitted.
-/
public structure StaticCssFile where
  /-- The file's name, relative to the directory that a genre serves its files from. -/
  filename : String
deriving BEq, Repr, Hashable, Ord

/--
An extra CSS file to be emitted and added to the page.
-/
public structure CssFile extends StaticCssFile where
  /-- The stylesheet's contents. -/
  contents : CSS
deriving BEq, ToJson, FromJson, Repr, Hashable, Ord

/--
An extra JS file to be included in the header, but not emitted.
-/
public structure StaticJsFile where
  /-- The file's name, relative to the directory that a genre serves its files from. -/
  filename : String
  /-- Whether the reference to the script carries `defer`. -/
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
  /-- The source map's name, relative to the directory that a genre serves its files from. -/
  filename : String
  /-- The source map's contents. -/
  contents : String
deriving BEq, ToJson, FromJson, Repr, Hashable, Ord

/--
An extra JS file to be emitted and added to the page.
-/
public structure JsFile extends StaticJsFile where
  /-- The script's contents. -/
  contents : JS
  /-- The script's source map, when it has one. -/
  sourceMap? : Option JsSourceMap
deriving BEq, ToJson, FromJson, Repr, Hashable, Ord

/--
Orders scripts so that each one comes after every file that it names in `after`.

Unconstrained scripts, or constraints that are unsatisfiable due to cycles in the `after` relation,
remain in their original order.
-/
public def sortByAfter (staticFile : α → StaticJsFile) (files : Array α) : Array α :=
  go #[] files
where
  go (placed todo : Array α) : Array α :=
    if _ : todo.isEmpty then placed
    else
      let ready := fun f =>
        (staticFile f).after.all fun name => placed.any fun g => (staticFile g).filename == name
      match _ : todo.findIdx? ready with
      | none => placed ++ todo
      | some i =>
        match todo[i]? with
        | none => placed ++ todo
        | some next =>
          go (placed.push next) (todo.extract 0 i ++ todo.extract (i + 1) todo.size)
  termination_by todo.size
  decreasing_by grind [Array.findIdx?_eq_some_iff_findIdx_eq]
