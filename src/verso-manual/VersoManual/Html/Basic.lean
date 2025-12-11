/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Lean.Data.Json.FromToJson

set_option linter.missingDocs true
set_option doc.verso true

open Lean
namespace Verso.Genre.Manual

/-!
This module contains wrappers around strings that prevent different formats from being confused by
accident.
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

public instance : DecidableLE CSS := fun x y => inferInstanceAs (DecidableLE String) x.css y.css

public instance : LT CSS where
  lt x y := x.css < y.css

public instance : DecidableLT CSS := fun x y => inferInstanceAs (DecidableLT String) x.css y.css

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

public instance : DecidableLE JS := fun x y => inferInstanceAs (DecidableLE String) x.js y.js

public instance : LT JS where
  lt x y := x.js < y.js

public instance : DecidableLT JS := fun x y => inferInstanceAs (DecidableLT String) x.js y.js

public instance : Coe String JS where
  coe := JS.mk

public instance : ToJson JS where
  toJson v := .str v.js

public instance : FromJson JS where
  fromJson? v := do
    JS.mk <$> v.getStr?
