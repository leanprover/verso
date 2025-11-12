/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Json.FromToJson

open Lean (ToJson FromJson)

namespace Verso.Genre.Manual

/--
A description of an open-source license used by a frontend component that's included in
generated HTML. This is used to create an attribution page.
-/
public structure LicenseInfo where
  /-- SPDX license identifier -/
  identifier : String

  /-- Dependency name. This is used in a header, and for alphabetical sorting. -/
  dependency : String

  /--
  How is the dependency used? This can give better credit.

  Examples:
    * "The display of mathematical formulae is powered by KaTeX."
    * "The graphs are rendered using Chart.js."
  -/
  howUsed : Option String

  /-- A link target used to credit the dependency's author -/
  link : Option String

  /--
  The license or notice text in plain text, divided into sections with optional headers.
   -/
  text : Array (Option String × String)

deriving Repr, DecidableEq, ToJson, FromJson, Hashable, Inhabited
