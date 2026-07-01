/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Lean.Data.Json

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

open Lean

/--
Encodes a {name}`Lean.Name` structurally, preserving the numeric and hygienic components that the
standard string form does not round-trip. The widget and the single-test runner exchange test names
this way.
-/
def nameToJson : Name → Json
  | .anonymous => .null
  | .str p s => Json.mkObj [("str", .arr #[nameToJson p, .str s])]
  | .num p n => Json.mkObj [("num", .arr #[nameToJson p, .num n])]

/-- Decodes a {name}`Lean.Name` written by {name}`nameToJson`. -/
partial def nameOfJson? (j : Json) : Except String Name := do
  if j.isNull then return .anonymous
  if let .ok arr := j.getObjVal? "str" then
    let #[p, s] := (← fromJson? arr : Array Json) | .error "malformed name component"
    return .str (← nameOfJson? p) (← fromJson? s)
  if let .ok arr := j.getObjVal? "num" then
    let #[p, n] := (← fromJson? arr : Array Json) | .error "malformed name component"
    return .num (← nameOfJson? p) (← fromJson? n)
  .error "expected an encoded `Name`"
