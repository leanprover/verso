/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Options

public section

/-- Warns when headers don't have tags -/
register_option linter.verso.manual.headerTags : Bool := {
  defValue := false
  descr := "if true, warn when headers don't have tags"
}
