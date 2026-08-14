/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.TestM
public import Errata.Result

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/-- Runs a returned verdict as a test action. -/
def TestResult.toTest : TestResult → TestM Unit
  | .pass => pure ()
  | .fail f => throw f
  | .skip reason => Errata.skip reason

/-- Types that can serve as the body of a test. -/
class IsTest (α : Type) where
  /-- Runs the value as a test action. -/
  toTest : α → TestM Unit

instance : IsTest (TestM Unit) where
  toTest act := act

instance : IsTest TestResult where
  toTest := TestResult.toTest

instance : IsTest (IO TestResult) where
  toTest act := do (← act).toTest

instance : IsTest Bool where
  toTest b := unless b do failHere "expected true, got false"

instance : IsTest (IO Bool) where
  toTest act := do unless (← act) do failHere "expected true, got false"
