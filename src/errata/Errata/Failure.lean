/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Source locations, failures, and the status of a check: the vocabulary that a test's own results and
the outcome of a whole test share.
-/
module

public import Lean.Data.Position

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/--
A source span, used in failure messages and editor integration.
-/
structure Location where
  /-- The source file that contains the span. -/
  file : String
  /-- The start of the span. -/
  startPos : Lean.Position
  /-- The end of the span. -/
  endPos : Lean.Position
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- A test failure, carrying the information needed to explain it. -/
structure TestFailure where
  /-- A short description of what went wrong. -/
  message : String
  /-- Supporting detail, such as a diff, a counterexample, or expected and actual values. -/
  detail? : Option String := none
  /-- The source location of the failed check, when known. -/
  location? : Option Location := none
deriving Repr, Inhabited, DecidableEq

/-- The verdict that a test body may return. -/
inductive TestResult where
  /-- The test passed. -/
  | pass
  /-- The test failed, with details. -/
  | fail (failure : TestFailure)
deriving Repr, Inhabited

/-- The recorded outcome of a test or a named result. -/
inductive Status where
  /-- The check passed. -/
  | pass
  /-- The check failed. -/
  | fail (failure : TestFailure)
  /-- An error escaped the check, so it could not produce a verdict. -/
  | error (message : String)
deriving Repr, Inhabited, DecidableEq

/-- Whether a status counts as success for the exit code. -/
def Status.isSuccess : Status → Bool
  | .pass => true
  | .fail _ | .error _ => false
