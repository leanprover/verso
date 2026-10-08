/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata

open Errata

/-- Fails in its own code, after writing a line. -/
@[test]
def ownFailure : Test := do
  IO.println "before the failure"
  fail "the check failed"

/-- A failure inside nested named results, beside a named result that passes. -/
@[test]
def nestedFailure : Test := do
  result "fine" (IO.println "all good")
  result "outer" do
    result "inner" (assertBEq 1 2)

/-- A failed check whose line has characters that take two UTF-16 code units each before the check. -/
@[test]
def astralFailure : Test := do
  result "🙂🙂" (assertBEq 1 2)

/-- Ends the runner's process before the test reports an outcome. -/
@[test]
def exits : Test := do
  IO.println "about to exit"
  IO.Process.exit 3

/--
Whether a list is unlucky. About a fifth of the lists with at least six elements are, and which ones
are depends on every element, so each seed finds a different counterexample.
-/
private def unlucky (l : List Nat) : Bool :=
  let mix (acc : UInt64) (n : Nat) : UInt64 :=
    let x := (acc ^^^ n.toUInt64) * 1099511628211
    x ^^^ (x >>> 31)
  if l.length < 6 then false
  else l.foldl mix 14695981039346656037 % 5 == 0

/-- An `assertTrue` that fails in the test's own code, after writing a line. -/
@[test]
def ownAssertTrue : Test := do
  IO.println "checking the condition"
  assertTrue false "the message of the top-level assertTrue"

/-- An `assertTrue` that fails within a named result. -/
@[test]
def nestedAssertTrue : Test := do
  result "condition" (assertTrue false "the message of the nested assertTrue")

/-- A property that fails, with a counterexample that depends on the seed. -/
@[test]
def unluckyLists : Test :=
  property (∀ l : List Nat, unlucky l = false)
