/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module

public import Errata

set_option doc.verso true

open Errata

/--
How much longer the pauses in these tests are than their shortest version, which keeps the test
suite fast. Set it to {lean}`100` to watch the output stream into the widget.
-/
private def sleepMultiplier : UInt32 := 1

/--
Whether the tests in this module should generally pass. Set it to {name}`false` to experiment with
failing tests.
-/
private def shouldPass : Bool := true

/--
Writing to {lit}`stdout` and {lit}`stderr`.
-/
@[test]
def bothStreams : Test := do
  IO.println "the first line, on stdout"
  IO.eprintln "a warning, on stderr"
  IO.println "the last line, on stdout"
  assertTrue shouldPass "`shouldPass` is false"

/--
Writing individual lines, with pauses.
-/
@[test]
def streamedOutput : Test := do
  for step in [1, 2, 3, 4, 5] do
    IO.println s!"step {step} of 5"
    IO.sleep <| 3 * step * sleepMultiplier
  IO.eprintln "the last step wrote to stderr"
  assertTrue shouldPass "`shouldPass` is false"

/--
A property: reversing a list of natural numbers twice gives the list back.

The widget reports the random seed and allows experimentation with it.
-/
@[test]
def reverseReverse : Test :=
  property (∀ l : List Nat, (if shouldPass then l.reverse else l).reverse = l)

/--
Whether a list is unlucky.

About a fifth of the lists with at least six elements are unlucky, and shrinking leaves a
counterexample about as long as the one found.
-/
private def unlucky (l : List Nat) : Bool :=
  let mix (acc : UInt64) (n : Nat) : UInt64 :=
    let x := (acc ^^^ n.toUInt64) * 1099511628211
    x ^^^ (x >>> 31)
  if l.length < 6 then false
  else l.foldl mix 14695981039346656037 % 5 == 0

/--
A property test that is highly likely to fail in a variety of ways.
-/
--@[test]
def unluckyLists : Test :=
  property (∀ l : List Nat, unlucky l = false)

/--
Whether the located checks pass. Set it to {name}`false` to see where a failed check is.
-/
private def locatedPass : Bool := true

/--
Failures that know where they came from.

Every assertion records its own source position, which the widget offers as a link beside the
message. Following one opens the file at the check that failed, and each of these fails somewhere
else.
-/
@[test]
def locatedFailures : Test := do
  result "a number" do
    assertBEq 42 (if locatedPass then 42 else 41)
  result "a string" do
    assertContains "needle" (if locatedPass then "a needle in a haystack" else "only hay")
  result "deeper down" do
    result "a list" do
      assertBEq [1, 2, 3] (if locatedPass then [1, 2, 3] else [1, 2])

/--
A test with named results, one inside another, with output at each level.
-/
@[test]
def nestedResults : Test := do
  IO.println "setting up"
  result "parsing" do
    IO.println "reading the source"
    for _ in 0...5 do
      IO.sleep <| 2 * sleepMultiplier
      IO.println "..."
    result "tokens" do
      IO.println "12 tokens"
      IO.sleep <| 5 * sleepMultiplier
      assertBEq 12 12
    result "syntax" do
      assertBEq "(+ 1 2)" (if shouldPass then "(+ 1 2)" else "(+ 1 3)")
  result "evaluation" do
    IO.eprintln "the evaluator is slow today"
    result "arithmetic" (assertBEq 4 (2 + 2))
  IO.println "tearing down"
