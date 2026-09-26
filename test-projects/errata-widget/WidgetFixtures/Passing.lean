/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata

open Errata

public section

/-- Writes to both streams. -/
@[test]
def bothStreams : Test := do
  IO.println "on stdout"
  IO.eprintln "on stderr"
  IO.println "stdout again"

/-- Writes a line at a time, with pauses between them. -/
@[test]
def streamed : Test := do
  for step in [1, 2, 3, 4] do
    IO.println s!"step {step}"
    IO.sleep 700

/-- Keeps writing for a minute, so that it can be cancelled while it runs. -/
@[test]
def slow : Test := do
  for tick in [0:120] do
    IO.println s!"tick {tick}"
    IO.sleep 500

/-- Named results, with output at each level, and results that report nothing beyond a verdict. -/
@[test]
def nested : Test := do
  IO.println "setting up"
  result "parsing" do
    IO.println "reading"
    result "tokens" do
      IO.println "12 tokens"
    result "quiet" (pure ())
  result "silent" (pure ())

/-- Output from before, inside, and after a named result. -/
@[test]
def copyOrder : Test := do
  IO.println "outer"
  result "inner" (IO.println "within")
  IO.println "after"

/-- Subprocesses write to the runner's own standard output and error, which the test's capture misses. -/
@[test]
def strayOutput : Test := do
  IO.println "captured"
  let child ← IO.Process.spawn { cmd := "printf", args := #["stray output"], stdout := .inherit }
  discard child.wait
  let child ← IO.Process.spawn { cmd := "sh", args := #["-c", "printf 'stray error\\n' >&2"] }
  discard child.wait

/-- A test with a docstring over two lines,
   whose closing delimiter follows its last text. -/
@[test]
def longDocstring : Test := IO.println "documented"

/-- A test that a later command marks as a test. -/
def markedSeparately : Test := IO.println "marked separately"

attribute [test] markedSeparately

/-- A test whose attribute list spans two lines. -/
@[reducible,
  test]
def multiLineAttributes : Test := IO.println "two lines of attributes"

/--
A named result that fails within an `expectFail` whose action ends with an escaping error, within an
`expectFail` that expects the failure.
-/
@[test]
def nestedExpectFail : Test := do
  expectFail do
    result "outer" do
      expectFail do
        result "inner" (assertBEq 1 2)
        liftM (throw (IO.userError "escaped") : IO Unit)

/-- A property that holds. -/
@[test]
def reverseReverse : seed → Test :=
  property (∀ l : List Nat, l.reverse.reverse = l)

/-- A named result that fails within `expectFail`, beside a named result that passes. -/
@[test]
def expectedFailure : Test := do
  expectFail do
    result "expected" (assertBEq 1 2)
  result "fine" (pure ())

/-- Writes one line far longer than one read of the runner's output, made of three-byte characters. -/
@[test]
def wideCharacters : Test :=
  IO.println (String.ofList (List.replicate 100000 '∀'))

/-- Leaves a process running that holds the runner's output pipes open after the test has ended. -/
@[test]
def lingeringProcess : Test := do
  IO.println "started a helper"
  discard <| IO.Process.spawn { cmd := "sleep", args := #["37"] }

/-- The words that `readsSettings` greets with. -/
@[setting, expose]
def greeting : Setting where
  type := String
  fromString s := some s
  default? := some "hello"

/-- Whether `readsSettings` fails. -/
@[setting, expose]
def strict : Setting where
  type := Bool
  fromString
    | "true" => some true
    | "false" => some false
    | _ => none
  default? := some "false"

/-- Writes its greeting, and fails when `strict` is `true`. -/
@[test]
def readsSettings (word : greeting) (strict : strict) : Test := do
  IO.println s!"greeting: {word}"
  if strict then
    fail "strict was set"

/-- Whom `greetsAudience` greets. It has no default, so a run needs a value for it. -/
@[setting, expose]
def audience : Setting where
  type := String
  fromString s := some s

/-- Greets its audience, which a run must name. -/
@[test]
def greetsAudience (who : audience) : Test :=
  IO.println s!"hello, {who}"

/--
Tagged `manual`, which every profile's default filter leaves out, so a run of it sets the default
filter aside.
-/
@[test (tags := manual)]
def manualOnly : Test :=
  IO.println "ran by hand"
