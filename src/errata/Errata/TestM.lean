/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.Context
public import Errata.Result
public import Errata.Here

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/--
The monad in which tests run.

The reader carries the configuration and the result log; the exception layer carries a structured
failure, which the interpreter distinguishes from an {name}`IO.Error` that escapes.
-/
abbrev TestM := ReaderT Context (ExceptT TestFailure IO)

/-- A test: a {name}`TestM` action that succeeds unless it fails an assertion or raises an error. -/
abbrev Test := TestM Unit

/--
Fails at the location recorded in the context. The runner seeds that with the test's own source
range, so a failure with no more specific location still points at the test. This is the primitive
the internal layer uses when no call site is available.
-/
def failHere (message : String) (detail? : Option String := none) : TestM α := do
  throw { message, detail?, location? := some (← read).location }

/--
Fails at an explicit source location. The assertion language captures its call site with
{lit}`here%` and reports through this primitive.
-/
def failAt (loc : Location) (message : String) (detail? : Option String := none) : TestM α :=
  throw { message, detail?, location? := some loc }

/-- Fails the current test, or named result, with a message and optional detail. -/
def fail (message : String) (detail? : Option String := none)
    (loc : Location := by exact here%) : TestM α :=
  failAt loc message detail?

/--
Runs an action with the current failure location set to a call site, which defaults to the caller.
A user-defined assertion helper can wrap its checks in this so their failures report at the helper's
call site rather than inside the helper.
-/
def withLocation (loc : Location := by exact here%) (act : TestM α) : TestM α :=
  withReader ({ · with location := loc }) act

/-- All values supplied for a project option, in order; records that the option was read. -/
def optionValues (name : String) : TestM (Array String) := do
  let ctx ← read
  ctx.usedOptions.modify (·.insert name)
  return ctx.options.getD name #[]

/-- The last value supplied for a project option, if any; records that the option was read. -/
def option? (name : String) : TestM (Option String) :=
  return (← optionValues name).back?

/-- Whether a project option is present and not set to an explicit false value; records the read. -/
def flag (name : String) : TestM Bool :=
  return match (← optionValues name).back? with
    | some v => v != "false" && v != "0" && v != "no"
    | none => false

/-- Builds a result for the current scope with the given status and duration. -/
def Context.mkResult (ctx : Context) (status : Status) (durationMs : Nat := 0) : Result :=
  { package := ctx.package, moduleName := ctx.moduleName, test := ctx.test,
    resultPath := ctx.resultPath, status, durationMs }

/-- A passing result for the current scope. -/
def Context.pass (ctx : Context) (durationMs : Nat := 0) : Result :=
  ctx.mkResult .pass durationMs

/-- A failed result for the current scope. -/
def Context.fail (ctx : Context) (failure : TestFailure) (durationMs : Nat := 0) : Result :=
  ctx.mkResult (.fail failure) durationMs

/-- An errored result for the current scope. -/
def Context.error (ctx : Context) (message : String) (durationMs : Nat := 0) : Result :=
  ctx.mkResult (.error message) durationMs

/-- A skipped result for the current scope. -/
def Context.skip (ctx : Context) (reason : String) (durationMs : Nat := 0) : Result :=
  ctx.mkResult (.skip reason) durationMs

/-- Records a skipped result for the current scope. -/
def skip (reason : String) : TestM Unit := do
  let ctx ← read
  ctx.log.modify (·.push (ctx.skip reason))

/-- A stream that appends each write to a log, tagged by the stream it came from. -/
private def captureStream (log : IO.Ref (Array Output)) (mk : String → Output) : IO.FS.Stream where
  flush := pure ()
  read _ := pure .empty
  write bytes := log.modify (·.push (mk (String.fromUTF8! bytes)))
  getLine := pure ""
  putStr s := log.modify (·.push (mk s))
  isTty := pure false

/--
Runs a test action with the given context, capturing its outcome as data rather than letting it
propagate. The action's stdout and stderr are recorded, in order and tagged by stream, and returned
alongside the outcome, so a test's output is shown only when it fails.
-/
def runCapturing (ctx : Context) (act : TestM Unit) :
    IO (Except IO.Error (Except TestFailure Unit) × OutputLog) := do
  let log ← IO.mkRef (#[] : Array Output)
  let outcome ← IO.withStdout (captureStream log .stdout) <|
    IO.withStderr (captureStream log .stderr) <| ((act ctx).run).toBaseIO
  return (outcome, { log := ← log.get })

/--
Runs an action with stdout and stderr captured into a fresh log, then returns the captured output
in order. The redirection is local to the action, so a test can make assertions about what the
action wrote.
-/
def captureOutput (act : TestM Unit) : TestM OutputLog := do
  let log ← IO.mkRef (#[] : Array Output)
  IO.withStdout (captureStream log .stdout) <| IO.withStderr (captureStream log .stderr) act
  return { log := ← log.get }

/--
Runs a named result within the current test.

Its path extends the current path, and its failure is isolated from sibling results. If the action
records no nested results and completes, it contributes one passing result; if it throws, it
contributes one failed or errored result.
-/
def result (name : String) (act : TestM Unit) : TestM Unit :=
  withReader (fun c => { c with resultPath := c.resultPath.push name }) do
    let ctx ← read
    let before := (← ctx.log.get).size
    let start ← IO.monoMsNow
    let (outcome, output) ← runCapturing ctx act
    let stop ← IO.monoMsNow
    let dur := stop - start
    let after := (← ctx.log.get).size
    match outcome with
    | .error e =>
      ctx.log.modify (·.push { ctx.error (toString e) dur with output })
    | .ok (.error f) =>
      ctx.log.modify (·.push { ctx.fail f dur with output })
    | .ok (.ok ()) =>
      if after == before then
        ctx.log.modify (·.push (ctx.pass dur))

/--
Expects the action to fail an assertion. The current scope passes if it does and fails if it
succeeds. An escaping {name}`IO.Error` is not an expected failure: it propagates and is reported as an
error, so broken setup is not mistaken for a passing negative test.
-/
def expectFail (act : TestM Unit) (loc : Location := by exact here%) : TestM Unit := do
  try
    act
  catch _ =>
    return
  failAt loc "expected the action to fail, but it passed"
