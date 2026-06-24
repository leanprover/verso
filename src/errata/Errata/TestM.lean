/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.Context
public import Errata.Result

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

/-- Fails the current test, or named result, with a message and optional detail. -/
def fail (message : String) (detail? : Option String := none)
    (location? : Option Location := none) : TestM α :=
  throw { message, detail?, location? }

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

/-- Runs a test action, capturing its outcome as data rather than letting it propagate. -/
def captureOutcome (act : TestM Unit) :
    TestM (Except IO.Error (Except TestFailure Unit)) := do
  let ctx ← read
  let outcome ← ((act ctx).run).toBaseIO
  pure outcome

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
    let outcome ← captureOutcome act
    let stop ← IO.monoMsNow
    let dur := stop - start
    let after := (← ctx.log.get).size
    match outcome with
    | .error e =>
      ctx.log.modify (·.push (ctx.error (toString e) dur))
    | .ok (.error f) =>
      ctx.log.modify (·.push (ctx.fail f dur))
    | .ok (.ok ()) =>
      if after == before then
        ctx.log.modify (·.push (ctx.pass dur))

/--
Expects the action to fail an assertion. The current scope passes if it does and fails if it
succeeds. An escaping {name}`IO.Error` is not an expected failure: it propagates and is reported as an
error, so broken setup is not mistaken for a passing negative test.
-/
def expectFail (act : TestM Unit) : TestM Unit := do
  try
    act
  catch _ =>
    return
  fail "expected the action to fail, but it passed"
