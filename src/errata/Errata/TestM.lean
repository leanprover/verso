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
{lit}`failure` fails the test at the context's location, and {lit}`<|>` recovers from an assertion
failure by running the alternative. An escaping {name}`IO.Error` still propagates, so {lit}`<|>` does
not mask a broken setup.
-/
instance : Alternative TestM where
  failure := failHere "failure"
  orElse x y := tryCatch x fun _ => y ()

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
def Context.mkResult (ctx : Context) (status : Status) (durationMs : Nat := 0) : Result := {
  package := ctx.package, moduleName := ctx.moduleName, test := ctx.test,
  resultPath := ctx.resultPath, status, durationMs, description? := ctx.description?
}

/-- A passing result for the current scope. -/
def Context.pass (ctx : Context) (durationMs : Nat := 0) : Result :=
  ctx.mkResult .pass durationMs

/-- A failed result for the current scope. -/
def Context.fail (ctx : Context) (failure : TestFailure) (durationMs : Nat := 0) : Result :=
  ctx.mkResult (.fail failure) durationMs

/-- A result for the current scope that raised an error. -/
def Context.error (ctx : Context) (message : String) (durationMs : Nat := 0) : Result :=
  ctx.mkResult (.error message) durationMs

/-- A skipped result for the current scope. -/
def Context.skip (ctx : Context) (reason : String) (durationMs : Nat := 0) : Result :=
  ctx.mkResult (.skip reason) durationMs

/--
The result a captured run contributes beyond any nested results it recorded.

A raised error or a failed assertion becomes one error or failed result carrying the captured output.
A clean run becomes one passing result with the output when it recorded no nested results; when it did
record some, those results stand for it and it adds nothing of its own.
-/
def Context.resultOfOutcome (ctx : Context)
    (outcome : Except IO.Error (Except TestFailure Unit)) (output : OutputLog) (durationMs : Nat)
    (hasNested : Bool) : Option Result :=
  match outcome with
  | .error e => some { ctx.error (toString e) durationMs with output }
  | .ok (.error f) => some { ctx.fail f durationMs with output }
  | .ok (.ok ()) => if hasNested then none else some { ctx.pass durationMs with output }

/-- Records a skipped result for the current scope. -/
def skip (reason : String) : TestM Unit := do
  let ctx ← read
  ctx.log.modify (·.push (ctx.skip reason))

/-- Writes a file, creating all parent directories if necessary. -/
def writeFile (path : System.FilePath) (contents : String) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path contents

/-- Writes a binary file, creating all parent directories if necessary. -/
def writeBinFile (path : System.FilePath) (contents : ByteArray) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeBinFile path contents

/--
The number of bytes in the {lit}`UTF-8` sequence a lead byte introduces, or {name}`none` for a
continuation or invalid byte.
-/
private def utf8SeqLength (b : UInt8) : Option Nat :=
  if b &&& 0x80 == 0 then some 1
  else if b &&& 0xE0 == 0xC0 then some 2
  else if b &&& 0xF0 == 0xE0 then some 3
  else if b &&& 0xF8 == 0xF0 then some 4
  else none

/--
Splits bytes into a prefix ready to decode and a tail that is the start of an unfinished
{lit}`UTF-8` code point. Bytes that cannot be completed by any continuation go in the prefix, where
decoding reports them as invalid.
-/
private def splitUtf8Tail (bytes : ByteArray) : ByteArray × ByteArray := Id.run do
  for back in [1 : 4] do
    if back > bytes.size then break
    let i := bytes.size - back
    if let some len := utf8SeqLength bytes[i]! then
      if i + len > bytes.size then
        return (bytes.extract 0 i, bytes.extract i bytes.size)
      else
        break
  return (bytes, .empty)

/--
A stream that hands each write to a destination as a fragment tagged by the stream it came from.

A write of raw bytes may end partway through a {lit}`UTF-8` code point; the trailing bytes wait in a
buffer for the write that completes them. Bytes that decode to nothing valid are rejected. The
returned action ends the capture, rejecting any buffered bytes whose code point never arrived.
-/
private def captureStream (emit : Output → IO Unit) (mk : String → Output) :
    IO (IO.FS.Stream × IO Unit) := do
  let pending ← IO.mkRef ByteArray.empty
  let invalid : IO.Error :=
    .userError "a raw byte write to a captured stream was not valid UTF-8"
  let stream : IO.FS.Stream := {
    flush := pure ()
    read := fun _ => pure .empty
    write := fun bytes => do
      let (ready, rest) := splitUtf8Tail ((← pending.get) ++ bytes)
      match String.fromUTF8? ready with
      | some s =>
        pending.set rest
        unless s.isEmpty do emit (mk s)
      | none =>
        pending.set .empty
        throw invalid
    getLine := pure ""
    putStr := fun s => emit (mk s)
    isTty := pure false
  }
  let close : IO Unit := do
    unless (← pending.get).isEmpty do
      pending.set .empty
      throw invalid
  return (stream, close)

/--
Runs a test action with the given context, capturing its outcome as data rather than letting it
propagate. The action's stdout and stderr are recorded as text, in order and tagged by stream, and
returned alongside the outcome. Each fragment is also handed to the context's output destination as
it is written, so a live runner can stream output while the test runs.
-/
def runCapturing (ctx : Context) (act : TestM Unit) :
    IO (Except IO.Error (Except TestFailure Unit) × OutputLog) := do
  let log ← IO.mkRef (#[] : Array Output)
  -- The destination runs with the streams from before the outermost capture, so writing to stdout
  -- from it reaches the runner instead of re-entering a capture at any level.
  let real ←
    match ctx.realStreams? with
    | some streams => pure streams
    | none => do pure { stdout := ← IO.getStdout, stderr := ← IO.getStderr : RealStreams }
  let ctx := { ctx with realStreams? := some real }
  let emit (o : Output) : IO Unit := do
    log.modify (·.push o)
    unless ← ctx.outputFailed.get do
      try
        IO.withStdout real.stdout <| IO.withStderr real.stderr <| ctx.writeOutput o
      catch e =>
        ctx.outputFailed.set true
        -- Saying so can fail in turn, when the destination that just failed was stderr itself.
        try real.stderr.putStr s!"warning: live output destination failed: {e}\n" catch _ => pure ()
  let (outStream, outClose) ← captureStream emit .stdout
  let (errStream, errClose) ← captureStream emit .stderr
  -- Closing inside the captured action makes dangling bytes at the end of the test an error of the
  -- test itself.
  let body : IO (Except TestFailure Unit) := do
    let r ← (act ctx).run
    outClose
    errClose
    return r
  let outcome ← IO.withStdout outStream <| IO.withStderr errStream <| body.toBaseIO
  return (outcome, { log := ← log.get })

/--
Runs an action with stdout and stderr captured into a fresh log, then returns the captured text in
order. The redirection is local to the action, so a test can make assertions about what the action
wrote.
-/
def captureOutput (act : TestM Unit) : TestM OutputLog := do
  let log ← IO.mkRef (#[] : Array Output)
  let emit (o : Output) : IO Unit := log.modify (·.push o)
  let completed ← IO.mkRef false
  let (outStream, outClose) ← captureStream emit .stdout
  let (errStream, errClose) ← captureStream emit .stderr
  try
    IO.withStdout outStream <| IO.withStderr errStream do
      act
      outClose
      errClose
    completed.set true
  finally
    -- An action that does not complete never receives this log, and what it wrote is what explains
    -- the failure, so the fragments are handed to the enclosing capture instead.
    unless ← completed.get do
      for o in ← log.get do
        match o with
        | .stdout s => IO.print s
        | .stderr s => IO.eprint s
  return { log := ← log.get }

/--
Runs a named result within the current test.

Its path extends the current path, and its failure is isolated from sibling results. If the action
records no nested results and completes, it contributes one passing result; if it throws, it
contributes one failed result or one that raised an error.
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
    if let some r := ctx.resultOfOutcome outcome output dur (after != before) then
      ctx.log.modify (·.push r)

/--
Expects the action to fail an assertion. The current scope passes if it does and fails if it
succeeds. An escaping {name}`IO.Error` is not an expected failure: it propagates and is reported as an
error, so broken setup is not mistaken for a passing negative test.
-/
def expectFail (act : TestM Unit) (loc : Location := by exact here%) : TestM Unit := do
  let ctx ← read
  let before := (← ctx.log.get).size
  let threw ←
    try
      act
      pure false
    catch _ =>
      pure true
  -- A nested `result` records a failure rather than propagating it, so the results the action
  -- recorded are inspected too. Their failures are the expected failure and are dropped.
  -- Everything else is retained because a recorded error is a broken setup rather than a failure.
  let logged ← ctx.log.get
  let added := logged.extract before logged.size
  let failedInside := added.any (·.status matches .fail _)
  ctx.log.set (logged.extract 0 before ++ added.filter (fun r => !(r.status matches .fail _)))
  unless threw || failedInside do
    failAt loc "expected the action to fail, but it passed"
