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
{name}`failure` fails the test at the context's location, and {lit}`<|>` recovers from an assertion
failure by running the alternative. An escaping {name}`IO.Error` still propagates, so {lit}`<|>` does
not mask a broken setup.
-/
instance : Alternative TestM where
  failure := failHere "failure"
  orElse x y := tryCatch x fun _ => y ()

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
def Context.mkResult (ctx : Context) (status : Status) (durationMs : Nat := 0) : Result where
  package := ctx.package
  moduleName := ctx.moduleName
  test := ctx.test
  resultPath := ctx.resultPath
  status
  durationMs
  description? := ctx.description?

/--
Builds the result for a test or named result that has just finished running.

{name}`outcome` is how its own code ended: an error, a failed assertion, or completion.
{name}`output` is what its own code printed. {name}`durationMs` is how long the whole run took, and
{name}`insideMs` is how much of that was spent in the named results it ran, {name}`recorded`.

The status is the worst of the code's own outcome and the statuses of the named results directly
below it: an error outranks a failure, which outranks a pass. The duration does not include that of
inner named results.
-/
def Context.resultOfOutcome (ctx : Context)
    (outcome : Except IO.Error (Except TestFailure Unit)) (output : OutputLog)
    (durationMs insideMs : Nat) (recorded : Array Result) : Result :=
  let below := recorded.filter (·.resultPath.size == ctx.resultPath.size + 1)
  let errors := below.countP (·.status matches .error _)
  let failures := below.countP (·.status matches .fail _)
  let count (n : Nat) (what : String) : String :=
    if n == 1 then s!"a named result {what}" else s!"{n} named results {what}"
  let status : Status :=
    match outcome with
    | .error e => .error (toString e)
    | .ok (.error f) => if errors > 0 then .error (count errors "raised an error") else .fail f
    | .ok (.ok ()) =>
      if errors > 0 then .error (count errors "raised an error")
      else if failures > 0 then
        .fail { message := count failures "did not pass", location? := some ctx.location }
      else .pass
  { ctx.mkResult status (durationMs - insideMs) with output }

/--
Splits bytes into a prefix ready to decode and a tail that is the start of an unfinished
{lit}`UTF-8` code point. Bytes that cannot be completed by any continuation go in the prefix, where
decoding reports them as invalid.
-/
private def splitUtf8Tail (bytes : ByteArray) : ByteArray × ByteArray := Id.run do
  -- A continuation byte sends the search one byte further back for its lead byte.
  for back in [1 : 4] do
    if back > bytes.size then break
    let i := bytes.size - back
    if h : bytes[i]!.IsUTF8FirstByte then
      if i + bytes[i]!.utf8ByteSize h > bytes.size then
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
  let write (bytes : ByteArray) : IO Unit := do
    let (ready, rest) := splitUtf8Tail ((← pending.get) ++ bytes)
    match String.fromUTF8? ready with
    | some s =>
      pending.set rest
      unless s.isEmpty do emit (mk s)
    | none =>
      pending.set .empty
      throw invalid
  let stream : IO.FS.Stream := {
    -- A flush partway through a code point is not an error: the partial sequence stays buffered
    -- for the write that completes it.
    flush := pure ()
    read := fun _ => pure .empty
    write
    getLine := pure ""
    -- Text goes through the byte pathway, so output mixed from `putStr` and raw writes is
    -- recorded in the order it was produced, and text interrupting an unfinished code point is
    -- reported as the malformed stream it is.
    putStr := fun s => write s.toUTF8
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

Output from tasks or subprocesses spawned by the test is not captured.
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
    if let some dest := ctx.writeOutput then
      unless ← ctx.outputFailed.get do
        try
          IO.withStdout real.stdout <| IO.withStderr real.stderr <| dest o
        catch e =>
          ctx.outputFailed.set true
          -- Saying so can fail in turn, when the destination that just failed was stderr itself.
          try real.stderr.putStr s!"warning: live output destination failed: {e}\n" catch _ => pure ()
  let (outStream, outClose) ← captureStream emit .stdout
  let (errStream, errClose) ← captureStream emit .stderr
  -- Closing inside the captured action makes dangling bytes at the end of the test an error of the
  -- test itself. When the test already failed, that failure is the report's verdict, and a
  -- dangling-byte error at close does not displace it.
  let body : IO (Except TestFailure Unit) := do
    let r ← (act ctx).run
    match r with
    | .ok () =>
      outClose
      errClose
    | .error _ =>
      try outClose; errClose catch _ => pure ()
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
Runs {name}`act` as a named result of the current test.

The name is added to the current result path, so nested named results have dotted names. A failure
in {name}`act` is recorded and does not stop the test, so the named results that follow still run.

The run produces one result for {name}`act` itself, followed by the results of any named results
inside it. Its status follows {name}`Context.resultOfOutcome`: an error if {name}`act` raised one, a
failure if it failed an assertion or one of its own named results did not pass, and a pass
otherwise. Its output and its duration are its own, leaving out what happened inside its named
results.
-/
def result (name : String) (act : TestM Unit) : TestM Unit := do
  let outer ← read
  let insideMs ← IO.mkRef 0
  -- The docstring belongs to the test's declaration, so a named result's scope has none.
  let dur ← withReader (fun c =>
      { c with resultPath := c.resultPath.push name, insideMs, description? := none }) do
    let ctx ← read
    let before := (← ctx.log.get).size
    let start ← IO.monoMsNow
    let (outcome, output) ← runCapturing ctx act
    let stop ← IO.monoMsNow
    let dur := stop - start
    let logged ← ctx.log.get
    let recorded := logged.extract before logged.size
    let own := ctx.resultOfOutcome outcome output dur (← insideMs.get) recorded
    ctx.log.set (logged.extract 0 before ++ #[own] ++ recorded)
    pure dur
  -- The enclosing scope's own time leaves out this block's whole duration.
  outer.insideMs.modify (· + dur)

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
  let logged ← ctx.log.get
  let added := logged.extract before logged.size
  let failedInside := added.any (·.status matches .fail _)
  let erroredInside := added.any (·.status matches .error _)
  ctx.log.set (logged.extract 0 before ++ added.filter (fun r => !(r.status matches .fail _)))
  unless threw || failedInside || erroredInside do
    failAt loc "expected the action to fail, but it passed"
