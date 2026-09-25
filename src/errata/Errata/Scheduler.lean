/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The runner's scheduler: a pure function from the scheduler's state and an event, such as a process
that ended, to the new state and the commands that the runner performs, such as starting a test.
It decides which test runs next, when each fixture's phases run, how many hardware threads each
process is granted, and when the run is over.
-/
module

public import Errata.Outcome
public import Std.Data.HashMap

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata.Scheduler

/-- A fixture, as the scheduler sees it. Fixtures are numbered by their positions in the run. -/
structure FixtureSpec where
  /-- The fixtures that this one takes, by their positions, each before this one. -/
  deps : Array Nat := #[]
  /-- The number of hardware threads that the fixture's phases ask for. -/
  threads : Nat := 1
  /-- The mandatory setting that has no value, when the fixture's setup cannot run without it. -/
  missing? : Option String := none
deriving Repr, Inhabited, DecidableEq

/-- A test, as the scheduler sees it. Tests are numbered by their positions in the queue. -/
structure TestSpec where
  /-- The fixtures that the test uses, by their positions, each exclusively or shared. -/
  fixtures : Array (Nat × Bool) := #[]
  /-- The number of hardware threads that the test asks for. -/
  threads : Nat := 1
  /-- The mandatory setting that has no value, when the test cannot run without it. -/
  missing? : Option String := none
deriving Repr, Inhabited, DecidableEq

/-- A unit of work that the runner runs in a process of its own. -/
inductive Job where
  /-- Runs a test. -/
  | test (test : Nat)
  /-- Runs a fixture's setup. -/
  | setup (fixture : Nat)
  /-- Runs a fixture's prepare before a test that uses it. -/
  | prepare (fixture : Nat) (test : Nat)
  /-- Runs a fixture's teardown. -/
  | teardown (fixture : Nat)
deriving Repr, Inhabited, DecidableEq, BEq, Hashable

/-- Why a test or a fixture's setup is reported without running. -/
inductive Skip where
  /-- A mandatory setting has no value. -/
  | settingMissing (setting : String)
  /-- A fixture that the test needs failed in the given phase. -/
  | fixtureFailed (fixture : Nat) (phase : FixturePhase)
deriving Repr, Inhabited, DecidableEq

/-- What the scheduler asks the runner to do. -/
inductive Command where
  /--
  Starts a job in a process of its own, granted {name}`grant` hardware threads, with the values of
  the fixtures that it receives, by their positions.
  -/
  | spawn (job : Job) (grant : Nat) (values : Array (Nat × String))
  /-- Reports a test, or a fixture's setup, as ended for the given reason, without a process. -/
  | skip (job : Job) (reason : Skip)
  /-- Ends the run: nothing is running, and nothing more will run. -/
  | finish
deriving Repr, Inhabited, DecidableEq

/-- Something that happened during a run. -/
inductive Event where
  /-- The run begins. -/
  | begin
  /-- A fixture's setup wrote its value. -/
  | valueProduced (fixture : Nat) (value : String)
  /-- A job's process ended, successfully or not. -/
  | exited (job : Job) (succeeded : Bool)
  /-- A job's process ran past its timeout and was stopped. -/
  | timedOut (job : Job)
  /--
  The run was cancelled: no test or prepare starts, the fixtures whose setups were invoked are torn
  down once their running users end, and then the run ends.
  -/
  | cancelled
deriving Repr, Inhabited, DecidableEq

/-- Where a test is in its run. -/
inductive TestStatus where
  /-- It has not started. -/
  | pending
  /-- It holds its claims, and the prepare of its fixture at this index in its list is running. -/
  | preparing (next : Nat)
  /-- Its process is running. -/
  | running
  /-- It has ended, or was reported without running. -/
  | done
deriving Repr, Inhabited, DecidableEq

/-- Where a fixture is in its run. -/
inductive FixtureStatus where
  /-- Its setup has not been invoked. -/
  | unset
  /-- Its setup is running. -/
  | settingUp
  /-- Its setup produced this value. -/
  | ready (value : String)
  /--
  It cannot serve its users: its own setup failed, or a fixture that it takes failed, as
  {name}`root` and {name}`phase` say. {name}`invoked` says whether its own setup was invoked.
  -/
  | failed (root : Nat) (phase : FixturePhase) (invoked : Bool)
  /-- Its teardown is running. -/
  | tearingDown
  /-- Its teardown has ended. -/
  | tornDown
deriving Repr, Inhabited, DecidableEq

/--
The scheduler's state. The pool is a number of slots, and each running job holds the slots of its
grant. Tests claim each fixture that they use, exclusively or shared, from their first prepare until
they end.
-/
structure State where
  /-- The number of hardware-thread slots in the pool. -/
  pool : Nat
  /-- The slots that no job holds. -/
  free : Nat
  /-- The tests, in queue order. -/
  tests : Array TestSpec
  /-- The fixtures, each after the fixtures it takes. -/
  fixtures : Array FixtureSpec
  /-- Each test's fixtures and the fixtures that they take, each after the fixtures it takes. -/
  closures : Array (Array Nat)
  /-- Each test's status. -/
  testStatus : Array TestStatus
  /--
  The slots that each test holds from its first prepare until it ends: until it starts, its
  reservation, the largest grant among its prepares and itself; from then on, its own grant.
  -/
  reserved : Array Nat
  /-- Each fixture's status. -/
  fixtureStatus : Array FixtureStatus
  /-- The value that each fixture's running setup has written so far. -/
  written : Array (Option String)
  /-- The number of unfinished tests whose closures include each fixture. -/
  openUsers : Array Nat
  /-- The test that holds each fixture exclusively, if one does. -/
  exclusiveHolder : Array (Option Nat)
  /-- The number of tests that hold each fixture shared. -/
  sharedHolders : Array Nat
  /-- The setups and teardowns that are running, with the slots each holds. -/
  fixtureJobs : Array (Job × Nat) := #[]
  /-- Whether the run was cancelled. -/
  cancelled : Bool := false
  /-- Whether the run has ended. -/
  finished : Bool := false
deriving Repr, Inhabited

/--
The grant for a request of {name}`n` threads: the request, at least one, and at most the pool.
-/
def State.grant (s : State) (n : Nat) : Nat := max 1 (min n s.pool)

/--
The fixtures in {name}`roots` and every fixture that they take, directly or through others, each
after the fixtures it takes.
-/
def closureOf (fixtures : Array FixtureSpec) (roots : Array Nat) : Array Nat := Id.run do
  let mut wanted : Std.HashMap Nat Unit := roots.foldl (init := {}) fun m f => m.insert f ()
  -- Each fixture's own fixtures come before it, so one pass from the last to the first reaches all.
  for i in (List.range fixtures.size).reverse do
    if wanted.contains i then
      for d in fixtures[i]!.deps do wanted := wanted.insert d ()
  return (List.range fixtures.size).toArray.filter wanted.contains

/-- The state at the start of a run with {name}`pool` slots, the tests, and the fixtures. -/
def State.init (pool : Nat) (tests : Array TestSpec) (fixtures : Array FixtureSpec) : State :=
  let pool := max pool 1
  let closures := tests.map fun t => closureOf fixtures (t.fixtures.map (·.1))
  let openUsers := closures.foldl (init := Array.replicate fixtures.size 0) fun acc c =>
    c.foldl (init := acc) fun acc f => acc.modify f (· + 1)
  { pool, free := pool, tests, fixtures, closures
    testStatus := Array.replicate tests.size .pending
    reserved := Array.replicate tests.size 0
    fixtureStatus := Array.replicate fixtures.size .unset
    written := Array.replicate fixtures.size none
    openUsers
    exclusiveHolder := Array.replicate fixtures.size none
    sharedHolders := Array.replicate fixtures.size 0 }

/-- The value of a fixture whose setup produced one. -/
def State.value? (s : State) (f : Nat) : Option String :=
  match s.fixtureStatus[f]? with
  | some (.ready v) => some v
  | _ => none

/-- Whether a fixture's setup was invoked. -/
def State.invoked (s : State) (f : Nat) : Bool :=
  match s.fixtureStatus[f]? with
  | some .unset | none => false
  | some (.failed _ _ invoked) => invoked
  | some _ => true

/-- The values of the given fixtures, by their positions, for those whose setups produced one. -/
def State.valuesOf (s : State) (fs : Array Nat) : Array (Nat × String) :=
  fs.filterMap fun f => (s.value? f).map (f, ·)

/-- The fixture's failure, when it cannot serve its users. -/
def State.failure? (s : State) (f : Nat) : Option (Nat × FixturePhase) :=
  match s.fixtureStatus[f]? with
  | some (.failed root phase _) => some (root, phase)
  | _ => none

/--
Marks a fixture as failed in a phase, and every fixture that takes it, directly or through others,
and has not been set up, as failed because of it.
-/
def State.failFixture (s : State) (f : Nat) (phase : FixturePhase) (invoked : Bool) : State :=
    Id.run do
  let mut s := { s with fixtureStatus := s.fixtureStatus.set! f (.failed f phase invoked) }
  -- Fixtures come after the fixtures they take, so one forward pass reaches every dependent.
  for g in [f + 1 : s.fixtures.size] do
    if s.fixtureStatus[g]! matches .unset then
      if s.fixtures[g]!.deps.any fun d => (s.failure? d).isSome then
        s := { s with fixtureStatus := s.fixtureStatus.set! g (.failed f phase false) }
  return s

/--
The slots that a test holds from its first prepare until it starts: the largest grant among its
prepares and itself. From its start to its end it holds its own grant.
-/
def State.reservation (s : State) (t : Nat) : Nat :=
  let test := s.tests[t]!
  test.fixtures.foldl (init := s.grant test.threads) fun r (f, _) =>
    max r (s.grant s.fixtures[f]!.threads)

/-- Ends a test: releases its claims and its slots, and counts it out of its fixtures' users. -/
def State.endTest (s : State) (t : Nat) : State := Id.run do
  let mut s := s
  let wasActive := !(s.testStatus[t]! matches .pending | .done)
  if wasActive then
    for (f, exclusive) in s.tests[t]!.fixtures do
      if exclusive then
        s := { s with exclusiveHolder := s.exclusiveHolder.set! f none }
      else
        s := { s with sharedHolders := s.sharedHolders.modify f (· - 1) }
    s := { s with free := s.free + s.reserved[t]!, reserved := s.reserved.set! t 0 }
  for f in s.closures[t]! do
    s := { s with openUsers := s.openUsers.modify f (· - 1) }
  return { s with testStatus := s.testStatus.set! t .done }

/--
The command that starts a test's next step: the prepare of its fixture at {name}`next`, or the test.
-/
def State.nextStep (s : State) (t : Nat) (next : Nat) : State × Command :=
  let test := s.tests[t]!
  match test.fixtures[next]? with
  | some (f, _) =>
    let values := s.valuesOf (#[f] ++ s.fixtures[f]!.deps)
    ({ s with testStatus := s.testStatus.set! t (.preparing next) },
      .spawn (.prepare f t) (s.grant s.fixtures[f]!.threads) values)
  | none =>
    -- The test keeps the slots of its own grant, and frees those that only its prepares needed.
    let keep := s.grant test.threads
    let held := s.reserved[t]!
    ({ s with
        testStatus := s.testStatus.set! t .running
        free := s.free + (held - keep), reserved := s.reserved.set! t (min held keep) },
      .spawn (.test t) keep (s.valuesOf (test.fixtures.map (·.1))))

/--
Whether a fixture's teardown may start: its setup was invoked, it has not been torn down, no
unfinished test needs it, and every invoked fixture that takes it has been torn down.
-/
def State.teardownReady (s : State) (f : Nat) : Bool :=
  let status := s.fixtureStatus[f]!
  let settled := match status with
    | .ready _ => true
    | .failed _ _ invoked => invoked
    | _ => false
  settled && s.openUsers[f]! == 0 &&
    (List.range s.fixtures.size).all fun g =>
      !(s.fixtures[g]!.deps.contains f) || !s.invoked g || s.fixtureStatus[g]! matches .tornDown

/-- Starts the teardowns that may start, as far as the free slots allow. -/
def State.startTeardowns (s : State) : State × Array Command := Id.run do
  let mut s := s
  let mut out := #[]
  for f in [0 : s.fixtures.size] do
    if s.teardownReady f then
      let grant := s.grant s.fixtures[f]!.threads
      if s.free ≥ grant then
        let values := (s.value? f |>.map fun v => #[(f, v)]).getD #[] ++
          s.valuesOf s.fixtures[f]!.deps
        s := { s with
          free := s.free - grant, fixtureStatus := s.fixtureStatus.set! f .tearingDown
          fixtureJobs := s.fixtureJobs.push (.teardown f, grant) }
        out := out.push (.spawn (.teardown f) grant values)
  return (s, out)

/--
Starts what may start, in queue order. Tests that are reported without running wait until every test
before them has ended, so reports keep the queue's order where the pool allows it. Tests start once
their fixtures are set up, their claims are free, and their slots are free: exclusive claims need
the fixture free of other users, and shared claims need it free of exclusive ones. Earlier waiting
tests go first: fixtures that one of them wants exclusively wait for it, and fixtures that one of
them wants at all wait for it before an exclusive claim, so the users of a fixture take it in queue
order. Once a job waits for slots, the jobs after it wait too, so large requests are served. Setups
start as their first users reach them, after the setups of the fixtures they take. Tests that a
failed fixture already dooms start no setups, so fixtures are set up only for users that can run.

Once the run is cancelled, the tests that have not started are dropped without a report, and every
fixture whose setup was invoked is torn down once its running users have ended.
-/
def State.fill (s : State) : State × Array Command := Id.run do
  if s.finished then return (s, #[])
  let mut s := s
  let mut out : Array Command := #[]
  if s.cancelled then
    for t in [0 : s.tests.size] do
      if s.testStatus[t]! matches .pending then s := s.endTest t
  else
    let (s', cmds) := s.startTeardowns
    s := s'
    out := out ++ cmds
    let mut earlierUnfinished := false
    let mut slotsBlocked := false
    -- For each fixture that an earlier test waits for, whether one of them wants it exclusively.
    let mut wanted : Std.HashMap Nat Bool := {}
    for t in [0 : s.tests.size] do
      unless s.testStatus[t]! matches .pending do
        unless s.testStatus[t]! matches .done do earlierUnfinished := true
        continue
      let test := s.tests[t]!
      if let some setting := test.missing? then
        if earlierUnfinished then continue
        s := s.endTest t
        out := out.push (.skip (.test t) (.settingMissing setting))
        continue
      -- Fixtures whose mandatory settings have no value fail at once, and doom their users.
      for f in s.closures[t]! do
        if s.fixtureStatus[f]! matches .unset then
          if let some setting := s.fixtures[f]!.missing? then
            s := s.failFixture f .setup false
            out := out.push (.skip (.setup f) (.settingMissing setting))
      if let some (root, phase) := s.closures[t]!.findSome? s.failure? then
        if earlierUnfinished then continue
        s := s.endTest t
        out := out.push (.skip (.test t) (.fixtureFailed root phase))
        continue
      -- The setups that the test waits for, each after the setups of the fixtures it takes.
      for f in s.closures[t]! do
        unless s.fixtureStatus[f]! matches .unset do continue
        unless s.fixtures[f]!.deps.all (s.value? · |>.isSome) do continue
        if !slotsBlocked then
          let grant := s.grant s.fixtures[f]!.threads
          if s.free ≥ grant then
            s := { s with
              free := s.free - grant, fixtureStatus := s.fixtureStatus.set! f .settingUp
              fixtureJobs := s.fixtureJobs.push (.setup f, grant) }
            out := out.push (.spawn (.setup f) grant (s.valuesOf s.fixtures[f]!.deps))
          else slotsBlocked := true
      let ready := s.closures[t]!.all (s.value? · |>.isSome)
      let claimable := test.fixtures.all fun (f, exclusive) =>
        if exclusive then
          s.exclusiveHolder[f]!.isNone && s.sharedHolders[f]! == 0 && !wanted.contains f
        else
          s.exclusiveHolder[f]!.isNone && wanted.get? f != some true
      let mut started := false
      if ready && claimable && !slotsBlocked then
        let r := s.reservation t
        if s.free ≥ r then
          for (f, exclusive) in test.fixtures do
            if exclusive then
              s := { s with exclusiveHolder := s.exclusiveHolder.set! f (some t) }
            else
              s := { s with sharedHolders := s.sharedHolders.modify f (· + 1) }
          s := { s with free := s.free - r, reserved := s.reserved.set! t r }
          let (s', cmd) := s.nextStep t 0
          s := s'
          out := out.push cmd
          started := true
        else slotsBlocked := true
      unless started do
        for (f, exclusive) in test.fixtures do
          wanted := wanted.insert f (exclusive || wanted.getD f false)
      earlierUnfinished := true
  -- Tests reported without running, or dropped, may have been the last users of their fixtures.
  let (s', cmds) := s.startTeardowns
  s := s'
  out := out ++ cmds
  let idle := s.fixtureJobs.isEmpty && s.testStatus.all fun
    | .pending | .done => true
    | _ => false
  let allDone := s.testStatus.all (· matches .done)
  let teardownsLeft := (List.range s.fixtures.size).any fun f =>
    s.invoked f && !(s.fixtureStatus[f]! matches .tornDown)
  if idle && allDone && !teardownsLeft then
    s := { s with finished := true }
    out := out.push .finish
  return (s, out)

/-- Releases the slots of a setup or teardown that ended. -/
def State.releaseFixtureJob (s : State) (job : Job) : State :=
  match s.fixtureJobs.findIdx? (·.1 == job) with
  | some i =>
    { s with free := s.free + s.fixtureJobs[i]!.2, fixtureJobs := s.fixtureJobs.eraseIdx! i }
  | none => s

/-- Takes in the end of a job's process: {name}`succeeded` is false for a failure or a timeout. -/
def State.ended (s : State) (job : Job) (succeeded : Bool) : State × Array Command :=
  match job with
  | .test t => (s.endTest t, #[])
  | .setup f =>
    let s := s.releaseFixtureJob job
    if succeeded then
      let value := s.written[f]!.getD ""
      ({ s with fixtureStatus := s.fixtureStatus.set! f (.ready value) }, #[])
    else (s.failFixture f .setup true, #[])
  | .prepare f t =>
    -- Cancelled runs start nothing more, so the test ends after its prepare.
    if s.cancelled then (s.endTest t, #[])
    else if succeeded then
      match s.testStatus[t]! with
      | .preparing next =>
        let (s, cmd) := s.nextStep t (next + 1)
        (s, #[cmd])
      | _ => (s, #[])
    else
      (s.endTest t, #[.skip (.test t) (.fixtureFailed f .prepare)])
  | .teardown f =>
    let s := s.releaseFixtureJob job
    ({ s with fixtureStatus := s.fixtureStatus.set! f .tornDown }, #[])

/--
Handles one event: the new state, and the commands that the runner performs, in order. After
every event the scheduler starts what may start, and ends the run once nothing runs and nothing is
left.
-/
def step (s : State) : Event → State × Array Command
  | .begin => s.fill
  | .valueProduced f value => ({ s with written := s.written.set! f (some value) }, #[])
  | .exited job succeeded =>
    let (s, cmds) := s.ended job succeeded
    let (s, more) := s.fill
    (s, cmds ++ more)
  | .timedOut job =>
    let (s, cmds) := s.ended job false
    let (s, more) := s.fill
    (s, cmds ++ more)
  | .cancelled =>
    let s := { s with cancelled := true }
    s.fill

end Errata.Scheduler
