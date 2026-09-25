/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Property tests of the runner's scheduler. A simulation drives the pure scheduler through a random
run: random tests and fixtures, claims, fixture dependencies, thread requests, pool sizes, durations,
failures, and cancellations. It checks every command against the rules the scheduler promises.
-/
module

public import Errata

open Errata
open Errata.Scheduler

public section

namespace ErrataTests.Scheduling

/-- A number drawn from the scenario's seed for the given key, below {name}`bound`. -/
def draw (seed : UInt64) (key : List Nat) (bound : Nat) : Nat :=
  let h := key.foldl (fun h k => mixHash h (hash k)) (mixHash seed 7919)
  if bound == 0 then 0 else h.toNat % bound

/-- Whether a draw with the given key succeeds, with probability one in {name}`n`. -/
def chance (seed : UInt64) (key : List Nat) (n : Nat) : Bool :=
  draw seed key n == 0

/-- A random run: its pool, its tests and fixtures, and how each job behaves. -/
structure Scenario where
  /-- The scenario's seed, from which each job's duration and outcome are drawn. -/
  seed : UInt64
  /-- The number of slots. -/
  pool : Nat
  /-- The tests. -/
  tests : Array TestSpec
  /-- The fixtures. -/
  fixtures : Array FixtureSpec
  /-- The time at which the run is cancelled, if it is. -/
  cancelAt? : Option Nat
deriving Repr

/-- The key of a job, for the draws of its duration and its outcome. -/
def jobKey : Job → List Nat
  | .test t => [1, t]
  | .setup f => [2, f]
  | .prepare f t => [3, f, t]
  | .teardown f => [4, f]

/-- How long a job runs in the scenario. -/
def Scenario.duration (sc : Scenario) (job : Job) : Nat :=
  draw sc.seed (0 :: jobKey job) 9

/-- How a job ends in the scenario: {lit}`0` succeeds, {lit}`1` fails, and {lit}`2` times out. -/
def Scenario.ending (sc : Scenario) (job : Job) : Nat :=
  match job with
  | .test _ => draw sc.seed (5 :: jobKey job) 3
  | _ => if chance sc.seed (6 :: jobKey job) 5 then 1 + draw sc.seed (8 :: jobKey job) 2 else 0

/-- A random scenario from a seed. -/
def scenario (seed : UInt64) : Scenario := Id.run do
  let pool := 1 + draw seed [10] 4
  let fixtureCount := draw seed [11] 5
  let mut fixtures := #[]
  for f in [0 : fixtureCount] do
    let deps := (List.range f).toArray.filter fun d => chance seed [12, f, d] 3
    let threads := 1 + draw seed [13, f] (pool + 1)
    let missing? := if chance seed [14, f] 9 then some s!"setting{f}" else none
    fixtures := fixtures.push { deps, threads, missing? }
  let testCount := 1 + draw seed [15] 9
  let mut tests := #[]
  for t in [0 : testCount] do
    let uses := (List.range fixtureCount).toArray.filterMap fun f =>
      if chance seed [16, t, f] 2 then some (f, !chance seed [17, t, f] 2) else none
    let threads := 1 + draw seed [18, t] (pool + 2)
    let missing? := if chance seed [19, t] 10 then some s!"testSetting{t}" else none
    tests := tests.push { fixtures := uses, threads, missing? }
  let cancelAt? := if chance seed [20] 8 then some (draw seed [21] 30) else none
  return { seed, pool, tests, fixtures, cancelAt? }

/-- What the simulation has seen so far. -/
structure Sim where
  /-- The scheduler's state. -/
  state : State
  /-- The simulated time. -/
  now : Nat := 0
  /-- The running jobs, each with its end time, its grant, and how it ends. -/
  running : Array (Job × Nat × Nat × Nat) := #[]
  /-- The tests that hold claims. -/
  holding : Array Nat := #[]
  /-- For each fixture, the last test that claimed it exclusively. -/
  lastExclusive : Array (Option Nat) := #[]
  /-- The prepares that ended successfully, each a fixture and a test. -/
  prepared : Array (Nat × Nat) := #[]
  /-- The fixtures whose teardowns have started. -/
  teardownStarted : Array Bool := #[]
  /-- The number of times each test was started or reported without running. -/
  outcomes : Array Nat
  /-- The fixtures whose setups ended successfully. -/
  setUp : Array Bool
  /-- The number of times each fixture's setup started. -/
  setups : Array Nat
  /-- The number of times each fixture's teardown started. -/
  teardowns : Array Nat
  /-- The fixtures whose teardowns have ended. -/
  tornDown : Array Bool
  /-- The fixtures whose setups failed. -/
  failedSetups : Array Nat := #[]
  /-- The prepares that failed, each a fixture and a test. -/
  failedPrepares : Array (Nat × Nat) := #[]
  /-- The tests that have ended or were reported without running. -/
  ended : Array Bool
  /-- Whether the run was cancelled. -/
  cancelled : Bool := false
  /-- Whether the run has finished. -/
  finished : Bool := false
  /-- The rules that the commands broke. -/
  violations : Array String := #[]

/-- The fixtures that a test needs, directly or through the fixtures that its fixtures take. -/
def Sim.closure (s : Sim) (t : Nat) : Array Nat :=
  closureOf s.state.fixtures (s.state.tests[t]!.fixtures.map (·.1))

/-- Records a broken rule. -/
def Sim.violate (s : Sim) (msg : String) : Sim :=
  { s with violations := s.violations.push s!"at {s.now}: {msg}" }

/-- The slots that the running processes hold. -/
def Sim.slotsInUse (s : Sim) : Nat := s.running.foldl (· + ·.2.2.1) 0

/--
Checks that a test may claim its fixtures now, and that it claims each fixture it uses exclusively
after the earlier tests that do, and records its claim.
-/
def Sim.claim (s : Sim) (t : Nat) : Sim := Id.run do
  let mut s := s
  for (f, exclusive) in s.state.tests[t]!.fixtures do
    for u in s.holding do
      for (g, other) in s.state.tests[u]!.fixtures do
        if g == f && (exclusive || other) then
          s := s.violate s!"test {t} claims fixture {f} while test {u} holds it"
    if exclusive then
      if let some u := s.lastExclusive[f]! then
        if u > t then s := s.violate s!"test {t} claims fixture {f} after test {u}, a later one"
      s := { s with lastExclusive := s.lastExclusive.set! f (some t) }
  return { s with holding := s.holding.push t }

/-- Checks that no fixture that a job needs has begun its teardown. -/
def Sim.notTornDown (s : Sim) (job : Job) (fs : Array Nat) : Sim :=
  fs.foldl (init := s) fun s f =>
    if s.teardownStarted[f]! then s.violate s!"{repr job} started after fixture {f}'s teardown"
    else s

/-- Ends a test's claim. -/
def Sim.release (s : Sim) (t : Nat) : Sim :=
  { s with holding := s.holding.filter (· != t), ended := s.ended.set! t true }

/-- The number of threads that a job asks for. -/
def Sim.request (s : Sim) : Job → Nat
  | .test t => s.state.tests[t]!.threads
  | .setup f | .prepare f _ | .teardown f => s.state.fixtures[f]!.threads

/-- Checks a command against the rules and performs it in the simulation. -/
def Sim.perform (sc : Scenario) (s : Sim) (cmd : Command) : Sim := Id.run do
  let mut s := s
  if s.finished then return s.violate s!"a command after the end: {repr cmd}"
  match cmd with
  | .finish =>
    unless s.running.isEmpty do s := s.violate "the run ended while jobs ran"
    return { s with finished := true }
  | .skip job reason =>
    match job, reason with
    | .test t, .settingMissing _ =>
      if s.state.tests[t]!.missing?.isNone then s := s.violate s!"test {t} reported missing a setting"
      s := { s with outcomes := s.outcomes.modify t (· + 1) }
      s := s.release t
    | .test t, .fixtureFailed f phase =>
      unless (s.closure t).contains f do s := s.violate s!"test {t} blamed fixture {f}, which it lacks"
      let failed := match phase with
        | .setup => s.failedSetups.contains f || s.state.fixtures[f]!.missing?.isSome
        | .prepare => s.failedPrepares.contains (f, t)
        | .teardown => false
      unless failed do s := s.violate s!"test {t} blamed fixture {f} in {phase.name}"
      s := { s with outcomes := s.outcomes.modify t (· + 1) }
      s := s.release t
    | .setup f, .settingMissing _ =>
      if s.state.fixtures[f]!.missing?.isNone then
        s := s.violate s!"fixture {f} reported missing a setting"
    | _, _ => s := s.violate s!"an unexpected report: {repr cmd}"
    return s
  | .spawn job grant values =>
    if s.cancelled && !(job matches .teardown _) then
      s := s.violate s!"a job started after the cancellation: {repr job}"
    let request := s.request job
    unless grant == max 1 (min request sc.pool) do
      s := s.violate s!"{repr job} asked for {request} threads and was granted {grant}"
    if s.slotsInUse + grant > sc.pool then
      s := s.violate s!"{repr job} needs {grant} slots and {s.slotsInUse} of {sc.pool} are in use"
    let needsValues (fs : Array Nat) : Sim → Sim := fun s => fs.foldl (init := s) fun s f =>
      if !s.setUp[f]! then s.violate s!"{repr job} started before the setup of fixture {f} ended"
      else if !values.any (·.1 == f) then s.violate s!"{repr job} lacks the value of fixture {f}"
      else s
    match job with
    | .test t =>
      s := { s with outcomes := s.outcomes.modify t (· + 1) }
      if s.state.tests[t]!.fixtures.isEmpty then s := s.claim t
      for f in s.closure t do
        unless s.setUp[f]! do s := s.violate s!"test {t} started before the setup of fixture {f}"
      s := needsValues (s.state.tests[t]!.fixtures.map (·.1)) s
      for (f, _) in s.state.tests[t]!.fixtures do
        if s.failedPrepares.contains (f, t) then
          s := s.violate s!"test {t} started after its prepare of fixture {f} failed"
        unless s.prepared.contains (f, t) do
          s := s.violate s!"test {t} started before its prepare of fixture {f} ended"
      s := s.notTornDown job (s.closure t)
      unless s.holding.contains t do s := s.violate s!"test {t} started without its claims"
    | .setup f =>
      s := { s with setups := s.setups.modify f (· + 1) }
      s := needsValues s.state.fixtures[f]!.deps s
      s := s.notTornDown job (closureOf s.state.fixtures #[f])
    | .prepare f t =>
      if s.state.tests[t]!.fixtures[0]?.map (·.1) == some f then s := s.claim t
      s := needsValues #[f] s
      s := s.notTornDown job (s.closure t)
      unless s.holding.contains t do s := s.violate s!"the prepare of {f} for {t} ran unclaimed"
    | .teardown f =>
      s := { s with teardowns := s.teardowns.modify f (· + 1)
                    teardownStarted := s.teardownStarted.set! f true }
      if s.setups[f]! == 0 then s := s.violate s!"fixture {f} torn down without a setup"
      for t in s.holding do
        if (s.closure t).contains f then
          s := s.violate s!"fixture {f} torn down before test {t} ended"
      for g in [0 : s.state.fixtures.size] do
        if s.state.fixtures[g]!.deps.contains f && s.setups[g]! > 0 && !s.tornDown[g]! then
          s := s.violate s!"fixture {f} torn down before fixture {g}, which takes it"
    let ending := sc.ending job
    return { s with running := s.running.push (job, s.now + sc.duration job, grant, ending) }

/-- Performs the commands in order. -/
def Sim.performAll (sc : Scenario) (s : Sim) (cmds : Array Command) : Sim :=
  cmds.foldl (Sim.perform sc) s

/-- Feeds an event to the scheduler and performs its commands. -/
def Sim.feed (sc : Scenario) (s : Sim) (ev : Event) : Sim :=
  let (state, cmds) := step s.state ev
  Sim.performAll sc { s with state } cmds

/-- Ends the running job that ends first, and tells the scheduler. -/
def Sim.advance (sc : Scenario) (s : Sim) : Sim := Id.run do
  let some i := (List.range s.running.size).foldl (init := none) fun best i =>
      match best with
      | none => some i
      | some b => if s.running[i]!.2.1 < s.running[b]!.2.1 then some i else best
    | return s
  let (job, stop, _, ending) := s.running[i]!
  let mut s := { s with running := s.running.eraseIdx! i, now := stop }
  if let some cancelTime := sc.cancelAt? then
    if !s.cancelled && cancelTime ≤ stop then
      s := { s with cancelled := true }
      s := Sim.feed sc s .cancelled
  let succeeded := ending == 0
  match job with
  | .test t => s := s.release t
  | .setup f =>
    if succeeded then s := { s with setUp := s.setUp.set! f true }
    else s := { s with failedSetups := s.failedSetups.push f }
  | .prepare f t =>
    if succeeded then s := { s with prepared := s.prepared.push (f, t) }
    else s := { s with failedPrepares := s.failedPrepares.push (f, t) }
    -- If a prepare ends after the cancellation, its test ends too and runs no more.
    if s.cancelled then s := s.release t
  | .teardown f => s := { s with tornDown := s.tornDown.set! f true }
  if succeeded then
    if let .setup f := job then s := Sim.feed sc s (.valueProduced f s!"value {f}")
  let ev : Event := if ending == 2 then .timedOut job else .exited job succeeded
  -- If a prepare failed, its test's claim ends, and the scheduler reports the test as a skip.
  return Sim.feed sc s ev

/-- Runs the simulation until the run ends, the scheduler stalls, or a bound is reached. -/
partial def Sim.run (sc : Scenario) (s : Sim) (steps : Nat := 0) : Sim :=
  if s.finished then s
  else if s.running.isEmpty then s.violate "the scheduler stalled with nothing running"
  else if steps > 10000 then s.violate "the run did not end"
  else Sim.run sc (Sim.advance sc s) (steps + 1)

/-- The rules that a scenario's run breaks, including those checked once it has ended. -/
def violations (seed : UInt64) : List String := Id.run do
  let sc := scenario seed
  let state := State.init sc.pool sc.tests sc.fixtures
  let n := sc.tests.size
  let m := sc.fixtures.size
  let s : Sim := {
    state, outcomes := Array.replicate n 0, setUp := Array.replicate m false
    setups := Array.replicate m 0, teardowns := Array.replicate m 0
    tornDown := Array.replicate m false, ended := Array.replicate n false
    lastExclusive := Array.replicate m none, teardownStarted := Array.replicate m false }
  let mut s := Sim.run sc (Sim.feed sc s .begin)
  unless s.finished do s := s.violate "the run did not finish"
  for t in [0 : n] do
    if s.outcomes[t]! > 1 then s := s.violate s!"test {t} was scheduled {s.outcomes[t]!} times"
    if !s.cancelled && s.outcomes[t]! == 0 then
      s := s.violate s!"test {t} was never scheduled"
  for f in [0 : m] do
    if s.setups[f]! > 1 then s := s.violate s!"fixture {f} was set up {s.setups[f]!} times"
    if s.teardowns[f]! > 1 then s := s.violate s!"fixture {f} was torn down {s.teardowns[f]!} times"
    if s.setups[f]! == 1 && s.teardowns[f]! == 0 then
      s := s.violate s!"fixture {f} was set up and never torn down"
  return s.violations.toList

/--
The scheduler keeps its rules in random runs, cancelled ones and jobs that take no time included:
no two exclusive users of a fixture overlap, no shared user overlaps an exclusive one, and exclusive
users claim a fixture in queue order; the slots in use never exceed the pool, and each grant is the
request or the whole pool; each test is scheduled once or reported without running, unless the run
is cancelled first, and runs after its prepares; setups end before their fixtures' users and the
setups of the fixtures that take them begin; teardowns run once whenever the setup ran, cancelled
runs included, after the last user and after the teardowns of the fixtures that take them, and
nothing that needs a fixture starts after its teardown; and the run ends.
-/
@[test]
def schedulerKeepsItsRules : seed → Test :=
  property (∀ a b : Nat, violations (mixHash (hash a) (hash b)) = [])

/-- Two shared users of one fixture run at the same time when the pool allows it. -/
@[test]
def sharedUsersOverlap : Test := do
  let tests : Array TestSpec := #[{ fixtures := #[(0, false)] }, { fixtures := #[(0, false)] }]
  let s := State.init 2 tests #[{}]
  let (s, cmds) := step s .begin
  assertBEq #[Command.spawn (.setup 0) 1 #[]] cmds
  let (s, _) := step s (.valueProduced 0 "v")
  let (_, cmds) := step s (.exited (.setup 0) true)
  assertBEq #[Command.spawn (.prepare 0 0) 1 #[(0, "v")], .spawn (.prepare 0 1) 1 #[(0, "v")]] cmds

/--
A test holds its prepare's grant while the prepare runs and its own grant while it runs, so the
slots that only the prepare needed serve the next test at once.
-/
@[test]
def testsHoldTheirOwnGrantWhileTheyRun : Test := do
  let tests : Array TestSpec := #[{ fixtures := #[(0, false)] }, { fixtures := #[(0, false)] }]
  let s := State.init 5 tests #[{ threads := 4 }]
  let (s, _) := step s .begin
  let (s, cmds) := step s (.exited (.setup 0) true)
  assertBEq #[Command.spawn (.prepare 0 0) 4 #[(0, "")]] cmds
  let (s, cmds) := step s (.exited (.prepare 0 0) true)
  assertBEq #[Command.spawn (.test 0) 1 #[(0, "")], .spawn (.prepare 0 1) 4 #[(0, "")]] cmds
  let (s, _) := step s (.exited (.test 0) true)
  let (_, cmds) := step s (.exited (.prepare 0 1) true)
  assertBEq #[Command.spawn (.test 1) 1 #[(0, "")]] cmds

/-- Two exclusive users of one fixture run one after the other, in queue order. -/
@[test]
def exclusiveUsersTakeTurns : Test := do
  let tests : Array TestSpec := #[{ fixtures := #[(0, true)] }, { fixtures := #[(0, true)] }]
  let s := State.init 4 tests #[{}]
  let (s, _) := step s .begin
  let (s, cmds) := step s (.exited (.setup 0) true)
  assertBEq #[Command.spawn (.prepare 0 0) 1 #[(0, "")]] cmds
  let (s, cmds) := step s (.exited (.prepare 0 0) true)
  assertBEq #[Command.spawn (.test 0) 1 #[(0, "")]] cmds
  let (s, cmds) := step s (.exited (.test 0) true)
  assertBEq #[Command.spawn (.prepare 0 1) 1 #[(0, "")]] cmds
  let (s, _) := step s (.exited (.prepare 0 1) true)
  let (s, cmds) := step s (.exited (.test 1) true)
  assertBEq #[Command.spawn (.teardown 0) 1 #[(0, "")]] cmds
  let (_, cmds) := step s (.exited (.teardown 0) true)
  assertBEq #[Command.finish] cmds

/-- Requests larger than the pool are granted the whole pool and run alone. -/
@[test]
def oversizeRequestsRunAlone : Test := do
  let tests : Array TestSpec := #[{}, { threads := 9 }, {}]
  let s := State.init 3 tests #[]
  let (s, cmds) := step s .begin
  assertBEq #[Command.spawn (.test 0) 1 #[]] cmds
  let (s, cmds) := step s (.exited (.test 0) true)
  assertBEq #[Command.spawn (.test 1) 3 #[]] cmds
  let (_, cmds) := step s (.exited (.test 1) true)
  assertBEq #[Command.spawn (.test 2) 1 #[]] cmds

/--
If a setup fails, its fixture's users are reported as inconclusive without running, and its teardown
still runs, without a value.
-/
@[test]
def failedSetupStopsUsers : Test := do
  let tests : Array TestSpec := #[{ fixtures := #[(0, true)] }, {}]
  let s := State.init 1 tests #[{}]
  let (s, _) := step s .begin
  let (s, cmds) := step s (.timedOut (.setup 0))
  assertBEq #[Command.skip (.test 0) (.fixtureFailed 0 .setup), .spawn (.test 1) 1 #[]] cmds
  let (s, cmds) := step s (.exited (.test 1) true)
  assertBEq #[Command.spawn (.teardown 0) 1 #[]] cmds
  let (_, cmds) := step s (.exited (.teardown 0) false)
  assertBEq #[Command.finish] cmds

/--
Cancelled runs start no more tests, and tear down each fixture whose setup ran once its running
users end.
-/
@[test]
def cancelledRunTearsDown : Test := do
  let tests : Array TestSpec := #[{ fixtures := #[(0, true)] }, { fixtures := #[(0, true)] }]
  let s := State.init 2 tests #[{}]
  let (s, _) := step s .begin
  let (s, _) := step s (.valueProduced 0 "v")
  let (s, _) := step s (.exited (.setup 0) true)
  let (s, _) := step s (.exited (.prepare 0 0) true)
  let (s, cmds) := step s .cancelled
  assertBEq #[] cmds
  let (s, cmds) := step s (.exited (.test 0) false)
  assertBEq #[Command.spawn (.teardown 0) 1 #[(0, "v")]] cmds
  let (_, cmds) := step s (.exited (.teardown 0) true)
  assertBEq #[Command.finish] cmds

/-- Tests that a failed fixture dooms start no setups of their other fixtures. -/
@[test]
def doomedTestsSetNothingUp : Test := do
  let s := State.init 1 #[{ fixtures := #[(0, true), (1, true)] }] #[{}, {}]
  let (s, cmds) := step s .begin
  assertBEq #[Command.spawn (.setup 0) 1 #[]] cmds
  let (_, cmds) := step s (.exited (.setup 0) false)
  assertBEq #[Command.skip (.test 0) (.fixtureFailed 0 .setup), .spawn (.teardown 0) 1 #[]] cmds

/-- Tests that receive a setting with another value than their fixtures did draw a warning. -/
@[test]
def settingConflictsWarn : Test := do
  let plan : Runner.Plan := {
    pool := 1
    tests := #[({ exeIdx := 0, name := "t" }, { settings := #[("g", "override")] })]
    fixtures := #[(0, { name := "F" }, { settings := #[("g", "profile")] })]
    testSpecs := #[{ fixtures := #[(0, true)] }], fixtureSpecs := #[{}] }
  assertBEq #["the test t receives the setting g as \"override\", and its fixture F received it as \
    \"profile\""] plan.settingConflicts

end ErrataTests.Scheduling
