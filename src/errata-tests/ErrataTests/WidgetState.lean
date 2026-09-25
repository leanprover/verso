/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Tests of a run as the editor widget's server follows it: the transitions of its phase, taken in
every order, and the display that the runner's events file gives.
-/
module

public import Errata
import ErrataTests.Conformance

open Errata Errata.Widget
open Lean (Json)

public section

namespace ErrataTests.WidgetState

/-- One change of each kind. The kill that {lit}`arm` records is {lean}`(pure () : IO Unit)`. -/
def changes : Array (String × Change) := #[
  ("locked", .locked 1), ("listed", .listed 5), ("execStart", .execStart 7),
  ("output", .output { stream := .stdout, text := "x" }), ("result", .result { id := 1 }),
  ("step", .step { fixture := "f", status := "pass" }),
  ("issue", .issue { level := "warning", message := "w" }),
  ("outcome", .outcome { status := "pass" }), ("ended", .ended),
  ("finish", .finish { status := "error" }), ("cancel", .cancel), ("arm", .arm (pure ())),
  ("exited", .exited)]

/-- The sizes of what a run has collected, which only a live run adds to. -/
def sizesOf (d : RunData) : List Nat :=
  [d.chunks.size, d.results.size, d.steps.size, d.issues.size, d.execStartTime, d.buildMs]

/--
What is wrong with the transition from {name}`d` by the change named {name}`name`, if anything.

 * A run that is over stays as it is.
 * The driver's exit clears the kill and changes nothing else.
 * A cancel applies to a live run whose driver is still running, and its action is the kill that
   the run holds.
 * A run ends once and keeps its outcome.
 * Only a live run whose driver is still running is armed.
 * Only the lock ends the waiting, and only the List phase ends the building.
 * An outcome arrives once.
-/
def problem (d : RunData) (name : String) (c : Change) : Option String :=
  let after := d.apply c
  let d' := (after.map (·.1)).getD d
  let act? := after.bind (·.2)
  if !d.phase.isLive && after.isSome then
    some s!"{name} changed a run that was {d.phase.name}"
  else if after.isSome && (c matches .exited) &&
      (d'.phase != d.phase || sizesOf d' != sizesOf d || d'.kill?.isSome) then
    some "the driver's exit changed more than the kill"
  else if (c matches .cancel) && after.isSome && act?.isSome != d.kill?.isSome then
    some "a cancel's action is not the run's kill"
  else if (c matches .cancel) && after.isSome && !(d'.phase matches .cancelled) then
    some "a cancel did not cancel"
  else if (c matches .cancel | .arm _) && d.exited && after.isSome then
    some s!"{name} applied after the driver exited"
  else if !(c matches .locked _) && d.phase matches .waiting && d'.phase matches .building then
    some s!"{name} ended the waiting"
  else if !(c matches .listed _) && d.phase matches .building && d'.phase matches .running then
    some s!"{name} ended the building"
  else if (c matches .listed _) && after.isSome && !(d.phase matches .building) then
    some "the List phase began outside the building"
  else if (c matches .outcome _) && d.outcome?.isSome && after.isSome then
    some "a second outcome was taken"
  else if (c matches .ended | .finish _) && after.isSome && d.outcome?.isSome &&
      d'.phase != .done d.outcome?.get! then
    some "a run that reported an outcome ended with another"
  else if !(c matches .cancel) && act?.isSome then
    some s!"{name} has an action"
  else none

/--
Every sequence of up to four changes, applied to a new run, makes only transitions that
{name}`problem` accepts. Among them are a cancel against a finished run, output after the end, a
kill after the driver was reaped, and an outcome twice.
-/
@[test]
def transitionsInEveryOrder : Test := do
  let fresh : RunData := { wakeup := ← IO.Promise.new }
  let n := changes.size
  let mut found : Array String := #[]
  let mut count := 0
  for len in [1 : 5] do
    for code in [0 : n ^ len] do
      let mut d := fresh
      let mut path : Array String := #[]
      let mut rest := code
      for _ in [0 : len] do
        let (name, c) := changes[rest % n]?.getD ("exited", .exited)
        rest := rest / n
        path := path.push name
        if let some p := problem d name c then
          if found.size < 5 then found := found.push s!"{", ".intercalate path.toList}: {p}"
        d := ((d.apply c).map (·.1)).getD d
      count := count + 1
  assertTrue found.isEmpty
    s!"{found.size} problems among {count} sequences:\n{"\n".intercalate found.toList}"

/--
A cancel that arrives after the driver was reaped is answered as finished: it kills nothing, and the
outcome that the rest of the events file gives is kept.
-/
@[test]
def noKillAfterReaping : Test := do
  let killed ← IO.mkRef 0
  let s ← RunState.new "r" "" 0 0
  assertTrue (← s.apply (.locked 0))
  assertTrue (← s.apply (.arm (killed.modify (· + 1))))
  assertTrue (← s.apply .exited)
  assertTrue (!(← s.cancelNamed "r")) "a cancel after the driver's exit applied"
  assertTrue (← s.apply (.outcome { status := "pass" }))
  assertTrue (← s.apply .ended)
  assertBEq 0 (← killed.get)
  assertTrue ((← s.phase) == .done { status := "pass" }) s!"the run is {(← s.phase).name}"

/-- A run cancelled while it waits for the build lock never starts building. -/
@[test]
def cancelWhileWaiting : Test := do
  let s ← RunState.new "r" "" 0 0
  assertBEq "waiting" (← s.phase).name
  assertTrue (← s.cancelNamed "r")
  assertTrue (!(← s.apply (.locked 5))) "a cancelled run took the lock"

/-- A cancel of a live run performs the kill that the run holds, once. -/
@[test]
def cancelKillsOnce : Test := do
  let killed ← IO.mkRef 0
  let s ← RunState.new "r" "" 0 0
  discard <| s.apply (.arm (killed.modify (· + 1)))
  assertTrue (← s.apply .cancel)
  assertTrue (!(← s.apply .cancel)) "a second cancel applies"
  assertBEq 1 (← killed.get)

/-- A cancel that names another run, or a run that is over, reports that it did nothing. -/
@[test]
def cancelNamingAnotherRun : Test := do
  let s ← RunState.new "current" "" 0 0
  assertTrue (!(← s.cancelNamed "stale")) "a stale identifier cancelled the run"
  assertTrue (← s.phase).isLive
  assertTrue (!(← s.cancelNamed "")) "an empty identifier cancelled the run"
  discard <| s.apply (.finish { status := "pass" })
  assertTrue (!(← s.cancelNamed "current")) "a finished run was cancelled"
  assertTrue ((← s.phase) matches .done _)

/--
A cancel and the end of a run that race each other from two threads settle the run once: exactly one
of them applies, and the kill runs exactly when the cancel won.
-/
@[test]
def cancelRacesTheEnd : Test := do
  for _ in [0 : 200] do
    let killed ← IO.mkRef 0
    let s ← RunState.new "r" "" 0 0
    discard <| s.apply (.arm (killed.modify (· + 1)))
    let cancel ← IO.asTask (prio := .dedicated) (s.apply .cancel)
    let finish ← IO.asTask (prio := .dedicated) (s.apply (.finish { status := "pass" }))
    let c ← IO.ofExcept (← IO.wait cancel)
    let f ← IO.ofExcept (← IO.wait finish)
    assertTrue (c != f) s!"cancel applied: {c}, finish applied: {f}"
    assertBEq (if c then 1 else 0) (← killed.get)

/-- The requests that wait on a run wake when a change applies to it, and only then. -/
@[test]
def changesWakeWaiters : Test := do
  let s ← RunState.new "r" "" 0 0
  let waiting := (← s.data.get).wakeup
  assertTrue (!(← s.apply (.listed 3))) "a waiting run began its List phase"
  assertTrue (!(← IO.hasFinished waiting.result?)) "a change that did not apply woke a waiter"
  assertTrue (← s.apply (.output { stream := .stdout, text := "x" }))
  assertTrue (← IO.hasFinished waiting.result?) "the waiter was not woken"
  assertTrue (!(← IO.hasFinished (← s.data.get).wakeup.result?)) "the new promise is resolved"
  -- A promise that nothing holds counts as dropped, and its result is then finished, so the run is
  -- kept alive until the checks are done.
  assertTrue (← s.phase).isLive

/--
Locations arrive with codepoint columns and lines from one, and the editor counts lines from zero
and columns in UTF-16 code units.
-/
@[test]
def locationsInTheEditorsUnits : Test := do
  IO.FS.withTempDir fun dir => do
    let file := dir / "Astral.lean"
    IO.FS.writeFile file "first line\n  result \"🙂🙂\" (assertBEq 1 2)\n"
    let cache ← SourceLines.new
    let l : Location := { file := file.toString, startPos := ⟨2, 16⟩, endPos := ⟨2, 29⟩ }
    let s ← Source.ofLocation cache l
    assertBEq 1 s.startLine
    assertBEq 18 s.startColumn
    assertBEq 31 s.endColumn
    assertBEq (System.Uri.pathToUri file.toString) s.uri
    result "an unreadable file keeps its columns" do
      let s ← Source.ofLocation cache { l with file := (dir / "Missing.lean").toString }
      assertBEq 16 s.startColumn

/-- The text that each result wrote, by the result's identifier, from a run's output. -/
def outputByResult (d : RunData) : Std.HashMap Nat String :=
  d.chunks.foldl (init := {}) fun m c => m.insert c.result (m.getD c.result "" ++ c.text)

/--
The latest report of each result, by identifier: a result reports its start and then its end, and
the end's fields win.
-/
def latestReports (d : RunData) : Std.HashMap Nat ResultNode :=
  d.results.foldl (init := {}) fun m r => m.insert r.id r

/--
The events file of a run of one test, from {lit}`--filter` and {lit}`--events`, gives the display
that the widget shows: the tree of named results with their parents and statuses, what each result
wrote, and the outcome, as the server's transitions build them from the file's records.
-/
@[test]
def displayFromEvents : Test := do
  let p := Conformance.leanProduct
  let r ← p.runTests #["nestedResults"]
  let s ← RunState.new "r" "" 0 0
  discard <| s.apply (.locked 0)
  let cache ← SourceLines.new
  for e in r.events do
    for c in ← changesOfRecord cache "nestedResults" 0 none e do
      discard <| s.apply c
  let d ← s.data.get
  let some (.done o) := some d.phase | fail s!"the run is {d.phase.name}"
  assertBEq "pass" o.status
  assertTrue o.ran
  let reports := latestReports d
  let tree := (List.range 6).map fun i =>
    (reports.get? i).map fun r => (r.name, r.parent, r.status?)
  assertBEq [some ("", 0, some "pass"), some ("parsing", 0, some "pass"),
      some ("tokens", 1, some "pass"), some ("syntax", 1, some "pass"),
      some ("evaluation", 0, some "pass"), some ("arithmetic", 4, some "pass")] tree
  let out := outputByResult d
  assertBEq (some "setting up\ntearing down\n") (out.get? 0)
  assertBEq (some ("reading the source\n" ++ "".intercalate (List.replicate 5 "...\n")))
    (out.get? 1)
  assertBEq (some "12 tokens\n") (out.get? 2)
  assertBEq (some "the evaluator is slow today\n") (out.get? 4)
  assertTrue (d.chunks.any fun c => c.result == 4 && c.stream == .stderr) "stderr stays apart"
  assertTrue (d.execStartTime > 0) "the test's start is known"

/--
The display of a run whose test fails an assertion in its own code: the test's own report has the
verdict and the place of the failed check.
-/
@[test]
def failureFromEvents : Test := do
  let p := Conformance.leanProduct
  let r ← p.run #[p.fails]
  let s ← RunState.new "r" "" 0 0
  discard <| s.apply (.locked 0)
  let cache ← SourceLines.new
  for e in r.events do
    for c in ← changesOfRecord cache p.fails.test 0 none e do
      discard <| s.apply c
  let d ← s.data.get
  let some (.done o) := some d.phase | fail s!"the run is {d.phase.name}"
  assertBEq "fail" o.status
  let failed := d.results.filter (·.status? == some "fail")
  assertTrue (failed.any (·.location?.isSome)) "the failed check has a place"

/--
Records about other tests change nothing, fixture phases are steps, issues are kept, and a run that
ends without an outcome for its test ends with an error that says so.
-/
@[test]
def recordsOfOtherKinds : Test := do
  let s ← RunState.new "r" "" 90 0
  discard <| s.apply (.locked 100)
  let cache ← SourceLines.new
  let apply (j : Json) : TestM Unit := do
    for c in ← changesOfRecord cache "t" 100 none j do discard <| s.apply c
  let str := Json.str
  apply (Json.mkObj [("type", str "phase"), ("name", str "List"), ("time_ms", Lean.toJson 150)])
  apply (Json.mkObj [("type", str "output"), ("test", str "other"), ("text", str "not mine")])
  apply (Json.mkObj [("type", str "issue"), ("level", str "warning"), ("message", str "careful")])
  apply (Json.mkObj [("type", str "outcome"), ("kind", str "fixture"), ("test", str "db"),
    ("path", Lean.toJson #["db", "setup"]), ("reported", Json.mkObj [("status", str "pass")])])
  apply (Json.mkObj [("type", str "end")])
  let d ← s.data.get
  assertBEq 50 d.buildMs
  assertBEq 0 d.chunks.size
  assertBEq #[({ level := "warning", message := "careful" } : Issue)] d.issues
  assertBEq #["db"] (d.steps.map (·.fixture))
  assertTrue (d.phase == .done .noTest) s!"the run is {d.phase.name}"

end ErrataTests.WidgetState
