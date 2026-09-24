/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
How a test run in a process of its own ends: with a verdict that the test executable reported, or
inconclusive, with the reason the runner observed from outside the process.
-/
module

public import Errata.Failure
public import Lean.Data.Json

public section

set_option linter.missingDocs true
set_option doc.verso true

open Lean (Json ToJson FromJson)

namespace Errata

/-- The phases of a fixture. -/
inductive FixturePhase where
  /-- The phase that runs once per run and produces the fixture's value. -/
  | setup
  /-- The phase that runs before each test that uses the fixture. -/
  | prepare
  /-- The phase that runs once at the end, whenever the setup was invoked. -/
  | teardown
deriving Repr, Inhabited, DecidableEq, BEq

/-- The name of a fixture phase, as the protocol and the reports write it. -/
def FixturePhase.name : FixturePhase → String
  | .setup => "setup"
  | .prepare => "prepare"
  | .teardown => "teardown"

/-- The fixture phase with the given name. -/
def FixturePhase.ofName? : String → Option FixturePhase
  | "setup" => some .setup
  | "prepare" => some .prepare
  | "teardown" => some .teardown
  | _ => none

/-- A test's own verdict: the same three cases as {name}`Status`. -/
inductive Verdict where
  /-- The test passed. -/
  | pass
  /-- The test failed an assertion. -/
  | fail (failure : TestFailure)
  /-- An error escaped the test, so it could not produce a verdict of its own. -/
  | error (message : String)
deriving Repr, Inhabited, DecidableEq

/-- The verdict that corresponds to a status. -/
def Status.toVerdict : Status → Verdict
  | .pass => .pass
  | .fail f => .fail f
  | .error m => .error m

/-- The status that corresponds to a verdict. -/
def Verdict.toStatus : Verdict → Status
  | .pass => .pass
  | .fail f => .fail f
  | .error m => .error m

/-- Whether the verdict is a pass. -/
def Verdict.isPass : Verdict → Bool
  | .pass => true
  | .fail _ | .error _ => false

/-- The reasons that a test ends without a verdict that the runner can trust. -/
inductive Inconclusive where
  /-- A fixture that the test needs failed in the given phase, so the test was not run. -/
  | fixtureFailed (fixture : String) (phase : FixturePhase)
  /-- A mandatory setting has no value, so the test was not run. -/
  | settingMissing (setting : String)
  /-- The test executable could not be started. -/
  | spawnFailed (message : String)
  /--
  The test ran past its timeout and was terminated, after {name}`afterMs` milliseconds.
  {name}`killed` says whether it outlasted the grace period and had to be killed.
  -/
  | timedOut (afterMs : Nat) (killed : Bool)
  /-- The test executable was ended by the given signal. -/
  | signaled (signal : Nat)
  /-- The test executable exited with a non-zero code and reported no verdict. -/
  | exitedWithoutVerdict (code : UInt32)
  /-- The test executable's exit code contradicts the verdict it reported. -/
  | verdictMismatch (exitCode : UInt32) (claimed : Verdict)
  /-- The test executable's result file could not be read. -/
  | resultStreamUnreadable (message : String)
deriving Repr, Inhabited, DecidableEq

/-- How a test ended. -/
inductive Outcome where
  /-- The test executable reported a verdict, or its exit code implied one. -/
  | reported (verdict : Verdict)
  /-- No verdict could be established; the reason was observed from outside the process. -/
  | inconclusive (reason : Inconclusive)
deriving Repr, Inhabited, DecidableEq

/-- The name of an inconclusive reason, as the protocol and the reports write it. -/
def Inconclusive.reasonName : Inconclusive → String
  | .fixtureFailed .. => "fixtureFailed"
  | .settingMissing .. => "settingMissing"
  | .spawnFailed .. => "spawnFailed"
  | .timedOut .. => "timedOut"
  | .signaled .. => "signaled"
  | .exitedWithoutVerdict .. => "exitedWithoutVerdict"
  | .verdictMismatch .. => "verdictMismatch"
  | .resultStreamUnreadable .. => "resultStreamUnreadable"

/-- The name of a verdict's status: {lit}`pass`, {lit}`fail`, or {lit}`error`. -/
def Verdict.statusName : Verdict → String
  | .pass => "pass"
  | .fail _ => "fail"
  | .error _ => "error"

/-- A sentence that explains an inconclusive reason to a person. -/
def Inconclusive.describe : Inconclusive → String
  | .fixtureFailed f p => s!"the fixture {f} failed in its {p.name} phase"
  | .settingMissing s => s!"the mandatory setting {s} has no value"
  | .spawnFailed m => s!"the test executable could not be started: {m}"
  | .timedOut ms killed =>
    s!"timed out after {ms}ms and was {if killed then "killed" else "terminated"}"
  | .signaled s => s!"the test executable was ended by signal {s} (exit code {128 + s})"
  | .exitedWithoutVerdict c => s!"the test executable exited with code {c} without a verdict"
  | .verdictMismatch c v =>
    s!"the test executable exited with code {c} after reporting the verdict {v.statusName}"
  | .resultStreamUnreadable m => s!"the result file could not be read: {m}"

/-- The status that an outcome counts as where only a status fits: inconclusive is an error. -/
def Outcome.toStatus : Outcome → Status
  | .reported v => v.toStatus
  | .inconclusive r => .error s!"inconclusive: {r.describe}"

/-- Whether an outcome is a reported pass. -/
def Outcome.isPass : Outcome → Bool
  | .reported .pass => true
  | _ => false

instance : ToJson Location where
  toJson l := json%{
    "file": $l.file,
    "startLine": $l.startPos.line,
    "startColumn": $l.startPos.column,
    "endLine": $l.endPos.line,
    "endColumn": $l.endPos.column
  }

instance : FromJson Location where
  fromJson? j := do
    return {
      file := ← j.getObjValAs? String "file",
      startPos := ⟨← j.getObjValAs? Nat "startLine", ← j.getObjValAs? Nat "startColumn"⟩,
      endPos := ⟨← j.getObjValAs? Nat "endLine", ← j.getObjValAs? Nat "endColumn"⟩
    }

/-- Decodes an optional field: absent maps to {lean}`none`. -/
def optField [FromJson α] (j : Json) (key : String) : Except String (Option α) :=
  match j.getObjVal? key with
  | .ok v => some <$> FromJson.fromJson? v
  | .error _ => pure none

/-- The fields of a verdict: its status and, for a failure or error, what explains it. -/
def Verdict.fields : Verdict → List (String × Json)
  | .pass => [("status", Json.str "pass")]
  | .fail f =>
    [("status", Json.str "fail"), ("message", Json.str f.message)] ++
      (match f.detail? with | some d => [("detail", Json.str d)] | none => []) ++
      (match f.location? with | some l => [("location", ToJson.toJson l)] | none => [])
  | .error m => [("status", Json.str "error"), ("message", Json.str m)]

instance : ToJson Verdict where
  toJson v := Json.mkObj v.fields

instance : FromJson Verdict where
  fromJson? j := do
    match ← j.getObjValAs? String "status" with
    | "pass" => return .pass
    | "error" => return .error (← j.getObjValAs? String "message")
    | "fail" => return .fail {
        message := ← j.getObjValAs? String "message",
        detail? := ← optField j "detail",
        location? := ← optField j "location"
      }
    | other => .error s!"unknown status: {other}"

instance : ToJson Inconclusive where
  toJson r := Json.mkObj <| ("reason", Json.str r.reasonName) :: match r with
    | .fixtureFailed f p => [("fixture", Json.str f), ("phase", Json.str p.name)]
    | .settingMissing s => [("setting", Json.str s)]
    | .spawnFailed m => [("message", Json.str m)]
    | .timedOut ms killed => [("after_ms", ToJson.toJson ms), ("killed", ToJson.toJson killed)]
    | .signaled s => [("signal", ToJson.toJson s)]
    | .exitedWithoutVerdict c => [("code", ToJson.toJson c.toNat)]
    | .verdictMismatch c v => [("exit_code", ToJson.toJson c.toNat), ("claimed", ToJson.toJson v)]
    | .resultStreamUnreadable m => [("message", Json.str m)]

instance : FromJson Inconclusive where
  fromJson? j := do
    match ← j.getObjValAs? String "reason" with
    | "fixtureFailed" =>
      let phase ← j.getObjValAs? String "phase"
      let some phase := FixturePhase.ofName? phase | .error s!"unknown fixture phase: {phase}"
      return .fixtureFailed (← j.getObjValAs? String "fixture") phase
    | "settingMissing" => return .settingMissing (← j.getObjValAs? String "setting")
    | "spawnFailed" => return .spawnFailed (← j.getObjValAs? String "message")
    | "timedOut" =>
      return .timedOut (← j.getObjValAs? Nat "after_ms") (← j.getObjValAs? Bool "killed")
    | "signaled" => return .signaled (← j.getObjValAs? Nat "signal")
    | "exitedWithoutVerdict" =>
      return .exitedWithoutVerdict (← j.getObjValAs? Nat "code").toUInt32
    | "verdictMismatch" =>
      return .verdictMismatch (← j.getObjValAs? Nat "exit_code").toUInt32
        (← j.getObjValAs? Verdict "claimed")
    | "resultStreamUnreadable" => return .resultStreamUnreadable (← j.getObjValAs? String "message")
    | other => .error s!"unknown inconclusive reason: {other}"

/--
The fields of an outcome: {lit}`reported`, holding the verdict, or {lit}`inconclusive`, holding the
reason and its details.
-/
def Outcome.fields : Outcome → List (String × Json)
  | .reported v => [("reported", ToJson.toJson v)]
  | .inconclusive r => [("inconclusive", ToJson.toJson r)]

/-- Decodes an outcome from the fields of an object that {name}`Outcome.fields` wrote. -/
def Outcome.ofFields? (j : Json) : Except String Outcome := do
  match j.getObjVal? "reported", j.getObjVal? "inconclusive" with
  | .ok v, _ => return .reported (← FromJson.fromJson? v)
  | _, .ok r => return .inconclusive (← FromJson.fromJson? r)
  | _, _ => .error "the outcome has neither a verdict nor an inconclusive reason"
