/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Tests of the progress display: the lines that a frame renders to, the frame's changes as events are
dispatched, and the bytes that a display writes to its stream.
-/
module

public import Errata

open Errata

public section

namespace ErrataTests.Progress

/-- The monotonic time at which the frames of these tests are rendered. -/
def now : Nat := 10000000

/-- A running entry of the executable {name}`exe` that started {name}`agoMs` milliseconds ago. -/
def entry (exe test : String) (agoMs : Nat) (path : Array String := #[]) : Errata.Progress.Entry :=
  { exe, test, path, startMs := now - agoMs }

/-- The frame of the user's example: 125 of 852 tests completed, and two tests running. -/
def example1 : Errata.Progress.Frame := {
  total := 852, completed := 125, passed := 123, failed := 2
  running := #[entry "VersoTests" "someMoreTest" 9000, entry "VersoTests" "testtesttest" 744000]
}

/-- The user's example renders to the count line with its bar and the running list. -/
@[test]
def rendersTheExample : Test := do
  assertBEq #[
      "125/852 tests completed (123 passed, 2 failed) [=======" ++
        "                                            ]",
      "Running:",
      " VersoTests  someMoreTest (0:09)",
      " VersoTests  testtesttest (12:24)"]
    (Errata.Progress.render example1 now 100 10 false)

/-- With nothing running, the display is the count line and {lit}`Running:`. -/
@[test]
def rendersNothingRunning : Test := do
  assertBEq #["0/3 tests completed (0 passed, 0 failed)", "Running:"]
    (Errata.Progress.render { total := 3 } now 45 10 false)
  assertBEq #["0/0 tests completed (0 passed, 0 failed) [          ]", "Running:"]
    (Errata.Progress.render {} now 53 10 false)

/-- The bar fills the width that the counts leave, and it is left out below its least width. -/
@[test]
def barFitsTheWidth : Test := do
  let frame : Errata.Progress.Frame :=
    { total := 4, completed := 2, passed := 2, running := #[entry "Lib" "a.long.name" 0] }
  for width in [60, 40, 20] do
    result s!"width {width}" do
      let lines := Errata.Progress.render frame now width 3 false
      for l in lines do
        assertTrue (l.length ≤ width) s!"{l.quote} is wider than {width}"
      assertBEq (width == 60) ((lines[0]!.splitOn "[").length == 2)
  assertBEq #["2/4 tests completed (2 passed, 0 failed) [========         ]", "Running:",
      " Lib  a.long.name (0:00)"]
    (Errata.Progress.render frame now 60 3 false)
  assertBEq #["2/4 tests completed (2 passed, 0 failed)", "Running:", " Lib  a.long.name (0:00)"]
    (Errata.Progress.render frame now 40 3 false)
  assertBEq #["2/4 tests completed ", "Running:", " Lib  a.long… (0:00)"]
    (Errata.Progress.render frame now 20 3 false)

/-- Elapsed times are minutes and seconds, with hours counted as minutes. -/
@[test]
def elapsedTimes : Test := do
  assertBEq "0:09" (Errata.Progress.elapsed 9000)
  assertBEq "12:24" (Errata.Progress.elapsed (12 * 60000 + 24000))
  assertBEq "72:05" (Errata.Progress.elapsed (72 * 60000 + 5000 + 999))

/-- Names are escaped as the report escapes them, and those too long for the width are cut. -/
@[test]
def namesEscapedAndCut : Test := do
  let frame : Errata.Progress.Frame :=
    { running := #[entry "Lib" "a\nb" 0, entry "Lib" "averyveryverylongname" 61000,
        { exe := "Lib", test := "db", phase := "prepare T", key := "prepare T", startMs := now }] }
  assertBEq #[" Lib  a\\nb (0:00)", " Lib  averyveryver… (1:01)", " Lib  db prepare T (0:00)"]
    ((Errata.Progress.render frame now 26 3 false).extract 2 5)
  -- With no room for the name, the line is cut.
  assertBEq " Lib  av" ((Errata.Progress.render frame now 8 3 false)[3]!)

/-- With color, the words have the report's styles and the bar has none. -/
@[test]
def colorsTheWords : Test := do
  let lines := Errata.Progress.render example1 now 100 10 true
  assertContains "\x1b[32;1mpassed\x1b[0m" lines[0]!
  assertContains "\x1b[31;1mfailed\x1b[0m" lines[0]!
  assertContains "\x1b[35;1mVersoTests\x1b[0m" lines[2]!
  assertContains "\x1b[34;1msomeMoreTest\x1b[0m" lines[2]!
  let bar := (lines[0]!.splitOn ") [").getLast!
  assertNotContains "\x1b" bar
  assertBEq ("=======" ++ "".pushn ' ' 44 ++ "]") bar

/-- The frame follows dispatched events; fixture phases count in neither the total nor the tests. -/
@[test]
def framesFollowEvents : Test := do
  let planned (test : String) (kind : Result.Kind := .test) : Runner.Planned :=
    { exe := "Lib", test, kind, key := if kind matches .fixture then "setup" else ""
      path := if kind matches .fixture then #[test, "setup"] else #[test], reproduce := "" }
  let res (test : String) (outcome : Outcome) (kind : Result.Kind := .test) : Result :=
    { exe := "Lib", test, kind, outcome }
  let f : Errata.Progress.Frame := { total := 2 }
  let f := f.after (.testStarted (planned "fx" .fixture)) #[] 5
  let f := f.after (.testStarted (planned "a")) #[] 7
  assertBEq #["fx setup", "a"] (f.running.map fun e => (e.test ++ " " ++ e.phase).trimAscii.copy)
  let f := f.after (.testEnded "Lib" "fx" "setup" (.exited 0) 1)
    #[res "fx" (.reported .pass) .fixture] 9
  assertBEq (0, 0, 0) (f.completed, f.passed, f.failed)
  let f := f.after (.testEnded "Lib" "a" "" (.exited 0) 1)
    #[res "a" (.reported .pass), { res "a" (.reported (.fail { message := "no" })) with
      resultPath := #["inner"] }] 9
  assertBEq (1, 0, 1) (f.completed, f.passed, f.failed)
  assertBEq 0 f.running.size
  let f := f.after (.testStarted (planned "b")) #[] 10
  let f := f.after (.testEnded "Lib" "b" "" (.settingMissing "s") 0)
    #[res "b" (.inconclusive (.settingMissing "s"))] 10
  assertBEq (2, 0, 2) (f.completed, f.passed, f.failed)

/--
The display fits the terminal's rows: at most the rows less two lines, the last entry that fits
replaced by the number of entries left out. Zero rows set no bound.
-/
@[test]
def blockFitsTheRows : Test := do
  let frame : Errata.Progress.Frame :=
    { total := 20, running := (List.range 16).toArray.map (entry "Lib" s!"t{·}" 0) }
  assertBEq 18 (Errata.Progress.render frame now 60 3 false).size
  assertBEq 18 (Errata.Progress.render frame now 60 3 false (rows := 0)).size
  let capped := Errata.Progress.render frame now 60 3 false (rows := 12)
  assertBEq 10 capped.size
  assertBEq " Lib  t6 (0:00)" capped[8]!
  assertBEq " … and 9 more" capped[9]!
  assertBEq 18 (Errata.Progress.render frame now 60 3 false (rows := 20)).size
  assertBEq 2 (Errata.Progress.render frame now 60 3 false (rows := 4)).size
  assertBEq 1 (Errata.Progress.render frame now 60 3 false (rows := 3)).size
  assertBEq 3 (Errata.Progress.render frame now 60 3 false (rows := 5)).size

/-- A failed fixture phase shows on the count line, in the singular for one. -/
@[test]
def countsFailedFixtures : Test := do
  assertBEq "1/2 tests completed (1 passed, 0 failed, 1 fixture failed)"
    (Errata.Progress.countLine { total := 2, completed := 1, passed := 1, fixturesFailed := 1 }
      60 false)
  assertBEq "0/2 tests completed (0 passed, 0 failed, 2 fixtures failed)"
    (Errata.Progress.countLine { total := 2, fixturesFailed := 2 } 60 false)

/--
A display writes its block, erases it above each printed line and draws it again below, and erases
it for good when it is cleared, leaving the printed lines. It renders one column narrower than the
terminal.
-/
@[test]
def displayWritesItsBlock : Test := do
  let buf ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let d ← Errata.Progress.Display.new (IO.FS.Stream.ofBuffer buf) false
    (size? := some { cols := 61 })
  d.start 2 3 (ticker := false)
  d.print "FAIL Lib x"
  -- An entry that starts in the future shows an elapsed time of zero.
  let e : Errata.Progress.Entry := { exe := "Lib", test := "t", startMs := (← IO.monoMsNow) + now }
  d.update (·.start e)
  d.clear
  d.clear
  d.print "Summary"
  let written := String.fromUTF8! (← buf.get).data
  let block (f : Errata.Progress.Frame) : String :=
    String.join ((Errata.Progress.render f 0 60 3 false).toList.map (· ++ "\n"))
  let empty : Errata.Progress.Frame := { total := 2 }
  let expected :=
    block empty ++
    "\x1b[2A\x1b[J" ++ "FAIL Lib x\n" ++ block empty ++
    "\x1b[2A\x1b[J" ++ block { empty with running := #[{ e with startMs := 0 }] } ++
    "\x1b[3A\x1b[J" ++
    "Summary\n"
  assertBEq expected written
  assertBEq
    "0/2 tests completed (0 passed, 0 failed) [                 ]\nRunning:\n Lib  t (0:00)\n"
    (block { empty with running := #[{ e with startMs := 0 }] })

end ErrataTests.Progress
