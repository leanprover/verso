/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The progress display that the human report keeps below its printed lines on a terminal: the count
line with its bar, then the running list. A frame holds what the display shows and renders to lines;
a display owns the terminal, erasing and redrawing the block of lines as the run proceeds.
-/
module

public import Errata.Dispatcher
public import Errata.CommandLine
public import Std.Sync.Mutex

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata.Progress

open Errata.Runner

/-- A test or a fixture's phase in the running list. -/
structure Entry where
  /-- The test executable's name. -/
  exe : String
  /-- The test's name, or the fixture's for a fixture's phase. -/
  test : String
  /-- The components of the test's name, for its styles. -/
  path : Array String := #[]
  /--
  The phase of a fixture, as the report's fixture lines show it ({lit}`setup`, {lit}`prepare T`, or
  {lit}`teardown`), and the empty string for a test.
  -/
  phase : String := ""
  /-- What tells a fixture's phase apart from a test of the same name, as {name}`Planned.key`. -/
  key : String := ""
  /-- When it started, in milliseconds on the monotonic clock. -/
  startMs : Nat
deriving Repr, Inhabited, DecidableEq

/-- The running-list entry of a test or a fixture's phase that starts at {name}`startMs`. -/
def Entry.ofPlanned (p : Planned) (startMs : Nat) : Entry :=
  match p.kind with
  | .test => { exe := p.exe, test := p.test, path := p.path, key := p.key, startMs }
  | .fixture =>
    { exe := p.exe, test := p.test, key := p.key, startMs
      phase := " ".intercalate (p.path.extract 1 p.path.size).toList }

/-- What the progress display shows. -/
structure Frame where
  /-- The number of tests that the Run phase reports. -/
  total : Nat := 0
  /-- The number of tests completed. -/
  completed : Nat := 0
  /-- The number of completed tests that passed. -/
  passed : Nat := 0
  /-- The number of completed tests that failed, had an error, or were inconclusive. -/
  failed : Nat := 0
  /-- The running tests and fixture phases, in the order they started. -/
  running : Array Entry := #[]
deriving Repr, Inhabited, DecidableEq

/-- Adds an entry to the running list. -/
def Frame.start (f : Frame) (e : Entry) : Frame :=
  { f with running := f.running.push e }

/--
Removes the entry with the given executable, name, and key from the running list. When
{name}`passed?` holds a value, a test completed, and it counts as passed when the value is true and
as failed otherwise. Fixture phases give no value and count in neither.
-/
def Frame.finish (f : Frame) (exe test key : String) (passed? : Option Bool) : Frame :=
  let running := match f.running.findIdx? (fun e => e.exe == exe && e.test == test && e.key == key)
    with
    | some i => f.running.eraseIdx! i
    | none => f.running
  match passed? with
  | none => { f with running }
  | some true => { f with running, completed := f.completed + 1, passed := f.passed + 1 }
  | some false => { f with running, completed := f.completed + 1, failed := f.failed + 1 }

/--
The frame after a dispatched event, at {name}`nowMs` on the monotonic clock. Tests and fixture
phases join the running list when they start and leave it when they end. When a test ends, it
completes, and it passed when every result of it that the event added to the run, {name}`fresh`,
passed. Tests that the runner reports without starting a process start and end in the same way.
-/
def Frame.after (f : Frame) (ev : Event) (fresh : Array Result) (nowMs : Nat) : Frame :=
  match ev with
  | .testStarted p => f.start (.ofPlanned p nowMs)
  | .testEnded exe test key .. =>
    match fresh[0]? with
    | none => f
    | some own =>
      let passed? := if own.kind matches .test then some (fresh.all (·.outcome.isPass)) else none
      f.finish exe test key passed?
  | _ => f

/-- An elapsed time in milliseconds as minutes and seconds, {lit}`m:ss`, with hours as minutes. -/
def elapsed (ms : Nat) : String :=
  let s := ms / 1000
  let secs := toString (s % 60)
  s!"{s / 60}:{if secs.length < 2 then "0" ++ secs else secs}"

/-- The fewest columns that the bar takes, its brackets included. -/
def minBarWidth : Nat := 10

/-- The first {name}`n` characters of a string. -/
private def takeChars (n : Nat) (s : String) : String :=
  String.ofList (s.toList.take n)

/--
The count line: the tests completed out of the total, with those that passed and failed, then a
space and the bar of {lit}`=` and spaces that fills the rest of {name}`width`, when at least
{name}`minBarWidth` columns remain for it. When the counts alone are wider than {name}`width`, they
are cut to it, uncolored.
-/
def countLine (f : Frame) (width : Nat) (color : Bool) : String :=
  let plain := s!"{f.completed}/{f.total} tests completed ({f.passed} passed, {f.failed} failed)"
  if plain.length > width then takeChars width plain
  else
    let n (k : Nat) := Style.count.paint color (toString k)
    let styled := s!"{n f.completed}/{n f.total} tests completed ({n f.passed} \
      {Style.pass.paint color "passed"}, {n f.failed} {Style.fail.paint color "failed"})"
    let room := width - plain.length - 1
    if room < minBarWidth then styled
    else
      let inner := room - 2
      let filled := if f.total == 0 then 0 else min inner (inner * f.completed / f.total)
      s!"{styled} [{"".pushn '=' filled}{"".pushn ' ' (inner - filled)}]"

/--
The line of a running entry: a space, the executable padded to {name}`exeWidth`, two spaces, the
name with its control characters escaped, and the time since the entry started in parentheses. When
the line would be wider than {name}`width`, the name is shortened to fit, ending with {lit}`…`; when
no room is left for the name, the whole line is cut to {name}`width`, uncolored.
-/
def runningLine (e : Entry) (nowMs width exeWidth : Nat) (color : Bool) : String :=
  let pad := "".pushn ' ' (exeWidth - e.exe.length)
  let lead := " " ++ e.exe ++ pad ++ "  "
  let tail := s!" ({elapsed (nowMs - e.startMs)})"
  let escapedPhase := Filter.escapeControls e.phase
  let name :=
    if e.phase.isEmpty then Filter.escapeControls e.test
    else Filter.escapeControls e.test ++ " " ++ escapedPhase
  let styledLead := " " ++ Style.exe.paint color e.exe ++ pad ++ "  "
  if lead.length + name.length + tail.length ≤ width then
    let styled :=
      if e.phase.isEmpty then styleTestName color e.test e.path
      else styleTestName color e.test #[] ++ " " ++ Style.testName.paint color escapedPhase
    styledLead ++ styled ++ tail
  else if lead.length + tail.length + 2 ≤ width then
    let room := width - lead.length - tail.length
    styledLead ++ Style.testName.paint color (takeChars (room - 1) name ++ "…") ++ tail
  else takeChars width (lead ++ name ++ tail)

/--
The lines of the progress display: the count line, then {lit}`Running:` and one line per running
entry, none wider than {name}`width`. {name}`nowMs` is the time on the monotonic clock that the
elapsed times are measured to, and {name}`exeWidth` is the width of the executable column. The
words are in the report's styles when {name}`color` is true; the bar has no color.
-/
def render (f : Frame) (nowMs width exeWidth : Nat) (color : Bool) : Array String :=
  #[countLine f width color, takeChars width "Running:"] ++
    f.running.map (runningLine · nowMs width exeWidth color)

/-- What a display holds between its operations. -/
structure DisplayState where
  /-- What the display shows. -/
  frame : Frame := {}
  /-- Whether the display is drawn: from its start until it is cleared. -/
  live : Bool := false
  /-- Whether clearing the display has ended it. -/
  ended : Bool := false
  /-- The number of lines of the block drawn last, which the next redraw erases. -/
  drawn : Nat := 0
  /-- The width of the executable column. -/
  exeWidth : Nat := 0
  /-- The terminal's width. -/
  width : Nat := 80
  /-- When the terminal's width was read last, on the monotonic clock. -/
  widthReadMs? : Option Nat := none

/--
The progress display on a terminal: the block of lines that {name}`render` gives, kept below the
lines printed through the display. Every write of the display is one {name}`IO.FS.Stream.putStr`
followed by a flush.
-/
structure Display where
  /-- Where the display writes. -/
  out : IO.FS.Stream
  /-- Whether the display's words are colored. -/
  color : Bool
  /-- The terminal's width when it is fixed; otherwise it is read from the terminal. -/
  width? : Option Nat := none
  /-- The display's state, behind a lock. -/
  state : Std.Mutex DisplayState

/-- How often the terminal's width is read at most, in milliseconds. -/
def widthReadEveryMs : Nat := 2000

/-- How often a live display is redrawn, in milliseconds, so that the elapsed times advance. -/
def tickMs : UInt32 := 1000

/--
The width of the terminal on standard output: {lit}`COLUMNS` when it is set to a positive number,
else the columns that {lit}`stty size` reports for standard output, which it reads as its own
standard input, else 80.
-/
def terminalWidth : IO Nat := do
  if let some n := (← IO.getEnv "COLUMNS").bind (·.trimAscii.copy.toNat?) then
    if n > 0 then return n
  try
    -- The child's standard output is the runner's, the terminal; `stty` reads the size of its
    -- standard input, which the shell makes that terminal, and reports on the piped standard error.
    let child ← IO.Process.spawn
      { cmd := "sh", args := #["-c", "stty size <&1 >&2"], stdin := .null, stdout := .inherit
        stderr := .piped }
    let out ← child.stderr.readToEnd
    let _ ← child.wait
    match (out.splitOn " ").getLast?.bind (·.trimAscii.copy.toNat?) with
    | some n => return if n > 0 then n else 80
    | none => return 80
  catch _ => return 80

/-- A display that writes to {name}`out`, drawn once it is started. -/
def Display.new (out : IO.FS.Stream) (color : Bool) (width? : Option Nat := none) :
    BaseIO Display :=
  return { out, color, width?, state := ← Std.Mutex.new {} }

/-- The terminal sequences that erase a block of {name}`n` lines above the cursor. -/
def eraseText (n : Nat) : String :=
  if n == 0 then "" else s!"\x1b[{n}A\x1b[J"

/--
Erases the drawn block, writes {name}`text`, and draws the block again when the display is live, as
one write. The terminal's width is read first when the last reading is older than
{name}`widthReadEveryMs`.
-/
private def Display.redraw (d : Display) (text : String) :
    Std.AtomicT DisplayState IO Unit := do
  let s ← get
  if !s.live then
    unless text.isEmpty do
      d.out.putStr text
      d.out.flush
    return
  let now ← IO.monoMsNow
  let s ← match d.width? with
    | some width => pure { s with width }
    | none =>
      if s.widthReadMs?.all (· + widthReadEveryMs ≤ now) then
        pure { s with width := ← terminalWidth, widthReadMs? := some now }
      else pure s
  let lines := render s.frame now s.width s.exeWidth d.color
  set { s with drawn := lines.size }
  d.out.putStr (eraseText s.drawn ++ text ++ String.join (lines.toList.map (· ++ "\n")))
  d.out.flush

/--
Prints lines above the display and changes its frame with {name}`f`, in one write: the block is
erased, the lines are written, and the block is drawn again.
-/
def Display.emit (d : Display) (lines : Array String) (f : Frame → Frame := id) : IO Unit :=
  d.state.atomically do
    modify fun s => { s with frame := f s.frame }
    d.redraw (String.join (lines.toList.map (· ++ "\n")))

/-- Prints a line above the display. -/
def Display.print (d : Display) (line : String) : IO Unit :=
  d.emit #[line]

/-- Changes the display's frame and redraws it. -/
def Display.update (d : Display) (f : Frame → Frame) : IO Unit :=
  d.emit #[] f

/--
Erases the display and draws nothing more; later lines are printed as they are. Clearing an ended
display changes nothing.
-/
def Display.clear (d : Display) : IO Unit :=
  d.state.atomically do
    let s ← get
    set { s with live := false, ended := true, drawn := 0 }
    if s.live && s.drawn > 0 then
      d.out.putStr (eraseText s.drawn)
      d.out.flush

/--
Draws the display with {name}`total` tests to complete and an executable column {name}`exeWidth`
wide. When {name}`ticker` is true, a thread redraws the display every second until it is cleared.
After {name}`Display.clear`, starting draws nothing.
-/
def Display.start (d : Display) (total exeWidth : Nat) (ticker : Bool := true) : IO Unit := do
  let started ← d.state.atomically do
    if (← get).ended then return false
    modify fun s => { s with live := true, exeWidth, frame := { s.frame with total } }
    d.redraw ""
    return true
  if started && ticker then
    let _ ← IO.asTask (prio := .dedicated) do
      repeat
        IO.sleep tickMs
        let live ← d.state.atomically do
          if (← get).live then
            d.redraw ""
            return true
          else return false
        unless live do break

/--
Whether a run keeps the progress display: the command is {lit}`run`, {lit}`--hide-progress-bar` is
absent, the platform is not Windows, standard output is a terminal, and {lit}`TERM` is set and is
not {lit}`dumb`.
-/
def enabled (opts : Options) : IO Bool := do
  if opts.hideProgressBar || opts.command != .run || System.Platform.isWindows then return false
  unless ← (← IO.getStdout).isTty do return false
  match ← IO.getEnv "TERM" with
  | none | some "" | some "dumb" => return false
  | some _ => return true

end Errata.Progress
