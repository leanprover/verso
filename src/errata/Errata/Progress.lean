/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The progress display that the human report keeps below its printed lines on a terminal: the count
line with its bar, then the running list. A frame holds what the display shows, and `render` turns
it into lines. A display owns the terminal, and erases and redraws the block of lines as the run
proceeds.
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
  /-- The number of tests that the run selects. -/
  total : Nat := 0
  /-- The number of tests completed. -/
  completed : Nat := 0
  /-- The number of completed tests that passed. -/
  passed : Nat := 0
  /-- The number of completed tests that failed, had an error, or were inconclusive. -/
  failed : Nat := 0
  /-- The number of fixture phases that ended without passing. -/
  fixturesFailed : Nat := 0
  /-- The running tests and fixture phases, in the order they started. -/
  running : Array Entry := #[]
deriving Repr, Inhabited, DecidableEq

/-- Adds an entry to the running list. -/
def Frame.start (f : Frame) (e : Entry) : Frame :=
  { f with running := f.running.push e }

/--
Removes the entry with the given executable, name, and key from the running list. A value in
{name}`passed?` marks a completed test, which counts as passed when the value is true and as failed
when it is false. Fixture phases have no value and change no count.
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
phases join the running list when they start and leave it when they end. {name}`fresh` holds the
results that the event added to the run. Tests that end are completed: they count as passed when
all of these results passed, and as failed otherwise. Fixture phases that end count among the
failed fixture phases when any of these results did not pass. Tests that the runner reports
without starting a process also start and end through these events.
-/
def Frame.after (f : Frame) (ev : Event) (fresh : Array Result) (nowMs : Nat) : Frame :=
  match ev with
  | .testStarted p => f.start (.ofPlanned p nowMs)
  | .testEnded exe test key .. =>
    match fresh[0]? with
    | none => f
    | some own =>
      let passed := fresh.all (·.outcome.isPass)
      match own.kind with
      | .test => f.finish exe test key (some passed)
      | .fixture =>
        let f := f.finish exe test key none
        if passed then f else { f with fixturesFailed := f.fixturesFailed + 1 }
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
The count line: the tests completed out of the total, those that passed and those that failed, and
the failed fixture phases when there are any. When at least {name}`minBarWidth` columns of
{name}`width` remain, a space and a bar of {lit}`=` and spaces fill them. When the counts alone are
wider than {name}`width`, they are cut to it, uncolored.
-/
def countLine (f : Frame) (width : Nat) (color : Bool) : String :=
  let fixturesWord := if f.fixturesFailed == 1 then "fixture failed" else "fixtures failed"
  let plainFixtures :=
    if f.fixturesFailed == 0 then "" else s!", {f.fixturesFailed} {fixturesWord}"
  let plain := s!"{f.completed}/{f.total} tests completed ({f.passed} passed, {f.failed} failed\
    {plainFixtures})"
  if plain.length > width then takeChars width plain
  else
    let n (k : Nat) := Style.count.paint color (toString k)
    let fixtures :=
      if f.fixturesFailed == 0 then ""
      else s!", {n f.fixturesFailed} {Style.fail.paint color fixturesWord}"
    let styled := s!"{n f.completed}/{n f.total} tests completed ({n f.passed} \
      {Style.pass.paint color "passed"}, {n f.failed} {Style.fail.paint color "failed"}{fixtures})"
    let room := width - plain.length - 1
    if room < minBarWidth then styled
    else
      let inner := room - 2
      let filled := if f.total == 0 then 0 else min inner (inner * f.completed / f.total)
      s!"{styled} [{"".pushn '=' filled}{"".pushn ' ' (inner - filled)}]"

/--
The line of a running entry: a space, the executable padded to {name}`exeWidth`, two spaces, the
name with its control characters escaped, and the time since the entry started in parentheses. When
the line would be wider than {name}`width`, the name is shortened to fit, ending with {lit}`…`. When
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

When {name}`rows` is not zero, the display has at most {name}`rows` less two lines: the count line,
{lit}`Running:`, and at most {name}`rows` less four entries. With fewer than four rows, it has as
many of the first two lines as fit. When more entries are running than fit, the last line that
fits reads {lit}`… and N more`, with the number of entries left out.
-/
def render (f : Frame) (nowMs width exeWidth : Nat) (color : Bool) (rows : Nat := 0) :
    Array String :=
  let head := #[countLine f width color, takeChars width "Running:"]
  let line (e : Entry) := runningLine e nowMs width exeWidth color
  if rows == 0 then head ++ f.running.map line
  else
    let most := rows - 2
    if most < 2 then head.extract 0 most
    else
      let room := most - 2
      if f.running.size ≤ room then head ++ f.running.map line
      else if room == 0 then head
      else
        let shown := room - 1
        head ++ (f.running.extract 0 shown).map line ++
          #[takeChars width s!" … and {f.running.size - shown} more"]

/-- The size of a terminal, in rows and columns of characters. -/
structure TerminalSize where
  /-- The number of rows, or zero when it is unknown. -/
  rows : Nat := 0
  /-- The number of columns. -/
  cols : Nat := 80
deriving Repr, Inhabited, DecidableEq

/-- What a display holds between its operations. -/
structure DisplayState where
  /-- What the display shows. -/
  frame : Frame := {}
  /-- Whether the display is drawn: from its start until it is cleared. -/
  live : Bool := false
  /-- Whether the display has been cleared, which ends it. -/
  ended : Bool := false
  /-- Whether a batch is running, which leaves the block undrawn until the batch ends. -/
  held : Bool := false
  /-- The number of lines of the block drawn last, which the next redraw erases. -/
  drawn : Nat := 0
  /-- The width of the executable column. -/
  exeWidth : Nat := 0

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
  /-- The terminal's size when it is fixed; otherwise it is read from the terminal. -/
  size? : Option TerminalSize := none
  /-- The terminal's size as last read. -/
  size : IO.Ref TerminalSize
  /-- The display's state, behind a lock. -/
  state : Std.Mutex DisplayState

/-- The time in milliseconds between two redraws of the ticker, which advance the elapsed times. -/
def tickMs : UInt32 := 1000

/-- How many redraws of the ticker pass between two readings of the terminal's size. -/
def ticksPerSizeRead : Nat := 2

/--
The size of the terminal on standard output. The columns are {lit}`COLUMNS` when it is set to a
positive number, and otherwise what {lit}`stty size` reports for standard output. The rows come
from {lit}`LINES` or {lit}`stty size` in the same way. When neither gives a value, the columns are
80 and the rows are unknown.
-/
def terminalSize : IO TerminalSize := do
  let fromEnv (name : String) : IO (Option Nat) := do
    return (← IO.getEnv name).bind (·.trimAscii.copy.toNat?) |>.filter (· > 0)
  let cols? ← fromEnv "COLUMNS"
  let rows? ← fromEnv "LINES"
  if let (some cols, some rows) := (cols?, rows?) then return { rows, cols }
  let stty : TerminalSize ← try
    -- `stty` reports the size of its standard input to its standard output. The shell makes its
    -- standard input the inherited standard output and its standard output the piped standard
    -- error.
    let child ← IO.Process.spawn
      { cmd := "sh", args := #["-c", "stty size <&1 >&2"], stdin := .null, stdout := .inherit
        stderr := .piped }
    let out ← child.stderr.readToEnd
    let _ ← child.wait
    match (out.trimAscii.copy.splitOn " ").map (·.toNat?) with
    | [some rows, some cols] => pure { rows, cols := if cols > 0 then cols else 80 }
    | _ => pure {}
  catch _ => pure {}
  return { rows := rows?.getD stty.rows, cols := cols?.getD stty.cols }

/-- A display that writes to {name}`out`, drawn once it is started. -/
def Display.new (out : IO.FS.Stream) (color : Bool) (size? : Option TerminalSize := none) :
    BaseIO Display :=
  return { out, color, size?, size := ← IO.mkRef (size?.getD {}), state := ← Std.Mutex.new {} }

/-- Reads the terminal's size again, unless the display's size is fixed. -/
def Display.readSize (d : Display) : IO Unit := do
  if d.size?.isNone then d.size.set (← terminalSize)

/-- The terminal sequences that erase a block of {name}`n` lines above the cursor. -/
def eraseText (n : Nat) : String :=
  if n == 0 then "" else s!"\x1b[{n}A\x1b[J"

/--
Writes {name}`text` in one write. While the display is live, the write first erases the drawn
block, and it ends with the block drawn again when no batch is running. The block is rendered one
column narrower than the terminal.
-/
private def Display.redraw (d : Display) (text : String) :
    Std.AtomicT DisplayState IO Unit := do
  let s ← get
  if !s.live then
    unless text.isEmpty do
      d.out.putStr text
      d.out.flush
    return
  let lines ← if s.held then pure #[] else do
    let size ← d.size.get
    pure (render s.frame (← IO.monoMsNow) (size.cols - 1) s.exeWidth d.color size.rows)
  set { s with drawn := lines.size }
  let out := eraseText s.drawn ++ text ++ String.join (lines.toList.map (· ++ "\n"))
  unless out.isEmpty do
    d.out.putStr out
    d.out.flush

/-- Changes the display's frame with {name}`f` and prints lines above it, redrawing it once. -/
def Display.emit (d : Display) (lines : Array String) (f : Frame → Frame := id) : IO Unit :=
  d.state.atomically do
    modify fun s => { s with frame := f s.frame }
    d.redraw (String.join (lines.toList.map (· ++ "\n")))

/-- Prints a line above the display. -/
def Display.print (d : Display) (line : String) : IO Unit :=
  d.emit #[line]

/-- What the display shows. -/
def Display.frame (d : Display) : IO Frame :=
  d.state.atomically (return (← get).frame)

/-- Changes the display's frame and redraws it. -/
def Display.update (d : Display) (f : Frame → Frame) : IO Unit :=
  d.emit #[] f

/--
Runs {name}`act` as a batch: the lines that it prints appear with the block erased, and the block is
drawn once, when the batch ends.
-/
def Display.batch {α} (d : Display) (act : IO α) : IO α := do
  d.state.atomically (modify fun s => { s with held := true })
  try act
  finally
    d.state.atomically do
      modify fun s => { s with held := false }
      d.redraw ""

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
Reads the terminal's size and draws the display with {name}`total` tests to complete and an
executable column {name}`exeWidth` wide. When {name}`ticker` is true, a thread redraws the display
every {name}`tickMs` milliseconds until it is cleared, and reads the terminal's size once every
{name}`ticksPerSizeRead` redraws, outside the display's lock. After {name}`Display.clear`, starting
draws nothing.
-/
def Display.start (d : Display) (total exeWidth : Nat) (ticker : Bool := true) : IO Unit := do
  d.readSize
  let started ← d.state.atomically do
    if (← get).ended then return false
    modify fun s => { s with live := true, exeWidth, frame := { s.frame with total } }
    d.redraw ""
    return true
  if started && ticker then
    let _ ← IO.asTask (prio := .dedicated) do
      let mut ticks := 0
      repeat
        IO.sleep tickMs
        ticks := ticks + 1
        if ticks % ticksPerSizeRead == 0 then d.readSize
        let live ← d.state.atomically do
          let s ← get
          if s.live && !s.held then d.redraw ""
          return s.live
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
