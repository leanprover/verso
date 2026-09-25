/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The runner: it lists the tests of every test executable in its configuration, selects the tests that
the filters name, resolves what each receives, runs each in a process of its own under a timeout,
merges what the test executable reported with what it observed from outside, and writes the reports.
-/
module

public import Errata.RunnerConfig
public import Errata.Resolution
public import Errata.Dispatcher
public import Errata.ProcessControl
public import Errata.CommandLine
public import Std.Sync.Mutex
import all Errata.FS

public section

set_option linter.missingDocs true
set_option doc.verso true

open Lean (Json ToJson)

namespace Errata.Runner

open ProcessControl

/-- Whether a character can appear unquoted in a word for a POSIX shell. -/
private def shellSafe (c : Char) : Bool :=
  c.isAlphanum || "_-./:=@%+,".contains c

/-- A word quoted for a POSIX shell: as it is when that is safe, and in single quotes otherwise. -/
def shellQuote (s : String) : String :=
  if !s.isEmpty && s.all shellSafe then s
  else "'" ++ s.replace "'" "'\\''" ++ "'"

/-- Where a run's reporters send their output. -/
structure Sinks where
  /-- Receives each line of the events file. -/
  event : Json → IO Unit := fun _ => pure ()
  /-- Receives each line of the human-readable report. -/
  line : String → IO Unit := fun _ => pure ()

/-- The dispatcher: the state of the run, behind a lock that every event passes through. -/
structure Dispatcher where
  /-- The state. -/
  state : Std.Mutex State
  /-- Where actions go. -/
  sinks : Sinks

/-- Handles one event under the dispatcher's lock, calling the reporters before it returns. -/
def Dispatcher.dispatch (d : Dispatcher) (ev : Event) : IO Unit :=
  d.state.atomically do
    let (s, actions) := step (← get) ev
    set s
    for a in actions do
      match a with
      | .event j => d.sinks.event j
      | .print l => d.sinks.line l

/-- The dispatcher's current state. -/
def Dispatcher.get (d : Dispatcher) : IO State :=
  d.state.atomically MonadState.get

/--
The processes of a run that are running, and whether the run has been cancelled. Every process
starts under the lock, after a check of the cancellation. Once the run is cancelled, every later
start is refused.
-/
structure Registry where
  /-- Whether the run has been cancelled, and the groups that are running. -/
  state : Std.Mutex (Bool × Array Group)

/-- A registry with nothing running. -/
def Registry.new : BaseIO Registry := do
  return { state := ← Std.Mutex.new (false, #[]) }

/--
Starts a process with {name}`start` and records it. When the run has been cancelled, the result is
{lean}`none` and {name}`start` is skipped.
-/
def Registry.start (r : Registry) (start : IO Group) : IO (Option Group) :=
  r.state.atomically do
    let (cancelled, groups) ← get
    if cancelled then return none
    let g ← start
    set (cancelled, groups.push g)
    return some g

/-- Forgets a process that the run has finished with. -/
def Registry.release (r : Registry) (g : Group) : IO Unit :=
  r.state.atomically (modify fun (c, gs) => (c, gs.filter (·.pid != g.pid)))

/-- Whether the run has been cancelled. -/
def Registry.cancelled (r : Registry) : IO Bool :=
  r.state.atomically (return (← get).1)

/--
Cancels the run: every later start is refused, every running group is asked to terminate, and the
groups whose first process is still running after {name}`graceMs` milliseconds are killed. The parts
of the run that started the processes wait for them.
-/
def Registry.cancel (r : Registry) (graceMs : Nat) : IO Unit := do
  let groups ← r.state.atomically do
    let (_, gs) ← get
    set (true, gs)
    return gs
  for g in groups do g.terminate
  let deadline := (← IO.monoMsNow) + graceMs
  repeat
    let live ← (← r.state.atomically (return (← get).2)).filterM (·.armed.get)
    if live.isEmpty || (← IO.monoMsNow) ≥ deadline then break
    IO.sleep pollMs
  for g in (← r.state.atomically (return (← get).2)) do g.kill

/-- What the parts of a run share. -/
structure RunContext where
  /-- The configuration. -/
  config : Config
  /-- The options. -/
  opts : Options
  /-- The run's seed. -/
  runSeed : Nat
  /-- The run's identifier, which every test executable receives as {lit}`ERRATA_RUN_ID`. -/
  runId : String := ""
  /-- A directory for the result files of the run. -/
  dir : System.FilePath
  /-- The dispatcher. -/
  dispatcher : Dispatcher
  /-- The processes that are running, and whether the run has been cancelled. -/
  registry : Registry
  /-- How long a test executable may take to list its tests, in milliseconds. -/
  listTimeoutMs : Nat := defaultTimeoutMs
  /-- How long a listing that ran past its timeout has before it is killed, in milliseconds. -/
  listGracePeriodMs : Nat := defaultGracePeriodMs

/--
The environment variable that asks a process to treat its standard input as its lifeline, and to
end when it closes.
-/
def lifelineVariable : String := "ERRATA_LIFELINE"

/-- A new run identifier: 64 random bits, written as 16 hexadecimal digits. -/
def newRunId : IO String := do
  let bytes ← IO.getRandomBytes 8
  let hex (n : Nat) : String := String.singleton (Nat.digitChar n)
  return bytes.foldl (init := "") fun acc b => acc ++ hex (b.toNat / 16) ++ hex (b.toNat % 16)

/--
The environment variables that every test executable receives. {lit}`LEAN_ABORT_ON_PANIC` is
{lit}`1`, so a panic ends the process that panicked, and {lit}`ERRATA_RUN_ID` is the run's
identifier, the same for every process of one run.
-/
def RunContext.env (ctx : RunContext) (exe : ExecutableConfig) : Array (String × Option String) :=
  #[("LEAN_ABORT_ON_PANIC", some "1"), (lifelineVariable, some "1"),
      ("ERRATA_RUN_ID", some ctx.runId)] ++
    (ctx.config.errataDir?.map fun d => #[("ERRATA_DIR", some d)]).getD #[] ++
    exe.env.map fun (k, v) => (k, some v)

/--
The pipe grace, in milliseconds: how long the processes that a test executable started may hold its
output pipes after it exits.
-/
def pipeGraceMs : Nat := 500

/--
Waits for the readers of a process's output pipes once the process has exited. When processes that
it started still hold the pipes after the pipe grace, {name}`Group.sweep` ends its group with the
pipe grace as the sweep's grace period, and the readers then get one more pipe grace.
-/
def releasePipes (g : Group) (readers : List (Task (Except IO.Error Unit))) : IO Unit := do
  unless ← waitAtMost pipeGraceMs readers do
    g.sweep pipeGraceMs
    discard <| waitAtMost pipeGraceMs readers

/--
Runs a command in a process group of its own, with the listing's timeout and grace period, and
returns its exit code with what it wrote to standard output and standard error. The exit code is
{lean}`none` when it timed out. The whole result is {lean}`none` when the run has been cancelled.
-/
def runListing (ctx : RunContext) (exe : ExecutableConfig) (args : Array String) :
    IO (Option (Option UInt32 × String × String)) := do
  let some cmd := exe.command[0]? | throw <| .userError "the command is empty"
  let some g ← ctx.registry.start
      (spawnGroup cmd (exe.command.extract 1 exe.command.size ++ args) exe.cwd? (ctx.env exe))
    | return none
  let out ← IO.mkRef ""
  let err ← IO.mkRef ""
  let outTask ← IO.asTask (prio := .dedicated)
    (forwardLines g.child.stdout fun l => out.modify (· ++ l))
  let errTask ← IO.asTask (prio := .dedicated)
    (forwardLines g.child.stderr fun l => err.modify (· ++ l))
  let finished ← g.waitAtMost ctx.listTimeoutMs
  unless finished do discard <| g.terminateGraceKill ctx.listGracePeriodMs
  let code ← g.wait
  releasePipes g [outTask, errTask]
  ctx.registry.release g
  return some (if finished then some code else none, ← out.get, ← err.get)

/-- The report of a test executable that could not list its tests. -/
private def listFailure (exe : ExecutableConfig) (why stdout stderr : String) : String :=
  let streams :=
    (if stdout.isEmpty then "" else s!"\nstdout:\n{stdout}") ++
    (if stderr.isEmpty then "" else s!"\nstderr:\n{stderr}")
  s!"the test executable {exe.name} could not list its tests: {why}\n\
    command: {" ".intercalate (exe.command.toList.map shellQuote)} errata-list <out>{streams}"

/--
Asks one test executable for its inventory. The result is its settings and its tests, or the message
that says why it could not list them.
-/
def listExecutable (ctx : RunContext) (idx : Nat) (exe : ExecutableConfig) :
    IO (Except String Listing) := do
  let file := ctx.dir / s!"list-{idx}.jsonl"
  IO.FS.writeFile file ""
  let listing ←
    try runListing ctx exe #["errata-list", file.toString]
    catch e => return .error (listFailure exe s!"it could not be started: {e}" "" "")
  let some (code?, stdout, stderr) := listing
    | return .error (listFailure exe "the run was cancelled" "" "")
  let fail (why : String) := Except.error (listFailure exe why stdout stderr)
  let some code := code?
    | return fail s!"it did not finish within {ctx.listTimeoutMs}ms"
  unless code == 0 do
    return match signalOfExitCode? code with
      | some s => fail s!"it was ended by signal {s} (exit code {code})"
      | none => fail s!"it exited with code {code}"
  let text ← IO.FS.readFile file
  let lines := text.splitOn "\n" |>.filter (!·.trimAscii.isEmpty)
  if lines.isEmpty then return fail "it wrote nothing to its list file"
  let mut sawProtocol := false
  let mut settings : Array SettingInfo := #[]
  let mut tests : Array InventoryTest := #[]
  let mut names : Std.HashSet String := {}
  for line in lines do
    match Protocol.Record.parseLine line with
    | .error e => return fail s!"its list file has a line that could not be read: {e}"
    | .ok none => continue
    | .ok (some (_, record)) =>
      match record with
      | .protocol v? =>
        let v := v?.getD 0
        unless Protocol.minVersion ≤ v && v ≤ Protocol.maxVersion do
          return fail s!"it speaks protocol version {v}, and this runner accepts versions \
            {Protocol.minVersion} to {Protocol.maxVersion}"
        sawProtocol := true
      | .setting name? description? default? =>
        unless sawProtocol do return fail "its list file does not begin with a protocol record"
        let some name := name? | return fail "its list file has a setting without a name"
        if settings.any (·.name == name) then
          return fail s!"it declares the setting {name} more than once"
        settings := settings.push { name, description?, default? }
      | .test info =>
        unless sawProtocol do return fail "its list file does not begin with a protocol record"
        let some name := info.name? | return fail "its list file has a test without a name"
        -- The inventory leaves out benchmarks.
        if info.kind? == some "benchmark" then continue
        if names.contains name then return fail s!"it lists the test {name} more than once"
        names := names.insert name
        tests := tests.push {
          exeIdx := idx, name, path := info.path?.getD #[], file? := info.file?,
          line? := info.line?, description? := info.description?, tags := info.tags?.getD #[]
          settings := info.settings?.getD #[]
        }
      | _ => unless sawProtocol do
          return fail "its list file does not begin with a protocol record"
  unless sawProtocol do return fail "its list file has no protocol record"
  return .ok { settings, tests }

/-- The arguments of a test executable that runs one test. -/
def runArgs (out name : String) (settings : Array (String × String)) : Array String :=
  #["errata-run", out, name] ++ settings.map fun (k, v) => s!"setting:{k}={v}"

/--
The command that runs a test again by hand, quoted for a POSIX shell. Its records go to standard
error.
-/
def RunContext.reproduce (ctx : RunContext) (exe : ExecutableConfig) (name : String)
    (settings : Array (String × String)) : String :=
  let env : Array (String × String) :=
    #[("LEAN_ABORT_ON_PANIC", "1")] ++
    ((ctx.config.errataDir?.map fun d => #[("ERRATA_DIR", d)]).getD #[]) ++ exe.env
  let words := env.map (fun (k, v) => s!"{k}={shellQuote v}") ++
    (exe.command ++ runArgs "/dev/stderr" name settings).map shellQuote
  let cd := match exe.cwd? with | some d => s!"cd {shellQuote d} && " | none => ""
  cd ++ " ".intercalate words.toList

/--
The settings that a test executable receives for a test: the resolved values of the settings the
test takes, in the order it takes them, and {lit}`updateGolden` when golden checks rewrite their
expected files.
-/
def Resolved.arguments (r : Resolved) : Array (String × String) :=
  r.settings ++ (if r.updateGolden then #[("updateGolden", "true")] else #[])

/-- The test as the dispatcher plans it, with what it receives. -/
def RunContext.planned (ctx : RunContext) (exe : ExecutableConfig) (t : InventoryTest)
    (r : Resolved) : Planned :=
  let settings := r.arguments
  { exe := exe.name, test := t.name, path := t.path, description? := t.description?
    seed? := (r.settings.find? (·.1 == seedSetting)).map (·.2), settings
    reproduce := ctx.reproduce exe t.name settings, slowAfterMs := r.slowAfterMs }

/--
Runs one test in a process of its own, with the settings and limits resolved for it. Records from its
result file and lines from its standard output and standard error go to the dispatcher as they
arrive. Before a line of output is handed on, the result file is read up to its end, so the records
that the test wrote before that output precede it. The test is terminated at its timeout and killed
after the grace period. The run loop checks the clock after every bounded read of the result file.
Once the test executable has exited, the processes that it started have the pipe grace to release
its output pipes, and then its process group is swept. If {name}`t`'s mandatory setting has no
value, then it is reported with no process started. The result is {lean}`false` when the run has
been cancelled and the test was not started.
-/
def runOne (ctx : RunContext) (n : Nat) (t : InventoryTest) (r : Resolved) : IO Bool := do
  let exe := ctx.config.executables[t.exeIdx]!
  let planned := ctx.planned exe t r
  let d := ctx.dispatcher
  if let some missing := r.missing[0]? then
    d.dispatch (.testStarted planned)
    d.dispatch (.testEnded exe.name t.name (.settingMissing missing) 0)
    return true
  let file := ctx.dir / s!"run-{n}.jsonl"
  IO.FS.writeFile file ""
  let start ← IO.monoMsNow
  let ended (exit : Exit) : IO Unit := do
    d.dispatch (.testEnded exe.name t.name exit ((← IO.monoMsNow) - start))
  let spawned ←
    try
      let some cmd := exe.command[0]? | throw <| .userError "the command is empty"
      let g? ← ctx.registry.start <|
        spawnGroup cmd
          (exe.command.extract 1 exe.command.size ++ runArgs file.toString t.name planned.settings)
          exe.cwd? (ctx.env exe)
      pure (Except.ok g?)
    catch e => pure (.error (toString e))
  let g ← match spawned with
    | .ok none => return false
    | .ok (some g) =>
      d.dispatch (.testStarted planned)
      pure g
    | .error e =>
      d.dispatch (.testStarted planned)
      ended (.spawnFailed e)
      return true
  let tail ← Tail.open file
  let onFileLine (bytes : ByteArray) : IO Unit := do
    let line := decodeLine bytes
    if line.trimAscii.isEmpty then return
    match Protocol.Record.parseLine line with
    | .ok (some (json, record)) => d.dispatch (.record exe.name t.name json record)
    | .ok none => pure ()
    | .error e => d.dispatch (.unreadable exe.name t.name e)
  let fileLock ← Std.Mutex.new ()
  let pollFile : IO Bool := fileLock.atomically (tail.poll onFileLine)
  let forward (stream : String) (line : String) : IO Unit :=
    fileLock.atomically do
      -- The file is read to its end, a bounded read at a time, so that the records written before
      -- this line precede it. Reading stops at the test's timeout, which the run loop enforces.
      repeat
        if (← IO.monoMsNow) ≥ start + r.timeoutMs then break
        unless ← tail.poll onFileLine do break
      d.dispatch (.captured exe.name t.name stream line (← Protocol.nowMs))
  let outTask ← IO.asTask (prio := .dedicated) (forwardLines g.child.stdout (forward "stdout"))
  let errTask ← IO.asTask (prio := .dedicated) (forwardLines g.child.stderr (forward "stderr"))
  let mut timedOut : Option (Nat × Bool) := none
  repeat
    let read ← pollFile
    if (← g.tryWait).isSome then break
    let elapsed := (← IO.monoMsNow) - start
    if elapsed ≥ r.timeoutMs then
      let killed ← g.terminateGraceKill r.gracePeriodMs
      timedOut := some (elapsed, killed)
      break
    unless read do IO.sleep pollMs
  let code ← g.wait
  -- What a test that timed out wrote is read for at most the grace period more.
  let deadline? ← if timedOut.isSome then
      pure (some ((← IO.monoMsNow) + r.gracePeriodMs))
    else pure none
  fileLock.atomically (tail.finish onFileLine deadline?)
  releasePipes g [outTask, errTask]
  ctx.registry.release g
  let exit := match timedOut with
    | some (ms, killed) => Exit.timedOut ms killed
    | none => .exited code
  ended exit
  return true

/-- A value as a listing shows it, quoted so that an empty value shows. -/
private def showValue (v : String) : String := v.quote

/-- Text indented line by line. -/
private def indented (indent text : String) : String :=
  "\n".intercalate ((text.trimAscii.copy.splitOn "\n").map (indent ++ ·))

/-- The selected tests, grouped by their test executables in inventory order. -/
private def byExecutable (selected : Array (InventoryTest × Resolved)) :
    Array (Nat × Array (InventoryTest × Resolved)) :=
  selected.foldl (init := #[]) fun acc (t, r) =>
    match acc.back? with
    | some (i, group) =>
      if i == t.exeIdx then acc.pop.push (i, group.push (t, r)) else acc.push (t.exeIdx, #[(t, r)])
    | none => #[(t.exeIdx, #[(t, r)])]

/--
Prints the selected tests in nextest's human format: each test executable's name and a colon, then
its selected tests, indented by four spaces. With {name}`verbose`, the settings that the test
executables declare come first when there are any, with their descriptions and defaults; each test
is followed by its file and line, its tags, its description, and the values it receives; and the
mandatory settings that nothing gives a value come last, with the tests that need them. Seeds derived from a run seed
that the command line leaves to chance are shown as derived.
-/
def printHumanList (ctx : RunContext) (color verbose : Bool) (listings : Array Listing)
    (selected : Array (InventoryTest × Resolved)) : IO Unit := do
  let line := ctx.dispatcher.sinks.line
  -- The settings' heading is printed only when a test executable declares a setting.
  if verbose && listings.any (!·.settings.isEmpty) then
    line "Settings:"
    let mut shown : Std.HashSet String := {}
    for l in listings do
      for s in l.settings do
        if shown.contains s.name then continue
        shown := shown.insert s.name
        let dflt := match s.default? with | some d => s!" (default {showValue d})" | none => ""
        line s!"  {s.name}{dflt}"
        if let some d := s.description? then line (indented "      " d)
  let mut missing : Array (String × String) := #[]
  for (idx, tests) in byExecutable selected do
    line s!"{Style.exe.paint color ctx.config.executables[idx]!.name}:"
    for (t, r) in tests do
      let name := styleTestName color t.name t.path
      unless verbose do
        line s!"    {name}"
        continue
      let loc := match t.file?, t.line? with
        | some f, some l => s!"  ({f}:{l})"
        | some f, none => s!"  ({f})"
        | _, _ => ""
      let tags := if t.tags.isEmpty then "" else s!"  [{", ".intercalate t.tags.toList}]"
      line s!"    {name}{loc}{tags}"
      if let some d := t.description? then line (indented "        " d)
      for (k, v) in r.settings do
        -- Seeds derived from a random run seed differ in every run, so their values say nothing.
        if k == seedSetting && r.derivedSeed && ctx.opts.seed.isNone then
          line s!"        {k}: derived from the run's seed"
        else
          line s!"        {k} = {showValue v}"
      for m in r.missing do
        line s!"        {m}: no value"
        missing := missing.push (m, t.name)
  unless missing.isEmpty do
    line "Mandatory settings without a value:"
    for (m, t) in missing do
      line s!"  {m}, which {t} needs"

/--
Prints one line per selected test, in inventory order: the executable, the name, the file and line,
and the tags, in columns padded to their widest entry with two spaces between them.
-/
def printOnelineList (ctx : RunContext) (selected : Array (InventoryTest × Resolved)) :
    IO Unit := do
  let rows := selected.map fun (t, _) =>
    let loc := match t.file?, t.line? with
      | some f, some l => s!"{f}:{l}"
      | some f, none => f
      | _, _ => "-"
    let tags := if t.tags.isEmpty then "" else s!"[{", ".intercalate t.tags.toList}]"
    #[ctx.config.executables[t.exeIdx]!.name, t.name, loc, tags]
  let width (i : Nat) : Nat := rows.foldl (fun w r => max w (r[i]!.length)) 0
  let widths := #[width 0, width 1, width 2]
  for r in rows do
    let cols := (List.range 3).map fun i => r[i]!.pushn ' ' (widths[i]! - r[i]!.length)
    ctx.dispatcher.sinks.line ("  ".intercalate (cols ++ [r[3]!]) |>.trimAsciiEnd.copy)

/--
The selected tests as JSON: the profile, the run's seed, the number of listed tests selected and
left out, the names of the test executables that the filters ruled out before building, the
settings that the test executables declare, and each test executable with its selected tests.
Each test has its name, path, file, line, tags, and description, the values it receives, the
mandatory settings without a value, whether its seed is derived from the run's, and its timeout,
grace period, and slow mark in milliseconds.
-/
def inventoryJson (ctx : RunContext) (profile : String) (listings : Array Listing)
    (selected : Array (InventoryTest × Resolved)) (skipped : Nat) : Json := Id.run do
  let opt {α} [ToJson α] (key : String) (v? : Option α) : List (String × Json) :=
    (v?.map fun v => (key, ToJson.toJson v)).toList
  let mut settings : Array Json := #[]
  let mut seen : Std.HashSet String := {}
  for l in listings do
    for s in l.settings do
      if seen.contains s.name then continue
      seen := seen.insert s.name
      settings := settings.push <| Json.mkObj <| [("name", Json.str s.name)] ++
        opt "description" s.description? ++ opt "default" s.default?
  let testJson (t : InventoryTest) (r : Resolved) : Json := Json.mkObj <|
    [("name", Json.str t.name), ("path", ToJson.toJson t.path)] ++ opt "file" t.file? ++
    opt "line" t.line? ++ [("tags", ToJson.toJson t.tags)] ++ opt "description" t.description? ++
    [("settings", Json.mkObj (r.settings.toList.map fun (k, v) => (k, Json.str v))),
      ("missing", ToJson.toJson r.missing), ("derived-seed", Json.bool r.derivedSeed),
      ("timeout-ms", ToJson.toJson r.timeoutMs), ("grace-period-ms", ToJson.toJson r.gracePeriodMs),
      ("slow-after-ms", ToJson.toJson r.slowAfterMs)]
  let groups := byExecutable selected
  let executables := ctx.config.executables.mapIdx fun i e =>
    let tests := (groups.find? (·.1 == i)).map (·.2) |>.getD #[]
    Json.mkObj [("name", Json.str e.name), ("command", ToJson.toJson e.command),
      ("tests", Json.arr (tests.map fun (t, r) => testJson t r))]
  return Json.mkObj [("profile", Json.str profile), ("seed", ToJson.toJson ctx.runSeed),
    ("selected", ToJson.toJson selected.size), ("skipped", ToJson.toJson skipped),
    ("executables-skipped", ToJson.toJson ctx.config.ruledOut),
    ("settings", Json.arr settings), ("executables", Json.arr executables)]

/-- The message of a configuration that has no profile with the given name. -/
def unknownProfile (config : Config) (name : String) : String :=
  s!"the configuration has no profile named {name}; its profiles are \
    {", ".intercalate config.profileNames.toList}"

/--
The filters of a run, parsed: the selection, from the command line's filters and the profile's
default filter, or the configuration's when the profile has none, and each override's filter. The
result is the messages of the filters that do not parse, and of a default filter that contains
{lit}`default()`, with the exit code they end the run with: {name}`ExitCode.setupError` when a
filter of the configuration is among them, as nextest treats its configuration's filters, and
{name}`ExitCode.invalidFilter` otherwise.
-/
def parseSelection (config : Config) (opts : Options) (profile : Profile) :
    Except (Array String × UInt32) (Selection × Array (SourcedFilter × Override)) := do
  let mut errors := #[]
  let mut configErrors := false
  let mut defaultFilter? : Option SourcedFilter := none
  if let some f := profile.defaultFilter? <|> config.defaultFilter? then
    match SourcedFilter.parse f.text f.source with
    | .ok sf =>
      match sf.expr.defaultSpan? with
      | some span =>
        errors := errors.push s!"{sf.at span.start}: default() stands for the default filter, so \
          the default filter cannot contain it"
        configErrors := true
      | none => defaultFilter? := some sf
    | .error e =>
      errors := errors.push e
      configErrors := true
  let mut filters := #[]
  for f in opts.filters do
    match SourcedFilter.parse f (.argument "--filter") with
    | .ok sf => filters := filters.push sf
    | .error e => errors := errors.push e
  let mut overrides := #[]
  for o in profile.overrides do
    match SourcedFilter.parse o.filter.text o.filter.source with
    | .ok sf => overrides := overrides.push (sf, o)
    | .error e =>
      errors := errors.push e
      configErrors := true
  unless errors.isEmpty do
    throw (errors, if configErrors then ExitCode.setupError else ExitCode.invalidFilter)
  let selection : Selection := {
    filters, names := opts.nameFilters, skips := opts.skips, exact := opts.exact
    default? := defaultFilter?, useDefault := !opts.ignoreDefaultFilter }
  return (selection, overrides)

/--
Asks every test executable for its inventory, in parallel. The result is each executable's listing,
or {lean}`none` when one could not list, which the dispatcher has been told.
-/
def listAll (ctx : RunContext) : IO (Option (Array Listing)) := do
  let d := ctx.dispatcher
  let listings ← ctx.config.executables.mapIdxM fun i exe =>
    IO.asTask (prio := .dedicated) (listExecutable ctx i exe)
  let mut out := #[]
  let mut listed := true
  for task in listings do
    match ← IO.wait task with
    | .ok (.ok l) => out := out.push l
    | .ok (.error msg) =>
      listed := false
      d.dispatch (.issue { isError := true, message := msg })
    | .error e =>
      listed := false
      d.dispatch (.issue { isError := true, message := s!"a test executable could not list: {e}" })
  return if listed then some out else none

/--
The message of a run that selects no test under {lit}`--no-tests fail`.
-/
def noTestsMessage : String :=
  "no tests to run; --no-tests warn or --no-tests pass accepts a run that selects none"

/--
Runs or lists the tests of every test executable in the configuration, reporting to {name}`sinks` as
the run proceeds, and returns the report with the exit code. The events file's lines and the
human-readable report's lines go to the sinks; the report files are the caller's to write. The
{lit}`protocol` line of the events file is sent first. The human-readable report is colored when
{name}`color` is true.

Filters with syntax errors, unknown profiles, and profiles whose {lit}`jobs` is above one end the
run before the List phase. The List phase lists every executable, then checks the configuration
against the inventory: values that the command line gives to settings that no executable declares
are errors, and those that the profile gives are warnings; the filters are evaluated, with a warning
for each atom and each filter that selects nothing. The configuration's filters draw these warnings
only when the run has every test executable of the package. The {lit}`list` command then prints the
selected tests in its message format. The Run phase runs the selected tests in inventory order.
-/
def execute (config : Config) (opts : Options) (sinks : Sinks)
    (registry : Option Registry := none) (color : Bool := false) : IO (RunReport × UInt32) := do
  let runSeed ← match opts.seed with
    | some s => pure s
    | none => IO.rand 0 (2 ^ 32 - 1)
  let runId ← newRunId
  let listing := opts.command == .list
  -- A listing prints no results, so its reporter prints nothing of its own.
  let human : HumanReporter := { verbosity := if listing then .silent else opts.verbosity, color }
  let dispatcher : Dispatcher :=
    { state := ← Std.Mutex.new { human, wfail := opts.wfail, startMs := ← Protocol.nowMs }, sinks }
  sinks.event (Json.mkObj [("type", Json.str "protocol"), ("version", ToJson.toJson Protocol.version),
    ("run_id", Json.str runId)])
  let registry ← match registry with
    | some r => pure r
    | none => Registry.new
  let d := dispatcher
  let finish (code : UInt32) (skipped? : Option (Nat × Nat) := none) :
      IO (RunReport × UInt32) := do
    -- A listing runs nothing, so it has no counts to sum up.
    d.dispatch (.ended (← Protocol.nowMs) (!listing) skipped?)
    let s ← d.get
    return ({ results := s.results, issues := s.issues, seed := runSeed, runId }, code)
  for w in config.warnings do
    d.dispatch (.issue { isError := false, message := w })
  let some profile := config.profile? opts.profile
    | d.dispatch (.issue { isError := true, message := unknownProfile config opts.profile })
      finish ExitCode.setupError
  if let some jobs := profile.jobs? then
    unless jobs == 1 do
      d.dispatch (.issue { isError := true, message := s!"the profile {profile.name} sets jobs to \
        {jobs}: only 1 is supported" })
      return ← finish ExitCode.setupError
  let (selection, overrides) ← match parseSelection config opts profile with
    | .ok fs => pure fs
    | .error (errors, code) =>
      for e in errors do d.dispatch (.issue { isError := true, message := e })
      return ← finish code
  IO.FS.withTempDir fun dir => do
    let ctx : RunContext := {
      config, opts, runSeed, runId, dir, dispatcher, registry
      listTimeoutMs := opts.timeoutMs? <|> profile.timeoutMs? |>.getD defaultTimeoutMs
      listGracePeriodMs := opts.gracePeriodMs? <|> profile.gracePeriodMs? |>.getD defaultGracePeriodMs
    }
    d.dispatch (.phase "List" (← Protocol.nowMs))
    let some listings ← listAll ctx | finish ExitCode.listFailed
    let inventory := listings.flatMap (·.tests)
    let exeName (t : InventoryTest) : String := config.executables[t.exeIdx]!.name
    let resolution : ResolutionContext := {
      sets := opts.sets, profile, overrides, timeoutMs? := opts.timeoutMs?
      gracePeriodMs? := opts.gracePeriodMs?, updateGolden := opts.updateGolden, runSeed
      default? := selection.default?
    }
    -- Values that the command line gives to settings that nothing declares stop the run. Those that
    -- the configuration gives are warnings, since profiles serve the executables of every library
    -- and runs may select some of them.
    let declared := listings.flatMap (·.settings.map (·.name))
    let undeclared := resolution.undeclared declared
    let names := declared.foldl (init := #[]) fun acc n => if acc.contains n then acc else acc.push n
    for u in undeclared do
      d.dispatch (.issue { isError := u.commandLine, message := s!"{u.place} gives the setting \
        {u.name} a value, and no test executable of this run declares it; the declared settings are \
        {if names.isEmpty then "none" else ", ".intercalate names.toList}" })
    if undeclared.any (·.commandLine) then return ← finish ExitCode.setupError
    let records := inventory.map fun t => t.record (exeName t)
    -- An `exe(…)` is judged against every executable of the package, those that the filters ruled
    -- out before building included.
    let exes := config.executableNames
    -- The configuration's filters serve every executable of the package, so they are checked
    -- against the inventory only when the run has all of them. The command line's always are.
    let checked := selection.filters ++
      (if config.partialSelection then #[] else selection.default?.toArray ++ overrides.map (·.1))
    for f in checked do
      for w in f.warnings records exes selection.defaultSelects do
        d.dispatch (.issue { isError := false, message := w })
    let selected := inventory.filterMap fun t =>
      if selection.selects (t.record (exeName t)) then
        some (t, resolution.resolve (exeName t) listings[t.exeIdx]!.settings t)
      else none
    let skipped := inventory.size - selected.size
    if listing then
      match opts.messageFormat with
      | .human => printHumanList ctx color (opts.verbosity != .silent) listings selected
      | .oneline => printOnelineList ctx selected
      | .json => sinks.line (inventoryJson ctx profile.name listings selected skipped).compress
      | .jsonPretty => sinks.line (inventoryJson ctx profile.name listings selected skipped).pretty
      return ← finish ExitCode.ok
    if selected.isEmpty then
      match opts.noTests with
      | .fail => d.dispatch (.issue { isError := true, message := noTestsMessage })
      | .warn => d.dispatch (.issue { isError := false, message := "no tests to run" })
      | .pass => pure ()
    d.dispatch (.phase "Run" (← Protocol.nowMs))
    for h : i in [0 : selected.size] do
      let (t, r) := selected[i]
      unless ← runOne ctx i t r do break
    let s ← d.get
    -- Under `--wfail`, the warning of `--no-tests warn` fails the run as `--no-tests fail` does.
    let code :=
      if selected.isEmpty && (opts.noTests == .fail || (opts.noTests == .warn && opts.wfail)) then
        ExitCode.noTestsRun
      else if s.results.all (·.outcome.isPass) && !s.issues.any (·.isError) then ExitCode.ok
      else ExitCode.testRunFailed
    finish code (skipped, config.ruledOut.size)

/--
The paths of the JUnit, JSON, and Markdown reports: the command line's, or else the profile's, which
are relative to the package's directory.
-/
def reportPaths (config : Config) (opts : Options) :
    Option String × Option String × Option String :=
  let profile? := config.profile? opts.profile
  let fromProfile (field : Profile → Option String) : Option String :=
    (profile?.bind field).map fun (p : String) =>
      match config.packageDir? with
      | some dir => (System.FilePath.mk dir / System.FilePath.mk p).toString
      | none => p
  (opts.junitPath <|> fromProfile (·.junitPath?), opts.jsonPath <|> fromProfile (·.jsonPath?),
    opts.markdownPath <|> fromProfile (·.markdownPath?))

/-- Writes the report files at the paths that {name}`reportPaths` gives. -/
def writeReports (config : Config) (opts : Options) (report : RunReport) : IO Unit := do
  let (junit?, json?, markdown?) := reportPaths config opts
  let write (path? : Option String) (render : RunReport → String) : IO Unit := do
    if let some path := path? then writeFile path (render report)
  write junit? junitReport
  write json? jsonReport
  write markdown? markdownReport

/--
Runs or lists the tests as {name}`execute` does, with the human-readable output on standard output,
colored when {name}`color` is true, and the events in the file that the options name; then writes
the report files of a run and prints the issues. The result is {name}`execute`'s exit code. A
cancelled run writes no report files and returns {name}`ExitCode.other`.
-/
def executeAndWrite (config : Config) (opts : Options)
    (registry : Option Registry := none) (color : Bool := false) : IO UInt32 := do
  let registry ← match registry with
    | some r => pure r
    | none => Registry.new
  let events? ← opts.eventsPath.mapM fun p => do
    if let some parent := (p : System.FilePath).parent then IO.FS.createDirAll parent
    IO.FS.Handle.mk p .append
  let sinks : Sinks := {
    event := fun j => do
      if let some h := events? then
        h.putStr (j.compress ++ "\n")
        h.flush
    line := fun l => do
      IO.println l
      (← IO.getStdout).flush
  }
  let (report, code) ← execute config opts sinks registry color
  -- A cancelled run writes no reports.
  if ← registry.cancelled then return ExitCode.other
  if opts.command == .run then writeReports config opts report
  for issue in report.issues do
    IO.eprintln s!"{issue.level}: {issue.message}"
  return code

/--
Cancels the run once the runner's lifeline, its standard input, closes: every later start is
refused, and the running processes are terminated and, after the grace period, killed. The driver
holds the other end of that pipe, which closes when the driver exits, however it exits. After the
cancellation, the run loop has the grace period, four pipe graces, and two more seconds to end, and
then the runner exits with {lit}`1`.
-/
def exitWhenStdinCloses (parentIn : IO.FS.Stream) (registry : Registry) (graceMs : Nat) :
    IO Unit := do
  repeat
    if (← parentIn.getLine).isEmpty then break
  try IO.eprintln "errata-runner: standard input closed, so the run ends" catch _ => pure ()
  registry.cancel graceMs
  -- The run loop reaps the processes and ends what they left holding their pipes; this bounds how
  -- long that may take.
  IO.sleep (graceMs + 4 * pipeGraceMs + 2000).toUInt32
  try (← IO.getStdout).flush catch _ => pure ()
  IO.Process.forceExit 1

/--
Whether the human-readable output is colored, from the choice, the environment variable lookup
{name}`env`, and whether standard output is a terminal. For {lit}`auto`, a
{lit}`CLICOLOR_FORCE` that is set and is not {lit}`0` forces color, and otherwise a
{lit}`NO_COLOR` that is set and not empty disables it; without either, the output is colored when
it goes to a terminal.
-/
def colorOf (choice : ColorChoice) (env : String → Option String) (terminal : Bool) : Bool :=
  match choice with
  | .always => true
  | .never => false
  | .auto =>
    if (env "CLICOLOR_FORCE").any (fun v => !v.isEmpty && v != "0") then true
    else if (env "NO_COLOR").any (!·.isEmpty) then false
    else terminal

/-- Whether this process colors its human-readable output, as {name}`colorOf` decides. -/
def useColor (choice : ColorChoice) : IO Bool := do
  let force ← IO.getEnv "CLICOLOR_FORCE"
  let noColor ← IO.getEnv "NO_COLOR"
  let env (name : String) : Option String :=
    if name == "CLICOLOR_FORCE" then force else if name == "NO_COLOR" then noColor else none
  return colorOf choice env (← (← IO.getStdout).isTty)

/--
Reports a command line that could not be read, with the way to the usage text, and returns
{name}`ExitCode.usage`. When the command line asks for the usage text anywhere, prints it instead
and returns {name}`ExitCode.ok`.
-/
def badCommandLine (args : List String) (invocation message : String) : IO UInt32 := do
  if args.any (fun a => a == "--help" || a == "-h") then
    IO.print (usage invocation)
    return ExitCode.ok
  IO.eprintln s!"error: {message}"
  IO.eprintln s!"Run `{invocation} --help` for the options."
  return ExitCode.usage

/--
The driver's planning mode, {lit}`errata-runner errata-plan REQUEST OUT ARGS...`, which the driver
runs before it builds any test executable. {name}`request` is a JSON object with the path of
{lit}`config.json` under {lit}`config`, the command that the arguments follow under
{lit}`invocation`, and the names of the test executables that the package can have under
{lit}`executables`. The mode reads the command line {name}`args` as a run would, checks the profile
and the filters, and writes to the file {name}`out` a JSON object with the command, the profile,
the executables that the filters do not rule out by their names alone, whether the targets that
the profile's settings need must be built, and whether the phases are named as they begin. When the
command line asks for the usage text, the mode prints it and writes {lit}`{"help": true}`. The
result is the exit code: {name}`ExitCode.ok`, or the code of the problem, which the mode reports.
-/
def plan (request out : String) (args : List String) : IO UInt32 := do
  let req ← IO.ofExcept (Json.parse request)
  let invocation := (req.getObjValAs? String "invocation").toOption.getD "errata-runner"
  let configPath ← IO.ofExcept (req.getObjValAs? String "config")
  let candidates := (req.getObjValAs? (Array String) "executables").toOption.getD #[]
  let write (j : Json) : IO Unit := IO.FS.writeFile out (j.compress ++ "\n")
  let opts ← match parseCommandLine args (← IO.getEnv "ERRATA_PROFILE") with
    | .ok opts => pure opts
    | .error msg =>
      let code ← badCommandLine args invocation msg
      if code == ExitCode.ok then write (Json.mkObj [("help", Json.bool true)])
      return code
  if opts.help then
    IO.print (usage invocation)
    write (Json.mkObj [("help", Json.bool true)])
    return ExitCode.ok
  let config ←
    try IO.ofExcept (Config.ofJson (← readJsonFile configPath) (Json.mkObj []) none)
    catch e =>
      IO.eprintln s!"error: {e}"
      return ExitCode.setupError
  let some profile := config.profile? opts.profile
    | IO.eprintln s!"error: {unknownProfile config opts.profile}"
      return ExitCode.setupError
  match parseSelection config opts profile with
  | .error (errors, code) =>
    for e in errors do IO.eprintln s!"error: {e}"
    return code
  | .ok (selection, _) =>
    write <| Json.mkObj [("command", Json.str opts.command.name),
      ("profile", Json.str profile.name),
      ("executables", ToJson.toJson (candidates.filter selection.mayContain)),
      ("needs", Json.bool opts.resolvesSettings),
      ("phases", Json.bool (opts.command == .run && opts.verbosity.showsPasses))]
    return ExitCode.ok

/--
The runner's entry point: {lit}`errata-runner CONFIG WORKSPACE [run|list] [OPTIONS]
[NAME-FILTER]... [-- NAME-FILTER...]`, where {lit}`CONFIG` is the {lit}`config.json` that
{lit}`errata-config` writes and {lit}`WORKSPACE` the {lit}`workspace.json` that the driver writes;
or {lit}`errata-runner errata-plan …`, which {name}`plan` describes. The workspace's
{lit}`invocation`, when it has one, names the command in the usage text. When
{lit}`ERRATA_LIFELINE` is {lit}`1` in its environment, the runner watches its standard input and
cancels the run when it closes. The profile is {lit}`ERRATA_PROFILE` when the command line names
none.
-/
def main (args : List String) : IO UInt32 := do
  if let "errata-plan" :: request :: out :: rest := args then
    return ← plan request out rest
  let invocation ← do
    match args with
    | _ :: path :: _ =>
      if path.startsWith "-" then pure none
      else
        try pure ((← readJsonFile path).getObjValAs? String "invocation").toOption
        catch _ => pure none
    | _ => pure none
  let invocation := invocation.getD "errata-runner CONFIG WORKSPACE"
  let opts ← match parseOptions args (← IO.getEnv "ERRATA_PROFILE") with
    | .ok opts => pure opts
    | .error msg => return ← badCommandLine args invocation msg
  if opts.help then
    IO.print (usage invocation)
    return ExitCode.ok
  -- The targets that the profile's settings need are built for a run, and for a listing that shows
  -- what each test receives.
  let required? := if opts.resolvesSettings then some opts.profile else none
  let config ←
    try Config.load opts.configPath opts.workspacePath required?
    catch e =>
      IO.eprintln s!"error: {e}"
      return ExitCode.setupError
  let registry ← Registry.new
  let grace := opts.gracePeriodMs?.getD defaultGracePeriodMs
  -- The driver sets the variable when it gives the runner a standard input to watch.
  if (← IO.getEnv lifelineVariable) == some "1" then
    let _ ← IO.asTask (prio := .dedicated) (exitWhenStdinCloses (← IO.getStdin) registry grace)
  let code ← executeAndWrite config opts (some registry) (← useColor opts.color)
  try (← IO.getStdout).flush catch _ => pure ()
  try (← IO.getStderr).flush catch _ => pure ()
  -- The thread that reads standard input runs until the pipe closes, and a Lean program that
  -- returns from `main` waits for its threads, so the runner ends the process itself.
  IO.Process.forceExit code.toUInt8
