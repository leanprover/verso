/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Starting processes in groups of their own, following what they write, and ending them together with
everything they started.
-/
module

public import Init.System.IO
public import Init.System.Platform
public import Init.Data.String

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata.ProcessControl

/-- The standard streams of a process in a group: all three are pipes. -/
abbrev PipedConfig : IO.Process.StdioConfig :=
  { stdin := .piped, stdout := .piped, stderr := .piped }

/--
A process started in a session and process group of its own. A signal to the group reaches
everything the process started. Its standard input is a lifeline: when the pipe closes, a process
that watches its standard input learns that the process which started it has ended.

The group's identifier is the process's own. The group is signaled only while it is armed. It is
disarmed when {lit}`Group.tryWait` or {lit}`Group.wait` reports the exit.
-/
structure Group where
  /-- The process. -/
  child : IO.Process.Child PipedConfig
  /-- The process's identifier, which is also its group's. -/
  pid : UInt32
  /-- Whether the process is still to be waited for. -/
  armed : IO.Ref Bool
  /-- The exit code, once the process has been waited for. -/
  exitCode : IO.Ref (Option UInt32)

/--
Whether a command can be found from the directory {name}`cwd`: a command with a directory in it
names a file relative to that directory, and any other command is looked for on {name}`path?`, or on
this process's {lit}`PATH` when that is {lean}`none`. The check looks only for the file.
-/
def commandExists (cmd : String) (cwd : Option System.FilePath := none)
    (path? : Option String := none) : IO Bool := do
  let isFile (p : System.FilePath) : IO Bool := do
    try return (← p.metadata).type != .dir catch _ => return false
  if cmd.contains '/' || (System.Platform.isWindows && cmd.contains '\\') then
    let path : System.FilePath := cmd
    isFile (if path.isAbsolute then path else (cwd.getD ".") / path)
  else
    let searchPath ← match path? with
      | some p => pure p
      | none => pure ((← IO.getEnv "PATH").getD "")
    let dirs := searchPath.splitOn System.SearchPath.separator.toString
    for dir in dirs do
      unless dir.isEmpty do
        if ← isFile (dir / cmd) then return true
        if System.Platform.isWindows then
          if ← isFile (dir / (cmd ++ ".exe")) then return true
    return false

/--
The operating system's identifier of the child process. The runtime's function reads the child and
leaves it with the caller, as the borrowed parameter here says, so the child's pipes close when the
caller's last reference to it goes.
-/
@[extern "lean_io_process_child_pid"]
opaque childPid {cfg : @& IO.Process.StdioConfig} : @& IO.Process.Child cfg → UInt32

/--
Starts a process in a group of its own. The command and the working directory are checked first,
and a missing one is an error here. A command without a directory is looked for on the
{lit}`PATH` that {name}`env` sets, when it sets one.
-/
def spawnGroup (cmd : String) (args : Array String) (cwd : Option System.FilePath := none)
    (env : Array (String × Option String) := #[]) : IO Group := do
  if let some dir := cwd then
    unless ← dir.isDir do
      throw <| .userError s!"the working directory {dir} does not exist"
  let path? := (env.findRev? (·.1 == "PATH")).map (·.2.getD "")
  unless ← commandExists cmd cwd path? do
    throw <| .userError s!"the command {cmd} was not found"
  let child ← IO.Process.spawn {
    cmd, args, cwd, env, setsid := true
    stdin := .piped, stdout := .piped, stderr := .piped
  }
  return { child, pid := childPid child, armed := ← IO.mkRef true, exitCode := ← IO.mkRef none }

/-- The exit code, if the process has exited. A process that has exited is disarmed. -/
def Group.tryWait (g : Group) : IO (Option UInt32) := do
  if let some c ← g.exitCode.get then return some c
  let c? ← g.child.tryWait
  if let some c := c? then
    g.armed.set false
    g.exitCode.set (some c)
  return c?

/-- Waits for the process to exit and returns its exit code. The process is then disarmed. -/
def Group.wait (g : Group) : IO UInt32 := do
  if let some c ← g.exitCode.get then return c
  let c ← g.child.wait
  g.armed.set false
  g.exitCode.set (some c)
  return c

/--
Sends a signal to every process in the group {name}`pgid`, by running the system's {lit}`kill`.
The result says whether the group had a member to receive it. The signal is named as {lit}`kill`
names it, such as {lit}`TERM`, {lit}`KILL`, or {lit}`0`, which only checks that the group exists.
-/
def signalGroup (signal : String) (pgid : UInt32) : IO Bool := do
  if System.Platform.isWindows then
    if signal == "0" then return false
    let out ← IO.Process.output { cmd := "taskkill", args := #["/T", "/F", "/PID", toString pgid] }
    return out.exitCode == 0
  try
    let out ← IO.Process.output {
      cmd := "kill", args := #[s!"-{signal}", "--", s!"-{pgid}"], stdin := .null
    }
    return out.exitCode == 0
  catch _ =>
    return false

/--
Asks the group to terminate, with {lit}`SIGTERM` sent by the system's {lit}`kill`, while the process
is armed.
-/
def Group.terminate (g : Group) : IO Unit := do
  if ← g.armed.get then discard <| signalGroup "TERM" g.pid

/-- Kills the group, with {lit}`SIGKILL`, while the process is armed. -/
def Group.kill (g : Group) : IO Unit := do
  if ← g.armed.get then
    -- `Child.kill` fails while the process is still making its group. The system's `kill` is the
    -- second attempt.
    try g.child.kill catch _ => discard <| signalGroup "KILL" g.pid

/-- How long to wait between checks on a process, in milliseconds. -/
def pollMs : UInt32 := 15

/-- Waits up to {name}`ms` milliseconds for the process to exit. Returns whether it has. -/
partial def Group.waitAtMost (g : Group) (ms : Nat) : IO Bool := do
  let deadline := (← IO.monoMsNow) + ms
  let rec loop : IO Bool := do
    if (← g.tryWait).isSome then return true
    if (← IO.monoMsNow) ≥ deadline then return false
    IO.sleep pollMs
    loop
  loop

/--
Ends the process: asks its group to terminate, gives it {name}`graceMs` milliseconds, then kills the
group. The result says whether the kill was needed.
-/
def Group.terminateGraceKill (g : Group) (graceMs : Nat) : IO Bool := do
  g.terminate
  if ← g.waitAtMost graceMs then return false
  g.kill
  discard g.wait
  return true

/--
Ends what remains of the group after its first process has been waited for. It asks the group to
terminate, and returns if the group has no member to receive the signal. Otherwise it checks the
group every {name}`pollMs` milliseconds, returns once the group is empty, and kills the group if it
still has members after {name}`graceMs` milliseconds. It is meant for a group whose members still
hold the first process's output pipes open. On Windows it returns at once.
-/
partial def Group.sweep (g : Group) (graceMs : Nat) : IO Unit := do
  if System.Platform.isWindows then return
  unless ← signalGroup "TERM" g.pid do return
  let deadline := (← IO.monoMsNow) + graceMs
  let rec loop : IO Unit := do
    unless ← signalGroup "0" g.pid do return
    if (← IO.monoMsNow) ≥ deadline then
      discard <| signalGroup "KILL" g.pid
      return
    IO.sleep pollMs
    loop
  loop

/--
Asks every process in this process's own group to terminate, this process included. A test
executable that the runner started leads a group of its own, so this ends everything the test
started.
-/
def killOwnGroup : IO Unit := do
  discard <| signalGroup "TERM" (← IO.Process.getPID)

/--
Bytes that arrive in pieces, split into lines at newline bytes. A piece may end within a line, or
within a character, and the bytes wait for the piece that completes the line.
-/
structure LineBuffer where
  /-- The bytes of the incomplete line. -/
  pending : ByteArray := .empty

/-- Adds bytes, returning the lines that they complete, without their newlines. -/
def LineBuffer.push (buf : LineBuffer) (bytes : ByteArray) : Array ByteArray × LineBuffer := Id.run do
  let all := buf.pending ++ bytes
  let mut lines := #[]
  let mut start := 0
  for i in [buf.pending.size : all.size] do
    if all[i]! == '\n'.toUInt8 then
      lines := lines.push (all.extract start i)
      start := i + 1
  return (lines, { pending := all.extract start all.size })

/--
Decodes the bytes of a line as UTF-8. When the line is not valid UTF-8, each byte of {lit}`0x80` or
above becomes {lit}`U+FFFD`.
-/
def decodeLine (bytes : ByteArray) : String :=
  match String.fromUTF8? bytes with
  | some s => s
  | none => String.ofList <| bytes.toList.map fun b =>
    if b < 0x80 then Char.ofNat b.toNat else '�'

/--
A file that another process appends lines to, read as it grows. Reads are of at most 64 KiB, and a
line is handed on once all of it has arrived.
-/
structure Tail where
  /-- The file, opened for reading. -/
  handle : IO.FS.Handle
  /-- The bytes of the line being read. -/
  buffer : IO.Ref LineBuffer

/-- Opens a file to follow. -/
def Tail.open (path : System.FilePath) : IO Tail := do
  return { handle := ← IO.FS.Handle.mk path .read, buffer := ← IO.mkRef {} }

/--
Reads what has arrived, in at most {name}`maxReads` reads, and hands on each complete line. Returns
whether anything arrived. A caller that must also watch the clock calls it again while it returns
{lean}`true`.
-/
def Tail.poll (t : Tail) (onLine : ByteArray → IO Unit) (maxReads : Nat := 16) : IO Bool := do
  let mut any := false
  for _ in [0 : maxReads] do
    let bytes ← t.handle.read 65536
    if bytes.isEmpty then break
    any := true
    let (lines, buf) := (← t.buffer.get).push bytes
    t.buffer.set buf
    for l in lines do onLine l
  return any

/--
Reads the rest of the file and hands on its last line, which may lack a newline. With a deadline, in
milliseconds of {name}`IO.monoMsNow`, reading stops there and the rest of the file is left unread.
-/
def Tail.finish (t : Tail) (onLine : ByteArray → IO Unit) (deadline? : Option Nat := none) :
    IO Unit := do
  repeat
    if let some d := deadline? then
      if (← IO.monoMsNow) ≥ d then return
    unless ← t.poll onLine do break
  let rest := (← t.buffer.get).pending
  t.buffer.set {}
  unless rest.isEmpty do onLine rest

/--
Follows the file until {name}`exited` says that its writer has exited, then reads what is left.
The file is checked again every {name}`pollMs` milliseconds when nothing new has arrived.
-/
def Tail.follow (t : Tail) (exited : IO Bool) (onLine : ByteArray → IO Unit) : IO Unit := do
  repeat
    if ← t.poll onLine then continue
    if ← exited then break
    IO.sleep pollMs
  t.finish onLine

/-- Hands on each line read from {name}`handle` until it closes, keeping each line's newline. -/
partial def forwardLines (handle : IO.FS.Handle) (onLine : String → IO Unit) : IO Unit := do
  let line ← handle.getLine
  if line.isEmpty then return
  onLine line
  forwardLines handle onLine

/--
Waits until every task has finished, or until {name}`ms` milliseconds have passed. Returns whether
every task has finished.
-/
def waitAtMost (ms : Nat) (tasks : List (Task (Except IO.Error Unit))) : IO Bool := do
  let allDone ← IO.mapTasks (fun _ => pure ()) tasks
  let timeout ← IO.asTask (prio := .dedicated) (IO.sleep ms.toUInt32)
  discard <| IO.waitAny [allDone, timeout]
  IO.hasFinished allDone

/-- The number of CPUs in a list such as {lit}`0-3,8,10-11`, or {lean}`none` if it is malformed. -/
def countCpuList (s : String) : Option Nat := do
  let mut n := 0
  for part in s.trimAscii.copy.splitOn "," do
    let part := part.trimAscii.copy
    if part.isEmpty then continue
    match part.splitOn "-" with
    | [a] => let _ ← a.toNat?; n := n + 1
    | [a, b] =>
      let a ← a.toNat?
      let b ← b.toNat?
      if b < a then none
      n := n + (b - a + 1)
    | _ => none
  return n

/-- The CPUs this process may run on, from the Linux {lit}`/proc/self/status` file. -/
private def allowedCpus : IO (Option Nat) := do
  let text ← try IO.FS.readFile "/proc/self/status" catch _ => return none
  for line in text.splitOn "\n" do
    if let some rest := line.dropPrefix? "Cpus_allowed_list:" then
      return countCpuList rest.copy
  return none

/-- The ceiling of a quota over a period, when both are positive. -/
private def quotaCpus (quota period : String) : Option Nat := do
  let q ← quota.trimAscii.copy.toNat?
  let p ← period.trimAscii.copy.toNat?
  if q == 0 || p == 0 then none
  return (q + p - 1) / p

/--
The CPUs that this process's cgroup allows it, from the cgroup's {lit}`cpu.max` (version 2) or its
{lit}`cpu.cfs_quota_us` and {lit}`cpu.cfs_period_us` (version 1), when a quota is set.
-/
private def cgroupCpus : IO (Option Nat) := do
  let read (p : System.FilePath) : IO (Option String) :=
    try some <$> IO.FS.readFile p catch _ => pure none
  let mut dirs : Array System.FilePath := #["/sys/fs/cgroup"]
  if let some cg ← read "/proc/self/cgroup" then
    for line in cg.splitOn "\n" do
      if let some path := line.dropPrefix? "0::" then
        dirs := dirs.push ("/sys/fs/cgroup" ++ path.copy.trimAscii.copy)
  for dir in dirs.reverse do
    if let some max ← read (dir / "cpu.max") then
      match max.trimAscii.copy.splitOn " " with
      | [q, p] => return quotaCpus q p
      | _ => pure ()
  for dir in ["/sys/fs/cgroup/cpu", "/sys/fs/cgroup/cpu,cpuacct"] do
    let dir : System.FilePath := dir
    if let (some q, some p) := (← read (dir / "cpu.cfs_quota_us"), ← read (dir / "cpu.cfs_period_us")) then
      return quotaCpus q p
  return none

/--
The number of tests that may run at once by default: the least of the machine's hardware threads,
the CPUs that the process may run on, and the CPUs that its cgroup's quota allows. When none of them
is known, the result is one, with a warning to report.
-/
def availableParallelism : IO (Nat × Option String) := do
  let hw := (System.Platform.Internal.getHardwareConcurrency ()).toNat
  let known := [if hw == 0 then none else some hw, ← allowedCpus, ← cgroupCpus].filterMap id
  match known.min? with
  | some n => if n == 0 then pure (1, some warning) else pure (n, none)
  | none => pure (1, some warning)
where
  warning := "the number of CPUs available could not be determined, so tests run one at a time"
