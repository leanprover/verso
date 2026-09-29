/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Lsp.Ipc
import Lean.Server.Test.Runner
import Lean.Server.FileWorker.WidgetRequests
import VersoUtil.Elan

set_option doc.verso true

/-!
A client of the Lean language server for the tests and benchmarks. It starts {lit}`lake serve` in a
Lake workspace so that documents can import the workspace's libraries. It communicates with the
server over LSP as an editor does. Diagnostics are read through the server's interactive
diagnostics, with their trace messages expanded into text.
-/

namespace VersoGen.Server

open Lean Lean.Lsp Lean.JsonRpc

open Lean.Server.Test.Runner.Client (InteractiveDiagnostic MsgEmbed StrictOrLazy)

/--
The directory for the files that the tests and benchmarks generate in the Lake workspace at
{name}`root`. It is below the workspace's {lit}`.lake` directory, which git ignores.
-/
public def scratchDir (root : System.FilePath) (name : String) : System.FilePath :=
  root / ".lake" / "versogen" / name

/--
A language server session, with the ID of its next request and an action that stops the server's
processes.
-/
public structure Server where
  nextId : IO.Ref Nat
  stop : IO Unit

/-- Whether {name}`task` finishes within {name}`ms` milliseconds. -/
def taskFinishesWithin {β : Type} (ms : Nat) (task : Task β) : IO Bool := do
  let start ← IO.monoMsNow
  while !(← IO.hasFinished task) do
    if (← IO.monoMsNow) - start ≥ ms then return false
    IO.sleep 10
  return true

/--
Runs {name}`act` in a task of its own and waits for it for at most {name}`ms` milliseconds. The
result is {name}`none` if {name}`act` doesn't finish in time, and the task then keeps running.
-/
def finishesWithin {α : Type} (ms : Nat) (act : IO α) : IO (Option α) := do
  let task ← IO.asTask act .dedicated
  if ← taskFinishesWithin ms task then return some (← IO.ofExcept task.get) else return none

/-- How long a server's processes have to exit after {lit}`SIGTERM`, in milliseconds. -/
def terminationDeadline : Nat := 1000

/--
Stops the process group of a server that was started with {lit}`setsid`: {lit}`lake serve`, its
{lit}`lean --server` and the file workers. Processes that ignore {lit}`SIGTERM` for a second, such
as stopped ones, get {lit}`SIGKILL`. Errors are ignored, since the processes may have exited
already.
-/
def stopProcessGroup (child : IO.Process.Child Ipc.ipcStdioConfig) : IO Unit := do
  try child.kill catch _ => pure ()
  let exited ← IO.asTask child.wait .dedicated
  unless ← taskFinishesWithin terminationDeadline exited do
    try discard <| IO.Process.output { cmd := "kill", args := #["-KILL", s!"-{child.pid}"] }
    catch _ => pure ()
    discard <| IO.wait exited

def Server.freshId (server : Server) : IO Nat :=
  server.nextId.modifyGet fun n => (n, n + 1)

/-- Sends a request and waits for its response, discarding notifications in between. -/
def Server.request (server : Server) (method : String) [ToJson α] (params : α) (β)
    [FromJson β] : Ipc.IpcM β := do
  let id ← server.freshId
  Ipc.writeRequest ⟨id, method, params⟩
  return (← Ipc.readResponseAs id β).result

/-- Sends a request, giving the error as text if the server answers with an error. -/
public def Server.request? (server : Server) (method : String) [ToJson α] (params : α) :
    Ipc.IpcM (Except String Json) := do
  try return .ok (← server.request method params Json)
  catch e => return .error (toString e)

/-- Initializes the server in the same way as {name}`Lean.Server.Test.Runner.main`. -/
def initializeServer : Ipc.IpcM Unit := do
  let initializationOptions? := some {
    hasWidgets? := some true
    logCfg? := none
  }
  let capabilities := {
    textDocument? := some {
      completion? := some {
        completionItem? := some {
          insertReplaceSupport? := true
        }
      }
    }
    lean? := some {
      incrementalDiagnosticSupport? := some true
      silentDiagnosticSupport? := some true
      rpcWireFormat? := some .v1
    }
  }
  Ipc.writeRequest ⟨0, "initialize", { initializationOptions?, capabilities : InitializeParams }⟩
  let _ ← Ipc.readResponseAs 0 InitializeResult
  Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩

/-- How long a server has to answer the shutdown request and exit, in milliseconds. -/
def shutdownDeadline : Nat := 10000

/--
Runs {name}`act` in a session of {lit}`lake serve` in the Lake workspace at {name}`root`, then shuts
the server down.

Lean receives {name}`options`. The server is shut down also when {name}`act` throws. It runs in a
process group of its own, and the whole group is stopped when the server doesn't answer the shutdown
request and exit within ten seconds or when the shutdown fails.
-/
public def withServer (root : System.FilePath) (options : Array String)
    (act : Server → Ipc.IpcM α) : IO α := do
  let child ← IO.Process.spawn {
    Verso.Elan.getSpawnArgsForLake (#["serve", "--"] ++ options) (cwd := some root) with
    toStdioConfig := Ipc.ipcStdioConfig, setsid := true
  }
  let server : Server := { nextId := ← IO.mkRef 1, stop := stopProcessGroup child }
  let shutdown : IO Unit := do
    let id ← server.freshId
    let done ← try
        finishesWithin shutdownDeadline <| ReaderT.run (r := child) do
          Ipc.shutdown id
          discard Ipc.waitForExit
      catch _ => pure none
    if done.isNone then server.stop
  try
    let result ← ReaderT.run (r := child) do
      initializeServer
      act server
    shutdown
    return result
  catch e =>
    shutdown
    throw e

/-- An open document in a language server session, with its current version. -/
public structure OpenDoc where
  server : Server
  uri : DocumentUri
  version : IO.Ref Nat

/-- Writes a document's text to {name}`path` and opens the document in the server. -/
public def Server.openDoc (server : Server) (path : System.FilePath) (text : String) :
    Ipc.IpcM OpenDoc := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path text
  let uri := System.Uri.pathToUri (← IO.FS.realPath path)
  Ipc.writeNotification ⟨"textDocument/didOpen", {
    textDocument := { uri, languageId := "lean", version := 1, text } : DidOpenTextDocumentParams }⟩
  return { server, uri, version := ← IO.mkRef 1 }

public def OpenDoc.close (doc : OpenDoc) : Ipc.IpcM Unit :=
  Ipc.writeNotification ⟨"textDocument/didClose",
    { textDocument := { uri := doc.uri } : DidCloseTextDocumentParams }⟩

/-- Opens a closed document again with {name}`text`, as its next version. -/
public def OpenDoc.reopen (doc : OpenDoc) (text : String) : Ipc.IpcM Unit := do
  let version ← doc.version.modifyGet fun v => (v + 1, v + 1)
  Ipc.writeNotification ⟨"textDocument/didOpen", {
    textDocument := { uri := doc.uri, languageId := "lean", version, text }
    : DidOpenTextDocumentParams }⟩

/-- Sends an LSP edit as the next version. -/
public def OpenDoc.change (doc : OpenDoc) (e : Lsp.TextEdit) : Ipc.IpcM Unit := do
  let version ← doc.version.modifyGet fun v => (v + 1, v + 1)
  Ipc.writeNotification ⟨"textDocument/didChange", {
    textDocument := { uri := doc.uri, version? := some version }
    contentChanges := #[.rangeChange e.range e.newText]
    : DidChangeTextDocumentParams }⟩

/-- How long a document has to finish processing, in milliseconds. -/
def processingDeadline : Nat := 5 * 60 * 1000

/--
Runs {name}`act`, which waits for the server to process {name}`version` of the document. When
{name}`act` hasn't finished after five minutes, the server is stopped and an error that names the
document and the version is thrown.
-/
def OpenDoc.waitWithin (doc : OpenDoc) (version : Nat) (act : Ipc.IpcM Unit) : Ipc.IpcM Unit := do
  let child ← read
  if (← finishesWithin processingDeadline (ReaderT.run (r := child) act)).isNone then
    doc.server.stop
    throw <| IO.userError
      s!"the language server didn't finish version {version} of {doc.uri} within five minutes"

/--
Waits until the server has processed the current version and discards its diagnostics. When the
server hasn't finished after five minutes, it is stopped and an error that names the document and
the version is thrown.
-/
public def OpenDoc.wait (doc : OpenDoc) : Ipc.IpcM Unit := do
  let id ← doc.server.freshId
  let version ← doc.version.get
  doc.waitWithin version (discard <| Ipc.collectDiagnostics id doc.uri version)

/-- A diagnostic, with its message as text and with trace nodes expanded. -/
public structure TextDiagnostic where
  pos : Lsp.Position
  severity : String
  text : String
deriving BEq

public def TextDiagnostic.describe (d : TextDiagnostic) : String :=
  s!"{d.pos.line + 1}:{d.pos.character} {d.severity}: {d.text}"

def OpenDoc.rpcCall (doc : OpenDoc) (session : UInt64) (method : Name) (params : Json) (β : Type)
    [FromJson β] : Ipc.IpcM β :=
  doc.server.request "$/lean/rpc/call"
    ({ textDocument := { uri := doc.uri }, position := ⟨0, 0⟩, sessionId := session, method,
       params } : RpcCallParams) β

/-- Renders an interactive message as text, expanding trace children that are sent lazily. -/
partial def render (doc : OpenDoc) (session : UInt64) :
    Widget.TaggedText MsgEmbed → Ipc.IpcM String
  | .text s => pure s
  | .append xs => return (← xs.mapM (render doc session)).foldl (· ++ ·) ""
  | .tag e _ =>
    match e with
    | .expr t => pure t.stripTags
    | .goal _ => pure "(goal)"
    | .widget _ alt => render doc session alt
    | .trace _ cls msg _ children => do
      let children : Array (Widget.TaggedText MsgEmbed) ← match children with
        | .strict cs => pure cs
        | .lazy ref =>
          doc.rpcCall session `Lean.Widget.lazyTraceChildrenToInteractive (toJson ref) _
      let mut out := s!"[{cls}] {← render doc session msg}"
      for c in children do
        for line in (← render doc session c).split '\n' do
          out := out ++ "\n  " ++ line
      return out

/-- The current version's diagnostics, as text, in the order of their positions. -/
public def OpenDoc.diagnostics (doc : OpenDoc) : Ipc.IpcM (Array TextDiagnostic) := do
  doc.wait
  let session := (← doc.server.request "$/lean/rpc/connect" ({ uri := doc.uri } : RpcConnectParams)
    RpcConnected).sessionId
  let diags ← doc.rpcCall session `Lean.Widget.getInteractiveDiagnostics
    (toJson ({ lineRange? := none } : Widget.GetInteractiveDiagnosticsParams))
    (Array InteractiveDiagnostic)
  let mut out := #[]
  for d in diags do
    let severity := match d.severity? with
      | some .error => "error"
      | some .warning => "warning"
      | some .information => "info"
      | some .hint => "hint"
      | none => "info"
    out := out.push { pos := d.range.start, severity, text := ← render doc session d.message }
  return out.qsort fun a b => (compare a.pos b.pos).then (compare a.text b.text) == .lt

/-! # Elaboration Time -/

/-- Throws if the diagnostics include an error. -/
def checkDiagnostics (p : PublishDiagnosticsParams) : IO Unit := do
  for d in p.diagnostics do
    if d.severity? == some .error then
      throw <| IO.userError s!"error while processing the file: {toJson d}"

/--
Waits until the server's {lit}`$/lean/fileProgress` notifications report that it has processed the
whole file, and throws when the server reports an error. It is modeled on
{name}`Lean.Server.Test.Runner.waitForMessage`.
-/
partial def waitForProcessingDone (uri : DocumentUri) (version : Nat) : Ipc.IpcM Unit := do
  match ← Ipc.readMessage with
  | .notification "textDocument/publishDiagnostics" (some param) =>
    match fromJson? (α := PublishDiagnosticsParams) (toJson param) with
    | Except.ok diagnosticParam =>
      checkDiagnostics diagnosticParam
      waitForProcessingDone uri version
    | Except.error inner =>
      throw <| IO.userError s!"Cannot decode publishDiagnostics parameters\n{inner}"
  | .notification "$/lean/fileProgress" (some param) =>
    match fromJson? (α := LeanFileProgressParams) (toJson param) with
    | .ok p =>
      if p.textDocument.uri == uri then
        if p.processing.any (·.kind == .fatalError) then
          throw <| IO.userError "waitForProcessingDone: \
            server reported fatalError while processing the file"
        if p.processing.isEmpty && p.textDocument.version?.getD version ≥ version then
          return
      waitForProcessingDone uri version
    | .error inner =>
      throw <| IO.userError s!"Cannot decode fileProgress parameters\n{inner}"
  | _ => waitForProcessingDone uri version

/--
The time in milliseconds that the server needs to process the file at {name}`path` again after
{name}`newText` is inserted on a line of its own at {name}`line` and {name}`character`, both counted
from 0. The server runs in the Lake workspace at {name}`root`. It throws if the server reports an
error or if a version of the file isn't processed within five minutes.
-/
public def reElabTime (root path : System.FilePath) (newText : String) (line character : Nat) :
    IO Nat := do
  let text ← IO.FS.readFile path
  withServer root #["-DstderrAsMessages=false"] fun server => do
    let doc ← server.openDoc path text
    doc.waitWithin 1 (waitForProcessingDone doc.uri 1)
    let pos : Lsp.Position := { line, character }
    let processingStart ← IO.monoMsNow
    doc.change { range := ⟨pos, pos⟩, newText := s!"\n{newText}\n" }
    doc.waitWithin 2 (waitForProcessingDone doc.uri 2)
    let processingEnd ← IO.monoMsNow
    if let some diags ← Ipc.collectDiagnostics (← server.freshId) doc.uri 2 then
      checkDiagnostics diags.param
    return processingEnd - processingStart
