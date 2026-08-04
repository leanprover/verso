import Lean.Server.Test.Runner

/-! Benchmark the LSP re-elaboration time of a Lean file.

Spawns `lake serve`, opens the file, waits for initial processing,
inserts `<text>` at position `<line>:<character>` (both 0-based),
then reports the time in milliseconds until processing finishes. -/

open Lean Lean.Lsp Lean.JsonRpc

def checkDiagnostics (p : PublishDiagnosticsParams) : IO Unit := do
  for d in p.diagnostics do
    if d.severity? == some .error then
      throw <| IO.userError s!"error while processing the file: \
        {toJson d}"

/-- Waits until the server reports via `$/lean/fileProgress` notifications
that the whole file has been processed,
or emits an error message.
Modeled after `Lean.Server.Test.Runner.waitForMessage`. -/
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

def main (args : List String) : IO Unit := do
  let [path, newText, line, character] := args
    | throw <| IO.userError
        "usage: lean --run InteractiveBench.lean <file> <new-text> <line> <character>"
  let some line := line.toNat?
    | throw <| IO.userError s!"not a number: {line}"
  let some character := character.toNat?
    | throw <| IO.userError s!"not a number: {character}"
  let path ← IO.FS.realPath path
  let uri := System.Uri.pathToUri path
  let text ← IO.FS.readFile path
  Ipc.runWith "lake" #["serve", "--", "-DstderrAsMessages=false"] do
    -- Initialization identical to `Lean.Server.Test.Runner.main`.
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

    Ipc.writeNotification ⟨"textDocument/didOpen", {
      textDocument := { uri, languageId := "lean", version := 1, text } : DidOpenTextDocumentParams }⟩
    waitForProcessingDone uri 1

    let pos : Lsp.Position := { line, character }
    let processingStart ← IO.monoMsNow
    Ipc.writeNotification ⟨"textDocument/didChange", {
      textDocument := { uri, version? := some 2 }
      contentChanges := #[.rangeChange ⟨pos, pos⟩ s!"\n{newText}\n"]
      : DidChangeTextDocumentParams }⟩
    waitForProcessingDone uri 2
    let processingEnd ← IO.monoMsNow

    if let some diags ← Ipc.collectDiagnostics 0 uri 2 then
      checkDiagnostics diags.param

    IO.println s!"re-elab time={processingEnd - processingStart}"

    Ipc.shutdown 1
    discard <| Ipc.waitForExit
