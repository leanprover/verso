/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import VersoServe

open Std Async Http
open VersoServe

set_option linter.missingDocs true
set_option doc.verso true

/-- The HTTP method name used in request logs. -/
def methodName : Method → String
  | .get => "GET"
  | .head => "HEAD"
  | .post => "POST"
  | .put => "PUT"
  | .delete => "DELETE"
  | .options => "OPTIONS"
  | .patch => "PATCH"
  | _ => "?"

/--
Determines which config file to load.

An explicit {lit}`--config` path that does not exist is a fatal error. With no flag, an existing
{lit}`serve.toml` in the current directory is used, and otherwise no file is loaded.
-/
def resolveConfigFile (cli : CliArgs) : IO (Option System.FilePath) := do
  match cli.configPath with
  | some p =>
    if ← p.pathExists then return some p
    else throw <| IO.userError s!"Config file not found: {p}"
  | none =>
    let default : System.FilePath := "serve.toml"
    if ← default.pathExists then return some default else return none

/--
Resolves each mount's directory to an absolute path.

A directory that does not exist is a fatal error naming the offending mount. The resolved roots form
the confinement set used for symlink and traversal checks.
-/
def resolveMounts (mounts : Array Mount) : IO (Array ResolvedMount) :=
  mounts.mapM fun m => do
    unless ← m.dir.pathExists do
      throw <| IO.userError s!"Mount directory not found: {m.dir} (serving {m.urlPrefix})"
    return { urlPrefix := m.urlPrefix, root := ← IO.FS.realPath m.dir }

/-- Prints the startup banner, including the always-present local-only notice. -/
def printBanner (config : ServeConfig) (mounts : Array ResolvedMount) (port : UInt16) : IO Unit := do
  IO.println "Verso HTTP server. This is for local writing and development only; it is not designed for production use."
  if let some b := config.banner then IO.println s!"  {b}"
  for m in mounts do
    IO.println s!"  Serving {m.urlPrefix} from {m.root}"
  IO.println s!"  http://127.0.0.1:{port}/"
  if port != config.port.toUInt16 then
    IO.println s!"  (the requested port {config.port.toNat} was unavailable, using {port})"
  IO.println "  Use Ctrl+C to exit."
  -- Flush so the banner appears at once, even when the server's output is captured or piped.
  (← IO.getStdout).flush

/-- The loopback socket address for a port. -/
def loopback (port : UInt16) : Net.SocketAddress :=
  .v4 (.mk (.ofParts 127 0 0 1) port)

/-- Entry point for the {lit}`serve` development HTTP server. -/
public def main (args : List String) : IO UInt32 := do
  let cli ← match parseArgs args with
    | .ok cli => pure cli
    | .error e => IO.eprintln e; IO.eprintln ""; IO.eprintln usage; return 1
  if cli.help then
    IO.println usage
    return 0
  let (config, mounts) ← try
      let cfgFile ← resolveConfigFile cli
      let base ← match cfgFile with
        | some f => loadServeConfig f
        | none => pure {}
      let config := base.withCli cli
      pure (config, ← resolveMounts config.mounts)
    catch e =>
      IO.eprintln s!"{e}"
      return (1 : UInt32)
  let stdConfig : Http.Config := { serverName := some (Header.Value.ofString! "verso-serve") }
  let portRef ← IO.mkRef config.port.toUInt16
  let handler := Server.Handler.ofFn fun req => do
    let r ← handleRequest config mounts req
    unless config.quiet do
      IO.eprintln s!"[{← portRef.get}] {methodName req.line.method} {req.line.uri} {r.line.status.toCode}"
      if config.verbose then
        let detail := ["range", "if-none-match", "if-modified-since", "user-agent"].filterMap fun h =>
          (req.line.headers.get? (Header.Name.ofString! h)).map fun v => s!"{h}: {v}"
        unless detail.isEmpty do
          IO.eprintln s!"    {"; ".intercalate detail}"
    return r
  Async.block do
    if config.strictPort then
      let server ← try
          Server.serve (loopback config.port.toUInt16) handler stdConfig
        catch _ =>
          throw <| IO.userError
            s!"Port {config.port.toNat} is unavailable. Pass a different --port, or omit --strict-port to try nearby ports."
      printBanner config mounts config.port.toUInt16
      server.waitShutdown
      return 0
    let tryBind := fun (p : UInt16) => do
      try return some (← Server.serve (loopback p) handler stdConfig)
      catch _ => return none
    match ← firstAvailable tryBind config.port.toUInt16 with
    | some (p, server) =>
      portRef.set p
      printBanner config mounts p
      server.waitShutdown
      return 0
    | none =>
      throw <| IO.userError s!"Could not bind to any port near {config.port.toNat}"
