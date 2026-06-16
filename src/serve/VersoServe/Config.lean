/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

import Lake.Toml
import Std.Http
public import Lake.Toml.Data.Value
public import Lake.Toml.Decode

open Lake (DecodeToml decodeToml)
open Lake.Toml hiding lit

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace VersoServe

/-- A TCP port a server may listen on. Excludes {lit}`0`, which never names a listening socket. -/
abbrev Port := { p : Nat // 0 < p ∧ p < 65536 }

namespace Port

instance : Inhabited Port := ⟨⟨8000, by decide⟩⟩

/-- The port as a {name}`Nat`. -/
def toNat (p : Port) : Nat := p.val

/-- The port as a {name}`UInt16`. -/
def toUInt16 (p : Port) : UInt16 := p.val.toUInt16

/-- The {name}`Port` for a number, or {name}`none` if it is {lit}`0` or above {lit}`65535`. -/
def ofNat? (n : Nat) : Option Port :=
  if h : 0 < n ∧ n < 65536 then some ⟨n, h⟩ else none

end Port

/--
A directory mounted at a URL prefix.

{open Mount}

The {name}`urlPrefix` is normalized to begin with `/` and to omit a trailing `/` except for the root
mount `/`. The {name}`dir` is resolved to an absolute path when the server starts.
-/
structure Mount where
  /-- The URL prefix this mount serves, such as `/` or `/foo`. -/
  urlPrefix : String
  /-- The directory whose contents are served under {name (full := Mount.urlPrefix)}`urlPrefix`. -/
  dir : System.FilePath
deriving Repr, BEq, Inhabited

/--
The status code of a redirect. Only the codes a redirect may use are representable.
-/
inductive RedirectStatus where
  /-- {lit}`301 Moved Permanently`. -/
  | movedPermanently
  /-- {lit}`302 Found`. -/
  | found
  /-- {lit}`303 See Other`. -/
  | seeOther
  /-- {lit}`307 Temporary Redirect`. -/
  | temporaryRedirect
  /-- {lit}`308 Permanent Redirect`. -/
  | permanentRedirect
deriving Repr, BEq, Inhabited

/-- The {name}`RedirectStatus` for an HTTP status number, or {name}`none` if it is not a redirect. -/
def RedirectStatus.ofNat? : Nat → Option RedirectStatus
  | 301 => some .movedPermanently
  | 302 => some .found
  | 303 => some .seeOther
  | 307 => some .temporaryRedirect
  | 308 => some .permanentRedirect
  | _ => none

/--
A redirect rule matched against the request path by prefix.
-/
structure RedirectRule where
  /-- The request-path prefix that triggers the redirect. -/
  fromPath : String
  /-- The location to redirect to. -/
  toPath : String
  /-- The redirect status code. -/
  status : RedirectStatus := .movedPermanently
deriving Repr, BEq, Inhabited

/--
{open HeaderRule}
A rule that sets response headers for requests whose path begins with {name}`path`.
-/
structure HeaderRule where
  /-- The request-path prefix that the rule applies to. -/
  path : String
  /-- The header names and values to set, applied in order. -/
  set : Array (String × String)
deriving Repr, BEq, Inhabited

/--
The fully resolved configuration for the server.
-/
structure ServeConfig where
  /-- The TCP port to listen on. -/
  port : Port := ⟨8000, by decide⟩
  /-- An optional line shown in the startup banner to identify the project. -/
  banner : Option String := none
  /-- Whether to send permissive CORS headers and answer {lit}`OPTIONS` preflight requests. -/
  cors : Bool := false
  /-- Whether to generate HTML listings for directories that lack an index file. -/
  directoryListing : Bool := true
  /-- Whether a request for a directory without a trailing slash redirects to add one. -/
  trailingSlashRedirect : Bool := true
  /-- Whether symbolic links may resolve to targets outside every mounted directory. -/
  followSymlinksOutsideRoot : Bool := false
  /-- The mount table, consulted by longest matching URL prefix. -/
  mounts : Array Mount := #[]
  /-- Redirect rules, tried in order. -/
  redirects : Array RedirectRule := #[]
  /-- Header rules, applied in order after the response is built. -/
  headers : Array HeaderRule := #[]
  /-- Whether to fail rather than fall back to another port when the port is taken. -/
  strictPort : Bool := false
  /-- Whether to suppress per-request logging. -/
  quiet : Bool := false
  /-- Whether to log additional detail. -/
  verbose : Bool := false
deriving Repr, Inhabited

/--
Normalizes a mount or rule URL prefix to begin with `/` and to drop a trailing `/` except for the
root prefix `/`.
-/
def normalizePrefix (s : String) : String :=
  let s := if s.startsWith "/" then s else "/" ++ s
  if s == "/" then s else (s.dropEndWhile (· == '/')).copy

/-- Reports every key of {name}`t` outside {name}`known` as a decode error at the key's value. -/
def logUnknownKeys (context : String) (known : List Lean.Name) (t : Table) : DecodeM Unit := do
  for (k, v) in t.items do
    unless known.contains k do
      logDecodeErrorAt v.ref s!"unknown {context}: '{k.toString (escape := false)}'"

/-- Fails the decode at the first key of {name}`t` outside the given set. -/
def rejectUnknownKeys (context : String) (known : List Lean.Name) (t : Table) : EDecodeM Unit := do
  for (k, v) in t.items do
    unless known.contains k do
      throwDecodeErrorAt v.ref s!"unknown {context}: '{k.toString (escape := false)}'"

/-- Decodes a {lit}`[[mounts]]` entry into a {name}`Mount`. -/
def decodeMount (v : Value) : EDecodeM Mount := do
  let t ← v.decodeTable
  rejectUnknownKeys "key in a [[mounts]] entry" [`path, `dir] t
  let path ← t.decode (α := String) `path
  let dir ← t.decode (α := String) `dir
  return { urlPrefix := normalizePrefix path, dir := dir }

instance : DecodeToml Mount := ⟨decodeMount⟩

/-- Decodes a {lit}`[[redirects]]` entry into a {name}`RedirectRule`. -/
def decodeRedirect (v : Value) : EDecodeM RedirectRule := do
  let t ← v.decodeTable
  rejectUnknownKeys "key in a [[redirects]] entry" [`«from», `to, `status] t
  let fromPath ← t.decode (α := String) `«from»
  let toPath ← t.decode (α := String) `to
  let statusNum ← t.decode? (α := Nat) `status
  let status ← match statusNum with
    | none => pure RedirectStatus.movedPermanently
    | some n => match RedirectStatus.ofNat? n with
      | some s => pure s
      | none =>
        let ref := (t.find? `status).map (·.ref) |>.getD .missing
        throwDecodeErrorAt ref s!"redirect status must be one of 301, 302, 303, 307, 308; got {n}"
  return {
    fromPath := normalizePrefix fromPath,
    toPath := toPath,
    status
  }

instance : DecodeToml RedirectRule := ⟨decodeRedirect⟩

/--
Decodes an inline {lit}`set = { ... }` table into name and value pairs, rejecting names and values
that are not valid HTTP header fields. A missing {lit}`set` is reported at {name}`ref`.
-/
def decodeHeaderSet (t : Table) (ref : Lean.Syntax) : EDecodeM (Array (String × String)) := do
  match t.find? `set with
  | none => throwDecodeErrorAt ref "missing required key: 'set'"
  | some (.table' _ setTable) =>
    setTable.items.foldlM (init := #[]) fun acc (k, v) => do
      let name := k.toString (escape := false)
      let .string _ value := v
        | throwDecodeErrorAt v.ref s!"header value for '{name}' must be a string"
      unless (Std.Http.Header.Name.ofString? name).isSome do
        throwDecodeErrorAt v.ref s!"invalid header name: '{name}'"
      unless (Std.Http.Header.Value.ofString? value).isSome do
        throwDecodeErrorAt v.ref s!"invalid value for header '{name}': {value.quote}"
      return acc.push (name, value)
  | some other => throwDecodeErrorAt other.ref "'set' must be a table mapping header names to strings"

/-- Decodes a {lit}`[[headers]]` entry into a {name}`HeaderRule`. -/
def decodeHeaderRule (v : Value) : EDecodeM HeaderRule := do
  let t ← v.decodeTable
  rejectUnknownKeys "key in a [[headers]] entry" [`path, `set] t
  let path ← t.decode (α := String) `path
  return { path := normalizePrefix path, set := ← decodeHeaderSet t v.ref }

instance : DecodeToml HeaderRule := ⟨decodeHeaderRule⟩

/--
Decodes a TOML table into a {name}`ServeConfig`, leaving {name (full := Mount.dir)}`dir` paths
unresolved.
-/
def decodeServeConfig (table : Table) : Except (Array DecodeError) ServeConfig :=
  let action : DecodeM ServeConfig := do
    let topKnown : List Lean.Name :=
      [`port, `banner, `cors, `directory_listing, `trailing_slash_redirect,
       `follow_symlinks_outside_root, `mounts, `redirects, `headers]
    logUnknownKeys "top-level key" topKnown table
    let portNum ← table.tryDecode? (α := Nat) `port
    let port : Port ← match portNum with
      | none => pure ⟨8000, by decide⟩
      | some n =>
        match Port.ofNat? n with
        | some p => pure p
        | none =>
          let ref := (table.find? `port).map (·.ref) |>.getD .missing
          logDecodeErrorAt ref s!"port out of range (1-65535): {n}"
          pure ⟨8000, by decide⟩
    let banner ← table.tryDecode? (α := String) `banner
    let cors ← Table.tryDecodeD `cors (false : Bool) table
    let directoryListing ← Table.tryDecodeD `directory_listing (true : Bool) table
    let trailingSlashRedirect ← Table.tryDecodeD `trailing_slash_redirect (true : Bool) table
    let followSymlinksOutsideRoot ←
      Table.tryDecodeD `follow_symlinks_outside_root (false : Bool) table
    let mounts ← Table.tryDecodeD `mounts (#[] : Array Mount) table
    let redirects ← Table.tryDecodeD `redirects (#[] : Array RedirectRule) table
    let headers ← Table.tryDecodeD `headers (#[] : Array HeaderRule) table
    return {
      port,
      banner, cors, directoryListing, trailingSlashRedirect,
      followSymlinksOutsideRoot, mounts, redirects, headers
    }
  match action #[] with
  | .ok config errors => if errors.isEmpty then .ok config else .error errors

/-- Parses a TOML string into a {name}`ServeConfig`. Returns defaults for empty input. -/
def parseServeConfig (input : String) (source := "<string>") : IO ServeConfig := do
  if input.trimAscii.isEmpty then
    return {}
  let ictx := Lean.Parser.mkInputContext input source
  match ← Lake.Toml.loadToml ictx |>.toBaseIO with
  | .ok table =>
    match decodeServeConfig table with
    | .ok config => return config
    | .error errors =>
      let render := fun (e : DecodeError) =>
        match e.ref.getPos? with
        | some pos =>
          let p := ictx.fileMap.toPosition pos
          s!"{source}:{p.line}:{p.column}: {e.msg}"
        | none => e.msg
      throw <| IO.userError s!"Errors in {source}:\n{"\n".intercalate (errors.map render).toList}"
  | .error log =>
    let msgs ← log.toList.mapM fun msg => msg.toString
    throw <| IO.userError s!"Failed to parse {source}:\n{"\n".intercalate msgs}"

/--
Loads and parses a `serve.toml` file, rebasing each mount's {name (full := Mount.dir)}`dir` onto the
directory that contains the config file so paths are written relative to the config.
-/
def loadServeConfig (path : System.FilePath) : IO ServeConfig := do
  let input ← IO.FS.readFile path
  let config ← parseServeConfig input (source := path.toString)
  let base := path.parent.getD "."
  return { config with mounts := config.mounts.map fun m => { m with dir := base / m.dir } }

/--
Command-line arguments for the server, before merging with a config file. Options left as
{name}`none` were not given and do not override config-file values.
-/
structure CliArgs where
  /-- The explicit `--config` path, if given. -/
  configPath : Option System.FilePath := none
  /-- The `--port` value, if given. -/
  port : Option Port := none
  /-- The positional directory to serve at `/`, if given. -/
  dir : Option System.FilePath := none
  /-- Whether `--strict-port` was given. -/
  strictPort : Bool := false
  /-- Whether `--no-listing` was given. -/
  noListing : Bool := false
  /-- Whether `--no-trailing-slash-redirect` was given. -/
  noTrailingSlash : Bool := false
  /-- Whether `--cors` was given. -/
  cors : Bool := false
  /-- Whether `--quiet` was given. -/
  quiet : Bool := false
  /-- Whether {lit}`-v`/`--verbose` was given. -/
  verbose : Bool := false
  /-- Whether {lit}`-h`/`--help` was given. -/
  help : Bool := false
deriving Repr, Inhabited

/-- Usage text for the {lit}`serve` executable. -/
def usage : String :=
"Usage: serve [OPTIONS] [DIR]

Serve a directory over HTTP for local development. Binds 127.0.0.1 only;
it is not for production use.

Arguments:
  DIR                            Directory to serve at '/' (default: current directory)

Options:
  -p, --port PORT                Port to listen on (default: 8000)
      --strict-port              Fail if the port is taken instead of trying the next free one
      --config FILE              Load configuration from FILE (default: ./serve.toml if present)
      --no-listing               Disable directory listings
      --no-trailing-slash-redirect
                                 Serve directories in place instead of redirecting to add a slash
      --cors                     Send permissive CORS headers
      --quiet                    Suppress per-request logging
  -v, --verbose                  Log additional detail
  -h, --help                     Show this help and exit"

/-- Parses command-line arguments into a {name}`CliArgs`. -/
def parseArgs (args : List String) : Except String CliArgs :=
  let rec loop (acc : CliArgs) : List String → Except String CliArgs
    | [] => pure acc
    | "-h" :: _ | "--help" :: _ => pure { acc with help := true }
    | "-p" :: p :: more | "--port" :: p :: more =>
      match p.toNat? with
      | some n =>
        match Port.ofNat? n with
        | some port => loop { acc with port := some port } more
        | none => throw s!"Port out of range (1-65535): {p}"
      | none => throw s!"Invalid port: {p}"
    | ["-p"] | ["--port"] => throw "Missing value after '--port'"
    | "--config" :: c :: more => loop { acc with configPath := some c } more
    | ["--config"] => throw "Missing value after '--config'"
    | "--strict-port" :: more => loop { acc with strictPort := true } more
    | "--no-listing" :: more => loop { acc with noListing := true } more
    | "--no-trailing-slash-redirect" :: more => loop { acc with noTrailingSlash := true } more
    | "--cors" :: more => loop { acc with cors := true } more
    | "--quiet" :: more => loop { acc with quiet := true } more
    | "-v" :: more | "--verbose" :: more => loop { acc with verbose := true } more
    | other :: more =>
      if other.startsWith "-" then throw s!"Unknown option: {other}"
      else if acc.dir.isSome then throw s!"Unexpected extra argument: {other}"
      else loop { acc with dir := some other } more
  loop {} args

/--
Applies command-line overrides to a config loaded from a file.

Scalar flags override the corresponding config values. A positional directory replaces the `/`
mount. If no `/` mount remains, a default one serving the current directory is added, so `/` is
always mapped.
-/
def ServeConfig.withCli (config : ServeConfig) (cli : CliArgs) : ServeConfig :=
  let config := {
    config with
    port := cli.port.getD config.port,
    cors := config.cors || cli.cors,
    directoryListing := config.directoryListing && !cli.noListing,
    trailingSlashRedirect := config.trailingSlashRedirect && !cli.noTrailingSlash,
    strictPort := cli.strictPort,
    quiet := cli.quiet,
    verbose := cli.verbose
  }
  let config :=
    match cli.dir with
    | some d =>
      let root : Mount := { urlPrefix := "/", dir := d }
      if config.mounts.any (fun (m : Mount) => m.urlPrefix == "/") then
        { config with
          mounts := config.mounts.map fun (m : Mount) => if m.urlPrefix == "/" then root else m }
      else
        { config with mounts := config.mounts.push root }
    | none => config
  if config.mounts.any (fun (m : Mount) => m.urlPrefix == "/") then config
  else { config with mounts := config.mounts.push { urlPrefix := "/", dir := "." } }
