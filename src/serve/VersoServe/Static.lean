/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Std.Http
public import Std.Async
public import Std.Time
public import Std.Data.HashMap
public import VersoServe.Mime
public import VersoServe.Config

open Std Async Http

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace VersoServe

/-! # Pure helpers -/

/-- The URL prefix segments of a mount or rule, with empty segments removed. -/
def prefixSegments (urlPrefix : String) : Array String :=
  (urlPrefix.splitOn "/").toArray.filter (· != "")

/--
Resolves a request's path segments against a mount table, returning the matching entry and the
segments beneath its prefix.

The entry whose URL prefix has the most segments wins, so more specific mounts override less
specific ones. The result does not depend on the order of {name}`mounts`.
-/
def resolveMountBy {α : Type} (urlPrefixOf : α → String) (mounts : Array α)
    (segs : Array String) : Option (α × Array String) :=
    Id.run do
  let mut best : Option (α × Nat) := none
  for h : i in 0...mounts.size do
    let pre := prefixSegments (urlPrefixOf mounts[i])
    if pre.isPrefixOf segs then
      match best with
      | some (bestEntry, bestLen) =>
        -- Uses ordering on strings as a tie breaker in case of equal prefix lengths
        if pre.size > bestLen ||
            (pre.size == bestLen && urlPrefixOf mounts[i] < urlPrefixOf bestEntry) then
          best := some (mounts[i], pre.size)
      | none => best := some (mounts[i], pre.size)
  return best.map fun (entry, preLen) => (entry, segs.extract preLen segs.size)

/-- Resolves request path segments against a {name}`Mount` table. -/
def resolveMount (mounts : Array Mount) (segs : Array String) : Option (Mount × Array String) :=
  resolveMountBy Mount.urlPrefix mounts segs

/-- The outcome of interpreting a {lit}`Range` request header against a known content size. -/
inductive RangeResult where
  /-- Serve the whole representation; no usable range was requested. -/
  | full
  /-- Serve bytes {name}`start` through {name}`stop` inclusive. -/
  | range (start stop : Nat)
  /-- The requested range cannot be satisfied for this size. -/
  | unsatisfiable
deriving Repr, BEq, Inhabited


/--
Interprets a single-range {lit}`Range` header value against a content size of {name}`size` bytes.

Supports {lit}`bytes=start-stop`, the open form {lit}`bytes=start-`, and the suffix form {lit}`bytes=-count`.
Multi-range requests and unparseable values yield {name}`RangeResult.full`.
-/
def parseRange (header : String) (size : Nat) : RangeResult := Id.run do
  if size == 0 then return .unsatisfiable
  -- A real Range header is short; treat oversized values as absent so the split below stays bounded.
  if header.length > 256 then return .full
  let header := header.trimAscii
  unless header.startsWith "bytes=" do return .full
  let spec := (header.drop "bytes=".length).trimAscii
  if spec.contains ',' then return .full
  match spec.split "-" |>.toArray with
  | #[a, b] =>
    if a.isEmpty then
      match b.toNat? with
      | some n =>
        if n == 0 then return .unsatisfiable
        let start := if n >= size then 0 else size - n
        return .range start (size - 1)
      | none => return .full
    else
      match a.toNat? with
      | none => return .full
      | some start =>
        if start >= size then return .unsatisfiable
        let stop := if b.isEmpty then size - 1 else min (b.toNat?.getD (size - 1)) (size - 1)
        if stop < start then return .unsatisfiable else return .range start stop
  | _ => return .full

/-- The ETag for a file's contents, including surrounding quotes. -/
def etag (bytes : ByteArray) : String :=
  "\"" ++ toString (hash bytes) ++ "\""

/--
The first redirect rule that matches {name}`urlPath`, returning its status code and target location.

A rule matches when its prefix equals the path or is a leading path segment. The path beneath the
matched prefix is appended to the target.
-/
def matchRedirect (rules : Array RedirectRule) (urlPath : String) :
    Option (RedirectStatus × String) :=
  rules.findSome? fun r =>
    if urlPath == r.fromPath || urlPath.startsWith (r.fromPath ++ "/") then
      some (r.status, r.toPath ++ urlPath.drop r.fromPath.length)
    else none

/--
The header names and values to set for {name}`urlPath`, accumulated from every matching rule in order.

A rule matches when its prefix equals the path, is a leading path segment, or is the root prefix.
Later pairs override earlier ones for the same header.
-/
def matchHeaderRules (rules : Array HeaderRule) (urlPath : String) : Array (String × String) :=
  rules.foldl (init := #[]) fun acc r =>
    if r.path == "/" || urlPath == r.path || urlPath.startsWith (r.path ++ "/") then acc ++ r.set
    else acc

/-- Escapes the characters that are unsafe in HTML text and double-quoted attributes. -/
def htmlEscape (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;" |>.replace "\"" "&quot;"

/-- Renders a directory listing as an HTML page. -/
def renderListing (urlPath : String) (entries : Array (String × Bool)) : String :=
  let rows := entries.foldl (init := "") fun acc (name, isDir) =>
    let display := if isDir then name ++ "/" else name
    acc ++ s!"<li><a href=\"{htmlEscape display}\">{htmlEscape display}</a></li>\n"
  "<!DOCTYPE html>\n" ++
    s!"<html><head><meta charset=\"utf-8\"><title>Index of {htmlEscape urlPath}</title></head>" ++
    s!"<body><h1>Index of {htmlEscape urlPath}</h1><ul>\n{rows}</ul></body></html>\n"

/-- The HTTP {name}`Status` for a redirect rule. -/
def RedirectStatus.toStatus : RedirectStatus → Status
  | .movedPermanently => .movedPermanently
  | .found => .found
  | .seeOther => .seeOther
  | .temporaryRedirect => .temporaryRedirect
  | .permanentRedirect => .permanentRedirect

/-! # Filesystem resolution -/

/-- A mount whose directory has been resolved to an absolute path. -/
structure ResolvedMount where
  /-- The URL prefix this mount serves. -/
  urlPrefix : String
  /-- The absolute, symlink-resolved directory served under {name}`ResolvedMount.urlPrefix`. -/
  root : System.FilePath
deriving Repr, Inhabited

/-- Whether {name}`real` lies within {name}`root` (equal to it or beneath it). -/
def isWithin (root real : System.FilePath) : Bool :=
  let r := root.toString
  let p := real.toString
  p == r || p.startsWith (r ++ "/")

/-- Formats a filesystem modification time as an HTTP date. -/
def httpDate (t : IO.FS.SystemTime) : String :=
  let ts := Std.Time.Timestamp.ofSecondsSinceUnixEpoch (Std.Time.Second.Offset.ofInt t.sec)
  (Std.Time.DateTime.ofTimestamp ts .GMT).toRFC822String

/-! # Request handling -/

/-- Erases a response body to {name}`Std.Http.Body.Any`. -/
def toAny {β : Type} [Body β] (r : Response β) : Response Body.Any :=
  { r with body := Body.Any.ofBody r.body }

/-- The CORS headers to add when cross-origin sharing is enabled. -/
def corsHeaders (cfg : ServeConfig) : Array (String × String) :=
  if cfg.cors then #[("Access-Control-Allow-Origin", "*")] else #[]

/--
Collapses repeated header names so the last value for each name wins, matched case-insensitively.

Header names are emitted at the position of their final occurrence, so a custom rule that sets a
header already present replaces it rather than adding a second copy.
-/
def dedupHeaders (hdrs : Array (String × String)) : Array (String × String) := Id.run do
  -- Keyed by lowercased name; the stored index is the position of the name's last occurrence.
  let mut byName : Std.HashMap String (Nat × String × String) := {}
  for h : i in 0...hdrs.size do
    let (name, value) := hdrs[i]
    byName := byName.insert name.toLower (i, name, value)
  let ordered := byName.valuesArray.qsort (·.1 < ·.1)
  return ordered.map fun (_, name, value) => (name, value)

/--
The headers applied to every response: revalidation caching, CORS when enabled, and the custom
header rules that match {name}`urlPath`.
-/
def policyHeaders (cfg : ServeConfig) (urlPath : String) : Array (String × String) :=
  #[("Cache-Control", "no-cache")] ++ corsHeaders cfg ++ matchHeaderRules cfg.headers urlPath

/--
A response builder with the given status and headers, after collapsing duplicate names. A header
whose name or value is not valid is dropped rather than aborting the response.
-/
def builderWith (status : Status) (hdrs : Array (String × String)) : Response.Builder :=
  (dedupHeaders hdrs).foldl (init := Response.withStatus status) fun b (k, v) =>
    match Header.Name.ofString? k, Header.Value.ofString? v with
    | some name, some value => b.header name value
    | _, _ => b

/-- Builds a response with no body and the given status and headers. -/
def respondEmpty (status : Status) (hdrs : Array (String × String)) : Async (Response Body.Any) := do
  let r ← (builderWith status hdrs).empty
  return toAny r

/-- Builds a response carrying {name}`body` with the given status and headers. -/
def respondBytes (status : Status) (hdrs : Array (String × String))
    (body : ByteArray) : Async (Response Body.Any) := do
  let r ← (builderWith status hdrs).fromBytes body
  return toAny r

/--
Builds a response with the given headers and a declared content length of {name}`size`, but no body
bytes. The body is never produced, so the content is not read.
-/
def respondHead (status : Status) (hdrs : Array (String × String)) (size : Nat) :
    Async (Response Body.Any) := do
  let body ← Body.empty
  body.setKnownSize (some (.fixed size))
  return toAny ((builderWith status hdrs).body body)

/-- Reads a request header as a string, if present. -/
def header? (req : Request Body.Stream) (name : String) : Option String :=
  (req.line.headers.get? (Header.Name.ofString! name)).map toString

/--
Serves a single file, applying caching, conditional requests, and ranges. The {name}`policy`
headers are added to every response.
-/
def serveFile (req : Request Body.Stream) (file : System.FilePath)
    (policy : Array (String × String)) : Async (Response Body.Any) := do
  let bytes ← IO.FS.readBinFile file
  let md ← file.metadata
  let etagVal := etag bytes
  let lastMod := httpDate md.modified
  let commonHdrs := #[("ETag", etagVal), ("Last-Modified", lastMod)] ++ policy
  let inm := header? req "if-none-match"
  let ims := header? req "if-modified-since"
  if inm == some etagVal || ims == some lastMod then
    respondEmpty .notModified commonHdrs
  else
    let fileHdrs :=
      #[("Content-Type", contentTypeForPath file), ("Accept-Ranges", "bytes")] ++ commonHdrs
    match header? req "range" with
    | some rangeHeader =>
      match parseRange rangeHeader bytes.size with
      | .range start stop =>
        let part := bytes.extract start (stop + 1)
        let cr := s!"bytes {start}-{stop}/{bytes.size}"
        respondBytes .partialContent (fileHdrs.push ("Content-Range", cr)) part
      | .unsatisfiable =>
        respondEmpty .rangeNotSatisfiable (policy.push ("Content-Range", s!"bytes */{bytes.size}"))
      | .full => respondBytes .ok fileHdrs bytes
    | none => respondBytes .ok fileHdrs bytes

/--
Answers a {lit}`HEAD` request for a file from its metadata alone, without reading the contents.

The {lit}`ETag` is derived from the contents, so it is omitted here; conditional {lit}`HEAD`
requests revalidate against {lit}`Last-Modified`.
-/
def serveHead (req : Request Body.Stream) (file : System.FilePath)
    (policy : Array (String × String)) : Async (Response Body.Any) := do
  let md ← file.metadata
  let lastMod := httpDate md.modified
  let commonHdrs := #[("Last-Modified", lastMod)] ++ policy
  if header? req "if-modified-since" == some lastMod then
    respondEmpty .notModified commonHdrs
  else
    let hdrs := #[("Content-Type", contentTypeForPath file), ("Accept-Ranges", "bytes")] ++ commonHdrs
    respondHead .ok hdrs md.byteSize.toNat

/-- Serves an HTML listing of a directory's entries. The {name}`policy` headers are added. -/
def serveListing (dir : System.FilePath) (urlPath : String)
    (policy : Array (String × String)) : Async (Response Body.Any) := do
  let entries ← dir.readDir
  let mut items : Array (String × Bool) := #[]
  for e in entries do
    items := items.push (e.fileName, ← e.path.isDir)
  let sorted := items.qsort fun a b => a.1 < b.1
  let html := renderListing urlPath sorted
  respondBytes .ok (#[("Content-Type", "text/html; charset=utf-8")] ++ policy) html.toUTF8

/--
Resolves {name}`path` and reports whether it stays inside a mounted root, honoring the
{name (full := ServeConfig.followSymlinksOutsideRoot)}`followSymlinksOutsideRoot` setting.
-/
def withinMounts (cfg : ServeConfig) (mounts : Array ResolvedMount) (path : System.FilePath) :
    IO Bool := do
  if cfg.followSymlinksOutsideRoot then return true
  let real ← IO.FS.realPath path
  return mounts.any fun m => isWithin m.root real

/-- Handles a {lit}`GET` or {lit}`HEAD` request by resolving it against the mount table. -/
def handleGet (cfg : ServeConfig) (mounts : Array ResolvedMount) (req : Request Body.Stream)
    (fsSegs : Array String) (hasSlash : Bool) (urlPath : String)
    (policy : Array (String × String)) : Async (Response Body.Any) := do
  -- A HEAD request returns the headers a GET would, but without reading the file contents.
  let serveContent := fun (file : System.FilePath) =>
    if req.line.method matches .head then serveHead req file policy else serveFile req file policy
  match matchRedirect cfg.redirects urlPath with
  | some (status, loc) => respondEmpty (RedirectStatus.toStatus status) (policy.push ("Location", loc))
  | none =>
    match resolveMountBy ResolvedMount.urlPrefix mounts fsSegs with
    | none => respondEmpty .notFound policy
    | some (mount, rest) =>
      let candidate := rest.foldl (init := mount.root) fun p s => p / s
      if !(← candidate.pathExists) then
        respondEmpty .notFound policy
      else if !(← withinMounts cfg mounts candidate) then
        respondEmpty .forbidden policy
      else
        let real ← IO.FS.realPath candidate
        let md ← real.metadata
        match md.type with
        | .dir =>
          if !hasSlash && cfg.trailingSlashRedirect then
            respondEmpty .movedPermanently (policy.push ("Location", urlPath ++ "/"))
          else
            let indexPath := real / "index.html"
            -- The index file may itself be a symlink that escapes the root, so reconfine it.
            if (← indexPath.pathExists) && (← withinMounts cfg mounts indexPath) then
              serveContent indexPath
            else if (← indexPath.pathExists) then
              respondEmpty .forbidden policy
            else if cfg.directoryListing then serveListing real urlPath policy
            else respondEmpty .forbidden policy
        | _ => serveContent real

/--
Whether any path segment contains a Unicode control character (the C0 range, {lit}`DEL`, or the C1
range), which has no place in a request path.
-/
def hasControlChar (segs : Array String) : Bool :=
  segs.any fun s => s.any fun c =>
    let n := c.toNat
    n < 0x20 || (0x7f <= n && n <= 0x9f)

/-- The top-level request handler dispatching on the HTTP method. -/
def handle (cfg : ServeConfig) (mounts : Array ResolvedMount)
    (req : Request Body.Stream) : Async (Response Body.Any) := do
  let segs := req.line.uri.path.normalize.toDecodedSegments
  -- A control character can only arrive percent-encoded; reject it so it cannot reach a header.
  if hasControlChar segs then
    return ← respondEmpty .badRequest (corsHeaders cfg)
  let fsSegs := segs.filter (· != "")
  let hasSlash := fsSegs.isEmpty || segs.back? == some ""
  let urlPath := "/" ++ "/".intercalate fsSegs.toList
  let policy := policyHeaders cfg urlPath
  match req.line.method with
  | .get | .head => handleGet cfg mounts req fsSegs hasSlash urlPath policy
  | .options =>
    if cfg.cors then
      respondEmpty .noContent
        (#[("Access-Control-Allow-Methods", "GET, HEAD, OPTIONS"),
          ("Access-Control-Allow-Headers", "*")] ++ policy)
    else respondEmpty .methodNotAllowed (#[("Allow", "GET, HEAD")] ++ policy)
  | _ => respondEmpty .methodNotAllowed (#[("Allow", "GET, HEAD")] ++ policy)

/-- Runs the request handler, turning an unexpected error into a {lit}`500` response. -/
def handleRequest (cfg : ServeConfig) (mounts : Array ResolvedMount)
    (req : Request Body.Stream) : Async (Response Body.Any) := do
  try
    handle cfg mounts req
  catch e =>
    IO.eprintln s!"Error handling {req.line.uri}: {e}"
    respondEmpty .internalServerError (corsHeaders cfg)

/-- Builds the stateless handler for a configuration and its resolved mounts. -/
def mkHandler (cfg : ServeConfig) (mounts : Array ResolvedMount) : Server.StatelessHandler :=
  Server.Handler.ofFn fun req => do
    let r ← handleRequest cfg mounts req
    return r

/-- The number of consecutive ports to try, starting from the requested one. -/
def portScanCount : Nat := 50

/--
Tries to bind at {name}`port` and then at each consecutive port, returning the first success along
with the port that worked.

Scanning consecutive ports lets several servers started with default settings coexist, since each
takes the lowest free port. {name}`tryBind` reports a successful bind as {name}`Option.some` and an
unavailable port as {name}`Option.none`. Ports past the maximum are skipped, and the result does not
depend on why a port is unavailable, so it is portable across operating systems.
-/
def firstAvailable {m : Type → Type} {α : Type} [Monad m] (tryBind : UInt16 → m (Option α))
    (port : UInt16) (offsets : List Nat := List.range portScanCount) : m (Option (UInt16 × α)) := do
  for off in offsets do
    let n := port.toNat + off
    if n <= 65535 then
      if let some a ← tryBind n.toUInt16 then
        return some (n.toUInt16, a)
  return none
