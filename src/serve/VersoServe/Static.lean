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

/-- One side of a single-range {lit}`Range` specification. -/
inductive RangeEnd where
  /-- The side was omitted, as in the open form {lit}`bytes=start-` or suffix form {lit}`bytes=-count`. -/
  | empty
  /-- The side named a byte offset. -/
  | ofNat (n : Nat)
  /-- The side was present but not a number. -/
  | malformed
deriving Repr, BEq, Inhabited

/-- Classifies one side of a {lit}`Range` specification. -/
def RangeEnd.ofSlice (s : String.Slice) : RangeEnd :=
  if s.isEmpty then .empty
  else if let some n := s.toNat? then .ofNat n
  else .malformed

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
    return getRange (RangeEnd.ofSlice a) (RangeEnd.ofSlice b)
  | _ => return .full
where
  getRange : (start stop : RangeEnd) → RangeResult
    -- Suffix form `bytes=-count`: the last `count` bytes.
  | .empty, .ofNat n =>
    if n == 0 then .unsatisfiable
    else .range (if n >= size then 0 else size - n) (size - 1)
  -- Open form `bytes=start-`: from `start` to the end of the content.
  | .ofNat start, .empty =>
    if start >= size then .unsatisfiable else .range start (size - 1)
  -- Closed form `bytes=start-stop`.
  | .ofNat start, .ofNat stop =>
    if start >= size then .unsatisfiable
    else
      let stop := min stop (size - 1)
      if stop < start then .unsatisfiable else .range start stop
  -- Both sides empty, or a non-numeric side: unparseable.
  | _, _ => .full

/-- The ETag for a file's contents, including surrounding quotes. -/
def etag (bytes : ByteArray) : String :=
  -- The validator is derived from the file contents, so rebuilding the site without changing a
  -- file still revalidates as unchanged.
  "\"" ++ toString (hash bytes) ++ "\""

/--
The first redirect rule that matches {name}`urlPath`, returning its status code and target location.

A rule matches when its prefix equals the path, is a leading path segment, or is the root prefix
{lit}`/`, which matches everything. The path beneath the matched prefix is appended to the target.
-/
def matchRedirect (rules : Array RedirectRule) (urlPath : String) :
    Option (RedirectStatus × String) :=
  rules.findSome? fun r =>
    if r.fromPath == "/" || urlPath == r.fromPath || urlPath.startsWith (r.fromPath ++ "/") then
      let rest :=
        if urlPath == r.fromPath then ""
        else if r.fromPath == "/" then urlPath
        else (urlPath.drop r.fromPath.length).copy
      some (r.status, r.toPath ++ rest)
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

/-- The uppercase hexadecimal digit for a value below sixteen. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + '0'.toNat) else Char.ofNat (n - 10 + 'A'.toNat)

/-- Percent-encodes a string's UTF-8 bytes, leaving the unreserved URL characters unchanged. -/
def percentEncode (s : String) : String :=
  s.toUTF8.foldl (init := "") fun acc b =>
    let n := b.toNat
    let unreserved :=
      (n >= 0x30 && n <= 0x39) || (n >= 0x41 && n <= 0x5a) || (n >= 0x61 && n <= 0x7a)
        || n == 0x2d || n == 0x2e || n == 0x5f || n == 0x7e
    if unreserved then acc.push (Char.ofNat n)
    else acc ++ s!"%{hexDigit (n / 16)}{hexDigit (n % 16)}"

/-- The stylesheet inlined into every generated directory listing. -/
def listingCss : String := include_str "listing.css"

/-- Renders a directory listing as an HTML page. -/
def renderListing (urlPath : String) (entries : Array (String × Bool)) : String :=
  let row := fun (cls href display : String) =>
    s!"<li class=\"{cls}\"><a href=\"{htmlEscape href}\">{htmlEscape display}</a></li>\n"
  let parent := if urlPath == "/" then "" else row "up" "../" "Parent directory"
  let rows := entries.foldl (init := "") fun acc (name, isDir) =>
    let suffix := if isDir then "/" else ""
    -- The link text shows the name; the href percent-encodes it so `?`, `#`, spaces, and the like
    -- stay part of the path rather than becoming URL syntax.
    let href := percentEncode name ++ suffix
    let display := name ++ suffix
    acc ++ row (if isDir then "dir" else "file") href display
  "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n" ++
    "<meta charset=\"utf-8\">\n" ++
    "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n" ++
    s!"<title>Index of {htmlEscape urlPath}</title>\n" ++
    s!"<style>{listingCss}</style>\n" ++
    "</head>\n<body>\n<main>\n" ++
    s!"<h1><span class=\"label\">Index of</span>{htmlEscape urlPath}</h1>\n" ++
    s!"<ul>\n{parent}{rows}</ul>\n" ++
    "</main>\n</body>\n</html>\n"

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

/--
Whether {name}`real` lies within {name}`root` (equal to it or beneath it).
-/
def isWithin (root real : System.FilePath) : Bool :=
  -- The comparison is by path component, so it holds on platforms whose separator is not `/` and is
  -- not fooled by a sibling whose name extends the root's.
  root.components.isPrefixOf real.components

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

Each header name appears once, at the position of its final occurrence, so a custom rule that sets a
header already present updates the existing one in place.
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
bytes.
-/
def respondHead (status : Status) (hdrs : Array (String × String)) (size : Nat) :
    Async (Response Body.Any) := do
  let body ← Body.empty
  body.setKnownSize (some (.fixed size))
  return toAny ((builderWith status hdrs).body body)

/-- Reads a request header as a string, if present. -/
def header? (req : Request Body.Stream) (name : String) : Option String :=
  (req.line.headers.get? (Header.Name.ofString! name)).map toString

/-- The response data for a file. -/
structure FileResponse where
  /-- The contents of the file -/
  bytes : ByteArray
  /--
  The headers to return, including the {lit}`ETag` and {lit}`Last-Modified` headers along with any
  provided by the framework.
  -/
  headers : Array (String × String)
  /--
  Whether the {lit}`ETag` and {lit}`Last-Modified` headers show that the client's cached copy is
  already current.
  -/
  notModified : Bool

/--
Reads a file and the information every response to a request for it shares.
-/
def fileResponseState (req : Request Body.Stream) (file : System.FilePath)
    (policy : Array (String × String)) : Async FileResponse := do
  let bytes ← IO.FS.readBinFile file
  let md ← file.metadata
  let etagVal := etag bytes
  let lastMod := httpDate md.modified
  let commonHdrs := #[("ETag", etagVal), ("Last-Modified", lastMod)] ++ policy
  let notModified :=
    header? req "if-none-match" == some etagVal || header? req "if-modified-since" == some lastMod
  return { bytes, headers := commonHdrs, notModified }

/--
Serves a single file, applying caching, conditional requests, and ranges. The {name}`policy`
headers are added to every response.
-/
def serveFile (req : Request Body.Stream) (file : System.FilePath)
    (policy : Array (String × String)) : Async (Response Body.Any) := do
  let { bytes, headers := commonHdrs, notModified } ← fileResponseState req file policy
  if notModified then
    respondEmpty .notModified commonHdrs
  else
    let fileHdrs :=
      #[("Content-Type", contentTypeForFile file bytes), ("Accept-Ranges", "bytes")] ++ commonHdrs
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
Answers a {lit}`HEAD` request for a file, producing the same headers a {lit}`GET` would but without
the body.
-/
def serveHead (req : Request Body.Stream) (file : System.FilePath)
    (policy : Array (String × String)) : Async (Response Body.Any) := do
  -- The file is read in full because the ETag follows its contents.
  let { bytes, headers := commonHdrs, notModified } ← fileResponseState req file policy
  if notModified then
    respondEmpty .notModified commonHdrs
  else
    let hdrs := #[("Content-Type", contentTypeForFile file bytes), ("Accept-Ranges", "bytes")] ++ commonHdrs
    respondHead .ok hdrs bytes.size

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
Normalizes path segments by dropping each {lit}`.` and letting each {lit}`..` remove the segment
before it. The result is the list of names to descend from a mount's root.

A {lit}`..` with no earlier segment to remove would point above the root, so that case yields
{name}`none`. A segment that contains a platform path separator (which can appear once a {lit}`%2F`
or {lit}`%5C` is decoded) or that names an absolute location such as a drive letter is also refused,
so an encoded separator cannot smuggle a {lit}`..` or an absolute path past this check. The check is
purely textual and never consults the filesystem.
-/
def confineSegments (segs : Array String) : Option (Array String) := do
  let mut out : Array String := #[]
  for s in segs do
    if s.any (System.FilePath.pathSeparators.contains ·) then failure
    if (s : System.FilePath).isAbsolute then failure
    if s == "." then continue
    else if s == ".." then
      if out.isEmpty then failure
      else out := out.pop
    else out := out.push s
  return out

/--
Reports whether {name}`path` resolves to a target inside a mounted root.

{open ServeConfig}

Symbolic links can still point outside a root, so this follows the path with {name}`IO.FS.realPath`
and checks the result, unless {name}`followSymlinksOutsideRoot` is set.
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
  -- A HEAD request returns the headers a GET would, but with no body.
  let serveContent := fun (file : System.FilePath) =>
    if req.line.method matches .head then serveHead req file policy else serveFile req file policy
  match matchRedirect cfg.redirects urlPath with
  | some (status, loc) => respondEmpty (RedirectStatus.toStatus status) (policy.push ("Location", loc))
  | none =>
    match resolveMountBy ResolvedMount.urlPrefix mounts fsSegs with
    | none => respondEmpty .notFound policy
    | some (mount, rest) =>
      -- `..` is resolved here, before touching the filesystem, so it can never climb above the mount.
      let some safe := confineSegments rest
        | respondEmpty .forbidden policy
      let candidate := safe.foldl (init := mount.root) fun p s => p / s
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
            if ← indexPath.pathExists then
              -- The index file may itself be a symlink that escapes the root, so reconfine it.
              if ← withinMounts cfg mounts indexPath then serveContent indexPath
              else respondEmpty .forbidden policy
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
    return ← respondEmpty .badRequest (#[("Cache-Control", "no-cache")] ++ corsHeaders cfg)
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
    respondEmpty .internalServerError (#[("Cache-Control", "no-cache")] ++ corsHeaders cfg)

/-- Builds the stateless handler for a configuration and its resolved mounts. -/
def mkHandler (cfg : ServeConfig) (mounts : Array ResolvedMount) : Server.StatelessHandler :=
  Server.Handler.ofFn fun req => handleRequest cfg mounts req

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
