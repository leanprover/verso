/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Std.Http
import Plausible
import Plausible.ArbitraryFueled
import VersoServe
import VersoServe.Static

open Plausible
open Std Async Http
open VersoServe

namespace Verso.Tests.Serve

/-! ## Property-based checks (Plausible) -/

open scoped Plausible.Decorations in
/-- Runs a Plausible property as an `IO` test. -/
def testProp
    (p : Prop) (cfg : Configuration := {})
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] :
    IO (TestResult p') :=
  Testable.checkIO p' (cfg := cfg)

/-- A range result stays within bounds whenever it selects a sub-range. -/
def propRangeBounds := testProp <| ∀ (a b size : Nat), show Bool from
  match parseRange s!"bytes={a}-{b}" size with
  | .range s e => s ≤ e && e < size
  | _ => true

/-- The resolved mount's prefix is genuinely a prefix of the request, and no match is missed. -/
def propMountPrefix := testProp <| ∀ (prefixes segs : Array String), show Bool from
  match resolveMountBy id prefixes segs with
  | some (p, _) => (prefixSegments p).isPrefixOf segs
  | none => prefixes.all fun q => !(prefixSegments q).isPrefixOf segs

/-- The chosen mount has the longest matching prefix of any candidate. -/
def propMountLongest := testProp <| ∀ (prefixes segs : Array String), show Bool from
  match resolveMountBy id prefixes segs with
  | some (p, _) =>
    prefixes.all fun q =>
      !(prefixSegments q).isPrefixOf segs || (prefixSegments q).size ≤ (prefixSegments p).size
  | none => True

/-- Mount resolution does not depend on the order of the mount table. -/
def propMountShuffle := testProp <| ∀ (prefixes segs : Array String),
  (resolveMountBy id prefixes segs).map (·.1) ==
    (resolveMountBy id prefixes.reverse segs).map (·.1)

open Lean in
/-- The properties to check, paired with display names. -/
meta def props : List (Name × (Σ p, IO (TestResult p))) := [
  (`propRangeBounds, ⟨_, propRangeBounds⟩),
  (`propMountPrefix, ⟨_, propMountPrefix⟩),
  (`propMountLongest, ⟨_, propMountLongest⟩),
  (`propMountShuffle, ⟨_, propMountShuffle⟩),
]

/-! ## Unit checks -/

/-- The mount table from the user-guide example. -/
def exampleMounts : Array Mount := #[
  { urlPrefix := "/", dir := "root" },
  { urlPrefix := "/foo", dir := "foo" },
  { urlPrefix := "/bar", dir := "bar" },
  { urlPrefix := "/foo/x", dir := "foox" }]

/-- Resolves a URL path against {name}`exampleMounts` and reports the matched prefix. -/
def resolvedPrefix (mounts : Array Mount) (path : String) : Option String :=
  let segs := (path.splitOn "/").toArray.filter (· != "")
  (resolveMount mounts segs).map (·.1.urlPrefix)

/-- The deterministic unit checks, paired with display names. -/
def units : List (String × Bool) := [
  -- MIME
  ("mime html", mimeType? "HTML" == some "text/html"),
  ("mime css charset", contentTypeForPath "a.css" == "text/css; charset=utf-8"),
  ("mime png case", contentTypeForPath "A.PNG" == "image/png"),
  ("mime unknown", contentTypeForPath "a.xyz" == "application/octet-stream"),
  -- prefix normalization
  ("normalize adds slash", normalizePrefix "foo" == "/foo"),
  ("normalize drops trailing", normalizePrefix "/foo/" == "/foo"),
  ("normalize root", normalizePrefix "/" == "/"),
  -- mount resolution example
  ("mount /foo/y", resolvedPrefix exampleMounts "/foo/y" == some "/foo"),
  ("mount /foo/x/z", resolvedPrefix exampleMounts "/foo/x/z" == some "/foo/x"),
  ("mount /bar/a", resolvedPrefix exampleMounts "/bar/a" == some "/bar"),
  ("mount /baz", resolvedPrefix exampleMounts "/baz" == some "/"),
  ("mount root", resolvedPrefix exampleMounts "/" == some "/"),
  -- two mounts sharing a directory both resolve
  ("mounts same dir",
    let ms : Array Mount := #[{ urlPrefix := "/a", dir := "d" }, { urlPrefix := "/b", dir := "d" }]
    resolvedPrefix ms "/a/x" == some "/a" && resolvedPrefix ms "/b/y" == some "/b"),
  -- root precedence: positional dir, else config root, else current directory
  ("root from positional",
    let cfg : ServeConfig := { mounts := #[{ urlPrefix := "/", dir := "fromconfig" }] }
    cfg.withCli { dir := some "fromcli" }
      |>.mounts.find? (·.urlPrefix == "/")
      |>.map (·.dir.toString)
      |>.isEqSome "fromcli"),
  ("root from config",
    let cfg : ServeConfig := { mounts := #[{ urlPrefix := "/", dir := "fromconfig" }] }
    cfg.withCli {}
      |>.mounts.find? (·.urlPrefix == "/")
      |>.map (·.dir.toString)
      |>.isEqSome "fromconfig"),
  ("root falls back to cwd alongside other mounts",
    let cfg : ServeConfig := { mounts := #[{ urlPrefix := "/foo", dir := "f" }] }
    cfg.withCli {}
      |>.mounts.find? (·.urlPrefix == "/")
      |>.map (·.dir.toString)
      |>.isEqSome "."),
  -- range parsing
  ("range explicit", parseRange "bytes=0-9" 100 == .range 0 9),
  ("range suffix", parseRange "bytes=-10" 100 == .range 90 99),
  ("range open", parseRange "bytes=90-" 100 == .range 90 99),
  ("range past end", parseRange "bytes=200-" 100 == .unsatisfiable),
  ("range reversed", parseRange "bytes=5-2" 100 == .unsatisfiable),
  ("range multi", parseRange "bytes=0-9,20-30" 100 == .full),
  ("range absent", parseRange "items=0-9" 100 == .full),
  -- etag
  ("etag stable", etag "abc".toUTF8 == etag "abc".toUTF8),
  ("etag distinct", etag "abc".toUTF8 != etag "abd".toUTF8),
  -- redirects
  ("redirect prefix",
    matchRedirect #[{ fromPath := "/old", toPath := "/new", status := .movedPermanently }] "/old/x"
      |>.isEqSome (.movedPermanently, "/new/x")),
  ("redirect miss",
    matchRedirect #[{ fromPath := "/old", toPath := "/new", status := .movedPermanently }] "/other" |>.isNone),
  ("redirect first wins",
    matchRedirect #[{ fromPath := "/a", toPath := "/x", status := .movedPermanently },
                    { fromPath := "/a", toPath := "/y", status := .found }] "/a" ==
      some (.movedPermanently, "/x")),
  -- redirect status validation rejects non-redirect codes
  ("redirect status valid", RedirectStatus.ofNat? 308 == some .permanentRedirect),
  ("redirect status invalid", RedirectStatus.ofNat? 404 == none),
  -- port subtype rejects out-of-range and zero
  ("port valid", (Port.ofNat? 8080).map (·.toNat) == some 8080),
  ("port zero", Port.ofNat? 0 == none),
  ("port too large", Port.ofNat? 70000 == none),
  -- header rules
  ("header rule match",
    matchHeaderRules #[{ path := "/assets", set := #[("X-Frame-Options", "DENY")] }] "/assets/a.js" ==
      #[("X-Frame-Options", "DENY")]),
  ("header rule miss",
    matchHeaderRules #[{ path := "/assets", set := #[("X-Frame-Options", "DENY")] }] "/other" == #[]),
  -- escaping
  ("html escape", htmlEscape "<a>&\"" == "&lt;a&gt;&amp;&quot;"),
  -- header dedup keeps the last value for a name, matched case-insensitively
  ("dedup last wins",
    dedupHeaders #[("Cache-Control", "no-cache"), ("cache-control", "max-age=1"), ("ETag", "x")] ==
      #[("cache-control", "max-age=1"), ("ETag", "x")]),
  -- control-character detection accepts non-ASCII scripts but rejects C0/C1 controls
  ("unicode Danish ok", !hasControlChar #["øllebrød"]),
  ("unicode Arabic ok", !hasControlChar #["اَلْعَرَبِيَّةُ"]),
  ("unicode Chinese ok", !hasControlChar #["中文文件"]),
  ("unicode Devanagari ok", !hasControlChar #["नमस्ते"]),
  ("unicode emoji ok", !hasControlChar #["All goals proved!🎉"]),
  ("unicode fraktur ok", !hasControlChar #["𝔏𝔢𝔞𝔫"]),
  ("c0 control detected", hasControlChar #[String.singleton (Char.ofNat 0x0d)]),
  ("c1 control detected", hasControlChar #[String.singleton (Char.ofNat 0x85)]),
]

/-! ## In-process integration (Mock transport) -/

/-- Sends a raw HTTP request to a handler over an in-memory connection and returns the raw response. -/
def runRequest (handler : Server.StatelessHandler) (raw : String) : IO String :=
  Async.block do
    let (client, server) ← Std.Http.Internal.Mock.new
    client.send raw.toUTF8
    client.getSendChan.close
    Server.serveConnection server handler { generateDate := false } |>.run
    let res ← client.recv?
    return String.fromUTF8! (res.getD .empty)

/-- A `GET` request line with a `Connection: close` header so the server completes after one reply. -/
def get (path : String) : String :=
  s!"GET {path} HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n"

/-- A `HEAD` request line with a `Connection: close` header. -/
def head (path : String) : String :=
  s!"HEAD {path} HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n"

/-- The value of the named header in a raw HTTP response, matched case-insensitively. -/
def headerValue (response : String) (name : String) : Option String :=
  (response.splitOn "\r\n").find? (·.toLower.startsWith (name.toLower ++ ":"))
    |>.map fun line => (line.drop (name.length + 1)).trimAscii.copy

/-- The uppercase hexadecimal digit for a value below sixteen. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + '0'.toNat) else Char.ofNat (n - 10 + 'A'.toNat)

/-- Percent-encodes a string's UTF-8 bytes, leaving the unreserved characters as they are. -/
def percentEncode (s : String) : String :=
  s.toUTF8.foldl (init := "") fun acc b =>
    let n := b.toNat
    let unreserved :=
      (n >= 0x30 && n <= 0x39) || (n >= 0x41 && n <= 0x5a) || (n >= 0x61 && n <= 0x7a)
        || n == 0x2d || n == 0x2e || n == 0x5f || n == 0x7e
    if unreserved then acc.push (Char.ofNat n)
    else acc ++ s!"%{hexDigit (n / 16)}{hexDigit (n % 16)}"

/-- File names in scripts the server should serve unchanged. -/
def unicodeNames : List String :=
  ["øllebrød", "اَلْعَرَبِيَّةُ", "中文文件", "नमस्ते", "All goals proved!🎉", "𝔏𝔢𝔞𝔫"]

/-- Runs the integration checks against a temporary directory tree, returning failure messages. -/
def integrationFailures : IO (Array String) := do
  let tmp ← IO.FS.createTempDir
  -- The served directory is a subdirectory, so a sibling file lets us probe traversal escapes.
  let root := tmp / "site"
  IO.FS.createDirAll root
  IO.FS.writeFile (root / "index.html") "<h1>home</h1>"
  IO.FS.writeFile (root / "data.txt") "0123456789"
  IO.FS.writeFile (tmp / "secret.txt") "TOPSECRET"
  let mounts ← (#[{ urlPrefix := "/", dir := root : Mount }] : Array Mount).mapM fun m =>
    return { urlPrefix := m.urlPrefix, root := ← IO.FS.realPath m.dir : ResolvedMount }
  let handler := mkHandler {} mounts
  -- A second configuration sets a custom Cache-Control to check that it overrides the default.
  let overrideCfg : ServeConfig :=
    { headers := #[{ path := "/", set := #[("Cache-Control", "max-age=99")] }] }
  let overrideHandler := mkHandler overrideCfg mounts
  let check (name : String) (raw : String) (pred : String → Bool) :
      StateT (Array String) IO Unit := do
    unless pred (← runRequest handler raw) do modify (·.push name)
  let (_, fails) ← StateT.run (s := #[]) do
    check "index 200" (get "/") fun r => r.startsWith "HTTP/1.1 200" && (r.splitOn "home").length > 1
    check "missing 404" (get "/nope") (·.startsWith "HTTP/1.1 404")
    check "post 405" "POST / HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"
      (·.startsWith "HTTP/1.1 405")
    -- HEAD reports the content length without a body, and `data.txt` holds ten bytes.
    check "head no body" (head "/data.txt") fun r =>
      r.startsWith "HTTP/1.1 200"
        && (r.toLower.splitOn "content-length: 10").length == 2
        && (r.splitOn "0123456789").length == 1
    -- Path traversal: an encoded `..` must not escape the mount root or leak the sibling file.
    check "encoded traversal blocked" (get "/%2e%2e/secret.txt") fun r =>
      !r.startsWith "HTTP/1.1 200" && (r.splitOn "TOPSECRET").length == 1
    -- A control character in the path (here CR LF, percent-encoded) is rejected with 400.
    check "control char rejected" (get "/foo%0d%0abar") (·.startsWith "HTTP/1.1 400")
    -- Files named in non-ASCII scripts are served when requested with their percent-encoded names.
    for name in unicodeNames do
      let fileName := name ++ ".txt"
      IO.FS.writeFile (root / fileName) s!"BODY {name}"
      check s!"unicode file {name}" (get s!"/{percentEncode fileName}") fun r =>
        r.startsWith "HTTP/1.1 200" && (r.splitOn s!"BODY {name}").length == 2
    -- Caching: validators are present, and a conditional request revalidates to 304.
    let first ← runRequest handler (get "/data.txt")
    unless first.startsWith "HTTP/1.1 200"
        && (first.toLower.splitOn "cache-control: no-cache").length > 1
        && (first.toLower.splitOn "last-modified:").length > 1 do
      modify (·.push "cache validators")
    match headerValue first "etag" with
    | none => modify (·.push "etag header")
    | some etag =>
      let cond := s!"GET /data.txt HTTP/1.1\r\nHost: x\r\nIf-None-Match: {etag}\r\nConnection: close\r\n\r\n"
      unless (← runRequest handler cond).startsWith "HTTP/1.1 304" do
        modify (·.push "conditional 304")
    -- A custom Cache-Control rule replaces the default rather than producing a duplicate.
    let over ← runRequest overrideHandler (get "/data.txt")
    unless (over.toLower.splitOn "cache-control: max-age=99").length == 2
        && (over.toLower.splitOn "cache-control: no-cache").length == 1 do
      modify (·.push "custom header override")
    -- An invalid header name in the config is rejected when the file is parsed.
    let badConfig := "[[headers]]\npath = \"/\"\nset = { \"bad name\" = \"x\" }"
    match ← (parseServeConfig badConfig).toBaseIO with
    | .ok _ => modify (·.push "invalid header name accepted")
    | .error _ => pure ()
  IO.FS.removeDirAll tmp
  return fails

/-! ## Entry point -/

/-- Runs every serve test, printing each result and returning the number of failures. -/
public def runServeTests : IO Nat := do
  let mut failures := 0
  for (name, test) in props do
    IO.print s!"{name}: "
    let res ← test.2
    IO.println res
    unless res matches .success .. do failures := failures + 1
  for (name, ok) in units do
    if ok then
      IO.println s!"{name}: ok"
    else
      IO.println s!"{name}: FAILED"
      failures := failures + 1
  for name in ← integrationFailures do
    IO.println s!"integration {name}: FAILED"
    failures := failures + 1
  return failures
