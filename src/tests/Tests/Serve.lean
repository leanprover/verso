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
  ("range malformed end", parseRange "bytes=5-x" 100 == .full),
  ("range malformed start", parseRange "bytes=x-5" 100 == .full),
  ("range both empty", parseRange "bytes=-" 100 == .full),
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
  -- exact match leaves nothing to append beneath the prefix
  ("redirect exact",
    matchRedirect #[{ fromPath := "/old", toPath := "/new", status := .movedPermanently }] "/old"
      |>.isEqSome (.movedPermanently, "/new")),
  -- the root prefix matches every path and carries the whole path onto the target
  ("redirect root prefix",
    matchRedirect #[{ fromPath := "/", toPath := "/new", status := .movedPermanently }] "/foo/bar"
      |>.isEqSome (.movedPermanently, "/new/foo/bar")),
  ("redirect root exact",
    matchRedirect #[{ fromPath := "/", toPath := "/new", status := .movedPermanently }] "/"
      |>.isEqSome (.movedPermanently, "/new")),
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
  -- listing links percent-encode the href while the link text stays readable
  ("listing href encodes",
    let html := renderListing "/" #[("a b#c.txt", false)]
    (html.splitOn "href=\"a%20b%23c.txt\"").length != 1 && (html.splitOn ">a b#c.txt<").length != 1),
  ("listing dir href keeps slash",
    let html := renderListing "/" #[("my dir", true)]
    (html.splitOn "href=\"my%20dir/\"").length != 1),
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
  -- path confinement drops `.`, pops `..`, and refuses to climb above the root
  ("confine plain", confineSegments #["a", "b"] |>.isEqSome #["a", "b"]),
  ("confine dot dropped", confineSegments #["a", ".", "b"] |>.isEqSome #["a", "b"]),
  ("confine dotdot pops", confineSegments #["a", "..", "b"] |>.isEqSome #["b"]),
  ("confine escape rejected", confineSegments #[".."] |>.isNone),
  ("confine deep escape rejected", confineSegments #["a", "..", "..", "b"] |>.isNone),
  -- a segment that decoded to contain a separator is refused, so it cannot carry a `..`
  ("confine rejects embedded slash", confineSegments #["a/b"] |>.isNone),
  ("confine rejects encoded traversal", confineSegments #["../secret.txt"] |>.isNone),
  -- command-line flags fold into the configuration they override
  ("cli no-listing disables",
    ({ directoryListing := true : ServeConfig }.withCli { noListing := true }).directoryListing == false),
  ("cli keeps listing by default",
    ({ directoryListing := true : ServeConfig }.withCli {}).directoryListing == true),
  ("cli cors enables",
    ({ cors := false : ServeConfig }.withCli { cors := true }).cors == true),
  ("cli no-trailing-slash disables",
    ({ trailingSlashRedirect := true : ServeConfig }.withCli { noTrailingSlash := true }).trailingSlashRedirect == false),
  ("cli port overrides",
    (({} : ServeConfig).withCli { port := Port.ofNat? 9000 }).port.toNat == 9000),
  -- argument parsing accepts valid forms and rejects malformed ones
  ("args long port", parseArgs ["--port", "9000"] |>.toOption.bind (·.port) |>.map (·.toNat) |>.isEqSome 9000),
  ("args short port", parseArgs ["-p", "3000"] |>.toOption.bind (·.port) |>.map (·.toNat) |>.isEqSome 3000),
  ("args positional dir", parseArgs ["site"] |>.toOption.bind (·.dir) |>.map (·.toString) |>.isEqSome "site"),
  ("args boolean flags",
    parseArgs ["--cors", "--quiet"] |>.toOption.map (fun a => a.cors && a.quiet) |>.isEqSome true),
  ("args unknown option rejected", (parseArgs ["--nope"]).toOption.isNone),
  ("args missing port value rejected", (parseArgs ["--port"]).toOption.isNone),
  ("args non-numeric port rejected", (parseArgs ["--port", "x"]).toOption.isNone),
  ("args out-of-range port rejected", (parseArgs ["--port", "0"]).toOption.isNone),
  ("args extra positional rejected", (parseArgs ["a", "b"]).toOption.isNone),
  -- port scanning skips taken ports and reports the one it settled on
  ("port scan skips taken",
    (Id.run <| firstAvailable (m := Id) (fun p => if [8000, 8001].contains p.toNat then none else some p) 8000)
      |>.map (·.1.toNat) |>.isEqSome 8002),
  ("port scan all taken",
    (Id.run <| firstAvailable (m := Id) (fun (_ : UInt16) => (none : Option UInt16)) 8000).isNone),
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
  -- Further configurations exercise CORS, redirects, listings, and the trailing-slash toggle.
  let corsHandler := mkHandler { cors := true } mounts
  let redirectHandler :=
    mkHandler { redirects := #[{ fromPath := "/old", toPath := "/new" }] } mounts
  let noListingHandler := mkHandler { directoryListing := false } mounts
  let noSlashHandler := mkHandler { trailingSlashRedirect := false } mounts
  let followHandler := mkHandler { followSymlinksOutsideRoot := true } mounts
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
    -- A directory without an index file is served as a generated HTML listing of its entries.
    IO.FS.createDirAll (root / "listing")
    IO.FS.writeFile (root / "listing" / "note.txt") "hi"
    check "directory listing" (get "/listing/") fun r =>
      r.startsWith "HTTP/1.1 200" && (r.splitOn "Index of").length > 1 && (r.splitOn "note.txt").length > 1
    -- With listings disabled, the same directory is refused.
    unless (← runRequest noListingHandler (get "/listing/")).startsWith "HTTP/1.1 403" do
      modify (·.push "no-listing 403")
    -- A directory requested without a trailing slash redirects to add one.
    check "trailing slash redirect" (get "/listing") fun r =>
      r.startsWith "HTTP/1.1 301" && (r.toLower.splitOn "location: /listing/").length == 2
    -- With the redirect disabled, the directory is served in place.
    unless (← runRequest noSlashHandler (get "/listing")).startsWith "HTTP/1.1 200" do
      modify (·.push "no-trailing-slash serves in place")
    -- A configured redirect rule returns a 301 whose location carries the path beneath the prefix.
    let red ← runRequest redirectHandler (get "/old/page")
    unless red.startsWith "HTTP/1.1 301" && (red.toLower.splitOn "location: /new/page").length == 2 do
      modify (·.push "redirect rule")
    -- CORS: a preflight is answered with 204, and a GET carries the cross-origin header.
    let pre ← runRequest corsHandler "OPTIONS / HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"
    unless pre.startsWith "HTTP/1.1 204"
        && (pre.toLower.splitOn "access-control-allow-methods").length > 1 do
      modify (·.push "cors preflight")
    unless ((← runRequest corsHandler (get "/data.txt")).toLower.splitOn "access-control-allow-origin: *").length > 1 do
      modify (·.push "cors get header")
    -- Without CORS, OPTIONS is not allowed.
    unless (← runRequest handler "OPTIONS / HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n").startsWith "HTTP/1.1 405" do
      modify (·.push "options 405")
    -- A Range request returns the requested slice with 206 and a Content-Range header.
    let ranged ← runRequest handler "GET /data.txt HTTP/1.1\r\nHost: x\r\nRange: bytes=2-5\r\nConnection: close\r\n\r\n"
    unless ranged.startsWith "HTTP/1.1 206"
        && (ranged.toLower.splitOn "content-range: bytes 2-5/10").length == 2
        && (ranged.splitOn "2345").length > 1 do
      modify (·.push "range 206")
    -- An unsatisfiable range is rejected with 416.
    unless (← runRequest handler "GET /data.txt HTTP/1.1\r\nHost: x\r\nRange: bytes=50-60\r\nConnection: close\r\n\r\n").startsWith "HTTP/1.1 416" do
      modify (·.push "range 416")
    -- Relaxing symlink confinement still does not permit `..` to climb above the mount.
    let escaped ← runRequest followHandler (get "/%2e%2e/secret.txt")
    unless !escaped.startsWith "HTTP/1.1 200" && (escaped.splitOn "TOPSECRET").length == 1 do
      modify (·.push "follow-symlinks still confines traversal")
    -- An encoded slash must not smuggle `..` past confinement, even with symlinks relaxed.
    let slashEscaped ← runRequest followHandler (get "/..%2Fsecret.txt")
    unless !slashEscaped.startsWith "HTTP/1.1 200" && (slashEscaped.splitOn "TOPSECRET").length == 1 do
      modify (·.push "follow-symlinks still confines encoded-slash traversal")
    -- A complete configuration parses into ports, mounts, redirects, and headers.
    let goodConfig :=
      "port = 4000\n[[mounts]]\npath = \"/api\"\ndir = \"out\"\n" ++
        "[[redirects]]\nfrom = \"/old\"\nto = \"/new\"\nstatus = 302\n" ++
        "[[headers]]\npath = \"/\"\nset = { \"X-Frame-Options\" = \"DENY\" }"
    match ← (parseServeConfig goodConfig).toBaseIO with
    | .error _ => modify (·.push "valid config rejected")
    | .ok cfg =>
      unless cfg.port.toNat == 4000 && cfg.mounts.size == 1
          && cfg.redirects.any (·.status == .found) && cfg.headers.size == 1 do
        modify (·.push "valid config fields")
    -- An unknown top-level key is rejected.
    match ← (parseServeConfig "nonsense = 1").toBaseIO with
    | .ok _ => modify (·.push "unknown key accepted")
    | .error _ => pure ()
    -- A status that is not a redirect code is rejected.
    match ← (parseServeConfig "[[redirects]]\nfrom = \"/a\"\nto = \"/b\"\nstatus = 404").toBaseIO with
    | .ok _ => modify (·.push "bad redirect status accepted")
    | .error _ => pure ()
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
