/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Errata
import Std.Http
import Plausible
import Plausible.ArbitraryFueled
import VersoServe
import VersoServe.Static

open Errata
open Plausible
open Std Async Http
open VersoServe

namespace Verso.Tests.Serve

/-! ## Property-based checks (Plausible) -/

/-- A range result stays within bounds whenever it selects a sub-range. -/
@[test]
def rangeBounds : Test := property <| ∀ (a b size : Nat), show Bool from
  match parseRange s!"bytes={a}-{b}" size with
  | .range s e => s ≤ e && e < size
  | _ => true

/-- The resolved mount's prefix is genuinely a prefix of the request, and no match is missed. -/
@[test]
def mountPrefix : Test := property <| ∀ (prefixes segs : Array String), show Bool from
  match resolveMountBy id prefixes segs with
  | some (p, _) => (prefixSegments p).isPrefixOf segs
  | none => prefixes.all fun q => !(prefixSegments q).isPrefixOf segs

/-- The chosen mount has the longest matching prefix of any candidate. -/
@[test]
def mountLongest : Test := property <| ∀ (prefixes segs : Array String), show Bool from
  match resolveMountBy id prefixes segs with
  | some (p, _) =>
    prefixes.all fun q =>
      !(prefixSegments q).isPrefixOf segs || (prefixSegments q).size ≤ (prefixSegments p).size
  | none => True

/-- Mount resolution does not depend on the order of the mount table. -/
@[test]
def mountShuffle : Test := property <| ∀ (prefixes segs : Array String),
  (resolveMountBy id prefixes segs).map (·.1) ==
    (resolveMountBy id prefixes.reverse segs).map (·.1)

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
private def units : List (String × Bool) := [
  -- MIME
  ("mime html", mimeType? "HTML" == some ⟨"text", "html"⟩),
  ("mime css charset", contentTypeForPath "a.css" == "text/css; charset=utf-8"),
  ("mime svg charset", contentTypeForPath "a.svg" == "image/svg+xml; charset=utf-8"),
  ("mime json charset", contentTypeForPath "a.json" == "application/json; charset=utf-8"),
  ("mime xml charset", contentTypeForPath "a.xml" == "application/xml; charset=utf-8"),
  ("mime png no charset", contentTypeForPath "A.PNG" == "image/png"),
  ("mime unknown", contentTypeForPath "a.xyz" == "application/octet-stream"),
  -- an unknown extension is sniffed from the contents, so a text script is shown rather than downloaded
  ("sniff text script", contentTypeForFile "foo.sh" "#!/bin/sh\necho hi\n".toUTF8 == "text/plain; charset=utf-8"),
  ("sniff binary octet-stream", contentTypeForFile "blob.xyz" (ByteArray.mk #[0x00, 0x01, 0x02]) == "application/octet-stream"),
  ("sniff known extension wins", contentTypeForFile "page.html" (ByteArray.mk #[0x00]) == "text/html; charset=utf-8"),
  ("looks textual utf-8", looksTextual "héllo".toUTF8),
  ("looks binary on nul", !looksTextual (ByteArray.mk #[0x41, 0x00, 0x42])),
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
  -- the root mount comes from the positional dir, else the config root, else the current directory
  ("root from positional",
    ({} : ServeConfig).withCli { dir := some "fromcli" }
      |>.toOption
      |>.bind (·.mounts.find? (·.urlPrefix == "/"))
      |>.map (·.dir.toString)
      |>.isEqSome "fromcli"),
  ("root from config",
    let cfg : ServeConfig := { mounts := #[{ urlPrefix := "/", dir := "fromconfig" }] }
    cfg.withCli {}
      |>.toOption
      |>.bind (·.mounts.find? (·.urlPrefix == "/"))
      |>.map (·.dir.toString)
      |>.isEqSome "fromconfig"),
  ("root falls back to cwd alongside other mounts",
    let cfg : ServeConfig := { mounts := #[{ urlPrefix := "/foo", dir := "f" }] }
    cfg.withCli {}
      |>.toOption
      |>.bind (·.mounts.find? (·.urlPrefix == "/"))
      |>.map (·.dir.toString)
      |>.isEqSome "."),
  -- a positional dir is rejected when the config file defines mounts, root or otherwise
  ("positional rejected with config root mount",
    let cfg : ServeConfig := { mounts := #[{ urlPrefix := "/", dir := "fromconfig" }] }
    (cfg.withCli { dir := some "fromcli" }).toOption.isNone),
  ("positional rejected with other config mounts",
    let cfg : ServeConfig := { mounts := #[{ urlPrefix := "/foo", dir := "f" }] }
    (cfg.withCli { dir := some "fromcli" }).toOption.isNone),
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
  ("range oversized header", parseRange ("bytes=0-" ++ String.ofList (List.replicate 300 '0')) 100 == .full),
  ("range zero size", parseRange "bytes=0-9" 0 == .unsatisfiable),
  -- confinement is by path component, so a sibling whose name extends the root is outside it
  ("within self", isWithin "/site" "/site"),
  ("within child", isWithin "/site" "/site/index.html"),
  ("within rejects sibling", !isWithin "/site" "/sitething"),
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
  ("cli keeps listing by default",
    ({ directoryListing := true : ServeConfig }.withCli {}).toOption
      |>.map (·.directoryListing) |>.isEqSome true),
  ("cli port overrides",
    (({} : ServeConfig).withCli { port := Port.ofNat? 9000 }).toOption
      |>.map (·.port.toNat) |>.isEqSome 9000),
  -- argument parsing accepts valid forms and rejects malformed ones
  ("args long port", VersoServe.parseArgs ["--port", "9000"] |>.toOption.bind (·.port) |>.map (·.toNat) |>.isEqSome 9000),
  ("args short port", VersoServe.parseArgs ["-p", "3000"] |>.toOption.bind (·.port) |>.map (·.toNat) |>.isEqSome 3000),
  ("args positional dir", VersoServe.parseArgs ["site"] |>.toOption.bind (·.dir) |>.map (·.toString) |>.isEqSome "site"),
  ("args boolean flags",
    VersoServe.parseArgs ["--quiet"] |>.toOption.map (fun a => a.quiet) |>.isEqSome true),
  ("args unknown option rejected", (VersoServe.parseArgs ["--nope"]).toOption.isNone),
  ("args missing port value rejected", (VersoServe.parseArgs ["--port"]).toOption.isNone),
  ("args non-numeric port rejected", (VersoServe.parseArgs ["--port", "x"]).toOption.isNone),
  ("args out-of-range port rejected", (VersoServe.parseArgs ["--port", "0"]).toOption.isNone),
  ("args extra positional rejected", (VersoServe.parseArgs ["a", "b"]).toOption.isNone),
  -- port scanning skips taken ports and reports the one it settled on
  ("port scan skips taken",
    (Id.run <| firstAvailable (m := Id) (fun p => if [8000, 8001].contains p.toNat then none else some p) 8000)
      |>.map (·.1.toNat) |>.isEqSome 8002),
  ("port scan all taken",
    (Id.run <| firstAvailable (m := Id) (fun (_ : UInt16) => (none : Option UInt16)) 8000).isNone),
  -- scanning never wraps past the maximum port: offsets above 65535 are skipped, not retried
  ("port scan stops at max",
    (Id.run <| firstAvailable (m := Id) (fun p => if p.toNat == 65535 then none else some p) 65535).isNone),
]

/-- Every deterministic unit check in {name}`units` passes, reported as one result per check. -/
@[test]
def unitChecks : Test := do
  for (name, ok) in units do
    result name (assertTrue ok)

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

/--
Every in-process integration check against the mock transport passes, reported as one result per
check.
-/
@[test]
def integration : Test := do
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
  let check (name : String) (raw : String) (pred : String → Bool) : TestM Unit := do
    result name do
      let response ← runRequest handler raw
      assertTrue (pred response) "unexpected response" (detail? := some response)
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
  -- An unknown extension is sniffed: a UTF-8 text script is served inline as text/plain.
  IO.FS.writeFile (root / "script.sh") "#!/bin/sh\necho hi\n"
  check "unknown text served inline" (get "/script.sh") fun r =>
    r.startsWith "HTTP/1.1 200" && (r.toLower.splitOn "content-type: text/plain").length == 2
  -- A binary file with an unknown extension stays application/octet-stream.
  IO.FS.writeBinFile (root / "blob.xyz") (ByteArray.mk #[0x00, 0x01, 0x02, 0x00])
  check "unknown binary octet-stream" (get "/blob.xyz") fun r =>
    r.startsWith "HTTP/1.1 200" && (r.toLower.splitOn "content-type: application/octet-stream").length == 2
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
  result "cache validators" do
    assertTrue (first.startsWith "HTTP/1.1 200"
        && (first.toLower.splitOn "cache-control: no-cache").length > 1
        && (first.toLower.splitOn "last-modified:").length > 1)
      "unexpected response" (detail? := some first)
  result "conditional 304" do
    let some etag := headerValue first "etag"
      | fail "no ETag header on the response" (detail? := some first)
    let cond := s!"GET /data.txt HTTP/1.1\r\nHost: x\r\nIf-None-Match: {etag}\r\nConnection: close\r\n\r\n"
    let response ← runRequest handler cond
    assertTrue (response.startsWith "HTTP/1.1 304") "unexpected response" (detail? := some response)
  -- A custom Cache-Control rule replaces the default rather than producing a duplicate.
  let over ← runRequest overrideHandler (get "/data.txt")
  result "custom header override" do
    assertTrue ((over.toLower.splitOn "cache-control: max-age=99").length == 2
        && (over.toLower.splitOn "cache-control: no-cache").length == 1)
      "unexpected response" (detail? := some over)
  -- A directory without an index file is served as a generated HTML listing of its entries.
  IO.FS.createDirAll (root / "listing")
  IO.FS.writeFile (root / "listing" / "note.txt") "hi"
  check "directory listing" (get "/listing/") fun r =>
    r.startsWith "HTTP/1.1 200" && (r.splitOn "Index of").length > 1 && (r.splitOn "note.txt").length > 1
  -- With listings disabled, the same directory is refused.
  result "no-listing 403" do
    let response ← runRequest noListingHandler (get "/listing/")
    assertTrue (response.startsWith "HTTP/1.1 403") "unexpected response" (detail? := some response)
  -- A directory requested without a trailing slash redirects to add one.
  check "trailing slash redirect" (get "/listing") fun r =>
    r.startsWith "HTTP/1.1 301" && (r.toLower.splitOn "location: /listing/").length == 2
  -- With the redirect disabled, the directory is served in place.
  result "no-trailing-slash serves in place" do
    let response ← runRequest noSlashHandler (get "/listing")
    assertTrue (response.startsWith "HTTP/1.1 200") "unexpected response" (detail? := some response)
  -- A configured redirect rule returns a 301 whose location carries the path beneath the prefix.
  result "redirect rule" do
    let red ← runRequest redirectHandler (get "/old/page")
    assertTrue (red.startsWith "HTTP/1.1 301" && (red.toLower.splitOn "location: /new/page").length == 2)
      "unexpected response" (detail? := some red)
  -- CORS: a preflight is answered with 204, and a GET carries the cross-origin header.
  result "cors preflight" do
    let pre ← runRequest corsHandler "OPTIONS / HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"
    assertTrue (pre.startsWith "HTTP/1.1 204"
        && (pre.toLower.splitOn "access-control-allow-methods").length > 1)
      "unexpected response" (detail? := some pre)
  result "cors get header" do
    let response ← runRequest corsHandler (get "/data.txt")
    assertTrue ((response.toLower.splitOn "access-control-allow-origin: *").length > 1)
      "unexpected response" (detail? := some response)
  -- Without CORS, OPTIONS is not allowed.
  result "options 405" do
    let response ← runRequest handler "OPTIONS / HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"
    assertTrue (response.startsWith "HTTP/1.1 405") "unexpected response" (detail? := some response)
  -- A Range request returns the requested slice with 206 and a Content-Range header.
  result "range 206" do
    let ranged ← runRequest handler "GET /data.txt HTTP/1.1\r\nHost: x\r\nRange: bytes=2-5\r\nConnection: close\r\n\r\n"
    assertTrue (ranged.startsWith "HTTP/1.1 206"
        && (ranged.toLower.splitOn "content-range: bytes 2-5/10").length == 2
        && (ranged.splitOn "2345").length > 1)
      "unexpected response" (detail? := some ranged)
  -- An unsatisfiable range is rejected with 416.
  result "range 416" do
    let response ← runRequest handler "GET /data.txt HTTP/1.1\r\nHost: x\r\nRange: bytes=50-60\r\nConnection: close\r\n\r\n"
    assertTrue (response.startsWith "HTTP/1.1 416") "unexpected response" (detail? := some response)
  -- Relaxing symlink confinement still does not permit `..` to climb above the mount.
  result "follow-symlinks still confines traversal" do
    let escaped ← runRequest followHandler (get "/%2e%2e/secret.txt")
    assertTrue (!escaped.startsWith "HTTP/1.1 200" && (escaped.splitOn "TOPSECRET").length == 1)
      "unexpected response" (detail? := some escaped)
  -- An encoded slash must not smuggle `..` past confinement, even with symlinks relaxed.
  result "follow-symlinks still confines encoded-slash traversal" do
    let slashEscaped ← runRequest followHandler (get "/..%2Fsecret.txt")
    assertTrue (!slashEscaped.startsWith "HTTP/1.1 200" && (slashEscaped.splitOn "TOPSECRET").length == 1)
      "unexpected response" (detail? := some slashEscaped)
  -- A complete configuration parses into ports, mounts, redirects, and headers.
  result "valid config" do
    let goodConfig :=
      "port = 4000\n[[mounts]]\npath = \"/api\"\ndir = \"out\"\n" ++
        "[[redirects]]\nfrom = \"/old\"\nto = \"/new\"\nstatus = 302\n" ++
        "[[headers]]\npath = \"/\"\nset = { \"X-Frame-Options\" = \"DENY\" }"
    match ← (parseServeConfig goodConfig).toBaseIO with
    | .error e => fail "valid config rejected" (detail? := some (toString e))
    | .ok cfg =>
      assertTrue
        (cfg.port.toNat == 4000 && cfg.mounts.size == 1
          && cfg.redirects.any (·.status == .found) && cfg.headers.size == 1)
        "config fields not parsed as expected"
  -- An unknown top-level key is rejected.
  result "unknown key rejected" <|
    assertThrowsIO (parseServeConfig "nonsense = 1")
  -- A status that is not a redirect code is rejected.
  result "bad redirect status rejected" <|
    assertThrowsIO (parseServeConfig "[[redirects]]\nfrom = \"/a\"\nto = \"/b\"\nstatus = 404")
  -- Redirect targets are emitted as Location headers, so invalid header values are rejected.
  result "invalid redirect target rejected" <|
    assertThrowsIO (parseServeConfig "[[redirects]]\nfrom = \"/a\"\nto = \"/b\nX: y\"")
  -- An invalid header name in the config is rejected when the file is parsed.
  result "invalid header name rejected" <|
    assertThrowsIO (parseServeConfig "[[headers]]\npath = \"/\"\nset = { \"bad name\" = \"x\" }")
  -- Entries missing a required field are rejected rather than filled with a silent default.
  result "mount without dir rejected" <|
    assertThrowsIO (parseServeConfig "[[mounts]]\npath = \"/api\"")
  result "redirect without target rejected" <|
    assertThrowsIO (parseServeConfig "[[redirects]]\nfrom = \"/old\"")
  result "header without set rejected" <|
    assertThrowsIO (parseServeConfig "[[headers]]\npath = \"/\"")
  -- An empty or whitespace-only config behaves the same as no file: defaults throughout.
  result "empty config defaults" do
    for blank in ["", "   \n  \t\n"] do
      match ← (parseServeConfig blank).toBaseIO with
      | .error e => fail "empty config rejected" (detail? := some (toString e))
      | .ok cfg =>
        assertTrue
          (cfg.port.toNat == 8000 && cfg.mounts.isEmpty && cfg.directoryListing
            && cfg.trailingSlashRedirect && !cfg.cors)
          "empty config did not produce the defaults"
  -- Every unknown key in an entry is reported, not only the first.
  result "all unknown entry keys reported" do
    let twoBad := "[[mounts]]\npath = \"/\"\ndir = \"d\"\nbad1 = \"x\"\nbad2 = \"y\""
    match ← (parseServeConfig twoBad).toBaseIO with
    | .ok _ => fail "unknown entry keys accepted"
    | .error e =>
      let msg := toString e
      assertTrue ((msg.splitOn "bad1").length > 1 && (msg.splitOn "bad2").length > 1)
        "not every unknown entry key is reported" (detail? := some msg)
  -- Mount directories in a config file are resolved relative to the file's own directory.
  let cfgDir := tmp / "proj"
  IO.FS.createDirAll cfgDir
  IO.FS.writeFile (cfgDir / "verso-serve.toml") "[[mounts]]\npath = \"/\"\ndir = \"site\""
  result "config mount rebased to config dir" do
    let loaded ← loadServeConfig (cfgDir / "verso-serve.toml")
    assertTrue (loaded.mounts.size == 1 && loaded.mounts[0]!.dir == cfgDir / "site")
  -- An explicit config path that is missing is fatal; an existing one is returned.
  result "missing config path fatal" <|
    assertThrowsIO (resolveConfigFile { configPath := some (tmp / "nope.toml") })
  result "existing config path found" do
    match ← (resolveConfigFile { configPath := some (cfgDir / "verso-serve.toml") }).toBaseIO with
    | .ok (some _) => pure ()
    | _ => fail "existing config path not found"
  -- A mount whose directory is missing is fatal; an existing one resolves to an absolute root.
  result "missing mount dir fatal" <|
    assertThrowsIO (resolveMounts #[{ urlPrefix := "/", dir := tmp / "absent" }])
  result "existing mount dir resolved" do
    match ← (resolveMounts #[{ urlPrefix := "/", dir := root }]).toBaseIO with
    | .ok rms => assertTrue (rms.size == 1 && rms[0]!.root.isAbsolute) "mount dir not resolved"
    | .error e => fail "existing mount dir rejected" (detail? := some (toString e))
  IO.FS.removeDirAll tmp
