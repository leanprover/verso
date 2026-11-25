/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

import Errata
import Lean.Data.Html
import Verso.Output.Html.ContentSecurityPolicy
public meta import Verso.Output.Html.ContentSecurityPolicy

namespace Verso.Tests.ContentSecurityPolicy

open Lean (Html)
open Verso.Output.Html.ContentSecurityPolicy

def page (head body : Array Html) : Html :=
  html%{<html><head>{.seq head}</head><body>{.seq body}</body></html>}

def script (body : Html) : Html := html%{<script>{body}</script>}

def srcScript (src : String) : Html := html%{<script src={src}></script>}

def policyOf (h : Html) (config : Config := {}) : String := (collect config h).render

def hashesOf (h : Html) : Array String := (collect {} h).hashes

def basePolicy : String := "script-src 'self'; base-uri 'self'"

/- Normalization -/

#test_guard normalizeScriptBody "a\r\nb" == "a\nb"
#test_guard normalizeScriptBody "a\rb" == "a\nb"
#test_guard normalizeScriptBody "a\nb" == "a\nb"
#test_guard normalizeScriptBody "a\r\r\nb\r" == "a\n\nb\n"
#test_guard normalizeScriptBody "\r\n\r\n" == "\n\n"
#test_guard normalizeScriptBody "a\x00b" == "a\uFFFDb"
#test_guard normalizeScriptBody "héllo, wörld" == "héllo, wörld"

#test_guard scriptHash "a\r\nb" == scriptHash "a\nb"
#test_guard scriptHash "a\rb" == scriptHash "a\nb"
#test_guard scriptHash "a\x00b" == scriptHash "a\uFFFDb"
#test_guard scriptHash "a" != scriptHash "b"
#test_guard (scriptHash "x").startsWith "'sha256-"
#test_guard (scriptHash "x").endsWith "'"

/- Exact hashes, computed with `printf '%s' "$body" | openssl dgst -sha256 -binary | openssl base64 -A` -/

#test_guard scriptHash "" == "'sha256-47DEQpj8HBSa+/TImW+5JCeuQeRkm5NMpJWZG3hSuFU='"
#test_guard scriptHash "a\nb" == "'sha256-fhj3NzEbLcOy8mndeDlrA1HxT7Zu+oefdoyyMYGIPHg='"
#test_guard scriptHash "a\r\nb" == "'sha256-fhj3NzEbLcOy8mndeDlrA1HxT7Zu+oefdoyyMYGIPHg='"
#test_guard scriptHash "a\rb" == "'sha256-fhj3NzEbLcOy8mndeDlrA1HxT7Zu+oefdoyyMYGIPHg='"
#test_guard scriptHash "a\x00b" == "'sha256-BQh4Ezku/Bb+j/RIkgxjKOU6+GXfOUGUNmWdn/2pD3s='"

/- Script bodies are hashed as the printer renders them -/

def jsSource : String := "if (a && b < c) { log(\"héllo\"); }"

#test_guard hashesOf (page #[script (.text jsSource)] #[]) ==
  #[scriptHash "if (a &amp;&amp; b &lt; c) { log(\"héllo\"); }"]
#test_guard hashesOf (page #[script (.raw jsSource)] #[]) == #[scriptHash jsSource]
#test_guard hashesOf (page #[script (.seq #[.raw "let x = 1;", .text " a < b"])] #[]) ==
  #[scriptHash "let x = 1; a &lt; b"]
#test_guard hashesOf (page #[script .empty] #[]) == #[scriptHash ""]

#test_guard hashesOf (page #[script (.text jsSource)] #[]) ==
  #["'sha256-SVsnvpw/UvI5UPXXMp+eFea6wtLC0yCssJiUxsWjMZo='"]
#test_guard hashesOf (page #[script (.raw jsSource)] #[]) ==
  #["'sha256-EW9HhRel9YXibtoCk63tLBdMCOlhPacfTwc5zLrW+e0='"]

/- Every inline script counts, wherever it is and whatever its type -/

#test_guard hashesOf (page
    #[script (.raw "one")]
    #[html%{<div>{script (.raw "two")}</div>},
      html%{<script type="module">{.raw "three"}</script>},
      html%{<script type="application/json">{.raw "four"}</script>},
      html%{<noscript>{script (.raw "five")}</noscript>},
      html%{<svg>{script (.raw "six")}</svg>}]) ==
  #[scriptHash "one", scriptHash "two", scriptHash "three", scriptHash "four", scriptHash "five",
    scriptHash "six"]

#test_guard hashesOf (page #[] #[script (.raw "same"), script (.raw "other"), script (.raw "same")]) ==
  #[scriptHash "same", scriptHash "other"]

#test_guard hashesOf (page #[] #[html%{<SCRIPT>{.raw "upper"}</SCRIPT>}]) == #[scriptHash "upper"]

#test_guard hashesOf (page #[] #[html%{<script SRC="/a.js">{.raw "ignored"}</script>}]) == #[]

/- Hosts and sources -/

def hostName? (text : String) : Option String :=
  (Host.ofString text).toOption.map (·.name)

#test_guard hostName? "cdn.example" == some "cdn.example"
#test_guard hostName? "CDN.Example" == some "cdn.example"
#test_guard hostName? "localhost" == some "localhost"
#test_guard hostName? "a-b.c-d.example" == some "a-b.c-d.example"
#test_guard hostName? "127.0.0.1" == some "127.0.0.1"

def badHostTexts : Array String := #[
  "", "*", "*.example", "a..example", ".a.example", "a.example.", "a_b.example",
  "user@a.example", "[::1]", "a.example:443", "https://a.example", "a.example/path",
  "a.example;script-src", "a example", " a.example", "a.example\n", "'self'", "a'b", "a,b", "é.example"
]

#test_guard badHostTexts.all fun text =>
  match Host.ofString text with
  | .ok _ => false
  | .error message => !message.isEmpty

def portNumber? (port : Int) : Option UInt16 := (Port.ofInt port).toOption.map (·.number)

#test_guard portNumber? 1 == some 1
#test_guard portNumber? 443 == some 443
#test_guard portNumber? 8443 == some 8443
#test_guard portNumber? 65535 == some 65535
#test_guard #[0, -1, 65536, 100000].all fun n =>
  match Port.ofInt n with
  | .ok _ => false
  | .error message => !message.isEmpty

def sourceOf (host : String) (scheme : Option Scheme := none)
    (onlySubdomains : Bool := false) (port : Option Int := none) : Array Source :=
  match Host.ofString host, port.mapM Port.ofInt with
  | .ok host, .ok port => #[{ scheme, host, onlySubdomains, port }]
  | _, _ => #[]

def renderSources (sources : Array Source) : Array String := sources.map (·.render)

#test_guard renderSources (sourceOf "cdn.example" (some .https)) == #["https://cdn.example"]
#test_guard renderSources (sourceOf "cdn.example" (some .http)) == #["http://cdn.example"]
#test_guard renderSources (sourceOf "cdn.example" (port := some 8443)) == #["cdn.example:8443"]
#test_guard renderSources (sourceOf "example.com" (onlySubdomains := true)) == #["*.example.com"]
#test_guard renderSources (sourceOf "example.com" (some .https) true (some 443)) ==
  #["https://*.example.com:443"]
#test_guard renderSources (sourceOf "CDN.Example" (some .https)) == #["https://cdn.example"]
#test_guard renderSources (sourceOf "bad;host") == #[]
#test_guard renderSources (sourceOf "cdn.example" (port := some 1)) == #["cdn.example:1"]
#test_guard renderSources (sourceOf "cdn.example" (port := some 65535)) == #["cdn.example:65535"]
#test_guard renderSources (sourceOf "cdn.example" (port := some 0)) == #[]

/- Origins and extra sources -/

#test_guard policyOf (page #[srcScript "/static/a.js", srcScript "b.js", srcScript "../c.js"] #[]) ==
  basePolicy

#test_guard policyOf (page #[srcScript "data:text/javascript,1", srcScript "blob:x"] #[]) ==
  basePolicy

#test_guard policyOf (page
    #[srcScript "https://b.example/x.js", srcScript "HTTPS://A.Example:8443/y.js?q#f"]
    #[srcScript "https://b.example/z.js", srcScript "http://c.example", script (.raw "s")]) ==
  s!"script-src 'self' https://b.example https://a.example:8443 http://c.example {scriptHash "s"}; base-uri 'self'"

#test_guard policyOf (page #[srcScript "https://a.example:0443/x.js"] #[]) ==
  "script-src 'self' https://a.example:443; base-uri 'self'"
#test_guard policyOf (page #[srcScript "https://a.example:1/x.js", srcScript "//b.example:65535/x.js",
    srcScript "http://c.example:00080"] #[]) ==
  "script-src 'self' https://a.example:1 b.example:65535 http://c.example:80; base-uri 'self'"
#test_guard #["https://a.example:0/x.js", "https://a.example:00000/x.js", "https://a.example:65536/x.js",
    "//a.example:0/x.js", "//a.example:65536/x.js", "https://a.example:-1/x.js"].all fun src =>
  policyOf (page #[srcScript src] #[]) == basePolicy

def extraSources : Array Source :=
  sourceOf "b.example" (some .https) ++ sourceOf "d.example" (some .https) ++
  sourceOf "d.example" (some .https) ++ sourceOf "cdn.example" ++
  sourceOf "cdn.example" (onlySubdomains := true) (port := some 443) ++
  sourceOf "E.example" (some .https)

#test_guard extraSources.size == 6

#test_guard policyOf (config := { extraScriptSources := extraSources })
    (page #[srcScript "https://b.example/x.js", script (.raw "s")] #[script (.raw "s")]) ==
  s!"script-src 'self' https://b.example https://d.example cdn.example *.cdn.example:443 https://e.example {scriptHash "s"}; base-uri 'self'"

#test_guard renderSources (collect { extraScriptSources := sourceOf "x.example" (some .https) }
    (page #[] #[])).extraSources == #["https://x.example"]

def duplicatedPolicy : Policy where
  origins := sourceOf "a.example" (some .https)
  extraSources := sourceOf "a.example" (some .https) ++ sourceOf "a.example"
  hashes := #["'sha256-x'", "'sha256-x'"]

#test_guard duplicatedPolicy.render ==
  "script-src 'self' https://a.example a.example 'sha256-x'; base-uri 'self'"

/- Keyword flags -/

#test_guard policyOf (config := { allowEval := true }) (page #[] #[]) ==
  "script-src 'self' 'unsafe-eval'; base-uri 'self'"
#test_guard policyOf (config := { allowWebAssemblyCompilation := true }) (page #[] #[]) ==
  "script-src 'self' 'wasm-unsafe-eval'; base-uri 'self'"
#test_guard policyOf
    (config := { allowWebAssemblyCompilation := true, allowEval := true,
                 extraScriptSources := sourceOf "cdn.example" })
    (page #[srcScript "https://a.example/x.js", script (.raw "s")] #[]) ==
  s!"script-src 'self' 'unsafe-eval' 'wasm-unsafe-eval' https://a.example cdn.example {scriptHash "s"}; base-uri 'self'"

/- Protocol-relative script URLs -/

#test_guard policyOf (page #[srcScript "//cdn.example/x.js"] #[]) ==
  "script-src 'self' cdn.example; base-uri 'self'"
#test_guard policyOf (page #[srcScript "//CDN.example:8443/x.js", srcScript "//cdn.example:8443"] #[]) ==
  "script-src 'self' cdn.example:8443; base-uri 'self'"
#test_guard policyOf (page #[srcScript "//cdn.example/x.js", srcScript "https://cdn.example/y.js"] #[]) ==
  "script-src 'self' cdn.example https://cdn.example; base-uri 'self'"

def maliciousProtocolRelative : Array String := #[
  "//evil.example;script-src */x.js",
  "//evil.example' 'unsafe-inline",
  "//evil.example 'unsafe-inline'",
  "//a..example/x.js",
  "//*.example/x.js",
  "//user@a.example/x.js",
  "//a.example:99999/x.js",
  "//",
  "///x.js",
  "\\\\evil.example/x.js",
  "//a.example/x\\y.js",
  "/\\evil.example/x.js"
]

#test_guard maliciousProtocolRelative.all fun src =>
  policyOf (page #[srcScript src] #[]) == basePolicy

/- Values from the page never reach the policy unvalidated -/

def maliciousSources : Array String := #[
  "https://evil.example;script-src *",
  "https://evil.example; script-src *",
  "https://a.example' 'unsafe-inline",
  "https://a.example 'unsafe-inline'",
  "https://a.example/x.js 'unsafe-inline'",
  "https://a.example,https://b.example",
  " https://a.example/x.js",
  "https://a.example\n/x.js",
  "https://a.example:80x/x.js",
  "https://a.example:/x.js",
  "https://a.example:99999/x.js",
  "https://a.example:1:2/x.js",
  "https://user@a.example/x.js",
  "https://a.example@evil.example/x.js",
  "https://[::1]/x.js",
  "https://a_b.example/x.js",
  "https://a..example/x.js",
  "https://.a.example/x.js",
  "https:a.example/x.js",
  "https:/a.example/x.js",
  "https:\\\\a.example\\x.js",
  "https://*/x.js",
  "https://*.a.example/x.js",
  "https:///x.js"
]

#test_guard maliciousSources.all fun src =>
  policyOf (page #[srcScript src] #[]) == basePolicy

-- The characters with the Unicode White_Space property.
def unicodeWhitespace : Array Char := #[
  '\t', '\n', '\x0b', '\x0c', '\r', ' ', '\u0085', '\xa0', '\u1680',
  '\u2000', '\u2001', '\u2002', '\u2003', '\u2004', '\u2005', '\u2006', '\u2007', '\u2008',
  '\u2009', '\u200A', '\u2028', '\u2029', '\u202F', '\u205F', '\u3000'
]

def whitespaceSources : Array String :=
  unicodeWhitespace.foldl (init := #[]) fun acc c =>
    acc ++ #[s!"https://a.example/{c}x.js", s!"https://a.example{c}/x.js", s!"//a.example/{c}x.js",
      s!"http://a.example/x.js{c}"]

#test_guard whitespaceSources.size == 4 * 25

#test_guard whitespaceSources.all fun src =>
  policyOf (page #[srcScript src] #[]) == basePolicy

#test_guard policyOf (page #[srcScript "https://a.example/\u200Bx.js"] #[]) ==
  "script-src 'self' https://a.example; base-uri 'self'"

#test_guard #["javascript:alert(1)", "data:text/javascript,1", "blob:x", "/static/a.js", "a.js",
    "ftp://a.example/x.js"].all fun src =>
  policyOf (page #[srcScript src] #[]) == basePolicy

/- Insertion into `head` -/

def metaOf (h : Html) (config : Config := {}) : Html :=
  html%{<meta http-equiv="Content-Security-Policy" content={policyOf h config}/>}

def charset : Html := html%{<meta charset="utf-8"/>}

def headed : Html :=
  page
    #[html%{<base href="../"/>},
      script (.raw "first"),
      srcScript "https://cdn.example/lib.js"]
    #[script (.raw "last")]

#test_guard apply {} headed ==
  page
    #[metaOf headed,
      html%{<base href="../"/>},
      script (.raw "first"),
      srcScript "https://cdn.example/lib.js"]
    #[script (.raw "last")]

#test_guard (apply {} (page #[] #[])).render == (page #[metaOf (page #[] #[])] #[]).render

#test_guard (apply {} (.seq #[.raw "<!DOCTYPE html>",
    html%{<html><head>{.raw "<title>t</title>"}</head><body></body></html>}])).render ==
  "<!DOCTYPE html><html><head><meta http-equiv=\"Content-Security-Policy\" content=\"script-src 'self'; base-uri 'self'\"/><title>t</title></head><body></body></html>"

def placed (head : Array Html) : String :=
  (apply {} (page head #[])).render

def policyMeta : String :=
  "<meta http-equiv=\"Content-Security-Policy\" content=\"script-src 'self'; base-uri 'self'\"/>"

#test_guard placed #[charset, html%{<base href="/"/>}] ==
  s!"<html><head><meta charset=\"utf-8\"/>{policyMeta}<base href=\"/\"/></head><body></body></html>"

#test_guard placed #[charset] ==
  s!"<html><head><meta charset=\"utf-8\"/>{policyMeta}</head><body></body></html>"

#test_guard placed #[.text "\n  ", .seq #[.text "\x0c\t\r "], charset, .text "\n"] ==
  s!"<html><head>\n  \x0c\t\r <meta charset=\"utf-8\"/>{policyMeta}\n</head><body></body></html>"

#test_guard placed #[.raw "<!-- generated -->", charset] ==
  s!"<html><head>{policyMeta}<!-- generated --><meta charset=\"utf-8\"/></head><body></body></html>"

#test_guard placed #[.raw " ", charset] ==
  s!"<html><head>{policyMeta} <meta charset=\"utf-8\"/></head><body></body></html>"

#test_guard placed #[.seq #[.seq #[charset], html%{<title>t</title>}]] ==
  s!"<html><head><meta charset=\"utf-8\"/>{policyMeta}<title>t</title></head><body></body></html>"

#test_guard placed #[html%{<META CharSet="utf-8"/>}] ==
  s!"<html><head><META CharSet=\"utf-8\"/>{policyMeta}</head><body></body></html>"

#test_guard placed #[html%{<base href="/"/>}, charset] ==
  s!"<html><head>{policyMeta}<base href=\"/\"/><meta charset=\"utf-8\"/></head><body></body></html>"

#test_guard placed #[html%{<meta name="viewport" content="width=device-width"/>}, charset] ==
  s!"<html><head>{policyMeta}<meta name=\"viewport\" content=\"width=device-width\"/><meta charset=\"utf-8\"/></head><body></body></html>"

#test_guard placed #[.text "x", charset] ==
  s!"<html><head>{policyMeta}x<meta charset=\"utf-8\"/></head><body></body></html>"

#test_guard placed #[.raw "<title>t</title>", charset] ==
  s!"<html><head>{policyMeta}<title>t</title><meta charset=\"utf-8\"/></head><body></body></html>"

def noHead : Html := html%{<html><body>{script (.raw "x")}</body></html>}

#test_guard apply {} noHead == noHead
#test_guard apply {} html%{<html><body><script><head></head></script></body></html>} ==
  html%{<html><body><script><head></head></script></body></html>}

def headInScript : Html := html%{<html><script><head></head></script><head></head><body></body></html>}

#test_guard (apply {} headInScript).render ==
  s!"<html><script><head></head></script><head>{(metaOf headInScript).render}</head><body></body></html>"

#test_guard (apply {} (.seq #[.raw "<!DOCTYPE html>", html%{<HEAD></HEAD>}])).render ==
  s!"<!DOCTYPE html><HEAD>{policyMeta}</HEAD>"

/- Extra sources and origins -/

#test_guard renderSources (collect { extraScriptSources := sourceOf "a.example" (some .https) }
    (page #[srcScript "https://a.example/x.js"] #[])).extraSources == #[]
#test_guard renderSources (collect { extraScriptSources := sourceOf "a.example" (some .https) }
    (page #[srcScript "https://a.example/x.js"] #[])).origins == #["https://a.example"]

/- Disabled configuration -/

def troublesome : Html :=
  page #[] #[.raw "<script>x</script>", html%{<a onclick="f()" href="javascript:f()"></a>}]

#test_guard apply { enabled := false } headed == headed
#test_guard apply { enabled := false } troublesome == troublesome
#test_guard apply { enabled := false, allowEval := true, extraScriptSources := sourceOf "a.example" } headed ==
  headed

/- A complete page, as the rehash helper must reproduce it -/

def samplePage : Html := html%{
  <html lang="en">
    <head>
      <meta charset="utf-8"/>
      <base href="/"/>
      <script src="https://cdn.example/lib.js"></script>
      <script>{.raw "window.inHead = 1;"}</script>
    </head>
    <body>
      <p>Hello</p>
      <script>{.raw "window.inBody = 2;"}</script>
    </body>
  </html>
}

def sampleConfig : Config := { extraScriptSources := sourceOf "analytics.example" (some .https) }

#test_guard (apply sampleConfig samplePage).render ==
  s!"<html lang=\"en\"><head><meta charset=\"utf-8\"/><meta http-equiv=\"Content-Security-Policy\" content=\"script-src 'self' https://cdn.example https://analytics.example {scriptHash "window.inHead = 1;"} {scriptHash "window.inBody = 2;"}; base-uri 'self'\"/><base href=\"/\"/><script src=\"https://cdn.example/lib.js\"></script><script>window.inHead = 1;</script></head><body><p>Hello</p><script>window.inBody = 2;</script></body></html>"

#test_guard (apply sampleConfig samplePage).render ==
  "<html lang=\"en\"><head><meta charset=\"utf-8\"/><meta http-equiv=\"Content-Security-Policy\" content=\"script-src 'self' https://cdn.example https://analytics.example 'sha256-zagrBsqmUpNTNqf2zXEe6chvc+8vg1v2GKWMvG30r34=' 'sha256-Whc1+XOKQqbV1dL/y8vYlrbk7cdgZzIo/FIVuZ0RExY='; base-uri 'self'\"/><base href=\"/\"/><script src=\"https://cdn.example/lib.js\"></script><script>window.inHead = 1;</script></head><body><p>Hello</p><script>window.inBody = 2;</script></body></html>"
