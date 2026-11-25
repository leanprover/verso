/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Html
public import Lean.Data.Json.FromToJson
import VersoUtil.Base64
import VersoUtil.Hash

namespace Verso.Output.Html.ContentSecurityPolicy

open Lean (Html Json ToJson FromJson)

/-- A URL scheme, either HTTP or HTTPS. -/
public inductive Scheme where
  /-- Unencrypted HTTP. -/
  | http
  /-- Encrypted HTTPS. -/
  | https
deriving Repr, DecidableEq, Hashable, Inhabited, ToJson, FromJson

/-- Converts a scheme to a string. -/
public def Scheme.render : Scheme → String
  | .http => "http"
  | .https => "https"

/--
A validated host name. Use `Host.ofString` to construct one.
-/
public structure Host where
  -- The constructor is private so that every host passes `Host.ofString`.
  private mk ::
  /-- The validated host name. -/
  name : String
deriving Repr, DecidableEq, Hashable

def isHostLabelChar (c : Char) : Bool :=
  c.isAlphanum || c == '-'

/-- Validates a string as a potential hostname. -/
public def Host.ofString (text : String) : Except String Host := do
  if text.isEmpty then
    throw "The host is empty."
  if let some c := (text.find? (fun c => !isHostLabelChar c && c != '.')).bind (·.get?) then
    throw s!"The host {text.quote} contains {c.quote}. \
      A host may contain only ASCII letters, digits, '-', and '.'."
  if text.startsWith '.' || text.endsWith '.' || text.contains ".." then
    throw s!"The host {text.quote} starts or ends with '.' or contains '..'."
  return ⟨text.toLower⟩

public instance : ToJson Host where
  toJson host := host.name

public instance : FromJson Host where
  fromJson? json := do Host.ofString (← json.getStr?)

/-- A port. -/
public structure Port where
  /-- The port number. -/
  number : UInt16
  /-- `0` is not a valid port number. -/
  nonzero : number ≠ 0
deriving Repr, DecidableEq, Hashable

/-- Validates and converts a port number. -/
public def Port.ofInt (port : Int) : Except String Port :=
  if h : 1 ≤ port ∧ port ≤ 65535 then .ok ⟨port.toNat.toUInt16, by grind⟩
  else .error s!"The port {port} is outside the range from 1 to 65535."

public instance : ToJson Port where
  toJson port := port.number.toNat

public instance : FromJson Port where
  fromJson? json := do Port.ofInt (← json.getInt?)

/--
A source expression, which may occur in a source list, in a content security policy.
-/
public structure Source where
  /--
  The URL scheme (e.g. `https`). If it is omitted, the source matches the page's own scheme.
  -/
  scheme : Option Scheme := none
  /-- The host name (e.g. `example.com`). -/
  host : Host
  /--
  Whether the source matches only the subdomains of `host`, such as `test.example.com` for
  `example.com`.

  A source with this flag doesn't match `host` itself. Allowing both takes two sources.
  -/
  onlySubdomains : Bool := false
  /-- A port number. If it is omitted, the source matches the scheme's default port. -/
  port : Option Port := none
deriving Repr, DecidableEq, Hashable, ToJson, FromJson

/--
Renders a specification of a source expression into a form suitable for use in a content security
policy.
-/
public def Source.render (source : Source) : String :=
  let scheme := source.scheme.map (·.render ++ "://") |>.getD ""
  let subdomains := if source.onlySubdomains then "*." else ""
  let port := source.port.map (s!":{·.number}") |>.getD ""
  scheme ++ subdomains ++ source.host.name ++ port

/--
A specification of a content security policy that can be translated into an appropriate `<meta>` tag.
-/
public structure Config where
  /-- Whether to generate the `<meta>` tag. -/
  enabled : Bool := true
  /--
  Whether JavaScript code should be able to call `eval`.

  Code that can call `eval` can also compile WebAssembly, so the `allowWebAssemblyCompilation` field
  is irrelevant if `allowEval` is `true`.
  -/
  allowEval : Bool := false
  /--
  Whether scripts in the page may compile WebAssembly code.
  -/
  allowWebAssemblyCompilation : Bool := false
  /--
  Additional sources from which scripts may be executed. Use this for scripts loaded from remote
  hosts if Verso does not automatically detect them.
  -/
  extraScriptSources : Array Source := #[]
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- A content security policy that can be added to `<head>`. -/
public structure Policy where
  /--
  Whether JavaScript code should be able to call `eval`.

  Code that can call `eval` can also compile WebAssembly, so the `allowWebAssemblyCompilation` field
  is irrelevant if `allowEval` is `true`.
  -/
  allowEval : Bool := false
  /--
  Whether scripts in the page may compile WebAssembly code.
  -/
  allowWebAssemblyCompilation : Bool := false
  /-- Allowed origins for scripts, as collected from the HTML. -/
  origins : Std.HashSet Source := {}
  /-- Further allowed origins for scripts, provided by the author. -/
  extraSources : Std.HashSet Source := {}
  /-- The inline script source texts to allow by hashes in the final policy value. -/
  inlineScripts : Std.HashSet String := {}
deriving Repr, BEq, Inhabited

/--
Normalizes the body of a script using the same algorithm as browsers:
1. CRLF line breaks become LF
2. Null characters become {lean}`'\uFFFD'`
-/
public def normalizeScriptBody (body : String) : String := Id.run do
  let mut out := ""
  let mut afterCr := false
  for c in body do
    if afterCr && c == '\n' then
      afterCr := false
      continue
    afterCr := c == '\r'
    out := out.push <|
      if c == '\r' then '\n'
      else if c == '\x00' then '\uFFFD'
      else c
  return out

public def scriptHash (body : String) : String :=
  s!"'sha256-{normalizeScriptBody body |>.toUTF8 |> Hash.sha256 |> Base64.encode}'"

/-- Converts a policy to a string that's suitable for a `<meta>` tag. -/
public def Policy.render (policy : Policy) : String :=
  let keywords :=
    (if policy.allowEval then #["'unsafe-eval'"] else #[]) ++
    (if policy.allowWebAssemblyCompilation then #["'wasm-unsafe-eval'"] else #[])
  let sorted (items : Std.HashSet String) := items.toArray.qsort (· < ·)
  let hosts := (policy.origins ∪ policy.extraSources).fold (·.insert ·.render) {}
  let hashes := policy.inlineScripts.fold (·.insert <| scriptHash ·) {}
  let sources := #["'self'"] ++ keywords ++ sorted hosts ++ sorted hashes
  sources.foldl (fun policy source => policy ++ " " ++ source) "script-src" ++ "; base-uri 'self'"

def isAsciiWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'

def isDecimal (s : String.Slice) : Bool :=
  !s.isEmpty && s.all Char.isDigit

/--
Checks whether the URL parser changes or rejects a host name.

The parser reads a host as an IPv4 address when its last label is a decimal or hexadecimal number
(https://url.spec.whatwg.org/#ends-in-a-number-checker). It writes a valid address as four decimal
numbers from 0 to 255 without leading zeros (https://url.spec.whatwg.org/#concept-ipv4-serializer).
-/
def isRewrittenIpv4 (host : Host) : Bool :=
  let labels := (host.name.split '.').toArray
  let last := labels.back?.getD "".toSlice
  let endsInNumber := isDecimal last || (last.dropPrefix? "0x").any (·.all Char.isHexDigit)
  let isCanonical (label : String.Slice) : Bool :=
    isDecimal label && label.toNat?.all (· ≤ 255) &&
      (label.utf8ByteSize == 1 || !label.startsWith '0')
  endsInNumber && !(labels.size == 4 && labels.all isCanonical)

/-- Parses `host[:port]` from a URL without a wildcard. -/
def authoritySource? (scheme : Option Scheme) (authority : String.Slice) : Option Source := do
  let host ← (Host.ofString (authority.takeWhile (· != ':')).copy).toOption
  if isRewrittenIpv4 host then none
  let afterHost := authority.dropWhile (· != ':')
  let port ←
    if afterHost.isEmpty then pure none
    else
      let digits := afterHost.drop 1
      if digits.isEmpty || !digits.all Char.isDigit then none
      else some <$> (Port.ofInt (digits.toNat?.getD 0)).toOption
  return { scheme, host, port }

def authorityOf (rest : String.Slice) : String.Slice :=
  rest.takeWhile fun c => c != '/' && c != '?' && c != '#'

/-- Splits `scheme://rest` for the `http` and `https` schemes. -/
def splitHttpUrl? (url : String) : Option (Scheme × String.Slice) :=
  let lower := url.toLower
  if lower.startsWith "https://" then some (.https, url.drop 8)
  else if lower.startsWith "http://" then some (.http, url.drop 7)
  else none

/-- The characters with the Unicode `White_Space` property. -/
def isUnicodeWhitespace (c : Char) : Bool :=
  (c.toNat ≥ 0x09 && c.toNat ≤ 0x0D) || c == ' ' || c == '\u0085' || c == '\u00A0' ||
  c == '\u1680' || (c.toNat ≥ 0x2000 && c.toNat ≤ 0x200A) || c == '\u2028' || c == '\u2029' ||
  c == '\u202F' || c == '\u205F' || c == '\u3000'

/-- Characters that could end a source or start a new one in the rendered policy. -/
def hasForbiddenChar (s : String) : Bool :=
  s.any fun c => c.toNat ≤ 0x20 || isUnicodeWhitespace c || c == ';' || c == ',' || c == '\''

/--
The origin that a script `src` loads from, for absolute `http(s)` and protocol-relative URLs.

A protocol-relative URL such as `//cdn.example/x.js` results in a host source without a scheme.
Browsers treat `\` like `/` in these URLs, so a protocol-relative URL with a `\` doesn't result in a
source.
-/
def scriptOrigin? (src : String) : Option Source :=
  if hasForbiddenChar src then none
  else match splitHttpUrl? src with
    | some (scheme, rest) => authoritySource? (some scheme) (authorityOf rest)
    | none =>
      if src.startsWith "//" && !src.contains '\\' then
        authoritySource? none (authorityOf (src.drop 2))
      else none

def attribute? (attrs : Array (String × String)) (name : String) : Option String :=
  attrs.find? (·.1.toLower == name) |>.map (·.2)

/--
Checks whether the HTML parser reads the children of an SVG or MathML element as HTML.

These elements are the HTML integration points and the MathML text integration points
(https://html.spec.whatwg.org/multipage/parsing.html#tree-construction-dispatcher).
-/
def isHtmlIntegrationPoint (tag : String) : Bool :=
  #["foreignobject", "desc", "title", "mi", "mo", "mn", "ms", "mtext", "annotation-xml"].contains
    tag

/--
The text of a script element in SVG or MathML, as the browser builds it.

In SVG and MathML, the HTML parser decodes character references in a script and turns markup into
child elements, which are not part of the script's text. A text node contributes the string that it
holds. A raw node contributes its string as written, which is the browser's text whenever it
contains neither `&` nor `<`.
-/
def foreignScriptText : Html → String
  | .text s | .raw s => s
  | .seq hs => hs.attach.foldl (fun text ⟨h, _⟩ => text ++ foreignScriptText h) ""
  | .element .. => ""

structure Scripts where
  origins : Std.HashSet Source := {}
  inlineScripts : Std.HashSet String := {}

/--
Collects the scripts in an HTML tree. `foreign` is `true` inside SVG and MathML, where the browser
parses script bodies as text with character references.
-/
def Scripts.visit (scripts : Scripts) (foreign : Bool) : Html → Scripts
  | .seq hs => hs.foldl (init := scripts) (fun s h => s.visit foreign h)
  | .element tag attrs children =>
    let tag := tag.toLower
    if tag == "script" then
      match attribute? attrs "src" with
      | some src =>
        match scriptOrigin? src with
        | some origin => { scripts with origins := scripts.origins.insert origin }
        | none => scripts
      | none =>
        let body := if foreign then foreignScriptText children else children.render
        { scripts with inlineScripts := scripts.inlineScripts.insert body }
    else
      let foreign :=
        if foreign then !isHtmlIntegrationPoint tag else tag == "svg" || tag == "math"
      scripts.visit foreign children
  | _ => scripts

/--
Converts a configuration to a suitable policy for `html` by collecting the document's inline scripts
and setting other properties as specified.
-/
public def collect (config : Config) (html : Html) : Policy :=
  let scripts := Scripts.visit {} false html
  let extras := config.extraScriptSources.foldl (init := {}) fun extras source =>
    if source ∈ scripts.origins then extras else extras.insert source
  {
    allowEval := config.allowEval
    allowWebAssemblyCompilation := config.allowWebAssemblyCompilation
    origins := scripts.origins
    extraSources := extras
    inlineScripts := scripts.inlineScripts
  }

def flatten : Html → Array Html
  | .seq hs => hs.attach.foldl (fun nodes ⟨h, _⟩ => nodes ++ flatten h) #[]
  | h => #[h]

def isCharsetMeta : Html → Bool
  | .element tag attrs _ => tag.toLower == "meta" && attrs.any (·.1.toLower == "charset")
  | _ => false

def isWhitespaceText : Html → Bool
  | .text t => t.all isAsciiWhitespace
  | _ => false

-- The policy follows a leading `<meta charset>` so that the charset stays within the first
-- 1024 bytes of the page, where browsers look for it.
def addToHead (policyElement : Html) (children : Html) : Html :=
  let nodes := flatten children
  match nodes.findIdx? (!isWhitespaceText ·) with
  | some i =>
    if isCharsetMeta nodes[i]! then
      .seq (nodes.extract 0 (i + 1) ++ #[policyElement] ++ nodes.extract (i + 1))
    else policyElement ++ children
  | none => policyElement ++ children

-- Adds the policy to the first `head` element in document order outside scripts.
def insertIntoHead (policyElement : Html) : Html → Option Html
  | .element tag attrs children =>
    let lower := tag.toLower
    if lower == "head" then some (.element tag attrs (addToHead policyElement children))
    else if lower == "script" then none
    else (insertIntoHead policyElement children).map (.element tag attrs ·)
  | .seq hs =>
    let (inserted, hs) := hs.foldl (init := (false, #[])) fun (inserted, nodes) h =>
      if inserted then (true, nodes.push h)
      else match insertIntoHead policyElement h with
        | some h => (true, nodes.push h)
        | none => (false, nodes.push h)
    if inserted then some (.seq hs) else none
  | _ => none

/--
Applies a policy configuration to an HTML document by inserting the appropriate `<meta>` element in the head.
-/
public def apply (config : Config) (html : Html) : Html :=
  if !config.enabled then html
  else
    let policyElement :=
      html%{<meta http-equiv="Content-Security-Policy" content={(collect config html).render}/>}
    (insertIntoHead policyElement html).getD html
