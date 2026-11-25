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
  | http
  | https
deriving Repr, DecidableEq, Hashable, Inhabited, ToJson, FromJson

/-- Converts a scheme to a string. -/
public def Scheme.render : Scheme → String
  | .http => "http"
  | .https => "https"

public structure Host where
  -- The constructor is private so that every host passes `Host.ofString`.
  private mk ::
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

public structure Port where
  number : UInt16
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
  scheme : Option Scheme := none
  host : Host
  includeSubdomains : Bool := false
  port : Option Port := none
deriving Repr, DecidableEq, Hashable, ToJson, FromJson

public def Source.render (source : Source) : String :=
  let scheme := source.scheme.map (·.render ++ "://") |>.getD ""
  let subdomains := if source.includeSubdomains then "*." else ""
  let port := source.port.map (s!":{·.number}") |>.getD ""
  scheme ++ subdomains ++ source.host.name ++ port

public structure Config where
  enabled : Bool := true
  allowEval : Bool := false
  allowWebAssemblyCompilation : Bool := false
  extraScriptSources : Array Source := #[]
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- A content security policy that can be added to `<head>`. -/
public structure Policy where
  allowEval : Bool := false
  allowWebAssemblyCompilation : Bool := false
  origins : Array Source := #[]
  extraSources : Array Source := #[]
  hashes : Array String := #[]
deriving Repr, BEq, Inhabited

def pushNew [BEq α] (xs : Array α) (x : α) : Array α :=
  if xs.contains x then xs else xs.push x

/-- Converts a policy to a string that's suitable for a `<meta>` tag. -/
public def Policy.render (policy : Policy) : String :=
  let keywords :=
    (if policy.allowEval then #["'unsafe-eval'"] else #[]) ++
    (if policy.allowWebAssemblyCompilation then #["'wasm-unsafe-eval'"] else #[])
  let sources :=
    ((policy.origins ++ policy.extraSources).map (·.render) ++ policy.hashes).foldl pushNew
      (#["'self'"] ++ keywords)
  sources.foldl (fun policy source => policy ++ " " ++ source) "script-src" ++ "; base-uri 'self'"

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

def isAsciiWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'

def isSchemeChar (c : Char) : Bool :=
  c.isAlphanum || c == '+' || c == '-' || c == '.'

-- Browsers strip leading C0 controls and spaces and remove tabs and newlines before they read
-- the scheme of a URL.
def urlSchemeText (url : String) : String :=
  (url.dropWhile (fun (c : Char) => c.toNat ≤ 0x20)).foldl (init := "") fun text c =>
    if c == '\t' || c == '\n' || c == '\r' then text else text.push c

def urlScheme? (url : String) : Option String :=
  let text := urlSchemeText url
  let scheme := text.takeWhile isSchemeChar
  match scheme.front? with
  | some c =>
    if c.isAlpha && (text.dropWhile isSchemeChar).startsWith ':' then some scheme.copy.toLower
    else none
  | none => none

/-- Parses `host[:port]` from a URL without a wildcard. -/
def authoritySource? (scheme : Option Scheme) (authority : String.Slice) : Option Source := do
  let host ← (Host.ofString (authority.takeWhile (· != ':')).copy).toOption
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
A protocol-relative URL such as `//cdn.example/x.js` results in a host source without a scheme.
Browsers treat `\` like `/` here.
-/
def protocolRelativeOrigin? (src : String) : Option Source :=
  if hasForbiddenChar src || src.contains '\\' || !src.startsWith "//" then none
  else authoritySource? none (authorityOf (src.drop 2))

def isProtocolRelative (src : String) : Bool :=
  let isSlash (c : Char) : Bool := c == '/' || c == '\\'
  match (urlSchemeText src).dropPrefix? isSlash with
  | some rest => rest.startsWith isSlash
  | none => false

/-- The origin that a script `src` loads from, for absolute `http(s)` and protocol-relative URLs. -/
def scriptOrigin? (src : String) : Option Source :=
  match urlScheme? src with
  | some "http" | some "https" =>
    if hasForbiddenChar src then none
    else match splitHttpUrl? src with
      | none => none
      | some (scheme, rest) => authoritySource? (some scheme) (authorityOf rest)
  | some _ => none
  | none => if isProtocolRelative src then protocolRelativeOrigin? src else none

def attribute? (attrs : Array (String × String)) (name : String) : Option String :=
  attrs.find? (·.1.toLower == name) |>.map (·.2)

structure Scripts where
  origins : Array Source := #[]
  hashes : Array String := #[]

def Scripts.visit (scripts : Scripts) : Html → Scripts
  | .seq hs => hs.foldl (init := scripts) (fun s h => s.visit h)
  | .element tag attrs children =>
    if tag.toLower == "script" then
      match attribute? attrs "src" with
      | some src =>
        match scriptOrigin? src with
        | some origin => { scripts with origins := pushNew scripts.origins origin }
        | none => scripts
      | none => { scripts with hashes := pushNew scripts.hashes (scriptHash children.render) }
    else scripts.visit children
  | _ => scripts

/--
Converts a configuration to a suitable policy for `html` by collecting the hashes of the document's
inline scripts and setting other properties as specified.
-/
public def collect (config : Config) (html : Html) : Policy :=
  let scripts := Scripts.visit {} html
  let extras := config.extraScriptSources.foldl (init := #[]) fun extras source =>
    if scripts.origins.contains source then extras else pushNew extras source
  {
    allowEval := config.allowEval
    allowWebAssemblyCompilation := config.allowWebAssemblyCompilation
    origins := scripts.origins
    extraSources := extras
    hashes := scripts.hashes
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
