/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Html
public import Lean.Data.Json.FromToJson
import Verso.Output.Html.Entities
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
  /-- Trusted inline script bodies to authorize explicitly, for example scripts in raw HTML. -/
  extraInlineScripts : Array String := #[]
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

/-- Parses the entire authority as `host[:port]`, without a wildcard. -/
def authoritySource? (scheme : Option Scheme) (authority : String.Slice) : Option Source := do
  let host ← (Host.ofString (authority.takeWhile (· != ':')).copy).toOption
  if isRewrittenIpv4 host then none
  let afterHost := authority.dropWhile (· != ':')
  let port ←
    if afterHost.isEmpty then pure none
    else
      let digits ← afterHost.dropPrefix? ':'
      let number ← digits.toNat?
      some <$> (Port.ofInt number).toOption
  return { scheme, host, port }

def authorityOf (rest : String.Slice) : String.Slice :=
  rest.takeWhile fun c => c != '/' && c != '?' && c != '#'

/-- Splits `scheme://rest` for the `http` and `https` schemes. -/
def splitHttpUrl? (url : String) : Option (Scheme × String.Slice) :=
  let lower := url.toLower
  if lower.startsWith "https://" then some (.https, url.drop 8)
  else if lower.startsWith "http://" then some (.http, url.drop 7)
  else none

/--
The origin that a script `src` loads from, for absolute `http(s)` and protocol-relative URLs.

A protocol-relative URL such as `//cdn.example/x.js` results in a host source without a scheme.
Browsers treat `\` like `/` in these URLs, so a protocol-relative URL with a `\` doesn't result in a
source.
-/
def scriptOrigin? (src : String) : Option Source :=
  -- HTML parsing replaces NUL with U+FFFD before URL parsing. Trim the remaining
  -- leading and trailing C0 controls and space, then remove tabs and newlines.
  let trim (c : Char) := c != '\x00' && c ≤ ' '
  let src := (src.dropWhile trim |>.dropEndWhile trim).copy
    |>.replace "\t" "" |>.replace "\n" "" |>.replace "\r" ""
  -- Only the validated authority is emitted. Path, query, and fragment punctuation
  -- cannot become part of the CSP source.
  match splitHttpUrl? src with
  | some (scheme, rest) => authoritySource? (some scheme) (authorityOf rest)
  | none =>
    if src.startsWith "//" && !src.contains '\\' then
      authoritySource? none (authorityOf (src.drop 2))
    else none

def attribute? (attrs : Array (String × String)) (name : String) : Option String :=
  attrs.find? (·.1.toLower == name) |>.map (·.2)

inductive ScriptNamespace where
  | html | svg | math
deriving BEq

-- The children of foreign integration points are parsed as HTML. An SVG child of MathML
-- annotation-xml also enters the SVG namespace regardless of the annotation's encoding.
def childNamespace (ns : ScriptNamespace) (tag : String) (attrs : Array (String × String)) :
    ScriptNamespace :=
  match ns with
  | .html =>
    if tag == "svg" then .svg else if tag == "math" then .math else .html
  | .svg =>
    if #["foreignobject", "desc", "title"].contains tag then .html else .svg
  | .math =>
    if #["mi", "mo", "mn", "ms", "mtext"].contains tag then .html
    else if tag == "annotation-xml" &&
        (attribute? attrs "encoding").any
          (fun value => #["text/html", "application/xhtml+xml"].contains value.toLower) then .html
    else .math

-- https://mimesniff.spec.whatwg.org/#javascript-mime-type
def isJavaScriptMimeType (type : String) : Bool :=
  #["application/ecmascript", "application/javascript", "application/x-ecmascript",
    "application/x-javascript", "text/ecmascript", "text/javascript", "text/javascript1.0",
    "text/javascript1.1", "text/javascript1.2", "text/javascript1.3", "text/javascript1.4",
    "text/javascript1.5", "text/jscript", "text/livescript", "text/x-ecmascript",
    "text/x-javascript"].contains type

def scriptType (attrs : Array (String × String)) : String :=
  match attribute? attrs "type" with
  | some type => type.toLower
  | none =>
    match attribute? attrs "language" with
    | some lang => if lang.isEmpty then "" else "text/" ++ lang.toLower
    | none => ""

-- HTML's legacy event restriction applies only to classic HTML scripts with both attributes.
def allowsLegacyEvent (attrs : Array (String × String)) : Bool :=
  let clean (s : String) := (s.dropWhile isAsciiWhitespace |>.dropEndWhile isAsciiWhitespace).copy.toLower
  match attribute? attrs "for", attribute? attrs "event" with
  | some target, some event => clean target == "window" && clean event ∈ #["onload", "onload()"]
  | _, _ => true

-- Descendants of these HTML elements are inert or are parsed as text.
def isInertContainer (tag : String) : Bool :=
  match tag with
  | "template" | "noscript" | "title" | "textarea" | "style" | "xmp" | "iframe"
  | "noembed" | "noframes" | "plaintext" => true
  | _ => false

structure Scripts where
  origins : Std.HashSet Source := {}
  inlineScripts : Std.HashSet String := {}

def flatten : Html → Array Html
  | .seq hs => hs.foldl (fun nodes h => nodes ++ flatten h) #[]
  | h => #[h]
termination_by h => h

-- The HTML tokenizer consumes the longest named reference in the table, including legacy
-- spellings without a semicolon. If nothing matches, the ampersand is literal.
def svgReference (rest : String.Slice) : Option (String × String.Slice) := do
  if let some number := rest.dropPrefix? '#' then
    let hex := number.startsWith 'x' || number.startsWith 'X'
    let digits := if hex then (number.drop 1).takeWhile Char.isHexDigit else number.takeWhile Char.isDigit
    if !digits.isEmpty then
      let ref := (if hex then "#x" else "#") ++ digits.copy
      let after := number.drop (digits.utf8ByteSize + (if hex then 1 else 0))
      return (← Html.characterReference? ref, after.dropPrefix ';')
  else
    -- The longest name in the HTML entity table has 31 letters.
    let name := (rest.take 31).takeWhile Char.isAlphanum
    let mut len := name.utf8ByteSize
    let after := rest.drop len
    if after.startsWith ';' then
      if let some value := Entities.entityStrings["&" ++ name.copy ++ ";"]? then
        return (value, after.drop 1)
    while len > 0 do
      if let some value := Entities.entityStrings["&" ++ (name.take len).copy]? then
        return (value, rest.drop len)
      len := len - 1
  return ("&", rest)

-- Decode the serialized text between child elements of an SVG script. In foreign content,
-- CDATA is literal and character references outside CDATA are decoded by the HTML tokenizer.
-- Decline markup we cannot interpret exactly, so we never authorize a guessed script body.
def decodeSvgText (source : String) : Option String := do
  let mut rest := (normalizeScriptBody source).toSlice
  let mut text := ""
  while let some pos := rest.find? (fun c => c == '<' || c == '&') do
    text := text ++ (rest.sliceTo pos).copy
    rest := rest.sliceFrom pos
    if let some data := rest.dropPrefix? "<![CDATA[" then
      let endPos ← data.find? "]]>"
      text := text ++ (data.sliceTo endPos).copy
      rest := (data.sliceFrom endPos).drop 3
    else if let some ref := rest.dropPrefix? '&' then
      let (decoded, after) ← svgReference ref
      text := text ++ decoded
      rest := after
    else
      rest := rest.drop 1
      guard (!(rest.startsWith Char.isAlpha || rest.startsWith '!' || rest.startsWith '/' || rest.startsWith '?'))
      text := text.push '<'
  return text ++ rest.copy

def foreignScriptText? (children : Html) : Option String := do
  let mut text := ""
  let mut run := ""
  -- Adjacent raw and text nodes share tokenizer state, even across nested sequences.
  for child in flatten children do
    match child with
    | .element .. =>
      text := text ++ (← decodeSvgText run)
      run := ""
    | _ => run := run ++ child.render
  return text ++ (← decodeSvgText run)

/--
The DOM Standard lists the built-in [valid shadow host names](https://dom.spec.whatwg.org/#valid-shadow-host-name)
and also permits [valid custom element names](https://html.spec.whatwg.org/multipage/custom-elements.html#valid-custom-element-name).
-/
def canHostShadowRoot (tag : String) : Bool :=
  #["article", "aside", "blockquote", "body", "div", "footer", "h1", "h2", "h3", "h4",
    "h5", "h6", "header", "main", "nav", "p", "section", "span"].contains tag ||
    (tag.contains '-' && tag.front.isLower &&
      !tag.any (fun c => isAsciiWhitespace c || c == '\x00' || c == '/' || c == '>') &&
      !(#["annotation-xml", "color-profile", "font-face", "font-face-src", "font-face-uri",
          "font-face-format", "font-face-name", "missing-glyph"].contains tag))

def shadowContents? : Html → Option Html
  | .element tag attrs children => do
    guard (tag.toLower == "template")
    let mode ← attribute? attrs "shadowrootmode"
    guard (#["open", "closed"].contains mode.toLower)
    return children
  | _ => none

/--
Collects browser-processed scripts in the structured HTML tree.
-/
partial def Scripts.visit (scripts : Scripts) (ns : ScriptNamespace) (inMathAnnotation := false) : Html → Except String Scripts
  | .seq hs => hs.foldlM (init := scripts) (fun s h => s.visit ns inMathAnnotation h)
  | .element tag attrs children =>
    let tag := tag.toLower
    if tag == "script" then
      if ns == .math then pure scripts else
      let foreign := ns == .svg
      let type := if foreign then (attribute? attrs "type").getD "" |>.toLower else scriptType attrs
      let mime := (type.dropWhile isAsciiWhitespace |>.dropEndWhile isAsciiWhitespace).copy
      let classic := type.isEmpty || isJavaScriptMimeType mime
      let canExecute := type == "module" || (classic && (foreign || allowsLegacyEvent attrs))
      let inlineOnly := !foreign && (type == "importmap" || type == "speculationrules")
      let src := if foreign then (attribute? attrs "href").orElse (fun _ => attribute? attrs "xlink:href")
        else attribute? attrs "src"
      match src with
      | some src =>
        if canExecute then
          match scriptOrigin? src with
          | some origin => pure { scripts with origins := scripts.origins.insert origin }
          | none => pure scripts
        else pure scripts
      | none =>
        if canExecute || inlineOnly then
          match (if foreign then foreignScriptText? children else some children.render) with
          | some body => pure { scripts with inlineScripts := scripts.inlineScripts.insert body }
          | none => throw "Cannot determine the text of an inline SVG script for the content security policy. Use Html.text for its JavaScript source, or wrap the raw source in a CDATA section."
        else pure scripts
    else if ns == .html && isInertContainer tag then pure scripts
    else
      let current := if inMathAnnotation && tag == "svg" then .svg else ns
      if current == .html && canHostShadowRoot tag then
        visitShadowHostChildren scripts children
      else
        scripts.visit (childNamespace current tag attrs) (current == .math && tag == "annotation-xml") children
  | _ => pure scripts
where
  visitShadowHostChildren (scripts : Scripts) (children : Html) : Except String Scripts := do
    let mut scripts := scripts
    let mut attached := false
    for child in flatten children do
      if !attached then
        if let some contents := shadowContents? child then
          attached := true
          scripts ← scripts.visit .html false contents
          continue
      scripts ← scripts.visit .html false child
    return scripts

/--
Collects the document's scripts and builds a policy using `config`. Returns an error if the
text of an inline SVG script cannot be determined.
-/
public def collect (config : Config) (html : Html) : Except String Policy := do
  let scripts ← Scripts.visit {} .html false html
  let extras := config.extraScriptSources.foldl (init := {}) fun extras source =>
    if source ∈ scripts.origins then extras else extras.insert source
  return {
    allowEval := config.allowEval
    allowWebAssemblyCompilation := config.allowWebAssemblyCompilation
    origins := scripts.origins
    extraSources := extras
    inlineScripts := config.extraInlineScripts.foldl (·.insert ·) scripts.inlineScripts
  }

def isCharsetMeta : Html → Bool
  | .element tag attrs children =>
    tag.toLower == "meta" && children.isEmpty &&
      -- Only passive metadata may precede the policy.
      attrs.all (fun (name, _) =>
        let name := name.toLower
        (name.all fun c => c.isAlphanum || c == '-' || c == '_') &&
          !name.startsWith "on" && name != "http-equiv" && name != "is") &&
      attrs.any (·.1.toLower == "charset")
  | _ => false

def isWhitespaceNode : Html → Bool
  | .text t | .raw t => t.all isAsciiWhitespace
  | _ => false

-- The HTML printer writes attribute names verbatim. On an opening tag before the
-- policy, each name must survive serialization as a single attribute name.
def hasValidAttributeNames (attrs : Array (String × String)) : Bool :=
  attrs.all fun (name, _) =>
    !name.isEmpty && name.all fun c =>
      c > ' ' && c != '\x7f' && !(c == '"' || c == '\'' || c == '>' || c == '<' || c == '/' || c == '=')

-- The policy follows a leading `<meta charset>` so that the charset stays within the first
-- 1024 bytes of the page, where browsers look for it.
def addToHead (policyElement : Html) (children : Html) : Html :=
  let nodes := flatten children
  match nodes.findFinIdx? (!isWhitespaceNode ·) with
  | some i =>
    if isCharsetMeta nodes[i] then
      .seq (nodes.extract 0 (i.val + 1) ++ #[policyElement] ++ nodes.extract (i.val + 1))
    else if let some j := nodes.findFinIdx? isPlainUtf8 then
      .seq (#[nodes[j], policyElement] ++ nodes.eraseIdx j)
    else policyElement ++ children
  | none => policyElement ++ children
where
  isPlainUtf8 : Html → Bool
    | .element tag #[(name, value)] body =>
      tag.toLower == "meta" && name.toLower == "charset" && value.toLower == "utf-8" && body.isEmpty
    | _ => false

/-- Checks that a serialized document prefix contains only whitespace or the HTML doctype. -/
public def isDocumentPreamble (text : String) : Bool :=
  let text := text.toSlice.dropWhile isAsciiWhitespace
  text.isEmpty ||
    (text.copy.toLower.dropPrefix? "<!doctype html>").any (·.all isAsciiWhitespace)

-- Identify the head before any element or text that could cause the parser to leave the head.
def insertIntoLeadingHead (policyElement : Html) (nodes : Array Html) : Option (Array Html) := do
  let index ← nodes.findFinIdx? (!isWhitespaceNode ·)
  let .element tag attrs children := nodes[index] | none
  if tag.toLower != "head" || !hasValidAttributeNames attrs then none
  else some (nodes.set index (.element tag attrs (addToHead policyElement children)))

-- Require a structured head at the start of the document or of its outer html element.
def insertIntoHead (policyElement : Html) (html : Html) : Option Html := do
  let nodes := flatten html
  let index ← nodes.findFinIdx? fun
    | .raw s => !isDocumentPreamble s
    | node => !isWhitespaceNode node
  let .element tag attrs children := nodes[index] | none
  let nodes ←
    if tag.toLower == "html" then
      guard (hasValidAttributeNames attrs)
      let children ← insertIntoLeadingHead policyElement (flatten children)
      pure (nodes.set index (.element tag attrs (.seq children)))
    else
      let head ← insertIntoLeadingHead policyElement (nodes.extract index)
      pure (nodes.extract 0 index ++ head)
  match html with
  | .element .. => nodes[0]?
  | _ => some (.seq nodes)

/--
Applies a policy configuration to an HTML document by inserting a policy in its leading `<head>`
When the policy is enabled, documents without such a head are rejected.
-/
public def apply (config : Config) (html : Html) : Except String Html :=
  if !config.enabled then .ok html
  else do
    let policy ← collect config html
    let policyElement :=
      html%{<meta http-equiv="Content-Security-Policy" content={policy.render}/>}
    match insertIntoHead policyElement html with
    | some html => .ok html
    | none => .error "Cannot install the content security policy: expected a leading structured <head> and valid attribute names on <html> and <head>."
