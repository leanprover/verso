/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

import Errata
import Lean.Data.Json
import all Verso.Output.Html.ContentSecurityPolicy

namespace Verso.Tests.ContentSecurityPolicyUrls

open Lean (Json)
open Errata
open Verso.Output.Html.ContentSecurityPolicy

/--
URL parser test cases from web-platform-tests (https://github.com/web-platform-tests/wpt). The file
`src/tests/data/wpt-url/README.md` describes the specific subset that's used for testing here.
-/
def corpus : String := include_str "../data/wpt-url/urltestdata.json"

/-- A test case: the input, its base URL, and the parsed URL, which is `none` for a failure. -/
structure Case where
  input : String
  base : Option String
  /-- The expected protocol (such as `https:`), host name, and port of the parsed URL. -/
  parsed : Option (String × String × String)

def Case.fromJson? (json : Json) : Except String Case := do
  let input ← json.getObjValAs? String "input"
  let base := (json.getObjValAs? String "base").toOption
  if (json.getObjValAs? Bool "failure").toOption == some true then
    return { input, base, parsed := none }
  let protocol ← json.getObjValAs? String "protocol"
  let hostname ← json.getObjValAs? String "hostname"
  let port ← json.getObjValAs? String "port"
  return { input, base, parsed := some (protocol, hostname, port) }

def isHttpProtocol (protocol : String) : Bool :=
  protocol == "http:" || protocol == "https:"

def defaultPort (protocol : String) : String :=
  if protocol == "https:" then "443" else "80"

/--
Checks a source against the expected parse of a case. A source without a scheme is judged only when
the case's base URL is HTTP or HTTPS, which makes it resolve like it does on a page.
-/
def Case.check (case : Case) (source : Source) : Option String := do
  if source.scheme.isNone then
    let base := (case.base.getD "").toLower
    unless base.startsWith "http:" || base.startsWith "https:" do none
  let (protocol, hostname, port) ← match case.parsed with
    | none => return "the URL parser rejects the input"
    | some parsed => pure parsed
  unless isHttpProtocol protocol do return s!"the protocol is {protocol}"
  if let some scheme := source.scheme then
    unless protocol == scheme.render ++ ":" do return s!"the protocol is {protocol}"
  unless hostname == source.host.name do return s!"the host name is {hostname}"
  let sourcePort := source.port.map (toString ·.number) |>.getD ""
  unless port == sourcePort || (port.isEmpty && sourcePort == defaultPort protocol) do
    return s!"the port is {port.quote}"
  none

def cases : Except String (Array Case) := do
  let json ← Json.parse corpus
  let entries ← json.getArr?
  entries.mapM Case.fromJson?

def isSchemeChar (c : Char) : Bool :=
  c.isAlphanum || c == '+' || c == '-' || c == '.'

-- An input that starts with a scheme or with two slashes or backslashes doesn't resolve to the
-- page's own origin.
def namesOrigin (input : String) : Bool :=
  let isSlash (c : Char) : Bool := c == '/' || c == '\\'
  match input.dropPrefix? isSlash with
  | some rest => rest.startsWith isSlash
  | none =>
    !(input.takeWhile isSchemeChar).isEmpty && (input.dropWhile isSchemeChar).startsWith ':'

/--
Every source that `scriptOrigin?` finds in a test case agrees with the URL parser, and its rendered
form doesn't contain a character that ends a source in the policy.
-/
@[test]
def matchesWPTCorpus : Test := do
  let cases ← match cases with
    | .ok cases => pure cases
    | .error e => failHere s!"could not read the test cases: {e}"
  assertTrue (cases.size > 800) "the test cases are missing"
  let mut problems := #[]
  let mut found := 0
  let mut missed := #[]
  for case in cases do
    match scriptOrigin? case.input with
    | some source =>
      found := found + 1
      if source.render.any (fun c => c.toNat ≤ 0x20 || c == ';' || c == ',' || c == '\'') then
        problems := problems.push
          s!"{case.input.quote}: {source.render.quote} has a forbidden character"
      if let some problem := case.check source then
        problems := problems.push s!"{case.input.quote} gives {source.render.quote}, but {problem}"
    | none =>
      if let some (protocol, _, _) := case.parsed then
        if isHttpProtocol protocol && namesOrigin case.input then
          missed := missed.push case.input
  IO.println s!"{cases.size} cases, {found} sources found"
  IO.println s!"{missed.size} HTTP or HTTPS URLs with an origin that `scriptOrigin?` doesn't find:"
  for input in missed do
    IO.println s!"  {input.quote}"
  unless problems.isEmpty do
    failHere s!"{problems.size} sources disagree with the URL parser"
      (detail? := some (problems.foldl (· ++ ·.push '\n') ""))
