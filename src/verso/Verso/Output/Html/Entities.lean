/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
meta import Init.System.FilePath
public import Lean.Data.Json.Basic
import Lean.Data.Json

public import Std.Data.HashMap
public import Std.Data.HashSet

open Lean
open Std


namespace Verso.Output.Html.Entities

/-!
This is based on the following:
 * https://html.spec.whatwg.org/multipage/syntax.html#syntax-charref
 * https://html.spec.whatwg.org/multipage/named-characters.html#named-character-references
 * https://html.spec.whatwg.org/entities.json
-/

/-!
# Loading Data

The entity data is provided as a JSON file from the specification. This section loads and processes
it at compile time.
-/

-- Including as a string ensures that the path is correctly made relative to the current file
private def entityJsonFile := include_str "entities.json"

private initialize entityInfo : Json × HashMap String String × HashMap String (HashSet String) ← do
  let json ←
    match Json.parse entityJsonFile with
    | .error e => throw <| .userError s!"Error parsing HTML entity JSON: {e}"
    | .ok v => pure v
  let table ←
    match json.getObj? with
    | .error e => throw <| .userError s!"Error extracting JSON object for entities: {e}"
    | .ok v => pure v
  let decode ←
    table.foldlM (init := {}) fun soFar entity v =>
      match v.getObjValAs? String "characters" with
      | .error e => throw <| .userError s!"Failed to get characters for entity '{entity}': {e}"
      | .ok s => pure <| soFar.insert entity s

  let encode := decode.fold (init := {}) fun soFar entity v =>
    soFar.alter v fun entities? => entities?.getD {} |>.insert entity

  pure (json, decode, encode)

/-!
# Public API
-/

/--
The JSON HTML entity database, from [the specification](https://html.spec.whatwg.org/entities.json).
-/
public def json := entityInfo.1

/--
A table mapping HTML entity strings (such as `&amp;`) to the strings that they denote (such as `&`).
Most entities denote just one character, but some entities are represented by combining characters,
so the returned string may have a length greater than one.
-/
public def entityStrings := entityInfo.2.1

/--
A table mapping strings (such as `&`) to the named entities that denote them (such as `&amp;`).

Most entities denote just one character, but some entities are represented by combining characters.
Some strings are denoted by more than one named entity; for example, `&` can be represented by both
`&amp;` and `&AMP`. Not all named entities end in a semicolon.
-/
public def stringEntities := entityInfo.2.2

private def isHexDigit (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

private def decodeHex (s : String) : Option Nat := do
  if s.isEmpty then failure
  let mut n := 0
  let mut iter := s.startValidPos
  while h : iter ≠ s.endValidPos do
    let c := iter.get h
    iter := iter.next h

    if '0' ≤ c && c ≤ '9' then n := n <<< 4 + (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then n := n <<< 4 + (10 + c.toNat - 'a'.toNat)
    else if 'A' ≤ c && c ≤ 'F' then n := n <<< 4 + (10 + c.toNat - 'A'.toNat)
    else failure
  return n

end Entities

open Entities

/--
Decodes an HTML entity string, which may be a named entity (e.g. `ˆ&amp;`), a decimal entity (e.g.
`&#32;`), or a hexadecimal entity (e.g. `&#x20;`).
-/
public def decodeEntity? (entityString : String) : Option String := do
  if let some x := entityStrings[entityString]? then return x
  unless entityString.startsWith "&" do failure
  let entityString := entityString.stripPrefix "&"
  unless entityString.endsWith ";" do failure
  let entityString := entityString.stripSuffix ";"

  if entityString.startsWith "#" then -- numeric reference
    let entityString := entityString.stripPrefix "#"
    if entityString.startsWith "x" || entityString.startsWith "X" then
      let v ← entityString.drop 1 |> decodeHex
      refToChar v
    else if String.Pos.Raw.get? entityString 0 |>.map isHexDigit |>.getD false then
      let v ← entityString.toNat?
      refToChar v
    else failure
  else failure
where
  refToChar (n : Nat) : Option String := do
    if n == 0x0d then failure
    if nonCharacter n then failure
    if control n && !asciiWhitespace n then failure
    return .singleton <| Char.ofNat n

  /--
  Checks whether a character reference is a [noncharacter](https://infra.spec.whatwg.org/#noncharacter)
  -/
  nonCharacter (n : Nat) : Bool :=
    0xFDD0 ≤ n && n ≤ 0xFDEF ||
    n == 0xFFFE || n == 0xFFFF || n == 0x1FFFE || n == 0x1FFFF || n == 0x2FFFE || n == 0x2FFFF ||
    n == 0x3FFFE || n == 0x3FFFF || n == 0x4FFFE || n == 0x4FFFF || n == 0x5FFFE || n == 0x5FFFF ||
    n == 0x6FFFE || n == 0x6FFFF || n == 0x7FFFE || n == 0x7FFFF || n == 0x8FFFE || n == 0x8FFFF ||
    n == 0x9FFFE || n == 0x9FFFF || n == 0xAFFFE || n == 0xAFFFF || n == 0xBFFFE || n == 0xBFFFF ||
    n == 0xCFFFE || n == 0xCFFFF || n == 0xDFFFE || n == 0xDFFFF || n == 0xEFFFE || n == 0xEFFFF ||
    n == 0xFFFFE || n == 0xFFFFF || n == 0x10FFFE || n == 0x10FFFF

  /--
  Checks whether a character reference is a [control](https://infra.spec.whatwg.org/#control)
  -/
  control (n : Nat) : Bool := 0x007F ≤ n && n ≤ 0x009F

  /--
  Checks whether a character reference is [ASCII whitespace](https://infra.spec.whatwg.org/#ascii-whitespace)
  -/
  asciiWhitespace (n : Nat) : Bool :=
    n == 0x0009 || -- TAB
    n == 0x000A || -- LF
    n == 0x000C || -- FF
    n == 0x000D || -- CR
    n == 0x0020    -- SPACE

/--
Encodes a character as a named HTML entity.
-/
public def namedEntity? (char : Char) : Option (HashSet String) :=
  stringEntities[String.singleton char]?
