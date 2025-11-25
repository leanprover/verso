/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

import Std.Data.HashMap
meta import VersoUtil.BinFiles
import VersoUtil.BinFiles
import Std.Data.HashMap
public import Lean.Data.Json.FromToJson

open Std (HashMap)

set_option linter.missingDocs true
set_option doc.verso true

public section

namespace Verso.Search

open Lean

/--
Transforms data in a Verso documentation domain into a quick-jump item.
-/
public structure DomainMapper where
  /--
  The name to be shown in the search UI, such as {lean}`"Compiler Option"` or {lean}`"Terminology"`.
  -/
  displayName : String
  /--
  The HTML class name to apply to results from the domain.

  {open DomainMapper}

  Use {name}`quickJumpCss` to apply CSS rules based on this class name.
  -/
  className : String
  /--
  JavaScript code to transform items from the domain's serialization in {lit}`xref.json` into
  searchable items.

  Searchable items are JavaScript objects with the following fields:
   * {lit}`searchKey` is the string used for fuzzy matching against the user's input
   * {lit}`address` is the link target to be used when clicking on the search result
   * {lit}`domainId` is the domain's name
   * {lit}`ref` is a representation of the value itself, used for equality comparison in case of
     duplicate search keys
  -/
  dataToSearchables : String
  /--
  CSS to be used in the quick-jump box to customize results from the given domain.
  -/
  quickJumpCss : Option String := none
deriving Repr, DecidableEq, ToJson, FromJson

/--
Constructs a domain mapper with default code for the {name}`dataToSearchables` field.

This default code is suitable when the canonical name of the object is the string that users should search for.
-/
public def DomainMapper.withDefaultJs (domain : Lean.Name) (displayName className : String) (css : Option String := none) : DomainMapper where
  displayName := displayName
  className := className
  quickJumpCss := css
  dataToSearchables :=
    "(domainData) =>
  Object.entries(domainData.contents).map(([key, value]) => ({
    searchKey: key,
    address: `${value[0].address}#${value[0].id}`,
    domainId: '" ++ domain.toString ++ "',
    ref: value,
  }))"

open Std Format in
/--
Generates JavaScript code for the provided domain mapper.
-/
public def DomainMapper.toJs (mapper : DomainMapper) : Std.Format :=
  nest 2 <| group <|
    text "{" ++ line ++
    nest 2 (group ("dataToSearchables:" ++ line ++ mapper.dataToSearchables)) ++ "," ++ line ++
    nest 2 (group ("className:" ++ line ++ text mapper.className.quote)) ++ "," ++ line ++
    nest 2 (group ("displayName:" ++ line ++ text mapper.displayName.quote)) ++ line ++
    text "}"

-- Objects could be included as literals, rather than defined, but that makes it more difficult to
-- debug the resulting JS code if needed.
section
private def isValidFirstChar (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == '$'

private def isValidIdChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '$'

private def jsReservedWords : List String := [
  "abstract", "arguments", "await", "boolean", "break", "byte", "case", "catch",
  "char", "class", "const", "continue", "debugger", "default", "delete", "do",
  "double", "else", "enum", "eval", "export", "extends", "false", "final",
  "finally", "float", "for", "function", "goto", "if", "implements", "import",
  "in", "instanceof", "int", "interface", "let", "long", "native", "new",
  "null", "package", "private", "protected", "public", "return", "short",
  "static", "super", "switch", "synchronized", "this", "throw", "throws",
  "transient", "true", "try", "typeof", "var", "void", "volatile", "while",
  "with", "yield"
]


private def isReservedWord (s : String) : Bool :=
  jsReservedWords.contains s


private def charToHex (c : Char) : String :=
  let code := c.toNat
  let hex := Nat.toDigits 16 code
  let hexString := String.ofList hex
  -- Pad to at least 2 characters
  if hexString.length = 1 then "0" ++ hexString else hexString

/--
Mangles a domain's name to that for its mapper, to be used in JS code.
-/
private def jsName (domainName : String) : String := Id.run do
  if domainName.isEmpty then return "_"

  let first := domainName.startPos.get!
  let mut out : String :=
    if isValidFirstChar first then
      first.toString
    else if first.isDigit then
      "_".push first
    else
      "_x" ++ charToHex first

  let mut iter := String.Legacy.iter domainName |>.next
  while h : iter.hasNext do
    let c := iter.curr' h
    iter := iter.next' h
    if isValidIdChar c then
      out := out.push c
    else if c == '.' then
      out := out ++ "_DOT_"
    else
      out := out ++ "_x" ++ charToHex c

  return if isReservedWord out then
    out.push '_'
  else
    out
end

/--
A mapping from Verso domain names to their search customizations.
-/
public abbrev DomainMappers : Type := HashMap String DomainMapper

open Std.Format in
/--
Generates code for the provided collection of domain mappers, constructing a JS constant named
{lit}`domainMappers` that's suitable for the quick-jump feature.
-/
public def DomainMappers.toJs (mappers : DomainMappers) : Std.Format :=
  let ms := mappers.fold (init := nil) fun code dom m => code ++ line ++ line ++ gen dom m
  let ms' := mappers.keys.map fun dom => nest 2 <| group <| text dom.quote ++ ":" ++ line ++ jsName dom
  ms ++ line ++ line ++
  group (nest 2 ("export const domainMappers = {" ++ (text "," ++ line).joinSep ms') ++ line ++ "};")
where
  gen (dom : String) (m : DomainMapper) :=
    text typeComment ++ line ++
    nest 2 (group (text "const " ++ text (jsName dom) ++ " = " ++ m.toJs ++ ";"))

  typeComment := "/**\n * @type {DomainMapper}\n */"

/--
Collects the CSS customizations for each domain.
-/
public def DomainMappers.quickJumpCss (mappers : DomainMappers) : String :=
  mappers.fold (init := "") fun css _ m =>
    match m.quickJumpCss with
    | none => css
    | some x => css ++ x ++ "\n"


section
open Verso.BinFiles

/--
The search box code
-/
public def searchBoxCode : Array (String × ByteArray) :=
  (include_bin_dir "../../../static-web/search").filterMap fun (name, contents) =>
    if name.endsWith "domain-mappers.js" then none
    else some (name.dropPrefix "../../../static-web/search/" |>.copy, contents)

end
