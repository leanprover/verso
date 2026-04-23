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
public import Verso.Instances
public import MultiVerso.NameMap
public import Verso.Output.Html

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
  /--
  JavaScript code to give a custom rendering for a searchable item. This should be a function that
  takes three arguments:

  {open DomainMapper}
   * {lit}`searchable` is a Searchable object (returned by the {name}`dataToSearchables` function)
     {lit}`Searchable` is the TypeScript type
     {lit}`{searchKey: string, address: string, domainId: string, ref?: any}`. {lit}`searchKey` is
     the text that the user can search for, {lit}`address` is the result's link destination,
     {lit}`domainId` is the name of the Verso domain, and {lit}`ref` is arbitrary data that will
     be passed to a custom rendering function if one exists.
   * {lit}`matchedParts` is an array of objects with TypeScript type
     {lit}`{t: 'text', v: string} | {t: 'highlight', v: string}`. Objects with {lit}`text` in the
     {lit}`t` field are the parts of the search result that provide context, while objects with
     {lit}`highlight` are the parts of the result that match the search string.
   * {lit}`document` is the DOM document object
  -/
  customRender : Option String := none
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

/--
Generates JavaScript code for the provided domain mapper.
-/
public def DomainMapper.toJs (mapper : DomainMapper) : Std.Format :=
  .nest 2 <| .group <|
    .text "{" ++ .line ++
    .nest 2 (.group ("dataToSearchables:" ++ .line ++ mapper.dataToSearchables)) ++ "," ++ .line ++
    .nest 2 (.group ("className:" ++ .line ++ .text mapper.className.quote)) ++ "," ++ .line ++
    .nest 2 (.group ("displayName:" ++ .line ++ .text mapper.displayName.quote)) ++ "," ++ .line ++
    (match mapper.customRender with
      | .none => .nil
      | .some customRender =>
          .nest 2 (.group ("customRender:" ++ .line ++ .text customRender)) ++ "," ++ .line) ++
    .text "}"

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
Site-level search priorities. Values are on a scale from {lit}`0` to {lit}`99`, with {lit}`50` as
the neutral default.

{open SearchPriorities}

The two global knobs, {name}`semantic` and {name}`fullText`, bias the balance between the
quick-jump and full-text result streams. Raising {name}`semantic` above {lean (type := "Fin 100")}`50` prioritizes
fuzzy (quick-jump) matches over full-text matches; raising {name}`fullText` does the reverse.

{name}`domains` assigns per-domain priority to the quick-jump lane, keyed by domain name (e.g.
{lean}`` `Verso.Genre.Manual.section ``). A site may boost or de-emphasize domains shipped by a
library without having to redefine the library's mapper.

All fields compose additively (in log space) with the per-item and per-section priorities in each
stream: a semantic match is scored against {name}`semantic` plus its domain entry plus its item
and section contributions; a full-text match is scored against {name}`fullText` plus its
per-document priority baked in at index time.
-/
public structure SearchPriorities where
  /-- Priority applied to all semantic (fuzzy / quick-jump) match scores. -/
  semantic : Fin 100 := 50
  /-- Priority applied to all full-text search match scores. -/
  fullText : Fin 100 := 50
  /--
  Per-domain priority for quick-jump results, keyed by domain name. Domains not listed here are
  treated as neutral.
  -/
  domains : Verso.NameMap (Fin 100) := {}
deriving Repr, BEq, ToJson, FromJson

/--
A mapping from Verso domain names to their search customizations.
-/
public abbrev DomainMappers : Type := HashMap String DomainMapper

open Std.Format in
/--
Generates code for the provided collection of domain mappers, constructing a JS constant named
{lit}`domainMappers` that's suitable for the quick-jump feature. Also emits a {lit}`searchPriorities`
constant carrying the global full-text / semantic multipliers.
-/
public def DomainMappers.toJs (mappers : DomainMappers) (priorities : SearchPriorities := {}) : Std.Format :=
  let ms := mappers.fold (init := nil) fun code dom m => code ++ line ++ line ++ gen dom m
  let ms' := mappers.keys.map fun dom => nest 2 <| group <| text dom.quote ++ ":" ++ line ++ jsName dom
  -- Emit per-domain priorities as a JS object literal so the browser can look up a domain's
  -- priority by id in one step.
  let domEntries : List Std.Format := priorities.domains.foldl (init := []) fun acc k p =>
    (nest 2 <| group <| text k.toString.quote ++ ":" ++ line ++ text (toString p.val)) :: acc
  let domEntries := domEntries.reverse
  let domainsLit :=
    group (nest 2 ("{" ++ (text "," ++ line).joinSep domEntries) ++ line ++ "}")
  let prio :=
    group (nest 2 (
      "export const searchPriorities = {" ++ line ++
      nest 2 ("semantic: " ++ text (toString priorities.semantic.val) ++ "," ++ line ++
              "fullText: " ++ text (toString priorities.fullText.val) ++ "," ++ line ++
              "domains: " ++ domainsLit) ++ line ++
      "};"))
  ms ++ line ++ line ++
  group (nest 2 ("export const domainMappers = {" ++ (text "," ++ line).joinSep ms') ++ line ++ "};") ++
  line ++ line ++ prio
where
  gen (dom : String) (m : DomainMapper) :=
    text typeComment ++ line ++
    nest 2 (group (text "const " ++ text (jsName dom) ++ " = " ++ m.toJs ++ ";"))

  typeComment := "/**\n * @type {DomainMapper}\n */"

/--
Collects the CSS customizations for each domain.

Domain mappers traditionally scope their rules under {lit}`#search-wrapper` (the
quick-jump combobox's outer element). The full-page search results view reuses the exact
same {lit}`.search-result` markup but lives in a different DOM subtree, so the rules need
to match there too. We rewrite every {lit}`#search-wrapper` to the class
{lit}`.verso-search-results`, which both the combobox wrapper and the full-page results
list carry. Keeping the rewrite here means existing {name}`quickJumpCss` values (which
freely refer to {lit}`#search-wrapper`) keep working without any caller-side changes.
-/
public def DomainMappers.quickJumpCss (mappers : DomainMappers) : String :=
  let raw := mappers.fold (init := "") fun css _ m =>
    match m.quickJumpCss with
    | none => css
    | some x => css ++ x ++ "\n"
  raw.replace "#search-wrapper" ".verso-search-results"


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

/--
The `<script>` and `<link>` tags every page needs to load the search infrastructure
(full-text index, quick-jump combobox on normal pages, plain input + live-updating
list on the full-page search view). All three HTML genres emit the same assets into
the same sibling directory (by convention {lit}`-verso-search/`), so they all include
the same fragment — returning it from one place means new search assets get picked up
by every genre at once.

{name}`searchDir` is the site-root-relative path of the directory containing the
emitted search assets. It is spliced into every {lit}`src`/{lit}`href`, with a trailing
slash added automatically if missing.
-/
public def searchAssetTags (searchDir : String := "-verso-search") : Verso.Output.Html :=
  open Verso.Output.Html in
  let d := if searchDir.endsWith "/" then searchDir else searchDir ++ "/"
  {{
    <script src=s!"{d}elasticlunr.min.js"></script>
    <script src=s!"{d}fuzzysort.min.js"></script>
    <script src=s!"{d}searchIndex.js"></script>
    <script src=s!"{d}search-config.js"></script>
    <script type="module" src=s!"{d}search-init.js"></script>
    <link rel="stylesheet" href=s!"{d}search-box.css"/>
    <link rel="stylesheet" href=s!"{d}search-page.css"/>
    <link rel="stylesheet" href=s!"{d}search-highlight.css"/>
    <link rel="stylesheet" href=s!"{d}domain-display.css"/>
    <script src=s!"{d}search-highlight.js" defer="defer"></script>
  }}
