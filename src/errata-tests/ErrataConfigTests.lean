/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Tests of the processing of `errata.toml`, in process: validation with positions, the forms that
settings and strings take, compound durations, and the positions of the characters of filters.
-/
module

public import Errata
public import ErrataConfig

open Errata

public section

namespace ErrataConfigTests

/-- The variants of `errata.toml` that the tests read. -/
def variantsDir : System.FilePath := "src/errata-tests/fixtures/driver-toml/variants"

/-- Reads and validates the variant {name}`name`. -/
def parseVariant (name : String) : IO (Except (Array String) ErrataConfig.File) := do
  ErrataConfig.parse (← IO.FS.readFile (variantsDir / s!"{name}.toml"))

/-- The profile named {name}`name` of a validated file. -/
def profileOf (f : ErrataConfig.File) (name : String) : TestM ErrataConfig.Profile := do
  match f.profiles.find? (·.name == name) with
  | some p => pure p
  | none => fail s!"no profile named '{name}'"

/--
Validation reports each problem at its position in the file: a TOML syntax error, a setting that is
neither a string nor `{ needs = … }` whether its name is a quoted key or nested tables, an unknown
key, profiles that inherit in a cycle, malformed durations, and a malformed `[[executable]]`.
-/
@[test]
def validationReportsPositions : Test := do
  let cases : List (String × List String) := [
    ("syntax", ["errata.toml:1:16:"]),
    ("wrong-type", ["errata.toml:2:22: the setting 'TomlLib.stampFile' must be a string or \
      { needs = \"target\" }, and it is an integer"]),
    ("nested-wrong-type", ["errata.toml:2:20: the setting 'TomlLib.stampFile' must be a string or \
      { needs = \"target\" }, and it is a boolean"]),
    ("unknown-key", ["errata.toml:3:9: unknown key 'flavor' in the profile 'default'"]),
    ("cycle", ["errata.toml:2:11: the profiles inherit in a cycle: a → b → a",
      "errata.toml:5:11: the profiles inherit in a cycle: b → a → b"]),
    ("bad-duration", ["errata.toml:2:10: 'timeout' must be a duration"]),
    ("misordered-duration", ["errata.toml:2:10: 'timeout' must be a duration of one or more whole \
      numbers, each followed by one of the units h, m, s, ms, used at most once each and in that \
      order, such as 90s, 10m, or 2m30s, and it is \"30s2m\""]),
    ("bad-executable", ["errata.toml:3:10: 'command' must have at least one word"])]
  for (variant, messages) in cases do
    result variant do
      match ← parseVariant variant with
      | .ok _ => fail "the file was accepted"
      | .error problems =>
        let all := "\n".intercalate problems.toList
        for m in messages do
          assertContains m all

/--
Settings' names may be written as nested tables as well as quoted dotted keys, and a file may begin
with a byte-order mark and give durations with spaces around them. A setting that needs a target
names the target and the position of its name.
-/
@[test]
def readsTomlForms : Test := do
  for variant in ["nested", "bom"] do
    result variant do
      match ← parseVariant variant with
      | .error problems => fail s!"the file was rejected: {problems}"
      | .ok f =>
        let p ← profileOf f "default"
        let needsStamp := p.settings.any fun (k, v) =>
          k == "TomlLib.stampFile" && v matches .needs "stamp" ..
        assertTrue needsStamp s!"the setting was not read as needing `stamp`: {repr p.settings}"
  result "a duration with spaces" do
    match ← parseVariant "bom" with
    | .error problems => fail s!"the file was rejected: {problems}"
    | .ok f => assertBEq (some 600000) (← profileOf f "default").timeoutMs?

/-- Compound durations such as `2m30s` reach the elaborated file as their totals in milliseconds. -/
@[test]
def compoundDurations : Test := do
  match ← parseVariant "compound-duration" with
  | .error problems => fail s!"the file was rejected: {problems}"
  | .ok f =>
    let p ← profileOf f "default"
    assertBEq (some 150000) p.timeoutMs?
    let json := f.toJson
    assertBEq (some 150000)
      ((json.getObjValD "profiles").getObjValD "default" |>.getObjValAs? Nat "timeout-ms").toOption
  let valid : List (String × Nat) := [("90s", 90000), ("0s", 0), ("1h30m", 5400000),
    ("1s500ms", 1500), (" 2m30s ", 150000)]
  for (text, ms) in valid do
    result text do assertBEq (some ms) (ErrataConfig.durationMs? text)
  for text in ["30s2m", "2m2m", "2 m", "2.5m", "m", ""] do
    result (if text.isEmpty then "the empty string" else text) do
      assertBEq none (ErrataConfig.durationMs? text)

/--
Errors in filters are reported at the line and column in the file of the character where they were
found, in each of TOML's four forms of string, past escapes and a dropped first newline.
-/
@[test]
def filterPositions : Test := do
  let cases := [("filter-literal", "2:33"), ("filter-basic", "2:53"),
    ("filter-ml-literal", "4:8"), ("multiline-filter", "4:8"), ("filter-ml-continued", "4:8")]
  for (variant, place) in cases do
    result variant do
      match ← parseVariant variant with
      | .error problems => fail s!"the file was rejected: {problems}"
      | .ok f =>
        let some filter := (← profileOf f "default").defaultFilter? | fail "no default filter"
        let .error e := Filter.parse filter.text | fail "the filter parsed"
        let source := Filter.Source.file "errata.toml" filter.line filter.col
          (filter.positions?.getD #[])
        assertBEq s!"errata.toml:{place}: expected ')' to end the matcher" (e.render source)

/--
A string token decodes by TOML's rules, with the byte offset of each character and then of the
closing delimiter. Tokens with escapes that TOML does not define have no offsets.
-/
@[test]
def stringOffsets : Test := do
  let cases : List (String × Option (String × Array Nat)) := [
    ("'a\\b'", some ("a\\b", #[1, 2, 3, 4])),
    ("\"a\\\\b\"", some ("a\\b", #[1, 2, 4, 5])),
    ("\"\\u0041x\"", some ("Ax", #[1, 7, 8])),
    ("'''\nab'''", some ("ab", #[4, 5, 6])),
    ("\"\"\"\r\nab\"\"\"", some ("ab", #[5, 6, 7])),
    ("\"\"\"a \\\n  b\"\"\"", some ("a b", #[3, 4, 9, 10])),
    ("\"a\\qb\"", none),
    ("\"\\u00\"", none)]
  for (token, expected) in cases do
    result token do assertBEq expected (ErrataConfig.stringOffsets? token)

/--
When a string's token decodes to a text other than the one the TOML reader gave, the filter has no
positions, and its errors name the string's own position and the offset.
-/
@[test]
def filterPositionsFallBack : Test := do
  let source := "f = 'abc'"
  let fileMap := Lean.FileMap.ofString source
  let ref := Lean.Syntax.atom (.synthetic ⟨4⟩ ⟨9⟩) "'abc'"
  let read (text : String) : Option ErrataConfig.FilterString :=
    (((ErrataConfig.readFilter "f" (.string ref text)).run fileMap).run #[]).1
  result "a token that decodes to the text" do
    assertBEq (some (some #[(1, 5), (1, 6), (1, 7), (1, 8)])) ((read "abc").map (·.positions?))
  result "a token that decodes to another text" do
    assertBEq (some none) ((read "abd").map (·.positions?))
  result "the error without positions" do
    let .error e := Filter.parse "name(y" | fail "the filter parsed"
    assertBEq "errata.toml:1:4: at offset 6 in the filter: expected ')' to end the matcher"
      (e.render (.file "errata.toml" 1 4 #[]))

end ErrataConfigTests
