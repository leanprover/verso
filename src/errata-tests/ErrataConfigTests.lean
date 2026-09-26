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
  ErrataConfig.parse "errata.toml" (← IO.FS.readFile (variantsDir / s!"{name}.toml"))

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
      { needs = \"name\" }, and it is an integer"]),
    ("nested-wrong-type", ["errata.toml:2:20: the setting 'TomlLib.stampFile' must be a string or \
      { needs = \"name\" }, and it is a boolean"]),
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
with a byte-order mark and give durations with spaces around them. A setting that refers to a need
names the need and the position of its name.
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
  result "nested tables through the runner" do
    match ← parseVariant "nested" with
    | .error problems => fail s!"the file was rejected: {problems}"
    | .ok f =>
      let workspace := Lean.Json.mkObj [("protocol", 1),
        ("needs", Lean.Json.mkObj [("stamp", "/out/stamp.txt")])]
      match Runner.Config.ofJson f.toJson workspace (some "default") with
      | .error e => fail e
      | .ok c =>
        assertBEq (some #[("TomlLib.stampFile", "/out/stamp.txt")])
          ((c.profile? "default").map (·.settings))

/-- The problems that validating {name}`text` reports, joined by newlines. -/
def problemsOf (text : String) : TestM String := do
  match ← ErrataConfig.parse "errata.toml" text with
  | .ok _ => fail "the file was accepted"
  | .error problems => return "\n".intercalate problems.toList

/--
The `[needs]` table binds names to Lake targets, each with the position of its target's string, and
the elaborated file holds it under `needs`. Settings of profiles and of overrides refer to its
names, and each reference keeps the name. A reference to a name that the table lacks is a problem at
the reference, and so is a value of the table that is not a string, at the value.
-/
@[test]
def needsTable : Test := do
  let text := "[needs]\nexe = \"verso\"\nsite = \"pkg/:site\"\n\n\
    [profile.default.settings]\na = { needs = \"exe\" }\n\n\
    [[profile.default.override]]\nfilter = \"all()\"\nsettings = { b = { needs = \"site\" } }\n"
  match ← ErrataConfig.parse "errata.toml" text with
  | .error problems => fail s!"the file was rejected: {problems}"
  | .ok f =>
    result "the table" do
      assertBEq #[("exe", "verso", 2, 6), ("site", "pkg/:site", 3, 7)]
        (f.needs.map fun n => (n.name, n.target, n.line, n.col))
      let needs := f.toJson.getObjValD "needs"
      assertBEq (some "pkg/:site") ((needs.getObjValD "site").getObjValAs? String "target").toOption
    let p ← profileOf f "default"
    result "a profile's reference" do
      assertTrue (p.settings.any fun (k, v) => k == "a" && v matches .needs "exe" ..)
        s!"the reference was not read: {repr p.settings}"
    result "an override's reference" do
      let settings := p.overrides.flatMap (·.settings)
      assertTrue (settings.any fun (k, v) => k == "b" && v matches .needs "site" ..)
        s!"the reference was not read: {repr settings}"
  let cases : List (String × String × String) := [
    ("a name that the table lacks", "[profile.default.settings]\na = { needs = \"nope\" }\n",
      "errata.toml:2:14: the setting 'a' refers to the need 'nope', and the [needs] table has no \
        entry of that name"),
    ("a name that the table lacks, in an override",
      "[needs]\nx = \"t\"\n[[profile.default.override]]\nfilter = \"all()\"\n\
        settings = { a = { needs = \"y\" } }\n",
      "errata.toml:5:27: the setting 'a' refers to the need 'y', and the [needs] table has no \
        entry of that name"),
    ("a value of the table that is not a string", "[needs]\nexe = 3\n",
      "errata.toml:2:6: the need 'exe' must name a Lake target as a string, and it is an integer")]
  for (name, text, message) in cases do
    result name do assertBEq message (← problemsOf text)

/--
Validation reports inheritance from a missing profile or from the profile itself, keys that
overrides do not take, a repeated `[[executable]]` name, `needs` tables with other keys or a
non-string name, and a setting given both in a nested table and as a dotted key.
-/
@[test]
def reportsStructuralProblems : Test := do
  let cases : List (String × String × String) := [
    ("a missing parent", "[profile.a]\ninherits = \"nope\"\n",
      "errata.toml:2:11: the profile 'a' inherits from 'nope', which is not a profile"),
    ("the profile itself", "[profile.a]\ninherits = \"a\"\n",
      "errata.toml:2:11: the profiles inherit in a cycle: a → a"),
    ("a key of a profile in an override",
      "[[profile.default.override]]\nfilter = \"all()\"\njobs = 2\n",
      "errata.toml:3:7: unknown key 'jobs' in an override of the profile 'default'"),
    ("a repeated executable",
      "[[executable]]\nname = \"x\"\ncommand = [\"a\"]\n\
        [[executable]]\nname = \"x\"\ncommand = [\"b\"]\n",
      "the [[executable]] name 'x' is used more than once"),
    ("a needs table with other keys",
      "[profile.default.settings]\nx = { needs = \"t\", other = \"u\" }\n",
      "the setting 'x' must be a string or { needs = \"name\" }, and its table has keys besides \
        'needs'"),
    ("a non-string need", "[profile.default.settings]\ny = { needs = 1 }\n",
      "'needs' must name an entry of the [needs] table as a string, and it is an integer"),
    ("a setting nested and flat",
      "[profile.default.settings]\n\"A.b\" = \"1\"\n[profile.default.settings.A]\nb = \"2\"\n",
      "the setting 'A.b' is given twice")]
  for (name, text, message) in cases do
    result name do assertContains message (← problemsOf text)

/--
Problems are reported in the order of the file, and problems at one position in the order they
were found. A cycle is named by its own profiles, each of which reports it, and a profile that only
leads into it adds nothing.
-/
@[test]
def reportsProblemsInOrder : Test := do
  result "a bare [[executable]]" do
    assertBEq "errata.toml:1:0: an [[executable]] needs a 'name'\n\
      errata.toml:1:0: an [[executable]] needs a 'command'" (← problemsOf "[[executable]]\n")
  result "a profile that leads into a cycle" do
    let text := "[profile.b]\ninherits = \"c\"\n[profile.c]\ninherits = \"d\"\n\
      [profile.d]\ninherits = \"c\"\n"
    assertBEq "errata.toml:4:11: the profiles inherit in a cycle: c → d → c\n\
      errata.toml:6:11: the profiles inherit in a cycle: d → c → d" (← problemsOf text)

/-- The built `errata-config` reports a file that it cannot read, and exits with `1`. -/
@[test]
def configBinaryReportsUnreadableFile : Test := do
  let exe : System.FilePath := ".lake/build/bin/errata-config"
  unless ← exe.pathExists do fail s!"errata-config is not built at {exe}"
  IO.FS.withTempDir fun dir => do
    let out ← IO.Process.output
      { cmd := exe.toString, args := #[dir.toString, (dir / "config.json").toString] }
    assertBEq 1 out.exitCode
    assertContains s!"errata-config: cannot read {dir}:" out.stderr

/--
The built `errata-config` names the configuration file by the path its command line gives: in a
syntax error, in an unknown key's problem, and in the position of each filter of the elaborated
file.
-/
@[test]
def configBinaryNamesItsFile : Test := do
  let exe : System.FilePath := ".lake/build/bin/errata-config"
  unless ← exe.pathExists do fail s!"errata-config is not built at {exe}"
  IO.FS.withTempDir fun dir => do
    let file := dir / "other.toml"
    let out := dir / "config.json"
    let elaborate (text : String) : IO IO.Process.Output := do
      IO.FS.writeFile file text
      IO.Process.output { cmd := exe.toString, args := #[file.toString, out.toString] }
    result "a syntax error" do
      let r ← elaborate "[profile.default\n"
      assertBEq 1 r.exitCode
      assertContains s!"{file}:1:" r.stderr
      assertNotContains "errata.toml" r.stderr
    result "an unknown key" do
      let r ← elaborate "[profile.default]\nflavor = \"x\"\n"
      assertBEq 1 r.exitCode
      assertContains s!"{file}:2:9: unknown key 'flavor' in the profile 'default'" r.stderr
    result "a filter's position" do
      let r ← elaborate "default-filter = \"all()\"\n"
      assertBEq 0 r.exitCode
      let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile out))
      assertBEq (some file.toString)
        ((json.getObjValD "default-filter").getObjValAs? String "file").toOption

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
  for text in ["30s2m", "2m2m", "2 m", "2.5m", "m", "", "1d", "-1s"] do
    result (if text.isEmpty then "the empty string" else text) do
      assertBEq none (ErrataConfig.durationMs? text)
  result "a very large number" do
    assertBEq (some (99999999999999999999 * 1000))
      (ErrataConfig.durationMs? "99999999999999999999s")

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
closing delimiter. Tokens with escapes outside TOML's set have no offsets.
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
    ("\"\\U0001F600x\"", some ((String.singleton (Char.ofNat 0x1F600)).push 'x', #[1, 11, 12])),
    ("'''a\r\nb'''", some ("a\r\nb", #[3, 4, 5, 6, 7])),
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

/--
Profiles name their report files with `junit`, `json`, and `markdown`, each a path, which profiles
inherit from their ancestors and the runner reads from the elaborated file. Paths that are not
strings, or are empty, are problems at their positions.
-/
@[test]
def reportPathsAreProfileKeys : Test := do
  let text := "[profile.default]\njunit = \"r.xml\"\n\n[profile.ci]\nmarkdown = \"s.md\"\n\
    json = \"out/r.json\"\n"
  match ← ErrataConfig.parse "errata.toml" text with
  | .error problems => fail s!"the file was rejected: {problems}"
  | .ok f =>
    let ci ← profileOf f "ci"
    assertBEq (some "r.xml") ci.junit?
    assertBEq (some "s.md") ci.markdown?
    assertBEq (some "out/r.json") ci.json?
    assertBEq none (← profileOf f "default").markdown?
    match Runner.Config.ofJson f.toJson (Lean.Json.mkObj [("protocol", 1)]) none with
    | .error e => fail e
    | .ok c =>
      let p? := c.profile? "ci"
      assertBEq (some (some "r.xml")) (p?.map (·.junitPath?))
      assertBEq (some (some "s.md")) (p?.map (·.markdownPath?))
      assertBEq (some (some "out/r.json")) (p?.map (·.jsonPath?))
  let cases : List (String × String) := [
    ("[profile.ci]\njunit = 3\n",
      "errata.toml:2:8: 'junit' must be a path string, and it is an integer"),
    ("[profile.ci]\nmarkdown = \"\"\n",
      "errata.toml:2:11: 'markdown' must be a path, and it is the empty string")]
  for (text, message) in cases do
    result message do
      match ← ErrataConfig.parse "errata.toml" text with
      | .ok _ => fail "the file was accepted"
      | .error problems => assertBEq #[message] problems

/--
Profiles name the order in which the runner starts tests with `order`, `"default"` or `"shuffle"`,
which profiles inherit from their ancestors and the runner reads from the elaborated file. Other
values are problems at their positions, and so is the key in an override, since a run has one order.
-/
@[test]
def orderIsAProfileKey : Test := do
  let text := "[profile.default]\norder = \"shuffle\"\n\n[profile.ci]\njobs = 2\n\n\
    [profile.plain]\norder = \"default\"\n"
  match ← ErrataConfig.parse "errata.toml" text with
  | .error problems => fail s!"the file was rejected: {problems}"
  | .ok f =>
    assertBEq (some .shuffle) (← profileOf f "default").order?
    assertBEq (some .shuffle) (← profileOf f "ci").order?
    assertBEq (some .default) (← profileOf f "plain").order?
    match Runner.Config.ofJson f.toJson (Lean.Json.mkObj [("protocol", 1)]) none with
    | .error e => fail e
    | .ok c =>
      assertBEq (some (some .shuffle)) ((c.profile? "ci").map (·.order?))
      assertBEq (some (some .default)) ((c.profile? "plain").map (·.order?))
  match ← ErrataConfig.parse "errata.toml" "[profile.default]\njobs = 2\n" with
  | .error problems => fail s!"the file was rejected: {problems}"
  | .ok f => assertBEq none (← profileOf f "default").order?
  let cases : List (String × String) := [
    ("[profile.ci]\norder = \"random\"\n",
      "errata.toml:2:8: 'order' must be \"default\" or \"shuffle\", and it is \"random\""),
    ("[profile.ci]\norder = 1\n",
      "errata.toml:2:8: 'order' must be the string \"default\" or \"shuffle\", and it is an \
        integer"),
    ("[[profile.default.override]]\nfilter = \"all()\"\norder = \"shuffle\"\n",
      "errata.toml:3:8: 'order' is one per run, so it belongs to a profile and never to an \
        override")]
  for (text, message) in cases do
    result message do
      match ← ErrataConfig.parse "errata.toml" text with
      | .ok _ => fail "the file was accepted"
      | .error problems => assertBEq #[message] problems

/--
A profile bounds its fixtures' phases with `fixture-timeout`. The key in an override is a problem at
its position, since a fixture's phases serve several tests.
-/
@[test]
def fixtureTimeoutIsAProfileKey : Test := do
  match ← ErrataConfig.parse "errata.toml" "[profile.default]\nfixture-timeout = \"2m\"\n" with
  | .error problems => fail s!"the file was rejected: {problems}"
  | .ok f => assertBEq (some 120000) (← profileOf f "default").fixtureTimeoutMs?
  let text := "[[profile.default.override]]\nfilter = \"all()\"\nfixture-timeout = \"1m\"\n"
  match ← ErrataConfig.parse "errata.toml" text with
  | .ok _ => fail "the file was accepted"
  | .error problems =>
    assertBEq #["errata.toml:3:18: a fixture's phases serve several tests, so 'fixture-timeout' \
      belongs to a profile and never to an override"] problems

/--
The runner writes the report files at the paths that the profile names, relative to the package's
directory, and a path on the command line takes the place of the profile's.
-/
@[test]
def reportPathsResolve : Test := do
  let config : Runner.Config := {
    packageDir? := some "/pkg"
    profiles := #[{ name := "ci", junitPath? := some "r.xml", markdownPath? := some "s.md" }] }
  assertBEq (some "/pkg/r.xml", none, some "/pkg/s.md")
    (Runner.reportPaths config { profile := "ci" })
  assertBEq (some "mine.xml", some "j.json", some "/pkg/s.md")
    (Runner.reportPaths config
      { profile := "ci", junitPath := some "mine.xml", jsonPath := some "j.json" })
  assertBEq (none, none, none) (Runner.reportPaths config {})

end ErrataConfigTests
