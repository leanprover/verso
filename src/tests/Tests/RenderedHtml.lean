/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import VersoRenderedHtml

public section

open Lean (Json ToJson FromJson toJson fromJson?)
open Verso Multi RenderedHtml

namespace Tests.RenderedHtml

/-- The hand-written format version 1 directory that guards the format contract. -/
def fixtureDir : System.FilePath := "test-projects/rendered-html-fixture"

/-- A directory whose page paths have a gap. -/
def sparseFixtureDir : System.FilePath := "test-projects/rendered-html-sparse-fixture"

/-- A directory whose static files claim page destinations. -/
def conflictFixtureDir : System.FilePath := "test-projects/rendered-html-conflict-fixture"

private abbrev TestM := StateRefT Nat IO

private def fail (message : String) : TestM Unit := do
  IO.eprintln s!"  FAIL: {message}"
  modify (· + 1)

private def check (condition : Bool) (message : String) : TestM Unit :=
  unless condition do fail message

private def checkEq [BEq α] [ToString α] (actual expected : α) (what : String) : TestM Unit :=
  unless actual == expected do
    fail s!"{what}: expected '{expected}', got '{actual}'"

private def attempt (act : IO α) : IO (Except String α) := do
  try
    return .ok (← act)
  catch e =>
    return .error (toString e)

private def mentions (message : String) (fragment : String) : Bool :=
  (message.find? fragment).isSome

private def expectRejected (what : String) (expected : List String) (forbidden : List String := [])
    (act : IO α) : TestM Unit := do
  match ← attempt act with
  | .ok _ => fail s!"{what} was accepted"
  | .error message =>
    for e in expected do
      unless mentions message e do
        fail s!"{what} was rejected, but the message did not mention '{e}': {message}"
    for f in forbidden do
      if mentions message f then
        fail s!"{what} was rejected, and the message wrongly mentioned '{f}': {message}"

private def expectAccepted (what : String) (act : IO α) : TestM (Option α) := do
  match ← attempt act with
  | .ok v => return some v
  | .error message =>
    fail s!"{what} was rejected: {message}"
    return none

/-- A manifest with fields that this version of Verso does not know, at both levels. -/
private def manifestWithUnknownFields : String := "
{\"format\": \"verso-rendered-html\",
 \"formatVersion\": 1,
 \"futureField\": {\"anything\": [1, 2, 3]},
 \"generator\": {\"tool\": \"t\", \"version\": \"v\", \"toolchain\": \"tc\", \"futureField\": 1},
 \"title\": \"Round Trip\",
 \"titleHtml\": \"Round <em>Trip</em>\",
 \"stylesheets\": [{\"path\": \"static/a.css\", \"role\": \"variables\"},
                 {\"path\": \"static/b.css\", \"role\": \"content\"},
                 {\"path\": \"static/c.css\", \"role\": \"someday\"}],
 \"scripts\": [{\"path\": \"static/a.js\", \"defer\": true,
              \"provides\": {\"name\": \"katex\", \"version\": \"0.16.22\"}}],
 \"pages\": {\"\": {\"title\": \"Root\", \"titleHtml\": \"Root\", \"futureField\": 7,
                \"fragments\": {\"content\": {\"file\": \"fragments/content.html\",
                                          \"rootToken\": \"%verso:root%\",
                                          \"futureField\": \"x\"}}},
           \"one\": {\"title\": \"One\", \"titleHtml\": \"One\",
                   \"fragments\": {\"content\": {\"file\": \"fragments/one/content.html\",
                                             \"rootToken\": \"%verso:root%\"}}}}}
"

private def parseManifest (text : String) : IO RenderedHtmlContent := do
  let json ←
    match Json.parse text with
    | .ok json => pure json
    | .error e => throw <| .userError s!"Failed to parse: {e}"
  match fromJson? json with
  | .ok (manifest : RenderedHtmlContent) => pure manifest
  | .error e => throw <| .userError s!"Failed to read: {e}"

private def testRoundTrip : TestM Unit := do
  let some manifest ← expectAccepted "A manifest with unknown fields"
      (parseManifest manifestWithUnknownFields)
    | return
  checkEq manifest.title "Round Trip" "The title of the round-tripped manifest"
  checkEq manifest.pages.size 2 "The page count of the round-tripped manifest"
  checkEq manifest.stylesheets.size 3 "The stylesheet count of the round-tripped manifest"
  check (manifest.stylesheets[2]!.role == .other "someday")
    "An unrecognized stylesheet role is kept"
  check (!manifest.stylesheets[2]!.role.placesAsVariables)
    "An unrecognized stylesheet role is placed as content"
  check (manifest.stylesheets[0]!.role.placesAsVariables)
    "The variables role is placed ahead of the rest"
  checkEq manifest.stylesheets[0]!.mountPath "a.css" "The mount path of a stylesheet"
  checkEq manifest.scripts[0]!.mountPath "a.js" "The mount path of a script"
  checkEq (manifest.scripts[0]!.provides.map (·.name)) (some "katex")
    "The library that a script is a copy of"
  checkEq (manifest.stylesheets[0]!.provides.map (·.name)) none
    "A stylesheet that is no library names none"
  let again ← parseManifest (toJson manifest).compress
  checkEq (toJson again).compress (toJson manifest).compress
    "Serializing and reading a manifest again is the identity"

/-- A manifest that leaves out every field that carries a default. -/
private def manifestWithoutOptionalFields : String := "
{\"format\": \"verso-rendered-html\",
 \"formatVersion\": 1,
 \"generator\": {\"tool\": \"t\", \"version\": \"v\", \"toolchain\": \"tc\"},
 \"title\": \"Sparse\",
 \"titleHtml\": \"Sparse\"}
"

private def testOptionalFields : TestM Unit := do
  let some manifest ← expectAccepted "A manifest that leaves out the fields carrying defaults"
      (parseManifest manifestWithoutOptionalFields)
    | return
  checkEq manifest.stylesheets.size 0 "An absent stylesheet list reads as empty"
  checkEq manifest.scripts.size 0 "An absent script list reads as empty"
  checkEq manifest.pages.size 0 "An absent page map reads as empty"
  -- A field that is present but of the wrong type is still an error.
  expectRejected "A manifest whose stylesheet list is not a list" [] (act := parseManifest <|
    "{\"format\": \"verso-rendered-html\", \"formatVersion\": 1,
      \"generator\": {\"tool\": \"t\", \"version\": \"v\", \"toolchain\": \"tc\"},
      \"title\": \"T\", \"titleHtml\": \"T\", \"stylesheets\": 7}")

private def testFixture : TestM Unit := do
  let some loaded ← expectAccepted "The checked-in fixture" (load fixtureDir)
    | return
  let manifest := loaded.manifest
  checkEq manifest.formatVersion 1 "The fixture's format version"
  checkEq manifest.title "Fixture Content" "The fixture's title"
  checkEq manifest.titleHtml "Fixture <em>Content</em>" "The fixture's HTML title"
  let paths := manifest.pages.toArray.map (pathToString ·.fst)
  checkEq (", ".intercalate paths.toList) ", guide, guide/first, guide/step-1"
    "The fixture's page paths, in order"
  check (manifest.stylesheets.any (·.role == .other "decoration"))
    "The fixture carries a stylesheet with an unrecognized role"

  let some rootPage := manifest.pages[(#[] : Multi.Path)]?
    | fail "The fixture has no root page"
  checkEq rootPage.title "Fixture Content" "The fixture root page's title"
  let some rootFragment := rootPage.fragments["content".sluggify]?
    | fail "The fixture root page has no content fragment"
  checkEq rootFragment.rootToken defaultRootToken "The fixture root fragment's token"
  let rootText ← loaded.readFragment rootFragment "../.."
  check (mentions rootText "href=\"../../guide/\"")
    s!"Substituting the fixture root fragment's token: {rootText}"
  check (mentions rootText "href=\"/\"")
    "A URL that begins with a slash carries no token"
  check (!mentions rootText defaultRootToken)
    "Substitution replaces every occurrence of the token"

  let some deepPage := manifest.pages[(#["guide", "first"] : Multi.Path)]?
    | fail "The fixture has no page at 'guide/first'"
  checkEq deepPage.titleHtml "First <code>Steps</code>" "The fixture deep page's HTML title"
  let some deepFragment := deepPage.fragments["content".sluggify]?
    | fail "The fixture page at 'guide/first' has no content fragment"
  check (deepFragment.rootToken != defaultRootToken)
    "A fragment whose prose spells the default token declares a uniquified one"
  let deepText ← loaded.readFragment deepFragment "../../.."
  check (mentions deepText defaultRootToken)
    "Uniquifying a fragment's token leaves the prose that spells the default token alone"
  check (mentions deepText "href=\"../../../files/example.txt\"")
    s!"Substituting a uniquified token: {deepText}"

private def testTokens : TestM Unit := do
  check (hasToken defaultRootToken s!"a {defaultRootToken} b") "A token in the text is found"
  check (!hasToken defaultRootToken "a b") "A token that is absent is not found"
  checkEq (chooseToken "nothing to see here") defaultRootToken
    "Text without the default token gets the default token"
  let chosen := chooseToken s!"prose that spells {defaultRootToken}"
  check (chosen != defaultRootToken) "Text with the default token gets a uniquified token"
  check (!hasToken chosen s!"prose that spells {defaultRootToken}")
    "The uniquified token does not occur in the text"
  checkEq (substitute defaultRootToken "x" s!"{defaultRootToken}/a {defaultRootToken}/b")
    "x/a x/b" "Substitution replaces every occurrence"

private def testRejections : TestM Unit := do
  expectRejected "A sparse page path set" ["guide"] (act := load sparseFixtureDir)
  expectRejected "A directory whose static files claim page destinations"
    ["index.html", "guide"] (forbidden := ["'ab'", "static/ab"])
    (act := load conflictFixtureDir)

  IO.FS.withTempDir fun tmp => do
    let dir := tmp / "newer"
    IO.FS.createDirAll dir
    IO.FS.writeFile (manifestFile dir)
      "{\"format\": \"verso-rendered-html\", \"formatVersion\": 99,
        \"generator\": {\"tool\": \"t\", \"version\": \"v\", \"toolchain\": \"tc\"},
        \"title\": \"T\", \"titleHtml\": \"T\", \"stylesheets\": [], \"scripts\": [],
        \"pages\": {}}"
    expectRejected "A newer format version" ["newer Verso"] (act := load dir)

  IO.FS.withTempDir fun tmp => do
    let dir := tmp / "missing-asset"
    IO.FS.createDirAll (dir / "fragments")
    IO.FS.writeFile (dir / "fragments" / "content.html") "<div>%verso:root%</div>"
    IO.FS.writeFile (manifestFile dir)
      "{\"format\": \"verso-rendered-html\", \"formatVersion\": 1,
        \"generator\": {\"tool\": \"t\", \"version\": \"v\", \"toolchain\": \"tc\"},
        \"title\": \"T\", \"titleHtml\": \"T\",
        \"stylesheets\": [{\"path\": \"static/gone.css\", \"role\": \"content\"}],
        \"pages\": {\"\": {\"title\": \"T\", \"titleHtml\": \"T\",
                       \"fragments\": {\"content\": {\"file\": \"fragments/content.html\",
                                                 \"rootToken\": \"%verso:root%\"}}}}}"
    expectRejected "A stylesheet that is not there" ["static/gone.css"] (act := load dir)

  IO.FS.withTempDir fun tmp => do
    let dir := tmp / "no-pages"
    IO.FS.createDirAll dir
    IO.FS.writeFile (manifestFile dir)
      "{\"format\": \"verso-rendered-html\", \"formatVersion\": 1,
        \"generator\": {\"tool\": \"t\", \"version\": \"v\", \"toolchain\": \"tc\"},
        \"title\": \"T\", \"titleHtml\": \"T\", \"pages\": {}}"
    expectRejected "A manifest with no pages" ["dense"] (act := load dir)

  for (what, path) in [("absolute", "/etc/passwd"), ("dotted", "fragments/../../secret.html")] do
    IO.FS.withTempDir fun tmp => do
      let dir := tmp / what
      IO.FS.createDirAll dir
      IO.FS.writeFile (manifestFile dir) <|
        "{\"format\": \"verso-rendered-html\", \"formatVersion\": 1,
          \"generator\": {\"tool\": \"t\", \"version\": \"v\", \"toolchain\": \"tc\"},
          \"title\": \"T\", \"titleHtml\": \"T\", \"stylesheets\": [], \"scripts\": [],
          \"pages\": {\"\": {\"title\": \"T\", \"titleHtml\": \"T\",
                         \"fragments\": {\"content\": {\"file\": \"" ++ path ++
        "\", \"rootToken\": \"%verso:root%\"}}}}}"
      expectRejected s!"A fragment file with an {what} path" [path] (act := load dir)

  for badPath in ["a/b c", "a//b", "a/./b", "a/../b"] do
    expectRejected s!"A page path '{badPath}'" [] (act := parseManifest <|
      "{\"format\": \"verso-rendered-html\", \"formatVersion\": 1,
        \"generator\": {\"tool\": \"t\", \"version\": \"v\", \"toolchain\": \"tc\"},
        \"title\": \"T\", \"titleHtml\": \"T\", \"stylesheets\": [], \"scripts\": [],
        \"pages\": {\"" ++ badPath ++
      "\": {\"title\": \"T\", \"titleHtml\": \"T\", \"fragments\": {}}}}")

private def testSlugs : TestM Unit := do
  for good in ["abc", "a-b_c", "ABC123", "-", "_"] do
    check (Slug.isSlug? good |>.isSome) s!"'{good}' is a slug"
  for bad in ["a b", "a.b", "a/b", "a<b", "æble", ".", ".."] do
    check (Slug.isSlug? bad |>.isNone) s!"'{bad}' is not a slug"
    check (bad.sluggify.toString != bad) s!"Sluggifying '{bad}' changes it"

private def sampleOutput : Output where
  generator := { tool := "verso-tests", version := "1", toolchain := "none" }
  title := "Written Content"
  titleHtml := "Written Content"
  stylesheets := #[{ path := "static/-verso-data/x.css", role := .variables }]
  scripts := #[{ path := "static/-verso-data/x.js", defer := true }]
  pages := #[
    { path := #[], title := "Root", titleHtml := "Root",
      fragments := #[{
        name := "content".sluggify, rootToken := defaultRootToken,
        content := s!"<div class=\"verso-content content w\"><a href=\"{defaultRootToken}/one/\">One</a></div>"
      }] },
    { path := #["one"], title := "One", titleHtml := "One",
      fragments := #[{
        name := "content".sluggify, rootToken := defaultRootToken,
        content := "<div class=\"verso-content content w\"><p>One.</p></div>"
      }] }
  ]

private def testWrite : TestM Unit := do
  IO.FS.withTempDir fun tmp => do
    let first := tmp / "first"
    let second := tmp / "second"
    for dir in [first, second] do
      IO.FS.createDirAll dir
      writeStaticFile dir "-verso-data/x.css" (.text ":root { --verso-text-color: black; }\n")
      writeStaticFile dir "-verso-data/x.js" (.text "// nothing\n")
      let _ ← expectAccepted "Writing a directory" (write dir sampleOutput)
    let firstManifest ← IO.FS.readBinFile (manifestFile first)
    let secondManifest ← IO.FS.readBinFile (manifestFile second)
    check (firstManifest == secondManifest)
      "Writing unchanged content twice produces identical manifests"
    let some loaded ← expectAccepted "A directory that was just written" (load first)
      | return
    checkEq loaded.manifest.pages.size 2 "The page count of a directory that was just written"

    let third := tmp / "third"
    IO.FS.createDirAll third
    writeStaticFile third "-verso-data/x.js" (.text "// nothing\n")
    expectRejected "Writing a directory that names a stylesheet it did not write"
      ["x.css"] (act := write third sampleOutput)

    let fourth := tmp / "fourth"
    IO.FS.createDirAll fourth
    writeStaticFile fourth "-verso-data/x.css" (.text ":root {}\n")
    writeStaticFile fourth "-verso-data/x.js" (.text "// nothing\n")
    expectRejected "Writing a directory with no pages"
      ["dense"] (act := write fourth { sampleOutput with pages := #[] })

  IO.FS.withTempDir fun tmp => do
    let dir := tmp / "conflict"
    IO.FS.createDirAll dir
    writeStaticFile dir "index.html" (.text "<p>Claims the root page's destination.</p>\n")
    writeStaticFile dir "-verso-data/x.css" (.text ":root { }\n")
    writeStaticFile dir "-verso-data/x.js" (.text "// nothing\n")
    expectRejected "Writing a directory whose static files claim a page destination"
      ["index.html"] (act := write dir sampleOutput)

  IO.FS.withTempDir fun tmp => do
    let dir := tmp / "sparse"
    IO.FS.createDirAll dir
    expectRejected "Writing a sparse page path set" ["deep"] (act := write dir { sampleOutput with
        pages := #[
          { path := #[], title := "Root", titleHtml := "Root", fragments := #[] },
          { path := #["deep", "page"], title := "Deep", titleHtml := "Deep", fragments := #[] }
        ] })

  IO.FS.withTempDir fun tmp => do
    let dir := tmp / "asset"
    IO.FS.createDirAll dir
    expectRejected "Writing an asset path outside the static directory" ["elsewhere"]
      (act := write dir { sampleOutput with
        stylesheets := #[{ path := "elsewhere/x.css", role := .content }] })

/--
Runs the rendered HTML content format tests, returning the number of failures.
-/
def runRenderedHtmlTests : IO Nat := do
  let ((), failures) ←
    (do
      testRoundTrip
      testOptionalFields
      testFixture
      testTokens
      testRejections
      testSlugs
      testWrite : TestM Unit).run 0
  return failures

end Tests.RenderedHtml
