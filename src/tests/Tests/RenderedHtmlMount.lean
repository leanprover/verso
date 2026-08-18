/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import VersoBlog
public import VersoRenderedHtml
public import Tests.RenderedHtmlExport

public section

open Lean
open Verso Genre Blog
open Verso.Output (Html)
open Verso.Output.Html
open Verso.RenderedHtml (load)
open Tests.RenderedHtmlExport (quietLogger part)

namespace Tests.RenderedHtmlMount

private abbrev TestM := StateRefT Nat IO

private def fail (message : String) : TestM Unit := do
  IO.eprintln s!"  FAIL: {message}"
  modify (· + 1)

private def check (condition : Bool) (message : String) : TestM Unit :=
  unless condition do fail message

private def mentions (text : String) (fragment : String) : Bool :=
  (text.find? fragment).isSome

/-- The hand-written format version 1 directory that guards the format contract. -/
def fixtureDir : System.FilePath := "test-projects/rendered-html-fixture"

/-- A directory whose page paths have a gap. -/
def sparseFixtureDir : System.FilePath := "test-projects/rendered-html-sparse-fixture"

/-- A directory whose static files claim page destinations. -/
def conflictFixtureDir : System.FilePath := "test-projects/rendered-html-conflict-fixture"

/-- The directory that `tutorial-example-rendered-html` writes. -/
def tutorialContent : System.FilePath := "_out/tutorial-content/v1"

/-- A page that a mount can sit under. -/
private def holder (title : String) : Verso.Doc.Part Page :=
  part title #[Verso.Doc.Block.para #[.text "A page that holds mounts."]]

/-- A site that mounts `dirs`, each under the name it is paired with, at the top level. -/
def mountingSite (dirs : Array (String × System.FilePath)) : Site :=
  .page `mounting (holder "Mounting") <|
    dirs.map fun (name, dir) => Dir.mkMount name dir

/-- A site whose root is a blog, so it holds no directories. -/
def blogRootedSite : Site :=
  .blog `blogRoot (holder "A Blog") #[]

/-- The custom property definitions of one theme. -/
private def themeVars (color : String) : String :=
  ":root { --verso-text-color: " ++ color ++ "; }"

/-- A theme that places the fragments that a mount contributes. -/
def mountingTheme (color : String) (withLocalNav : Bool := true) : Theme :=
  { Theme.default with
    primaryTemplate := do
      return {{
        <html>
          <head>
            <title>{{← Template.param (α := String) "title"}}</title>
            {{← Template.builtinHeader}}
            <style>{{themeVars color}}</style>
          </head>
          <body>
            <header><nav class="top"><a href=".">"Home"</a></nav></header>
            <main>{{← Template.param "content"}}</main>
          </body>
        </html>
      }},
    pageTemplate := do
      match (← Template.param? (α := Html) "fragments.content") with
      | some content =>
        let localNav ←
          if withLocalNav then
            pure ((← Template.param? (α := Html) "fragments.localNav").getD .empty)
          else pure .empty
        return {{<article>{{localNav}}{{content}}</article>}}
      | none =>
        return {{<article><h1>{{← Template.param "title"}}</h1>{{← Template.param "content"}}</article>}} }

/--
Traverses and generates a site into `dir`, returning the errors and warnings that were reported.
-/
def generate (dir : System.FilePath) (site : Site) (theme : Theme) :
    IO (Array Verso.LogMessage × Array Verso.LogMessage) := do
  let logger ← quietLogger
  let cfg : Config := { destination := dir }
  let (site, xref) ← site.traverse cfg {} |>.run logger
  let ctxt : Generate.Context := {
    theme, site,
    ctxt := { path := .root, config := cfg, components := {} },
    xref, dir, config := cfg, header := Html.doctype,
    linkTargets := {}, components := {}
  }
  let (((), _), components) ← site.generate theme |>.run ctxt .empty {} |>.run logger
  Template.writeBuiltinAssets dir "body"
  Template.writeHeadAssets dir (theme.headAssets xref components)
  return (← logger.errors, ← logger.warnings)

/--
Traverses a site, returning its traversal state and the errors that were reported.

Traversal reports a conflict through the logger, not through the state, so a test that asserts no
conflict was reported has to read the logger.
-/
def traverseOnly (site : Site) : IO (TraverseState × Array Verso.LogMessage) := do
  let logger ← quietLogger
  let (_, xref) ← site.traverse {} {} |>.run logger
  return (xref, ← logger.errors)

private def attempt (act : IO α) : IO (Except String α) := do
  try
    return .ok (← act)
  catch e =>
    return .error (toString e)

private def expectRejected (what : String) (expected : List String) (act : IO α) : TestM Unit := do
  match ← attempt act with
  | .ok _ => fail s!"{what} was accepted"
  | .error message =>
    for e in expected do
      unless mentions message e do
        fail s!"{what} was rejected, but the message did not mention '{e}': {message}"

private def testPageIds : TestM Unit := do
  let site := mountingSite #[("fixture", fixtureDir), ("fixture-again", fixtureDir)]
  let (xref, errors) ← traverseOnly site
  for name in ["fixture", "fixture.guide", "fixture.guide.first", "fixture.guide.«step-1»",
      "«fixture-again»", "«fixture-again».guide", "«fixture-again».guide.«step-1»"] do
    let id := (Syntax.decodeNameLit s!"`{name}").getD .anonymous
    check (xref.pageIds.find? id |>.isSome)
      s!"Mounting registers the page ID '{name}': {xref.pageIds.toList.map (·.fst)}"
  check errors.isEmpty
    s!"Mounting the same directory twice reports no conflict: {errors.map (·.text)}"

private def testRejections : TestM Unit := do
  expectRejected "A mount of a sparse directory" ["guide"] <|
    traverseOnly (mountingSite #[("sparse", sparseFixtureDir)])
  expectRejected "A mount whose static files claim a page destination" ["index.html"] <|
    traverseOnly (mountingSite #[("conflicting", conflictFixtureDir)])
  expectRejected "Inserting a mount under a blog-rooted path" ["blog"] <|
    blogRootedSite.insertMount [] "fixture" fixtureDir
  expectRejected "Inserting a mount under a static directory" ["not a page"] <|
    (Site.page `s (holder "S") #[.static "files" "test-projects"]).insertMount
      ["files"] "fixture" fixtureDir
  expectRejected "Inserting a mount under a mount" ["not a page"] <|
    (mountingSite #[("fixture", fixtureDir)]).insertMount ["fixture"] "inner" fixtureDir
  expectRejected "Inserting a mount whose name is not a slug" ["slug"] <|
    (Site.page `s (holder "S") #[]).insertMount [] "not a slug" fixtureDir
  -- An empty name would put the mount's root page where its holder's own page goes.
  expectRejected "Inserting a mount whose name is empty" ["slug"] <|
    (Site.page `s (holder "S") #[]).insertMount [] "" fixtureDir
  -- Two directories of the same name would generate into the same place.
  expectRejected "Inserting a mount whose name is taken" ["already holds"] <|
    (mountingSite #[("fixture", fixtureDir)]).insertMount [] "fixture" fixtureDir
  expectRejected "Inserting a mount whose name a static directory holds" ["already holds"] <|
    (Site.page `s (holder "S") #[.static "files" "test-projects"]).insertMount
      [] "files" fixtureDir

private def testExportRejectsMounts : TestM Unit := do
  IO.FS.withTempDir fun tmp => do
    let exported := Tests.RenderedHtmlExport.exportSite (tmp / "mounts")
      (mountingSite #[("fixture", fixtureDir)]) (mountingTheme "black")
    match ← attempt exported with
    | .error message =>
      check (mentions message "mount")
        s!"Exporting a site that holds a mount is rejected: {message}"
    | .ok (_, errors) =>
      check (errors.any fun e => mentions e.text "mount" && mentions e.text "fixture")
        s!"Exporting a site that holds a mount is rejected: {errors.map (·.text)}"

private def testFragmentReports : TestM Unit := do
  IO.FS.withTempDir fun tmp => do
    let site := mountingSite #[("fixture", fixtureDir)]
    let (errors, warnings) ←
      generate (tmp / "dropped") site (mountingTheme "black" (withLocalNav := false))
    check errors.isEmpty s!"Generating a mounting site reported errors: {errors.map (·.text)}"
    check (warnings.any fun w => mentions w.text "localNav" && mentions w.text "fixture")
      s!"A fragment that no template placed is reported: {warnings.map (·.text)}"

    let dropping :=
      Site.page `mounting (holder "Mounting")
        #[Dir.mkMount "fixture" fixtureDir
            { droppedFragments := #["localNav".sluggify] }]
    let (_, warnings) ←
      generate (tmp / "silent") dropping (mountingTheme "black" (withLocalNav := false))
    check (!warnings.any (mentions ·.text "localNav"))
      s!"A mount that drops a fragment on purpose is silent: {warnings.map (·.text)}"

/-- The text between the first occurrence of `before` and the next occurrence of `after`. -/
private def between (before after : String) (text : String) : String :=
  match text.splitOn before with
  | _ :: rest :: _ => (rest.splitOn after).headD ""
  | _ => ""

private def testRetheming : TestM Unit := do
  IO.FS.withTempDir fun tmp => do
    let site := mountingSite #[("fixture", fixtureDir)]
    let dark := tmp / "dark"
    let light := tmp / "light"
    let _ ← generate dark site (mountingTheme "white")
    let _ ← generate light site (mountingTheme "black")
    let darkPage ← IO.FS.readFile (dark / "fixture" / "guide" / "index.html")
    let lightPage ← IO.FS.readFile (light / "fixture" / "guide" / "index.html")
    check (darkPage != lightPage)
      "Two themes whose custom properties differ produce different output"
    check (between "<main>" "</main>" darkPage == between "<main>" "</main>" lightPage)
      "Re-theming leaves the mounted markup alone"
    check (mentions darkPage "--verso-text-color: white" &&
           mentions lightPage "--verso-text-color: black")
      "Each theme's own custom properties reach the page"

    -- The site's own chrome renders on a page that mounts as it does on a page that does not.
    let mountingPage ← IO.FS.readFile (dark / "fixture" / "index.html")
    let plainPage ← IO.FS.readFile (dark / "index.html")
    check (mentions mountingPage "<nav class=\"top\">" && mentions plainPage "<nav class=\"top\">")
      "The site's own chrome renders on a page that mounts and on a page that does not"
    check (between "<header>" "</header>" mountingPage ==
           between "<header>" "</header>" plainPage)
      "The site's own chrome is the same on a page that mounts and on a page that does not"

private def testTutorialOutput : TestM Unit := do
  unless ← (tutorialContent / "verso-rendered-html.json").pathExists do
    IO.println <|
      s!"  Skipping the tutorial output check: '{tutorialContent}' does not exist. " ++
      "Run `lake exe tutorial-example-rendered-html` first."
    return
  match ← attempt (load tutorialContent) with
  | .error message => fail s!"The tutorial emitter's output did not load: {message}"
  | .ok loaded =>
    let manifest := loaded.manifest
    check (manifest.formatVersion == Verso.RenderedHtml.formatVersion)
      "The tutorial emitter writes the current format version"
    check (manifest.pages.contains #[])
      "The tutorial emitter writes a root page"
    check (manifest.stylesheets.any (·.role.placesAsVariables))
      "The tutorial emitter ships its custom property definitions"
    check (manifest.generator.tool == "verso-tutorial")
      s!"The tutorial emitter names itself: {manifest.generator.tool}"

/--
Runs the rendered HTML content mounting tests, returning the number of failures.
-/
def runRenderedHtmlMountTests : IO Nat := do
  let ((), failures) ←
    (do
      testPageIds
      testRejections
      testExportRejectsMounts
      testFragmentReports
      testRetheming
      testTutorialOutput : TestM Unit).run 0
  return failures

end Tests.RenderedHtmlMount
