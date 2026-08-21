/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import VersoBlog
public import VersoRenderedHtml

public section

open Lean
open Verso Genre Blog
open Verso.Output (Html)
open Verso.Output.Html
open Verso.RenderedHtml (load manifestFile staticDir)

namespace Tests.RenderedHtmlExport

private abbrev TestM := StateRefT Nat IO

private def fail (message : String) : TestM Unit := do
  IO.eprintln s!"  FAIL: {message}"
  modify (· + 1)

private def check (condition : Bool) (message : String) : TestM Unit :=
  unless condition do fail message

private def mentions (text : String) (fragment : String) : Bool :=
  (text.find? fragment).isSome

/-- A logger that accumulates messages without printing them. -/
def quietLogger : IO (Verso.Logger IO) := do
  let errorsRef ← IO.mkRef #[]
  let warningsRef ← IO.mkRef #[]
  return {
    log severity text loc := do
      let msg : Verso.LogMessage := { severity, text, loc }
      match severity with
      | .error => errorsRef.modify (·.push msg)
      | .warning => warningsRef.modify (·.push msg)
    errors := errorsRef.get
    warnings := warningsRef.get
  }

/-- A part with a plain-text title. -/
def part (title : String) (content : Array (Verso.Doc.Block Page))
    (subParts : Array (Verso.Doc.Part Page) := #[]) : Verso.Doc.Part Page :=
  Verso.Doc.Part.mk #[Verso.Doc.Inline.text title] title none content subParts

/-- A site whose links cover the cases that URL rewriting distinguishes. -/
def sampleSite : Site :=
  .page `sample
    (part "Sample Content" #[
      Verso.Doc.Block.para #[
        .link #[.text "the guide"] "guide/", .text " ",
        .link #[.text "elsewhere"] "https://lean-lang.org", .text " ",
        .link #[.text "the serving site"] "/", .text " ",
        .link #[.text "mail"] "mailto:nobody@example.com", .text " ",
        .math .inline "x^2"]])
    #[.page "guide" `sample.guide
        (part "The Guide" #[Verso.Doc.Block.para #[.text "Guide text."]]) #[]]

/-- A theme with a stylesheet of its own. -/
def sampleTheme : Theme :=
  { Theme.default with
    cssFiles := #[
      { filename := "sample.css",
        contents := ".sample { color: var(--verso-text-color); }\n" }] }

/-- A theme whose page template carries page chrome. -/
def chromeTheme : Theme :=
  { Theme.default with
    pageTemplate := do
      return {{<html><body><p>"Chrome where a fragment belongs."</p></body></html>}} }

/-- A theme whose page template is replaced, for one path, by one that carries page chrome. -/
def overriddenChromeTheme : Theme :=
  sampleTheme.override #["guide"]
    ⟨(do return {{<html><body><p>"Chrome from an ad hoc template."</p></body></html>}}), id⟩

/-- A site whose title needs an element that a title may not hold. -/
def imageTitleSite : Site :=
  .page `image
    (Verso.Doc.Part.mk #[Verso.Doc.Inline.image "alt" "picture.png"] "A picture" none #[] #[])
    #[]

private def exportOptions : RenderedHtmlOptions where
  generator := { tool := "verso-tests", version := "1", toolchain := "none" }

/--
Exports a site to `dir`, returning the manifest and the errors that were reported.
-/
def exportSite (dir : System.FilePath) (site : Site) (theme : Theme := sampleTheme) :
    IO (Verso.RenderedHtmlContent × Array Verso.LogMessage) := do
  let logger ← quietLogger
  let cfg : Config := {}
  let wrapper := exportOptions.wrapperClass site
  let (site, xref) ← site.traverse cfg {} |>.run logger
  let ctxt : Generate.Context := {
    theme, site,
    ctxt := { path := .root, config := cfg, components := {} },
    xref, dir, config := cfg, header := Html.doctype,
    linkTargets := {}, components := {}
  }
  let (((manifest, _), _)) ←
    Site.writeRenderedHtml dir theme site exportOptions wrapper |>.run ctxt .empty {} |>.run logger
  return (manifest, ← logger.errors)

private def testExport : TestM Unit := do
  IO.FS.withTempDir fun tmp => do
    let first := tmp / "first"
    let second := tmp / "second"
    let (manifest, errors) ← exportSite first sampleSite
    check errors.isEmpty s!"Exporting a site reported errors: {errors.map (·.text)}"
    check (manifest.pages.size == 2) s!"An exported site has 2 pages, got {manifest.pages.size}"
    check (manifest.title == "Sample Content") s!"The exported title is '{manifest.title}'"
    check (manifest.stylesheets[0]!.role == .variables)
      "The variables stylesheet comes first"
    check (manifest.stylesheets.any (·.path.endsWith "verso-vars.css"))
      "An exported directory ships the custom property definitions"
    check (manifest.scripts.any (·.path.endsWith "math.js"))
      "An exported directory ships the math script"

    let some loaded ← (do
      try
        return some (← load first)
      catch e =>
        fail s!"An exported directory did not load: {e}"
        return none)
      | return
    let some rootPage := loaded.manifest.pages[(#[] : Multi.Path)]?
      | fail "An exported directory has no root page"
    let some fragment := rootPage.fragments["content".sluggify]?
      | fail "An exported page has no content fragment"
    let text ← loaded.readFragmentText fragment
    check (mentions text s!"class=\"verso-content content verso-content-")
      s!"A fragment is wrapped: {text}"
    check (mentions text "data-verso-docs=")
      s!"The content fragment names its hover data: {text}"
    check (mentions text s!"href=\"{fragment.rootToken}/guide/\"")
      s!"A site-relative URL becomes relative to the token: {text}"
    check (mentions text "href=\"https://lean-lang.org\"")
      s!"An absolute URL is left alone: {text}"
    check (mentions text "href=\"/\"")
      s!"A root-relative URL is left alone: {text}"
    check (mentions text "href=\"mailto:nobody@example.com\"")
      s!"A URL with a scheme is left alone: {text}"
    check (!mentions text "<html") "A fragment carries no page chrome"
    check (!mentions text "<body") "A fragment carries no page chrome"
    check (!mentions text "<base") "A fragment carries no page chrome"
    check (← (staticDir first / "-verso-data" / "verso-vars.css").pathExists)
      "An exported directory ships the file its manifest names"
    check (← (staticDir first / "-verso-docs.json").pathExists)
      "An exported directory ships its hover data"

    let _ ← exportSite second sampleSite
    let firstBytes ← IO.FS.readBinFile (manifestFile first)
    let secondBytes ← IO.FS.readBinFile (manifestFile second)
    check (firstBytes == secondBytes)
      "Exporting unchanged content twice produces an identical manifest"

private def testChromeIsRejected : TestM Unit := do
  IO.FS.withTempDir fun tmp => do
    let dir := tmp / "chrome"
    let (_, errors) ← exportSite dir sampleSite chromeTheme
    check (errors.any (mentions ·.text "page chrome"))
      s!"A theme whose page template carries chrome is reported: {errors.map (·.text)}"

private def testAdHocChromeIsRejected : TestM Unit := do
  IO.FS.withTempDir fun tmp => do
    let dir := tmp / "adhoc"
    let (_, errors) ← exportSite dir sampleSite overriddenChromeTheme
    check (errors.any fun e => mentions e.text "page chrome" && mentions e.text "guide")
      s!"Chrome from a replaced page template is reported: {errors.map (·.text)}"

private def testAssetOrderIsStable : TestM Unit := do
  let two := Template.hashNamedCss "component" (Std.HashSet.ofList [".a {}", ".b {}"])
  let three := Template.hashNamedCss "component" (Std.HashSet.ofList [".a {}", ".b {}", ".c {}"])
  check (two.size == 2 && three.size == 3) "Naming assets by a hash of their contents keeps them all"
  let kept := three.filter fun css => two.any (·.filename == css.filename)
  check (kept.map (·.filename) == two.map (·.filename))
    s!"Adding an asset leaves the order of the others unchanged: {two.map (·.filename)} then {kept.map (·.filename)}"

/-- The URLs that rewriting distinguishes, and what the export makes of each. -/
private def urlTable : List (String × String) := [
  ("/x", "/x"),
  ("./x", "TOKEN/./x"),
  ("../x", "TOKEN/../x"),
  ("-verso-data/x", "TOKEN/-verso-data/x"),
  ("guide/", "TOKEN/guide/"),
  ("#frag", "#frag"),
  ("https://x", "https://x"),
  ("//cdn/x", "//cdn/x"),
  ("mailto:x", "mailto:x"),
  ("", "")
]

private def testUrlTable : TestM Unit := do
  for (url, expected) in urlTable do
    let actual := RenderedHtml.relocateUrl "TOKEN" url
    check (actual == expected) s!"Rewriting '{url}': expected '{expected}', got '{actual}'"

  -- The walk itself leaves `<base>` and remote content alone.
  let doc : Html := {{
    <div>
      <base href="/root/"/>
      <a href="/remote/x" data-verso-remote="true">"remote"</a>
      <a href="x" title="/not-a-url">"here"</a>
    </div>
  }}
  let rewritten := (doc.rewriteUrls ("[" ++ · ++ "]")).asString
  check ((rewritten.find? "<base href=\"/root/\">").isSome)
    s!"A base element keeps its own URL: {rewritten}"
  check ((rewritten.find? "href=\"/remote/x\"").isSome)
    s!"An element carrying data-verso-remote keeps its own URL: {rewritten}"
  check ((rewritten.find? "href=\"[x]\"").isSome)
    s!"Every other URL-valued attribute is rewritten: {rewritten}"
  check ((rewritten.find? "title=\"/not-a-url\"").isSome)
    s!"An attribute that holds no URL is left alone: {rewritten}"

private def testTitleIsChecked : TestM Unit := do
  IO.FS.withTempDir fun tmp => do
    let dir := tmp / "title"
    let (_, errors) ← exportSite dir imageTitleSite
    check (errors.any (mentions ·.text "title"))
      s!"A title that needs more than inline markup is reported: {errors.map (·.text)}"

/--
Runs the rendered HTML content export tests, returning the number of failures.
-/
def runRenderedHtmlExportTests : IO Nat := do
  let ((), failures) ←
    (do
      testExport
      testChromeIsRejected
      testAdHocChromeIsRejected
      testAssetOrderIsStable
      testUrlTable
      testTitleIsChecked : TestM Unit).run 0
  return failures

end Tests.RenderedHtmlExport
