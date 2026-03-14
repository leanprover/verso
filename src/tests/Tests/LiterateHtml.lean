/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoLiterate

set_option maxRecDepth 1024

namespace Tests.LiterateHtml

private def hasSubstring (s : String) (sub : String) : Bool :=
  s.find? sub |>.isSome

private def cleanDir (dir : System.FilePath) : IO Unit := do
  if ← dir.pathExists then
    IO.FS.removeDirAll dir
  IO.FS.createDirAll dir

/-- Runs a Lake executable via `lake exe`. Throws on non-zero exit. -/
private def runLakeExe (name : String) (args : Array String) : IO Unit := do
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["--quiet", "exe", name] ++ args
    stdout := .null
    stderr := .inherit
  }
  let exitCode ← child.wait
  if exitCode != 0 then
    throw <| IO.userError s!"{name} failed with exit code {exitCode}"

/-- Generate a module-map file from a JSON directory.
    Each .json file at `<jsonDir>/<A>/<B>.json` produces a line `A.B\t<path>`. -/
private def generateModuleMap (jsonDir mapFile : System.FilePath) : IO Unit := do
  let mut lines : Array String := #[]
  let mut todo := [(jsonDir, "")]
  repeat
    match todo with
    | [] => break
    | (dir, pfx) :: rest =>
      todo := rest
      for entry in ← dir.readDir do
        if ← entry.path.isDir then
          let component := entry.fileName
          let newPfx := if pfx.isEmpty then component else s!"{pfx}.{component}"
          todo := (entry.path, newPfx) :: todo
        else if entry.path.extension == some "json" then
          let stem := entry.path.fileStem.getD ""
          let modName := if pfx.isEmpty then stem else s!"{pfx}.{stem}"
          lines := lines.push s!"{modName}\t{entry.path}"
  IO.FS.writeFile mapFile ("\n".intercalate lines.toList ++ "\n")

/-- Runs verso-literate-html with a module-map generated from a JSON directory. -/
private def runLiterateHtml (jsonDir htmlDir : System.FilePath) (planFile configFile : Option System.FilePath := none) : IO Unit := do
  -- If plan file is provided, filter the module map to only planned modules
  let mapFile := htmlDir.addExtension "module-map"
  if let some pf := planFile then
    -- Generate full map, then filter by plan
    let fullMapFile := htmlDir.addExtension "full-module-map"
    generateModuleMap jsonDir fullMapFile
    let fullContents ← IO.FS.readFile fullMapFile
    let planContents ← IO.FS.readFile pf
    let planNames := planContents.splitOn "\n" |>.filter (!·.isEmpty)
    let filteredLines := fullContents.splitOn "\n" |>.filter fun line =>
      if line.isEmpty then false
      else match line.splitOn "\t" with
        | [name, _] => planNames.contains name
        | _ => false
    IO.FS.writeFile mapFile ("\n".intercalate filteredLines ++ "\n")
  else
    generateModuleMap jsonDir mapFile
  let mut args := #[htmlDir.toString, mapFile.toString]
  if let some cf := configFile then
    args := args.push cf.toString
  runLakeExe "verso-literate-html" args

/-- Runs verso-literate-plan to produce a plan file. -/
private def runLiteratePlan (moduleListFile planFile : System.FilePath) (tomlFile : Option System.FilePath := none) : IO Unit := do
  let mut args := #[moduleListFile.toString, planFile.toString]
  if let some tf := tomlFile then
    args := args ++ #[tf.toString]
  runLakeExe "verso-literate-plan" args

/-- Runs a Lake executable capturing stdout and stderr, returning (exitCode, stdout, stderr). -/
private def runLakeExeCapture (name : String) (args : Array String) : IO (UInt32 × String × String) := do
  let result ← IO.Process.output {
    cmd := "lake"
    args := #["--quiet", "exe", name] ++ args
  }
  return (result.exitCode, result.stdout, result.stderr)

/-- Runs verso-literate-plan capturing output, returning (exitCode, stdout, stderr). -/
private def runLiteratePlanCapture (moduleListFile planFile : System.FilePath) (tomlFile : Option System.FilePath := none) : IO (UInt32 × String × String) := do
  let mut args := #[moduleListFile.toString, planFile.toString]
  if let some tf := tomlFile then
    args := args ++ #[tf.toString]
  runLakeExeCapture "verso-literate-plan" args

/-- Runs verso-literate-html capturing output, returning (exitCode, stdout, stderr). -/
private def runLiterateHtmlCapture (jsonDir htmlDir : System.FilePath) (planFile configFile : Option System.FilePath := none) : IO (UInt32 × String × String) := do
  let mapFile := htmlDir.addExtension "module-map"
  if let some pf := planFile then
    let fullMapFile := htmlDir.addExtension "full-module-map"
    generateModuleMap jsonDir fullMapFile
    let fullContents ← IO.FS.readFile fullMapFile
    let planContents ← IO.FS.readFile pf
    let planNames := planContents.splitOn "\n" |>.filter (!·.isEmpty)
    let filteredLines := fullContents.splitOn "\n" |>.filter fun line =>
      if line.isEmpty then false
      else match line.splitOn "\t" with
        | [name, _] => planNames.contains name
        | _ => false
    IO.FS.writeFile mapFile ("\n".intercalate filteredLines ++ "\n")
  else
    generateModuleMap jsonDir mapFile
  let mut args := #[htmlDir.toString, mapFile.toString]
  if let some cf := configFile then
    args := args.push cf.toString
  runLakeExeCapture "verso-literate-html" args

/-- Shared test data: pre-built JSON directory and module list file. -/
structure TestData where
  jsonDir : System.FilePath
  modules : Array String
  moduleListFile : System.FilePath

/-- Run a test in an independent temporary directory. The callback receives
    the shared JSON dir, a fresh HTML output dir, and paths for plan/toml files. -/
private def withTestDir (data : TestData)
    (test : System.FilePath → System.FilePath → System.FilePath → System.FilePath → IO Unit) : IO Unit :=
  IO.FS.withTempDir fun tmpDir => do
    let htmlDir := tmpDir / "html"
    let planFile := tmpDir / "plan"
    let tomlFile := tmpDir / "literate.toml"
    IO.FS.createDirAll htmlDir
    test data.jsonDir htmlDir planFile tomlFile

-- ===== Individual tests =====

/-- All modules produce HTML files with expected structure, navigation, and content. -/
private def testDefaultBehavior (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ _ => do
  runLiterateHtml jsonDir htmlDir

  let expectedFiles := #[
    htmlDir / "LitConfig" / "index.html",
    htmlDir / "LitConfig" / "Core" / "index.html",
    htmlDir / "LitConfig" / "Core" / "Basic" / "index.html",
    htmlDir / "LitConfig" / "NoDocstrings" / "index.html",
    htmlDir / "index.html"
  ]
  for f in expectedFiles do
    unless ← f.pathExists do
      throw <| IO.userError s!"Expected HTML file not found: {f}"

  let landingHtml ← IO.FS.readFile (htmlDir / "index.html")
  unless hasSubstring landingHtml "LitConfig" do
    throw <| IO.userError "Landing page does not contain 'LitConfig'"

  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  unless hasSubstring litConfigHtml "<title>LitConfig</title>" do
    throw <| IO.userError "LitConfig page title is not 'LitConfig'"
  unless hasSubstring litConfigHtml "A Test Module" do
    throw <| IO.userError "LitConfig page does not contain module docstring content 'A Test Module'"
  unless hasSubstring litConfigHtml "code-box" do
    throw <| IO.userError "LitConfig page does not contain any code boxes"
  unless hasSubstring litConfigHtml "module-tree" do
    throw <| IO.userError "LitConfig page does not contain module tree navigation"
  unless hasSubstring litConfigHtml "breadcrumbs" do
    throw <| IO.userError "LitConfig page does not contain breadcrumbs"

  let coreHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "Core" / "index.html")
  unless hasSubstring coreHtml "Core Module" do
    throw <| IO.userError "Core page does not contain module docstring content 'Core Module'"

  let noDocHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "NoDocstrings" / "index.html")
  unless hasSubstring noDocHtml "code-box" do
    throw <| IO.userError "NoDocstrings page does not contain code boxes"

/-- Excluded modules produce no HTML output and are absent from the navbar. -/
private def testExclude (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir planFile tomlFile => do
  IO.FS.writeFile tomlFile "exclude = [\"LitConfig.NoDocstrings\"]\n"
  runLiteratePlan data.moduleListFile planFile (some tomlFile)
  runLiterateHtml jsonDir htmlDir (some planFile) (some tomlFile)

  if ← (htmlDir / "LitConfig" / "NoDocstrings" / "index.html").pathExists then
    throw <| IO.userError "Excluded module LitConfig.NoDocstrings should not have HTML output"
  unless ← (htmlDir / "LitConfig" / "index.html").pathExists do
    throw <| IO.userError "LitConfig should still have HTML output after exclude"
  unless ← (htmlDir / "LitConfig" / "Core" / "index.html").pathExists do
    throw <| IO.userError "LitConfig.Core should still have HTML output after exclude"
  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  let navbarSection := litConfigHtml.splitOn "module-tree" |>.getD 1 "" |>.splitOn "</nav>" |>.head!
  if hasSubstring navbarSection "NoDocstrings" then
    throw <| IO.userError "Navbar should not contain excluded module 'NoDocstrings'"

/-- The `order` config controls the ordering of modules in the navbar. -/
private def testNavbarOrder (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir planFile tomlFile => do
  IO.FS.writeFile tomlFile "order = [\"LitConfig.NoDocstrings\", \"LitConfig.Core\"]\n"
  runLiteratePlan data.moduleListFile planFile (some tomlFile)
  runLiterateHtml jsonDir htmlDir (some planFile) (some tomlFile)

  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  let navbarSection := litConfigHtml.splitOn "module-tree" |>.getD 1 "" |>.splitOn "</nav>" |>.head!
  let noDocPos := navbarSection.splitOn "NoDocstrings" |>.head! |>.length
  let corePos := navbarSection.splitOn ">Core<" |>.head! |>.length
  unless noDocPos < corePos do
    throw <| IO.userError s!"NoDocstrings (pos {noDocPos}) should appear before Core (pos {corePos}) in navbar"

/-- A configured landing page module's content replaces the default table of contents. -/
private def testLandingPage (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir planFile tomlFile => do
  IO.FS.writeFile tomlFile "landing_page = \"LitConfig.Core\"\n"
  runLiteratePlan data.moduleListFile planFile (some tomlFile)
  runLiterateHtml jsonDir htmlDir (some planFile) (some tomlFile)

  let landingHtml ← IO.FS.readFile (htmlDir / "index.html")
  unless hasSubstring landingHtml "Core Module" do
    throw <| IO.userError "Landing page should contain 'Core Module' content from the configured landing module"
  unless ← (htmlDir / "LitConfig" / "Core" / "index.html").pathExists do
    throw <| IO.userError "Core module should still exist at its normal location"

/-- Excluding a parent module also removes all its children from the output. -/
private def testRecursiveExclusion (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir planFile tomlFile => do
  IO.FS.writeFile tomlFile "exclude = [\"LitConfig.Core\"]\n"
  runLiteratePlan data.moduleListFile planFile (some tomlFile)
  runLiterateHtml jsonDir htmlDir (some planFile) (some tomlFile)

  if ← (htmlDir / "LitConfig" / "Core" / "index.html").pathExists then
    throw <| IO.userError "Excluded module LitConfig.Core should not have HTML output"
  if ← (htmlDir / "LitConfig" / "Core" / "Basic" / "index.html").pathExists then
    throw <| IO.userError "Child of excluded module LitConfig.Core.Basic should not have HTML output"
  unless ← (htmlDir / "LitConfig" / "index.html").pathExists do
    throw <| IO.userError "LitConfig should still have HTML output after excluding Core"
  unless ← (htmlDir / "LitConfig" / "NoDocstrings" / "index.html").pathExists do
    throw <| IO.userError "LitConfig.NoDocstrings should still have HTML output after excluding Core"

/-- The `order_children` config controls the ordering of children under a specific parent. -/
private def testOrderChildren (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir planFile tomlFile => do
  IO.FS.writeFile tomlFile "[order_children]\n\"LitConfig\" = [\"LitConfig.NoDocstrings\", \"LitConfig.Core\"]\n"
  runLiteratePlan data.moduleListFile planFile (some tomlFile)
  runLiterateHtml jsonDir htmlDir (some planFile) (some tomlFile)

  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  let navbarSection := litConfigHtml.splitOn "module-tree" |>.getD 1 "" |>.splitOn "</nav>" |>.head!
  let noDocPos := navbarSection.splitOn "NoDocstrings" |>.head! |>.length
  let corePos := navbarSection.splitOn ">Core<" |>.head! |>.length
  unless noDocPos < corePos do
    throw <| IO.userError s!"order_children: NoDocstrings (pos {noDocPos}) should appear before Core (pos {corePos}) in navbar"

/-- A non-empty `xref.json` cross-reference file is generated in the output. -/
private def testXrefJsonGenerated (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ _ => do
  runLiterateHtml jsonDir htmlDir
  unless ← (htmlDir / "xref.json").pathExists do
    throw <| IO.userError "xref.json was not generated"
  let xrefContent ← IO.FS.readFile (htmlDir / "xref.json")
  unless xrefContent.trimAscii.toString.length > 2 do
    throw <| IO.userError "xref.json is empty or trivial"

/-- The plan file lists all modules by default and respects exclusions. -/
private def testPlanFileContent (data : TestData) : IO Unit := IO.FS.withTempDir fun tmpDir => do
  let planFile := tmpDir / "plan"
  let tomlFile := tmpDir / "literate.toml"
  -- No config: plan should contain all modules
  runLiteratePlan data.moduleListFile planFile
  let planContent ← IO.FS.readFile planFile
  let planModules := planContent.splitOn "\n" |>.filter (!·.isEmpty)
  for mod in data.modules do
    unless planModules.contains mod do
      throw <| IO.userError s!"Plan file should contain module '{mod}' but doesn't"
  -- With exclusion: excluded modules should be absent from plan
  IO.FS.writeFile tomlFile "exclude = [\"LitConfig.Core\"]\n"
  runLiteratePlan data.moduleListFile planFile (some tomlFile)
  let planContent ← IO.FS.readFile planFile
  let planModules := planContent.splitOn "\n" |>.filter (!·.isEmpty)
  if planModules.contains "LitConfig.Core" then
    throw <| IO.userError "Plan file should not contain excluded module 'LitConfig.Core'"
  if planModules.contains "LitConfig.Core.Basic" then
    throw <| IO.userError "Plan file should not contain child of excluded module 'LitConfig.Core.Basic'"
  unless planModules.contains "LitConfig" do
    throw <| IO.userError "Plan file should still contain 'LitConfig' after excluding Core"

/-- Target filtering restricts the plan to only the specified module and its children. -/
private def testTargetsFiltering (data : TestData) : IO Unit := IO.FS.withTempDir fun tmpDir => do
  let planFile := tmpDir / "plan"
  let tomlFile := tmpDir / "literate.toml"
  IO.FS.writeFile tomlFile "[[targets]]\nmodule = \"LitConfig.Core\"\n"
  runLiteratePlan data.moduleListFile planFile (some tomlFile)
  let planContent ← IO.FS.readFile planFile
  let planModules := planContent.splitOn "\n" |>.filter (!·.isEmpty)
  unless planModules.contains "LitConfig.Core" do
    throw <| IO.userError "Plan with target LitConfig.Core should contain LitConfig.Core"
  unless planModules.contains "LitConfig.Core.Basic" do
    throw <| IO.userError "Plan with target LitConfig.Core should contain child LitConfig.Core.Basic"
  if planModules.contains "LitConfig.NoDocstrings" then
    throw <| IO.userError "Plan with target LitConfig.Core should not contain LitConfig.NoDocstrings"

/-- Library-level target filtering includes all modules belonging to that library. -/
private def testTargetsLibrary (data : TestData) : IO Unit := IO.FS.withTempDir fun tmpDir => do
  let planFile := tmpDir / "plan"
  let tomlFile := tmpDir / "literate.toml"
  IO.FS.writeFile tomlFile "[[targets]]\nlibrary = \"LitConfig\"\n"
  runLiteratePlan data.moduleListFile planFile (some tomlFile)
  let planContent ← IO.FS.readFile planFile
  let planModules := planContent.splitOn "\n" |>.filter (!·.isEmpty)
  -- All modules in the LitConfig library should be included
  unless planModules.contains "LitConfig" do
    throw <| IO.userError "Library target should include LitConfig"
  unless planModules.contains "LitConfig.Core" do
    throw <| IO.userError "Library target should include LitConfig.Core"
  unless planModules.contains "LitConfig.Core.Basic" do
    throw <| IO.userError "Library target should include LitConfig.Core.Basic"
  unless planModules.contains "LitConfig.NoDocstrings" do
    throw <| IO.userError "Library target should include LitConfig.NoDocstrings"

/-- Library-level target filtering with a non-matching library produces an empty set. -/
private def testTargetsLibraryNonexistent (data : TestData) : IO Unit := IO.FS.withTempDir fun tmpDir => do
  let planFile := tmpDir / "plan"
  let tomlFile := tmpDir / "literate.toml"
  IO.FS.writeFile tomlFile "[[targets]]\nlibrary = \"NonexistentLib\"\n"
  let (exitCode, _, _) ← runLiteratePlanCapture data.moduleListFile planFile (some tomlFile)
  unless exitCode != 0 do
    throw <| IO.userError "Library target with nonexistent library should fail"

/-- Combined library + module target filters to modules that match both constraints. -/
private def testTargetsLibraryAndModule (data : TestData) : IO Unit := IO.FS.withTempDir fun tmpDir => do
  let planFile := tmpDir / "plan"
  let tomlFile := tmpDir / "literate.toml"
  IO.FS.writeFile tomlFile "[[targets]]\nlibrary = \"LitConfig\"\nmodule = \"LitConfig.Core\"\n"
  runLiteratePlan data.moduleListFile planFile (some tomlFile)
  let planContent ← IO.FS.readFile planFile
  let planModules := planContent.splitOn "\n" |>.filter (!·.isEmpty)
  unless planModules.contains "LitConfig.Core" do
    throw <| IO.userError "Library+module target should include LitConfig.Core"
  unless planModules.contains "LitConfig.Core.Basic" do
    throw <| IO.userError "Library+module target should include LitConfig.Core.Basic"
  if planModules.contains "LitConfig.NoDocstrings" then
    throw <| IO.userError "Library+module target should not include LitConfig.NoDocstrings"

/-- Commands listed in `hide_commands` produce no output while other commands remain visible. -/
private def testHideCommands (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ tomlFile => do
  IO.FS.writeFile tomlFile "hide_commands = [\"set_option\"]\n"
  runLiterateHtml jsonDir htmlDir (configFile := some tomlFile)

  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  if hasSubstring litConfigHtml "set_option" then
    throw <| IO.userError "hide_commands: LitConfig page should not contain 'set_option' text"
  unless hasSubstring litConfigHtml "hello" do
    throw <| IO.userError "hide_commands: LitConfig page should still contain 'hello'"

/-- The metadata title appears in the landing page and module page `<title>` tags. -/
private def testMetadataTitle (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ tomlFile => do
  IO.FS.writeFile tomlFile "[metadata]\ntitle = \"Test Site\"\n"
  runLiterateHtml jsonDir htmlDir (configFile := some tomlFile)

  let landingHtml ← IO.FS.readFile (htmlDir / "index.html")
  unless hasSubstring landingHtml "<title>Test Site</title>" do
    throw <| IO.userError "metadata title: landing page <title> should contain 'Test Site'"
  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  unless hasSubstring litConfigHtml "LitConfig" do
    throw <| IO.userError "metadata title: module page should still contain module name 'LitConfig'"
  unless hasSubstring litConfigHtml "Test Site" do
    throw <| IO.userError "metadata title: module page title should contain 'Test Site'"

/-- Extra CSS files are copied to the output directory and linked in the HTML head. -/
private def testExtraCss (data : TestData) : IO Unit := IO.FS.withTempDir fun tmpDir => do
  let htmlDir := tmpDir / "html"
  let tomlFile := tmpDir / "literate.toml"
  IO.FS.createDirAll htmlDir
  let extraCssFile := tmpDir / "custom-test.css"
  IO.FS.writeFile extraCssFile "body { background: red; }\n"
  IO.FS.writeFile tomlFile s!"extra_css = [\"{extraCssFile}\"]\n"
  runLiterateHtml data.jsonDir htmlDir (configFile := some tomlFile)

  unless ← (htmlDir / "custom-test.css").pathExists do
    throw <| IO.userError "extra CSS: custom-test.css was not copied to output"
  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  unless hasSubstring litConfigHtml "custom-test.css" do
    throw <| IO.userError "extra CSS: HTML does not reference custom-test.css"

/-- Declaration docstrings are hidden globally while module docstrings remain visible. -/
private def testShowDocstringsFalse (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ tomlFile => do
  IO.FS.writeFile tomlFile "show_docstrings = false\n"
  runLiterateHtml jsonDir htmlDir (configFile := some tomlFile)

  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  if hasSubstring litConfigHtml "A greeting message" then
    throw <| IO.userError "show_docstrings=false: declaration docstring 'A greeting message' should be hidden"
  unless hasSubstring litConfigHtml "A Test Module" do
    throw <| IO.userError "show_docstrings=false: module docstring 'A Test Module' should still appear"

/-- `show_imports = false` hides the imports list. -/
private def testShowImportsFalse (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ tomlFile => do
  IO.FS.writeFile tomlFile "show_imports = false\n"
  runLiterateHtml jsonDir htmlDir (configFile := some tomlFile)

  let coreHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "Core" / "index.html")
  if hasSubstring coreHtml "imports-list" then
    throw <| IO.userError "show_imports=false: page should not contain 'imports-list'"

/-- Default config renders successfully (imports list depends on test data having populated import defines). -/
private def testShowImportsDefault (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ _ => do
  runLiterateHtml jsonDir htmlDir

  -- Verify the page renders without errors
  let coreHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "Core" / "index.html")
  unless hasSubstring coreHtml "code-box" do
    throw <| IO.userError "show_imports default: Core page should contain code boxes"

/-- Default config renders output blocks for #eval commands. -/
private def testShowOutput (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ _ => do
  runLiterateHtml jsonDir htmlDir

  let coreHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "Core" / "index.html")
  -- Check for an actual lean-output element (class on a <pre> tag), not just the CSS rules
  unless hasSubstring coreHtml "class=\"hl lean lean-output" do
    throw <| IO.userError "show_output default: Core page should contain output block elements for #eval commands"

/-- `show_output = []` suppresses all output blocks. -/
private def testShowOutputEmpty (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ tomlFile => do
  IO.FS.writeFile tomlFile "show_output = []\n"
  runLiterateHtml jsonDir htmlDir (configFile := some tomlFile)

  let coreHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "Core" / "index.html")
  -- Check that no actual lean-output elements exist (CSS rules in `<style>` don't count)
  if hasSubstring coreHtml "class=\"hl lean lean-output" then
    throw <| IO.userError "show_output=[]: Core page should not contain output block elements"

/-- Docstrings are hidden for specific named declarations while other content remains. -/
private def testHideDocstringsFor (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ tomlFile => do
  IO.FS.writeFile tomlFile "hide_docstrings_for = [\"hello\"]\n"
  runLiterateHtml jsonDir htmlDir (configFile := some tomlFile)

  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  if hasSubstring litConfigHtml "A greeting message" then
    throw <| IO.userError "hide_docstrings_for: 'A greeting message' should be hidden for 'hello'"
  unless hasSubstring litConfigHtml "A Test Module" do
    throw <| IO.userError "hide_docstrings_for: module docstring 'A Test Module' should still appear"

/-- Favicon is copied to the output directory and linked in the HTML. -/
private def testFavicon (data : TestData) : IO Unit := IO.FS.withTempDir fun tmpDir => do
  let htmlDir := tmpDir / "html"
  let tomlFile := tmpDir / "literate.toml"
  IO.FS.createDirAll htmlDir
  let faviconFile := tmpDir / "test-favicon.png"
  IO.FS.writeFile faviconFile "fake-png-data"
  IO.FS.writeFile tomlFile s!"[metadata]\nfavicon = \"{faviconFile}\"\n"
  runLiterateHtml data.jsonDir htmlDir (configFile := some tomlFile)

  unless ← (htmlDir / "test-favicon.png").pathExists do
    throw <| IO.userError "favicon: test-favicon.png was not copied to output"
  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  unless hasSubstring litConfigHtml "test-favicon.png" do
    throw <| IO.userError "favicon: HTML does not reference test-favicon.png"

/-- Extra JS files are copied to the output directory and linked in the HTML. -/
private def testExtraJs (data : TestData) : IO Unit := IO.FS.withTempDir fun tmpDir => do
  let htmlDir := tmpDir / "html"
  let tomlFile := tmpDir / "literate.toml"
  IO.FS.createDirAll htmlDir
  let extraJsFile := tmpDir / "custom-test.js"
  IO.FS.writeFile extraJsFile "console.log('test');\n"
  IO.FS.writeFile tomlFile s!"extra_js = [\"{extraJsFile}\"]\n"
  runLiterateHtml data.jsonDir htmlDir (configFile := some tomlFile)

  unless ← (htmlDir / "custom-test.js").pathExists do
    throw <| IO.userError "extra JS: custom-test.js was not copied to output"
  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  unless hasSubstring litConfigHtml "custom-test.js" do
    throw <| IO.userError "extra JS: HTML does not reference custom-test.js"

/-- Targets + exclude: exclusion narrows the target set. -/
private def testTargetsPlusExclude (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir planFile tomlFile => do
  IO.FS.writeFile tomlFile "exclude = [\"LitConfig.Core.Basic\"]\n\n[[targets]]\nmodule = \"LitConfig.Core\"\n"
  runLiteratePlan data.moduleListFile planFile (some tomlFile)
  runLiterateHtml jsonDir htmlDir (some planFile) (some tomlFile)

  unless ← (htmlDir / "LitConfig" / "Core" / "index.html").pathExists do
    throw <| IO.userError "targets+exclude: LitConfig.Core should exist"
  if ← (htmlDir / "LitConfig" / "Core" / "Basic" / "index.html").pathExists then
    throw <| IO.userError "targets+exclude: LitConfig.Core.Basic should be excluded"
  if ← (htmlDir / "LitConfig" / "NoDocstrings" / "index.html").pathExists then
    throw <| IO.userError "targets+exclude: LitConfig.NoDocstrings should not be in targets"

/-- show_docstrings = false with show_docstrings_for exceptions still shows the excepted docstring. -/
private def testShowDocstringsForExceptions (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ tomlFile => do
  IO.FS.writeFile tomlFile "show_docstrings = false\nshow_docstrings_for = [\"hello\"]\n"
  runLiterateHtml jsonDir htmlDir (configFile := some tomlFile)

  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  unless hasSubstring litConfigHtml "A greeting message" do
    throw <| IO.userError "show_docstrings_for exception: 'A greeting message' should be visible for 'hello'"
  -- Other declaration docstrings should be hidden (e.g., in Core module)
  let coreHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "Core" / "index.html")
  if hasSubstring coreHtml "Doubles a natural number" then
    throw <| IO.userError "show_docstrings_for exception: 'Doubles a natural number' should be hidden"

/-- Metadata description appears as a meta tag in the HTML. -/
private def testMetadataDescription (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ tomlFile => do
  IO.FS.writeFile tomlFile "[metadata]\ndescription = \"A test description\"\n"
  runLiterateHtml jsonDir htmlDir (configFile := some tomlFile)

  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  unless hasSubstring litConfigHtml "A test description" do
    throw <| IO.userError "metadata description: HTML should contain 'A test description'"
  unless hasSubstring litConfigHtml "meta" do
    throw <| IO.userError "metadata description: HTML should contain a meta tag"

/-- The current page is highlighted in the navbar with the 'current' class. -/
private def testCurrentPageHighlighting (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ _ => do
  runLiterateHtml jsonDir htmlDir

  let coreHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "Core" / "index.html")
  let navbarSection := coreHtml.splitOn "module-tree" |>.getD 1 "" |>.splitOn "</nav>" |>.head!
  -- The Core entry should have a 'current' class
  unless hasSubstring navbarSection "current" do
    throw <| IO.userError "current page highlighting: navbar should contain 'current' class"

/-- Plan with targets + exclude combined produces the correct reduced module set. -/
private def testPlanTargetsPlusExclude (data : TestData) : IO Unit := IO.FS.withTempDir fun tmpDir => do
  let planFile := tmpDir / "plan"
  let tomlFile := tmpDir / "literate.toml"
  IO.FS.writeFile tomlFile "exclude = [\"LitConfig.Core.Basic\"]\n\n[[targets]]\nmodule = \"LitConfig.Core\"\n"
  runLiteratePlan data.moduleListFile planFile (some tomlFile)
  let planContent ← IO.FS.readFile planFile
  let planModules := planContent.splitOn "\n" |>.filter (!·.isEmpty)
  unless planModules.contains "LitConfig.Core" do
    throw <| IO.userError "plan targets+exclude: should contain LitConfig.Core"
  if planModules.contains "LitConfig.Core.Basic" then
    throw <| IO.userError "plan targets+exclude: should not contain excluded LitConfig.Core.Basic"
  if planModules.contains "LitConfig" then
    throw <| IO.userError "plan targets+exclude: should not contain LitConfig (not in targets)"

/-- Plan fails with error when landing_page names a module not in the included set. -/
private def testPlanLandingPageNotInSet (data : TestData) : IO Unit := IO.FS.withTempDir fun tmpDir => do
  let planFile := tmpDir / "plan"
  let tomlFile := tmpDir / "literate.toml"
  IO.FS.writeFile tomlFile "landing_page = \"NonExistent.Module\"\n"
  let (exitCode, _, stderr) ← runLiteratePlanCapture data.moduleListFile planFile (some tomlFile)
  if exitCode == 0 then
    throw <| IO.userError "plan landing_page validation: should have failed with non-zero exit code"
  unless hasSubstring stderr "landing_page" do
    throw <| IO.userError "plan landing_page validation: stderr should mention 'landing_page'"

/-- Plan fails with error when all modules are excluded (empty module set). -/
private def testPlanEmptyModuleSet (data : TestData) : IO Unit := IO.FS.withTempDir fun tmpDir => do
  let planFile := tmpDir / "plan"
  let tomlFile := tmpDir / "literate.toml"
  IO.FS.writeFile tomlFile "exclude = [\"LitConfig\"]\n"
  let (exitCode, _, stderr) ← runLiteratePlanCapture data.moduleListFile planFile (some tomlFile)
  if exitCode == 0 then
    throw <| IO.userError "plan empty module set: should have failed with non-zero exit code"
  unless hasSubstring stderr "no modules" do
    throw <| IO.userError "plan empty module set: stderr should mention 'no modules'"

/-- Plan succeeds with a warning when an ordered module does not exist. -/
private def testPlanOrderWarning (data : TestData) : IO Unit := IO.FS.withTempDir fun tmpDir => do
  let planFile := tmpDir / "plan"
  let tomlFile := tmpDir / "literate.toml"
  IO.FS.writeFile tomlFile "order = [\"NonExistent.Module\"]\n"
  let (exitCode, _, stderr) ← runLiteratePlanCapture data.moduleListFile planFile (some tomlFile)
  if exitCode != 0 then
    throw <| IO.userError "plan order warning: should succeed (warning only, not error)"
  unless hasSubstring stderr "Warning" do
    throw <| IO.userError "plan order warning: stderr should contain a warning"
  unless hasSubstring stderr "NonExistent.Module" do
    throw <| IO.userError "plan order warning: stderr should mention 'NonExistent.Module'"

/-- HTML generation fails when hide_docstrings_for names a nonexistent declaration. -/
private def testHtmlInvalidDocstringFor (data : TestData) : IO Unit := IO.FS.withTempDir fun tmpDir => do
  let htmlDir := tmpDir / "html"
  let tomlFile := tmpDir / "literate.toml"
  IO.FS.createDirAll htmlDir
  IO.FS.writeFile tomlFile "hide_docstrings_for = [\"nonexistent_decl\"]\n"
  let (exitCode, _, stderr) ← runLiterateHtmlCapture data.jsonDir htmlDir (configFile := some tomlFile)
  if exitCode == 0 then
    throw <| IO.userError "HTML invalid docstring_for: should have failed with non-zero exit code"
  unless hasSubstring stderr "nonexistent_decl" do
    throw <| IO.userError "HTML invalid docstring_for: stderr should mention 'nonexistent_decl'"

/-- Theme CSS file is generated and linked when theme overrides are present. -/
private def testThemeCss (data : TestData) : IO Unit := IO.FS.withTempDir fun tmpDir => do
  let htmlDir := tmpDir / "html"
  let tomlFile := tmpDir / "literate.toml"
  IO.FS.createDirAll htmlDir
  IO.FS.writeFile tomlFile (String.intercalate "\n" [
    "[theme]",
    "code_box_background_color = \"#f0f0f0\"",
    "text_color = \"#222\"",
    "",
    "[theme.dark]",
    "text_color = \"#ddd\"",
    ""
  ])
  runLiterateHtml data.jsonDir htmlDir (configFile := some tomlFile)

  unless ← (htmlDir / "literate-theme.css").pathExists do
    throw <| IO.userError "theme: literate-theme.css was not generated"
  let themeCss ← IO.FS.readFile (htmlDir / "literate-theme.css")
  unless hasSubstring themeCss "--verso-code-box-background-color" do
    throw <| IO.userError "theme: literate-theme.css does not contain code box variable"
  unless hasSubstring themeCss "#f0f0f0" do
    throw <| IO.userError "theme: literate-theme.css does not contain light value"
  unless hasSubstring themeCss "prefers-color-scheme: dark" do
    throw <| IO.userError "theme: literate-theme.css does not contain dark media query"
  unless hasSubstring themeCss "#ddd" do
    throw <| IO.userError "theme: literate-theme.css does not contain dark value"
  unless hasSubstring themeCss "data-theme" do
    throw <| IO.userError "theme: literate-theme.css does not contain data-theme selector"
  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  unless hasSubstring litConfigHtml "literate-theme.css" do
    throw <| IO.userError "theme: HTML does not link literate-theme.css"

/-- No theme CSS file is generated when theme is empty. -/
private def testThemeCssEmpty (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ _ => do
  runLiterateHtml jsonDir htmlDir
  if ← (htmlDir / "literate-theme.css").pathExists then
    throw <| IO.userError "theme empty: literate-theme.css should not exist with default config"
  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  if hasSubstring litConfigHtml "literate-theme.css" then
    throw <| IO.userError "theme empty: HTML should not link literate-theme.css when no theme is set"

/-- Per-module hide_commands overrides global config. -/
private def testPerModuleHideCommands (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ tomlFile => do
  IO.FS.writeFile tomlFile (String.intercalate "\n" [
    "[modules.\"LitConfig\"]",
    "hide_commands = [\"set_option\"]",
    ""
  ])
  runLiterateHtml jsonDir htmlDir (configFile := some tomlFile)

  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  if hasSubstring litConfigHtml "set_option" then
    throw <| IO.userError "per-module hide_commands: LitConfig should not contain 'set_option'"
  -- Core should NOT be affected (no module config)
  let coreHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "Core" / "index.html")
  unless hasSubstring coreHtml "code-box" do
    throw <| IO.userError "per-module hide_commands: Core should still have code boxes"

/-- Per-module title appears in the page title and navbar. -/
private def testPerModuleTitle (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ tomlFile => do
  IO.FS.writeFile tomlFile (String.intercalate "\n" [
    "[modules.\"LitConfig.Core\"]",
    "title = \"Core Library\"",
    ""
  ])
  runLiterateHtml jsonDir htmlDir (configFile := some tomlFile)

  let coreHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "Core" / "index.html")
  unless hasSubstring coreHtml "Core Library" do
    throw <| IO.userError "per-module title: page should contain 'Core Library'"
  -- Check navbar
  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  let navbarSection := litConfigHtml.splitOn "module-tree" |>.getD 1 "" |>.splitOn "</nav>" |>.head!
  unless hasSubstring navbarSection "Core Library" do
    throw <| IO.userError "per-module title: navbar should contain 'Core Library'"

/-- Per-module URL override places the HTML at the custom path and updates navbar links. -/
private def testPerModuleUrl (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ tomlFile => do
  IO.FS.writeFile tomlFile (String.intercalate "\n" [
    "[modules.\"LitConfig.Core\"]",
    "url = \"core-docs\"",
    ""
  ])
  runLiterateHtml jsonDir htmlDir (configFile := some tomlFile)

  -- HTML should be at the custom URL path, not the default
  unless ← (htmlDir / "core-docs" / "index.html").pathExists do
    throw <| IO.userError "per-module url: expected HTML at core-docs/index.html"
  if ← (htmlDir / "LitConfig" / "Core" / "index.html").pathExists then
    throw <| IO.userError "per-module url: HTML should not exist at default path LitConfig/Core/index.html"
  -- Navbar should link to the custom URL
  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  let navbarSection := litConfigHtml.splitOn "module-tree" |>.getD 1 "" |>.splitOn "</nav>" |>.head!
  unless hasSubstring navbarSection "core-docs/" do
    throw <| IO.userError "per-module url: navbar should link to 'core-docs/'"

/-- Plan fails when two modules resolve to the same URL. -/
private def testPlanDuplicateUrl (data : TestData) : IO Unit := IO.FS.withTempDir fun tmpDir => do
  let planFile := tmpDir / "plan"
  let tomlFile := tmpDir / "literate.toml"
  -- Set LitConfig.Core's url to "LitConfig/NoDocstrings" which collides with the default
  -- URL for LitConfig.NoDocstrings
  IO.FS.writeFile tomlFile (String.intercalate "\n" [
    "[modules.\"LitConfig.Core\"]",
    "url = \"LitConfig/NoDocstrings\"",
    ""
  ])
  let (exitCode, _, stderr) ← runLiteratePlanCapture data.moduleListFile planFile (some tomlFile)
  if exitCode == 0 then
    throw <| IO.userError "plan duplicate url: should have failed with non-zero exit code"
  unless hasSubstring stderr "same URL" do
    throw <| IO.userError s!"plan duplicate url: stderr should mention 'same URL', got: {stderr}"

/-- CSS contains focus-visible indicators. -/
private def testAccessibilityFocusVisible (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ _ => do
  runLiterateHtml jsonDir htmlDir
  let css ← IO.FS.readFile (htmlDir / "literate.css")
  unless hasSubstring css "focus-visible" do
    throw <| IO.userError "accessibility: literate.css does not contain focus-visible rules"

/-- CSS contains prefers-reduced-motion rules. -/
private def testAccessibilityReducedMotion (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ _ => do
  runLiterateHtml jsonDir htmlDir
  let css ← IO.FS.readFile (htmlDir / "literate.css")
  unless hasSubstring css "prefers-reduced-motion" do
    throw <| IO.userError "accessibility: literate.css does not contain prefers-reduced-motion"

/-- Hamburger menu has ARIA attributes. -/
private def testAccessibilityAria (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ _ => do
  runLiterateHtml jsonDir htmlDir
  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  unless hasSubstring litConfigHtml "aria-label=\"Menu\"" do
    throw <| IO.userError "accessibility: hamburger input missing aria-label"
  unless hasSubstring litConfigHtml "aria-label=\"Toggle navigation\"" do
    throw <| IO.userError "accessibility: hamburger label missing aria-label"

/-- LitConfig root module (with headings) gets a page ToC. -/
private def testPageToc (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ _ => do
  runLiterateHtml jsonDir htmlDir
  let litConfigHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "index.html")
  unless hasSubstring litConfigHtml "page-toc" do
    throw <| IO.userError "page ToC: LitConfig page should contain page-toc"
  unless hasSubstring litConfigHtml "Page table of contents" do
    throw <| IO.userError "page ToC: page-toc should have aria-label"
  unless hasSubstring litConfigHtml "On this page" do
    throw <| IO.userError "page ToC: page-toc should contain 'On this page' title"

/-- NoDocstrings module (no headings) should not get a page ToC. -/
private def testPageTocAbsent (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ _ => do
  runLiterateHtml jsonDir htmlDir
  let noDocHtml ← IO.FS.readFile (htmlDir / "LitConfig" / "NoDocstrings" / "index.html")
  if hasSubstring noDocHtml "page-toc" then
    throw <| IO.userError "page ToC absent: NoDocstrings page should not have a page-toc"

/-- CSS contains dark mode defaults. -/
private def testCssDarkMode (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ _ => do
  runLiterateHtml jsonDir htmlDir
  let css ← IO.FS.readFile (htmlDir / "literate.css")
  unless hasSubstring css "prefers-color-scheme: dark" do
    throw <| IO.userError "dark mode: literate.css does not contain dark mode media query"

/-- CSS uses custom properties (var(--verso-*)) throughout. -/
private def testCssCustomProperties (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ _ => do
  runLiterateHtml jsonDir htmlDir
  let css ← IO.FS.readFile (htmlDir / "literate.css")
  unless hasSubstring css "--verso-text-color" do
    throw <| IO.userError "CSS vars: literate.css does not define --verso-text-color"
  unless hasSubstring css "--verso-background-color" do
    throw <| IO.userError "CSS vars: literate.css does not define --verso-background-color"
  unless hasSubstring css "--verso-link-color" do
    throw <| IO.userError "CSS vars: literate.css does not define --verso-link-color"
  unless hasSubstring css "var(--verso-text-color)" do
    throw <| IO.userError "CSS vars: literate.css does not use var(--verso-text-color)"

-- ===== Test runner =====

private def htmlTests (data : TestData) : List (String × IO Unit) := [
  ("default behavior", testDefaultBehavior data),
  ("exclude", testExclude data),
  ("navbar order", testNavbarOrder data),
  ("landing page", testLandingPage data),
  ("recursive exclusion", testRecursiveExclusion data),
  ("order_children", testOrderChildren data),
  ("xref.json generated", testXrefJsonGenerated data),
  ("plan file content", testPlanFileContent data),
  ("targets filtering", testTargetsFiltering data),
  ("targets library", testTargetsLibrary data),
  ("targets library nonexistent", testTargetsLibraryNonexistent data),
  ("targets library + module", testTargetsLibraryAndModule data),
  ("hide_commands", testHideCommands data),
  ("metadata title", testMetadataTitle data),
  ("extra CSS", testExtraCss data),
  ("show_docstrings = false", testShowDocstringsFalse data),
  ("hide_docstrings_for", testHideDocstringsFor data),
  ("show_imports = false", testShowImportsFalse data),
  ("show_imports default", testShowImportsDefault data),
  ("show_output", testShowOutput data),
  ("show_output = []", testShowOutputEmpty data),
  ("favicon", testFavicon data),
  ("extra JS", testExtraJs data),
  ("targets + exclude", testTargetsPlusExclude data),
  ("show_docstrings_for exceptions", testShowDocstringsForExceptions data),
  ("metadata description", testMetadataDescription data),
  ("current page highlighting", testCurrentPageHighlighting data),
  ("plan targets + exclude", testPlanTargetsPlusExclude data),
  ("plan landing_page not in set", testPlanLandingPageNotInSet data),
  ("plan empty module set", testPlanEmptyModuleSet data),
  ("plan order warning", testPlanOrderWarning data),
  ("HTML invalid docstring_for", testHtmlInvalidDocstringFor data),
  ("theme CSS", testThemeCss data),
  ("theme CSS empty", testThemeCssEmpty data),
  ("per-module hide_commands", testPerModuleHideCommands data),
  ("per-module title", testPerModuleTitle data),
  ("per-module url", testPerModuleUrl data),
  ("plan duplicate url", testPlanDuplicateUrl data),
  ("accessibility focus-visible", testAccessibilityFocusVisible data),
  ("accessibility reduced-motion", testAccessibilityReducedMotion data),
  ("accessibility ARIA", testAccessibilityAria data),
  ("page ToC", testPageToc data),
  ("page ToC absent", testPageTocAbsent data),
  ("CSS dark mode", testCssDarkMode data),
  ("CSS custom properties", testCssCustomProperties data)
]

def testLiterateHtml : IO Unit := do
  IO.println "Running literate HTML tests..."
  let projectDir := "test-projects/literate-config"
  let modules := #["LitConfig", "LitConfig.Core", "LitConfig.Core.Basic", "LitConfig.NoDocstrings"]

  -- First verify test project toolchain matches root toolchain
  let rootToolchain ← IO.FS.readFile "lean-toolchain"
  let testToolchain ← IO.FS.readFile (projectDir / "lean-toolchain")
  unless rootToolchain == testToolchain do
    throw <| IO.userError s!"test-projects/literate-config/lean-toolchain ({testToolchain.trimAscii}) does not match root lean-toolchain ({rootToolchain.trimAscii})"

  -- Next, ensure test project manifest is up to date
  let lakeVars :=
    #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
      "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
      "LEAN_GITHASH",
      "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]
  let updateResult ← IO.Process.output {
    cmd := "elan"
    args := #["run", "--install", rootToolchain.trimAscii.toString, "lake", "update", "verso"]
    cwd := projectDir
    env := lakeVars.map (·, none)
  }
  if updateResult.exitCode != 0 then
    IO.eprintln s!"lake update stderr: {updateResult.stderr}"
    throw <| IO.userError s!"lake update verso failed with exit code {updateResult.exitCode}"

  -- Build shared test data (JSON) in a persistent temp dir
  IO.FS.withTempDir fun sharedTmpDir => do
    let jsonDir := sharedTmpDir / "json"
    let moduleListFile := sharedTmpDir / "modules"
    IO.FS.createDirAll jsonDir

    IO.println "  Building literate JSON for test modules..."
    for mod in modules do
      let json ← VersoLiterate.loadModuleJson projectDir mod
      let jsonFile := mod.splitOn "." |>.foldl (init := jsonDir) (· / ·) |>.withExtension "json"
      IO.FS.createDirAll (jsonFile.parent.getD jsonDir)
      IO.FS.writeFile jsonFile json

    -- Write module list with library annotations (tab-separated: library\tmodule)
    -- All test modules belong to the "LitConfig" library
    let moduleEntries := modules.map fun m => s!"LitConfig\t{m}"
    IO.FS.writeFile moduleListFile ("\n".intercalate moduleEntries.toList ++ "\n")

    let data : TestData := { jsonDir, modules, moduleListFile }

    let mut failures := 0
    for (name, test) in htmlTests data do
      IO.print s!"  {name}... "
      try
        test
        IO.println "passed"
      catch e =>
        IO.eprintln s!"FAILED - {e}"
        failures := failures + 1

    if failures == 0 then
      IO.println "  All literate HTML tests passed!"
    else
      throw <| IO.userError s!"{failures} literate HTML test(s) failed"

end Tests.LiterateHtml
