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
    args := #["exe", name] ++ args
    stdout := .null
    stderr := .inherit
  }
  let exitCode ← child.wait
  if exitCode != 0 then
    throw <| IO.userError s!"{name} failed with exit code {exitCode}"

/-- Runs verso-literate-html with optional plan file and config file. -/
private def runLiterateHtml (jsonDir htmlDir : System.FilePath) (planFile configFile : Option System.FilePath := none) : IO Unit := do
  let mut args := #[jsonDir.toString, htmlDir.toString]
  if let some pf := planFile then
    args := args ++ #["--plan", pf.toString]
  if let some cf := configFile then
    args := args ++ #["--config", cf.toString]
  runLakeExe "verso-literate-html" args

/-- Runs verso-literate-plan to produce a plan file. -/
private def runLiteratePlan (moduleListFile planFile : System.FilePath) (tomlFile : Option System.FilePath := none) : IO Unit := do
  let mut args := #[moduleListFile.toString, planFile.toString]
  if let some tf := tomlFile then
    args := args ++ #[tf.toString]
  runLakeExe "verso-literate-plan" args

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

/-- Commands listed in `hide_commands` produce no output while other commands remain visible. -/
private def testHideCommands (data : TestData) : IO Unit := withTestDir data fun jsonDir htmlDir _ tomlFile => do
  IO.FS.writeFile tomlFile "hide_commands = [\"Lean.Parser.Command.set_option\"]\n"
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
  ("hide_commands", testHideCommands data),
  ("metadata title", testMetadataTitle data),
  ("extra CSS", testExtraCss data),
  ("show_docstrings = false", testShowDocstringsFalse data),
  ("hide_docstrings_for", testHideDocstringsFor data),
  ("show_imports = false", testShowImportsFalse data),
  ("show_imports default", testShowImportsDefault data),
  ("show_output", testShowOutput data),
  ("show_output = []", testShowOutputEmpty data)
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
    args := #["run", "--install", "leanprover/lean4:v4.28.0-rc1", "lake", "update", "verso"]
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

    IO.FS.writeFile moduleListFile ("\n".intercalate modules.toList ++ "\n")

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
