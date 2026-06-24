import Lake
open Lake DSL

require subverso from git "https://github.com/leanprover/subverso"@"main"
require MD4Lean from git "https://github.com/acmepjz/md4lean"@"main"
require plausible from git "https://github.com/leanprover-community/plausible"@"main"
require illuminate from git "https://github.com/leanprover/illuminate"@"main"

package verso where
  precompileModules := false -- temporarily disabled to work around an issue with nightly-2025-03-30
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib VersoUtil where
  srcDir := "src/verso-util"
  roots := #[`VersoUtil]

input_dir staticWeb where
  text := true
  path := "static-web"

input_dir vendorJs where
  path := "vendored-js"

@[default_target]
lean_lib Verso where
  srcDir := "src/verso"
  roots := #[`Verso]
  needs := #[staticWeb, vendorJs]

@[default_target]
lean_lib MultiVerso where
  srcDir := "src/multi-verso"
  roots := #[`MultiVerso]

@[default_target]
lean_lib VersoSearch where
  srcDir := "src/verso-search"
  -- Rebuild search when JS on disk changes
  needs := #[staticWeb]

@[default_target]
lean_lib VersoBlog where
  srcDir := "src/verso-blog"
  roots := #[`VersoBlog]

@[default_target]
lean_lib VersoManual where
  srcDir := "src/verso-manual"
  roots := #[`VersoManual]
  needs := #[staticWeb]

@[default_target]
lean_lib VersoIlluminate where
  srcDir := "src/verso-illuminate"
  roots := #[`VersoIlluminate]

input_file tutorialDefaultCss where
  text := true
  path := "src/verso-tutorial/default.css"

@[default_target]
lean_lib VersoTutorial where
  srcDir := "src/verso-tutorial"
  roots := #[`VersoTutorial]
  needs := #[tutorialDefaultCss]

input_file ghSetupLiteratePages where
  text := true
  path := "gh-setup/verso-literate-pages.yml"

@[default_target]
lean_exe «verso» where
  root := `VersoMain
  srcDir := "src/cli"
  needs := #[ghSetupLiteratePages]
  supportInterpreter := true

@[default_target]
lean_lib VersoLiterate where
  roots := #[`VersoLiterate]
  srcDir := "src/verso-literate"

@[default_target]
lean_exe «verso-literate» where
  root := `VersoLiterateMain
  srcDir := "src/verso-literate"
  supportInterpreter := true

@[default_target]
lean_lib VersoLiterateCode where
  srcDir := "src/verso-literate-code"
  roots := #[`VersoLiterateCode]

input_file «verso-html-css» where
  text := true
  path := "src/verso-html/code.css"

@[default_target]
lean_exe «verso-html» where
  root := `VersoHtmlMain
  srcDir := "src/verso-html"
  needs := #[«verso-html-css»]
  supportInterpreter := true

input_file «verso-literate-html-css» where
  text := true
  path := "src/verso-literate-html/literate.css"

input_dir literateStaticWeb where
  text := true
  path := "static-web/literate"

@[default_target]
lean_exe «verso-literate-html» where
  root := `LiterateHtmlMain
  srcDir := "src/verso-literate-html"
  needs := #[«verso-literate-html-css», literateStaticWeb]
  supportInterpreter := true

@[default_target]
lean_exe «verso-literate-plan» where
  root := `LiteratePlanMain
  srcDir := "src/verso-literate-plan"
  supportInterpreter := true

@[default_target]
input_file errataUsageFile where
  text := true
  path := "src/errata/Errata/usage.txt"

lean_lib Errata where
  srcDir := "src/errata"
  roots := #[`Errata]
  needs := #[errataUsageFile]

-- Enumerates the Errata tests defined in a module.
lean_exe «errata-enumerate» where
  root := `ErrataEnumerateMain
  srcDir := "src/errata"
  supportInterpreter := true

-- Writes the fully-qualified names of the Errata tests defined directly in a module.
module_facet errataTests mod : System.FilePath := do
  let ws ← getWorkspace
  let exeJob ← «errata-enumerate».fetch
  -- Depend on `leanArts`, not `olean`: enumeration reads the whole module, including private and
  -- `meta` test declarations, which the public olean's trace excludes. The `leanArts` trace inherits
  -- the source trace, so adding or removing any test invalidates the manifest.
  let modJob ← mod.leanArts.fetch
  let buildDir := ws.root.buildDir
  let outFile := mod.filePath (buildDir / "errata-tests") "json"
  exeJob.bindM fun exeFile =>
    modJob.mapM fun _arts => do
      addLeanTrace
      addTrace (← computeTrace exeFile)
      buildFileUnlessUpToDate' (text := true) outFile <|
        proc {
          cmd := exeFile.toString
          args := #[mod.name.toString, outFile.toString]
          env := ← getAugmentedEnv
        }
      pure outFile

-- Tests that exercise Errata using Errata itself.
lean_lib ErrataTests where
  srcDir := "src/errata-tests"
  roots := #[`ErrataTests]

-- The generated discovered-tests module (`allTests`), written by the Errata driver.
lean_lib ErrataGenerated where
  srcDir := ".lake/errata-runner"
  roots := #[`ErrataDiscovered]

-- The generated, discovered test runner. Its source is written by the Errata test driver.
lean_exe «errata-runner» where
  root := `ErrataRunnerMain
  srcDir := ".lake/errata-runner"
  supportInterpreter := true

/-- The test's name below its module: the declaration's components past the module prefix, dotted. -/
private def errataTestName (moduleName declName : Lean.Name) : String :=
  let modComps := moduleName.components
  let declComps := declName.components
  let below := if moduleName.isPrefixOf declName then declComps.drop modComps.length else declComps
  ".".intercalate (below.map (·.toString))

/-- Parse a per-module JSON manifest into the tests' user-facing names. -/
private def errataParseManifest (content : String) : Array String :=
  match Lean.Json.parse content with
  | .error _ => #[]
  | .ok json =>
    match json.getArr? with
    | .error _ => #[]
    | .ok arr => arr.filterMap fun j => (j.getStr?).toOption

/-- Generate the discovered-tests module: `import all` the test modules and collect their tests. -/
private def errataDiscoveredSource (packageName : String)
    (mods : Array (Lean.Name × Array String)) : String := Id.run do
  let mut imports := #["public import Errata"]
  let mut entries : Array String := #[]
  for (moduleName, tests) in mods do
    imports := imports.push s!"import all {moduleName}"
    for name in tests do
      let test := errataTestName moduleName name.toName
      entries := entries.push
        s!"  Errata.TestEntry.of \"{packageName}\" \"{moduleName}\" \"{test}\" (@{name})"
  let header := "\n".intercalate imports.toList
  let body := ",\n".intercalate entries.toList
  return s!"module\n\n{header}\n\n\
    public def allTests : Array Errata.TestEntry := #[\n{body}\n]\n"

/-- The main that runs the discovered tests. -/
private def errataMainSource : String :=
  "import Errata\n\
   import ErrataDiscovered\n\n\
   def main (args : List String) : IO UInt32 :=\n  \
   Errata.runMain allTests args\n"

/-- The module a target spec `[package/]module[#test]` selects (the unit of execution). -/
private def errataSpecModule (s : String) : String :=
  let afterPkg := match s.splitOn "/" with | [_, rest] => rest | _ => s
  (afterPkg.splitOn "#").headD afterPkg

/-- Whether a module is selected by the given target specs (empty selects everything). -/
private def errataModuleSelected (specs : List String) (moduleName : Lean.Name) : Bool :=
  specs.isEmpty || specs.any fun s =>
    let n := moduleName.toString
    n == s || n.startsWith (s ++ ".")

/-- Split driver arguments into module target specs and runner passthrough arguments. -/
private def errataSplitArgs (args : List String) : List String × List String :=
  match args.span (· != "--") with
  | (before, _ :: after) => (before, after)
  | (before, []) =>
    (before.filter (fun a => !a.startsWith "-"), before.filter (fun a => a.startsWith "-"))

/-- Usage information for `lake test`, shared with `Errata.usage` through one text file. -/
private def errataUsage : String := include_str "src/errata/Errata/usage.txt"

@[test_driver]
script «errata-test» (args) do
  let ws ← getWorkspace
  let (specs, runnerArgs) := errataSplitArgs args
  -- Answer `--help` before discovering or building anything.
  if runnerArgs.any (fun a => a == "--help" || a == "-h") then
    IO.println errataUsage
    return 0
  -- The module is the unit of execution; a test-level selector is rejected, not silently broadened.
  for spec in specs do
    if (spec.splitOn "#").length > 1 then
      IO.eprintln s!"error: Errata runs whole modules; '{spec}' names a test. \
        Select the module '{errataSpecModule spec}' instead."
      return 1
  let moduleSpecs := specs.map errataSpecModule
  -- Discover the tests in the selected modules, building the per-module enumeration facet.
  let (allNames, perModule) ← runBuild do
    let mut names : Array Lean.Name := #[]
    let mut jobs : Array (Job (Lean.Name × System.FilePath)) := #[]
    for lib in ws.root.leanLibs do
      -- The generated runner lib has no source until this script writes it, and it holds no tests.
      if lib.name == `ErrataGenerated then continue
      let mods ← (← lib.modules.fetch).await
      for m in mods do
        names := names.push m.name
        if errataModuleSelected moduleSpecs m.name then
          let job ← m.facet `errataTests |>.fetch
          jobs := jobs.push (job.map fun p => (m.name, p))
    pure ((Job.collectArray jobs).map fun ps => (names, ps))
  -- Every selector must name a real module.
  for spec in moduleSpecs do
    unless allNames.any (fun n => n.toString == spec || n.toString.startsWith (spec ++ ".")) do
      IO.eprintln s!"error: no module matches '{spec}'"
      return 1
  let mut mods : Array (Lean.Name × Array String) := #[]
  for (moduleName, path) in perModule do
    let tests := errataParseManifest (← IO.FS.readFile path)
    unless tests.isEmpty do
      mods := mods.push (moduleName, tests)
  -- Write the two generated sources, only when they change, so the build is reused across runs.
  let dir := ws.root.dir / ".lake" / "errata-runner"
  IO.FS.createDirAll dir
  for (name, src) in [("ErrataDiscovered.lean", errataDiscoveredSource ws.root.prettyName mods),
      ("ErrataRunnerMain.lean", errataMainSource)] do
    let file := dir / name
    let changed ← if ← file.pathExists then pure ((← IO.FS.readFile file) != src) else pure true
    if changed then IO.FS.writeFile file src
  -- Build and run the discovered runner.
  let some exe := ws.findLeanExe? `«errata-runner»
    | IO.eprintln "errata-runner executable is not configured"; return 1
  let exePath ← runBuild exe.fetch
  let child ← IO.Process.spawn { cmd := exePath.toString, args := runnerArgs.toArray }
  child.wait

@[default_target]
lean_lib Tests where
  srcDir := "src/tests"

-- The legacy ad-hoc test runner. The Errata driver below is the active test driver.
lean_exe «verso-tests» where
  root := `TestMain
  srcDir := "src/tests"
  supportInterpreter := true

lean_lib UsersGuide where
  srcDir := "doc"
  leanOptions := #[⟨`weak.linter.verso.manual.headerTags, true⟩]

@[default_target]
lean_exe usersguide where
  root := `UsersGuideMain
  supportInterpreter := true

-- A demo site that shows how to generate websites with Verso
lean_lib DemoSite where
  srcDir := "test-projects/website"
  roots := #[`DemoSite]

@[default_target]
lean_exe demosite where
  srcDir := "test-projects/website"
  root := `DemoSiteMain
  supportInterpreter := true

-- An example of a textbook project built in Verso
lean_lib DemoTextbook where
  srcDir := "test-projects/textbook"
  roots := #[`DemoTextbook]

@[default_target]
lean_exe demotextbook where
  srcDir := "test-projects/textbook"
  root := `DemoTextbookMain
  supportInterpreter := true

-- An example of a package documentation project built in Verso
lean_lib PackageManual where
  srcDir := "test-projects/package-manual"
  roots := #[`PackageManual]

@[default_target]
lean_exe packagedocs where
  srcDir := "test-projects/package-manual"
  root := `PackageManualMain
  supportInterpreter := true

-- An example of a minimal nontrivial custom genre
@[default_target]
lean_lib SimplePage where
  srcDir := "test-projects/custom-genre"
  roots := #[`SimplePage]

@[default_target]
lean_exe simplepage where
  srcDir := "test-projects/custom-genre"
  root := `SimplePageMain
  supportInterpreter := true

@[default_target]
lean_lib TutorialExample where
  srcDir := "test-projects/tutorial-test"

@[default_target]
lean_exe «tutorial-example» where
  srcDir := "test-projects/tutorial-test"
  root := `TutorialExampleMain
  supportInterpreter := true

private def leanOptionArgs (m : Module) : Array String := Id.run do
  let opts := Module.leanOptions m
  let vals := Lean.LeanOptions.values opts
  let mut args : Array String := #[]
  for (name, val) in vals.toList do
    let valStr :=
      match val with
      | .ofString s => s
      | .ofBool b => toString b
      | .ofNat n => toString n
    args := args.push s!"-D{name}={valStr}"
  return args

module_facet literate mod : System.FilePath := do
  let ws ← getWorkspace

  let exeJob ← «verso-literate».fetch
  let modJob ← mod.olean.fetch

  let buildDir := ws.root.buildDir
  let litFile := mod.filePath (buildDir / "literate") "json"

  let optArgs := leanOptionArgs mod

  exeJob.bindM fun exeFile =>
    modJob.mapM fun _oleanPath => do
      addLeanTrace
      addTrace (← computeTrace exeFile)
      addPureTrace (toString optArgs) "leanOptions"
      buildFileUnlessUpToDate' (text := true) litFile <|
        proc {
          cmd := exeFile.toString
          args := #[mod.name.toString, litFile.toString] ++ optArgs
          env := ← getAugmentedEnv
        }
      pure litFile

library_facet literate lib : Array System.FilePath := do
  let mods ← (← lib.modules.fetch).await
  let lits ← mods.mapM fun x =>
    x.facet `literate |>.fetch
  pure <| Job.collectArray lits


package_facet literate pkg : Array System.FilePath := do
  let libs := Job.collectArray (← pkg.leanLibs.mapM (·.facet `literate |>.fetch))
  let exes := Job.collectArray (← pkg.leanExes.mapM (·.toLeanLib.facet `literate |>.fetch))
  return libs.zipWith (·.flatten ++ ·.flatten) exes

section
variable [Monad m]
variable [MonadWorkspace m] [MonadLog m]
variable [MonadLiftT BaseIO m] [MonadLiftT IO m]

def checkDeployActions (pkg : Package) : m Unit := do
  let ws ← getWorkspace
  -- This is the build directory of the current root package (that is, the one t
  let buildDir := pkg.buildDir
  -- Check GitHub Pages workflow staleness
  let workflowFile : System.FilePath :=
    pkg.dir / ".github" / "workflows" / "verso-literate-pages.yml"
  let sentinelFile : System.FilePath := buildDir / ".literate-pages-prompted"
  let normalizeNl := fun (s : String) =>
    "\n".intercalate (s.splitOn "\n" |>.map fun (l : String) => l.trimAsciiEnd.copy)

  let some versoPkg ← pure (ws.findPackageByName? `verso)
    | Lake.logError "Verso was not found in the workspace"; return

  let ghPagesSetupFile : System.FilePath :=
    versoPkg.dir / "gh-setup" / "verso-literate-pages.yml"
  let ghPagesSetupContent ← IO.FS.readFile ghPagesSetupFile

  -- If the user already has the workflow file that we are producing, check for
  -- stale content
  if ← workflowFile.pathExists then
    let existingContent ← IO.FS.readFile workflowFile
    unless normalizeNl existingContent == normalizeNl ghPagesSetupContent do
      Lake.logWarning <|
        s!"{workflowFile} is outdated. Run `lake exe verso setup-literate` to update it."
    return

  -- If the workflow file doesn't exist, then check whether we've already told the user how to set
  -- it up. If not, tell them.
  unless ← sentinelFile.pathExists do
    Lake.logInfo "Run `lake exe verso setup-literate` to set up GitHub Pages deployment."
    IO.FS.writeFile sentinelFile ""
end

package_facet literateHtml pkg : System.FilePath := do
  let buildDir := pkg.buildDir
  let htmlDir := buildDir / "literate-html"
  let planFile := buildDir / "literate-plan"
  let moduleListFile := buildDir / "literate-modules"
  let moduleMapFile := buildDir / "literate-module-map"
  let tomlFile := pkg.dir / "literate.toml"

  -- Step 1: Collect all modules from libraries and executables
  let allModules ← pkg.leanLibs.foldlM (init := #[]) fun acc lib => do
    let mods ← (← lib.modules.fetch).await
    return acc ++ mods.map fun m => (lib.name, m, lib.srcDir)
  let allModules ← pkg.leanExes.foldlM (init := allModules) fun acc exe => do
    let lib := exe.toLeanLib
    let mods ← (← lib.modules.fetch).await
    return acc ++ mods.map fun m => (lib.name, m, lib.srcDir)

  let moduleListContent :=
    "\n".intercalate (allModules.map fun (libName, mod, _) => s!"{libName}\t{mod.name}").toList ++ "\n"

  let planExeJob ← «verso-literate-plan».fetch
  let htmlExeJob ← «verso-literate-html».fetch

  planExeJob.bindM fun planExeFile => do
    if ← tomlFile.pathExists then
      addTrace (← computeTrace tomlFile)
    else
      addPureTrace "No literate TOML config file"
    addPureTrace moduleListContent

    buildFileUnlessUpToDate' moduleListFile do
      IO.FS.createDirAll buildDir
      IO.FS.writeFile moduleListFile moduleListContent

    -- Re-add TOML trace (buildFileUnlessUpToDate' resets trace to output file hash)
    if ← tomlFile.pathExists then
      addTrace (← computeTrace tomlFile)
    addPureTrace moduleListContent

    buildFileUnlessUpToDate' planFile do
      let planArgs := #[moduleListFile.toString, planFile.toString] ++
        (if ← tomlFile.pathExists then #[tomlFile.toString] else #[])
      proc {
        cmd := planExeFile.toString
        args := planArgs
        env := ← getAugmentedEnv
      }

    -- Step 2: Read plan, fetch literate JSON for planned modules only
    let planContents ← IO.FS.readFile planFile
    let plannedNames := planContents.splitOn "\n"
      |>.filter (!·.isEmpty)
      |>.map String.toName

    let litJobs ← plannedNames.filterMapM fun name => do
      match allModules.find? fun (_, mod, _) => mod.name == name with
      | some (_, mod, srcDir) =>
        let job ← mod.facet `literate |>.fetch
        pure (some (name, job, srcDir))
      | none => pure none

    (Job.collectArray (litJobs.map (·.2.1) |>.toArray)).bindM fun litFiles => do
      -- Build module→JSON mapping (litFiles[i] corresponds to litJobs[i])
      let mappingContent := "\n".intercalate
        (litJobs.zip litFiles.toList |>.map fun ((name, _, srcDir), jsonPath) =>
          s!"{name}\t{jsonPath}\t{srcDir}") ++ "\n"
      addPureTrace mappingContent

      buildFileUnlessUpToDate' (text := true) moduleMapFile do
        IO.FS.writeFile moduleMapFile mappingContent

      -- Step 3: Run HTML generator with module map
      htmlExeJob.mapM fun htmlExeFile => do
        -- Re-add traces that were reset by buildFileUnlessUpToDate'
        for jsonPath in litFiles do
          addTrace (← computeTrace jsonPath)
        if ← tomlFile.pathExists then
          addTrace (← computeTrace tomlFile)
        buildUnlessUpToDate htmlDir (← getTrace) (htmlDir.addExtension "trace") do
          IO.FS.createDirAll htmlDir
          let mut htmlArgs := #[htmlDir.toString, moduleMapFile.toString]
          if ← tomlFile.pathExists then
            htmlArgs := htmlArgs.push tomlFile.toString
          proc {
            cmd := htmlExeFile.toString
            args := htmlArgs
            env := ← getAugmentedEnv
          }

        checkDeployActions pkg

        pure htmlDir
