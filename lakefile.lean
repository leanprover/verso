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

-- All test code: Errata test modules, compile-time tests, fixtures, and generators. Submodules are
-- globbed so each is built and every `@[test]` module is discoverable.
@[default_target]
lean_lib VersoTests where
  srcDir := "src/tests"
  roots := #[`VersoTests]
  globs := #[Glob.andSubmodules `VersoTests]

-- Everything below is Errata's own implementation: its library, the single-test runner and widget
-- support exe, its self-tests, the generated discovery runner, and the `lake test` driver.
section Errata

@[default_target]
input_file errataUsageFile where
  text := true
  path := "src/errata/Errata/usage.txt"

input_file errataRunTestWidgetJs where
  text := true
  path := "src/errata/Errata/widget/run_test_widget.js"

lean_lib Errata where
  srcDir := "src/errata"
  roots := #[`Errata]
  needs := #[errataUsageFile, errataRunTestWidgetJs]

-- Runs one test in a fresh process so the widget can stream its output and kill it on cancel.
@[default_target]
lean_exe «errata-run-one» where
  srcDir := "src/errata"
  root := `ErrataRunOne
  supportInterpreter := true

-- Tests that exercise Errata using Errata itself.
lean_lib ErrataTests where
  srcDir := "src/errata-tests"
  roots := #[`ErrataTests]

-- The selected test set, written by the driver. The generated targets depend on it, so changing
-- the selection changes their trace and Lake rebuilds them rather than relinking a stale object.
input_file errataSelection where
  text := true
  path := ".lake/errata-runner/selection"

-- The generated discovered-tests module (`allTests`), written by the Errata driver.
lean_lib ErrataGenerated where
  srcDir := ".lake/errata-runner"
  roots := #[`ErrataDiscovered]
  needs := #[errataSelection]

-- The generated, discovered test runner. Its source is written by the Errata test driver.
lean_exe «errata-runner» where
  root := `ErrataRunnerMain
  srcDir := ".lake/errata-runner"
  supportInterpreter := true
  needs := #[errataSelection]

/--
Whether a source file introduces Errata tests, by an `@[test]` attribute (applied inline or with a
separate `attribute [test] …`), a `#test_msgs` command, or a `#test_guard` command. This drives the
glob-coverage check, which reads source files before anything is built; test discovery itself reads
the compiled modules.
-/
private def errataSourceHasTests (lines : List String) : Bool :=
  lines.any fun line =>
    let t := line.trimAsciiStart.copy
    t.startsWith "@[test]" || t.startsWith "attribute [test" ||
      t.startsWith "#test_msgs" || t.startsWith "#test_guard"

/-- Reads a built module's `.olean` header: whether it participates in the module system, and whether
it records any `@[test]` (including those generated by `#test_msgs` and `#test_guard`). -/
private def errataModuleInfo (oleanFile : System.FilePath) : IO (Bool × Bool) := do
  let (data, region) ← Lean.readModuleData oleanFile
  let hasTests := data.entries.any fun (name, entries) => name == `Errata.test && entries.size > 0
  let isModule := data.isModule
  unsafe region.free
  return (isModule, hasTests)

/-- Generate the bridge module: `import all` the module-system test modules so their private tests
are reachable, gathering them into `allTests` through `getAllTests%`. -/
private def errataDiscoveredSource (packageName : String) (mods : Array Lean.Name) : String :=
  let imports := "\n".intercalate ("public import Errata" :: mods.toList.map (s!"import all {·}"))
  let modList := " ".intercalate (mods.toList.map (·.toString))
  s!"module\n\n{imports}\n\n\
    public def allTests : Array Errata.TestEntry := getAllTests% \"{packageName}\" {modList}\n"

/-- Generate the non-module main: import the bridge module and the non-module test modules (which a
`module` cannot import), then run their combined tests. -/
private def errataMainSource (packageName : String) (mods : Array Lean.Name) (discovered : Lean.Name) :
    String :=
  let imports := "\n".intercalate
    ("import Errata" :: s!"import {discovered}" :: mods.toList.map (s!"import {·}"))
  let modList := " ".intercalate (mods.toList.map (·.toString))
  s!"{imports}\n\n\
    def main (args : List String) : IO UInt32 :=\n  \
    Errata.runMain (allTests ++ getAllTests% \"{packageName}\" {modList}) args\n"

/--
Splits driver arguments at the `--test-options` marker into library names and runner passthrough
arguments. Library names precede the marker and may not look like options; everything after the
marker goes to the runner.
-/
private def errataSplitArgs (args : List String) : Except String (List String × List String) :=
  let (names, rest) :=
    match args.span (· != "--test-options") with
    | (names, _ :: after) => (names, after)
    | (names, []) => (names, [])
  match names.find? (·.startsWith "-") with
  | some opt =>
    .error s!"unexpected option '{opt}': arguments before the `--test-options` marker name the \
      libraries to test. Put runner options after the marker, \
      e.g. `lake test -- --test-options {opt}`."
  | none => .ok (names, rest)

/-- Usage information for `lake test`, shared with `Errata.usage` through one text file. -/
private def errataUsage : String := include_str "src/errata/Errata/usage.txt"

/-- Every `.lean` file below a directory, recursively. -/
private partial def errataLeanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  unless ← dir.pathExists do return #[]
  let mut out := #[]
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      out := out ++ (← errataLeanFiles entry.path)
    else if entry.path.extension == some "lean" then
      out := out.push entry.path
  return out

/-- The module name of a `.lean` file relative to a source directory, if it lies within it. -/
private def errataModuleOfPath (srcDir path : System.FilePath) : Option Lean.Name := do
  guard (path.extension == some "lean")
  let stem ← path.fileStem
  let parent ← path.parent
  guard (srcDir.components.isPrefixOf parent.components)
  let comps := parent.components.drop srcDir.components.length ++ [stem]
  some (".".intercalate comps).toName

/--
Warns about modules that look like they define tests but whose library's globs do not cover them, so
the tests would be silently undiscovered. A module within a library's root that is not matched by the
library's globs, in a file that introduces tests, is the signal. The check reads source text and is a
heuristic, so it warns rather than failing the run.
-/
private def errataWarnUncoveredTestModules (ws : Lake.Workspace) : IO Unit := do
  let mut missed : Array Lean.Name := #[]
  for lib in ws.root.leanLibs do
    if lib.name == `ErrataGenerated then continue
    let srcDir := lib.srcDir
    for path in ← errataLeanFiles srcDir do
      let some mod := errataModuleOfPath srcDir path | continue
      let withinRoot := lib.roots.any (·.isPrefixOf mod)
      let globbed := lib.config.globs.any (·.matches mod)
      if withinRoot && !globbed && !missed.contains mod then
        let lines := (← IO.FS.readFile path).splitOn "\n"
        if errataSourceHasTests lines then
          missed := missed.push mod
  unless missed.isEmpty do
    IO.eprintln "warning: these modules look like they define tests but their library's globs do \
      not cover them, so the tests are not discovered. Widen the library's `globs` \
      (e.g. `globs := #[Glob.andSubmodules `Root]`):"
    for mod in missed do
      IO.eprintln s!"  {mod}"

@[test_driver]
script «errata-test» (args) do
  let ws ← getWorkspace
  -- Answer `--help` before discovering or building anything.
  if args.any (fun a => a == "--help" || a == "-h") then
    IO.println errataUsage
    return 0
  let (libNames, runnerArgs) ←
    match errataSplitArgs args with
    | .ok result => pure result
    | .error msg =>
      IO.eprintln s!"error: {msg}"
      IO.eprintln errataUsage
      return 1
  -- Search the named libraries, or every library in the package by default. A name may be a bare
  -- `Library` in this package or a `package/Library` reaching into a dependency, following Lake's
  -- target syntax. The generated runner lib has no source until this script writes it, and no tests.
  let candidates := ws.root.leanLibs.filter (·.name != `ErrataGenerated)
  let libs ←
    if libNames.isEmpty then pure candidates
    else do
      let mut chosen : Array Lake.LeanLib := #[]
      for spec in libNames do
        let lib? ←
          match spec.splitOn "/" with
          | [libName] => pure (candidates.find? (·.name == libName.toName))
          | [pkgName, libName] =>
            let pkgName := if pkgName.startsWith "@" then pkgName.drop 1 else pkgName
            let pkg? := if pkgName.isEmpty then some ws.root else ws.findPackageByName? pkgName.toName
            match pkg? with
            | some pkg => pure (pkg.findLeanLib? libName.toName)
            | none =>
              IO.eprintln s!"error: no package named '{pkgName}'"
              return 1
          | _ =>
            IO.eprintln s!"error: invalid library spec '{spec}' (expected `Library` or `package/Library`)"
            return 1
        match lib? with
        | some lib => chosen := chosen.push lib
        | none =>
          IO.eprintln s!"error: no library matches '{spec}'"
          return 1
      pure chosen
  -- Modules that look like they define tests but escape their library's globs are likely a
  -- configuration slip; warn, but run the discovered suite anyway.
  errataWarnUncoveredTestModules ws
  -- Build every module in the selected libraries; their compiled `.olean` headers are authoritative
  -- on which modules carry tests, so no test is dropped by a source-level heuristic.
  let modInfos ← runBuild do
    let mut oleanJobs := #[]
    let mut infos : Array (Lean.Name × System.FilePath) := #[]
    for lib in libs do
      let mods ← (← lib.modules.fetch).await
      for m in mods do
        oleanJobs := oleanJobs.push (← m.olean.fetch)
        infos := infos.push (m.name, m.oleanFile)
    (Job.collectArray oleanJobs).map (sync := true) fun _ => infos
  -- A test module is one whose `.olean` records a test. Module-system test modules go in the bridge
  -- module (`import all`); non-module ones can only be imported by the non-module main.
  let mut moduleMods : Array Lean.Name := #[]
  let mut nonModuleMods : Array Lean.Name := #[]
  for (moduleName, oleanFile) in modInfos do
    let (isModule, hasTests) ← errataModuleInfo oleanFile
    if hasTests then
      if isModule then moduleMods := moduleMods.push moduleName
      else nonModuleMods := nonModuleMods.push moduleName
  -- Write the generated sources, plus a `selection` file naming the chosen test set. The generated
  -- targets depend on that file, so a changed selection invalidates them through Lake's own trace.
  let dir := ws.root.dir / ".lake" / "errata-runner"
  IO.FS.createDirAll dir
  let selection := "\n".intercalate ((moduleMods ++ nonModuleMods).map (·.toString) |>.qsort (· < ·)).toList
  for (name, src) in
      [("selection", selection ++ "\n"),
       ("ErrataDiscovered.lean", errataDiscoveredSource ws.root.prettyName moduleMods),
       ("ErrataRunnerMain.lean", errataMainSource ws.root.prettyName nonModuleMods `ErrataDiscovered)] do
    let file := dir / name
    let changed ← if ← file.pathExists then pure ((← IO.FS.readFile file) != src) else pure true
    if changed then IO.FS.writeFile file src
  -- Build and run the discovered runner.
  let exePath ← runBuild «errata-runner».fetch
  let child ← IO.Process.spawn { cmd := exePath.toString, args := runnerArgs.toArray }
  child.wait

end Errata

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
