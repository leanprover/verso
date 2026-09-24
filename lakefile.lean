import Lake
open Lake DSL

require subverso from git "https://github.com/leanprover/subverso"@"main"
require MD4Lean from git "https://github.com/acmepjz/md4lean"@"main"
require plausible from git "https://github.com/leanprover-community/plausible"@"main"
require illuminate from git "https://github.com/leanprover/illuminate"@"main"
require Cli from git "https://github.com/leanprover/lean4-cli"@"main"

package verso where
  precompileModules := true
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
lean_lib VersoServe where
  roots := #[`VersoServe]
  srcDir := "src/verso-serve"

@[default_target]
lean_exe «verso-serve» where
  root := `VersoServeMain
  srcDir := "src/verso-serve"

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

-- Everything below is Errata's own implementation: its library, the runner, the single-test runner
-- that supports the widget, its self-tests, the generated test executables, and the `lake test`
-- driver.
namespace Errata

input_file errataRunTestWidgetJs where
  text := true
  path := "src/errata/Errata/widget/run_test_widget.js"

@[default_target]
lean_lib Errata where
  srcDir := "src/errata"
  roots := #[`Errata]
  needs := #[errataRunTestWidgetJs]

-- Runs one test in a fresh process so the widget can stream its output and kill it on cancel. The
-- widget builds it when it runs a test.
lean_exe «errata-run-one» where
  srcDir := "src/errata"
  root := `ErrataRunOne
  supportInterpreter := true

-- The runner, which lists and runs the tests of the test executables that the driver builds.
lean_exe «errata-runner» where
  srcDir := "src/errata"
  root := `ErrataRunner

-- Tests that exercise Errata using Errata itself.
@[default_target]
lean_lib ErrataTests where
  srcDir := "src/errata-tests"
  roots := #[`ErrataTests]

-- The directory below a package's Lake directory where the Errata driver writes the generated
-- sources of the test executables of that package's libraries.
def errataRunnerDir : System.FilePath := defaultLakeDir / "errata-runner"

/--
The directory of a package's generated test-executable sources, as an executable configuration's
`srcDir`. Lake joins that onto the package's source directory, which keeps an absolute path as it
is, so the generated sources are found wherever a package keeps its source directory.
-/
private def errataRunnerSrcDir (pkg : Package) : System.FilePath :=
  pkg.dir / errataRunnerDir

/--
The root of a package's generated module names. Lean's search path chooses a directory by a module
name's first component, so that component carries the package's name: the generated modules of the
packages in one workspace then stay apart.
-/
private def errataGeneratedRoot (pkg : Package) : Lean.Name :=
  .mkSimple s!"ErrataGenerated_{pkg.baseName.toString (escape := false)}"

/-- The generated main module of a library's test executable. -/
private def errataMainModule (lib : LeanLib) : Lean.Name :=
  errataGeneratedRoot lib.pkg ++ lib.name

/--
A library's test executable, as an executable in the library's package, built in that package's
build directory.
-/
private def errataTestExe (lib : LeanLib) : LeanExe where
  pkg := lib.pkg
  name := .mkSimple s!"errata-test-{lib.name.toString (escape := false)}"
  config.root := errataMainModule lib
  config.srcDir := errataRunnerSrcDir lib.pkg
  config.supportInterpreter := true
  -- The main is a non-module file that imports module-system test modules on purpose. Packages
  -- designed for the module system don't need warnings in this case.
  config.allowNonModules := true

/--
Builds a library's test executable from the generated main in its package's Lake directory. Before
building this facet, the driver must generate the main.
-/
library_facet errataExe lib : System.FilePath := withCurrPackage lib.pkg do
  let exe := errataTestExe lib
  (← exe.root.linkInfoExport.fetch).mapM fun info => do
    let args := exe.exeOnlyLinkArgs ++ info.args
    addPureTrace exe.exeOnlyLinkArgs "LeanExe.exeOnlyLinkArgs"
    buildLeanExeSync exe.file info.objs info.libs args exe.sharedLean

/-- What the Errata driver needs to know about a built module. -/
private structure ModuleInfo where
  /--
  Whether the module records any tests (including `@[test]` and those generated by `#test_msgs` and
  `#test_guard`).
  -/
  hasTests : Bool

-- The `@[noinline]` keeps the reads in this action, so they happen before the caller frees the
-- data's memory region.
@[noinline] private def readModuleInfo (data : Lean.ModuleData) : BaseIO ModuleInfo := do
  let hasEntries (ext : Lean.Name) : Bool :=
    data.entries.any fun (name, entries) => name == ext && entries.size > 0
  return {
    hasTests := hasEntries `Errata.test
  }

private def moduleInfo (oleanFile : System.FilePath) : IO ModuleInfo := do
  let (data, region) ← Lean.readModuleData oleanFile
  let info ← readModuleInfo data
  unsafe region.free
  return info

/--
The modules that sit under a library's roots on disk without being among the modules the library
actually builds. Nothing imports them and no glob covers them, so they are never compiled, and any
tests they define never run. `known` is the library's module set.
-/
private def unreachableModules (lib : Lake.LeanLib) (known : Lean.NameSet) :
    IO (Array Lean.Name) := do
  let found ← IO.mkRef (#[] : Array Lean.Name)
  for root in lib.config.roots do
    try
      Lake.Glob.submodules root |>.forEachModuleIn lib.srcDir fun m => do
        unless known.contains m do found.modify (·.push m)
    catch
      -- Thrown for a root with no corresponding directory, which has no submodules to orphan.
      | .noFileOrDirectory .. => pure ()
      | e => throw e
  found.get

/--
Generates the main of a library's test executable. It is a non-module file, so that it can import
both module-system and legacy test modules, and it hands their tests to the Lean harness.
-/
private def mainSource (pkg : String) (mods : Array Lean.Name) : String :=
  let imports := "\n".intercalate <| "import Errata" :: mods.toList.map (s!"import {·}")
  s!"{imports}\n\n\
    def main (args : List String) : IO UInt32 :=\n  \
    Errata.Harness.main (getAllTests% {pkg.quote} {" ".intercalate (mods.toList.map (·.toString))}) \
      args\n"

/-- The configuration that the driver writes for the runner, as JSON. -/
private def configJson (executables : Array (String × System.FilePath)) (cwd : System.FilePath)
    (errataDir : String) (warnings : Array String) (invocation : String) : Lean.Json :=
  Lean.Json.mkObj [
    ("protocol", Lean.toJson (1 : Nat)),
    ("executables", Lean.Json.arr <| executables.map fun (name, path) =>
      Lean.Json.mkObj [("name", Lean.Json.str name),
        ("command", Lean.Json.arr #[Lean.Json.str path.toString]),
        ("cwd", Lean.Json.str cwd.toString)]),
    ("errataDir", Lean.Json.str errataDir),
    ("warnings", Lean.toJson warnings),
    ("invocation", Lean.Json.str invocation)
  ]

/--
How the Errata driver (the `Errata.run` script in this file) should be invoked: the command that
runs every test, and the command that arguments follow.

When the root package's test driver is the driver, the invocation command is `lake test`, with `lake
test --` to pass arguments. Otherwise, it is `lake run Errata.run` or `lake run <pkg>/Errata.run`,
depending on whether the script name is shadowed.

`self` is the package that defines the script.
-/
private def driverInvocation (ws : Workspace) (self : Package) : LakeT IO (String × String) := do
  let scriptName := `Errata.run
  let some found := self.scripts.find? scriptName
    | throw <| .userError s!"{self.prettyName} has no script named {scriptName}"
  let isTestDriver ← do
    if ws.root.testDriver.isEmpty then pure false
    else
      try
        let (pkg, driver) ← ws.root.resolveDriver "test" ws.root.testDriver
        pure (pkg.prettyName == self.prettyName && driver.toName == scriptName)
      catch _ => pure false
  if isTestDriver then return ("lake test", "lake test --")
  let spec :=
    if (ws.findScript? scriptName).map (·.name) == some found.name then scriptName.toString
    else found.name
  return (s!"lake run {spec}", s!"lake run {spec}")

/--
Splits driver arguments at the `--test-options` marker into library names and runner passthrough
arguments. Library names precede the marker and may not look like options; everything after the
marker goes to the runner.
-/
private def splitArgs (withArgs : String) (args : List String) :
    Except String (List String × List String) :=
  let (names, rest) :=
    match args.span (· != "--test-options") with
    | (names, _ :: after) => (names, after)
    | (names, []) => (names, [])
  match names.find? (·.startsWith "-") with
  | some opt =>
    .error s!"unexpected option '{opt}': arguments before the `--test-options` marker name the \
      libraries to test. Put runner options after the marker, \
      e.g. `{withArgs} --test-options {opt}`."
  | none => .ok (names, rest)

/--
Usage information for the driver, in terms of the commands that invoke it.
-/
private def usage (run withArgs : String) : String :=
  let forms := #[
    (run, "run every test in the package"),
    (s!"{withArgs} LIBRARY...", "run the tests in the given libraries"),
    (s!"{withArgs} LIBRARY... --test-options OPTION...", "pass runner options after the marker")]
  let width := forms.foldl (fun w (form, _) => max w form.length) 0
  let formLines := forms.map fun (form, what) =>
    s!"  {form.pushn ' ' (width + 2 - form.length)}{what}"
  s!"Errata test runner\n\n\
    Usage:\n{"\n".intercalate formLines.toList}\n\n\
    Tokens before `--test-options` name libraries. A library is a bare `Library` in this package\n\
    or a `package/Library` reaching into a dependency. Everything after the marker goes to the\n\
    test runner.\n\n\
    The runner documents its own options, including how to pass options to the tests \
    themselves:\n  {withArgs} --test-options --help\n"

-- The script's name is the one `driverInvocation` looks up.
@[test_driver]
script run (args) do
  let ws ← getWorkspace
  let some self := ws.findPackageByKey? __name__
    | IO.eprintln "error: the package that defines the Errata driver is not in the workspace"
      return 1
  let (run, withArgs) ← driverInvocation ws self
  -- Answer the driver's own `--help` before discovering or building anything. A `--help` after the
  -- marker asks for the runner's options, so it goes to the runner along with the other arguments.
  if (args.takeWhile (· != "--test-options")).any (fun a => a == "--help" || a == "-h") then
    IO.println (usage run withArgs)
    return 0
  let (libNames, runnerArgs) ←
    match splitArgs withArgs args with
    | .ok result => pure result
    | .error msg =>
      IO.eprintln s!"error: {msg}"
      IO.eprintln (usage run withArgs)
      return 1
  IO.println "== Discovery"
  (← IO.getStdout).flush
  -- Search the named libraries, or every library in the package by default. A name may be a bare
  -- `Library` in this package or a `package/Library` reaching into a dependency, following Lake's
  -- target syntax.
  let candidates := ws.root.leanLibs
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
  -- Build every module in the selected libraries; their compiled `.olean` headers are authoritative
  -- on which modules carry tests.
  let (modInfos, libMods) ← runBuild do
    let mut oleanJobs := #[]
    let mut infos : Array (Lean.Name × System.FilePath) := #[]
    let mut libMods : Array (Lake.LeanLib × Array Lean.Name) := #[]
    for lib in libs do
      let mods ← (← lib.modules.fetch).await
      libMods := libMods.push (lib, mods.map (·.name))
      for m in mods do
        oleanJobs := oleanJobs.push (← m.olean.fetch)
        infos := infos.push (m.name, m.oleanFile)
    pure <| (Job.collectArray oleanJobs).map (sync := true) fun _ => (infos, libMods)
  -- A test module is one whose `.olean` records a test.
  let mut testMods : Array Lean.Name := #[]
  for (moduleName, oleanFile) in modInfos do
    if (← moduleInfo oleanFile).hasTests then testMods := testMods.push moduleName
  -- A module that sits under a library's roots without being reachable from them is never built, so
  -- any tests it defines are silently left out. A library is checked when it was named on the
  -- command line, since naming it declares that its tests are expected, or when its built modules
  -- carry tests. That is a configuration slip rather than a test failure, so it is a warning that
  -- the runner reports alongside the results, and the run goes ahead.
  let mut unreachable : Array (Lake.LeanLib × Array Lean.Name) := #[]
  for (lib, mods) in libMods do
    if !libNames.isEmpty || mods.any (testMods.contains ·) then
      let known := mods.foldl (init := Lean.NameSet.empty) (·.insert ·)
      let missed ← unreachableModules lib known
      unless missed.isEmpty do unreachable := unreachable.push (lib, missed)
  let mut driverWarnings : Array String := #[]
  unless unreachable.isEmpty do
    let lines := unreachable.flatMap fun (lib, mods) => mods.map fun mod => s!"  {lib.name}: {mod}"
    driverWarnings := driverWarnings.push <|
      s!"these modules are not reachable from their library's roots, so any tests they define are \
        not discovered. Import them from a root, or widen the library's `globs` \
        (e.g. `globs := #[Glob.andSubmodules `Root]`):\n{"\n".intercalate lines.toList}"
  -- Each library with tests gets a test executable, whose main is generated in its package's Lake
  -- directory. The main changes only when the library's test modules do, so Lake's own traces
  -- rebuild what depends on it.
  let testLibs := libMods.filterMap fun (lib, mods) =>
    let own := mods.filter (testMods.contains ·)
    if own.isEmpty then none else some (lib, own)
  for (lib, mods) in testLibs do
    let file := Lean.modToFilePath (errataRunnerSrcDir lib.pkg) (errataMainModule lib) "lean"
    let src := mainSource lib.pkg.prettyName mods
    if let some parent := file.parent then IO.FS.createDirAll parent
    let changed ← if ← file.pathExists then pure ((← IO.FS.readFile file) != src) else pure true
    if changed then IO.FS.writeFile file src
  -- An executable is named after its library, and after its package too when two selected
  -- libraries share a name.
  let exeName (lib : Lake.LeanLib) : String :=
    let name := lib.name.toString (escape := false)
    if (testLibs.filter (·.1.name == lib.name)).size > 1 then s!"{lib.pkg.prettyName}/{name}"
    else name
  -- Build the test executables and the runner, then the runner's configuration, which Lake rebuilds
  -- when the discovery results or the executables change.
  let errataDir ← IO.FS.realPath self.dir
  let rootDir ← IO.FS.realPath ws.root.dir
  let configFile := ws.root.dir / defaultLakeDir / "errata" / "config.json"
  let some runnerExe := self.findLeanExe? `«errata-runner»
    | IO.eprintln "error: the package that defines the Errata driver has no errata-runner"
      return 1
  let (configPath, runnerPath) ← runBuild do
    let exeJobs ← testLibs.mapM fun (lib, _) => (lib.facet `errataExe).fetch
    let runnerJob ← runnerExe.exe.fetch
    (Job.collectArray exeJobs).bindM fun exePaths => do
      runnerJob.mapM fun runnerPath => do
        let mut executables := #[]
        for ((lib, _), path) in testLibs.zip exePaths do
          executables := executables.push (exeName lib, ← IO.FS.realPath path)
        -- Tests run from the root package's directory, where `lake test` runs.
        let content := (configJson executables rootDir errataDir.toString driverWarnings
          s!"{withArgs} --test-options").pretty ++ "\n"
        addPureTrace content "Errata runner configuration"
        buildFileUnlessUpToDate' (text := true) configFile do
          if let some parent := configFile.parent then IO.FS.createDirAll parent
          IO.FS.writeFile configFile content
        return (configFile, runnerPath)
  -- The runner gets a standard input that the driver holds and never writes to, and
  -- `ERRATA_LIFELINE` asks it to end its tests when that pipe closes. `LEAN_ABORT_ON_PANIC` is removed from its environment rather than
  -- inherited, because some CI systems set it; the runner sets it for the tests under
  -- `--exit-on-panic`.
  let child ← IO.Process.spawn {
    cmd := runnerPath.toString, args := #[configPath.toString] ++ runnerArgs.toArray
    stdin := .piped
    env := #[("LEAN_ABORT_ON_PANIC", none), ("ERRATA_LIFELINE", some "1")]
  }
  child.wait

end Errata

-- The release notes compute the version under development from this file while they elaborate,
-- so its contents are an input to the library.
input_file leanToolchain where
  text := true
  path := "lean-toolchain"

lean_lib UsersGuide where
  srcDir := "doc"
  leanOptions := #[⟨`weak.linter.verso.manual.headerTags, true⟩]
  needs := #[leanToolchain]

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
