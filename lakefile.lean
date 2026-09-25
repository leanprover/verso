import Lake
import Lake.CLI.Build
open Lake DSL

require subverso from git "https://github.com/leanprover/subverso"@"main"
require MD4Lean from git "https://github.com/acmepjz/md4lean"@"main"
require plausible from git "https://github.com/leanprover-community/plausible"@"main"
require illuminate from git "https://github.com/leanprover/illuminate"@"main"

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

-- Everything below is Errata's own implementation: its library, the runner, the interpreted
-- product, its self-tests, the generated test executables, and the `lake test` driver.
namespace Errata

input_file errataRunTestWidgetJs where
  text := true
  path := "src/errata/Errata/widget/run_test_widget.js"

@[default_target]
lean_lib Errata where
  srcDir := "src/errata"
  roots := #[`Errata]
  needs := #[errataRunTestWidgetJs]

-- The interpreted product of the Lean harness, which imports test modules and runs their tests with
-- no generated main and no link. The driver's `--interpreted` flag runs tests through it.
lean_exe «errata-interpret» where
  srcDir := "src/errata"
  root := `ErrataInterpret
  supportInterpreter := true

-- The runner, which lists and runs the tests of the test executables that the driver builds.
lean_exe «errata-runner» where
  srcDir := "src/errata"
  root := `ErrataRunner

-- The processing of `errata.toml`, which uses Lake's TOML parser and nothing else of Lake.
@[default_target]
lean_lib ErrataConfig where
  srcDir := "src/errata"
  roots := #[`ErrataConfig]

-- Validates `errata.toml` and writes the elaborated `.lake/errata/config.json`.
lean_exe «errata-config» where
  srcDir := "src/errata"
  root := `ErrataConfigMain

-- Tests that exercise Errata using Errata itself.
@[default_target]
lean_lib ErrataTests where
  srcDir := "src/errata-tests"
  roots := #[`ErrataTests]

-- Tests of the processing of `errata.toml`, in process.
@[default_target]
lean_lib ErrataConfigTests where
  srcDir := "src/errata-tests"
  roots := #[`ErrataConfigTests]

-- The directory below a package's Lake directory where the Errata driver writes the generated
-- sources of the test executables of that package's libraries.
def errataRunnerDir : System.FilePath := defaultLakeDir / "errata-runner"

/--
The directory of a package's generated sources for the test executables, as an executable
configuration's `srcDir`. Lake joins that onto the package's source directory, which keeps an
absolute path as it is, so the generated sources are found wherever a package keeps its source
directory.
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
Generates the main of a library's test executable. The main is a file without a `module` header. It
imports the library's test modules, with or without a `module` header, and hands their tests and
every helper they reach to the Lean harness.
-/
private def mainSource (pkg : String) (mods : Array Lean.Name) : String :=
  let imports := "\n".intercalate <| "import Errata" :: mods.toList.map (s!"import {·}")
  s!"{imports}\n\n\
    def main (args : List String) : IO UInt32 :=\n  \
    Errata.Harness.main (getAllTests% {pkg.quote} {" ".intercalate (mods.toList.map (·.toString))}) \
      args (helpers := getAllHelpers%)\n"

/-!
The configuration file, `errata.toml`, which `errata-config` validates and elaborates into
`.lake/errata/config.json`. The driver reads from that file the targets that the selected profile
needs and the test executables that the file adds.
-/

/-- An object's fields, or none when the value is not an object. -/
private def jsonFields (j : Lean.Json) : Array (String × Lean.Json) :=
  match j.getObj? with
  | .ok obj => obj.toArray
  | .error _ => #[]

/-- A natural-number field of an object, or zero. -/
private def jsonNat (j : Lean.Json) (key : String) : Nat :=
  (j.getObjValAs? Nat key).toOption.getD 0

/--
The distinct targets that the settings of a profile in `config.json` and of its overrides need, each
with the line and column of its name in `errata.toml`.
-/
private def neededTargets (profile : Lean.Json) : Array (String × Nat × Nat) := Id.run do
  let overrides := match profile.getObjValD "override" with
    | .arr os => os
    | _ => #[]
  let mut out := #[]
  for scope in #[profile] ++ overrides do
    for (_, v) in jsonFields (scope.getObjValD "settings") do
      if let .ok tgt := v.getObjValAs? String "needs" then
        unless out.any (·.1 == tgt) do out := out.push (tgt, jsonNat v "line", jsonNat v "col")
  return out

/-- A test executable that `errata.toml` adds, as `config.json` records it. -/
private structure AddedExecutable where
  name : String
  command : Array String
  cwd? : Option String
  line : Nat
  col : Nat

/-- The test executables that `errata.toml` adds, from `config.json`. -/
private def addedExecutables (config : Lean.Json) : Array AddedExecutable :=
  match config.getObjValD "executables" with
  | .arr es => es.filterMap fun e => do
    let name ← (e.getObjValAs? String "name").toOption
    let command ← (e.getObjValAs? (Array String) "command").toOption
    return { name, command, cwd? := (e.getObjValAs? String "cwd").toOption,
             line := jsonNat e "line", col := jsonNat e "col" }
  | _ => #[]

/-- A library's test executable, as `workspace.json` records it. -/
private structure LibraryExecutable where
  name : String
  command : Array String
  env : Array (String × String) := #[]

/-! ## The interpreted product -/

/--
A module name as the command line writes it, read as Lean writes it, with `«»` around a component
that needs them.
-/
private def moduleNameOf (written : String) : Lean.Name :=
  (Lean.Syntax.decodeNameLit ("`" ++ written)).getD written.toName

/--
The test executable of a library whose tests run through the interpreted product at `interpreter`:
the interpreter with the library's test modules among `modules`, then `--`, with the workspace's
search path in its environment.
-/
private def interpretedExecutable (ws : Workspace) (interpreter : System.FilePath) (name : String)
    (libModules modules : Array Lean.Name) : LibraryExecutable where
  name
  command := #[interpreter.toString] ++
    (modules.filter libModules.contains |>.map (·.toString)) ++ #["--"]
  env := #[("LEAN_PATH", ws.augmentedLeanPath.toString),
    ("LEAN_SYSROOT", ws.lakeEnv.lean.sysroot.toString)]

/--
What the workspace contributes to the run, `.lake/errata/workspace.json`, as JSON: the path of each
needed target's result, the libraries' test executables and the executables `added` that
`errata.toml` adds, the directory of Errata's sources, the driver's warnings, the command that the
runner's arguments follow, and the package's directory, `cwd`, where tests run and which report
paths in `errata.toml` are relative to. `known` names every test executable that the package can
have, and `ruledOut` those among them that the command line's filters ruled out before building.
Of those, `testLibraries` are the libraries known to have tests, and `addedOut` the executables that
`errata.toml` adds.
-/
private def workspaceJson (needs : Array (String × String))
    (executables : Array LibraryExecutable) (added : Array AddedExecutable)
    (cwd : System.FilePath) (errataDir : String) (warnings : Array String) (invocation : String)
    (known ruledOut testLibraries addedOut : Array String) : Lean.Json :=
  let added := added.map fun e =>
    Lean.Json.mkObj [("name", Lean.Json.str e.name),
      ("command", Lean.Json.arr (e.command.map Lean.Json.str)),
      ("cwd", Lean.Json.str (match e.cwd? with
        | some d => (cwd / d).normalize.toString
        | none => cwd.toString))]
  Lean.Json.mkObj <| [
    ("protocol", Lean.toJson (1 : Nat)),
    ("needs", Lean.Json.mkObj (needs.toList.map fun (tgt, path) => (tgt, Lean.Json.str path))),
    ("executables", Lean.Json.arr <| (executables.map fun e =>
      Lean.Json.mkObj <| [("name", Lean.Json.str e.name),
        ("command", Lean.Json.arr (e.command.map Lean.Json.str)),
        ("cwd", Lean.Json.str cwd.toString)] ++
        (if e.env.isEmpty then []
          else [("env", Lean.Json.mkObj (e.env.toList.map fun (k, v) => (k, Lean.Json.str v)))]))
      ++ added),
    ("errataDir", Lean.Json.str errataDir),
    ("warnings", Lean.toJson warnings),
    ("invocation", Lean.Json.str invocation),
    ("packageDir", Lean.Json.str cwd.toString),
    ("knownExecutables", Lean.toJson known),
    ("ruledOut", Lean.toJson ruledOut),
    ("skippedTestLibraries", Lean.toJson testLibraries),
    ("skippedExecutables", Lean.toJson addedOut)
  ] ++ (if ruledOut.isEmpty then [] else [("partial-selection", Lean.Json.bool true)])

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

/-!
The driver's exit codes for the problems it finds itself, the same as the runner's
(`Errata.Runner.ExitCode`), which this file cannot import.
-/

/-- `errata.toml` or a target that a setting needs is wrong. -/
private def setupErrorCode : UInt32 := 96

/-- A test executable, the runner, or a needed target could not be built. -/
private def buildFailedCode : UInt32 := 101

/--
What the runner's planning mode says about the command line: whether it printed the usage text, the
profile, the test executables that the filters do not rule out, whether the targets of the
profile's settings are needed, whether the phases are named as they begin, and the modules whose
tests run through the interpreted product.
-/
private structure Plan where
  help : Bool
  profile : String
  executables : Array String
  needs : Bool
  phases : Bool
  interpreted : Array Lean.Name

/-- The plan that the runner wrote as JSON. -/
private def Plan.ofJson (j : Lean.Json) : Plan where
  help := (j.getObjValAs? Bool "help").toOption.getD false
  profile := (j.getObjValAs? String "profile").toOption.getD "default"
  executables := (j.getObjValAs? (Array String) "executables").toOption.getD #[]
  needs := (j.getObjValAs? Bool "needs").toOption.getD true
  phases := (j.getObjValAs? Bool "phases").toOption.getD false
  interpreted := (j.getObjValAs? (Array String) "interpreted").toOption.getD #[] |>.map moduleNameOf

-- The script's name is the one `driverInvocation` looks up.
@[test_driver]
script run (args) do
  let ws ← getWorkspace
  let some self := ws.findPackageByKey? __name__
    | IO.eprintln "error: the package that defines the Errata driver is not in the workspace"
      return 1
  -- Every argument belongs to the runner, which reads the command line.
  let (_, withArgs) ← driverInvocation ws self
  -- The usage text is printed before anything is read or built, so it needs neither a valid
  -- `errata.toml` nor a built runner. It is the runner's usage text, kept beside Errata's sources
  -- with a placeholder for the command, which a test of Errata keeps equal to the runner's.
  if (args.takeWhile (· != "--")).any (fun a => a == "--help" || a == "-h") then
    let dir := match self.findLeanLib? `Errata with
      | some lib => lib.srcDir
      | none => self.dir
    IO.print ((← IO.FS.readFile (dir / "usage.txt")).replace "INVOCATION" withArgs)
    return 0
  -- The configuration file is elaborated before the tests are built, so that a mistake in it ends
  -- Discovery at once. Lake writes `config.json` again only when `errata.toml` or `errata-config`
  -- changes. A failed build is silent, so the problems that `errata-config` reports are relayed.
  let some configExe := self.findLeanExe? `«errata-config»
    | IO.eprintln "error: the package that defines the Errata driver has no errata-config"
      return 1
  let tomlPath := ws.root.dir / "errata.toml"
  let errataOut := ws.root.dir / defaultLakeDir / "errata"
  let configFile := errataOut / "config.json"
  let configProblems ← IO.mkRef ""
  let elaborated ←
    try
      discard <| runBuild do
        (← configExe.exe.fetch).mapM fun exePath => do
          addPureTrace (← if ← tomlPath.pathExists then IO.FS.readFile tomlPath else pure "")
            "errata.toml"
          buildFileUnlessUpToDate' (text := true) configFile do
            let out ← IO.Process.output
              { cmd := exePath.toString, args := #[tomlPath.toString, configFile.toString] }
            unless out.exitCode == 0 do
              configProblems.set (out.stdout ++ out.stderr)
              error "errata-config reported problems"
      pure true
    catch _ => pure false
  unless elaborated do
    let problems ← configProblems.get
    if problems.isEmpty then
      IO.eprintln s!"error: {configFile} could not be written"
      return buildFailedCode
    IO.eprint problems
    return setupErrorCode
  let config ← match Lean.Json.parse (← IO.FS.readFile configFile) with
    | .ok j => pure j
    | .error e =>
      IO.eprintln s!"error: {configFile} is not JSON: {e}"
      return setupErrorCode
  let added := addedExecutables config
  -- The runner reads the command line, so it is built first. Its planning mode checks the command
  -- line, the profile, and the filters, and names the test executables that the filters can select
  -- by the executables' names alone; only the libraries among them are built. The candidates are
  -- the root package's libraries and the executables that `errata.toml` adds.
  let some runnerExe := self.findLeanExe? `«errata-runner»
    | IO.eprintln "error: the package that defines the Errata driver has no errata-runner"
      return 1
  let runnerPath ←
    try runBuild runnerExe.exe.fetch
    catch e =>
      IO.eprintln s!"error: the Errata runner could not be built: {e}"
      return buildFailedCode
  let libName (lib : Lake.LeanLib) : String := lib.name.toString (escape := false)
  let candidates := ws.root.leanLibs.map libName ++ added.map (·.name)
  let planFile := errataOut / "plan.json"
  let request := Lean.Json.mkObj [("config", Lean.Json.str configFile.toString),
    ("invocation", Lean.Json.str withArgs), ("executables", Lean.toJson candidates)]
  let planned ← (← IO.Process.spawn {
    cmd := runnerPath.toString
    args := #["errata-plan", request.compress, planFile.toString] ++ args.toArray
    env := #[("LEAN_ABORT_ON_PANIC", none)]
  }).wait
  unless planned == 0 do return planned
  let plan ← match Lean.Json.parse (← IO.FS.readFile planFile) with
    | .ok j => pure (Plan.ofJson j)
    | .error e =>
      IO.eprintln s!"error: {planFile} is not JSON: {e}"
      return 1
  if plan.help then return 0
  -- The targets that the selected profile's settings need are resolved before any test library is
  -- built, so that an unknown target ends Discovery at once. Listings that show no settings need
  -- no targets.
  let wanted :=
    if plan.needs then neededTargets ((config.getObjValD "profiles").getObjValD plan.profile)
    else #[]
  let mut needed : Array (String × BuildSpec) := #[]
  let mut targetProblems : Array String := #[]
  for (tgt, line, col) in wanted do
    match ← (parseTargetSpec ws tgt).toBaseIO with
    | .error e =>
      targetProblems := targetProblems.push
        s!"errata.toml:{line}:{col}: the target '{tgt}' cannot be built: {e}"
    | .ok specs =>
      match specs[0]?, specs.size with
      | some spec, 1 => needed := needed.push (tgt, spec)
      | _, n =>
        let msg := s!"errata.toml:{line}:{col}: the target '{tgt}' names {n} build results, and a \
          setting needs exactly one"
        targetProblems := targetProblems.push msg
  unless targetProblems.isEmpty do
    for p in targetProblems do IO.eprintln p
    IO.eprintln s!"error: {tomlPath} has {targetProblems.size} \
      {if targetProblems.size == 1 then "problem" else "problems"}"
    return setupErrorCode
  if plan.phases then
    IO.println "== Discovery"
    (← IO.getStdout).flush
  -- Under `--interpreted`, the libraries that hold the named modules are the selection, and no
  -- executable that `errata.toml` adds is. Each named module belongs to a library of the root
  -- package that the filters leave in.
  let interpreted := plan.interpreted
  for m in interpreted do
    let some mod := ws.findModule? m
      | IO.eprintln s!"error: no library in the workspace holds the module '{m}'"
        return setupErrorCode
    unless mod.pkg.baseName == ws.root.baseName && plan.executables.contains (libName mod.lib) do
      IO.eprintln s!"error: no selected library holds the module '{m}' that --interpreted names"
      return setupErrorCode
  let libs :=
    if interpreted.isEmpty then ws.root.leanLibs.filter (plan.executables.contains <| libName ·)
    else ws.root.leanLibs.filter fun lib =>
      interpreted.any fun m => (ws.findModule? m).any (·.lib.name == lib.name)
  let addedExes :=
    if interpreted.isEmpty then added.filter (plan.executables.contains ·.name) else #[]
  let selected := libs.map libName ++ addedExes.map (·.name)
  let ruledOut := candidates.filter (!selected.contains ·)
  -- Libraries that the filters ruled out are test libraries when a module of theirs that an earlier
  -- build left on disk records a test. Nothing is built for this check, so the summary's count
  -- covers only libraries whose modules an earlier build left on disk. Under `--interpreted`, which
  -- runs a few tests soon after an edit, no library is checked.
  let ruledOutLibs :=
    if interpreted.isEmpty then ws.root.leanLibs.filter (ruledOut.contains <| libName ·) else #[]
  let ruledOutMods ← try
      runBuild do
        let mut found : Array (String × Array System.FilePath) := #[]
        for lib in ruledOutLibs do
          let mods ← (← lib.modules.fetch).await
          found := found.push (libName lib, mods.map (·.oleanFile))
        pure (Job.pure found)
    catch _ => pure #[]
  let mut skippedTestLibs : Array String := #[]
  for (name, oleans) in ruledOutMods do
    for olean in oleans do
      unless ← olean.pathExists do continue
      if (← moduleInfo olean).hasTests then
        skippedTestLibs := skippedTestLibs.push name
        break
  -- Build every module in the selected libraries; their compiled `.olean` headers are authoritative
  -- on which modules carry tests.
  let built ← try
      let r ← runBuild do
        let mut oleanJobs := #[]
        let mut infos : Array (Lean.Name × System.FilePath) := #[]
        let mut libMods : Array (Lake.LeanLib × Array Lean.Name) := #[]
        for lib in libs do
          -- Under `--interpreted`, only the named modules of the library are built, with their
          -- imports, so a module elsewhere in the library that fails to build leaves them runnable.
          let mods ←
            if interpreted.isEmpty then (← lib.modules.fetch).await
            else pure <| interpreted.filterMap fun m =>
              (ws.findModule? m).filter (·.lib.name == lib.name)
          libMods := libMods.push (lib, mods.map (·.name))
          for m in mods do
            oleanJobs := oleanJobs.push (← m.olean.fetch)
            infos := infos.push (m.name, m.oleanFile)
        pure <| (Job.collectArray oleanJobs).map (sync := true) fun _ => (infos, libMods)
      pure (some r)
    catch e =>
      IO.eprintln s!"error: the test libraries could not be built: {e}"
      pure none
  let some (modInfos, libMods) := built | return buildFailedCode
  -- A test module is one whose `.olean` records a test.
  let mut testMods : Array Lean.Name := #[]
  for (moduleName, oleanFile) in modInfos do
    if (← moduleInfo oleanFile).hasTests then testMods := testMods.push moduleName
  -- Modules that sit under a library's roots without being reachable from them are never built, so
  -- any tests they define are left out. Libraries whose built modules record tests are checked for
  -- such modules. They are configuration slips, which the runner reports as warnings alongside the
  -- results, and the run goes ahead. Under `--interpreted`, only the named modules are built, and
  -- no library is checked.
  let mut unreachable : Array (Lake.LeanLib × Array Lean.Name) := #[]
  for (lib, mods) in if interpreted.isEmpty then libMods else #[] do
    if mods.any (testMods.contains ·) then
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
  -- Under `--interpreted`, a library's tests are those of its modules that the flag names.
  let testLibs := libMods.filterMap fun (lib, mods) =>
    let own := mods.filter fun m =>
      testMods.contains m && (interpreted.isEmpty || interpreted.contains m)
    if own.isEmpty then none else some (lib, own)
  -- The interpreted product needs no generated main.
  for (lib, mods) in if interpreted.isEmpty then testLibs else #[] do
    let file := Lean.modToFilePath (errataRunnerSrcDir lib.pkg) (errataMainModule lib) "lean"
    let src := mainSource lib.pkg.prettyName mods
    if let some parent := file.parent then IO.FS.createDirAll parent
    let changed ← if ← file.pathExists then pure ((← IO.FS.readFile file) != src) else pure true
    if changed then IO.FS.writeFile file src
  -- Libraries' test executables are named after their libraries, so the executables that the
  -- configuration file adds must have names that no library of the package has.
  for e in added do
    if ws.root.leanLibs.any (libName · == e.name) then
      IO.eprintln s!"errata.toml:{e.line}:{e.col}: the [[executable]] name '{e.name}' is the name \
        of a library of the package"
      return setupErrorCode
  -- Test executables find Errata's shell harness in the directory of Errata's sources.
  let errataDir ← match self.findLeanLib? `Errata with
    | some lib => IO.FS.realPath lib.srcDir
    | none => IO.FS.realPath self.dir
  let rootDir ← IO.FS.realPath ws.root.dir
  let workspaceFile := errataOut / "workspace.json"
  let some interpreterExe := self.findLeanExe? `«errata-interpret»
    | IO.eprintln "error: the package that defines the Errata driver has no errata-interpret"
      return 1
  -- Build the test executables and every target that a setting of the selected profile needs, then
  -- `workspace.json`. Lake writes it again when `config.json`, the discovery results, the
  -- executables, or a needed target change: each needed target's trace flows into the continuation
  -- that writes the file.
  try
    runBuild do
      -- Each library's test executable, or under `--interpreted` the interpreted product with the
      -- library's modules.
      let libExesJob : Job (Array LibraryExecutable) ←
        if interpreted.isEmpty then do
          let exeJobs ← testLibs.mapM fun (lib, _) => (lib.facet `errataExe).fetch
          (Job.collectArray exeJobs).mapM fun exePaths => do
            let mut out : Array LibraryExecutable := #[]
            for ((lib, _), path) in testLibs.zip exePaths do
              let command := #[(← IO.FS.realPath path).toString]
              out := out.push { name := libName lib, command }
            return out
        else do
          let interpreterJob ← interpreterExe.exe.fetch
          interpreterJob.mapM fun path => do
            let path ← IO.FS.realPath path
            return testLibs.map fun (lib, mods) =>
              interpretedExecutable ws path (libName lib) mods interpreted
      let needJobs ← needed.mapM fun (_, spec) => spec.query .text
      (Job.collectArray needJobs).bindM fun needValues => do
      libExesJob.mapM fun executables => do
        let needs := needed.zipWith (fun (tgt, _) value => (tgt, value)) needValues
        -- Tests run from the root package's directory, where `lake test` runs.
        let content := (workspaceJson needs executables addedExes rootDir errataDir.toString
          driverWarnings withArgs candidates ruledOut skippedTestLibs
          (added.map (·.name) |>.filter ruledOut.contains)).pretty ++ "\n"
        addPureTrace (← IO.FS.readFile configFile) "config.json"
        addPureTrace content "workspace.json"
        buildFileUnlessUpToDate' (text := true) workspaceFile do
          IO.FS.createDirAll errataOut
          IO.FS.writeFile workspaceFile content
  catch e =>
    IO.eprintln s!"error: the test executables could not be built: {e}"
    return buildFailedCode
  -- The runner's standard input is a lifeline that the driver holds, and `ERRATA_LIFELINE` asks the
  -- runner to end its tests when that pipe closes. A driver started with
  -- `ERRATA_DRIVER_LIFELINE=1`, as the editor widget starts it, hands its own standard input on as
  -- the runner's lifeline, so the runner ends when the driver's parent does. The variable stops at
  -- the driver, so a driver that a test starts holds a lifeline of its own. The driver removes
  -- `LEAN_ABORT_ON_PANIC` from the runner's environment, and the runner sets it for every test
  -- executable.
  let handsOnLifeline := (← IO.getEnv "ERRATA_DRIVER_LIFELINE") == some "1"
  let child ← IO.Process.spawn {
    cmd := runnerPath.toString
    args := #[configFile.toString, workspaceFile.toString] ++ args.toArray
    stdin := if handsOnLifeline then .inherit else .piped
    env := #[("LEAN_ABORT_ON_PANIC", none), ("ERRATA_LIFELINE", some "1"),
      ("ERRATA_DRIVER_LIFELINE", none)]
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

/--
Runs a manual's executable to write its multi-page HTML into a directory of the build directory, and
returns the site's directory. The browser tests take such a site as their `siteDir` setting.
-/
def buildManualSite (pkg : Package) (exe : Job System.FilePath) (name : String) :
    FetchM (Job System.FilePath) :=
  exe.mapM fun exeFile => do
    let dir := pkg.buildDir / "sites" / name
    let index := dir / "html-multi" / "index.html"
    buildFileUnlessUpToDate' index do
      if ← dir.pathExists then IO.FS.removeDirAll dir
      proc { cmd := exeFile.toString, args := #["--output", dir.toString, "--without-html-single"] }
    return dir / "html-multi"

-- The user's guide as a multi-page HTML site, for the browser tests of search, navigation,
-- redirects, and KaTeX.
target usersGuideSite pkg : System.FilePath := do
  buildManualSite pkg (← usersguide.fetch) "usersguide"

-- The package documentation example as a multi-page HTML site, for its browser tests.
target packageManualSite pkg : System.FilePath := do
  buildManualSite pkg (← packagedocs.fetch) "package-manual"

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
