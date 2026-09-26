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

/-- What the `.olean` file `oleanFile` records about its module. -/
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
every helper and fixture they reach to the Lean harness.
-/
private def mainSource (pkg : String) (mods : Array Lean.Name) : String :=
  let imports := "\n".intercalate <| "import Errata" :: mods.toList.map (s!"import {·}")
  s!"{imports}\n\n\
    def main (args : List String) : IO UInt32 :=\n  \
    Errata.Harness.main (getAllTests% {pkg.quote} {" ".intercalate (mods.toList.map (·.toString))}) \
      args (helpers := getAllHelpers%) (fixtures := getAllFixtures%)\n"

/-!
The configuration file, `errata.toml`, which `errata-config` validates and elaborates into
`.lake/errata/config.json`. The driver reads from that file the needs' targets and the test
executables that the file adds.
-/

/-- An object's fields, or none when the value is not an object. -/
private def jsonFields (j : Lean.Json) : Array (String × Lean.Json) :=
  match j.getObj? with
  | .ok obj => obj.toArray
  | .error _ => #[]

/-- A natural-number field of an object, or zero. -/
private def jsonNat (j : Lean.Json) (key : String) : Nat :=
  (j.getObjValAs? Nat key).toOption.getD 0

/-- A need, as `config.json` and the plan record it. -/
private structure DriverNeed where
  /-- The need's name. -/
  name : String
  /-- The Lake target, in the workspace's target syntax. -/
  spec : String
  /-- The line of the target in `errata.toml`. -/
  line : Nat
  /-- The column of the target in `errata.toml`. -/
  col : Nat

/-- The needs of the `[needs]` table of `config.json`, in the file's order. -/
private def needsTable (config : Lean.Json) : Array DriverNeed :=
  match config.getObjValD "needs" with
  | .arr ns => ns.filterMap fun n => do
    let name ← (n.getObjValAs? String "name").toOption
    let spec ← (n.getObjValAs? String "target").toOption
    return { name, spec, line := jsonNat n "line", col := jsonNat n "col" }
  | _ => #[]

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

/-- A library's test executable, as `executables.json` records it. -/
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
The modules of the libraries `libs`, as JSON: each library's name, its roots, and its globs in
Lake's notation (`M`, `M.+`, or `M.*`), from which the editor widget finds the library, and so the
test executable, of a test's module.
-/
private def libraryModulesJson (libs : Array Lake.LeanLib) : Lean.Json :=
  Lean.Json.arr <| libs.map fun lib => Lean.Json.mkObj [
    ("name", Lean.Json.str (lib.name.toString (escape := false))),
    ("roots", Lean.toJson (lib.config.roots.map (·.toString))),
    ("globs", Lean.toJson (lib.config.globs.map (·.toString)))]

/--
What the workspace contributes to the plan, `executables.json`, as JSON: the libraries' test
executables and the executables `added` that `errata.toml` adds, the directory of Errata's sources,
the driver's warnings, the command that the runner's arguments follow, the package's directory,
`cwd`, where tests run and which report paths in `errata.toml` are relative to, and the modules of
the package's libraries, `libraries`. `known` names every test executable that the package can
have, and `ruledOut` those among them that the command line's filters ruled out before building. Of
those, `testLibraries` are the libraries known to have tests, and `addedOut` the executables that
`errata.toml` adds. The selection is partial when some executable is ruled out or when `someTests`
says that the executables run only some of their tests.
-/
private def executablesJson
    (executables : Array LibraryExecutable) (added : Array AddedExecutable)
    (cwd : System.FilePath) (errataDir : String) (warnings : Array String) (invocation : String)
    (known ruledOut testLibraries addedOut : Array String) (someTests : Bool)
    (libraries : Lean.Json) : Lean.Json :=
  let added := added.map fun e =>
    Lean.Json.mkObj [("name", Lean.Json.str e.name),
      ("command", Lean.Json.arr (e.command.map Lean.Json.str)),
      ("cwd", Lean.Json.str (match e.cwd? with
        | some d => (cwd / d).normalize.toString
        | none => cwd.toString))]
  Lean.Json.mkObj <| [
    ("protocol", Lean.toJson (1 : Nat)),
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
    ("skippedExecutables", Lean.toJson addedOut),
    ("libraries", libraries)
  ] ++ (if ruledOut.isEmpty && !someTests then [] else [("partial-selection", Lean.Json.bool true)])

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

/-- `errata.toml` or a need's target is wrong, or a need's target could not be built. -/
private def setupErrorCode : UInt32 := 96

/-- A test executable or the runner could not be built. -/
private def buildFailedCode : UInt32 := 101

/--
What the runner's `check` subcommand says about the command line: whether it printed the usage
text, the command, the profile, the test executables that the filters can select, whether the
phases are named as they begin, and the modules whose tests run through the interpreted product.
-/
private structure CheckedCommandLine where
  help : Bool
  command : String
  profile : String
  executables : Array String
  phases : Bool
  interpreted : Array Lean.Name

/-- What the runner's `check` subcommand wrote as JSON. -/
private def CheckedCommandLine.ofJson (j : Lean.Json) : CheckedCommandLine where
  help := (j.getObjValAs? Bool "help").toOption.getD false
  command := (j.getObjValAs? String "command").toOption.getD "run"
  profile := (j.getObjValAs? String "profile").toOption.getD "default"
  executables := (j.getObjValAs? (Array String) "executables").toOption.getD #[]
  phases := (j.getObjValAs? Bool "phases").toOption.getD false
  interpreted := (j.getObjValAs? (Array String) "interpreted").toOption.getD #[] |>.map moduleNameOf

/-- A new run identifier: 64 random bits, written as 16 hexadecimal digits. -/
private def drawRunId : IO String := do
  let bytes ← IO.getRandomBytes 8
  let hex (n : Nat) : String := String.singleton (Nat.digitChar n)
  return bytes.foldl (init := "") fun acc b => acc ++ hex (b.toNat / 16) ++ hex (b.toNat % 16)

/-- The age past which the run directories that earlier invocations left are removed: one day. -/
private def staleRunAgeSecs : Int := 24 * 60 * 60

/--
Removes the run directories under {lit}`runsDir` that last changed more than a day before
{lit}`current`, the directory of this invocation's run, whose time stands for the present.
-/
private def removeStaleRunDirs (runsDir current : System.FilePath) : IO Unit := do
  let now := (← current.metadata).modified.sec
  for entry in ← runsDir.readDir do
    if entry.path == current then continue
    try
      if now - (← entry.path.metadata).modified.sec > staleRunAgeSecs then
        IO.FS.removeDirAll entry.path
    catch _ => pure ()

/-- Writes a file whole: to a file beside it, then renamed into place. -/
private def writeFileAtomically (file : System.FilePath) (content : String) : IO Unit := do
  let staged := file.addExtension s!"{← IO.monoNanosNow}"
  IO.FS.writeFile staged content
  IO.FS.rename staged file

/-- A need that the plan names, with the tests that reach it, each written as `exe: test`. -/
private structure PlannedNeed where
  need : DriverNeed
  tests : Array String

/-- The needs that the plan names. -/
private def plannedNeeds (plan : Lean.Json) : Array PlannedNeed :=
  match plan.getObjValD "needs" with
  | .arr ns => ns.filterMap fun n => do
    let name ← (n.getObjValAs? String "name").toOption
    let spec ← (n.getObjValAs? String "target").toOption
    let tests := match n.getObjValD "tests" with
      | .arr ts => ts.filterMap fun t => do
        return s!"{← (t.getObjValAs? String "exe").toOption}: \
          {← (t.getObjValAs? String "test").toOption}"
      | _ => #[]
    return { need := { name, spec, line := jsonNat n "line", col := jsonNat n "col" }, tests }
  | _ => #[]

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
  let configOut ←
    if configFile.isAbsolute then pure configFile else (· / configFile) <$> IO.currentDir
  let configProblems ← IO.mkRef ""
  let elaborated ←
    try
      discard <| runBuild do
        (← configExe.exe.fetch).mapM fun exePath => do
          addPureTrace (← if ← tomlPath.pathExists then IO.FS.readFile tomlPath else pure "")
            "errata.toml"
          buildFileUnlessUpToDate' (text := true) configFile do
            -- `errata-config` runs in the package's directory and reads the file as `errata.toml`,
            -- the name that its problems and its filters' positions show, as the driver's own
            -- messages do.
            let out ← IO.Process.output
              { cmd := exePath.toString, args := #["errata.toml", configOut.toString],
                cwd := ws.root.dir }
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
  -- Each need's target is resolved before any test library is built, so that a target that the
  -- workspace lacks ends Discovery at once. Only the needs that the plan names are built.
  let mut needSpecs : Array (String × BuildSpec) := #[]
  let mut targetProblems : Array String := #[]
  for n in needsTable config do
    let tgt := n.spec
    match ← (parseTargetSpec ws tgt).toBaseIO with
    | .error e =>
      targetProblems := targetProblems.push
        s!"errata.toml:{n.line}:{n.col}: the target '{tgt}' of the need '{n.name}' cannot be \
          built: {e}"
    | .ok specs =>
      match specs[0]?, specs.size with
      | some spec, 1 => needSpecs := needSpecs.push (n.name, spec)
      | _, k =>
        let msg := s!"errata.toml:{n.line}:{n.col}: the target '{tgt}' of the need '{n.name}' \
          names {k} build results, and a need names exactly one"
        targetProblems := targetProblems.push msg
  unless targetProblems.isEmpty do
    for p in targetProblems do IO.eprintln p
    IO.eprintln s!"error: {tomlPath} has {targetProblems.size} \
      {if targetProblems.size == 1 then "problem" else "problems"}"
    return setupErrorCode
  -- The runner reads the command line, so it is built first. Its `check` subcommand checks the
  -- command line, the profile, and the filters, and names the test executables that the filters can
  -- select by the executables' names alone; only the libraries among them are built. The candidates
  -- are the root package's libraries and the executables that `errata.toml` adds.
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
  -- The run's identifier is drawn once, here, and reaches the runner's `plan` and `run` through
  -- `ERRATA_RUN_ID`. Each invocation keeps its files in a directory named by it and removes the
  -- directory when it ends, so invocations in one workspace at once read only their own files.
  -- Invocations that are killed leave their directories behind. Each invocation removes those
  -- older than a day and leaves the recent ones, which include those of invocations that run at
  -- once.
  let runId ← drawRunId
  let runsDir := errataOut / "runs"
  let runDir := runsDir / runId
  IO.FS.createDirAll runDir
  removeStaleRunDirs runsDir runDir
  try
    let checkFile := runDir / "command-line.json"
    let request := Lean.Json.mkObj [("config", Lean.Json.str configFile.toString),
      ("invocation", Lean.Json.str withArgs), ("executables", Lean.toJson candidates)]
    let checkedCode ← (← IO.Process.spawn {
      cmd := runnerPath.toString
      args := #["check", request.compress, checkFile.toString] ++ args.toArray
      env := #[("LEAN_ABORT_ON_PANIC", none)]
    }).wait
    unless checkedCode == 0 do return checkedCode
    let checked ← match Lean.Json.parse (← IO.FS.readFile checkFile) with
      | .ok j => pure (CheckedCommandLine.ofJson j)
      | .error e =>
        IO.eprintln s!"error: {checkFile} is not JSON: {e}"
        return 1
    if checked.help then return 0
    if checked.phases then
      IO.println "== Discovery"
      (← IO.getStdout).flush
    -- Under `--interpreted`, the libraries that hold the named modules are the selection, and no
    -- executable that `errata.toml` adds is. Each named module belongs to a library of the root
    -- package that the filters leave in.
    let interpreted := checked.interpreted
    for m in interpreted do
      let some mod := ws.findModule? m
        | IO.eprintln s!"error: no library in the workspace holds the module '{m}'"
          return setupErrorCode
      unless mod.pkg.baseName == ws.root.baseName &&
          checked.executables.contains (libName mod.lib) do
        IO.eprintln s!"error: no selected library holds the module '{m}' that --interpreted names"
        return setupErrorCode
    let libs :=
      if interpreted.isEmpty then
        ws.root.leanLibs.filter (checked.executables.contains <| libName ·)
      else ws.root.leanLibs.filter fun lib =>
        interpreted.any fun m => (ws.findModule? m).any (·.lib.name == lib.name)
    let addedExes :=
      if interpreted.isEmpty then added.filter (checked.executables.contains ·.name) else #[]
    let selected := libs.map libName ++ addedExes.map (·.name)
    let ruledOut := candidates.filter (!selected.contains ·)
    -- Libraries that the filters ruled out are test libraries when a module of theirs that an
    -- earlier build left on disk records a test. Nothing is built for this check, so the summary's
    -- count covers only libraries whose modules an earlier build left on disk. Under
    -- `--interpreted`, which runs a few tests soon after an edit, no library is checked.
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
    -- Build every module in the selected libraries; their compiled `.olean` headers are
    -- authoritative on which modules record tests.
    let built ← try
        let r ← runBuild do
          let mut oleanJobs := #[]
          let mut infos : Array (Lean.Name × System.FilePath) := #[]
          let mut libMods : Array (Lake.LeanLib × Array Lean.Name) := #[]
          for lib in libs do
            -- Under `--interpreted`, only the named modules of the library are built, with their
            -- imports, so a module elsewhere in the library that fails to build leaves them
            -- runnable.
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
    -- Modules that sit under a library's roots without being reachable from them are never built,
    -- so any tests they define are left out. Libraries whose built modules record tests are checked
    -- for such modules. They are configuration slips, which the runner reports as warnings
    -- alongside the results, and the run goes ahead. Under `--interpreted`, only the named modules
    -- are built, and no library is checked.
    let mut unreachable : Array (Lake.LeanLib × Array Lean.Name) := #[]
    for (lib, mods) in if interpreted.isEmpty then libMods else #[] do
      if mods.any (testMods.contains ·) then
        let known := mods.foldl (init := Lean.NameSet.empty) (·.insert ·)
        let missed ← unreachableModules lib known
        unless missed.isEmpty do unreachable := unreachable.push (lib, missed)
    let mut driverWarnings : Array String := #[]
    unless unreachable.isEmpty do
      let lines := unreachable.flatMap fun (lib, mods) =>
        mods.map fun mod => s!"  {lib.name}: {mod}"
      driverWarnings := driverWarnings.push <|
        s!"these modules are not reachable from their library's roots, so any tests they define \
          are not discovered. Import them from a root, or widen the library's `globs` \
          (e.g. `globs := #[Glob.andSubmodules `Root]`):\n{"\n".intercalate lines.toList}"
    -- Each library with tests gets a test executable, whose main is generated in its package's
    -- Lake directory. The main changes only when the library's test modules do, so Lake's own
    -- traces rebuild what depends on it.
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
        IO.eprintln s!"errata.toml:{e.line}:{e.col}: the [[executable]] name '{e.name}' is the \
          name of a library of the package"
        return setupErrorCode
    -- Test executables find Errata's shell harness in the directory of Errata's sources.
    let errataDir ← match self.findLeanLib? `Errata with
      | some lib => IO.FS.realPath lib.srcDir
      | none => IO.FS.realPath self.dir
    let rootDir ← IO.FS.realPath ws.root.dir
    let executablesFile := runDir / "executables.json"
    let planFile := runDir / "plan.json"
    let workspaceFile := runDir / "workspace.json"
    let some interpreterExe := self.findLeanExe? `«errata-interpret»
      | IO.eprintln "error: the package that defines the Errata driver has no errata-interpret"
        return 1
    -- Build the test executables, then write `executables.json`, which hands them to the runner's
    -- `plan` subcommand. The editor widget reads the workspace's latest copy of the file, beside
    -- `config.json`, for the modules of the package's libraries.
    let executables? ← try
      let executables ← runBuild do
        -- Each library's test executable, or under `--interpreted` the interpreted product with
        -- the library's modules.
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
        pure libExesJob
      pure (some executables)
    catch e =>
      IO.eprintln s!"error: the test executables could not be built: {e}"
      pure none
    let some executables := executables? | return buildFailedCode
    -- Tests run from the root package's directory, where `lake test` runs.
    let content := (executablesJson executables addedExes rootDir errataDir.toString
      driverWarnings withArgs candidates ruledOut skippedTestLibs
      (added.map (·.name) |>.filter ruledOut.contains) (!interpreted.isEmpty)
      (libraryModulesJson ws.root.leanLibs)).pretty ++ "\n"
    IO.FS.writeFile executablesFile content
    writeFileAtomically (errataOut / "executables.json") content
    -- The runner's standard input is a lifeline that the driver holds, and `ERRATA_LIFELINE` asks
    -- the runner to end its listings or its tests when that pipe closes. A driver started with
    -- `ERRATA_DRIVER_LIFELINE=1`, as the editor widget starts it, hands its own standard input on
    -- as the runner's lifeline, so the runner ends when the driver's parent does. The variable
    -- stops at the driver, so a driver that a test starts holds a lifeline of its own. The driver
    -- removes `LEAN_ABORT_ON_PANIC` from the runner's environment, and the runner sets it for every
    -- test executable. The runner has a session of its own, so an interrupt from the terminal
    -- reaches the driver alone, and the runner learns of it when the lifeline closes, clears its
    -- progress display, and cancels the run in order.
    let handsOnLifeline := (← IO.getEnv "ERRATA_DRIVER_LIFELINE") == some "1"
    let runnerProcess (subcommand : Array String) : IO.Process.SpawnArgs := {
      cmd := runnerPath.toString
      args := subcommand ++ args.toArray
      stdin := if handsOnLifeline then .inherit else .piped
      setsid := true
      env := #[("LEAN_ABORT_ON_PANIC", none), ("ERRATA_LIFELINE", some "1"),
        ("ERRATA_DRIVER_LIFELINE", none), ("ERRATA_RUN_ID", some runId)]
    }
    -- The runner's `plan` subcommand runs the List phase and writes the plan on every run.
    let planned ← (← IO.Process.spawn (runnerProcess
      #["plan", configFile.toString, executablesFile.toString, planFile.toString])).wait
    unless planned == 0 do return planned
    -- Listings print the plan and build no need.
    if checked.command == "list" then
      let child ← IO.Process.spawn {
        cmd := runnerPath.toString
        args := #["list", planFile.toString] ++ args.toArray
        env := #[("LEAN_ABORT_ON_PANIC", none)] }
      return (← child.wait)
    let plan ← match Lean.Json.parse (← IO.FS.readFile planFile) with
      | .ok j => pure j
      | .error e =>
        IO.eprintln s!"error: {planFile} is not JSON: {e}"
        return 1
    -- Build the needs that the plan names, then write `workspace.json`, which gives each need's
    -- value. Lake builds each need's target again only when its inputs change.
    let needs := plannedNeeds plan
    let needJobs ← IO.mkRef (#[] : Array (String × Job String))
    -- A plan that names no need has nothing to build.
    let values? ← if needs.isEmpty then pure (some #[]) else try
      let values ← runBuild do
        let mut jobs : Array (Job String) := #[]
        for n in needs do
          if let some (_, spec) := needSpecs.find? (·.1 == n.need.name) then
            let job ← spec.query .text
            jobs := jobs.push job
            needJobs.modify (·.push (n.need.name, job))
        pure (Job.collectArray jobs)
      pure (some values)
    catch _ => pure none
    let some values := values? | do
      -- A need failed when its job failed, or when its target could not even start a job.
      let started ← needJobs.get
      let failed ← needs.filterM fun n => do
        match started.find? (·.1 == n.need.name) with
        | some (_, job) => return (← job.wait?).isNone
        | none => return true
      for n in failed do
        IO.eprintln s!"errata.toml:{n.need.line}:{n.need.col}: the target '{n.need.spec}' of \
          the need '{n.need.name}' could not be built, and these tests reach it:\n  \
          {"\n  ".intercalate n.tests.toList}"
      return setupErrorCode
    let built := (← needJobs.get).map (·.1)
    IO.FS.writeFile workspaceFile <| (Lean.Json.mkObj [("protocol", Lean.toJson (1 : Nat)),
      ("needs", Lean.Json.mkObj ((built.zip values).toList.map fun (n, v) =>
        (n, Lean.Json.str v)))]).pretty ++ "\n"
    let child ← IO.Process.spawn (runnerProcess
      #["run", planFile.toString, workspaceFile.toString])
    child.wait
  finally
    try IO.FS.removeDirAll runDir catch _ => pure ()

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
returns the site's directory. The browser suites' site fixtures take such a site as a setting.
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
