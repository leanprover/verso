import Lake
import Lake.CLI.Build
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

-- Everything below is Errata's own implementation: its library, the runner, the widget's
-- single-test program, its self-tests, the generated test executables, and the `lake test` driver.
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

/-! The configuration file, `errata.toml`, which the driver validates and elaborates. -/

/-- A problem with `errata.toml`, at the value that it concerns. -/
private structure TomlProblem where
  ref : Lean.Syntax
  msg : String

/-- Validation of `errata.toml`, which gathers every problem it finds. -/
private abbrev TomlM := StateM (Array TomlProblem)

private def tomlProblem (ref : Lean.Syntax) (msg : String) : TomlM Unit :=
  modify (·.push ⟨ref, msg⟩)

private def tomlKey (k : Lean.Name) : String := k.toString (escape := false)

/-- What kind of TOML value a value is, for messages. -/
private def tomlKind : Lake.Toml.Value → String
  | .string .. => "a string"
  | .integer .. => "an integer"
  | .float .. => "a float"
  | .boolean .. => "a boolean"
  | .dateTime .. => "a date-time"
  | .array .. => "an array"
  | .table .. => "a table"

/-- Reports every key of a table outside `known`. -/
private def tomlCheckKeys (context : String) (known : List String) (t : Lake.Toml.Table) :
    TomlM Unit := do
  for (k, v) in t.items do
    unless known.contains (tomlKey k) do
      tomlProblem v.ref s!"unknown key '{tomlKey k}' in {context}"

/-- A filter's text, and the position of its first character in `errata.toml`. -/
private structure TomlFilter where
  text : String
  line : Nat
  col : Nat

/-- The value of a setting: a string, or the Lake target whose result is its value. -/
private inductive TomlSetting where
  | value (s : String)
  | needs (tgt : String) (ref : Lean.Syntax)

/-- A per-test override of a profile. -/
private structure TomlOverride where
  filter : TomlFilter
  timeoutMs? : Option Nat := none
  fixtureTimeoutMs? : Option Nat := none
  gracePeriodMs? : Option Nat := none
  slowAfterMs? : Option Nat := none
  updateGolden? : Option Bool := none
  settings : Array (String × TomlSetting) := #[]

/-- A profile, as the file gives it and, after inheritance, with its ancestors' values merged. -/
private structure TomlProfile where
  name : String
  ref : Lean.Syntax := .missing
  inherits? : Option (String × Lean.Syntax) := none
  timeoutMs? : Option Nat := none
  fixtureTimeoutMs? : Option Nat := none
  gracePeriodMs? : Option Nat := none
  slowAfterMs? : Option Nat := none
  jobs? : Option Nat := none
  updateGolden? : Option Bool := none
  settings : Array (String × TomlSetting) := #[]
  overrides : Array TomlOverride := #[]
  defaultFilter? : Option TomlFilter := none

/-- A test executable that `[[executable]]` adds. -/
private structure TomlExecutable where
  name : String
  ref : Lean.Syntax
  command : Array String
  cwd? : Option String

/-- What `errata.toml` says, validated. -/
private structure TomlConfig where
  defaultFilter? : Option TomlFilter := none
  executables : Array TomlExecutable := #[]
  profiles : Array TomlProfile := #[]

/--
A duration, `N` followed by `ms`, `s`, `m`, or `h`, in milliseconds. Whitespace around it is ignored,
as the runner ignores it.
-/
private def tomlDurationMs? (s : String) : Option Nat :=
  let s := s.trimAscii.copy
  let num (d : String) (scale : Nat) := d.toNat?.map (· * scale)
  if let some d := s.dropSuffix? "ms" then num d.copy 1
  else if let some d := s.dropSuffix? "s" then num d.copy 1000
  else if let some d := s.dropSuffix? "m" then num d.copy 60000
  else if let some d := s.dropSuffix? "h" then num d.copy 3600000
  else none

private def tomlDuration (key : String) (v : Lake.Toml.Value) (positive := false) :
    TomlM (Option Nat) := do
  match v with
  | .string ref s =>
    match tomlDurationMs? s with
    | some ms =>
      if positive && ms == 0 then
        tomlProblem ref s!"'{key}' must be longer than zero"
        return none
      return some ms
    | none =>
      tomlProblem ref s!"'{key}' must be a duration, such as \"90s\", \"10m\", \"500ms\", or \"1h\", \
        and it is {s.quote}"
      return none
  | other =>
    tomlProblem other.ref s!"'{key}' must be a duration string, and it is {tomlKind other}"
    return none

private def tomlString (key : String) (v : Lake.Toml.Value) : TomlM (Option String) := do
  match v with
  | .string _ s => return some s
  | other =>
    tomlProblem other.ref s!"'{key}' must be a string, and it is {tomlKind other}"
    return none

private def tomlBool (key : String) (v : Lake.Toml.Value) : TomlM (Option Bool) := do
  match v with
  | .boolean _ b => return some b
  | other =>
    tomlProblem other.ref s!"'{key}' must be a boolean, and it is {tomlKind other}"
    return none

/--
A filter string, with the position of its first character after the string's opening quotes. A
multi-line string whose opening quotes end their line starts on the next line, since TOML drops that
newline.
-/
private def tomlFilterOf (fileMap : Lean.FileMap) (key : String) (v : Lake.Toml.Value) :
    TomlM (Option TomlFilter) := do
  match v with
  | .string ref text =>
    let some pos := ref.getPos? | return some { text, line := 0, col := 0 }
    let p := fileMap.toPosition pos
    let slice (start len : Nat) : String :=
      ({ str := fileMap.source, startPos := ⟨pos.byteIdx + start⟩,
         stopPos := ⟨pos.byteIdx + start + len⟩ } : Substring.Raw).toString
    let opening := slice 0 3
    if opening == "\"\"\"" || opening == "'''" then
      if slice 3 1 == "\n" || slice 3 2 == "\r\n" then
        return some { text, line := p.line + 1, col := 0 }
      return some { text, line := p.line, col := p.column + 3 }
    return some { text, line := p.line, col := p.column + 1 }
  | other =>
    tomlProblem other.ref s!"'{key}' must be a string, and it is {tomlKind other}"
    return none

/--
The settings table. A setting's name is its fully qualified declaration name, written as a quoted
dotted key (`"A.B.c" = …`), a bare dotted key, or a key in a nested table (`[….settings.A.B]` with
`c = …`); nested tables are flattened into dotted names. Each value is a string or
`{ needs = "target" }`, with no coercion: a table with the key `needs` is a needed target, and any other
table holds more of the name.
-/
private partial def tomlSettings (v : Lake.Toml.Value) : TomlM (Array (String × TomlSetting)) := do
  let .table _ t := v
    | tomlProblem v.ref s!"'settings' must be a table, and it is {tomlKind v}"
      return #[]
  let shape := "a string or { needs = \"target\" }"
  let rec go (namePrefix : String) (t : Lake.Toml.Table) (out : Array (String × TomlSetting)) :
      TomlM (Array (String × TomlSetting)) := do
    let mut out := out
    for (k, sv) in t.items do
      let name := if namePrefix.isEmpty then tomlKey k else s!"{namePrefix}.{tomlKey k}"
      match sv with
      | .string ref s =>
        if out.any (·.1 == name) then tomlProblem ref s!"the setting '{name}' is given twice"
        else out := out.push (name, .value s)
      | .table ref inner =>
        match inner.find? `needs with
        | some (.string r tgt) =>
          if inner.items.size != 1 then
            tomlProblem ref s!"the setting '{name}' must be {shape}, and its table has keys \
              besides 'needs'"
          else if out.any (·.1 == name) then tomlProblem ref s!"the setting '{name}' is given twice"
          else out := out.push (name, .needs tgt r)
        | some other =>
          tomlProblem other.ref s!"'needs' must name a Lake target as a string, and it is \
            {tomlKind other}"
        | none =>
          if inner.items.isEmpty then
            tomlProblem ref s!"the setting '{name}' must be {shape}, and it is an empty table"
          else out ← go name inner out
      | other =>
        tomlProblem other.ref s!"the setting '{name}' must be {shape}, and it is {tomlKind other}"
    return out
  go "" t #[]

/-- The keys of an override. -/
private def overrideKeys : List String :=
  ["filter", "timeout", "fixture-timeout", "grace-period", "slow-after", "update-golden", "settings"]

private def tomlOverride (fileMap : Lean.FileMap) (profile : String) (v : Lake.Toml.Value) :
    TomlM (Option TomlOverride) := do
  let .table ref t := v
    | tomlProblem v.ref s!"each override of the profile '{profile}' must be a table, and it is \
        {tomlKind v}"
      return none
  tomlCheckKeys s!"an override of the profile '{profile}'" overrideKeys t
  let some filterValue := t.find? `filter
    | tomlProblem ref s!"an override of the profile '{profile}' needs a 'filter'"
      return none
  let some filter ← tomlFilterOf fileMap "filter" filterValue | return none
  let mut o : TomlOverride := { filter }
  if let some x := t.find? `timeout then o := { o with timeoutMs? := ← tomlDuration "timeout" x true }
  if let some x := t.find? `«fixture-timeout» then
    o := { o with fixtureTimeoutMs? := ← tomlDuration "fixture-timeout" x true }
  if let some x := t.find? `«grace-period» then
    o := { o with gracePeriodMs? := ← tomlDuration "grace-period" x }
  if let some x := t.find? `«slow-after» then
    o := { o with slowAfterMs? := ← tomlDuration "slow-after" x }
  if let some x := t.find? `«update-golden» then
    o := { o with updateGolden? := ← tomlBool "update-golden" x }
  if let some x := t.find? `settings then o := { o with settings := ← tomlSettings x }
  return some o

/-- The keys of a profile. -/
private def profileKeys : List String :=
  ["inherits", "timeout", "fixture-timeout", "grace-period", "slow-after", "jobs", "update-golden",
    "settings", "override", "default-filter"]

private def tomlProfile (fileMap : Lean.FileMap) (name : String) (v : Lake.Toml.Value) :
    TomlM (Option TomlProfile) := do
  let .table ref t := v
    | tomlProblem v.ref s!"the profile '{name}' must be a table, and it is {tomlKind v}"
      return none
  tomlCheckKeys s!"the profile '{name}'" profileKeys t
  let mut p : TomlProfile := { name, ref }
  if let some x := t.find? `inherits then
    if let some parent ← tomlString "inherits" x then p := { p with inherits? := some (parent, x.ref) }
  if let some x := t.find? `timeout then p := { p with timeoutMs? := ← tomlDuration "timeout" x true }
  if let some x := t.find? `«fixture-timeout» then
    p := { p with fixtureTimeoutMs? := ← tomlDuration "fixture-timeout" x true }
  if let some x := t.find? `«grace-period» then
    p := { p with gracePeriodMs? := ← tomlDuration "grace-period" x }
  if let some x := t.find? `«slow-after» then
    p := { p with slowAfterMs? := ← tomlDuration "slow-after" x }
  if let some x := t.find? `jobs then
    match x with
    | .integer _ n =>
      if n > 0 then p := { p with jobs? := some n.toNat }
      else tomlProblem x.ref s!"'jobs' must be a positive integer, and it is {n}"
    | other => tomlProblem other.ref s!"'jobs' must be a positive integer, and it is {tomlKind other}"
  if let some x := t.find? `«update-golden» then
    p := { p with updateGolden? := ← tomlBool "update-golden" x }
  if let some x := t.find? `settings then p := { p with settings := ← tomlSettings x }
  if let some x := t.find? `override then
    match x with
    | .array _ items =>
      let mut overrides := #[]
      for item in items do
        if let some o ← tomlOverride fileMap name item then overrides := overrides.push o
      p := { p with overrides }
    | other =>
      tomlProblem other.ref s!"'override' must be an array of tables, written [[profile.{name}.override]], \
        and it is {tomlKind other}"
  if let some x := t.find? `«default-filter» then
    p := { p with defaultFilter? := ← tomlFilterOf fileMap "default-filter" x }
  return some p

private def tomlExecutable (v : Lake.Toml.Value) : TomlM (Option TomlExecutable) := do
  let .table ref t := v
    | tomlProblem v.ref s!"each [[executable]] must be a table, and it is {tomlKind v}"
      return none
  tomlCheckKeys "an [[executable]]" ["name", "command", "cwd"] t
  let name? ← match t.find? `name with
    | some x => tomlString "name" x
    | none =>
      tomlProblem ref "an [[executable]] needs a 'name'"
      pure none
  let command? ← match t.find? `command with
    | some (.array r items) =>
      let mut words := #[]
      let mut ok := true
      for item in items do
        match item with
        | .string _ s => words := words.push s
        | other =>
          tomlProblem other.ref s!"each word of 'command' must be a string, and this one is \
            {tomlKind other}"
          ok := false
      if words.isEmpty && ok then
        tomlProblem r "'command' must have at least one word"
        pure none
      else pure (if ok then some words else none)
    | some other =>
      tomlProblem other.ref s!"'command' must be an array of strings, and it is {tomlKind other}"
      pure none
    | none =>
      tomlProblem ref "an [[executable]] needs a 'command'"
      pure none
  let cwd? ← match t.find? `cwd with
    | some x => tomlString "cwd" x
    | none => pure none
  let some name := name? | return none
  let some command := command? | return none
  return some { name, ref, command, cwd? }

/--
Applies inheritance: each profile gets its ancestors' values, the nearer ancestor winning per key,
settings merged per setting, and overrides concatenated with the ancestors' first. `default` is the
root, which every other profile inherits from unless it names another. The result always has
`default`.
-/
private def tomlInherit (profiles : Array TomlProfile) : TomlM (Array TomlProfile) := do
  let profiles :=
    if profiles.any (·.name == "default") then profiles else #[{ name := "default" }] ++ profiles
  let find (name : String) := profiles.find? (·.name == name)
  let mut out := #[]
  for p in profiles do
    if p.name == "default" then
      if let some (_, r) := p.inherits? then
        tomlProblem r "the profile 'default' is the root, and it inherits from no other profile"
    -- The chain from the profile up to the root, nearest first.
    let mut chain := #[p]
    let mut cur := p
    let mut broken := false
    repeat
      if cur.name == "default" then break
      let parentName := (cur.inherits?.map (·.1)).getD "default"
      let some parent := find parentName
        | if let some (_, r) := cur.inherits? then
            if cur.name == p.name then
              tomlProblem r s!"the profile '{cur.name}' inherits from '{parentName}', which is not a profile"
          broken := true
          break
      if chain.any (·.name == parent.name) then
        if let some (_, r) := p.inherits? then
          let names := (chain.map (·.name)).toList ++ [parent.name]
          tomlProblem r s!"the profiles inherit in a cycle: {" → ".intercalate names}"
        broken := true
        break
      chain := chain.push parent
      cur := parent
    if broken then continue
    -- The root first, so each nearer profile's values replace the farther ones'.
    let merged := chain.reverse.foldl (init := ({ name := p.name, ref := p.ref } : TomlProfile))
      fun acc q => {
        acc with
        timeoutMs? := q.timeoutMs? <|> acc.timeoutMs?
        fixtureTimeoutMs? := q.fixtureTimeoutMs? <|> acc.fixtureTimeoutMs?
        gracePeriodMs? := q.gracePeriodMs? <|> acc.gracePeriodMs?
        slowAfterMs? := q.slowAfterMs? <|> acc.slowAfterMs?
        jobs? := q.jobs? <|> acc.jobs?
        updateGolden? := q.updateGolden? <|> acc.updateGolden?
        settings := q.settings.foldl (init := acc.settings) fun s (k, v) =>
          (s.filter (·.1 != k)).push (k, v)
        overrides := acc.overrides ++ q.overrides
        defaultFilter? := q.defaultFilter? <|> acc.defaultFilter?
      }
    out := out.push merged
  return out

/-- Validates the whole of `errata.toml`. -/
private def tomlConfig (fileMap : Lean.FileMap) (t : Lake.Toml.Table) : TomlM TomlConfig := do
  tomlCheckKeys "errata.toml" ["default-filter", "executable", "profile"] t
  let mut config : TomlConfig := {}
  if let some x := t.find? `«default-filter» then
    config := { config with defaultFilter? := ← tomlFilterOf fileMap "default-filter" x }
  if let some x := t.find? `executable then
    match x with
    | .array _ items =>
      let mut exes : Array TomlExecutable := #[]
      for item in items do
        if let some e ← tomlExecutable item then
          if exes.any (·.name == e.name) then
            tomlProblem e.ref s!"the [[executable]] name '{e.name}' is used more than once"
          else exes := exes.push e
      config := { config with executables := exes }
    | other =>
      tomlProblem other.ref s!"'executable' must be an array of tables, written [[executable]], and \
        it is {tomlKind other}"
  if let some x := t.find? `profile then
    match x with
    | .table _ profiles =>
      let mut ps := #[]
      for (k, v) in profiles.items do
        if let some p ← tomlProfile fileMap (tomlKey k) v then ps := ps.push p
      config := { config with profiles := ← tomlInherit ps }
    | other =>
      tomlProblem other.ref s!"'profile' must be a table of profiles, written [profile.NAME], and it \
        is {tomlKind other}"
  if config.profiles.isEmpty then config := { config with profiles := #[{ name := "default" }] }
  return config

/-- A problem as `errata.toml:LINE:COL: message`. -/
private def renderTomlProblem (fileMap : Lean.FileMap) (p : TomlProblem) : String :=
  match p.ref.getPos? with
  | some pos =>
    let q := fileMap.toPosition pos
    s!"errata.toml:{q.line}:{q.column}: {p.msg}"
  | none => s!"errata.toml: {p.msg}"

/--
The elaborated configuration file: what it says, its text, and the build specification of each
distinct target that a `{ needs = … }` setting names.
-/
private structure ErrataToml where
  config : TomlConfig := {}
  text : String := ""
  fileMap : Lean.FileMap := default
  needs : Array (String × BuildSpec) := #[]

/--
Reads, validates, and elaborates `errata.toml` in the root package's directory, when there is one.
The result is the elaborated file, or every problem found, each at its position.
-/
private def loadErrataToml (ws : Workspace) : IO (Except (Array String) ErrataToml) := do
  let path := ws.root.dir / "errata.toml"
  unless ← path.pathExists do return .ok {}
  let text ← IO.FS.readFile path
  -- TOML's grammar has no byte-order mark, and some editors write one.
  let text := (text.dropPrefix? "﻿").map (·.copy) |>.getD text
  let ictx := Lean.Parser.mkInputContext text "errata.toml"
  let table ← match ← (Lake.Toml.loadToml ictx).toBaseIO with
    | .ok t => pure t
    | .error log => return .error (← log.toList.toArray.mapM fun m => m.toString)
  let (config, problems) := (tomlConfig ictx.fileMap table).run #[]
  let mut problems := problems
  -- Each target that a setting needs is resolved now, so that an unknown target is reported before
  -- anything is built.
  let mut needs : Array (String × BuildSpec) := #[]
  let settingsOf (p : TomlProfile) := p.settings ++ p.overrides.flatMap (·.settings)
  for p in config.profiles do
    for (_, s) in settingsOf p do
      let .needs tgt ref := s | continue
      if needs.any (·.1 == tgt) then continue
      match ← (parseTargetSpec ws tgt).toBaseIO with
      | .error e => problems := problems.push ⟨ref, s!"the target '{tgt}' cannot be built: {e}"⟩
      | .ok specs =>
        match specs[0]?, specs.size with
        | some spec, 1 => needs := needs.push (tgt, spec)
        | _, n => problems := problems.push ⟨ref, s!"the target '{tgt}' names {n} build results, \
            and a setting needs exactly one"⟩
  unless problems.isEmpty do
    let sorted := problems.qsort fun a b =>
      (a.ref.getPos?.map (·.byteIdx)).getD 0 < (b.ref.getPos?.map (·.byteIdx)).getD 0
    return .error (sorted.map (renderTomlProblem ictx.fileMap))
  return .ok { config, text, fileMap := ictx.fileMap, needs }

/-- A filter's text and position as the runner's configuration carries them. -/
private def filterJson (f : TomlFilter) : Lean.Json :=
  Lean.Json.mkObj [("text", Lean.Json.str f.text), ("file", Lean.Json.str "errata.toml"),
    ("line", Lean.toJson f.line), ("col", Lean.toJson f.col)]

/-- Settings as JSON, each `{ needs = … }` replaced by the target's result. -/
private def settingsJson (needs : Array (String × String)) (s : Array (String × TomlSetting)) :
    Lean.Json :=
  Lean.Json.mkObj <| s.toList.map fun (k, v) =>
    match v with
    | .value s => (k, Lean.Json.str s)
    | .needs tgt _ => (k, Lean.Json.str ((needs.find? (·.1 == tgt)).map (·.2) |>.getD ""))

/-- A field that is present only when the value is. -/
private def optJson [Lean.ToJson α] (key : String) : Option α → List (String × Lean.Json)
  | some v => [(key, Lean.toJson v)]
  | none => []

private def profileJson (needs : Array (String × String)) (p : TomlProfile) : Lean.Json :=
  let overrideJson (o : TomlOverride) : Lean.Json := Lean.Json.mkObj <|
    [("filter", filterJson o.filter)] ++ optJson "timeout-ms" o.timeoutMs? ++
    optJson "fixture-timeout-ms" o.fixtureTimeoutMs? ++ optJson "grace-period-ms" o.gracePeriodMs? ++
    optJson "slow-after-ms" o.slowAfterMs? ++ optJson "update-golden" o.updateGolden? ++
    [("settings", settingsJson needs o.settings)]
  Lean.Json.mkObj <|
    optJson "timeout-ms" p.timeoutMs? ++ optJson "fixture-timeout-ms" p.fixtureTimeoutMs? ++
    optJson "grace-period-ms" p.gracePeriodMs? ++ optJson "slow-after-ms" p.slowAfterMs? ++
    optJson "jobs" p.jobs? ++ optJson "update-golden" p.updateGolden? ++
    [("settings", settingsJson needs p.settings),
      ("override", Lean.Json.arr (p.overrides.map overrideJson))] ++
    (match p.defaultFilter? with | some f => [("default-filter", filterJson f)] | none => [])

/-- The configuration that the driver writes for the runner, as JSON. -/
private def configJson (executables : Array (String × System.FilePath)) (cwd : System.FilePath)
    (errataDir : String) (warnings : Array String) (invocation : String) (toml : ErrataToml)
    (needs : Array (String × String)) : Lean.Json :=
  let tomlExes := toml.config.executables.map fun e =>
    Lean.Json.mkObj [("name", Lean.Json.str e.name),
      ("command", Lean.Json.arr (e.command.map Lean.Json.str)),
      ("cwd", Lean.Json.str (match e.cwd? with
        | some d => (cwd / d).normalize.toString
        | none => cwd.toString))]
  Lean.Json.mkObj <| [
    ("protocol", Lean.toJson (1 : Nat)),
    ("executables", Lean.Json.arr <| (executables.map fun (name, path) =>
      Lean.Json.mkObj [("name", Lean.Json.str name),
        ("command", Lean.Json.arr #[Lean.Json.str path.toString]),
        ("cwd", Lean.Json.str cwd.toString)]) ++ tomlExes),
    ("errataDir", Lean.Json.str errataDir),
    ("warnings", Lean.toJson warnings),
    ("invocation", Lean.Json.str invocation),
    ("profiles", Lean.Json.mkObj (toml.config.profiles.toList.map fun p =>
      (p.name, profileJson needs p)))
  ] ++ (match toml.config.defaultFilter? with
    | some f => [("default-filter", filterJson f)]
    | none => [])

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
    (s!"{withArgs} LIBRARY... --test-options OPTION...", "pass runner options after the marker"),
    (s!"{withArgs} list [FILTER...]", "list the tests that the filters select")]
  let width := forms.foldl (fun w (form, _) => max w form.length) 0
  let formLines := forms.map fun (form, what) =>
    s!"  {form.pushn ' ' (width + 2 - form.length)}{what}"
  s!"Errata test runner\n\n\
    Usage:\n{"\n".intercalate formLines.toList}\n\n\
    Tokens before `--test-options` name libraries. A library is a bare `Library` in this package\n\
    or a `package/Library` reaching into a dependency. Everything after the marker goes to the\n\
    test runner.\n\n\
    With `list` as the first argument, the driver discovers the tests of every library and prints\n\
    one line per test that the filters select: its executable, name, file and line, and tags. No\n\
    filter selects every test, and several are joined by union. A library is selected with\n\
    `exe(Library)`, and the profile's default filter plays no part.\n\n\
    The configuration file `errata.toml`, in the package's directory, gives the tests' settings\n\
    and the runner's profiles.\n\n\
    The runner documents its own options, including how to give a test's settings values:\n  \
    {withArgs} --test-options --help\n"

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
  -- `list` as the first argument lists the tests of every library that the filters after it select.
  let (libNames, runnerArgs) ←
    if args.head? == some "list" then
      -- A filter begins with a predicate, a constant, `!`, or `(`, never with `-`.
      if let some opt := args.tail.find? (·.startsWith "-") then
        IO.eprintln s!"error: the `list` subcommand takes filters only, and {opt} is an option; \
          `list` applies exactly the filters it is given"
        IO.eprintln (usage run withArgs)
        return 1
      pure ([], args)
    else match splitArgs withArgs args with
    | .ok result => pure result
    | .error msg =>
      IO.eprintln s!"error: {msg}"
      IO.eprintln (usage run withArgs)
      return 1
  -- The configuration file is checked before anything is built, so that a mistake in it ends
  -- Discovery at once.
  let toml ← match ← loadErrataToml ws with
    | .ok toml => pure toml
    | .error problems =>
      for p in problems do IO.eprintln p
      IO.eprintln s!"error: {ws.root.dir / "errata.toml"} has {problems.size} \
        {if problems.size == 1 then "problem" else "problems"}"
      return 1
  -- The phases are named as they begin at a verbosity that shows passes, which these runner flags
  -- select.
  let verbose := runnerArgs.any fun a =>
    ["-v", "--verbose", "-vv", "--verbose-all", "-vvv", "--verbose-docs"].contains a
  if verbose then
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
  -- An executable that the configuration file adds is named apart from the libraries' executables.
  for e in toml.config.executables do
    if testLibs.any (exeName ·.1 == e.name) then
      IO.eprintln (renderTomlProblem toml.fileMap
        ⟨e.ref, s!"the [[executable]] name '{e.name}' is the name of a library's test executable"⟩)
      return 1
  -- Build the test executables, the runner, and every target that a setting needs, then the
  -- runner's configuration. Lake rebuilds the configuration when `errata.toml`, the discovery
  -- results, the executables, or a needed target change: each needed target's trace flows into the
  -- continuation that writes the file.
  let errataDir ← IO.FS.realPath self.dir
  let rootDir ← IO.FS.realPath ws.root.dir
  let configFile := ws.root.dir / defaultLakeDir / "errata" / "config.json"
  let some runnerExe := self.findLeanExe? `«errata-runner»
    | IO.eprintln "error: the package that defines the Errata driver has no errata-runner"
      return 1
  let (configPath, runnerPath) ← runBuild do
    let exeJobs ← testLibs.mapM fun (lib, _) => (lib.facet `errataExe).fetch
    let runnerJob ← runnerExe.exe.fetch
    let needJobs ← toml.needs.mapM fun (_, spec) => spec.query .text
    (Job.collectArray needJobs).bindM fun needValues => do
    (Job.collectArray exeJobs).bindM fun exePaths => do
      runnerJob.mapM fun runnerPath => do
        let mut executables := #[]
        for ((lib, _), path) in testLibs.zip exePaths do
          executables := executables.push (exeName lib, ← IO.FS.realPath path)
        let needs := toml.needs.zipWith (fun (tgt, _) value => (tgt, value)) needValues
        -- Tests run from the root package's directory, where `lake test` runs.
        let content := (configJson executables rootDir errataDir.toString driverWarnings
          s!"{withArgs} --test-options" toml needs).pretty ++ "\n"
        addPureTrace toml.text "errata.toml"
        addPureTrace content "Errata runner configuration"
        buildFileUnlessUpToDate' (text := true) configFile do
          if let some parent := configFile.parent then IO.FS.createDirAll parent
          IO.FS.writeFile configFile content
        return (configFile, runnerPath)
  -- The runner's standard input is a lifeline that the driver holds, and `ERRATA_LIFELINE` asks the
  -- runner to end its tests when that pipe closes. The driver removes `LEAN_ABORT_ON_PANIC` from
  -- the runner's environment, and the runner sets it for every test executable.
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
