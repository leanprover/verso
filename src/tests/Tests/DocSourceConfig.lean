/-
Copyright (c) 2025-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lake.Toml
import VersoManual.DB.Config

/-! # Tests for Doc Source Configuration Parsing

Tests for `Verso.Genre.Manual.DocSource.Config` — TOML parsing and lakefile generation.
-/

open Verso.Genre.Manual.DocSource
open Lake.Toml

/-- Parses a TOML string into a `Table`. Throws on parse error. -/
private def parseToml (input : String) : IO Table := do
  let ictx := Lean.Parser.mkInputContext input "<test>"
  match (← Lake.Toml.loadToml ictx |>.toBaseIO) with
  | .ok table => pure table
  | .error msgs =>
    let msgStrs ← msgs.toList.mapM fun msg => msg.data.toString
    throw <| .userError s!"TOML parse error:\n{"\n".intercalate msgStrs}"

/-- Asserts that two values are equal, throwing a descriptive error if not. -/
private def assertEqual [BEq α] [Repr α] (label : String) (expected actual : α) : IO Unit := do
  unless expected == actual do
    throw <| IO.userError s!"{label}: expected\n  {repr expected}\nbut got\n  {repr actual}"

/-- Asserts that a result is an error. -/
private def assertError [Repr α] (label : String) (result : Except String α) : IO Unit := do
  match result with
  | .error _ => pure ()
  | .ok v => throw <| IO.userError s!"{label}: expected an error but got\n  {repr v}"

/-- Asserts that a string contains a substring. -/
private def assertContains (label : String) (haystack needle : String) : IO Unit := do
  unless (haystack.splitOn needle).length > 1 do
    throw <| IO.userError s!"{label}: expected string to contain '{needle}' but got:\n  {haystack}"

-- ============================================================================
-- Config.ofToml tests
-- ============================================================================

private def testEmptyConfig : IO Unit := do
  let table ← parseToml ""
  let config ← IO.ofExcept <| Config.ofToml table
  assertEqual "empty config require" #[] config.require
  assertEqual "empty config libraries" #[] config.libraries
  assertEqual "empty config setup" #[] config.setup

private def testPathDependency : IO Unit := do
  let table ← parseToml "
[[require]]
name = \"Batteries\"
path = \"../batteries\"
"
  let config ← IO.ofExcept <| Config.ofToml table
  assertEqual "path dep count" 1 config.require.size
  let req := config.require[0]!
  assertEqual "path dep name" "Batteries" req.name
  assertEqual "path dep path" (some ⟨"../batteries"⟩) req.path
  assertEqual "path dep git" none req.git
  assertEqual "path dep rev" none req.rev

private def testGitDependency : IO Unit := do
  let table ← parseToml "
[[require]]
name = \"Mathlib\"
git = \"https://github.com/leanprover-community/mathlib4\"
rev = \"main\"
"
  let config ← IO.ofExcept <| Config.ofToml table
  assertEqual "git dep count" 1 config.require.size
  let req := config.require[0]!
  assertEqual "git dep name" "Mathlib" req.name
  assertEqual "git dep git" (some "https://github.com/leanprover-community/mathlib4") req.git
  assertEqual "git dep rev" (some "main") req.rev
  assertEqual "git dep path" none req.path

private def testGitDepWithSubDir : IO Unit := do
  let table ← parseToml "
[[require]]
name = \"MyLib\"
git = \"https://github.com/example/monorepo\"
rev = \"v1.0\"
subDir = \"packages/mylib\"
"
  let config ← IO.ofExcept <| Config.ofToml table
  let req := config.require[0]!
  assertEqual "subDir dep name" "MyLib" req.name
  assertEqual "subDir dep subDir" (some "packages/mylib") req.subDir

private def testMultipleRequires : IO Unit := do
  let table ← parseToml "
[[require]]
name = \"Batteries\"
git = \"https://github.com/leanprover/batteries\"
rev = \"main\"

[[require]]
name = \"Mathlib\"
git = \"https://github.com/leanprover-community/mathlib4\"
rev = \"main\"
"
  let config ← IO.ofExcept <| Config.ofToml table
  assertEqual "multi req count" 2 config.require.size
  assertEqual "multi req first name" "Batteries" config.require[0]!.name
  assertEqual "multi req second name" "Mathlib" config.require[1]!.name

private def testLibrariesField : IO Unit := do
  let table ← parseToml "
libraries = [\"Mathlib\", \"Batteries\"]

[[require]]
name = \"Mathlib\"
git = \"https://github.com/leanprover-community/mathlib4\"
rev = \"main\"
"
  let config ← IO.ofExcept <| Config.ofToml table
  assertEqual "libraries" #["Mathlib", "Batteries"] config.libraries

private def testSetupField : IO Unit := do
  let table ← parseToml "
setup = [\"lake exe cache get\", \"lake build Foo\"]
"
  let config ← IO.ofExcept <| Config.ofToml table
  assertEqual "setup" #["lake exe cache get", "lake build Foo"] config.setup

private def testFullConfig : IO Unit := do
  let table ← parseToml "
setup = [\"lake exe cache get\"]
libraries = [\"Mathlib\"]

[[require]]
name = \"Mathlib\"
git = \"https://github.com/leanprover-community/mathlib4\"
rev = \"main\"
"
  let config ← IO.ofExcept <| Config.ofToml table
  assertEqual "full config setup" #["lake exe cache get"] config.setup
  assertEqual "full config libraries" #["Mathlib"] config.libraries
  assertEqual "full config require count" 1 config.require.size
  assertEqual "full config require name" "Mathlib" config.require[0]!.name

private def testMissingName : IO Unit := do
  let table ← parseToml "
[[require]]
git = \"https://github.com/example/lib\"
"
  let result := Config.ofToml table
  assertError "missing name" result

private def testNoRequireEntries : IO Unit := do
  let table ← parseToml "
libraries = [\"Init\"]
"
  let config ← IO.ofExcept <| Config.ofToml table
  assertEqual "no requires" #[] config.require
  assertEqual "libraries only" #["Init"] config.libraries

-- ============================================================================
-- Lakefile generation tests
-- ============================================================================

private def testLakefileGenCoreOnly : IO Unit := do
  let lakefile := generateLakefile none "/abs/path/to/doc-gen4" "/project"
  assertContains "core-only header" lakefile "import Lake"
  assertContains "core-only package" lakefile "package «docgen-workspace»"
  assertContains "core-only docgen4" lakefile "require «doc-gen4» from \"/abs/path/to/doc-gen4\""
  -- Should not contain any user requires
  let lines := lakefile.splitOn "\n"
  let requireCount := lines.filter (·.startsWith "require") |>.length
  -- Only the doc-gen4 require
  assertEqual "core-only require count" 1 requireCount

private def testLakefileGenGitDep : IO Unit := do
  let config : Config := {
    require := #[{
      name := "Mathlib"
      git := some "https://github.com/leanprover-community/mathlib4"
      rev := some "main"
    }]
  }
  let lakefile := generateLakefile (some config) "/path/to/doc-gen4" "/project"
  assertContains "git dep lakefile docgen4" lakefile "require «doc-gen4» from \"/path/to/doc-gen4\""
  assertContains "git dep lakefile Mathlib" lakefile "require «Mathlib» from git"
  assertContains "git dep lakefile url" lakefile "\"https://github.com/leanprover-community/mathlib4\""
  assertContains "git dep lakefile rev" lakefile "@ \"main\""

private def testLakefileGenPathDep : IO Unit := do
  let config : Config := {
    require := #[{
      name := "Batteries"
      path := some "../batteries"
    }]
  }
  let lakefile := generateLakefile (some config) "/path/to/doc-gen4" "/project"
  -- Path should be resolved to absolute
  assertContains "path dep lakefile abs" lakefile "require «Batteries» from \"/project/../batteries\""

private def testLakefileGenAbsPathDep : IO Unit := do
  let config : Config := {
    require := #[{
      name := "Batteries"
      path := some "/absolute/path/to/batteries"
    }]
  }
  let lakefile := generateLakefile (some config) "/path/to/doc-gen4" "/project"
  assertContains "abs path dep lakefile" lakefile "require «Batteries» from \"/absolute/path/to/batteries\""

private def testLakefileGenMultipleDeps : IO Unit := do
  let config : Config := {
    require := #[
      { name := "Batteries", git := some "https://github.com/leanprover/batteries", rev := some "main" },
      { name := "Mathlib", git := some "https://github.com/leanprover-community/mathlib4", rev := some "main" }
    ]
  }
  let lakefile := generateLakefile (some config) "/path/to/doc-gen4" "/project"
  assertContains "multi dep Batteries" lakefile "require «Batteries»"
  assertContains "multi dep Mathlib" lakefile "require «Mathlib»"

-- ============================================================================
-- splitCommand tests
-- ============================================================================

private def testSplitSimple : IO Unit := do
  assertEqual "simple" (some ("lake", #["exe", "cache", "get"])) (splitCommand "lake exe cache get")

private def testSplitSingleArg : IO Unit := do
  assertEqual "single arg" (some ("lake", #[])) (splitCommand "lake")

private def testSplitEmpty : IO Unit := do
  assertEqual "empty" none (splitCommand "")

private def testSplitOnlySpaces : IO Unit := do
  assertEqual "only spaces" none (splitCommand "   ")

private def testSplitLeadingTrailingSpaces : IO Unit := do
  assertEqual "leading/trailing" (some ("lake", #["build"])) (splitCommand "  lake  build  ")

private def testSplitTabs : IO Unit := do
  assertEqual "tabs" (some ("lake", #["build", "Foo"])) (splitCommand "lake\tbuild\tFoo")

private def testSplitMixedWhitespace : IO Unit := do
  assertEqual "mixed ws" (some ("lake", #["build"])) (splitCommand " \t lake \t build \t ")

private def testSplitDoubleQuoted : IO Unit := do
  assertEqual "double quoted" (some ("echo", #["hello world"])) (splitCommand "echo \"hello world\"")

private def testSplitSingleQuoted : IO Unit := do
  assertEqual "single quoted" (some ("echo", #["hello world"])) (splitCommand "echo 'hello world'")

private def testSplitDoubleQuotedBackslash : IO Unit := do
  assertEqual "dq backslash" (some ("echo", #["hello\"world"])) (splitCommand "echo \"hello\\\"world\"")

private def testSplitDoubleQuotedBackslashN : IO Unit := do
  assertEqual "dq backslash-n" (some ("echo", #["hellonworld"])) (splitCommand "echo \"hello\\nworld\"")

private def testSplitSingleQuotedNoEscape : IO Unit := do
  assertEqual "sq no escape" (some ("echo", #["hello\\nworld"])) (splitCommand "echo 'hello\\nworld'")

private def testSplitEmptyDoubleQuotes : IO Unit := do
  assertEqual "empty dq" (some ("echo", #[""])) (splitCommand "echo \"\"")

private def testSplitEmptySingleQuotes : IO Unit := do
  assertEqual "empty sq" (some ("echo", #[""])) (splitCommand "echo ''")

private def testSplitQuotedConcat : IO Unit := do
  -- "hello"' '"world" → hello world (quotes are just delimiters, adjacent runs concatenate)
  assertEqual "quoted concat" (some ("echo", #["hello world"])) (splitCommand "echo \"hello\"' 'world")

private def testSplitMixedQuotesInArg : IO Unit := do
  assertEqual "mixed quotes" (some ("cmd", #["it's", "a \"test\""])) (splitCommand "cmd \"it's\" 'a \"test\"'")

private def testSplitUnclosedDoubleQuote : IO Unit := do
  -- Unmatched quote is treated as if closed at end of string
  assertEqual "unclosed dq" (some ("echo", #["hello world"])) (splitCommand "echo \"hello world")

private def testSplitUnclosedSingleQuote : IO Unit := do
  assertEqual "unclosed sq" (some ("echo", #["hello world"])) (splitCommand "echo 'hello world")

private def testSplitQuotedEmpty : IO Unit := do
  -- Just a pair of quotes produces a single empty-string argument (the executable name)
  assertEqual "just quotes" (some ("", #[])) (splitCommand "\"\"")

private def testSplitBackslashInDoubleQuotes : IO Unit := do
  -- Backslash at end of double-quoted string
  assertEqual "trailing backslash in dq" (some ("echo", #["hello\\"])) (splitCommand "echo \"hello\\\\\"")

private def testSplitMultipleQuotedArgs : IO Unit := do
  assertEqual "multi quoted" (some ("cmd", #["arg one", "arg two", "three"])) (splitCommand "cmd 'arg one' \"arg two\" three")

private def testSplitPathWithSpaces : IO Unit := do
  assertEqual "path with spaces" (some ("cd", #["/path/to/my project"])) (splitCommand "cd '/path/to/my project'")

private def testSplitConsecutiveSpaces : IO Unit := do
  assertEqual "consecutive spaces" (some ("a", #["b", "c"])) (splitCommand "a    b    c")

private def testSplitTabsAndSpaces : IO Unit := do
  assertEqual "tabs and spaces" (some ("a", #["b"])) (splitCommand "\t a \t b \t")

-- ============================================================================
-- Test runner
-- ============================================================================

private def docSourceConfigTests : List (String × IO Unit) := [
  ("Config.ofToml: empty config", testEmptyConfig),
  ("Config.ofToml: path dependency", testPathDependency),
  ("Config.ofToml: git dependency", testGitDependency),
  ("Config.ofToml: git dep with subDir", testGitDepWithSubDir),
  ("Config.ofToml: multiple requires", testMultipleRequires),
  ("Config.ofToml: libraries field", testLibrariesField),
  ("Config.ofToml: setup field", testSetupField),
  ("Config.ofToml: full config", testFullConfig),
  ("Config.ofToml: missing name error", testMissingName),
  ("Config.ofToml: no require entries", testNoRequireEntries),
  ("generateLakefile: core-only", testLakefileGenCoreOnly),
  ("generateLakefile: git dependency", testLakefileGenGitDep),
  ("generateLakefile: path dependency (relative)", testLakefileGenPathDep),
  ("generateLakefile: path dependency (absolute)", testLakefileGenAbsPathDep),
  ("generateLakefile: multiple dependencies", testLakefileGenMultipleDeps),
  ("splitCommand: simple", testSplitSimple),
  ("splitCommand: single arg", testSplitSingleArg),
  ("splitCommand: empty", testSplitEmpty),
  ("splitCommand: only spaces", testSplitOnlySpaces),
  ("splitCommand: leading/trailing spaces", testSplitLeadingTrailingSpaces),
  ("splitCommand: tabs", testSplitTabs),
  ("splitCommand: mixed whitespace", testSplitMixedWhitespace),
  ("splitCommand: double quoted", testSplitDoubleQuoted),
  ("splitCommand: single quoted", testSplitSingleQuoted),
  ("splitCommand: dq backslash escape", testSplitDoubleQuotedBackslash),
  ("splitCommand: dq backslash-n", testSplitDoubleQuotedBackslashN),
  ("splitCommand: sq no escape", testSplitSingleQuotedNoEscape),
  ("splitCommand: empty double quotes", testSplitEmptyDoubleQuotes),
  ("splitCommand: empty single quotes", testSplitEmptySingleQuotes),
  ("splitCommand: quoted concatenation", testSplitQuotedConcat),
  ("splitCommand: mixed quotes in arg", testSplitMixedQuotesInArg),
  ("splitCommand: unclosed double quote", testSplitUnclosedDoubleQuote),
  ("splitCommand: unclosed single quote", testSplitUnclosedSingleQuote),
  ("splitCommand: just quotes", testSplitQuotedEmpty),
  ("splitCommand: backslash in double quotes", testSplitBackslashInDoubleQuotes),
  ("splitCommand: multiple quoted args", testSplitMultipleQuotedArgs),
  ("splitCommand: path with spaces", testSplitPathWithSpaces),
  ("splitCommand: consecutive spaces", testSplitConsecutiveSpaces),
  ("splitCommand: tabs and spaces", testSplitTabsAndSpaces),
]

public def runDocSourceConfigTests : IO Nat := do
  IO.println "Running doc source config tests..."
  let mut failures := 0
  for (name, test) in docSourceConfigTests do
    IO.print s!"  {name}: "
    try
      test
      IO.println "ok"
    catch e =>
      IO.println s!"FAIL\n    {e}"
      failures := failures + 1
  return failures
