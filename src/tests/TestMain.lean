/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso
import VersoManual
import VersoSearch.PorterStemmer
import VersoUtil.LzCompress
import VersoLiterate
import Tests

structure Config where
  verbose : Bool := false
  updateExpected : Bool := false
  checkTeX : Bool := false

open Verso.Search.Stemmer.Porter in
def testStemmer (_ : Config) : IO Unit := do
  let voc := include_str "stemmer/voc.txt"
  let output := include_str "stemmer/output.txt"

  let data := voc.splitOn "\n"
  let outData := output.splitOn "\n"

  let mut failures := #[]
  for x in data, y in outData do
    let s := porterStem x
    unless s == y do
      failures := failures.push (x, s, y)
  unless failures.isEmpty do
    IO.eprintln s!"{failures.size} failures"
    for (x, s, y) in failures do
      IO.eprintln s!"{x} --> {s} (wanted '{y}')"
    throw <| IO.userError "Stemmer tests failed"

/--
Tests manual-genre TeX generation. `dir` is a subdirectory specific to a particular test document,
which is where actual output should go, and which contains the expected output directory.
`doc` is the document to be rendered.
-/
def testTexOutput
    (dir : System.FilePath)
    (doc : Verso.Doc.VersoDoc Verso.Genre.Manual)
    (config : Config)
    (extraFiles : List (System.FilePath × String) := [])
    (extraFilesTeX : List (System.FilePath × String) := []) : IO Unit := do
  let versoConfig : Verso.Genre.Manual.Config := {
    destination := "src/tests/integration" / dir / "output",
    emitTeX := true,
    emitHtmlMulti := .no,
    extraFiles,
    extraFilesTeX
  }

  let runTest : IO Unit  :=
    open Verso Genre Manual in do
    let logError (msg : String) := IO.eprintln msg
    ReaderT.run (emitTeX logError versoConfig doc.toPart) extension_impls%

  Verso.Integration.runTests { config with
    testDir := "src/tests/integration" / dir,
    updateExpected := config.updateExpected,
    runTest
  }

def testZip (cfg : Config) : IO Unit := do
  IO.println "Running zip tests with fixed files..."
  testExtract #[] .store
  testExtract #[] .deflate
  testExtract #[("empty", .empty)] .store
  testExtract #[("empty", .empty)] .deflate
  testExtract files .store
  testExtract files .deflate
  let chunkSize := me.size / 10
  for i in (0 : Nat)...10 do
    let me := me.extract 0 (i * chunkSize)
    testExtract #[("T2.lean", me)] .store
    testExtract #[("T2.lean", me)] .deflate
  for i in (0 : Nat)...10 do
    let me := me.extract 0 (i * chunkSize)
    let bwd := bwd.extract 0 (i * chunkSize)
    testExtract #[("T2.lean", me), ("other", bwd)] .store
    testExtract #[("T2.lean", me), ("other", bwd)] .deflate
  for _ in (0 : Nat)...10 do
    let seedValue ← IO.monoNanosNow
    if cfg.verbose then IO.println s!"Seed is {seedValue}"
    IO.setRandSeed seedValue
    let mut randFiles := #[]
    for _ in 0...(← IO.rand 0 15) do
      let name ← randName
      let size ← IO.rand 0 50000
      let content ← IO.getRandomBytes <| .ofNat size
      randFiles := randFiles.push (name, content)
    if cfg.verbose then
      IO.println s!"Running random zip test with {randFiles.size} files, sizes:"
      for (x, y) in randFiles do
        IO.println s!" * {x}: {y.size} bytes"
    else
      IO.println s!"Running random zip test with {randFiles.size} files"
    testExtract randFiles .store
    testExtract randFiles .deflate

where
  files := #[("x.txt", "abcdef\nlkjlkj".toByteArray), ("y.txt", "".toByteArray), ("z.txt", "abc\n\n".toByteArray)]
  me := (include_str "TestMain.lean").toByteArray
  bwd := me.foldl (init := .empty) fun x y => ByteArray.empty.push y ++ x
  randName : IO String := do
    let len ← IO.rand 1 10
    let stem ← len.foldM (init := "") fun _ _ acc => do
      return acc.push <| Char.ofNat ('a'.toNat + (← IO.rand 0 25))
    let len ← IO.rand 2 4
    let ext ← len.foldM (init := "") fun _ _ acc => do
      return acc.push <| Char.ofNat ('a'.toNat + (← IO.rand 0 25))
    return stem ++ "." ++ ext

open Verso.LzCompress in
def testLz (_ : Config) : IO Unit := do
  let actual := lzCompress r#"import Mathlib.Logic.Basic -- basic facts in logic
-- theorems in Lean's mathematics library

-- Let P and Q be true-false statements
variable (P Q : Prop)

-- The following is a basic result in logic
example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  -- its proof is already in Lean's mathematics library
  exact not_and_or

-- Here is another basic result in logic
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  apply? -- we can search for the proof in the library
  -- we can also replace `apply?` with its output
"#
  let expected :=
    "JYWwDg9gTgLgBAWQIYwBYBtgCMB0AZCAc2AGMcAhJAZ1LgFo64traAzJEmKuYAOznRFSAKAZw0AU2gSQ3" ++
    "PnDwSkvAOTcQKVDJSlumLFCRQAnsNGNF8AApxlAEzgBFJhPFQArhLrt0VV1RgUGQleLmEANyNgJCx0VwA" ++
    "KG2cALjgrKAgwAEozMQAVLThWCHRBAHc+Qh5uJCYWEjgoCSp3dHh5QWISYQkADyRwOLhUgBq4RLhAciIn" ++
    "LLhAFMI4MZtACiJFp2GAXiZTOHpGYC44MAyIVmrbdCakO2MefkVlNTgNSRfdAWxDE2Fdvo54XgQGAAfXs" ++
    "wOguUYAAkJE1zsogVooHUaA0mi02ncBEJun9Bq5RuMVjN5msbNMxiktlgdrYwGB0MYAPx7OBlVwkZRwPx" ++
    "GEioIrQcSFY4QU5YyQfAxGWlidlwTn8JC+CCNCQMjiuAAGSHpjKZmrZB35B24EHcMDA5uEQA"
  if actual ≠ expected then
    throw <| IO.userError "Mismatched lzCompress output"

def testSerialization (_ : Config) : IO Unit := do
  IO.println "Running serialization tests with Plausible..."
  let fails ← runSerializationTests
  if fails > 0 then
    throw <| IO.userError s!"{fails} serialization tests failed"

def testBlog (_ : Config) : IO Unit := do
  IO.println "Running blog tests with Plausible..."
  let fails ← runBlogTests
  if fails > 0 then
    throw <| IO.userError s!"{fails} blog tests failed"

def testLiterateConfig (_ : Config) : IO Unit := do
  let fails ← Tests.LiterateConfig.runLiterateConfigTests
  if fails > 0 then
    throw <| IO.userError s!"{fails} literate config tests failed"

def testLiterateHtml (_ : Config) : IO Unit :=
  Tests.LiterateHtml.testLiterateHtml

def testLiterateHtmlMultiRoot (_ : Config) : IO Unit :=
  Tests.LiterateHtml.testLiterateHtmlMultiRoot

def testDocSourceConfig (_ : Config) : IO Unit := do
  let fails ← runDocSourceConfigTests
  if fails > 0 then
    throw <| .userError s!"{fails} doc source config tests failed"

def testIndentColumn (_ : Config) : IO Unit := do
  let fails ← runIndentColumnTests
  if fails > 0 then
    throw <| .userError s!"{fails} indentColumn tests failed"

-- Interactive tests via the LSP server
def testInteractive (_ : Config) : IO Unit := do
  IO.println "Running interactive (LSP) tests..."
  IO.println s!"current dir: {(← IO.Process.getCurrentDir)}"
  -- We use the lower-level Process.spawn, which causes the subprocess to inherit the stdio
  let child ← IO.Process.spawn { cmd := "src/tests/interactive/run_interactive.sh" }
  let exitCode ← child.wait
  if exitCode != 0 then
    throw <| IO.userError s!"Interactive LSP tests failed with exit code {exitCode}"

private def hasSubstring (s : String) (sub : String) : Bool :=
  s.find? sub |>.isSome

def testSetupLiterate (_ : Config) : IO Unit := do
  IO.println "Running setup-literate tests..."
  let versoRoot ← IO.FS.realPath "."
  IO.FS.withTempDir fun tmpDir => do
    let run (cmd : String) (args : Array String) : IO Unit := do
      let result ← IO.Process.output {
        cmd := cmd
        args := args
        cwd := some tmpDir.toString
      }
      if result.exitCode != 0 then
        throw <| IO.userError s!"{cmd} failed: {result.stderr}"

    -- Set up a project that depends on the Verso being tested
    run "git" #["init", "-q"]
    let toolchain ← IO.FS.readFile "lean-toolchain"
    IO.FS.writeFile (tmpDir / "lean-toolchain") toolchain
    IO.FS.writeFile (tmpDir / "lakefile.toml")
      s!"name = \"test-project\"\n\n[[require]]\nname = \"verso\"\npath = \"{versoRoot}\"\n"

    -- Test 1: Fresh generation via lake exe
    let result ← IO.Process.output {
      cmd := "lake"
      args := #["exe", "verso", "setup-literate"]
      cwd := some tmpDir.toString
    }
    if result.exitCode != 0 then
      throw <| IO.userError s!"setup-literate failed: {result.stderr}\n{result.stdout}"

    let workflowFile := tmpDir / ".github" / "workflows" / "verso-literate-pages.yml"
    unless ← workflowFile.pathExists do
      throw <| IO.userError "Workflow file was not created"

    let content ← IO.FS.readFile workflowFile
    let checks := #[
      ("lake query :literateHtml", "lake query command"),
      ("deploy-pages@v", "deploy-pages action"),
      ("upload-pages-artifact@v", "upload-pages-artifact action"),
      ("lean-action@v", "lean-action")
    ]
    for (needle, desc) in checks do
      unless hasSubstring content needle do
        throw <| IO.userError s!"Workflow file missing {desc} ({needle})"
    IO.println "  fresh generation: passed"

    -- Test 2: Idempotent (no change)
    let result2 ← IO.Process.output {
      cmd := "lake"
      args := #["exe", "verso", "setup-literate"]
      cwd := some tmpDir.toString
    }
    unless hasSubstring result2.stdout "up to date" do
      throw <| IO.userError "Expected 'up to date' message on second run"
    IO.println "  idempotent: passed"

    -- Test 3: Outdated file gets .bak
    IO.FS.writeFile workflowFile "modified content\n"
    let result3 ← IO.Process.output {
      cmd := "lake"
      args := #["exe", "verso", "setup-literate"]
      cwd := some tmpDir.toString
    }
    if result3.exitCode != 0 then
      throw <| IO.userError s!"setup-literate (update) failed: {result3.stderr}"
    let bakFile := tmpDir / ".github" / "workflows" / "verso-literate-pages.yml.bak"
    unless ← bakFile.pathExists do
      throw <| IO.userError ".bak file was not created when updating"
    let bakContent ← IO.FS.readFile bakFile
    unless hasSubstring bakContent "modified content" do
      throw <| IO.userError ".bak file should contain old content"
    IO.println "  backup on update: passed"

    -- Test 4: actionlint validation
    let actionlintResult ← IO.Process.output {
      cmd := "actionlint"
      args := #[workflowFile.toString]
    }
    if actionlintResult.exitCode != 0 then
      throw <| IO.userError s!"actionlint failed: {actionlintResult.stderr}"
    IO.println "  actionlint: passed"

  IO.println "  All setup-literate tests passed."

open Verso.Integration in
def tests := [
  testSerialization,
  testBlog,
  testDocSourceConfig,
  testIndentColumn,
  testStemmer,
  testTexOutput "sample-doc" SampleDoc.doc,
  testTexOutput "inheritance-doc" InheritanceDoc.doc,
  testTexOutput "code-content-doc" CodeContent.doc,
  testTexOutput "extra-files-doc" ExtraFilesDoc.doc
    (extraFiles := [("src/tests/integration/extra-files-doc/test-data/shared", "shared")])
    (extraFilesTeX := [("src/tests/integration/extra-files-doc/test-data/TeX-only", "TeX-only")]),
  testTexOutput "front-matter-doc" FrontMatter.doc,
  testZip,
  testInteractive,
  testLiterateConfig,
  testLiterateHtml,
  testLiterateHtmlMultiRoot,
  testSetupLiterate
]

def getConfig (config : Config) : List String → IO Config
  | [] => pure config
  | "--update-expected" :: args => getConfig { config with updateExpected := true } args
  | "--verbose" :: args | "-v" :: args => getConfig { config with verbose := true } args
  | "--check-tex" :: args => getConfig { config with checkTeX := true } args
  | other :: _ => throw <| IO.userError s!"Didn't understand {other}"

def main (args : List String) : IO UInt32 := do
  let config ← getConfig {} args
  let mut failures := 0
  for test in tests do
    try
      test config
    catch
      | e => do
        IO.eprintln e
        failures := failures + 1
  if failures == 0 then
    IO.println "All tests passed"
  return failures
