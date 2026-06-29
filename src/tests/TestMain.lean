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
    let logger ← Verso.Logger.new
    emitTeX versoConfig doc.toPart |>.run extension_impls% |>.run logger

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

def testSearchJs (_ : Config) : IO Unit := do
  IO.println "Running search JS wire-format tests..."
  let fails ← Verso.Tests.SearchJs.runSearchJsTests
  if fails > 0 then
    throw <| IO.userError s!"{fails} search JS tests failed"

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

  IO.println "  All setup-literate tests passed."

open Verso in
def testBuildLog (_ : Config) : IO Unit := do
  IO.println "Running build-log tests..."
  -- A message logged with a position is saved with that location (a location always names a file).
  let logger ← Logger.new
  let pos : Lean.Lsp.Position := { line := 4, character := 2 }
  (reportError "boom" (some { file := "PosSave.lean", span := .pos pos }) : BuildLogT IO Unit).run logger
  let errs ← logger.errors
  let some m := errs[0]?
    | throw <| IO.userError s!"expected 1 saved error, got {errs.size}"
  unless m.severity == .error do throw <| IO.userError "expected error severity"
  match m.loc with
  | some { file := "PosSave.lean", span := .pos p } =>
    unless p.line == 4 && p.character == 2 do
      throw <| IO.userError "saved position does not match the logged span"
  | _ => throw <| IO.userError "expected a saved `PosSave.lean` `pos` location"

  -- A `range` span is likewise saved.
  let logger2 ← Logger.new
  let r : Lean.Lsp.Range :=
    { start := { line := 1, character := 0 }, «end» := { line := 1, character := 5 } }
  (reportWarning "careful" (some { file := "RangeSave.lean", span := .range r }) : BuildLogT IO Unit).run logger2
  let some w := (← logger2.warnings)[0]?
    | throw <| IO.userError "expected 1 saved warning"
  match w.loc with
  | some { span := .range _, .. } => pure ()
  | _ => throw <| IO.userError "expected a `range` span to be saved"

  -- Range formatting defers to Lean's `mkErrorStringWithPos`: `file:line:col-line:col`, 1-based
  -- line, 0-based column, with the full end position even within one line (no `line:col-col` collapse).
  let crossLine : LogMessage :=
    { severity := .error, text := "msg",
      loc := some { file := "CrossLine.lean",
                    span := .range { start := { line := 19, character := 4 }, «end» := { line := 20, character := 7 } } } }
  unless crossLine.format == "CrossLine.lean:20:4-21:7: msg" do
    throw <| IO.userError s!"cross-line range formatted as \"{crossLine.format}\""
  let sameLine : LogMessage :=
    { severity := .error, text := "msg",
      loc := some { file := "SameLine.lean",
                    span := .range { start := { line := 42, character := 4 }, «end» := { line := 42, character := 21 } } } }
  unless sameLine.format == "SameLine.lean:43:4-43:21: msg" do
    throw <| IO.userError s!"same-line range formatted as \"{sameLine.format}\""

  -- A located message is formatted uniformly as `file:line:col: text`.
  let loggerF ← Logger.new
  let errBufF ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  IO.withStderr (IO.FS.Stream.ofBuffer errBufF) <|
    (reportError "bad term" (some { file := "FileLoc.lean", span := .pos { line := 6, character := 3 } })
      : BuildLogT IO Unit).run loggerF
  let some mF := (← loggerF.errors)[0]?
    | throw <| IO.userError "expected 1 saved error with a file location"
  unless mF.loc.map (·.file) == some "FileLoc.lean" do
    throw <| IO.userError "saved location should carry the filename"
  unless hasSubstring (String.fromUTF8! (← errBufF.get).data) "FileLoc.lean:7:3: bad term" do
    throw <| IO.userError "a file location should format as file:line:col:"

  -- A single logging action can emit both severities; errors set the exit code, warnings do not.
  let logger3 ← Logger.new
  (do reportError "e1"; reportWarning "w1"; reportError "e2" : BuildLogT IO Unit).run logger3
  unless (← logger3.errors).size == 2 do throw <| IO.userError "expected 2 errors"
  unless (← logger3.warnings).size == 1 do throw <| IO.userError "expected 1 warning"
  unless (← logger3.exitCode) == 1 do throw <| IO.userError "errors must yield a non-zero exit code"

  let logger4 ← Logger.new
  (reportWarning "just a warning" : BuildLogT IO Unit).run logger4
  unless (← logger4.exitCode) == 0 do
    throw <| IO.userError "warnings must not affect the exit code"

  -- Logging prints to the *ambient* stderr, resolved at log time: a logger created before a
  -- stderr redirection still writes into the redirected stream, and nothing goes to stdout.
  let logger5 ← Logger.new
  let outBuf ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let errBuf ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  IO.withStdout (IO.FS.Stream.ofBuffer outBuf) <|
    IO.withStderr (IO.FS.Stream.ofBuffer errBuf) <|
      (do
        reportError "first problem" (some { file := "X.lean", span := .pos { line := 0, character := 0 } })
        reportWarning "second problem" : BuildLogT IO Unit).run logger5
  let errText := String.fromUTF8! (← errBuf.get).data
  let outText := String.fromUTF8! (← outBuf.get).data
  unless hasSubstring errText "X.lean:1:0: first problem" do
    throw <| IO.userError s!"stderr buffer is missing the formatted error; got: {errText}"
  unless hasSubstring errText "second problem" do
    throw <| IO.userError s!"stderr buffer is missing the warning; got: {errText}"
  unless outText.isEmpty do
    throw <| IO.userError s!"logging must not write to stdout; got: {outText}"
  unless (← logger5.errors).size == 1 && (← logger5.warnings).size == 1 do
    throw <| IO.userError "redirected logging should still accumulate into the logger's buffers"
  IO.println "  All build-log tests passed."

open Verso.Integration in
def tests := [
  testBuildLog,
  testSerialization,
  testSearchJs,
  testBlog,
  testStemmer,
  testTexOutput "sample-doc" SampleDoc.doc,
  testTexOutput "inheritance-doc" InheritanceDoc.doc,
  testTexOutput "code-content-doc" CodeContent.doc,
  testTexOutput "extra-files-doc" ExtraFilesDoc.doc
    (extraFiles := [("src/tests/integration/extra-files-doc/test-data/shared", "shared")])
    (extraFilesTeX := [("src/tests/integration/extra-files-doc/test-data/TeX-only", "TeX-only")]),
  testTexOutput "escape-doc" Escape.doc,
  testTexOutput "front-matter-doc" FrontMatter.doc,
  testTexOutput "diagram-doc" DiagramDoc.doc,
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
