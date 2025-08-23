
import Lean.Util.Diff

namespace Verso.GoldenTest

open Lean.Diff


/-- Configuration for the test runner -/
structure Config where
  /-- Where are input and expected files located? -/
  testDir : String
  updateExpected : Bool := false
  runTest : String → IO String

/-- Result of running a single test -/
inductive TestResult where
  | pass (name : String) : TestResult
  | fail (name expected actual : String) : TestResult
  | error (name message : String) : TestResult

/-- Statistics for a test run -/
structure TestStats where
  passed : Nat := 0
  failed : Nat := 0
  errors : Nat := 0

def TestStats.total (stats : TestStats) : Nat :=
  stats.passed + stats.failed + stats.errors

def TestStats.add (stats : TestStats) (result : TestResult) : TestStats :=
  match result with
  | .pass _ => { stats with passed := stats.passed + 1 }
  | .fail _ _ _ => { stats with failed := stats.failed + 1 }
  | .error _ _ => { stats with errors := stats.errors + 1 }


structure TestPaths where
  input : System.FilePath
  expected : System.FilePath
  output : System.FilePath

/-- Get paths for a test given the input file path -/
def getTestPaths (testDir : System.FilePath) (testName : String) : TestPaths where
  input := testDir / (testName ++  ".input")
  expected := testDir / (testName ++  ".expected")
  output := testDir / (testName ++  ".output")

/-- Run a single test -/
def runSingleTest (config : Config) (testName : String) : IO TestResult := do
  let {input, expected, output} := getTestPaths config.testDir testName

  try
    let inputString ← IO.FS.readFile input
    let outputString ← config.runTest inputString
    IO.FS.writeFile output outputString

    if config.updateExpected then
      IO.FS.writeFile expected outputString
      return TestResult.pass testName
    else
      if ← System.FilePath.pathExists expected then
        let expectedString ← IO.FS.readFile expected
        if output == expectedString then
          return TestResult.pass testName
        else
          return TestResult.fail testName expectedString outputString
      else
        return TestResult.error testName s!"Expected file not found: {expected}"

  catch e =>
    return TestResult.error testName (toString e)

/-- Find all .input files in the test directory -/
def findInputFiles (testDir : System.FilePath) : IO (Array String) := do
  let entries ← testDir.readDir
  return entries.filterMap fun f =>
    f.fileName.dropSuffix? ".input" <&> (·.toString)


/-- Print test result -/
def TestResult.print (result : TestResult) : IO Unit := do
  match result with
  | .pass name =>
    IO.println s!"✓ {name}"
  | .fail name expected actual =>
    IO.println s!"✗ {name}"
    IO.println s!"  Expected output differs from actual output"
    let d := diff (expected.split (· == '\n') |>.toArray) (actual.split (· == '\n') |>.toArray)
    IO.println (linesToString d)
  | .error name msg =>
    IO.println s!"✗ {name}"
    IO.println s!"  Error: {msg}"

/-- Print final statistics -/
def printStats (stats : TestStats) : IO Unit := do
  let total := stats.total
  IO.println ""
  IO.println s!"Tests run: {total}"
  IO.println s!"Passed: {stats.passed}"
  if stats.failed > 0 then
    IO.println s!"Failed: {stats.failed}"
  if stats.errors > 0 then
    IO.println s!"Errors: {stats.errors}"

  if stats.failed == 0 && stats.errors == 0 then
    IO.println "All tests passed! ✓"
  else
    IO.println s!"Some tests failed. ✗"

/-- Main test runner -/
def runTests (config : Config) : IO Unit := do
  unless ← System.FilePath.pathExists config.testDir do
    throw <| .userError s!"Test directory not found: {config.testDir}"

  let inputFiles ← findInputFiles config.testDir

  if inputFiles.isEmpty then
    IO.println s!"No .input files found in {config.testDir}"
    return

  if config.updateExpected then
    IO.println s!"Updating expected outputs in {config.testDir}..."
  else
    IO.println s!"Running tests in {config.testDir}..."
  IO.println ""

  let mut stats : TestStats := {}
  for inputFile in inputFiles do
    let result ← runSingleTest config inputFile
    result.print
    stats := stats.add result

  printStats stats

  if stats.failed == 0 && stats.errors == 0 then return
  else throw <| .userError s!"Failed with {stats.failed} failures and {stats.errors} errors"
