/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jason Reed
-/
import Lean.Util.Diff

namespace Verso.Integration

/-- Configuration for the test runner -/
structure Config where
  /-- Where are expected files located? We expect a subdirectory
  `expected` and `runTest` should produce files into a subdirectory
  `output`. -/
  testDir : System.FilePath
  /-- Should the expected output be replaced with the actual output? -/
  updateExpected : Bool := false
  /-- How to run the test -/
  runTest : IO Unit

/--
Returns all non-directory filepaths that are children of `root`, which
must be a directory. Returns these as paths relative to `root`.

This differs from `System.FilePath.walkRoot`, in that the latter returns
absolute paths, and includes subdirectories.
-/
partial def filesBelow (root : System.FilePath) :
    IO (Array System.FilePath) := Prod.snd <$> StateT.run (go ".") #[]
where
  go (p : System.FilePath) := do
    for d in (← (root / p).readDir) do
      if ← d.path.isDir then
        go (p / d.fileName)
      else
        modify (·.push (p / d.fileName))

/-- Main test runner -/
def runTests (config : Config) : IO Unit := do
  unless ← System.FilePath.pathExists config.testDir do
    throw <| .userError s!"Test directory not found: {config.testDir}"

  let expectedRoot := config.testDir / "expected"
  let outputRoot := config.testDir / "output"

  unless ← System.FilePath.pathExists expectedRoot do
    throw <| .userError s!"Expected output directory not found: {expectedRoot}"

  if config.updateExpected then
    IO.println s!"Updating expected outputs in {config.testDir}..."
    IO.FS.removeDirAll expectedRoot
    IO.println s!"TODO: cp -r {outputRoot} {expectedRoot}"
  else
    IO.println s!"Running test in {config.testDir}..."
    if ← outputRoot.pathExists then
      IO.FS.removeDirAll outputRoot
    config.runTest

    let expectedFiles := (← filesBelow expectedRoot)
    let outputFiles := (← filesBelow outputRoot)

    if expectedFiles != outputFiles then
      IO.println s!"✗ Expected files differ from actual files"
      IO.println s!"Expected files in {expectedRoot}:\n  {expectedFiles}"
      IO.println s!"Actual files in {outputRoot}:\n  {outputFiles}"
      throw <| .userError s!"Test in {config.testDir} failed"

    for file in expectedFiles do
      let expected ← IO.FS.readFile (expectedRoot / file)
      let actual ← IO.FS.readFile (outputRoot / file)
      if expected != actual then
        let d := Lean.Diff.diff (expected.split (· == '\n') |>.toArray) (actual.split (· == '\n') |>.toArray)
        IO.println s!"✗ In test {config.testDir}, output file {file}"
        IO.println s!"  Expected output differs from actual output"
        IO.println (Lean.Diff.linesToString d)
        throw <| .userError s!"Test in {config.testDir} failed"

  return
