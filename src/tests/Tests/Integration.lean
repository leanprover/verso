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

/--
Given an array of pairs `(src, tgt)` of absolute paths, copy every
`src` to every `tgt`, creating directories as necessary.
-/
partial def copyFiles (pairs : Array (System.FilePath × System.FilePath)) :
    IO Unit := do
  for (src, tgt) in pairs do
    if let .some parent := tgt.parent then
      IO.FS.createDirAll parent
    IO.FS.writeBinFile tgt (← IO.FS.readBinFile src)

/-- Main test runner -/
def runTests (config : Config) : IO Unit := do
  unless ← System.FilePath.pathExists config.testDir do
    throw <| .userError s!"Test directory not found: {config.testDir}"

  let outputRoot := config.testDir / "output"
  let expectedRoot := config.testDir / "expected"

  if config.updateExpected then
    let outputFiles := (← filesBelow outputRoot)
    IO.println s!"Updating expected outputs in {config.testDir}..."
    if ← System.FilePath.pathExists expectedRoot then do
      IO.FS.removeDirAll expectedRoot
    copyFiles (outputFiles.map (fun p => (outputRoot / p, expectedRoot / p)))
  else
    unless ← System.FilePath.pathExists expectedRoot do
      throw <| .userError s!"Expected output directory not found: {expectedRoot}"
    let expectedFiles := (← filesBelow expectedRoot)

    IO.println s!"Running test in {config.testDir}..."
    if ← outputRoot.pathExists then
      IO.FS.removeDirAll outputRoot
    config.runTest
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
