/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso
import VersoManual
import VersoSearch.PorterStemmer
import VersoUtil.LzCompress
import Tests

structure Config where
  updateExpected : Bool := false

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
def testTexOutput (dir : System.FilePath) (doc : Verso.Doc.VersoDoc Verso.Genre.Manual) :
    Config →  IO Unit := fun config =>
  let versoConfig : Verso.Genre.Manual.Config := {
    destination := "src/tests/integration" / dir / "output",
    emitTeX := true,
    emitHtmlMulti := false
  }

  let runTest : IO Unit  :=
    open Verso Genre Manual in do
    let logError (msg : String) := IO.eprintln msg
    ReaderT.run (emitTeX logError versoConfig doc.toPart) extension_impls%

  Verso.Integration.runTests {
    testDir := "src/tests/integration" / dir,
    updateExpected := config.updateExpected,
    runTest
  }

def testZip (_ : Config) : IO Unit := do
  IO.println "Running zip tests with fixed files..."
  testExtract #[] .store
  testExtract #[] .deflate
  testExtract #[("empty", .empty)] .store
  testExtract #[("empty", .empty)] .deflate
  testExtract files .store
  testExtract files .deflate
  for i in (0 : Nat)...(me.size / 10) do
    let me := me.extract 0 (i * 10)
    testExtract #[("T2.lean", me)] .store
    testExtract #[("T2.lean", me)] .deflate
  for i in (0 : Nat)...(me.size / 10) do
    let me := me.extract 0 (i * 10)
    let bwd := bwd.extract 0 (i * 10)
    testExtract #[("T2.lean", me), ("other", bwd)] .store
    testExtract #[("T2.lean", me), ("other", bwd)] .deflate
  for _ in (0 : Nat)...10 do
    IO.setRandSeed (← IO.monoNanosNow)
    let mut randFiles := #[]
    for _ in 0...(← IO.rand 0 15) do
      let name ← randName
      let size ← IO.rand 0 50000
      let content ← IO.getRandomBytes <| .ofNat size
      randFiles := randFiles.push (name, content)
    IO.println s!"Running random zip test with {randFiles.size} files, sizes:"
    for (x, y) in randFiles do
      IO.println s!" * {x}: {y.size} bytes"
    testExtract randFiles .store
    testExtract randFiles .deflate


where
  files := #[("x.txt", "abcdef\nlkjlkj".bytes), ("y.txt", "".bytes), ("z.txt", "abc\n\n".bytes)]
  me := (include_str "TestMain.lean").bytes
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
    throw <| .userError "Mismatched lzCompress output"

open Verso.Integration in
def tests := [
  testStemmer,
  testTexOutput "sample-doc" SampleDoc.doc,
  testZip
]

def getConfig (config : Config) : List String → IO Config
  | [] => pure config
  | "--update-expected" :: args => getConfig { config with updateExpected := true } args
  | other :: _ => throw <| .userError s!"Didn't understand {other}"

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
