/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso
import VersoManual
import VersoSearch.PorterStemmer
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
def testTexOutput (dir : System.FilePath) (doc : Verso.Doc.Part Verso.Genre.Manual) :
    Config →  IO Unit := fun config =>
  let versoConfig : Verso.Genre.Manual.Config := {
    destination := "src/tests/integration" / dir / "output",
    emitTeX := true,
    emitHtmlMulti := false
  }

  let runTest : IO Unit  :=
    open Verso Genre Manual in do
    let logError (msg : String) := IO.eprintln msg
    ReaderT.run (emitTeX logError versoConfig doc) extension_impls%

  Verso.Integration.runTests {
    testDir := "src/tests/integration" / dir,
    updateExpected := config.updateExpected,
    runTest
  }

open Verso.Integration in
def tests := [
  testStemmer,
  testTexOutput "sample-doc" SampleDoc.doc
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
