/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoSearch.PorterStemmer
import Tests
import Verso.Parser

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

def testBlockParser (config : Config) : IO Unit := do
  Verso.GoldenTest.runTests {
    testDir := "src/tests/parser/blocks"
    runTest := Verso.Parser.blocks {} |>.test
    updateExpected := config.updateExpected
  }

def testParser (dir : System.FilePath) (fn : Lean.Parser.ParserFn) : Config → IO Unit := fun config =>
  Verso.GoldenTest.runTests {
    testDir := ("src/tests/parser" : System.FilePath) / dir,
    runTest := fn.test,
    updateExpected := config.updateExpected
  }

open Lean.Parser in
open Verso.Parser in
def tests := [
  testStemmer, testBlockParser,
  testParser "metadataBlock" metadataBlock,
  testParser "val" val,
  testParser "arg" arg,
  testParser "nameAndArgs" nameAndArgs,
  testParser "inlineTextChar" inlineTextChar,
  testParser "manyInlineTextChar" (asStringFn (many1Fn inlineTextChar)),
  testParser "inline/emph" (emph {}),
  testParser "inline/code" code,
  testParser "inline/role" (role {}),
  testParser "inline" (inline {}),
  testParser "block/code" (codeBlock {}),
  testParser "block/blocks" (blocks {}),
  testParser "block/directive" (directive {}),
  testParser "block/ulIndicator" (lookaheadUnorderedListIndicator {} (fun type => fakeAtom s! "{repr type}")),
  testParser "block/olIndicator" (lookaheadOrderedListIndicator {} (fun type i => fakeAtom s! "{repr type} {i}")),
  testParser "block/" (block {}),

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
