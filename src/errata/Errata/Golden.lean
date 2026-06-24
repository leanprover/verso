/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.TestM
import Lean.Util.Diff

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/--
A line-by-line diff of expected against actual output. Lines marked {lit}`-` are in the expected
output only, and lines marked {lit}`+` are in the actual output only.
-/
private def goldenDiff (expected actual : String) : String :=
  let diff := Lean.Diff.diff (expected.splitOn "\n").toArray (actual.splitOn "\n").toArray
  "- expected, + actual:\n" ++ Lean.Diff.linesToString diff

/-- Compares a produced string against a golden file, or rewrites it under `--update-golden`. -/
def goldenFile (expected : System.FilePath) (actual : String) : TestM Unit := do
  let ctx ← read
  if ctx.updateGolden then
    if let some parent := expected.parent then IO.FS.createDirAll parent
    IO.FS.writeFile expected actual
  else if ← expected.pathExists then
    let want ← IO.FS.readFile expected
    unless want == actual do
      fail s!"golden mismatch for {expected}"
        (detail? := some (goldenDiff want actual))
  else
    fail s!"missing golden file {expected}"
      (detail? := some "Run with --update-golden to create it.")

/-- All files below a directory, recursively. -/
partial def filesUnder (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      out := out ++ (← filesUnder entry.path)
    else
      out := out.push entry.path
  return out

/-- The path of a file relative to a base directory. -/
private def relativeTo (base file : System.FilePath) : String :=
  (file.toString.drop (base.toString.length + 1)).copy

/-- Compares a produced directory tree against a golden tree, or rewrites it under `--update-golden`. -/
def goldenDir (expected actual : System.FilePath) : TestM Unit := do
  let ctx ← read
  let actualFiles ← filesUnder actual
  if ctx.updateGolden then
    let actualRels := actualFiles.map (relativeTo actual)
    for file in actualFiles do
      let dest := expected / relativeTo actual file
      if let some parent := dest.parent then IO.FS.createDirAll parent
      IO.FS.writeFile dest (← IO.FS.readFile file)
    -- Remove expected files that the produced output no longer contains.
    if ← expected.pathExists then
      for file in ← filesUnder expected do
        unless actualRels.contains (relativeTo expected file) do
          IO.FS.removeFile file
    return
  unless ← expected.pathExists do
    fail s!"missing golden directory {expected}"
      (detail? := some "Run with --update-golden to create it.")
  for file in actualFiles do
    let rel := relativeTo actual file
    let want := expected / rel
    unless ← want.pathExists do
      fail s!"file not present in the golden directory: {rel}"
    let wantContent ← IO.FS.readFile want
    let gotContent ← IO.FS.readFile file
    unless wantContent == gotContent do
      fail s!"golden mismatch for {rel}"
        (detail? := some (goldenDiff wantContent gotContent))
  for file in ← filesUnder expected do
    let rel := relativeTo expected file
    unless ← (actual / rel).pathExists do
      fail s!"file missing from the produced output: {rel}"
