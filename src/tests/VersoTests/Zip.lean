/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import VersoUtil.Zip
import Errata

open Verso.Zip Errata

/-!
Tests round-tripping files through the zip writer and the external `unzip` tool.
-/

/-- A block of Lean-code-shaped bytes to zip: the project's lakefile. -/
def sampleBytes : ByteArray := (include_str "../../../lakefile.lean").toByteArray

/-- A random `stem.ext` filename. -/
private def randName : IO String := do
  let len ← IO.rand 1 10
  let stem ← len.foldM (init := "") fun _ _ acc => do
    return acc.push <| Char.ofNat ('a'.toNat + (← IO.rand 0 25))
  let len ← IO.rand 2 4
  let ext ← len.foldM (init := "") fun _ _ acc => do
    return acc.push <| Char.ofNat ('a'.toNat + (← IO.rand 0 25))
  return stem ++ "." ++ ext

/-- Zips `files` with `method`, extracts the archive with `unzip`, and checks each file round-trips. -/
def extractRoundTrips (files : Array (String × ByteArray)) (method : CompressionMethod)
    (loc : Location := by exact here%) : TestM Unit :=
  IO.FS.withTempDir fun dir => do
    let dir := dir / s!"{← IO.monoMsNow}"
    IO.FS.createDirAll dir
    let archive := dir / "out.zip"
    zipToFile archive files method
    let out ← IO.Process.output { cmd := "unzip", args := #["-u", archive.toString, "-d", dir.toString] }
    -- `unzip` returns 1 on an empty archive and 2 on a corrupt one.
    unless out.exitCode == 0 || (files.isEmpty && out.exitCode == 1) do
      failAt loc s!"unzip exited with code {out.exitCode}" (detail? := some out.stderr)
    for (name, contents) in files do
      let found ← IO.FS.readBinFile (dir / name)
      unless found == contents do
        failAt loc s!"contents of {name} do not match"
          (detail? := some s!"expected {contents.size} bytes, got {found.size}")

/-- Fixed file sets round-trip under both compression methods. -/
@[test]
def zipFixed : Test := do
  let files := #[("x.txt", "abcdef\nlkjlkj".toByteArray), ("y.txt", "".toByteArray),
    ("z.txt", "abc\n\n".toByteArray)]
  for method in [CompressionMethod.store, .deflate] do
    extractRoundTrips #[] method
    extractRoundTrips #[("empty", .empty)] method
    extractRoundTrips files method

/-- Increasingly large prefixes of a block round-trip, alone and paired with another. -/
@[test]
def zipChunked : Test := do
  let me := sampleBytes
  let bwd := me.foldl (init := .empty) fun acc b => ByteArray.empty.push b ++ acc
  let chunk := me.size / 10
  for method in [CompressionMethod.store, .deflate] do
    for i in [0:11] do
      let block := me.extract 0 (i * chunk)
      extractRoundTrips #[("T2.lean", block)] method
      extractRoundTrips #[("T2.lean", block), ("other", bwd.extract 0 (i * chunk))] method

/-- Random file sets round-trip under both compression methods. -/
@[test]
def zipRandom : Test := do
  for _ in [0:10] do
    let seed ← IO.monoNanosNow
    IO.setRandSeed seed
    -- Printed only if the test fails, so a failure is reproducible.
    IO.println s!"random seed: {seed}"
    let count ← IO.rand 0 15
    let mut files := #[]
    for _ in [0:count] do
      let bytes ← IO.getRandomBytes (.ofNat (← IO.rand 0 50000))
      files := files.push (← randName, bytes)
    for method in [CompressionMethod.store, .deflate] do
      extractRoundTrips files method
