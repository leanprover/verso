/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import VersoUtil.Base64
import Errata

namespace Verso.Tests.Base64

open Verso.Base64 Errata

def checkEncode (input : ByteArray) (expected : String)
    (loc : Location := by exact here%) : TestM Unit := do
  let actual := encode input
  unless actual == expected do
    failAt loc s!"encoding {input} gave {actual.quote}, expected {expected.quote}"

-- The test vectors from RFC 4648, section 10.
@[test]
def rfc4648Vectors : Test := do
  checkEncode "".toUTF8 ""
  checkEncode "f".toUTF8 "Zg=="
  checkEncode "fo".toUTF8 "Zm8="
  checkEncode "foo".toUTF8 "Zm9v"
  checkEncode "foob".toUTF8 "Zm9vYg=="
  checkEncode "fooba".toUTF8 "Zm9vYmE="
  checkEncode "foobar".toUTF8 "Zm9vYmFy"

@[test]
def wholeAlphabet : Test := do
  let bytes : ByteArray :=
    .mk #[
      0x00, 0x10, 0x83, 0x10, 0x51, 0x87, 0x20, 0x92, 0x8b, 0x30, 0xd3, 0x8f,
      0x41, 0x14, 0x93, 0x51, 0x55, 0x97, 0x61, 0x96, 0x9b, 0x71, 0xd7, 0x9f,
      0x82, 0x18, 0xa3, 0x92, 0x59, 0xa7, 0xa2, 0x9a, 0xab, 0xb2, 0xdb, 0xaf,
      0xc3, 0x1c, 0xb3, 0xd3, 0x5d, 0xb7, 0xe3, 0x9e, 0xbb, 0xf3, 0xdf, 0xbf
    ]
  checkEncode bytes "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
  checkEncode (.mk #[0xfb, 0xff]) "+/8="
  checkEncode (.mk #[0xfc]) "/A=="
  checkEncode (.mk #[0xff, 0xff, 0xff]) "////"
  checkEncode (.mk #[0x00, 0x00, 0x00]) "AAAA"

@[test]
def thirtyTwoBytes : Test := do
  let input : ByteArray :=
    .mk #[
      0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde,
      0x5d, 0xae, 0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
      0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad
    ]
  checkEncode input "ungWv48Bz+pBQUDeXa4iI7ADYaOWF3qctBD/YfIAFa0="

def opensslBase64 (input : ByteArray) : TestM String := do
  let spawned ← IO.Process.spawn {
      cmd := "openssl", args := #["base64", "-A"],
      stdin := .piped, stdout := .piped, stderr := .piped
    } |>.toBaseIO
  let child ←
    match spawned with
    | .ok child => pure child
    | .error e => failHere s!"could not run openssl: {e}"
  let (stdin, child) ← child.takeStdin
  let stdout ← IO.asTask child.stdout.readToEnd
  let stderr ← IO.asTask child.stderr.readToEnd
  stdin.write input
  stdin.flush
  let exitCode ← child.wait
  let out ← IO.ofExcept stdout.get
  let err ← IO.ofExcept stderr.get
  unless exitCode == 0 do
    failHere s!"openssl exited with code {exitCode}" (detail? := some err)
  return out

def randomBytes (gen : StdGen) (size : Nat) : ByteArray × StdGen := Id.run do
  let mut gen := gen
  let mut bytes := ByteArray.emptyWithCapacity size
  for _ in 0...size do
    let (b, gen') := randNat gen 0 255
    gen := gen'
    bytes := bytes.push b.toUInt8
  return (bytes, gen)

-- The index of the first character at which `s` and `t` differ, with its position in each string.
-- When one string is a prefix of the other, the index is the length of the shorter one.
def firstDifference (s t : String) : Nat × s.Pos × t.Pos := Id.run do
  let mut idx := 0
  let mut p := s.startPos
  let mut q := t.startPos
  repeat
    if hp : p = s.endPos then break
    else if hq : q = t.endPos then break
    else if p.get hp != q.get hq then break
    else
      idx := idx + 1
      p := p.next hp
      q := q.next hq
  return (idx, p, q)

-- The 20 characters that start 10 characters before `p`, clipped to the string.
def window {s : String} (p : s.Pos) : String.Slice :=
  let start := p.prevn 10
  s.slice start (start.nextn 20) String.Pos.le_nextn

@[test]
def matchesOpenssl : Test := do
  let seed := (← read).seed
  let mut gen := mkStdGen seed
  let mut sizes := Array.range 301
  for _ in 0...5 do
    let (size, gen') := randNat gen 2000 10000
    gen := gen'
    sizes := sizes.push size
  for size in sizes do
    let (bytes, gen') := randomBytes gen size
    gen := gen'
    let expected ← opensslBase64 bytes
    let actual := encode bytes
    unless actual == expected do
      let (idx, expPos, actPos) := firstDifference expected actual
      failHere s!"encoding of {size} random bytes differs from openssl at index {idx}"
        (detail? := some <|
          s!"expected (from index {idx - 10}): {window expPos}\n" ++
          s!"actual (from index {idx - 10}):   {window actPos}\n" ++
          s!"expected length {expected.length}, actual length {actual.length}\n\n" ++
          s!"Reproduce with --seed {seed}.")
