/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

import VersoUtil.Hash
import Errata

namespace Verso.Tests.Sha256

open Verso.Hash
open Errata

def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n.toNat) else Char.ofNat ('a'.toNat + n.toNat - 10)

def hex (bytes : ByteArray) : String :=
  bytes.foldl (init := "") fun s b => (s.push (hexDigit (b >>> 4))).push (hexDigit (b &&& 0xf))

def hashHex (input : String) : String :=
  hex (sha256 input.toUTF8)

@[test]
def nistVectors : Test := do
  -- The empty message is from the NIST CAVP byte-oriented SHA-256 test vectors (SHA256ShortMsg)
  -- (https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing).
  assertBEq "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" (hashHex "")
  -- `abc` and the 448-bit message are the SHA-256 examples that NIST publishes for FIPS 180-4
  -- (https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf), at
  -- https://csrc.nist.gov/projects/cryptographic-standards-and-guidelines/example-values.
  assertBEq "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" (hashHex "abc")
  assertBEq "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    (hashHex "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
  -- The 896-bit message is the one in NIST's SHA-384 and SHA-512 examples. Its SHA-256 digest
  -- here comes from `openssl dgst -sha256`.
  assertBEq "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"
    (hashHex ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno" ++
      "ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"))
  -- One million `a`s is the message of FIPS 180-2 Appendix B.3
  -- (https://csrc.nist.gov/files/pubs/fips/180-2/final/docs/fips180-2.pdf).
  let mut million := ByteArray.emptyWithCapacity 1000000
  for _ in 0...1000000 do
    million := million.push 'a'.toUInt8
  assertBEq "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0" (hex (sha256 million))

def alphabetPrefix (n : Nat) : String := Id.run do
  let mut s := ""
  for i in 0...n do
    s := s.push (Char.ofNat ('a'.toNat + i % 26))
  return s

/--
Each message is the first `n` bytes of the alphabet repeated. Lengths 55 and 119 are the longest
that fit their padding in the last block, and 56 and 120 are the shortest that spill padding into an
extra block. Lengths 63, 64, 65, and 128 sit at or next to a block boundary.
-/
@[test]
def paddingBoundaries : Test := do
  let cases := #[
    (55, "595615dbe4f0f407ae397d08b4c2cb870cb9b0e11937416f950c5160acf9c005"),
    (56, "784f623b787495078e93ff28a25b581df0584055a7e71d8cd90c454716b92f51"),
    (63, "5ca3e1ef5207490eac01a795e5cc94d59582a5118bf9534665c8668d87aa647c"),
    (64, "2fcd5a0d60e4c941381fcc4e00a4bf8be422c3ddfafb93c809e8d1e2bfffae8e"),
    (65, "1b3cd1877ab2f2f19f7be001722554f336cb799df0329de0bb4c118dc6abc06d"),
    (119, "faef67da856d6fd9c8d12f9ed0a4fefd3cf0ce085ab43e2907418d457e3c354b"),
    (120, "c9512b08619c19fbb503c7da6b46ef20301e5f7a7a5f43989182398536f5c5c8"),
    (128, "6c05be2c4268843ae47e68e611277ce62c02153f2f4d2e1e2a1a4b44f766cf74")
  ]
  for (n, expected) in cases do
    result "Padding boundaries: {n}" do
      let input := alphabetPrefix n
      assertBEq input.utf8ByteSize n
      assertBEq (n, expected) (n, hashHex input)

/-- Computes a digest using OpenSSL for comparison -/
def opensslDigest (input : ByteArray) : TestM ByteArray := do
  let spawned ← IO.Process.spawn {
      cmd := "openssl", args := #["dgst", "-sha256", "-binary"],
      stdin := .piped, stdout := .piped, stderr := .piped
    } |>.toBaseIO
  let child ←
    match spawned with
    | .ok child => pure child
    | .error e => failHere s!"could not run openssl: {e}"
  let (stdin, child) ← child.takeStdin
  let stdout ← IO.asTask child.stdout.readBinToEnd
  let stderr ← IO.asTask child.stderr.readToEnd
  stdin.write input
  stdin.flush
  let exitCode ← child.wait
  let out ← IO.ofExcept stdout.get
  let err ← IO.ofExcept stderr.get
  unless exitCode == 0 do
    failHere s!"openssl exited with code {exitCode}" (detail? := some err)
  return out

-- Short lengths cover every remainder modulo 64. Clustered lengths lie between 9 bytes below and
-- 1 byte above a multiple of 64. Some lengths span several kilobytes.
def randomLength (gen : StdGen) : Nat × StdGen :=
  let (kind, gen) := randNat gen 0 9
  if kind < 5 then randNat gen 0 200
  else if kind < 9 then
    let (blocks, gen) := randNat gen 1 5
    let (offset, gen) := randNat gen 0 10
    (blocks * 64 - 9 + offset, gen)
  else randNat gen 2000 9000

def randomBytes (gen : StdGen) (size : Nat) : ByteArray × StdGen := Id.run do
  let mut gen := gen
  let mut bytes := ByteArray.emptyWithCapacity size
  for _ in 0...size do
    let (b, gen') := randNat gen 0 255
    gen := gen'
    bytes := bytes.push b.toUInt8
  return (bytes, gen)

-- Smaller inputs to try in place of a failing one: each half, the input without its first or last
-- byte, and the input with its first nonzero byte set to zero.
def shrinkCandidates (bytes : ByteArray) : Array ByteArray := Id.run do
  let n := bytes.size
  let mut out := #[]
  if n ≥ 2 then
    out := out.push (bytes.extract 0 (n / 2)) |>.push (bytes.extract (n / 2) n)
  if n ≥ 1 then
    out := out.push (bytes.extract 0 (n - 1)) |>.push (bytes.extract 1 n)
  for h : i in 0...n do
    if bytes[i] != 0 then
      out := out.push (bytes.set i 0)
      break
  return out

def mismatches (bytes : ByteArray) : TestM Bool :=
  return (← opensslDigest bytes) != sha256 bytes

def shrink (bytes : ByteArray) : TestM ByteArray := do
  let mut current := bytes
  let mut progress := true
  while progress do
    progress := false
    for candidate in shrinkCandidates current do
      if ← mismatches candidate then
        current := candidate
        progress := true
        break
  return current

@[test]
def matchesOpenssl : Test := do
  let seed := (← read).seed
  let mut gen := mkStdGen seed
  for _ in 0...300 do
    let (size, gen') := randomLength gen
    let (bytes, gen') := randomBytes gen' size
    gen := gen'
    if ← mismatches bytes then
      let minimal ← shrink bytes
      failHere s!"digest differs from openssl for a {minimal.size}-byte input"
        (detail? := some <|
          s!"input: {hex minimal}\n" ++
          s!"expected: {hex (← opensslDigest minimal)}\n" ++
          s!"actual:   {hex (sha256 minimal)}\n\n" ++
          s!"Reproduce with --seed {seed}.")
