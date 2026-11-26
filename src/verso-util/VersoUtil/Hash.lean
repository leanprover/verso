/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

namespace Verso.Hash

/-!
The round constants and initial hash value are from FIPS 180-4, sections 4.2.2 and 5.3.3
(https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf).
-/

def roundConstants : Vector UInt32 64 := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

structure State where
  a : UInt32 := 0x6a09e667
  b : UInt32 := 0xbb67ae85
  c : UInt32 := 0x3c6ef372
  d : UInt32 := 0xa54ff53a
  e : UInt32 := 0x510e527f
  f : UInt32 := 0x9b05688c
  g : UInt32 := 0x1f83d9ab
  h : UInt32 := 0x5be0cd19

@[inline] def rotr (x n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

@[inline] def readWord (data : ByteArray) (off : Nat) (h : off + 4 ≤ data.size) : UInt32 :=
  (data[off].toUInt32 <<< 24) ||| (data[off + 1].toUInt32 <<< 16) |||
    (data[off + 2].toUInt32 <<< 8) ||| data[off + 3].toUInt32

def loadBlock (w : Vector UInt32 64) (data : ByteArray) (off : Nat)
    (hoff : off + 64 ≤ data.size) (i : Nat) : Vector UInt32 64 :=
  if h : i < 16 then
    loadBlock (w.set i (readWord data (off + 4 * i) (by grind))) data off hoff (i + 1)
  else w
termination_by 16 - i

def expand (w : Vector UInt32 64) (i : Nat) : Vector UInt32 64 :=
  if h : i < 64 then
    let w15 := w[i - 15]
    let w2 := w[i - 2]
    let s0 := rotr w15 7 ^^^ rotr w15 18 ^^^ (w15 >>> 3)
    let s1 := rotr w2 17 ^^^ rotr w2 19 ^^^ (w2 >>> 10)
    expand (w.set i (w[i - 16] + s0 + w[i - 7] + s1)) (i + 1)
  else w
termination_by 64 - i

def rounds (w : Vector UInt32 64) (i : Nat) (a b c d e f g h : UInt32) : State :=
  if hi : i < 64 then
    let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ (~~~e &&& g)
    let t1 := h + s1 + ch + roundConstants[i] + w[i]
    let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    rounds w (i + 1) (t1 + s0 + maj) a b c (d + t1) e f g
  else { a, b, c, d, e, f, g, h }
termination_by 64 - i

/--
Processes the 64-byte block of `data` that starts at `off`.

The schedule `w` is returned so that the next block reuses its storage.
-/
def compress (st : State) (w : Vector UInt32 64) (data : ByteArray) (off : Nat)
    (hoff : off + 64 ≤ data.size) : State × Vector UInt32 64 :=
  let w := expand (loadBlock w data off hoff 0) 16
  let r := rounds w 0 st.a st.b st.c st.d st.e st.f st.g st.h
  let st' := {
    a := st.a + r.a, b := st.b + r.b, c := st.c + r.c, d := st.d + r.d,
    e := st.e + r.e, f := st.f + r.f, g := st.g + r.g, h := st.h + r.h
  }
  (st', w)

/-- Processes blocks `i` through `n - 1` of `data`. -/
def compressBlocks (st : State) (w : Vector UInt32 64) (data : ByteArray) (n : Nat)
    (hn : 64 * n ≤ data.size) (i : Nat) : State × Vector UInt32 64 :=
  if h : i < n then
    let (st, w) := compress st w data (64 * i) (by grind)
    compressBlocks st w data n hn (i + 1)
  else (st, w)
termination_by n - i

def pushWord (out : ByteArray) (x : UInt32) : ByteArray :=
  out.push (x >>> 24).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 8).toUInt8 |>.push x.toUInt8

public def sha256 (input : ByteArray) : ByteArray := Id.run do
  let size := input.size
  let fullBlocks := size / 64
  let (st, w) := compressBlocks {} (Vector.replicate 64 0) input fullBlocks (by grind) 0
  -- The final one or two blocks hold the remaining bytes, a 0x80 byte, zeros, and the message
  -- length in bits as a 64-bit big-endian integer. The zeros bring the length to 56 modulo 64.
  let mut tail := input.extract (64 * fullBlocks) size |>.push 0x80
  for _ in 0...(119 - size % 64) % 64 do
    tail := tail.push 0
  let bits := size.toUInt64 * 8
  for i in 0...8 do
    tail := tail.push (bits >>> (56 - 8 * i).toUInt64).toUInt8
  let (st, _) := compressBlocks st w tail (tail.size / 64) (by grind) 0
  let mut out := ByteArray.emptyWithCapacity 32
  for x in #[st.a, st.b, st.c, st.d, st.e, st.f, st.g, st.h] do
    out := pushWord out x
  return out
