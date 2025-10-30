/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoUtil.BinFiles.Z85

open Verso.BinFiles.Z85

section Test

private def ofArray (xs : Array UInt8) : ByteArray :=
  xs.foldl (init := ByteArray.emptyWithCapacity xs.size) ByteArray.push

-- Test functions
private def testEncode : IO Unit := do
  let testData : Array UInt8 := #[72, 101, 108, 108, 111]  -- "Hello"
  let encoded := encode (ofArray testData)
  IO.println s!"Encoded: {encoded}"


private def testDecode : IO Unit := do
  let testEncoded := "By/JnwmoN*"
  let decoded := decode testEncoded 8
  IO.println s!"Decoded bytes: {decoded}"
  -- Convert back to string for verification
  let chars := decoded.toList.map (fun b => Char.ofUInt8 b)
  IO.println s!"Decoded string: {String.mk chars}"

private def testRoundTrip : IO Unit := do
  let original : Array UInt8 := #[72, 101, 108, 108, 111, 32, 87, 111, 114, 108, 100, 33]  -- "Hello World!"
  let encoded := encode (ofArray original)
  IO.println s!"Original: {original}"
  IO.println s!"Encoded: {encoded}"

  let decoded := decode encoded original.size
  IO.println s!"Decoded: {decoded}"
  IO.println s!"Round trip successful: {original == decoded.toList.toArray}"


private local instance : BEq ByteArray where
  beq xs ys :=
    if h : xs.size = ys.size then
      xs.size.all fun i h => xs[i] = ys[i]
    else
      false

private def testRoundTripOf (original : ByteArray) : IO Unit := do
  let encoded := encode original
  let decoded := decode encoded original.size
  unless original == decoded do
    throw <| .userError "Mismatch"

private def test : IO Unit := do
  testEncode
  testDecode
  testRoundTrip
  IO.setRandSeed 5
  for i in [0:15] do
    let arr ← i.foldM (init := ByteArray.empty) fun _ _ xs => (xs.push <| UInt8.ofNat ·) <$> (IO.rand 0 256)
    testRoundTripOf arr


/--
info: Encoded: nm=QNzVx+q
Decoded bytes: [116, 101, 115, 116, 100, 97, 116, 97]
Decoded string: testdata
Original: #[72, 101, 108, 108, 111, 32, 87, 111, 114, 108, 100, 33]
Encoded: nm=QNzY&b1A+]nf
Decoded: [72, 101, 108, 108, 111, 32, 87, 111, 114, 108, 100, 33]
Round trip successful: true
-/
#guard_msgs in
#eval test

end Test
