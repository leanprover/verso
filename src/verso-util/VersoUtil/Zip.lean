module

import Std.Tactic.Do
import Std.Tactic.BVDecide

namespace Verso.Zip

open Std.Do

namespace CRC32

def table : Array UInt32 := Id.run do
  let mut table : Array UInt32 := .emptyWithCapacity 255
  for n in (0 : UInt32)...256 do
    table := table.push <| computeCrc n
  return table
where
  computeCrc (n : UInt32) : UInt32 := Id.run do
    let mut crc := n
    for _ in (0 : Nat)...8 do
      crc :=
        if crc % 2 == 1 then
          (crc >>> 1) ^^^ 0xEDB88320
        else crc >>> 1
    return crc


set_option mvcgen.warning false in
open Std in
@[simp, grind =]
theorem table.size_eq : table.size = 256 := by
  generalize h : table = x
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, tableSoFar⟩ =>
    ⌜tableSoFar.size = xs.prefix.length⌝
  case vc1 => grind
  case vc3 h =>
    rw [Rco.length_toList] at h
    simp_all [Rco.size, Iterators.Iter.size, Iterators.IteratorSize.size,
      Iterators.Iter.toIterM, Rco.Internal.iter, Rxo.HasSize.size, Rxc.HasSize.size]

#guard table[0] = 0x00000000
#guard table[1] = 0x77073096
#guard table[2] = 0xEE0E612C
#guard table[3] = 0x990951BA
#guard table[128] = 0xEDB88320
#guard table[255] = 0x2D02EF8D

def crc32 (data : ByteArray) : UInt32 := Id.run do
  let mut crc := 0xFFFFFFFF
  for byte in data do
    let idx := ((crc ^^^ byte.toUInt32) &&& 0xff)
    have : idx.toNat < table.size := by
      suffices idx < 256 by rw [table.size_eq]; assumption
      bv_decide
    crc := (crc >>> 8) ^^^ table[idx.toNat]
  return crc ^^^ 0xFFFFFFFF

#guard crc32 "123456789".bytes = 0xCBF43926
#guard crc32 "Hello, World!".bytes = 0xEC4AC3D0

end CRC32

namespace BitWriter
structure State where
  bytes : ByteArray := ByteArray.empty
  currentByte : UInt8 := 0
  /-- Position in current byte (0-7) -/
  bitPos : UInt8 := 0
  bitPos_lt_8 : bitPos < 8 := by grind

namespace State
def writeBit (bw : State) (bit : Bool) : State :=
  let bw := { bw with currentByte := bw.currentByte ||| (if bit then (1 : UInt8) <<< bw.bitPos else 0) }
  if h : bw.bitPos ≥ 7 then
    { bytes := bw.bytes.push bw.currentByte, currentByte := 0, bitPos := 0 }
  else
    { bw with bitPos := bw.bitPos + 1, bitPos_lt_8 := by grind }

def writeBits (bw : State) (value : UInt32) (numBits : Nat) : State :=
  let rec loop (bw : State) (v : UInt32) (n : Nat) : State :=
    match n with
    | 0 => bw
    | n' + 1 =>
      let bw := bw.writeBit ((v &&& 1) != 0)
      loop bw (v >>> 1) n'
  loop bw value numBits

def flush (bw : State) : ByteArray :=
  if bw.bitPos > 0 then
    bw.bytes.push bw.currentByte
  else
    bw.bytes
end State

end BitWriter


public inductive CompressionMethod where
  | store    -- No compression (method 0)
  | deflate  -- DEFLATE compression (method 8)
deriving Repr

def CompressionMethod.header : CompressionMethod → UInt16
  | .store => 0x0000
  | .deflate => 0x0008

structure FileEntry where
  name : String
  data : ByteArray
  crc : UInt32
  offset : UInt32
  compressedData : ByteArray
  compressionMethod : CompressionMethod

namespace DEFLATE

/-- LZ77 match: (length, distance) -/
structure Match where
  length : UInt32
  distance : UInt32

/--
Finds LZ77 matches using a simple hash table.

32768 is the largest window allowed by DEFLATE.
-/
def findMatches (data : ByteArray) (maxMatchLen : UInt32 := 258) (windowSize : UInt32 := 32768) : Array (Option Match) := Id.run do
  let mut result := #[]
  let mut hashTable : Std.HashMap UInt32 UInt32 := {}

  -- Computes a quick "fingerprint" of the indicated byte plus the next three bytes.
  -- Three bytes are used because it's the minimum match length of DEFLATE.
  -- Returns none at the end of the file.
  let hash3 (pos : UInt32) : Option UInt32 :=
    if h : pos.toNat + 2 < data.size then
      let x := data[pos.toNat].toUInt32
      let y := data[pos.toNat + 1].toUInt32 <<< 5
      let z := data[pos.toNat + 2].toUInt32 <<< 10
      some (x ^^^ y ^^^ z)
    else
      none

  for i in 0...data.size.toUInt32 do
    match hash3 i with
    | none =>
      result := result.push none
    | some h =>
      match hashTable[h]? with
      | none =>
        -- This 3-byte sequence hasn't been seen before, so it's new. Just emit it.
        result := result.push none
      | some prevPos =>
        let windowStart : UInt32 :=
          if i < windowSize then 0 else i - windowSize
        -- The sequence was seen before, at position `prevPos`. If it's close enough, then we can re-use it!
        if prevPos >= windowStart && prevPos < i then
          -- Find match length
          let mut matchLen : UInt32 := 0
          let maxLen := min maxMatchLen (data.size.toUInt32 - i)
          for j in 0...maxLen do
            if prevPos + j < data.size.toUInt32 && data[prevPos + j |>.toNat]! == data[i + j |>.toNat]! then
              matchLen := matchLen + 1
            else
              break

          if matchLen >= 3 then
            -- Remember the reference to the prior content
            result := result.push (some { length := matchLen, distance := i - prevPos : Match})
          else
            result := result.push none
        else
          result := result.push none

      hashTable := hashTable.insert h i

  return result

/-- Length codes and extra bits for DEFLATE -/
def lengthCode (len : UInt32) : UInt32 × UInt32 :=
  if len <= 10 then (254 + len, 0)
  else if len <= 18 then (265 + (len - 11) / 2, if len % 2 == 1 then 1 else 0)
  else if len <= 34 then (269 + (len - 19) / 4, (len - 19) % 4)
  else if len <= 66 then (273 + (len - 35) / 8, (len - 35) % 8)
  else if len <= 130 then (277 + (len - 67) / 16, (len - 67) % 16)
  else if len <= 257 then (281 + (len - 131) / 32, (len - 131) % 32)
  else (285, 0)

/-- Distance codes and extra bits for DEFLATE -/
def distanceCode (dist : UInt32) : UInt32 × UInt32 :=
  if dist <= 4 then (dist - 1, 0)
  else if dist <= 8 then (4 + (dist - 5) / 2, if dist % 2 == 1 then 1 else 0)
  else if dist <= 16 then (6 + (dist - 9) / 4, (dist - 9) % 4)
  else if dist <= 32 then (8 + (dist - 17) / 8, (dist - 17) % 8)
  else if dist <= 64 then (10 + (dist - 33) / 16, (dist - 33) % 16)
  else if dist <= 128 then (12 + (dist - 65) / 32, (dist - 65) % 32)
  else if dist <= 256 then (14 + (dist - 129) / 64, (dist - 129) % 64)
  else if dist <= 512 then (16 + (dist - 257) / 128, (dist - 257) % 128)
  else if dist <= 1024 then (18 + (dist - 513) / 256, (dist - 513) % 256)
  else if dist <= 2048 then (20 + (dist - 1025) / 512, (dist - 1025) % 512)
  else if dist <= 4096 then (22 + (dist - 2049) / 1024, (dist - 2049) % 1024)
  else if dist <= 8192 then (24 + (dist - 4097) / 2048, (dist - 4097) % 2048)
  else if dist <= 16384 then (26 + (dist - 8193) / 4096, (dist - 8193) % 4096)
  else (28 + (dist - 16385) / 8192, (dist - 16385) % 8192)

/-- Reverse bits in a value -/
def reverseBits (value : UInt32) (numBits : Nat) : UInt32 :=
  let rec loop (v : UInt32) (result : UInt32) (n : Nat) : UInt32 :=
    if n = 0 then result
    else loop (v >>> 1) ((result <<< 1) ||| (v &&& 1)) (n - 1)
  loop value 0 numBits

/-- Fixed Huffman codes for literals/lengths -/
def fixedLiteralCode (value : UInt32) : UInt32 × Nat :=
  if value <= 143 then
    (0b00110000 + value, 8)
  else if value <= 255 then
    (0b110010000 + (value - 144), 9)
  else if value <= 279 then
    (0b0000000 + (value - 256), 7)
  else
    (0b11000000 + (value - 280), 8)

/-- Helper to calculate base value for length codes -/
def lengthBase (code : UInt32) : UInt32 :=
  if code < 265 then 3
  else if code < 269 then 11 + ((code - 265) * 2)
  else if code < 273 then 19 + ((code - 269) * 4)
  else if code < 277 then 35 + ((code - 273) * 8)
  else if code < 281 then 67 + ((code - 277) * 16)
  else if code < 285 then 131 + ((code - 281) * 32)
  else 258

/-- Helper to calculate base value for distance codes -/
def distanceBase (code : UInt32) : UInt32 :=
  if code < 4 then code + 1
  else if code < 6 then 5 + ((code - 4) * 2)
  else if code < 8 then 9 + ((code - 6) * 4)
  else if code < 10 then 17 + ((code - 8) * 8)
  else if code < 12 then 33 + ((code - 10) * 16)
  else if code < 14 then 65 + ((code - 12) * 32)
  else if code < 16 then 129 + ((code - 14) * 64)
  else if code < 18 then 257 + ((code - 16) * 128)
  else if code < 20 then 513 + ((code - 18) * 256)
  else if code < 22 then 1025 + ((code - 20) * 512)
  else if code < 24 then 2049 + ((code - 22) * 1024)
  else if code < 26 then 4097 + ((code - 24) * 2048)
  else if code < 28 then 8193 + ((code - 26) * 4096)
  else 16385 + ((code - 28) * 8192)

/-- Number of extra bits for length codes -/
def lengthExtraBits (code : Nat) : Nat :=
  if code < 265 then 0
  else if code < 269 then 1
  else if code < 273 then 2
  else if code < 277 then 3
  else if code < 281 then 4
  else if code < 285 then 5
  else 0


/-- Number of extra bits for distance codes -/
def distanceExtraBits (code : UInt32) : Nat :=
  if code < 4 then 0
  else if code < 6 then 1
  else if code < 8 then 2
  else if code < 10 then 3
  else if code < 12 then 4
  else if code < 14 then 5
  else if code < 16 then 6
  else if code < 18 then 7
  else if code < 20 then 8
  else if code < 22 then 9
  else if code < 24 then 10
  else if code < 26 then 11
  else if code < 28 then 12
  else 13

/-- Compress data using DEFLATE with fixed Huffman codes -/
def compress (data : ByteArray) : ByteArray := Id.run do
  let mut bw : BitWriter.State := {}

  -- DEFLATE block header: BFINAL=1, BTYPE=01 (fixed Huffman)
  bw := bw.writeBits 0b011 3

  let «matches» := findMatches data
  let mut i : UInt32 := 0

  while h : i < data.size.toUInt32 do
    match «matches»[i.toNat]! with
    | some «match» =>
      -- Emit length/distance pair
      let (lenCode, _) := lengthCode match.length
      let (lenHuff, lenBits) := fixedLiteralCode lenCode
      let lenHuffRev := reverseBits lenHuff lenBits
      bw := bw.writeBits lenHuffRev lenBits

      -- Extra bits for length (if any)
      let numExtraBits := lengthExtraBits lenCode.toNat
      if numExtraBits > 0 then
        let extraVal := match.length - lengthBase lenCode
        bw := bw.writeBits extraVal numExtraBits

      -- Distance code
      let (distCode, _) := distanceCode match.distance
      let distHuff := reverseBits distCode 5
      bw := bw.writeBits distHuff 5

      -- Extra bits for distance (if any)
      let numDistExtra := distanceExtraBits distCode
      if numDistExtra > 0 then
        let extraVal := match.distance - distanceBase distCode
        bw := bw.writeBits extraVal numDistExtra

      i := i + match.length
    | none =>
      -- Emit literal
      let byte := data[i.toNat]!
      let (litHuff, litBits) := fixedLiteralCode byte.toUInt32
      let litHuffRev := reverseBits litHuff litBits
      bw := bw.writeBits litHuffRev litBits
      i := i + 1

  -- End of block marker (256)
  let (endHuff, endBits) := fixedLiteralCode 256
  let endHuffRev := reverseBits endHuff endBits
  bw := bw.writeBits endHuffRev endBits

  return bw.flush

end DEFLATE

section

variable [Monad m] [MonadState ByteArray m]

def writeUInt16LE (val : UInt16) : m Unit := do
  modify fun bytes =>
    bytes |>.push val.toUInt8 |>.push (val >>> 8).toUInt8

def writeUInt32LE (val : UInt32) : m Unit := do
  modify fun bytes =>
    bytes
      |>.push val.toUInt8
      |>.push (val >>> 8).toUInt8
      |>.push (val >>> 16).toUInt8
      |>.push (val >>> 24).toUInt8

def writeLocalFileHeader [Monad m] [MonadState ByteArray m] (entry : FileEntry) : m Unit := do
  let nameBytes := entry.name.toUTF8
  writeUInt32LE 0x04034b50  -- signature
  writeUInt16LE 0x0014       -- version needed (2.0 for DEFLATE)
  writeUInt16LE 0x0000       -- flags
  writeUInt16LE entry.compressionMethod.header
  writeUInt16LE 0x0000       -- mod time
  writeUInt16LE 0x0000       -- mod date
  writeUInt32LE entry.crc    -- crc32
  writeUInt32LE entry.compressedData.size.toUInt32  -- compressed size
  writeUInt32LE entry.data.size.toUInt32  -- uncompressed size
  writeUInt16LE nameBytes.size.toUInt16   -- filename length
  writeUInt16LE 0x0000       -- extra field length
  modify (· ++ nameBytes)    -- filename

def writeCentralDirHeader [Monad m] [MonadState ByteArray m] (entry : FileEntry) : m Unit := do
  let nameBytes := entry.name.toUTF8
  writeUInt32LE 0x02014b50  -- signature
  writeUInt16LE 0x0014       -- version made by
  writeUInt16LE 0x0014       -- version needed
  writeUInt16LE 0x0000       -- flags
  writeUInt16LE entry.compressionMethod.header
  writeUInt16LE 0x0000       -- mod time
  writeUInt16LE 0x0000       -- mod date
  writeUInt32LE entry.crc    -- crc32
  writeUInt32LE entry.compressedData.size.toUInt32  -- compressed size
  writeUInt32LE entry.data.size.toUInt32  -- uncompressed size
  writeUInt16LE nameBytes.size.toUInt16   -- filename length
  writeUInt16LE 0x0000       -- extra field length
  writeUInt16LE 0x0000       -- comment length
  writeUInt16LE 0x0000       -- disk number
  writeUInt16LE 0x0000       -- internal attrs
  writeUInt32LE 0x00000000   -- external attrs
  writeUInt32LE entry.offset -- offset of local header
  modify (· ++ nameBytes)    -- filename

def writeEndOfCentralDir [Monad m] [MonadState ByteArray m] (numEntries : UInt16) (cdSize : UInt32) (cdOffset : UInt32) : m Unit := do
  writeUInt32LE 0x06054b50  -- signature
  writeUInt16LE 0x0000       -- disk number
  writeUInt16LE 0x0000       -- central dir start disk
  writeUInt16LE numEntries   -- entries on this disk
  writeUInt16LE numEntries   -- total entries
  writeUInt32LE cdSize       -- central directory size
  writeUInt32LE cdOffset     -- central directory offset
  writeUInt16LE 0x0000       -- comment length

def buildZip [Monad m] [MonadState ByteArray m] (files : Array (String × ByteArray × CompressionMethod)) : m Unit := do
  let mut entries := #[]
  let mut offset := 0

  for (name, data, compressionMethod) in files do
    let crc := CRC32.crc32 data
    let compressedData :=
      match compressionMethod with
      | .store => data
      | .deflate => DEFLATE.compress data
    -- Calculate size of local file header
    let nameBytes := name.toUTF8
    let localHeaderSize := 30 + nameBytes.size  -- 30 bytes fixed header + filename
    entries := entries.push {
      name,
      data,
      crc,
      offset,
      compressedData,
      compressionMethod
    }
    offset := offset + localHeaderSize.toUInt32 + compressedData.size.toUInt32


  -- Write all local file headers + data
  for entry in entries do
    writeLocalFileHeader entry
    modify (· ++ entry.compressedData)

  let cdOffset := (← get).size.toUInt32

  -- Write central directory
  for entry in entries do
    writeCentralDirHeader entry

  let cdSize := (← get).size.toUInt32 - cdOffset

  -- Write end of central directory
  writeEndOfCentralDir entries.size.toUInt16 cdSize cdOffset

public def zip (files : Array (String × ByteArray)) (method : CompressionMethod := .deflate) : ByteArray :=
  StateT.run (m := Id) (buildZip (files.map fun (x, y) => (x, y, method))) ByteArray.empty |>.2

public def zipToFile (path : System.FilePath) (files : Array (String × ByteArray)) (method : CompressionMethod := .deflate) : IO Unit := do
  let files := files.map fun (x, y) => (x, y, method)
  let ((), zipData) ← (buildZip files : StateRefT ByteArray IO Unit).run ByteArray.empty
  IO.FS.writeBinFile path zipData

public def zipToHandle (handle : IO.FS.Handle) (files : Array (String × ByteArray)) (method : CompressionMethod := .deflate) : IO Unit := do
  let files := files.map fun (x, y) => (x, y, method)
  let ((), zipData) ← (buildZip files : StateRefT ByteArray IO Unit).run ByteArray.empty
  handle.write zipData


end
