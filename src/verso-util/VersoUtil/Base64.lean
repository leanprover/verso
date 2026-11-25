/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

namespace Verso.Base64

def alphabet : ByteArray :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toByteArray

theorem alphabet_size : alphabet.size = 64 := by decide

/-- The character for the six bits of `v` that start at bit `shift`. -/
def sextet (v : UInt32) (shift : UInt32) : Char :=
  let i := (v >>> shift).toNat % 64
  Char.ofUInt8 (alphabet[i]'(alphabet_size ▸ Nat.mod_lt _ (by decide)))

/--
Encodes the `bytes` into a form that is suitable for use in ASCII-only contexts.
-/
public def encode (bytes : ByteArray) : String := Id.run do
  let mut out := ""
  let mut i := 0
  while h : i + 3 ≤ bytes.size do
    let v := (bytes[i].toUInt32 <<< 16) ||| (bytes[i + 1].toUInt32 <<< 8) |||
      bytes[i + 2].toUInt32
    out := out.push (sextet v 18) |>.push (sextet v 12) |>.push (sextet v 6) |>.push (sextet v 0)
    i := i + 3
  match h : bytes.size - i with
  | 1 =>
    let v := bytes[i].toUInt32 <<< 16
    out := out.push (sextet v 18) |>.push (sextet v 12) |>.push '=' |>.push '='
  | 2 =>
    let v := (bytes[i].toUInt32 <<< 16) ||| (bytes[i + 1].toUInt32 <<< 8)
    out := out.push (sextet v 18) |>.push (sextet v 12) |>.push (sextet v 6) |>.push '='
  | _ => pure ()
  return out
