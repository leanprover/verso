/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jason Reed
-/
module
import Std.Data.HashMap

namespace Verso.LzCompress

def keyStrBase64 := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/="

def getCharFromInt (n : Nat) : Char := String.Pos.Raw.get keyStrBase64 ⟨n⟩

open Std

/-!
This code was adapted from https://github.com/pieroxy/lz-string
which was distributed under the MIT License as given below.

In its current state it is quite imperative and not particularly
idiomatic lean. The reason for using this code at all is to match the
compressed strings that lean4web uses.

MIT License

Copyright (c) 2013 Pieroxy pieroxy@pieroxy.net

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

-/
def compress (uncompressed : String)
             (bitsPerChar : Nat)
             (getCharFromInt : Nat → Char) : String := Id.run do
  if uncompressed.isEmpty then
    return ""

  let mut dictionary : HashMap String Nat := {}
  let mut dictionaryToCreate : HashMap String Bool := {}

  let mut wc : String := ""
  let mut w : String := ""
  let mut enlargeIn : Nat := 2
  let mut dictSize : Nat := 3
  let mut numBits : Nat := 2
  let mut data : Array Char := #[]
  let mut data_val : Nat := 0
  let mut data_position : Nat := 0

  for c in uncompressed.toList.map toString do
    if !dictionary.contains c then
      dictionary := dictionary.insert c dictSize
      dictSize := dictSize + 1
      dictionaryToCreate := dictionaryToCreate.insert c true
    wc := w ++ c
    if dictionary.contains wc then
      w := wc
    else
      if dictionaryToCreate.contains w then
        let code := String.Pos.Raw.get! w 0 |>.toNat
        if code < 256 then
          for _ in [:numBits] do
            data_val := data_val <<< 1
            if data_position == bitsPerChar - 1 then
              data := data.push (getCharFromInt data_val)
              data_position := 0
              data_val := 0
            else
              data_position := data_position + 1
          let mut value := code
          for _ in [0:8] do
            data_val := (data_val <<< 1) ||| (value &&& 1)
            if data_position == bitsPerChar - 1 then
              data := data.push (getCharFromInt data_val)
              data_position := 0
              data_val := 0
            else
              data_position := data_position + 1
            value := value >>> 1
        else
          let mut value := 1
          for _ in [:numBits] do
            data_val := (data_val <<< 1) ||| value
            if data_position == bitsPerChar - 1 then
              data := data.push (getCharFromInt data_val)
              data_position := 0
              data_val := 0
            else
              data_position := data_position + 1
            value := 0
          let mut value' := String.Pos.Raw.get! w 0 |> Char.toNat
          for _ in [0:16] do
            data_val := (data_val <<< 1) ||| (value' &&& 1)
            if data_position == bitsPerChar - 1 then
              data := data.push (getCharFromInt data_val)
              data_position := 0
              data_val := 0
            else
              data_position := data_position + 1
            value' := value' >>> 1
        enlargeIn := enlargeIn - 1
        if enlargeIn == 0 then
          enlargeIn := Nat.pow 2 numBits
          numBits := numBits + 1
        dictionaryToCreate := dictionaryToCreate.erase w
      else
        let mut value := dictionary.get! w
        for _ in [:numBits] do
          data_val := (data_val <<< 1) ||| (value &&& 1)
          if data_position == bitsPerChar - 1 then
            data := data.push (getCharFromInt data_val)
            data_position := 0
            data_val := 0
          else
            data_position := data_position + 1
          value := value >>> 1
      enlargeIn := enlargeIn - 1
      if enlargeIn == 0 then
        enlargeIn := Nat.pow 2 numBits
        numBits := numBits + 1
      dictionary := dictionary.insert wc dictSize
      dictSize := dictSize + 1
      w := c

  -- Output the code for _w if not empty
  if !w.isEmpty then
    if dictionaryToCreate.contains w then
      let code := String.Pos.Raw.get! w 0 |>.toNat
      if code < 256 then
        for _ in [:numBits] do
          data_val := data_val <<< 1
          if data_position == bitsPerChar - 1 then
            data := data.push (getCharFromInt data_val)
            data_position := 0
            data_val := 0
          else
            data_position := data_position + 1
        let mut value := code
        for _ in [0:8] do
          data_val := (data_val <<< 1) ||| (value &&& 1)
          if data_position == bitsPerChar - 1 then
            data := data.push (getCharFromInt data_val)
            data_position := 0
            data_val := 0
          else
            data_position := data_position + 1
          value := value >>> 1
      else
        let mut value := 1
        for _ in [:numBits] do
          data_val := (data_val <<< 1) ||| value
          if data_position == bitsPerChar - 1 then
            data := data.push (getCharFromInt data_val)
            data_position := 0
            data_val := 0
          else
            data_position := data_position + 1
          value := 0
        let mut value' := code
        for _ in [0:16] do
          data_val := (data_val <<< 1) ||| (value' &&& 1)
          if data_position == bitsPerChar - 1 then
            data := data.push (getCharFromInt data_val)
            data_position := 0
            data_val := 0
          else
            data_position := data_position + 1
          value' := value' >>> 1
      enlargeIn := enlargeIn - 1
      if enlargeIn == 0 then
        enlargeIn := Nat.pow 2 numBits
        numBits := numBits + 1
      dictionaryToCreate := dictionaryToCreate.erase w
    else
      let mut value := dictionary.get! w
      for _ in [:numBits] do
        data_val := (data_val <<< 1) ||| (value &&& 1)
        if data_position == bitsPerChar - 1 then
          data := data.push (getCharFromInt data_val)
          data_position := 0
          data_val := 0
        else
          data_position := data_position + 1
        value := value >>> 1
      enlargeIn := enlargeIn - 1
      if enlargeIn == 0 then
        enlargeIn := Nat.pow 2 numBits
        numBits := numBits + 1

  -- End of stream marker
  let mut value := 2
  for _ in [:numBits] do
    data_val := (data_val <<< 1) ||| (value &&& 1)
    if data_position == bitsPerChar - 1 then
      data := data.push (getCharFromInt data_val)
      data_position := 0
      data_val := 0
    else
      data_position := data_position + 1
    value := value >>> 1

  -- Flush last char
  let mut loop := true
  while loop do
    data_val := data_val <<< 1
    if data_position == bitsPerChar - 1 then
      data := data.push (getCharFromInt data_val)
      loop := false
    else
      data_position := data_position + 1

  return data.foldl (init := "") (·.push ·)

public def lzCompress (uncompressed : String) : String := compress uncompressed 6 getCharFromInt
