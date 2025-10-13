import Std.Data.HashMap

def keyStrBase64 := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/="

def getCharFromInt (n : Nat) : Char := keyStrBase64.get ⟨n⟩

open Std

/--
Ported from https://github.com/pieroxy/lz-string

Very imperative and not particularly idiomatic lean.

The reason for using this code at all is to match what lean4web uses.
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
        let code := w.get! 0 |>.toNat
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
          let mut value' := w.get! 0 |> Char.toNat
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
      let code := w.get! 0 |>.toNat
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

  return String.mk data.toList

def lzCompress (uncompressed : String) := compress uncompressed 6 getCharFromInt

/--
info: "JYWwDg9gTgLgBAWQIYwBYBtgCMB0AZCAc2AGMcAhJAZ1LgFo64traAzJEmKuYAOznRFSAKAZw0AU2gSQ3PnDwSkvAOTcQKVDJSlumLFCRQAnsNGNF8AApxlAEzgBFJhPFQArhLrt0VV1RgUGQleLmEANyNgJCx0VwAKG2cALjgrKAgwAEozMQAVLThWCHRBAHc+Qh5uJCYWEjgoCSp3dHh5QWISYQkADyRwOLhUgBq4RLhAciInLLhAFMI4MZtACiJFp2GAXiZTOHpGYC44MAyIVmrbdCakO2MefkVlNTgNSRfdAWxDE2Fdvo54XgQGAAfXswOguUYAAkJE1zsogVooHUaA0mi02ncBEJun9Bq5RuMVjN5msbNMxiktlgdrYwGB0MYAPx7OBlVwkZRwPxGEioIrQcSFY4QU5YyQfAxGWlidlwTn8JC+CCNCQMjiuAAGSHpjKZmrZB35B24EHcMDA5uEQA"
-/
#guard_msgs in
#eval lzCompress r#"import Mathlib.Logic.Basic -- basic facts in logic
-- theorems in Lean's mathematics library

-- Let P and Q be true-false statements
variable (P Q : Prop)

-- The following is a basic result in logic
example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  -- its proof is already in Lean's mathematics library
  exact not_and_or

-- Here is another basic result in logic
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  apply? -- we can search for the proof in the library
  -- we can also replace `apply?` with its output
"#
