/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
import Lean.Data.Json
public import Lean.Data.Json.FromToJson
import Verso.BEq
import VersoUtil.BinFiles.Z85

namespace Verso.Genre.Manual
open Lean

public structure DataFile where
  filename : String
  contents : ByteArray

open Verso.BEq in
public instance : BEq DataFile where
  beq := private ptrEqThen fun f1 f2 =>
    ptrEqThen' f1.filename f2.filename (· == ·) &&
    ptrEqThen' f1.contents f2.contents (· == ·)

public instance : Hashable DataFile where
  hash f := private mixHash f.filename.hash f.contents.hash

open Std Format in
public instance : Repr DataFile where
  reprPrec v _ := private
    .group <|
    .nestD
      (joinSep [
        text "{",
        group ("filename :=" ++ line ++ v.filename.quote ++ ","),
        group ("content :=" ++ line ++ s!"#<{v.contents.size} bytes>")
       ] line) ++
    line ++ "}"

public instance : ToJson DataFile where
  toJson f := private
    json%{"filename": $f.filename, "size": $f.contents.size, "content": $(BinFiles.Z85.encode f.contents)}

public instance : FromJson DataFile where
  fromJson? json := private do
    let filename ← json.getObjValAs? String "filename"
    let size ← json.getObjValAs? Nat "size"
    let contents ← json.getObjValAs? String "content"
    let contents := BinFiles.Z85.decode contents size
    return { filename, contents }
