/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Elab.Eval
import Lean.Elab.Term
import Verso.BinFiles.Z85

open Lean Elab Term
open Lean Environment

namespace Verso.BinFiles

private unsafe def evalFilePathUnsafe (stx : Syntax) : TermElabM System.FilePath :=
  evalTerm System.FilePath (Lean.mkConst ``System.FilePath) stx

@[implemented_by evalFilePathUnsafe]
private opaque evalFilePath (stx : Syntax) : TermElabM System.FilePath

/--
Includes a binary file in the Lean module. The source path is given relative to the current file.

Internally, the file's contents are represented using a string literal in the Z85 encoding, which is
similar to Base64 but more efficient.
-/
elab "include_bin " path:str : term => do
  let path ← evalFilePath path
  let ctx ← readThe Lean.Core.Context
  let srcPath := System.FilePath.mk ctx.fileName
  let some srcDir := srcPath.parent
    | throwError "cannot compute parent directory of '{srcPath}'"
  let path := srcDir / path
  let contents ← IO.FS.readBinFile path
  return mkApp2 (.const ``Z85.decode []) (mkStrLit (Z85.encode contents)) (toExpr contents.size)

private partial def binFiles (base : System.FilePath) (path : System.FilePath) : IO (Array (System.FilePath × Expr)) :=
  (·.snd) <$> StateT.run (go base path) #[]
where
  go (base path : System.FilePath) : StateT (Array _) IO Unit := do
    let here := base / path
    match (← here.metadata).type with
    | .dir =>
      for entry in (← here.readDir) do
        go base (path / entry.fileName)
    | .file =>
      let contents ← IO.FS.readBinFile here
      let e : Expr := mkApp2 (.const ``Z85.decode []) (mkStrLit (Z85.encode contents)) (toExpr contents.size)
      modify (·.push (path, e))
    | .symlink | .other => return ()


/--
Recursively includes a directory of binary files in the Lean module. The directory path is given
relative to the current file.

All files in the directory are included. The resulting value is an array of pairs of `String`s and
`ByteArray`s, where the strings are the filenames; the provided path is a prefix of all of them.
Symbolic links are not followed.

Internally, the files' contents are represented using string literals in the Z85 encoding, which is
similar to Base64 but more efficient.
-/
elab "include_bin_dir " path:str : term => do
  let path ← evalFilePath path
  let ctx ← readThe Lean.Core.Context
  let srcPath := System.FilePath.mk ctx.fileName
  let some srcDir := srcPath.parent
    | throwError "cannot compute parent directory of '{srcPath}'"
  let files ← binFiles srcDir path
  let string : Expr := .const ``String []
  let byteArray : Expr := .const ``ByteArray []
  let t : Expr := mkApp2 (.const ``Prod [0, 0]) string byteArray
  let fileList : Expr := files.foldr (init := .app (.const ``List.nil [0]) t) fun (path, arr) xs =>
    let x := mkApp4 (.const ``Prod.mk [0, 0]) string byteArray (.lit (.strVal path.toString)) arr
    mkApp3 (.const ``List.cons [0]) t x xs

  return mkApp2 (.const ``List.toArray [0]) t fileList
