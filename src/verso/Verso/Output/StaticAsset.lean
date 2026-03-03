/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
module
public import Lean.Elab.Eval
meta import Lean.Elab.Eval
open Lean

namespace Verso.Output
set_option doc.verso true
set_option doc.verso.suggestions false

/--
Static assets can be `linked` (if they're already present in a CDN or
otherwise available) or can be `copied` into the `-verso-data` directory
from local assets.
-/
public inductive StaticAssetSource where
  | copied : System.FilePath → StaticAssetSource
  | linked : String → StaticAssetSource

/--
Enumerate all files in a base directory
-/
private meta partial def listFiles (base : System.FilePath) (path : System.FilePath) : IO (Array System.FilePath) :=
  (·.snd) <$> StateT.run (go base path) #[]
where
  go (base path : System.FilePath) : StateT (Array _) IO Unit := do
    let here := base / path
    match (← here.metadata).type with
    | .dir =>
      for entry in (← here.readDir) do
        go base (path / entry.fileName)
    | .file =>
      modify (·.push path)
    | .symlink | .other => return ()

/--
Enumerate the contents of a directory as a list of {name}`System.FilePath`.

Using `include_asset_dir "../foo" "bar/baz"` will list all the files in
the directory `../foo/bar/baz` relative to current file; the resulting paths
will be relative to `../foo`, e.g. `bar/baz/a.txt` or
`bar/baz/a/b/c.txt`.

Does not follow symlinks.
-/
elab "include_asset_dir " base:str path:str : term => do
  let ctx ← readThe Lean.Core.Context
  let srcPath := System.FilePath.mk ctx.fileName
  let some srcDir := srcPath.parent
    | throwError "cannot compute parent directory of '{srcPath}'"
  let basePath := srcDir / base.getString
  unless ← System.FilePath.isDir basePath do
    throwError s!"Asset base path '{← IO.FS.realPath basePath}' is not a directory"
  unless ← System.FilePath.pathExists (basePath / path.getString) do
    throwError s!"Asset directory '{path.getString}' does not exist in asset base directory '{← IO.FS.realPath basePath}'"
  unless System.FilePath.isRelative path.getString do
    throwError s!"Asset directory '{path.getString}' must be relative"
  let t : Expr := mkConst ``System.FilePath
  let fileList ← listFiles basePath path.getString
  let fileListExpr : Expr :=
    fileList.toList.map (mkApp (mkConst ``System.FilePath.mk []) <| mkStrLit ·.toString)
      |>.foldr (init := .app (.const ``List.nil [0]) t) fun x xs =>
        mkApp3 (.const ``List.cons [0]) t x xs
  return fileListExpr
