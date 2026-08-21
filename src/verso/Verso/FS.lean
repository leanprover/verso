/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Verso.BuildLog
set_option doc.verso true

namespace Verso.FS

open IO.FS

/--
Ensures that {name}`dir` exists and is a directory. If {name}`dir` does not exist, then it and any
necessary parents are created. If it does exist, but is not a directory, then an error is thrown.
-/
public def ensureDir (dir : System.FilePath) : IO Unit := do
  if !(← dir.pathExists) then
    createDirAll dir
  if !(← dir.isDir) then
    throw (↑ s!"Not a directory: {dir}")

/--
Removes {name}`path`, which may name a file or a directory tree, if it exists.

If the path does not exist, nothing happens.
-/
public def removeTree (path : System.FilePath) : IO Unit := do
  if ← path.pathExists then
    if ← path.isDir then removeDirAll path
    else removeFile path

/--
Recursively copies a directory of files from {name}`src` to {name}`tgt`. Any errors are reported via
{name}`MonadBuildLog`, and paths that don't satisfy {name}`copyFile` are skipped.
-/
public partial def copyRecursively
    [Monad m] [MonadLiftT IO m] [MonadBuildLog m]
    (src tgt : System.FilePath) (copyFile : System.FilePath → IO Bool := fun _ => pure true) :
    m Unit := do
  unless ← (copyFile src : IO _) do return
  if (← (src.metadata : IO _)).type == .symlink then
    Verso.reportError s!"Can't copy '{src}' - symlinks not currently supported"
  if ← (src.isDir : IO _) then
    (ensureDir tgt : IO _)
    for d in ← (src.readDir : IO _) do
      copyRecursively d.path (tgt / d.fileName) (copyFile := copyFile)
  else
    withFile src .read fun h =>
      withFile tgt .write fun h' => do
        let mut buf ← h.read 1024
        while !buf.isEmpty do
          h'.write buf
          buf ← h.read 1024

/--
Replaces the directory tree at {name}`tgt` with a copy of {name}`src`, which may be a file or a
directory tree. If {name}`tgt` already exists, it is deleted.
-/
public def replaceTree
    [Monad m] [MonadLiftT IO m] [MonadBuildLog m] (src tgt : System.FilePath) : m Unit := do
  (removeTree tgt : IO _)
  copyRecursively src tgt
