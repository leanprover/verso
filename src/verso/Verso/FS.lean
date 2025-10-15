/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
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
Recursively copies a directory structure from {name}`src` to {name}`tgt`.

Some errors that occur while copying are logged using {name}`logError`.
-/
public partial def copyRecursively (logError : String → IO Unit) (src tgt : System.FilePath)  : IO Unit := do
  if (← src.metadata).type == .symlink then
    logError s!"Can't copy '{src}' - symlinks not currently supported"
  if ← src.isDir then
    ensureDir tgt
    for d in ← src.readDir do
      copyRecursively logError d.path (tgt.join d.fileName)
  else
    withFile src .read fun h =>
      withFile tgt .write fun h' => do
        let mut buf ← h.read 1024
        while !buf.isEmpty do
          h'.write buf
          buf ← h.read 1024
