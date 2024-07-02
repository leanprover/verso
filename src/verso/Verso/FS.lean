/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
namespace Verso.FS

open IO.FS

def ensureDir (dir : System.FilePath) : IO Unit := do
  if !(← dir.pathExists) then
    createDirAll dir
  if !(← dir.isDir) then
    throw (↑ s!"Not a directory: {dir}")

partial def copyRecursively (logError : String → IO Unit) (src tgt : System.FilePath)  : IO Unit := do
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
