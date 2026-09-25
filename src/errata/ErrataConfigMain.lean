/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
`errata-config FILE OUT`: reads and validates the configuration file `FILE` and writes the
elaborated file `OUT`. When `FILE` is absent, `OUT` holds the defaults.
-/
module

public import ErrataConfig

open ErrataConfig

/--
Writes the elaborated configuration file, or reports each problem with the configuration file on
standard error, at its position, and exits with {lit}`1`.
-/
public def main (args : List String) : IO UInt32 := do
  let [file, out] := args
    | IO.eprintln "usage: errata-config FILE OUT"
      return 2
  let file : System.FilePath := file
  let out : System.FilePath := out
  let result ←
    if ← file.pathExists then parse (← IO.FS.readFile file)
    else pure (.ok {})
  match result with
  | .ok f =>
    if let some parent := out.parent then IO.FS.createDirAll parent
    IO.FS.writeFile out (f.toJson.pretty ++ "\n")
    return 0
  | .error problems =>
    for p in problems do IO.eprintln p
    IO.eprintln s!"error: {file} has {problems.size} \
      {if problems.size == 1 then "problem" else "problems"}"
    return 1
