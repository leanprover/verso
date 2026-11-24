/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public meta import Lean.Elab.Term
public import VersoManual.LicenseInfo
meta import VersoManual.LicenseInfo

open Lean Elab Term

namespace Verso.Genre.Manual.LicenseInfo

/--
Splits license text into its header and body.

The header is the first non-blank line. A blank line separates it from the body, which starts at the
next non-blank line and continues to the end of the text.
-/
private meta def splitLicense (contents : String) : Except String (String × String) := do
  let mut header : Option String.Slice := none
  let mut blankSeen := false
  for line in contents.toSlice.lines do
    let blank := line.all Char.isWhitespace
    match header with
    | none =>
      unless blank do
        header := some line.trimAscii
    | some h =>
      if blank then
        blankSeen := true
      else if blankSeen then
        return (h.copy, (line.str.sliceFrom line.startInclusive).copy.replace "\r" "")
      else
        break
  if header.isSome && blankSeen then
    throw "the license text is empty"
  else
    throw "expected a header line, a blank line, and the license text"

/--
Includes a license file in the Lean module as a `LicenseInfo.Section`. The path is given relative to
the current file.

The first non-blank line of the file becomes the section's header, and the text after the blank line
that follows it becomes the section's text. Elaboration fails if the file does not have a header line
followed by a blank line and further text.
-/
elab "include_license " path:str : term => do
  let given := path.getString
  let ctx ← readThe Lean.Core.Context
  let srcPath := System.FilePath.mk ctx.fileName
  let some srcDir := srcPath.parent
    | throwError "cannot compute parent directory of '{srcPath}'"
  let contents ← IO.FS.readFile (srcDir / given)
  match splitLicense contents with
  | .ok (header, body) =>
    return mkApp2 (.const ``LicenseInfo.Section.mk []) (toExpr (some header)) (toExpr body)
  | .error e => throwError "invalid license file '{given}': {e}"
