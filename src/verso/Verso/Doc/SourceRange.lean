/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio Jesus Gallego Arias
-/
module
public import Lean.Syntax

namespace Verso.Doc

open Lean

public def sourceSpanContainsRange (start stop : String.Pos.Raw) (range : Syntax.Range) : Bool :=
  start ≤ range.start && range.stop ≤ stop

public def requireSyntaxRange (context : String) (stx : Syntax) : Syntax.Range :=
  match stx.getRange? with
  | some range => range
  | none => panic! s!"{context} has no recoverable source range: {repr stx}"

public def requireContainedSyntaxRange (context : String) (start stop : String.Pos.Raw)
    (range : Syntax.Range) : Syntax.Range :=
  if sourceSpanContainsRange start stop range then
    range
  else
    panic! s!"{context}: {repr range} outside {repr start}..{repr stop}"

/--
Return the original syntax after checking that its recovered range is contained in a source span.

This returns the syntax rather than `Unit` so callers can store the checked value directly. That
makes the invariant part of the normal data flow instead of relying on a validation call whose only
observable effect would be a possible panic.
-/
public def requireSyntaxWithContainedRange (context : String) (start stop : String.Pos.Raw)
    (stx : Syntax) : Syntax :=
  match stx.getRange? with
  | some range =>
    if sourceSpanContainsRange start stop range then
      stx
    else
      panic! s!"{context}: {repr range} outside {repr start}..{repr stop}"
  | none =>
    panic! s!"{context} has no recoverable source range: {repr stx}"

end Verso.Doc
