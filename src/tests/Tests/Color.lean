/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso.Color
import Lean.Elab.Command

/-!
Compile-time tests for the `color%` literal: the three accepted hex lengths elaborate, and other
lengths are rejected with a clear error. Value-level `css`/`tex` checks live in the runtime suite
(`testColor` in `TestMain`).
-/

open Verso

-- The three accepted lengths elaborate and render as expected (a 3-digit literal doubles each
-- digit; 8 digits keep the alpha byte).
/-- info: #ffffff -/
#guard_msgs in
#eval IO.println (color%#fff).css

/-- info: #4777ff -/
#guard_msgs in
#eval IO.println (color%#4777ff).css

/-- info: #aabbcc80 -/
#guard_msgs in
#eval IO.println (color%#aabbcc80).css

/-- error: expected 3, 6, or 8 hex digits, got 0 -/
#guard_msgs in
example : Color := color%#

/-- error: expected 3, 6, or 8 hex digits, got 4 -/
#guard_msgs in
example : Color := color%#1234

/-- error: expected 3, 6, or 8 hex digits, got 5 -/
#guard_msgs in
example : Color := color%#12345

/-- error: expected 3, 6, or 8 hex digits, got 7 -/
#guard_msgs in
example : Color := color%#1234567

-- The parser registers trailing whitespace on the hex token, so the original source (including the
-- spaces after the literal) can be reconstructed from the parse tree by `Syntax.reprint`.
open Lean Parser in
/-- info: round-trips: true -/
#guard_msgs in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let input := "color%#abc   "
  match runParserCategory (← getEnv) `term input with
  | .ok stx => IO.println s!"round-trips: {stx.reprint == some input}"
  | .error e => throwError e
