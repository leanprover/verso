/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Durations as `errata.toml` writes them, such as `90s` or `2m30s`.
-/
module

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace ErrataConfig

/-- The form of a duration, as the messages about malformed durations state it. -/
def durationForm : String :=
  "one or more whole numbers, each followed by one of the units h, m, s, ms, used at most once \
  each and in that order, such as 90s, 10m, or 2m30s"

/-- The units of a duration, in the order they are written, each with its length in milliseconds. -/
def durationUnits : List (String × Nat) :=
  [("h", 3600000), ("m", 60000), ("s", 1000), ("ms", 1)]

/--
A duration in milliseconds: a sequence of components such as {lit}`2m30s`, each a whole number
followed by a unit, with the units {lit}`h`, {lit}`m`, {lit}`s`, and {lit}`ms` in that order and
each at most once. Whitespace around it is ignored.
-/
def durationMs? (s : String) : Option Nat := Id.run do
  let mut cs := s.trimAscii.copy.toList
  if cs.isEmpty then return none
  let mut units := durationUnits
  let mut total := 0
  for _ in durationUnits do
    if cs.isEmpty then break
    let digits := cs.takeWhile Char.isDigit
    let rest := cs.dropWhile Char.isDigit
    let unit := String.ofList (rest.takeWhile Char.isAlpha)
    match units.dropWhile (·.1 != unit) with
    | (_, scale) :: later =>
      if digits.isEmpty then return none
      total := total + (String.ofList digits).toNat! * scale
      units := later
      cs := rest.dropWhile Char.isAlpha
    | [] => return none
  if cs.isEmpty then some total else none

end ErrataConfig
