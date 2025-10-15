/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Message
public import Lean.Meta.Hint


set_option doc.verso true
set_option pp.rawOnError true

open Lean Meta Hint

namespace Verso

/--
Creates a hint message with associated code action suggestions at a specified location.

The arguments are as follows:

: {name}`ref`

  the syntax location for the code action suggestions. Will be overridden by the
  {name}`Suggestion.span?` field on any suggestions that specify it.

: {name}`hint`

  the main message of the hint, which precedes its code action suggestions.

: {name}`suggestions`

  the suggestions to display.

: {name}`codeActionPrefix?`

  if specified, text to display in place of "Try this: " in the code action label

: {name}`forceList`

  if {name}`true`, suggestions will be displayed as a bulleted list even if there
  is only one.
-/
public def hintAt (ref : Syntax) (hint : MessageData) (suggestions : Array Suggestion)
    (codeActionPrefix? : Option String := none)
    (forceList : Bool := false) :
    CoreM MessageData :=
  -- The @ guards against upstream signature changes going unnoticed
  @MessageData.hint hint suggestions
    (ref? := some ref)
    (codeActionPrefix? := codeActionPrefix?)
    (forceList := forceList)
