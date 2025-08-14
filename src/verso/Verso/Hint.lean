/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Message
import Lean.Meta.Hint

open Lean Meta Hint

namespace Verso

/-
Creates a hint message with associated code action suggestions at a specified location.

The arguments are as follows:
* `ref`: the syntax location for the code action suggestions. Will be overridden by the `span?`
  field on any suggestions that specify it.
* `hint`: the main message of the hint, which precedes its code action suggestions.
* `suggestions`: the suggestions to display.
* `codeActionPrefix?`: if specified, text to display in place of "Try this: " in the code action
  label
* `forceList`: if `true`, suggestions will be displayed as a bulleted list even if there is only
  one.
-/
def hintAt (ref : Syntax) (hint : MessageData) (suggestions : Array Suggestion)
    (codeActionPrefix? : Option String := none)
    (forceList : Bool := false) :
    CoreM MessageData :=
  -- The @ guards against upstream signature changes going unnoticed
  @MessageData.hint hint suggestions (ref? := some ref) (codeActionPrefix? := codeActionPrefix?) (forceList := forceList)
