/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Environment
import Lean.Message
import Lean.Exception
import Verso

open Lean
open SubVerso.Highlighting

namespace Verso.Genre.Manual.InlineLean

initialize leanOutputs : EnvExtension (NameMap (List Highlighted.Message)) ←
  registerEnvExtension (pure {})

variable [Monad m] [MonadEnv m] [Elab.MonadInfoTree m] [MonadError m]

/--
Save the output of a Lean block.

`name` is the name the author assigned to the block.
-/
def saveOutputs (name : Name) (msgs : List Highlighted.Message) : m Unit :=
  modifyEnv (leanOutputs.modifyState · (·.insert name msgs))

def getOrSuggest (key : Ident) (map : NameMap α) : m α := do
  match map.find? key.getId with
  | some v => pure v
  | none =>
    for (n, _) in map do
      if shouldSuggest n then
        Doc.Suggestion.saveSuggestion key n.toString n.toString
    throwErrorAt key "'{key}' not found - options are {map.toList.map (·.fst)}"
where
  shouldSuggest (n : Name) :=
    let s1 := key.getId.toString
    let s2 := n.toString
    EditDistance.levenshtein s1 s2 (threshold s1 s2) |>.isSome
  threshold (s1 s2 : String) : Nat :=
    let l := max s1.length s2.length
    if l < 2 then 0
    else if l < 4 then 1
    else if l < 10 then 2
    else 3

def getOutputs (name : Ident) : m (List Highlighted.Message):= do
  leanOutputs.getState (← getEnv) |> getOrSuggest name
