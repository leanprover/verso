/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import SubVerso.Highlighting
import Lean.Message

open SubVerso.Highlighting
open Lean
open Std

namespace Verso.Code.External

/-- Converts all warnings to errors. -/
public def warningsToErrors (hl : Highlighted) : Highlighted :=
  match hl with
  | .seq xs => .seq <| xs.map warningsToErrors
  | .point .warning str => .point .error str
  | .point .. => hl
  | .tactics info start stop x => .tactics info start stop <| warningsToErrors x
  | .span infos x => .span (infos.map fun (k, str) => (if k matches .warning then .error else k, str)) (warningsToErrors x)
  | .text .. | .token .. | .unparsed .. => hl

/-- Extracts all messages from the given code. -/
public def allInfo (hl : Highlighted) : Array (Highlighted.Message × Option Highlighted) :=
  match hl with
  | .seq xs => xs.flatMap allInfo
  | .point k str => #[(⟨k, str⟩, none)]
  | .tactics _ _ _ x => allInfo x
  | .span infos x => (infos.map fun (k, str) => (⟨k, str⟩, some x)) ++ allInfo x
  | .text .. | .token .. | .unparsed .. => #[]
where
  toSev : Highlighted.Span.Kind → MessageSeverity
    | .error => .error
    | .info => .information
    | .warning => .warning

/--
Returns all the tokens (atoms, identifiers, etc) in `hl`.
-/
public def allTokens (hl : Highlighted) : HashSet String :=
  match hl with
  | .seq xs => xs.attach.map (fun ⟨h, _⟩ => allTokens h) |>.foldl (init := {}) HashSet.union
  | .point .. | .text .. | .unparsed .. => {}
  | .tactics _ _ _ x | .span _ x => allTokens x
  | .token ⟨_, s⟩ => {s}

/--
Returns all the name tokens in `hl`.
-/
public def allNames (hl : Highlighted) : HashSet String :=
  match hl with
  | .seq xs => xs.attach.map (fun ⟨h, _⟩ => allNames h) |>.foldl (init := {}) HashSet.union
  | .point .. | .text .. | .unparsed .. => {}
  | .tactics _ _ _ x | .span _ x => allNames x
  | .token ⟨.var .., s⟩ | .token ⟨.const .., s⟩ => {s}
  | .token _ => {}
