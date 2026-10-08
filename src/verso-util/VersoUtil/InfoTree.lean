/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Elab.InfoTree.Types
import Lean.Elab.InfoTree.Main

set_option doc.verso true

namespace Verso

open Lean Elab

/--
Folds {name}`f` over the info nodes in {name}`infoState` whose syntax could potentially overlap the
range from {name}`start` to {name}`stop`. Nodes whose source range doesn't overlap the range are
skipped.
-/
public partial def foldInfoIn (infoState : InfoState) (start stop : String.Pos.Raw)
    (f : Info → α → α) (init : α) : α :=
  infoState.trees.foldl (init := init) fun acc t => go t acc
where
  go : InfoTree → α → α
    | .context _ t, acc => go t acc
    | .node info children, acc =>
      if mayOverlap info.stx then
        children.foldl (init := f info acc) fun acc t => go t acc
      else acc
    | .hole id, acc =>
      match infoState.assignment.find? id with
      | some t => go t acc
      | none =>
        match infoState.lazyAssignment.find? id with
        | some t => go t.get acc
        | none => acc
  mayOverlap (stx : Syntax) : Bool :=
    match stx.getRange? with
    | some r => r.start ≤ stop && start ≤ r.stop
    | none => true

/--
Folds {name}`f` over the info nodes in {name}`infoState` whose syntax may contain {name}`pos`.
-/
public def foldInfoAt (infoState : InfoState) (pos : String.Pos.Raw)
    (f : Info → α → α) (init : α) : α :=
  foldInfoIn infoState pos pos f init

/--
Folds {name}`f` over the custom info nodes with data of type {name}`α` in {name}`infoState` whose
syntax could potentially overlap the range from {name}`start` to {name}`stop`. {name}`f` receives
each node's syntax with its data.
-/
public def foldCustomInfoIn (α : Type) [TypeName α] (infoState : InfoState)
    (start stop : String.Pos.Raw) (f : Syntax → α → β → β) (init : β) : β :=
  foldInfoIn infoState start stop (init := init) fun info acc =>
    match info with
    | .ofCustomInfo ⟨stx, data⟩ =>
      match data.get? α with
      | some x => f stx x acc
      | none => acc
    | _ => acc

/--
Folds {name}`f` over the custom info nodes with data of type {name}`α` in {name}`infoState` whose
syntax may contain {name}`pos`.
-/
public def foldCustomInfoAt (α : Type) [TypeName α] (infoState : InfoState) (pos : String.Pos.Raw)
    (f : Syntax → α → β → β) (init : β) : β :=
  foldCustomInfoIn α infoState pos pos f init
