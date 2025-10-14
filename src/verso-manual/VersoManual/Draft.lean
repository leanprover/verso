/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json
import Lean.Data.Json.FromToJson
import Std.Data.HashMap
import Std.Data.HashSet

import Verso.Doc.ArgParse
import Verso.Doc.Elab
import VersoManual.Basic

open Verso.ArgParse
open Verso Genre Manual
open Verso.Doc.Elab
open Lean (ToJson FromJson)
open Std (HashMap HashSet)

namespace Verso.Genre.Manual

inline_extension Inline.draft where
  traverse _id _data _contents := do
    if (← isDraft) then
      pure none
    else
      pure (some <| .concat #[])
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun go _ _ content => do
      content.mapM go

block_extension Block.draft where
  traverse _id _data _contents := do
    if (← isDraft) then
      pure none
    else
      pure (some <| .concat #[])
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      content.mapM goB

/-- Hide draft-only content when in not in draft mode -/
@[role]
def draft : RoleExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Inline.other Inline.draft #[$[$(← contents.mapM elabInline)],*])

/-- Hide draft-only content when in not in draft mode -/
@[directive draft]
def draftBlock : DirectiveExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Block.other Block.draft #[$[$(← contents.mapM elabBlock)],*])
