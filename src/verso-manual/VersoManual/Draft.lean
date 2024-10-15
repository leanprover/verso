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
import VersoManual.Basic

open Verso.ArgParse
open Verso Genre Manual
open Verso.Doc.Elab
open Lean (ToJson FromJson)
open Std (HashMap HashSet)

namespace Verso.Genre.Manual

def Inline.draft : Inline where
  name := `Verso.Genre.Manual.draft

def Block.draft : Block where
  name := `Verso.Genre.Manual.draft

/-- Hide draft-only content when in not in draft mode -/
@[role_expander draft]
def draft : RoleExpander
  | args, contents => do
    ArgParse.done.run args
    pure #[← ``(Verso.Doc.Inline.other Inline.draft #[$[$(← contents.mapM elabInline)],*])]

/-- Hide draft-only content when in not in draft mode -/
@[directive_expander draft]
def draftBlock : DirectiveExpander
  | args, contents => do
    ArgParse.done.run args
    pure #[← ``(Verso.Doc.Block.other Block.draft #[$[$(← contents.mapM elabBlock)],*])]

@[inline_extension draft]
def draft.descr : InlineDescr where
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

@[block_extension draft]
def draft.blockDescr : BlockDescr where
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
