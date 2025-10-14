/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso
import VersoManual.Basic
import VersoManual.HighlightedCode

open SubVerso.Highlighting

open Verso Genre Manual ArgParse Doc Elab
open Verso Output Html
open Verso Code Highlighted WebAssets
open Lean
open Lean.Doc.Syntax

namespace Verso.Genre.Manual.InlineLean

def Inline.option : Inline where

@[role]
def option : RoleExpanderOf Unit
  | (), inlines => withoutAsync do
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $optName:str )) := arg
      | throwErrorAt arg "Expected code literal with the option name"
    let optName := optName.getString.toName
    let optDecl ← getOptionDecl optName
    let hl : Highlighted := optTok optName optDecl.declName optDecl.descr

    `(Inline.other {Inline.option with data := ToJson.toJson $(quote hl)} #[Inline.code $(quote optName.toString)])
where
  optTok (name declName : Name) (descr : String) : Highlighted :=
    .token ⟨.option name declName descr , name.toString⟩

@[inline_extension Inline.option]
def option.descr : InlineDescr := withHighlighting {
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean option code while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml (g := Manual) "examples"
}
