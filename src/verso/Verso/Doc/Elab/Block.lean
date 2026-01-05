/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Verso.Doc.Elab.Monad
meta import Verso.Doc.Elab.Monad
public import Lean.DocString.Syntax
import Verso.Doc.Elab.Inline

set_option doc.verso true

namespace Verso.Doc.Elab

open Lean Elab
open PartElabM
open DocElabM
open Lean.Doc.Syntax
open Verso.ArgParse (SigDoc)

set_option backward.privateInPublic false

def decorateClosing : TSyntax `block → DocElabM Unit
  | `(block|:::%$s $_ $_* { $_* }%$e)
  | `(block|```%$s $_ $_* | $_ ```%$e)
  | `(block|%%%%$s $_* %%%%$e) => closes s e
  | _ => pure ()


variable (genre : Genre) in
/--
Elaborates a parsed block into a {name}`Target.Block`, which denotes an expression of type
{lean}`Doc.Block genre` in an unspecified {name}`genre`.
-/
public partial def elabBlock' (block : TSyntax `block) : DocElabM Target.Block :=
  withTraceNode `Elab.Verso.block (fun _ => pure m!"Block {block}") <|
  withRef block <| withFreshMacroScope <| withIncRecDepth <| do
  decorateClosing block
  match block.raw with
  | .missing =>
    return .stx (← ``(sorryAx Doc.Block (synthetic := true)))
  | stx@(.node _ kind _) =>
    let env ← getEnv
    let result ← match (← liftMacroM (expandMacroImpl? env stx)) with
    | some (_decl, stxNew?) => -- TODO terminfo here? Right now, we suppress most uses of it.
      let stxNew ← liftMacroM <| liftExcept stxNew?
      withMacroExpansionInfo stx stxNew <|
        withRef stxNew <|
          elabBlock' ⟨stxNew⟩
    | none =>
      let exp ← blockExpandersFor kind
      for e in exp do
        try
          let termStx ← withFreshMacroScope <| e stx
          return .stx termStx
        catch
          | ex@(.internal id) =>
            if id == unsupportedSyntaxExceptionId then continue
            else throw ex
          | ex => throw ex
      let exp ← blockElabsFor kind
      for e in exp do
        try
          let block ← withFreshMacroScope <| e stx
          return block
        catch
          | ex@(.internal id) =>
            if id == unsupportedSyntaxExceptionId then continue
            else throw ex
          | ex => throw ex
      throwUnexpected block
  | _ =>
    throwUnexpected block

variable (genre : Genre) in
/--
Elaborates a parsed block into syntax denoting an expression of type {lean}`Doc.Block genre`.
Consider using {name}`elabBlock'` instead.
-/
public partial def elabBlockTerm (block : TSyntax `block) : DocElabM Term := do
  (← elabBlock' block).toTerm ⟨(← readThe DocElabContext).genreSyntax⟩

@[deprecated elabBlockTerm "use `elabBlockTerm` for a precise replacement, or rewrite to use `elabBlock'`" (since := "2025-12-28")]
public def elabBlock := elabBlockTerm
