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

namespace Verso.Doc.Elab

open Lean Elab
open PartElabM
open DocElabM
open Lean.Doc (BlockView VersoBlock)
open Lean.Doc.Parser
open Verso.ArgParse (SigDoc)

set_option backward.privateInPublic false

/-- Records the delimiters of a block that has both, so that each hover mentions the other. -/
def decorateClosing : BlockView → DocElabM Unit
  | .directive v => closes v.opener v.closer
  | .codeblock v => closes v.openFence v.closeFence
  | .metadata v => closes v.opener v.closer
  | _ => pure ()


/-- Elaborates a parsed block into syntax denoting an expression of type `Block genre`. -/
public partial def elabBlock (block : VersoBlock) : DocElabM (TSyntax `term) :=
  withTraceNode `Elab.Verso.block (fun _ => pure m!"Block {block}") <|
  withRef block <| withFreshMacroScope <| withIncRecDepth <| do
  match block.raw with
  | .missing =>
    ``(sorryAx (Block _) (synthetic := true))
  | stx@(.node _ kind _) =>
    let env ← getEnv
    match (← liftMacroM (expandMacroImpl? env stx)) with
    | some (_decl, stxNew?) => -- TODO terminfo here? Right now, we suppress most uses of it.
      let stxNew ← liftMacroM <| liftExcept stxNew?
      withMacroExpansionInfo stx stxNew <|
        withRef stxNew <|
          elabBlock ⟨stxNew⟩
    | none =>
      let some view := BlockView.of ⟨stx⟩
        | throwUnexpected stx
      decorateClosing view
      let exp ← blockExpandersFor kind
      for e in exp do
        try
          let termStx ← withFreshMacroScope <| e view
          return termStx
        catch
          | ex@(.internal id) =>
            if id == unsupportedSyntaxExceptionId then continue
            else throw ex
          | ex => throw ex
      throwUnexpected block
  | _ =>
    throwUnexpected block
