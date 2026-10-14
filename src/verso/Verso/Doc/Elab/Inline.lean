/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Verso.Doc.Elab.Monad
meta import Verso.Doc.Elab.Monad
public import Lean.DocString.Syntax

namespace Verso.Doc.Elab

open Lean Elab
open PartElabM
open DocElabM
open Lean.Doc (InlineView VersoInline)
open Lean.Doc.Parser
open Verso.ArgParse (SigDoc)

set_option backward.privateInPublic false

public def throwUnexpected [Monad m] [MonadError m] (stx : Syntax) : m α :=
  throwErrorAt stx "unexpected syntax{indentD stx}"

/--
Runs `act`, which elaborates `stx`. In a top-level block that is partial syntax, if `stx` contains
`.missing` and `act` throws an error, then the error is logged and the result is the constant
`empty`. Lean has already reported the parse error that left the `.missing`. Otherwise, the result
is that of `act`.

`empty` is returned instead of `sorry` because this is called when the final document is built, not
when the block is elaborated. A `sorry` warning would appear in the last block of the document
rather than the block's syntax.
-/
public def elabWithMissing (stx : Syntax) (empty : Name)
    (act : DocElabM (TSyntax `term)) : DocElabM (TSyntax `term) := do
  unless (← readThe PartElabM.State).blockHasMissing && stx.hasMissing do return (← act)
  try act
  catch ex =>
    if ex.isInterrupt || ex.isRuntime then throw ex
    logException ex
    return mkCIdent empty

/--
Elaborates `.missing` as an inline or a block. In a top-level block that is partial syntax, the
result is the constant `empty`. Elsewhere, the result is `sorry` of the type `type`.
-/
public def elabMissing (empty : Name) (type : Name) : DocElabM (TSyntax `term) := do
  if (← readThe PartElabM.State).blockHasMissing then return mkCIdent empty
  ``(sorryAx ($(mkCIdent type) _) (synthetic := true))

public partial def elabInline (inline : VersoInline) : DocElabM (TSyntax `term) :=
  withRef inline <| withFreshMacroScope <| withIncRecDepth <| do
  match inline.raw with
  | .missing => elabMissing ``Verso.Doc.Inline.empty ``Verso.Doc.Inline
  | stx@(.node _ kind _) => elabWithMissing stx ``Verso.Doc.Inline.empty do
    let env ← getEnv
    match (← liftMacroM (expandMacroImpl? env stx)) with
    | some (_decl, stxNew?) => -- TODO terminfo here? Right now, we suppress most uses of it.
      let stxNew ← liftMacroM <| liftExcept stxNew?
      withMacroExpansionInfo stx stxNew <|
        withRef stxNew <|
          elabInline ⟨stxNew⟩
    | none =>
      let some view := InlineView.of ⟨stx⟩
        | throwUnexpected stx
      let exp ← inlineExpandersFor kind
      for e in exp do
        try
          let termStx ← withFreshMacroScope <| e view
          return termStx
        catch
          | ex@(.internal id) =>
            if id == unsupportedSyntaxExceptionId then pure ()
            else throw ex
          | ex => throw ex
      throwUnexpected stx
  | other =>
    throwUnexpected other
