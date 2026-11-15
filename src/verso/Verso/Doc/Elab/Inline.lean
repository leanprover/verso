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
Runs `act`, which elaborates an inline or a block. If `act` throws an error, the error is logged and
the result is the constant `empty`, so that the rest of the enclosing block is elaborated.

An abort exception results in `empty` without a message, because it signals that the error is
already logged. Interrupts, runtime exceptions and other internal exceptions are rethrown.
-/
public def elabOrEmpty (empty : Name) (act : DocElabM (TSyntax `term)) :
    DocElabM (TSyntax `term) := do
  try act
  catch ex =>
    -- Lean's `try` in `TermElabM` already passes these on.
    if ex.isInterrupt || ex.isRuntime then throw ex
    match ex with
    | .internal id _ => unless isAbortExceptionId id do throw ex
    | .error .. => logException ex
    return mkCIdent empty

/--
Elaborates an inline into syntax that denotes an expression of type `Inline genre`.

Inlines whose elaboration fails, either due to an exception thrown from their expander or all
expanders rejecting them as unknown syntax, have their exceptions logged and elaborate to
`Inline.empty`.

`Syntax.missing` elaborates to `Inline.empty` without an additional message because Lean has already
reported the parse error that gave rise to it.
-/
public partial def elabInline (inline : VersoInline) : DocElabM (TSyntax `term) :=
  withRef inline <| withFreshMacroScope <| withIncRecDepth <|
  elabOrEmpty ``Verso.Doc.Inline.empty do
  match inline.raw with
  | .missing => return mkCIdent ``Verso.Doc.Inline.empty
  | stx@(.node _ kind _) => do
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
