/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean

import LeanDoc.Doc.Elab.Monad
import LeanDoc.Syntax

namespace LeanDoc.Doc.Elab

open Lean Elab
open PartElabM
open LeanDoc.Syntax

partial def elabInline (inline : Syntax) : DocElabM (TSyntax `term) :=
  withRef inline <| withFreshMacroScope <| withIncRecDepth <| do
  match inline with
  | .missing =>
    ``(sorryAx Inline (synthetic := true))
  | stx@(.node _ kind _) =>
    let exp ← inlineExpandersFor kind
    for e in exp do
      try
        let termStx ← withFreshMacroScope <| e stx

        return termStx
      catch
        | ex@(.internal id) =>
          if id == unsupportedSyntaxExceptionId then pure ()
          else throw ex
        | ex => throw ex
    throwUnsupportedSyntax
  | _ =>
    throwUnsupportedSyntax

@[inline_expander LeanDoc.Syntax.text]
partial def _root_.LeanDoc.Syntax.text.expand : InlineExpander := fun x =>
  match x with
  | `(inline| $s:str) => do
    -- Erase the source locations from the string literal to prevent unwanted hover info
    ``(Inline.text $(⟨deleteInfo s.raw⟩))
  | other => dbg_trace "text {other}"; throwUnsupportedSyntax
  where
    deleteInfo : Syntax → Syntax
      | .node _ k args => .node .none k (args.map deleteInfo)
      | .atom _ val => .atom .none val
      | .ident _ rawVal val preres => .ident .none rawVal val preres
      | .missing => .missing


@[inline_expander LeanDoc.Syntax.linebreak]
def _root_.linebreak.expand : InlineExpander
  | `<low|(LeanDoc.Syntax.linebreak ~(.atom _ s))> =>
    ``(Inline.linebreak $(quote s))
  | _ => throwUnsupportedSyntax

@[inline_expander LeanDoc.Syntax.emph]
def _root_.LeanDoc.Syntax.emph.expand : InlineExpander
  | `(inline| _{ $args* }) => do
    ``(Inline.emph #[$[$(← args.mapM elabInline)],*])
  | _ => throwUnsupportedSyntax

@[inline_expander LeanDoc.Syntax.bold]
def _root_.LeanDoc.Syntax.bold.expand : InlineExpander
  | `(inline| *{ $args* }) => do
    ``(Inline.bold #[$[$(← args.mapM elabInline)],*])
  | _ => throwUnsupportedSyntax

@[inline_expander LeanDoc.Syntax.role]
def _root_.LeanDoc.Syntax.role.expand : InlineExpander
  | inline@`(inline| role{$name $args*} [$subjects]) => do
    --TODO arguments
      withRef inline <| withFreshMacroScope <| withIncRecDepth <| do
        let ⟨.node _ _ subjectArr⟩ := subjects
          | throwUnsupportedSyntax
        let name ← resolveGlobalConstNoOverloadWithInfo name
        let exp ← roleExpandersFor name
        let mut argVals := #[]
        for arg in args do
          match arg.raw with
          | `<low|(arg.anon ~v)> =>
            match v with
            | `($y:ident) => argVals := argVals.push <| .anonymous <| .name y
            | other => dbg_trace "didn't parse arg val {repr other}"; pure ()
          | `<low|(arg.named ~n ~_ ~v)> =>
            match n with
            | `($y:ident) =>
              match v with
              | `($z:ident) => argVals := argVals.push <| .named y <| .name z
              | other => dbg_trace "didn't parse arg val {repr other}"; pure ()
            | other => dbg_trace "didn't parse arg name {repr other}"; pure ()
          | other => dbg_trace "didn't parse arg {repr other}"; pure ()
        for e in exp do
          try
            let termStxs ← withFreshMacroScope <| e argVals subjectArr
            return (← ``(Inline.concat #[$[$termStxs],*]))
          catch
            | ex@(.internal id) =>
              if id == unsupportedSyntaxExceptionId then pure ()
              else throw ex
            | ex => throw ex
        throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax


@[inline_expander LeanDoc.Syntax.code]
def _root_.LeanDoc.Syntax.code.expand : InlineExpander
  |  `(inline| code{ $s }) =>
    ``(Inline.code $s)
  | _ => throwUnsupportedSyntax

def elabBlock (block : Syntax) : DocElabM (TSyntax `term) :=
  withRef block <| withFreshMacroScope <| withIncRecDepth <| do
  match block with
  | .missing =>
    ``(sorryAx Block (synthetic := true))
  | stx@(.node _ kind _) =>
    let exp ← blockExpandersFor kind
    for e in exp do
      try
        let termStx ← withFreshMacroScope <| e stx
        return termStx
      catch
        | ex@(.internal id) =>
          if id == unsupportedSyntaxExceptionId then pure ()
          else throw ex
        | ex => throw ex
    throwUnsupportedSyntax
  | _ =>
    dbg_trace "block not found: {block}"
    throwUnsupportedSyntax

def partCommand (cmd : Syntax) : PartElabM Unit :=
  withRef cmd <| withFreshMacroScope <| do
  match cmd with
  | stx@(.node _ kind _) =>
    let exp ← partCommandsFor kind
    for e in exp do
      try
        withFreshMacroScope <| e stx
        return
      catch
        | ex@(.internal id) =>
          if id == unsupportedSyntaxExceptionId then pure ()
          else throw ex
        | ex => throw ex
    fallback
  | _ =>
    fallback
where
  fallback : PartElabM Unit := do
    let blk ← liftDocElabM <| elabBlock cmd
    addBlock blk

partial def closePartsUntil (outer : Nat) (endPos : String.Pos) : PartElabM Unit := do
  let level ← currentLevel
  if outer ≤ level then
    match (← get).partContext.close endPos with
    | some ctxt' =>
      modify fun st => {st with partContext := ctxt'}
      if outer < level then
        closePartsUntil outer endPos
    | none => pure ()


@[part_command LeanDoc.Syntax.header]
partial def _root_.LeanDoc.Syntax.header.command : PartCommand
  | stx@(`<low|(LeanDoc.Syntax.header ~(.atom info hashes ) ~(.node _ `null inlines) ) >) => do
    let titleBits ← liftDocElabM <| inlines.mapM elabInline
    let titleString := headerStxToString (← getEnv) stx
    let headerLevel := hashes.length
    let ambientLevel ← currentLevel
    if headerLevel > ambientLevel + 1 then throwErrorAt stx "Wrong header nesting"
    -- New subheader?
    if headerLevel == ambientLevel + 1 then
      -- Prelude is done!
      pure ()
    else
      closePartsUntil ambientLevel info.getPos?.get!

    -- Start a new subpart
    push {
      titleSyntax := stx,
      expandedTitle := some (titleString, titleBits),
      blocks := #[],
      priorParts := #[]
    }

  | _ => throwUnsupportedSyntax


@[block_expander LeanDoc.Syntax.para]
partial def _root_.LeanDoc.Syntax.para.expand : BlockExpander
  | `<low|(LeanDoc.Syntax.para ~(.node _ `null args) )> => do
    ``(Block.para #[$[$(← args.mapM elabInline)],*])
  | _ =>
    throwUnsupportedSyntax


def elabLi (block : Syntax) : DocElabM (Syntax × TSyntax `term) :=
  withRef block <|
  match block with
  | `<low|(LeanDoc.Syntax.li (bullet (column ~(.atom _ n)) ~dot) ~(.node _ `null args) )> => do
    let item ← ``(ListItem.mk $(Syntax.mkNumLit n) #[$[$(← args.mapM elabBlock)],*])
    pure (dot, item)
  | _ =>
    dbg_trace "unexpected block {block}"
    throwUnsupportedSyntax

@[block_expander LeanDoc.Syntax.ul]
def _root_.LeanDoc.Syntax.ul.expand : BlockExpander
  | `<low|(LeanDoc.Syntax.ul ~_ ~(.node _ `null itemStxs) )> => do
    let mut bullets : Array Syntax := #[]
    let mut items : Array (TSyntax `term) := #[]
    for i in itemStxs do
      let (b, item) ← elabLi i
      bullets := bullets.push b
      items := items.push item
    let info := DocListInfo.mk bullets
    for b in bullets do
      pushInfoLeaf <| .ofCustomInfo {stx := b, value := Dynamic.mk info}
    ``(Block.ul #[$[$items],*])
  | _ =>
    throwUnsupportedSyntax

@[block_expander LeanDoc.Syntax.blockquote]
def _root_.LeanDoc.Syntax.blockquote.expand : BlockExpander
  | `<low|(LeanDoc.Syntax.blockquote ~_ ~(.node _ `null innerBlocks) )> => do
    ``(Block.blockquote #[$[$(← innerBlocks.mapM elabBlock)],*])
  | _ =>
    throwUnsupportedSyntax

@[block_expander LeanDoc.Syntax.codeblock]
def _root_.LeanDoc.Syntax.codeblock.expand : BlockExpander
  | `<low|(LeanDoc.Syntax.codeblock (column ~_col) ~_open ~_nameAndArgs ~(.atom _ contents) ~_close )> =>
    -- TODO name and args and indent
    ``(Block.code Option.none #[] 0 $(quote contents))
  | _ =>
    throwUnsupportedSyntax
