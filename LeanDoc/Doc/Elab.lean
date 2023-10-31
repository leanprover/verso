import Lean

import LeanDoc.Doc.Elab.Monad

namespace LeanDoc.Doc.Elab

open Lean Elab
open PartElabM

-- elab "#dump_inline_expand" : command => open Lean Elab Command in do
--   let out := inlineExpanderAttr.ext.getState (← getEnv)
--   dbg_trace (repr out.size)



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

@[inline_expander text]
def text.expand : InlineExpander := fun x =>
  match x with
  | `<low|(text ~(.atom _ s))> =>
    ``(Inline.text $(quote s))
  | other => dbg_trace "text {other}"; throwUnsupportedSyntax

@[inline_expander linebreak]
def linebreak.expand : InlineExpander
  | `<low|(linebreak ~(.atom _ s))> =>
    ``(Inline.linebreak $(quote s))
  | _ => throwUnsupportedSyntax

@[inline_expander emph]
def emph.expand : InlineExpander
  | `<low|(emph ~_open ~(.node _ `null args) ~_close)> => do
    ``(Inline.emph #[$[$(← args.mapM elabInline)],*])
  | _ => throwUnsupportedSyntax


-- partial def closeSectionsUntil (reason : Syntax) (outer : Nat) : PartElabM Unit := do
--   let some ⟨level, ptr, inPrelude⟩ := (← get).headerContext
--     | throwError "Not at the section level"
--   if outer ≤ level then
--     -- Close the prelude if we're in it
--     if let some i := inPrelude then
--       mkArray i
--       modify fun st => {st with headerContext := some ⟨level, ptr, none⟩}
--     dbg_trace "Making prelude array with {(← get).stack.extract (ptr+2) (← get).stack.size}"
--     mkArray (ptr + 2) -- just after the prelude
--     mkCApp ``Part.mk ptr
--     let tocElem := (← get).headerStack.back.close reason.getTailPos?.get!
--     modify fun st => {st with
--       headerContext := some ⟨level - 1, st.headerStack.back.ptr, none⟩,
--       headerStack := st.headerStack.pop
--     }
--     modify fun st => { st with
--       headerStack := st.headerStack.modify (st.headerStack.size - 1) (·.addChild tocElem)
--     }

--     if outer < level then
--       closeSectionsUntil reason outer



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


@[part_command header]
partial def header.command : PartCommand
  | stx@(`<low| (header ~(.atom info hashes ) ~(.node _ `null inlines) ) >) => do
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


@[block_expander para]
partial def para.expand : BlockExpander
  | `<low| (para ~(.node _ `null args) )> => do
    ``(Block.para #[$[$(← args.mapM elabInline)],*])
  | _ =>
    throwUnsupportedSyntax


def elabLi (block : Syntax) : DocElabM (Syntax × TSyntax `term) :=
  withRef block <|
  match block with
  | `<low| (li (bullet (column ~(.atom _ n)) ~dot) ~(.node _ `null args) )> => do
    let item ← ``(ListItem.mk $(Syntax.mkNumLit n) #[$[$(← args.mapM elabBlock)],*])
    pure (dot, item)
  | _ =>
    dbg_trace "unexpected block {block}"
    throwUnsupportedSyntax

@[block_expander ul]
def ul.expand : BlockExpander
  | `<low| (ul ~_ ~(.node _ `null itemStxs) )> => do
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

@[block_expander blockquote]
def blockquote.expand : BlockExpander
  | `<low| (blockquote ~_ ~(.node _ `null innerBlocks) )> => do
    ``(Block.blockquote #[$[$(← innerBlocks.mapM elabBlock)],*])
  | _ =>
    throwUnsupportedSyntax

@[block_expander code]
def code.expand : BlockExpander
  | `<low| (code (column ~_col) ~_open ~_name ~_args ~(.atom _ contents) ~_close )> =>
    -- TODO name and args and indent
    ``(Block.code Option.none #[] 0 $(quote contents))
  | _ =>
    throwUnsupportedSyntax
