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
open DocElabM
open LeanDoc.Syntax

def throwUnexpected [Monad m] [MonadError m] (stx : Syntax) : m α :=
  throwErrorAt stx "unexpected syntax{indentD stx}"

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
    throwUnexpected stx
  | other =>
    throwUnexpected other

@[inline_expander LeanDoc.Syntax.text]
partial def _root_.LeanDoc.Syntax.text.expand : InlineExpander := fun x =>
  match x with
  | `(inline| $s:str) => do
    -- Erase the source locations from the string literal to prevent unwanted hover info
    ``(Inline.text $(⟨deleteInfo s.raw⟩))
  | _ => throwUnsupportedSyntax
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

def parseArgVal (val : TSyntax `arg_val) : DocElabM ArgVal := do
  match val with
  | `($s:str) => pure <| .str s.getString
  | `($x:ident) => pure <| .name x
  | `($n:num) => pure <| .num <| n.getNat
  | other => throwErrorAt other "Can't decode argument value '{repr other}'"

def parseArgs (argStx : TSyntaxArray `argument) : DocElabM (Array Arg) := do
  let mut argVals := #[]
  for arg in argStx do
    match arg with
    | `(argument|$v:arg_val) =>
      argVals := argVals.push (.anon (← parseArgVal v))
    | `(argument|$x:ident := $v) =>
      argVals := argVals.push (.named x.getId (← parseArgVal v))
    | other => throwErrorAt other "Can't decode argument '{repr other}'"
  pure argVals


@[inline_expander LeanDoc.Syntax.role]
def _root_.LeanDoc.Syntax.role.expand : InlineExpander
  | inline@`(inline| role{$name $args*} [$subjects]) => do
      withRef inline <| withFreshMacroScope <| withIncRecDepth <| do
        let ⟨.node _ _ subjectArr⟩ := subjects
          | throwUnsupportedSyntax
        let name ← resolveGlobalConstNoOverloadWithInfo name
        let exp ← roleExpandersFor name
        let argVals ← parseArgs args
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

@[inline_expander LeanDoc.Syntax.link]
def _root_.LeanDoc.Syntax.link.expand : InlineExpander
  | `(inline| link[ $txt* ] $dest:link_target) => do
    let url : TSyntax `term ←
      match dest with
      | `(link_target| ( $url )) =>
        pure (↑ url)
      | `(link_target| [ $ref ]) => do
        -- Round-trip through quote to get rid of source locations, preventing unwanted IDE info
        addLinkRef ref
      | _ => throwErrorAt dest "Couldn't parse link destination"
    ``(Inline.link #[$[$(← txt.mapM elabInline)],*] $url)
  | _ => throwUnsupportedSyntax

@[inline_expander LeanDoc.Syntax.footnote]
def _root_.LeanDoc.Syntax.link.footnote : InlineExpander
  | `(inline| [^ $name:str ]) => do
    ``(Inline.footnote $name $(← addFootnoteRef name))
  | _ => throwUnsupportedSyntax


@[inline_expander LeanDoc.Syntax.image]
def _root_.LeanDoc.Syntax.image.expand : InlineExpander
  | `(inline| image[ $alt:str* ] $dest:link_target) => do
    let altText := String.join (alt.map (·.getString) |>.toList)
    let url : TSyntax `term ←
      match dest with
      | `(link_target| ( $url )) =>
        pure (↑ url)
      | `(link_target| [ $ref ]) => do
        -- Round-trip through quote to get rid of source locations, preventing unwanted IDE info
        addLinkRef ref
      | _ => throwErrorAt dest "Couldn't parse link destination"
    ``(Inline.image $(quote altText) $url)
  | _ => throwUnsupportedSyntax


@[inline_expander LeanDoc.Syntax.code]
def _root_.LeanDoc.Syntax.code.expand : InlineExpander
  |  `(inline| code{ $s }) =>
    ``(Inline.code $s)
  | _ => throwUnsupportedSyntax


@[inline_expander LeanDoc.Syntax.inline_math]
def _root_.LeanDoc.Syntax.inline_math.expand : InlineExpander
  |  `(inline| ${ code{ $s } }) =>
    ``(Inline.math MathMode.inline $s)
  | _ => throwUnsupportedSyntax

@[inline_expander LeanDoc.Syntax.display_math]
def _root_.LeanDoc.Syntax.display_math.expand : InlineExpander
  |  `(inline| $${ code{ $s } }) =>
    ``(Inline.math MathMode.display $s)
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
          if id == unsupportedSyntaxExceptionId then continue
          else throw ex
        | ex => throw ex
    throwUnexpected block
  | _ =>
    throwUnexpected block

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
          if id == unsupportedSyntaxExceptionId then continue
          else throw ex
        | ex => throw ex
    fallback
  | _ =>
    fallback
where
  fallback : PartElabM Unit := do
    if (← getThe PartElabM.State).partContext.priorParts.size > 0 then
      throwErrorAt cmd "Unexpected block"
    let blk ← liftDocElabM <| elabBlock cmd
    addBlock blk

@[part_command LeanDoc.Syntax.footnote_ref]
partial def _root_.LeanDoc.Syntax.footnote_ref.command : PartCommand
  | `(block| [^ $name:str ]: $contents* ) =>
    addFootnoteDef name =<< contents.mapM (elabInline ·.raw)
  | _ => throwUnsupportedSyntax

@[part_command LeanDoc.Syntax.link_ref]
partial def _root_.LeanDoc.Syntax.link_ref.command : PartCommand
  | `(block| [ $name:str ]: $url:str ) =>
    addLinkDef name url.getString
  | stx => dbg_trace  "{stx}"; throwUnsupportedSyntax

partial def closePartsUntil (outer : Nat) (endPos : String.Pos) : PartElabM Unit := do
  let level ← currentLevel
  if outer ≤ level then
    match (← getThe PartElabM.State).partContext.close endPos with
    | some ctxt' =>
      modifyThe PartElabM.State fun st => {st with partContext := ctxt'}
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
      if let none := info.getPos? then dbg_trace "No start position for {stx}"
      closePartsUntil headerLevel info.getPos!

    -- Start a new subpart
    push {
      titleSyntax := stx,
      expandedTitle := some (titleString, titleBits),
      blocks := #[],
      priorParts := #[]
    }

  | _ => throwUnsupportedSyntax


@[part_command LeanDoc.Syntax.block_role]
def includeSection : PartCommand
  | `(block|block_role{include $_args* }[ $content ]) => throwErrorAt content "Unexpected block argument"
  | `(block|block_role{include}) => throwError "Expected exactly one argument"
  | `(block|block_role{include $arg1 $arg2 $args*}) => throwErrorAt arg2 "Expected exactly one argument"
  | stx@`(block|block_role{include $args* }) => do
    match (← parseArgs args) with
    | #[.anon (.name x)] =>
      let name ← resolved x
      addPart <| .included name
    | _ => throwErrorAt stx "Expected exactly one positional argument that is a name"
  | stx => dbg_trace "Not {stx}"; Lean.Elab.throwUnsupportedSyntax
where
 resolved id := mkIdentFrom id <$> resolveGlobalConstNoOverload (mkIdentFrom id (docName id.getId))

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
  | `<low|(LeanDoc.Syntax.ul ~(.node _ `null itemStxs) )> => do
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

@[block_expander LeanDoc.Syntax.ol]
def _root_.LeanDoc.Syntax.ol.expand : BlockExpander
  | `<low|(LeanDoc.Syntax.ol (num ~start) ~(.node _ `null itemStxs) )> => do
    let mut bullets : Array Syntax := #[]
    let mut items : Array (TSyntax `term) := #[]
    for i in itemStxs do
      let (b, item) ← elabLi i
      bullets := bullets.push b
      items := items.push item
    let info := DocListInfo.mk bullets
    for b in bullets do
      pushInfoLeaf <| .ofCustomInfo {stx := b, value := Dynamic.mk info}
    ``(Block.ol $(Syntax.mkNumLit start.getAtomVal) #[$[$items],*])
  | _ =>
    throwUnsupportedSyntax

def elabDesc (block : Syntax) : DocElabM (Syntax × TSyntax `term) :=
  withRef block <|
  match block with
  | `<low|(LeanDoc.Syntax.desc ~colon ~(.node _ `null dts) ~_ ~(.node _ `null dds))> => do
    let item ← ``(DescItem.mk #[$[$(← dts.mapM elabInline)],*] #[$[$(← dds.mapM elabBlock)],*])
    pure (colon, item)
  | _ =>
    dbg_trace "unexpected block {block}"
    throwUnsupportedSyntax

@[block_expander LeanDoc.Syntax.dl]
def _root_.LeanDoc.Syntax.dl.expand : BlockExpander
  | `<low|(LeanDoc.Syntax.dl ~(.node _ `null itemStxs) )> => do
    let mut colons : Array Syntax := #[]
    let mut items : Array (TSyntax `term) := #[]
    for i in itemStxs do
      let (b, item) ← elabDesc i
      colons := colons.push b
      items := items.push item
    let info := DocListInfo.mk colons
    for b in colons do
      pushInfoLeaf <| .ofCustomInfo {stx := b, value := Dynamic.mk info}
    ``(Block.dl #[$[$items],*])
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
  | `<low|(LeanDoc.Syntax.codeblock (column ~(.atom _ _col)) ~_open ~(.node _ `null #[nameStx, .node _ `null argsStx]) ~(.atom info contents) ~_close )> => do
      let name ← resolveGlobalConstNoOverloadWithInfo nameStx
      let exp ← codeBlockExpandersFor name
      -- TODO typed syntax here
      let args ← parseArgs <| argsStx.map (⟨·⟩)
      for e in exp do
        try
          let termStxs ← withFreshMacroScope <| e args (Syntax.mkStrLit (info:=info) contents)
          return (← ``(Block.concat #[$[$termStxs],*]))
        catch
          | ex@(.internal id) =>
            if id == unsupportedSyntaxExceptionId then pure ()
            else throw ex
          | ex => throw ex
      dbg_trace "No code block expander for '{nameStx}' ---> '{name}'"
      throwUnsupportedSyntax
  | `<low|(LeanDoc.Syntax.codeblock (column ~(.atom _ col)) ~_open ~(.node _ `null #[]) ~(.atom _info contents) ~_close )> =>
    ``(Block.code Option.none #[] $(Syntax.mkNumLit col) $(quote contents))
  | _ =>
    throwUnsupportedSyntax

@[block_expander LeanDoc.Syntax.directive]
def _root_.LeanDoc.Syntax.directive.expand : BlockExpander
  | `<low|(LeanDoc.Syntax.directive  ~_open ~nameStx ~(.node _ `null argsStx) ~_fake ~_fake' ~(.node _ `null contents) ~_close )> => do
    let name ← resolveGlobalConstNoOverloadWithInfo nameStx
    let exp ← directiveExpandersFor name
    -- TODO typed syntax here
    let args ← parseArgs <| argsStx.map (⟨·⟩)
    for e in exp do
      try
        let termStxs ← withFreshMacroScope <| e args contents
        return (← ``(Block.concat #[$[$termStxs],*]))
      catch
        | ex@(.internal id) =>
          if id == unsupportedSyntaxExceptionId then pure ()
          else throw ex
        | ex => throw ex
    dbg_trace "No directive expander for '{nameStx}'"
    throwUnsupportedSyntax
  | stx =>
    dbg_trace "can't directive {stx}"
    throwUnsupportedSyntax
