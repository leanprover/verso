/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Doc.Elab.Monad
import Verso.Syntax

namespace Verso.Doc.Elab

open Lean Elab
open PartElabM
open DocElabM
open Verso.Syntax

def throwUnexpected [Monad m] [MonadError m] (stx : Syntax) : m α :=
  throwErrorAt stx "unexpected syntax{indentD stx}"

partial def elabInline' (inline : TSyntax `inline) : DocElabM Expr :=
  withRef inline <| withFreshMacroScope <| withIncRecDepth <| do
  let t ← inlineType
  match inline.raw with
  | .missing =>
    Meta.mkLabeledSorry t true true
  | stx@(.node _ kind _) =>
    let env ← getEnv
    let result ← match (← liftMacroM (expandMacroImpl? env stx)) with
    | some (_decl, stxNew?) => -- TODO terminfo here? Right now, we suppress most uses of it.
      let stxNew ← liftMacroM <| liftExcept stxNew?
      withMacroExpansionInfo stx stxNew <|
        withRef stxNew <|
          elabInline' ⟨stxNew⟩
    | none =>
      let exp ← inlineExpandersFor kind
      for e in exp do
        try
          let termStx ← withFreshMacroScope <| e stx
          return (← Term.elabTerm termStx (some t))
        catch
          | ex@(.internal id) =>
            if id == unsupportedSyntaxExceptionId then pure ()
            else throw ex
          | ex => throw ex

      let exp ← inlineElabsFor kind
      for e in exp do
        try
          let expr ← withFreshMacroScope <| e stx
          return expr
        catch
          | ex@(.internal id) =>
            if id == unsupportedSyntaxExceptionId then pure ()
            else throw ex
          | ex => throw ex

      throwUnexpected stx
  | other =>
    throwUnexpected other

partial def elabInline (inline : TSyntax `inline) : DocElabM (TSyntax `term) :=
  withRef inline <| withFreshMacroScope <| withIncRecDepth <| do
  match inline.raw with
  | .missing =>
    ``(sorryAx (Inline _) (synthetic := true))
  | stx@(.node _ kind _) =>
    let env ← getEnv
    let result ← match (← liftMacroM (expandMacroImpl? env stx)) with
    | some (_decl, stxNew?) => -- TODO terminfo here? Right now, we suppress most uses of it.
      let stxNew ← liftMacroM <| liftExcept stxNew?
      withMacroExpansionInfo stx stxNew <|
        withRef stxNew <|
          elabInline ⟨stxNew⟩
    | none =>
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

      let exp ← inlineElabsFor kind
      for e in exp do
        try
          let expr ← withFreshMacroScope <| e stx
          let n ← defineInline expr
          return mkIdentFrom stx n
        catch
          | ex@(.internal id) =>
            if id == unsupportedSyntaxExceptionId then pure ()
            else throw ex
          | ex => throw ex

      throwUnexpected stx
  | other =>
    throwUnexpected other

private def mkInline (ctor : Name) : DocElabM Expr := do
    let ⟨_, g⟩ ← readThe DocElabContext
    return .app (.const ctor []) g

private def mkInlineArr (ctor : Name) (xs : Array Expr) : DocElabM Expr := do
    let ⟨_, g⟩ ← readThe DocElabContext
    return mkApp2 (.const ctor []) g (← Meta.mkArrayLit (← inlineType) xs.toList)

@[inline_elab Verso.Syntax.text]
partial def _root_.Verso.Syntax.text.elab : InlineElab := fun x =>
  match x with
  | `(inline| $s:str) => do
    return .app (← mkInline ``Inline.text) (toExpr s.getString)
  | _ => throwUnsupportedSyntax

@[inline_elab Verso.Syntax.linebreak]
def _root_.linebreak.elab : InlineElab
  | `(inline|line! $s:str) => do
    return .app (← mkInline ``Inline.linebreak) (toExpr s.getString)
  | _ => throwUnsupportedSyntax

@[inline_elab Verso.Syntax.emph]
def _root_.Verso.Syntax.emph.elab : InlineElab
  | `(inline| _[ $args* ]) => do
    mkInlineArr ``Inline.emph (← args.mapM elabInline')
  | _ => throwUnsupportedSyntax

@[inline_elab Verso.Syntax.bold]
def _root_.Verso.Syntax.bold.elab : InlineElab
  | `(inline| *[ $args* ]) => do
    mkInlineArr ``Inline.bold (← args.mapM elabInline')
  | _ => throwUnsupportedSyntax

def parseArgVal (val : TSyntax `arg_val) : DocElabM ArgVal := do
  match val with
  | `(arg_val|$s:str) => pure <| .str s
  | `(arg_val|$x:ident) => pure <| .name x
  | `(arg_val|$n:num) => pure <| .num n
  | other => throwErrorAt other "Can't decode argument value '{repr other}'"

def parseArgs (argStx : TSyntaxArray `argument) : DocElabM (Array Arg) := do
  let mut argVals := #[]
  for arg in argStx do
    match arg with
    | `(argument|$v:arg_val) =>
      argVals := argVals.push (.anon (← parseArgVal v))
    | `(argument|$x:ident := $v) =>
      argVals := argVals.push (.named arg x (← parseArgVal v))
    | other => throwErrorAt other "Can't decode argument '{repr other}'"
  pure argVals

open Lean.Parser.Term in
def appFallback
    (stx : Syntax)
    (name : Ident) (resolvedName : Name)
    (argVals : Array Arg) (subjectArr : Option (Array (TSyntax `inline)))
    : DocElabM Term := do
  let f := mkIdentFrom name resolvedName
  let valStx : ArgVal → DocElabM Term := fun
    | .str s => pure s
    | .num n => pure n
    | .name x => pure x

  let argStx : Array Syntax ← argVals.mapM fun
    | .anon v => valStx v
    | .named _orig y v => do `(namedArgument|($y := $(← valStx v))) -- TODO location
  let subs ← subjectArr.mapM (·.mapM elabInline)
  let arrArg ← match subs with
    | some ss => (#[·]) <$> `(#[$ss,*])
    | none => pure #[]
  let appStx :=
    Syntax.node2 stx.getHeadInfo ``app
      f (.node .none nullKind <| arrArg ++ argStx)
  return ⟨appStx⟩



open Lean.Parser.Term in
@[inline_elab Verso.Syntax.role]
def _root_.Verso.Syntax.role.elab : InlineElab
  | inline@`(inline| role{$name $args*} [$subjects*]) => do
      withRef inline <| withFreshMacroScope <| withIncRecDepth <| do
        let ⟨genre, _⟩ ← readThe DocElabContext
        let it ← inlineType
        let resolvedName ← realizeGlobalConstNoOverloadWithInfo name
        let exp ← roleExpandersFor resolvedName
        let exp' ← roleElabsFor resolvedName
        let argVals ← parseArgs args
        if exp.isEmpty && exp'.isEmpty then
          -- If no expanders are registered, then try elaborating just as a
          -- function application node
          let appStx ← appFallback inline name resolvedName argVals subjects
          return (← Term.elabTerm appStx (some it))

        for e in exp do
          try
            let termStxs ← withFreshMacroScope <| e argVals subjects
            let termStxs ← termStxs.mapM fun t => (``(($t : Inline $(⟨genre⟩))))
            return (← Term.elabTerm (← ``(Inline.concat (genre := $(⟨genre⟩)) #[$[$termStxs],*])) (some it))
          catch
            | ex@(.internal id) =>
              if id == unsupportedSyntaxExceptionId then pure ()
              else throw ex
            | ex => throw ex

        for e in exp' do
          try
            return (← withFreshMacroScope <| e argVals subjects)
          catch
            | ex@(.internal id) =>
              if id == unsupportedSyntaxExceptionId then pure ()
              else throw ex
            | ex => throw ex

        throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

@[inline_elab Verso.Syntax.link]
def _root_.Verso.Syntax.link.expand : InlineElab
  | `(inline| link[ $txt* ] $dest:link_target) => do
    let url : Expr ←
      match dest with
      | `(link_target| ( $url )) =>
        Term.elabTerm (↑ url) none
      | `(link_target| [ $ref ]) => do
        -- Round-trip through quote to get rid of source locations, preventing unwanted IDE info
        Term.elabTerm (← addLinkRef ref) none
      | _ => throwErrorAt dest "Couldn't parse link destination"
    return .app (← mkInlineArr ``Inline.link (← txt.mapM elabInline')) url
  | _ => throwUnsupportedSyntax

@[inline_expander Verso.Syntax.footnote]
def _root_.Verso.Syntax.link.footnote : InlineExpander
  | `(inline| footnote( $name:str )) => do
    ``(Inline.footnote $name $(← addFootnoteRef name))
  | _ => throwUnsupportedSyntax


@[inline_expander Verso.Syntax.image]
def _root_.Verso.Syntax.image.expand : InlineExpander
  | `(inline| image( $alt:str ) $dest:link_target) => do
    let altText := alt.getString
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


@[inline_expander Verso.Syntax.code]
def _root_.Verso.Syntax.code.expand : InlineExpander
  |  `(inline| code( $s )) =>
    ``(Inline.code $(quote s.getString))
  | _ => throwUnsupportedSyntax


@[inline_expander Verso.Syntax.inline_math]
def _root_.Verso.Syntax.inline_math.expand : InlineExpander
  |  `(inline| \math code( $s )) =>
    ``(Inline.math MathMode.inline $s)
  | _ => throwUnsupportedSyntax

@[inline_expander Verso.Syntax.display_math]
def _root_.Verso.Syntax.display_math.expand : InlineExpander
  |  `(inline| \displaymath code( $s )) =>
    ``(Inline.math MathMode.display $s)
  | _ => throwUnsupportedSyntax

def decorateClosing : TSyntax `block → DocElabM Unit
  | `(block|:::%$s $_ $_* { $_* }%$e)
  | `(block|```%$s $_ $_* | $_ ```%$e)
  | `(block|%%%%$s $_* %%%%$e) => closes s e
  | _ => pure ()

open Lean.Elab.Term in
partial def elabBlock' (block : TSyntax `block) : DocElabM Expr :=
  withTraceNode `Elab.Verso.block (fun _ => pure m!"Block {block}") <|
  withRef block <| withFreshMacroScope <| withIncRecDepth <| do
  let ⟨_, g⟩ ← readThe DocElabContext
  let type : Expr := .app (.const ``Doc.Block []) g
  decorateClosing block
  match block.raw with
  | .missing =>
    Meta.mkSorry type true
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
          return (← elabTerm termStx (some type))
        catch
          | ex@(.internal id) =>
            if id == unsupportedSyntaxExceptionId then continue
            else throw ex
          | ex => throw ex
      let exp ← blockElabsFor kind
      for e in exp do
        try
          let b ← withFreshMacroScope <| e stx
          return b
        catch
          | ex@(.internal id) =>
            if id == unsupportedSyntaxExceptionId then continue
            else throw ex
          | ex => throw ex

      throwUnexpected block
  | _ =>
    throwUnexpected block

open Lean.Elab.Term in
partial def elabBlock (block : TSyntax `block) : DocElabM (TSyntax `term) :=
  withTraceNode `Elab.Verso.block (fun _ => pure m!"Block {block}") <|
  withRef block <| withFreshMacroScope <| withIncRecDepth <| do
  decorateClosing block
  match block.raw with
  | .missing =>
    ``(sorryAx Block (synthetic := true))
  | stx@(.node _ kind _) =>
    let env ← getEnv
    let result ← match (← liftMacroM (expandMacroImpl? env stx)) with
    | some (_decl, stxNew?) => -- TODO terminfo here? Right now, we suppress most uses of it.
      let stxNew ← liftMacroM <| liftExcept stxNew?
      withMacroExpansionInfo stx stxNew <|
        withRef stxNew <|
          elabBlock ⟨stxNew⟩
    | none =>
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
      let exp ← blockElabsFor kind
      for e in exp do
        try
          let b ← withFreshMacroScope <| e stx
          let n ← defineBlock b
          return mkIdentFrom stx n
        catch
          | ex@(.internal id) =>
            if id == unsupportedSyntaxExceptionId then continue
            else throw ex
          | ex => throw ex
      throwUnexpected block
  | _ =>
    throwUnexpected block

def partCommand (cmd : TSyntax `block) : PartElabM Unit :=
  withTraceNode `Elab.Verso.part (fun _ => pure m!"Part modification {cmd}") <|
  withRef cmd <| withFreshMacroScope <| do
  match cmd.raw with
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
    let blk ← liftDocElabM <| elabBlock' cmd
    addBlockExpr blk

@[part_command Verso.Syntax.footnote_ref]
partial def _root_.Verso.Syntax.footnote_ref.command : PartCommand
  | `(block| [^ $name:str ]: $contents* ) =>
    addFootnoteDef name =<< contents.mapM (elabInline ·)
  | _ => throwUnsupportedSyntax

@[part_command Verso.Syntax.link_ref]
partial def _root_.Verso.Syntax.link_ref.command : PartCommand
  | `(block| [ $name:str ]: $url:str ) =>
    addLinkDef name url.getString
  | _ => throwUnsupportedSyntax

partial def PartElabM.State.close (endPos : String.Pos) (state : PartElabM.State) : Option PartElabM.State :=
  state.partContext.close endPos |>.map ({state with partContext := ·})

partial def PartElabM.State.closeAll (endPos : String.Pos) (state : PartElabM.State) : PartElabM.State :=
  match state.close endPos with
  | none => state
  | some state' =>
    if state'.currentLevel > 0 then
      state'.closeAll endPos
    else state'

partial def closePartsUntil (outer : Nat) (endPos : String.Pos) : PartElabM Unit := do
  let level ← currentLevel
  if outer ≤ level then
    match (← getThe PartElabM.State).partContext.close endPos with
    | some ctxt' =>
      modifyThe PartElabM.State fun st => {st with partContext := ctxt'}
      if outer < level then
        closePartsUntil outer endPos
    | none => pure ()

@[part_command Verso.Syntax.header]
partial def _root_.Verso.Syntax.header.command : PartCommand
  | stx@`(block|header($headerLevel){$inlines*}) => do
    let titleBits ← liftDocElabM <| inlines.mapM elabInline
    let titleString := headerStxToString (← getEnv) stx
    let ambientLevel ← currentLevel
    let headerLevel := headerLevel.getNat + 1
    if headerLevel > ambientLevel + 1 then throwErrorAt stx "Wrong header nesting - got {headerLevel} but expected at most {ambientLevel}"
    -- New subheader?
    if headerLevel == ambientLevel + 1 then
      -- Prelude is done!
      pure ()
    else
      if let none := stx.getPos? then dbg_trace "No start position for {stx}"
      closePartsUntil headerLevel stx.getPos!

    -- Start a new subpart
    push {
      titleSyntax := stx,
      expandedTitle := some (titleString, titleBits),
      metadata := none,
      blocks := #[],
      priorParts := #[]
    }

  | _ => throwUnsupportedSyntax

@[part_command Verso.Syntax.metadata_block]
def _root_.Verso.Syntax.metadata_block.command : PartCommand
  | `(block| %%%%$tk $fieldOrAbbrev*  %%%) => do
    let ctxt := (← getThe PartElabM.State).partContext
    if ctxt.blocks.size > 0 || ctxt.priorParts.size > 0 then
      throwErrorAt tk "Metadata blocks must precede both content and subsections"
    if ctxt.metadata.isSome then
      throwErrorAt tk "Metadata already provided for this section"
    let stx ← `(term| { $fieldOrAbbrev* })
    modifyThe PartElabM.State fun st => {st with partContext.metadata := some stx}
  | _ => throwUnsupportedSyntax

@[part_command Verso.Syntax.block_role]
def includeSection : PartCommand
  | `(block|block_role{include $_args* }[ $content ]) => throwErrorAt content "Unexpected block argument"
  | `(block|block_role{include}) => throwError "Expected an argument"
  | `(block|block_role{include $arg1 $arg2 $arg3 $args*}) => throwErrorAt arg2 "Expected one or two arguments"
  | stx@`(block|block_role{include $args* }) => do
    match (← parseArgs args) with
    | #[.anon (.name x)] =>
      let name ← resolved x
      addPart <| .included name
    | #[.anon (.num lvl), .anon (.name x)] =>
      let name ← resolved x
      closePartsUntil lvl.getNat stx.getHeadInfo.getPos!
      addPart <| .included name
    | _ => throwErrorAt stx "Expected exactly one positional argument that is a name"
  | _ => Lean.Elab.throwUnsupportedSyntax
where
 resolved id := mkIdentFrom id <$> realizeGlobalConstNoOverloadWithInfo (mkIdentFrom id (docName id.getId))

@[block_elab Verso.Syntax.block_role]
def _root_.Verso.Syntax.block_role.elab : BlockElab := fun block =>
  match block with
  | `(block|block_role{$name $args*}) => do
    withTraceNode `Elab.Verso.block (fun _ => pure m!"Block role {name}") <|
    withRef block <| withFreshMacroScope <| withIncRecDepth <| do
      let ⟨genre, _⟩ ← readThe DocElabContext
      let resolvedName ← realizeGlobalConstNoOverloadWithInfo name
      let exp ← blockRoleExpandersFor resolvedName
      let elabs ← blockRoleElabsFor resolvedName
      let argVals ← parseArgs args
      if exp.isEmpty && elabs.isEmpty then
        return (← Term.elabTerm (← appFallback block name resolvedName argVals none) (some (← blockType)))
      for e in exp do
        try
          let termStxs ← withFreshMacroScope <| e argVals #[]
          return (← Term.elabTerm (← ``(Block.concat (genre := $(⟨genre⟩)) #[$[$termStxs],*])) (some (← blockType)))
        catch
          | ex@(.internal id) =>
            if id == unsupportedSyntaxExceptionId then pure ()
            else throw ex
          | ex => throw ex
      for e in elabs do
        try
          return (← withFreshMacroScope <| e argVals #[])
        catch
          | ex@(.internal id) =>
            if id == unsupportedSyntaxExceptionId then pure ()
            else throw ex
          | ex => throw ex

      throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

@[block_elab Verso.Syntax.para]
partial def _root_.Verso.Syntax.para.elab : BlockElab
  | `(block| para[ $args:inline* ]) => do
    Meta.mkAppM ``Block.para #[← Meta.mkArrayLit (← inlineType) (← args.mapM elabInline').toList]
  | _ =>
    throwUnsupportedSyntax

def elabLi (block : Syntax) : DocElabM (Syntax × Expr) :=
  withRef block <|
  match block with
  | `(list_item|*%$dot $contents:block*) => do
    let item ← Meta.mkAppM ``ListItem.mk #[(← Meta.mkArrayLit (← DocElabM.blockType) (← contents.mapM elabBlock').toList)]
    pure (dot, item)
  | _ =>
    throwUnsupportedSyntax

@[block_elab Verso.Syntax.ul]
def _root_.Verso.Syntax.ul.elab : BlockElab
  | `(block|ul{$itemStxs*}) => do
    let mut bullets : Array Syntax := #[]
    let mut items : Array Expr := #[]
    for i in itemStxs do
      let (b, item) ← elabLi i
      bullets := bullets.push b
      items := items.push item
    let info := DocListInfo.mk bullets itemStxs
    for b in bullets do
      pushInfoLeaf <| .ofCustomInfo {stx := b, value := Dynamic.mk info}
    let t ← Meta.mkAppM ``ListItem #[← DocElabM.blockType]
    Meta.mkAppM ``Block.ul #[← Meta.mkArrayLit t items.toList]
  | _ =>
    throwUnsupportedSyntax

@[block_elab Verso.Syntax.ol]
def _root_.Verso.Syntax.ol.elab : BlockElab
  | `(block|ol($start:num){$itemStxs*}) => do
    let mut bullets : Array Syntax := #[]
    let mut items : Array Expr := #[]
    for i in itemStxs do
      let (b, item) ← elabLi i
      bullets := bullets.push b
      items := items.push item
    let info := DocListInfo.mk bullets itemStxs
    for b in bullets do
      pushInfoLeaf <| .ofCustomInfo {stx := b, value := Dynamic.mk info}
    let t ← Meta.mkAppM ``ListItem #[← DocElabM.blockType]
    Meta.mkAppM ``Block.ol #[toExpr (Int.ofNat start.getNat), ← Meta.mkArrayLit t items.toList]
  | _ =>
    throwUnsupportedSyntax

def elabDesc (block : Syntax) : DocElabM (Syntax × Expr) :=
  withRef block <|
  match block with
  | `(desc_item|:%$colon $dts* => $dds*) => do
    let ⟨_, g⟩ ← readThe DocElabContext
    let it := .app (.const ``Inline []) g
    let bt := .app (.const ``Block []) g
    let item := mkApp4 (.const ``DescItem.mk [0, 0]) it bt (← Meta.mkArrayLit it (← dts.mapM elabInline').toList) (← Meta.mkArrayLit bt (← dds.mapM elabBlock').toList)
    pure (colon, item)
  | _ =>
    throwUnsupportedSyntax

@[block_elab Verso.Syntax.dl]
def _root_.Verso.Syntax.dl.elab : BlockElab
  | `(block|dl{$itemStxs*}) => do
    let ⟨_, g⟩ ← readThe DocElabContext
    let mut colons : Array Syntax := #[]
    let mut items : Array Expr := #[]
    for i in itemStxs do
      let (b, item) ← elabDesc i
      colons := colons.push b
      items := items.push item
    let info := DocListInfo.mk colons itemStxs
    for b in colons do
      pushInfoLeaf <| .ofCustomInfo {stx := b, value := Dynamic.mk info}
    let it := .app (.const ``Inline []) g
    let bt := .app (.const ``Block []) g
    let itemType := mkApp2 (.const ``DescItem [0, 0]) it bt
    return mkApp2 (.const ``Block.dl []) g (← Meta.mkArrayLit itemType items.toList)
  | _ =>
    throwUnsupportedSyntax

@[block_elab Verso.Syntax.blockquote]
def _root_.Verso.Syntax.blockquote.elab : BlockElab
  | `(block|> $innerBlocks*) => do
    let ⟨_, g⟩ ← readThe DocElabContext
    let bt ← blockType
    return mkApp2 (.const ``Block.blockquote []) g (← Meta.mkArrayLit bt (← innerBlocks.mapM elabBlock').toList)
  | _ =>
    throwUnsupportedSyntax


@[block_elab Verso.Syntax.codeblock]
def _root_.Verso.Syntax.codeblock.expand : BlockElab
  | `(block|``` $nameStx:ident $argsStx* | $contents:str ```) => do
      let ⟨_, g⟩ ← readThe DocElabContext
      let name ← realizeGlobalConstNoOverloadWithInfo nameStx
      -- TODO typed syntax here
      let args ← parseArgs <| argsStx.map (⟨·⟩)
      let bt ← blockType

      let exp ← codeBlockExpandersFor name
      for e in exp do
        try
          let termStxs ← withFreshMacroScope <| e args contents
          let blks ← termStxs.mapM (Term.elabTerm · (some bt))
          return mkApp2 (.const ``Block.concat []) g (← Meta.mkArrayLit bt blks.toList)
        catch
          | ex@(.internal id) =>
            if id == unsupportedSyntaxExceptionId then pure ()
            else throw ex
          | ex => throw ex

      let exp ← codeBlockElabsFor name
      for e in exp do
        try
          let blk ← withFreshMacroScope <| e args contents
          return blk
        catch
          | ex@(.internal id) =>
            if id == unsupportedSyntaxExceptionId then pure ()
            else throw ex
          | ex => throw ex

      throwUnsupportedSyntax
  | `(block|``` | $contents:str ```) => do
    let ⟨_, g⟩ ← readThe DocElabContext
    return mkApp2 (.const ``Block.code []) g (toExpr contents.getString)
  | _ =>
    throwUnsupportedSyntax

@[block_elab Verso.Syntax.directive]
def _root_.Verso.Syntax.directive.expand : BlockElab
  | `(block| ::: $nameStx:ident $argsStx* { $contents:block* } ) => do

    let ⟨genre, _⟩ ← readThe DocElabContext
    let name ← realizeGlobalConstNoOverloadWithInfo nameStx
    let args ← parseArgs argsStx

    let exp ← directiveExpandersFor name
    for e in exp do
      try
        let termStxs ← withFreshMacroScope <| e args contents
        return (← Term.elabTerm (← ``(Block.concat (genre := $(⟨genre⟩)) #[$[$termStxs],*])) (← blockType))
      catch
        | ex@(.internal id) =>
          if id == unsupportedSyntaxExceptionId then pure ()
          else throw ex
        | ex => throw ex

    let exp ← directiveElabsFor name
    for e in exp do
      try
        return (← withFreshMacroScope <| e args contents)
      catch
        | ex@(.internal id) =>
          if id == unsupportedSyntaxExceptionId then pure ()
          else throw ex
        | ex => throw ex

    throwUnsupportedSyntax
  | _ =>
    throwUnsupportedSyntax
