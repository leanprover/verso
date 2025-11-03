/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Doc.Elab.Monad
import Lean.DocString.Syntax

namespace Verso.Doc.Elab

open Lean Elab
open PartElabM
open DocElabM
open Lean.Doc.Syntax
open Verso.ArgParse (SigDoc)

def throwUnexpected [Monad m] [MonadError m] (stx : Syntax) : m α :=
  throwErrorAt stx "unexpected syntax{indentD stx}"

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
      throwUnexpected stx
  | other =>
    throwUnexpected other

@[inline_expander Lean.Doc.Syntax.text]
partial def _root_.Lean.Doc.Syntax.text.expand : InlineExpander := fun x =>
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

@[inline_expander Lean.Doc.Syntax.linebreak]
def _root_.linebreak.expand : InlineExpander
  | `(inline|line! $s:str) =>
    ``(Inline.linebreak $(quote s.getString))
  | _ => throwUnsupportedSyntax

@[inline_expander Lean.Doc.Syntax.emph]
def _root_.Lean.Doc.Syntax.emph.expand : InlineExpander
  | `(inline| _[ $args* ]) => do
    ``(Inline.emph #[$[$(← args.mapM elabInline)],*])
  | _ => throwUnsupportedSyntax

@[inline_expander Lean.Doc.Syntax.bold]
def _root_.Lean.Doc.Syntax.bold.expand : InlineExpander
  | `(inline| *[ $args* ]) => do
    ``(Inline.bold #[$[$(← args.mapM elabInline)],*])
  | _ => throwUnsupportedSyntax

def parseArgVal (val : TSyntax `arg_val) : DocElabM ArgVal := do
  match val with
  | `(arg_val|$s:str) => pure <| .str s
  | `(arg_val|$x:ident) => pure <| .name x
  | `(arg_val|$n:num) => pure <| .num n
  | other => throwErrorAt other "Can't decode argument value '{repr other}'"

def parseArgs (argStx : TSyntaxArray `doc_arg) : DocElabM (Array Arg) := do
  let mut argVals := #[]
  for arg in argStx do
    match arg with
    | `(doc_arg|$v:arg_val) =>
      argVals := argVals.push (.anon (← parseArgVal v))
    | `(doc_arg|$x:ident := $v) => do
      let src := (← getFileMap).source
      if let some ⟨s, e⟩ := x.raw.getRange? (canonicalOnly := true) then
        if let some ⟨s', e'⟩ := v.raw.getRange? (canonicalOnly := true) then
          let hint ← MessageData.hint m!"Replace with the updated syntax:" #[s!"({s.extract src e} := {s'.extract src e'})"] (ref? := some arg)
          logWarningAt arg m!"Deprecated named argument syntax for `{x}`{hint}"
      argVals := argVals.push (.named arg x (← parseArgVal v))
    | `(doc_arg|($x:ident := $v)) =>
      argVals := argVals.push (.named arg x (← parseArgVal v))
    | `(doc_arg|+$x) =>
      argVals := argVals.push (.flag arg x true)
    | `(doc_arg|-$x) =>
      argVals := argVals.push (.flag arg x false)
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
    | .flag _orig y v => `(namedArgument|($y := $(quote v))) -- TODO location
  let subs ← subjectArr.mapM (·.mapM elabInline)
  let arrArg ← match subs with
    | some ss => (#[·]) <$> `(#[$ss,*])
    | none => pure #[]
  let appStx :=
    Syntax.node2 stx.getHeadInfo ``app
      f (.node .none nullKind <| arrArg ++ argStx)
  return ⟨appStx⟩

private def expanderDocHover (stx : Syntax) (what : String) (name : Name) (doc? : Option String) (sig? : Option SigDoc) : DocElabM Unit := do
  let mut out := s!"{what} `{name}`"
  if let some sig := sig? then

    out := out ++ "\n\n" ++ (← sig.toString)
  if let some d := doc? then
    out := out ++ "\n\n" ++ d
  Hover.addCustomHover stx out


open Lean.Parser.Term in
@[inline_expander Lean.Doc.Syntax.role]
def _root_.Lean.Doc.Syntax.role.expand : InlineExpander
  | inline@`(inline| role{$name $args*} [$subjects*]) => do
      withRef inline <| withFreshMacroScope <| withIncRecDepth <| do
        let genre := (← readThe DocElabContext).genreSyntax
        let resolvedName ← realizeGlobalConstNoOverloadWithInfo name
        let exp ← roleExpandersFor resolvedName
        let argVals ← parseArgs args
        if exp.isEmpty then
          -- If no expanders are registered, then try elaborating just as a
          -- function application node
          return ← appFallback inline name resolvedName argVals subjects
        for (e, doc?, sig?) in exp do
          try
            let termStxs ← withFreshMacroScope <| e argVals subjects
            expanderDocHover name "Role" resolvedName doc? sig?
            let termStxs ← termStxs.mapM fun t => (``(($t : Inline $(⟨genre⟩))))
            if h : termStxs.size = 1 then return termStxs[0]
            else return (← ``(Inline.concat (genre := $(⟨genre⟩)) #[$[$termStxs],*]))
          catch
            | ex@(.internal id) =>
              if id == unsupportedSyntaxExceptionId then pure ()
              else throw ex
            | ex => throw ex
        throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

@[inline_expander Lean.Doc.Syntax.link]
def _root_.Lean.Doc.Syntax.link.expand : InlineExpander
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

@[inline_expander Lean.Doc.Syntax.footnote]
def _root_.Lean.Doc.Syntax.link.footnote : InlineExpander
  | `(inline| footnote( $name:str )) => do
    ``(Inline.footnote $(quote name.getString) $(← addFootnoteRef name))
  | _ => throwUnsupportedSyntax


@[inline_expander Lean.Doc.Syntax.image]
def _root_.Lean.Doc.Syntax.image.expand : InlineExpander
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


@[inline_expander Lean.Doc.Syntax.code]
def _root_.Lean.Doc.Syntax.code.expand : InlineExpander
  |  `(inline| code( $s )) =>
    ``(Inline.code $(quote s.getString))
  | _ => throwUnsupportedSyntax


@[inline_expander Lean.Doc.Syntax.inline_math]
def _root_.Lean.Doc.Syntax.inline_math.expand : InlineExpander
  |  `(inline| \math code( $s )) =>
    ``(Inline.math MathMode.inline $s)
  | _ => throwUnsupportedSyntax

@[inline_expander Lean.Doc.Syntax.display_math]
def _root_.Lean.Doc.Syntax.display_math.expand : InlineExpander
  |  `(inline| \displaymath code( $s )) =>
    ``(Inline.math MathMode.display $s)
  | _ => throwUnsupportedSyntax

def decorateClosing : TSyntax `block → DocElabM Unit
  | `(block|:::%$s $_ $_* { $_* }%$e)
  | `(block|```%$s $_ $_* | $_ ```%$e)
  | `(block|%%%%$s $_* %%%%$e) => closes s e
  | _ => pure ()

/-- Elaborates a parsed block into syntax denoting an expression of type `Block genre`. -/
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
      let which := (← getThe PartElabM.State).partContext.priorParts.back?.map fun
        | .mk _ _ titleString .. => s!" (namely “{titleString}”)"
        | .included n => s!" (namely `{unDocName n.getId}`)"
      let which := which.getD ""
      let msg := m!"Block content found in a context where a header was expected."
      let note := MessageData.note m!"A document part (section/chapter/etc) consists of a header, followed by zero or more blocks, followed by zero or more sub-parts. This block occurs after a sub-part{which}, but outside of the sub-parts."
      throwErrorAt cmd "{msg}\n{note}"
    let hygenicName := some <| mkIdent (← mkFreshUserName `docReconstInBlock)
    let blk ← withTheReader DocElabContext ({ · with docReconstructionPlaceholder := hygenicName }) <|
      elabBlock cmd
    addBlock blk (blockInternalDocReconstructionPlaceholder := hygenicName)

@[part_command Lean.Doc.Syntax.footnote_ref]
partial def _root_.Lean.Doc.Syntax.footnote_ref.command : PartCommand
  | `(block| [^ $name:str ]: $contents* ) =>
    addFootnoteDef name =<< contents.mapM (withRefsAllowed .onlyIfDefined <| elabInline ·)
  | _ => throwUnsupportedSyntax

@[part_command Lean.Doc.Syntax.link_ref]
partial def _root_.Lean.Doc.Syntax.link_ref.command : PartCommand
  | `(block| [ $name:str ]: $url:str ) =>
    addLinkDef name url.getString
  | _ => throwUnsupportedSyntax

partial def PartElabM.State.close (endPos : String.Pos.Raw) (state : PartElabM.State) : Option PartElabM.State :=
  state.partContext.close endPos |>.map ({state with partContext := ·})

partial def PartElabM.State.closeAll (endPos : String.Pos.Raw) (state : PartElabM.State) : PartElabM.State :=
  match state.close endPos with
  | none => state
  | some state' =>
    if state'.currentLevel > 0 then
      state'.closeAll endPos
    else state'

partial def closePartsUntil (outer : Nat) (endPos : String.Pos.Raw) : PartElabM Unit := do
  let level ← currentLevel
  if outer ≤ level then
    match (← getThe PartElabM.State).partContext.close endPos with
    | some ctxt' =>
      modifyThe PartElabM.State fun st => {st with partContext := ctxt'}
      if outer < level then
        closePartsUntil outer endPos
    | none => pure ()

@[part_command Lean.Doc.Syntax.header]
partial def _root_.Lean.Doc.Syntax.header.command : PartCommand
  | stx@`(block|header($headerLevel){$inlines*}) => do
    let titleBits ← liftDocElabM <| inlines.mapM elabInline
    let titleString := headerStxToString (← getEnv) stx
    let ambientLevel ← currentLevel
    let headerLevel := headerLevel.getNat + 1
    if headerLevel > ambientLevel + 1 then throwErrorAt stx "Wrong header nesting - got {"".pushn '#' headerLevel} but expected at most {"#".pushn '#' ambientLevel}"
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

@[part_command Lean.Doc.Syntax.metadata_block]
def _root_.Lean.Doc.Syntax.metadata_block.command : PartCommand
  | `(block| %%%%$tk $fieldOrAbbrev*  %%%) => do
    let ctxt := (← getThe PartElabM.State).partContext
    if ctxt.blocks.size > 0 || ctxt.priorParts.size > 0 then
      throwErrorAt tk "Metadata blocks must precede both content and subsections"
    if ctxt.metadata.isSome then
      throwErrorAt tk "Metadata already provided for this section"
    let stx ← `(term| { $fieldOrAbbrev* })
    modifyThe PartElabM.State fun st => {st with partContext.metadata := some stx}
  | _ => throwUnsupportedSyntax

@[part_command Lean.Doc.Syntax.command]
def includeSection : PartCommand
  | `(block|command{include $args* }) => do
    if h : args.size = 0 then throwError "Expected an argument"
    else if h : args.size > 2 then throwErrorAt args[2] "Expected one or two arguments"
    else
      let ref ← getRef
      Hover.addCustomHover ref
        r#"Includes another document at this point in the document.

  * `{include NAME}`: Includes the document as a child part.
  * `{include N NAME}`: Includes the document at header level `N`, as if its header had `N` header indicators (`#`) before it.
  "#
      match (← parseArgs args) with
      | #[.anon (.name x)] =>
        let name ← resolved x
        addPart <| .included name
      | #[.anon (.num lvl), .anon (.name x)] =>
        let name ← resolved x
        closePartsUntil lvl.getNat ref.getHeadInfo.getPos!
        addPart <| .included name
      | _ => throwErrorAt ref "Expected exactly one positional argument that is a name"
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)
where
 resolved id := mkIdentFrom id <$> realizeGlobalConstNoOverloadWithInfo (mkIdentFrom id (docName id.getId))

@[block_expander Lean.Doc.Syntax.command]
def _root_.Lean.Doc.Syntax.command.expand : BlockExpander := fun block =>
  match block with
  | `(block|command{$name $args*}) => do
    withTraceNode `Elab.Verso.block (fun _ => pure m!"Block role {name}") <|
    withRef block <| withFreshMacroScope <| withIncRecDepth <| do
      let genre := (← readThe DocElabContext).genreSyntax
      let resolvedName ← realizeGlobalConstNoOverloadWithInfo name
      let exp ← blockCommandExpandersFor resolvedName
      let argVals ← parseArgs args
      if exp.isEmpty then
        return ← appFallback block name resolvedName argVals none
      for (e, doc?, sig?) in exp do
        try
          let termStxs ← withFreshMacroScope <| e argVals
          expanderDocHover name "Command" resolvedName doc? sig?
          return (← ``(Block.concat (genre := $(⟨genre⟩)) #[$[$termStxs],*]))
        catch
          | ex@(.internal id) =>
            if id == unsupportedSyntaxExceptionId then pure ()
            else throw ex
          | ex => throw ex
      throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

@[block_expander Lean.Doc.Syntax.para]
partial def _root_.Lean.Doc.Syntax.para.expand : BlockExpander
  | `(block| para[ $args:inline* ]) => do
    let genre := (← readThe DocElabContext).genreSyntax
    ``(Block.para (genre := $(⟨genre⟩)) #[$[$(← args.mapM elabInline)],*])
  | _ =>
    throwUnsupportedSyntax


def elabLi (block : Syntax) : DocElabM (Syntax × TSyntax `term) :=
  withRef block <|
  match block with
  | `(list_item|*%$dot $contents:block*) => do
    let genre := (← readThe DocElabContext).genreSyntax
    let item ← ``(ListItem.mk (α := Block $(⟨genre⟩)) #[$[$(← contents.mapM elabBlock)],*])
    pure (dot, item)
  | _ =>
    throwUnsupportedSyntax

@[block_expander Lean.Doc.Syntax.ul]
def _root_.Lean.Doc.Syntax.ul.expand : BlockExpander
  | `(block|ul{$itemStxs*}) => do
    let genre := (← readThe DocElabContext).genreSyntax
    let mut bullets : Array Syntax := #[]
    let mut items : Array (TSyntax `term) := #[]
    for i in itemStxs do
      let (b, item) ← elabLi i
      bullets := bullets.push b
      items := items.push item
    let info := DocListInfo.mk bullets itemStxs
    for b in bullets do
      pushInfoLeaf <| .ofCustomInfo {stx := b, value := Dynamic.mk info}
    ``(Block.ul (genre := $(⟨genre⟩)) #[$items,*])
  | _ =>
    throwUnsupportedSyntax

@[block_expander Lean.Doc.Syntax.ol]
def _root_.Lean.Doc.Syntax.ol.expand : BlockExpander
  | `(block|ol($start:num){$itemStxs*}) => do
    let genre := (← readThe DocElabContext).genreSyntax
    let mut bullets : Array Syntax := #[]
    let mut items : Array (TSyntax `term) := #[]
    for i in itemStxs do
      let (b, item) ← elabLi i
      bullets := bullets.push b
      items := items.push item
    let info := DocListInfo.mk bullets itemStxs
    for b in bullets do
      pushInfoLeaf <| .ofCustomInfo {stx := b, value := Dynamic.mk info}
    ``(Block.ol (genre := $(⟨genre⟩)) $start #[$items,*])
  | _ =>
    throwUnsupportedSyntax

def elabDesc (block : Syntax) : DocElabM (Syntax × TSyntax `term) :=
  withRef block <|
  match block with
  | `(desc_item|:%$colon $dts* => $dds*) => do
    let genre := (← readThe DocElabContext).genreSyntax
    let item ← ``(DescItem.mk (α := Inline $(⟨genre⟩)) (β := Block $(⟨genre⟩))  #[$[$(← dts.mapM elabInline)],*] #[$[$(← dds.mapM elabBlock)],*])
    pure (colon, item)
  | _ =>
    throwUnsupportedSyntax

@[block_expander Lean.Doc.Syntax.dl]
def _root_.Lean.Doc.Syntax.dl.expand : BlockExpander
  | `(block|dl{$itemStxs*}) => do
    let genre := (← readThe DocElabContext).genreSyntax
    let mut colons : Array Syntax := #[]
    let mut items : Array (TSyntax `term) := #[]
    for i in itemStxs do
      let (b, item) ← elabDesc i
      colons := colons.push b
      items := items.push item
    let info := DocListInfo.mk colons itemStxs
    for b in colons do
      pushInfoLeaf <| .ofCustomInfo {stx := b, value := Dynamic.mk info}
    ``(Block.dl (genre := $(⟨genre⟩)) #[$[$items],*])
  | _ =>
    throwUnsupportedSyntax

@[block_expander Lean.Doc.Syntax.blockquote]
def _root_.Lean.Doc.Syntax.blockquote.expand : BlockExpander
  | `(block|> $innerBlocks*) => do
    ``(Block.blockquote #[$[$(← innerBlocks.mapM elabBlock)],*])
  | _ =>
    throwUnsupportedSyntax


@[block_expander Lean.Doc.Syntax.codeblock]
def _root_.Lean.Doc.Syntax.codeblock.expand : BlockExpander
  | `(block|``` $nameStx:ident $argsStx* | $contents:str ```) => do
    let genre := (← readThe DocElabContext).genreSyntax
    let name ← realizeGlobalConstNoOverloadWithInfo nameStx
    let exp ← codeBlockExpandersFor name
    -- TODO typed syntax here
    let args ← parseArgs <| argsStx.map (⟨·⟩)
    for (e, doc?, sig?) in exp do
      try
        let termStxs ← withFreshMacroScope <| e args contents
        expanderDocHover nameStx "Code block" name doc? sig?
        return (← ``(Block.concat (genre := $(⟨genre⟩)) #[$[$termStxs],*]))
      catch
        | ex@(.internal id) =>
          if id == unsupportedSyntaxExceptionId then pure ()
          else throw ex
        | ex => throw ex
    throwUnsupportedSyntax
  | `(block|``` | $contents:str ```) => do
    ``(Block.code $(quote contents.getString))
  | _ =>
    throwUnsupportedSyntax

@[block_expander Lean.Doc.Syntax.directive]
def _root_.Lean.Doc.Syntax.directive.expand : BlockExpander
  | `(block| ::: $nameStx:ident $argsStx* { $contents:block* } ) => do
    let genre := (← readThe DocElabContext).genreSyntax
    let name ← realizeGlobalConstNoOverloadWithInfo nameStx
    let exp ← directiveExpandersFor name
    let args ← parseArgs argsStx
    for (e, doc?, sig?) in exp do
      try
        let termStxs ← withFreshMacroScope <| e args contents
        expanderDocHover nameStx "Directive" name doc? sig?
        return (← ``(Block.concat (genre := $(⟨genre⟩)) #[$[$termStxs],*]))
      catch
        | ex@(.internal id) =>
          if id == unsupportedSyntaxExceptionId then pure ()
          else throw ex
        | ex => throw ex
    throwUnsupportedSyntax
  | _ =>
    throwUnsupportedSyntax
