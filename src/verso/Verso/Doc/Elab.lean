/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Verso.Doc.Elab.Monad
meta import Verso.Doc.Elab.Monad
public import Lean.DocString.Syntax
public meta import Verso.Doc.Elab.ExtensionResolution
import Verso.Doc.Elab.Inline
public import Verso.Doc.Elab.Inline
public meta import Verso.Doc.Elab.Inline
public import Verso.Doc.Elab.Block
public meta import Verso.Doc.Elab.Block

namespace Verso.Doc.Elab

open Lean Elab
open PartElabM
open DocElabM
open Lean.Doc (ArgView ArgValView BlockView DescItemView MathMode VersoBlock)
open Lean.Doc.Parser
open Verso.ArgParse (SigDoc)

set_option backward.privateInPublic false

@[inline_expander Lean.Doc.Parser.Inline.text]
public meta partial def _root_.Lean.Doc.Parser.Inline.text.expand : InlineExpander
  -- `quote` builds the literal without source locations, preventing unwanted hover info
  | .text v => ``(Inline.text $(quote v.getVersoText))
  | _ => throwUnsupportedSyntax

@[inline_expander Lean.Doc.Parser.Inline.linebreak]
public meta def _root_.Lean.Doc.Parser.Inline.linebreak.expand : InlineExpander
  | .linebreak _ => ``(Inline.linebreak $(quote "\n"))
  | _ => throwUnsupportedSyntax

@[inline_expander Lean.Doc.Parser.Inline.emph]
public meta def _root_.Lean.Doc.Parser.Inline.emph.expand : InlineExpander
  | .emph v => do
    ``(Inline.emph #[$[$(← v.content.mapM elabInline)],*])
  | _ => throwUnsupportedSyntax

@[inline_expander Lean.Doc.Parser.Inline.bold]
public meta def _root_.Lean.Doc.Parser.Inline.bold.expand : InlineExpander
  | .bold v => do
    ``(Inline.bold #[$[$(← v.content.mapM elabInline)],*])
  | _ => throwUnsupportedSyntax

meta def parseArgVal (val : TSyntax ``Lean.Doc.Parser.argVal) : DocElabM ArgVal := do
  match ArgValView.of val with
  | some (.str s _) => pure <| .str s
  | some (.name x) => pure <| .name x
  | some (.num n _) => pure <| .num n
  | none => throwErrorAt val "Can't decode argument value '{repr val}'"

public meta def parseArgs (argStx : TSyntaxArray ``Lean.Doc.Parser.arg) :
    DocElabM (Array Arg) := do
  let mut argVals := #[]
  for arg in argStx do
    match ArgView.of arg with
    | some (.anon (val := v) ..) =>
      argVals := argVals.push (.anon (← parseArgVal v))
    | some (.named (parens := none) (name := x) (val := v) ..) => do
      -- A named argument without parentheses is the deprecated spelling.
      let src := (← getFileMap).source
      if let some ⟨s, e⟩ := x.raw.getRange? (canonicalOnly := true) then
        if let some ⟨s', e'⟩ := v.raw.getRange? (canonicalOnly := true) then
          let hint ← MessageData.hint m!"Replace with the updated syntax:" #[s!"({s.extract src e} := {s'.extract src e'})"] (ref? := some arg)
          logWarningAt arg m!"Deprecated named argument syntax for `{x}`{hint}"
      argVals := argVals.push (.named arg x (← parseArgVal v))
    | some (.named (parens := some _) (name := x) (val := v) ..) =>
      argVals := argVals.push (.named arg x (← parseArgVal v))
    | some (.flag (name := x) (isOn := isOn) ..) =>
      argVals := argVals.push (.flag arg x isOn)
    | none => throwErrorAt arg "Can't decode argument '{repr arg}'"
  pure argVals

open Lean.Parser.Term in
open Lean.Doc in
meta def appFallback
    (stx : Syntax)
    (name : Ident) (resolvedName : Name)
    (argVals : Array Arg) (subjectArr : Option (Array VersoInline))
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

private meta def expanderDocHover (stx : Syntax) (what : String) (name : Name) (doc? : Option String) (sig? : Option SigDoc) : DocElabM Unit := do
  let mut out := s!"{what} `{name}`"
  if let some sig := sig? then

    out := out ++ "\n\n" ++ (← sig.toString)
  if let some d := doc? then
    out := out ++ "\n\n" ++ d
  Hover.addCustomHover stx out

private inductive ExtensionResultShape where
  | inline
  | block

private meta def extensionResult {α : Type}
    (shape : ExtensionResultShape)
    (what : String) (nameStx : Ident) (resolvedName : Name)
    (expanders : Array (α × Option String × Option SigDoc))
    (run : α → DocElabM (Array (TSyntax `term))) :
    DocElabM Term := do
  let genre := (← readThe DocElabContext).genreSyntax
  tryExtensionExpanders expanders fun (e, doc?, sig?) => do
    let termStxs ← withFreshMacroScope <| run e
    expanderDocHover nameStx what resolvedName doc? sig?
    match shape with
    | .inline =>
      let termStxs ← termStxs.mapM fun t => (``(($t : Inline $(⟨genre⟩))))
      if h : termStxs.size = 1 then return termStxs[0]
      else return (← ``(Inline.concat (genre := $(⟨genre⟩)) #[$[$termStxs],*]))
    | .block =>
      return (← ``(Block.concat (genre := $(⟨genre⟩)) #[$[$termStxs],*]))

open Lean.Parser.Term in
@[inline_expander Lean.Doc.Parser.Inline.role]
public meta def _root_.Lean.Doc.Parser.Inline.role.expand : InlineExpander
  | .role v => do
      let (name, args, subjects) := (v.name, v.args, v.content)
      withRef v.stx <| withFreshMacroScope <| withIncRecDepth <| do
        let (resolvedName, exp) ← registeredExtensionExpanders
          "role" "@[role]" registeredRoleNames roleExpandersFor isRoleExpanderTargetType name
        let argVals ← parseArgs args
        extensionResult .inline "Role" name resolvedName exp fun e => e argVals subjects
  | _ => throwUnsupportedSyntax

@[inline_expander Lean.Doc.Parser.Inline.link]
public meta def _root_.Lean.Doc.Parser.Inline.link.expand : InlineExpander
  | .link v => do
    let url : TSyntax `term ←
      match v.target with
      | .url (url := u) .. => pure (quote u.getVersoLinkUrl)
      | .ref (name := name) .. => addLinkRef name
    ``(Inline.link #[$[$(← v.content.mapM elabInline)],*] $url)
  | _ => throwUnsupportedSyntax

@[inline_expander Lean.Doc.Parser.Inline.footnote]
public meta def _root_.Lean.Doc.Parser.Inline.footnote.expand : InlineExpander
  | .footnote v => do
    ``(Inline.footnote $(quote v.getName) $(← addFootnoteRef v.name))
  | _ => throwUnsupportedSyntax


@[inline_expander Lean.Doc.Parser.Inline.image]
public meta def _root_.Lean.Doc.Parser.Inline.image.expand : InlineExpander
  | .image v => do
    let url : TSyntax `term ←
      match v.target with
      | .url (url := u) .. => pure (quote u.getVersoLinkUrl)
      | .ref (name := name) .. => addLinkRef name
    ``(Inline.image $(quote v.getAlt) $url)
  | _ => throwUnsupportedSyntax


@[inline_expander Lean.Doc.Parser.Inline.code]
public meta def _root_.Lean.Doc.Parser.Inline.code.expand : InlineExpander
  | .code v => ``(Inline.code $(quote v.getVersoCode))
  | _ => throwUnsupportedSyntax


/-- Both math markers share a view, which records which of them was written. -/
private meta def mathExpand : InlineExpander
  | .math v =>
    match v.mode with
    | .inline => ``(Inline.math MathMode.inline $(quote v.getVersoCode))
    | .display => ``(Inline.math MathMode.display $(quote v.getVersoCode))
  | _ => throwUnsupportedSyntax

@[inline_expander Lean.Doc.Parser.Inline.inline_math]
public meta def _root_.Lean.Doc.Parser.Inline.inline_math.expand : InlineExpander := mathExpand

@[inline_expander Lean.Doc.Parser.Inline.display_math]
public meta def _root_.Lean.Doc.Parser.Inline.display_math.expand : InlineExpander := mathExpand


public meta def partCommand (cmd : VersoBlock) : PartElabM Unit :=
  withTraceNode `Elab.Verso.part (fun _ => pure m!"Part modification {cmd}") <|
  withRef cmd <| withFreshMacroScope <| do
  match cmd.raw with
  | stx@(.node _ kind _) =>
    let some view := BlockView.of ⟨stx⟩
      | fallback
    let exp ← partCommandsFor kind
    for e in exp do
      try
        withFreshMacroScope <| e view
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
        | .mk _ _ _ titleString .. => s!" (namely “{titleString}”)"
        | .included n => s!" (namely `{unDocName n.getId}`)"
      let which := which.getD ""
      let msg := m!"Block content found in a context where a header was expected."
      let note := MessageData.note m!"A document part (section/chapter/etc) consists of a header, followed by zero or more blocks, followed by zero or more sub-parts. This block occurs after a sub-part{which}, but outside of the sub-parts."
      throwErrorAt cmd "{msg}\n{note}"
    let hygenicName := some <| mkIdent (← mkFreshUserName `docReconstInBlock)
    let blk ← withTheReader DocElabContext ({ · with docReconstructionPlaceholder := hygenicName }) <|
      elabBlock cmd
    addBlock blk (blockInternalDocReconstructionPlaceholder := hygenicName)

@[part_command Lean.Doc.Parser.Block.footnote_ref]
public meta partial def _root_.Lean.Doc.Parser.Block.footnote_ref.command : PartCommand
  | .footnoteRef v =>
    addFootnoteDef v.name =<< v.content.mapM (withRefsAllowed .onlyIfDefined <| elabInline ·)
  | _ => throwUnsupportedSyntax

@[part_command Lean.Doc.Parser.Block.link_ref]
public meta partial def _root_.Lean.Doc.Parser.Block.link_ref.command : PartCommand
  | .linkRef v => addLinkDef v.name v.getUrl
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



@[part_command Lean.Doc.Parser.Block.header]
public meta partial def _root_.Lean.Doc.Parser.Block.header.command : PartCommand
  | .header v => do
    let stx := v.stx
    let titleBits ← liftDocElabM <| v.content.mapM elabInline
    let titleString := inlinesToString (← getEnv) (v.content.map (·.raw))
    let ambientLevel ← currentLevel
    let headerLevel := v.level + 1
    if headerLevel > ambientLevel + 1 then throwErrorAt stx "Wrong header nesting - got {"".pushn '#' headerLevel} but expected at most {"#".pushn '#' ambientLevel}"
    -- New subheader?
    if headerLevel == ambientLevel + 1 then
      -- Prelude is done!
      pure ()
    else
      if let none := stx.raw.getPos? then dbg_trace "No start position for {stx}"
      PartElabM.closePartsUntil headerLevel stx.raw.getPos!

    -- Start a new subpart
    push {
      rangeSyntax := stx,
      selectionSyntax := stx,
      expandedTitle := some (titleString, titleBits),
      metadata := none,
      blocks := #[],
      priorParts := #[]
    }

  | _ => throwUnsupportedSyntax

@[part_command Lean.Doc.Parser.Block.metadata_block]
public meta def _root_.Lean.Doc.Parser.Block.metadata_block.command : PartCommand
  | .metadata v => do
    let ctxt := (← getThe PartElabM.State).partContext
    if ctxt.blocks.size > 0 || ctxt.priorParts.size > 0 then
      throwErrorAt v.opener "Metadata blocks must precede both content and subsections"
    if ctxt.metadata.isSome then
      throwErrorAt v.opener "Metadata already provided for this section"
    let fields := v.fields
    let stx : Term := ⟨(← `(Lean.Parser.Term.structInst| { $[$fields],* })).raw⟩
    modifyThe PartElabM.State fun st => {st with partContext.metadata := some stx}
  | _ => throwUnsupportedSyntax

@[part_command Lean.Doc.Parser.Block.command]
public meta def includeSection : PartCommand
  | .command v => do
    unless v.name.getId == `include do Lean.Elab.throwUnsupportedSyntax
    let args := v.args
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

@[block_expander Lean.Doc.Parser.Block.command]
public meta def _root_.Lean.Doc.Parser.Block.command.expand : BlockExpander
  | .command v => do
    let (block, name, args) := (v.stx, v.name, v.args)
    withTraceNode `Elab.Verso.block (fun _ => pure m!"Block role {name}") <|
    withRef block <| withFreshMacroScope <| withIncRecDepth <| do
      let resolvedName ← resolveKnownExtensionName "block command" registeredBlockCommandNames name
      let exp ← blockCommandExpandersFor resolvedName
      let argVals ← parseArgs args
      if exp.isEmpty then
        return ← appFallback block name resolvedName argVals none
      extensionResult .block "Command" name resolvedName exp fun e => e argVals
  | _ => throwUnsupportedSyntax

@[block_expander Lean.Doc.Parser.Block.para]
public meta partial def _root_.Lean.Doc.Parser.Block.para.expand : BlockExpander
  | .para v => do
    let genre := (← readThe DocElabContext).genreSyntax
    ``(Block.para (genre := $(⟨genre⟩)) #[$[$(← v.content.mapM elabInline)],*])
  | _ =>
    throwUnsupportedSyntax


meta def elabLi (marker : Syntax) (contents : Array VersoBlock)
    (stx : Syntax) : DocElabM (Syntax × TSyntax `term) :=
  withRef stx <| do
    let genre := (← readThe DocElabContext).genreSyntax
    let item ← ``(ListItem.mk (α := Block $(⟨genre⟩)) #[$[$(← contents.mapM elabBlock)],*])
    pure (marker, item)

@[block_expander Lean.Doc.Parser.Block.ul]
public meta def _root_.Lean.Doc.Parser.Block.ul.expand : BlockExpander
  | .ul v => do
    let genre := (← readThe DocElabContext).genreSyntax
    let mut bullets : Array Syntax := #[]
    let mut items : Array (TSyntax `term) := #[]
    for i in v.items do
      let (b, item) ← elabLi i.marker i.contents i.stx
      bullets := bullets.push b
      items := items.push item
    let info := DocListInfo.mk bullets (v.items.map (·.stx.raw))
    for b in bullets do
      pushInfoLeaf <| .ofCustomInfo {stx := b, value := Dynamic.mk info}
    ``(Block.ul (genre := $(⟨genre⟩)) #[$items,*])
  | _ =>
    throwUnsupportedSyntax

@[block_expander Lean.Doc.Parser.Block.ol]
public meta def _root_.Lean.Doc.Parser.Block.ol.expand : BlockExpander
  | .ol v => do
    let genre := (← readThe DocElabContext).genreSyntax
    let mut bullets : Array Syntax := #[]
    let mut items : Array (TSyntax `term) := #[]
    for i in v.items do
      let (b, item) ← elabLi i.marker i.contents i.stx
      bullets := bullets.push b
      items := items.push item
    let info := DocListInfo.mk bullets (v.items.map (·.stx.raw))
    for b in bullets do
      pushInfoLeaf <| .ofCustomInfo {stx := b, value := Dynamic.mk info}
    ``(Block.ol (genre := $(⟨genre⟩)) $(quote v.start) #[$items,*])
  | _ =>
    throwUnsupportedSyntax

meta def elabDesc (item : DescItemView) : DocElabM (Syntax × TSyntax `term) :=
  withRef item.stx <| do
    let genre := (← readThe DocElabContext).genreSyntax
    let item' ← ``(DescItem.mk (α := Inline $(⟨genre⟩)) (β := Block $(⟨genre⟩))  #[$[$(← item.term.mapM elabInline)],*] #[$[$(← item.desc.mapM elabBlock)],*])
    pure (item.marker, item')

@[block_expander Lean.Doc.Parser.Block.dl]
public meta def _root_.Lean.Doc.Parser.Block.dl.expand : BlockExpander
  | .dl v => do
    let genre := (← readThe DocElabContext).genreSyntax
    let mut colons : Array Syntax := #[]
    let mut items : Array (TSyntax `term) := #[]
    for i in v.items do
      let (b, item) ← elabDesc i
      colons := colons.push b
      items := items.push item
    let info := DocListInfo.mk colons (v.items.map (·.stx.raw))
    for b in colons do
      pushInfoLeaf <| .ofCustomInfo {stx := b, value := Dynamic.mk info}
    ``(Block.dl (genre := $(⟨genre⟩)) #[$[$items],*])
  | _ =>
    throwUnsupportedSyntax

@[block_expander Lean.Doc.Parser.Block.blockquote]
public meta def _root_.Lean.Doc.Parser.Block.blockquote.expand : BlockExpander
  | .blockquote v => do
    ``(Block.blockquote #[$[$(← v.content.mapM elabBlock)],*])
  | _ =>
    throwUnsupportedSyntax


@[block_expander Lean.Doc.Parser.Block.codeblock]
public meta def _root_.Lean.Doc.Parser.Block.codeblock.expand : BlockExpander
  | .codeblock v => do
    let some nameStx := v.name?
      | return ← ``(Block.code $(quote v.getVersoCodeBlock))
    let args ← parseArgs v.args
    let (resolvedName, exp) ← registeredExtensionExpanders
      "code block" "@[code_block]" registeredCodeBlockNames codeBlockExpandersFor
      isCodeBlockExpanderTargetType nameStx
    extensionResult .block "Code block" nameStx resolvedName exp fun e => e args v.content
  | _ =>
    throwUnsupportedSyntax

@[block_expander Lean.Doc.Parser.Block.directive]
public meta def _root_.Lean.Doc.Parser.Block.directive.expand : BlockExpander
  | .directive v => do
    let args ← parseArgs v.args
    let (resolvedName, exp) ← registeredExtensionExpanders
      "directive" "@[directive]" registeredDirectiveNames directiveExpandersFor
      isDirectiveExpanderTargetType v.name
    extensionResult .block "Directive" v.name resolvedName exp fun e => e args v.content
  | _ =>
    throwUnsupportedSyntax
