/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public meta import Lean.Linter.Basic
public meta import Lean.Meta.Hint
public meta import Lean.Server.CodeActions.Basic
public meta import Verso.Doc.Concrete
public meta import MultiVerso.Slug
public meta import VersoManual.Linters.Options
import VersoManual.Basic

set_option linter.missingDocs true

open Lean Linter Elab Command
open Lean.Doc (HeaderView MetadataView VersoInline)

namespace Verso.Genre.Manual

/-- Checks whether `field`'s name is `tag`. -/
private meta def isTagField (field : TSyntax ``Lean.Parser.Term.structInstField) : Bool :=
    match field with
    | `(Lean.Parser.Term.structInstField|
        $x:ident $[$_* $[$_:typeSpec]? $_:structInstFieldDecl]?) => x.getId == `tag
    | _ => false

private meta partial def suggestId' (name : Array VersoInline) : String := Id.run do
  let mut strTitle := ""
  for inl in name do
    match inl.view with
    | .text s => strTitle := strTitle ++ s.getVersoText.toLower
    | .code c => strTitle := strTitle ++ c.getVersoCode
    | .emph e => strTitle := strTitle ++ suggestId' e.content
    | .bold b => strTitle := strTitle ++ suggestId' b.content
    | .link l => strTitle := strTitle ++ suggestId' l.content
    | .role r => strTitle := strTitle ++ suggestId' r.content
    | _ => pure ()
  return strTitle

private meta def suggestId (name : Array VersoInline) : String :=
  suggestId' name |>.sluggify |>.toString

/--
A recorded fix that adds a tag to a header that's missing one.
-/
private meta structure HeaderTagFix where
  /-- The title and the text edit of each quick fix. -/
  fixes : Array (String × Lsp.TextEdit)
deriving TypeName

/--
A marker placed in the info tree of a header that indicates that the header tag linter applies to
it.
-/
private meta structure HeaderTagCheck where
deriving TypeName

/--
Builds `hint` with `MessageData.hint` and pushes a `HeaderTagFix` leaf for `stx` with the titles
and edits of the hint's code actions.

The `MessageData` is used to provide a clickable InfoView hint, while the info leaf is used for code
actions that need to trigger on a multi-command range. The hint's code actions are at `ref`, and
its preview shows the text in `preview?` with the edit.
-/
private meta def headerHint (stx ref : Syntax) (hint : MessageData)
    (suggestions : Array (String × String)) (range : Syntax.Range)
    (preview? : Option Syntax.Range := none) : CoreM MessageData := do
  let msg ← MessageData.hint hint (ref? := some ref) <|
    suggestions.map fun (title, text) => {
      suggestion := .string text, toCodeActionTitle? := some fun _ => title,
      span? := some (Syntax.ofRange range), previewSpan? := preview?.map Syntax.ofRange
    }
  let lspRange := (← getFileMap).utf8RangeToLspRange range
  let fixes := suggestions.map fun (title, newText) => (title, { range := lspRange, newText })
  pushInfoLeaf <| .ofCustomInfo { stx, value := .mk { fixes : HeaderTagFix } }
  return msg

private meta def tagNote : MessageData :=
  MessageData.note <|
    "The tag is used as a permanent name for the section or chapter. Writers " ++
    "of this or other documents may use it to link to the section, and it is " ++
    "used to share permanent links. In HTML content, they are used as IDs for " ++
    "headers. Section tags should remain unchanged over time."

/--
Warns about `header` unless `next?` is a metadata block with a `tag` field.

`next?` should be the block after the header, or `none` when the header is the last block in the
document.
-/
private meta def checkHeader (header : HeaderView) (next? : Option Syntax) :
    CommandElabM Unit := do
  let metadata? := next?.bind (MetadataView.of ⟨·⟩)
  -- Abort if the next field is metadata with a tag field. Otherwise continue.
  if metadata?.any (·.fields.any isTagField) then return
  let text ← getFileMap
  let some ⟨start, stop⟩ := header.stx.raw.getRange? | return
  let name := suggestId header.content
  let blockStr := start.extract text.source stop
  let log (hint : MessageData) :=
    logLint linter.verso.manual.headerTags header.stx m!"Missing permalink tag{hint}{tagNote}"
  let tagField := s!"tag := \"{name}\""
  match metadata? with
  | none =>
    let suggestions := #[
      (s!"Add `{tagField}`", s!"{blockStr}\n%%%\n{tagField}\n%%%"),
      ("Add `tag := none`", s!"{blockStr}\n%%%\ntag := none\n%%%")
    ]
    log <| ← runTermElabM fun _ =>
      headerHint header.stx (Syntax.ofRange ⟨start, stop⟩)
        "Add a metadata block with a tag or explicitly indicate that no tag is desired:"
        suggestions ⟨start, stop⟩
  | some metadata =>
    let some ⟨_, stop1⟩ := metadata.opener.getRange? | return
    let some ⟨_, stop2⟩ := metadata.closer.getRange? | return
    let some range := (mkNullNode #[header.stx, metadata.stx]).getRange? | return
    let afterOpener := stop1.extract text.source stop2
    let suggestions := #[
      (s!"Add `{tagField}`", s!"{blockStr}\n%%%\n{tagField}{afterOpener}"),
      ("Add `tag := none`", s!"{blockStr}\n%%%\ntag := none{afterOpener}")
    ]
    log <| ← runTermElabM fun _ =>
      headerHint header.stx (Syntax.ofRange range)
        "Add a tag to the metadata block or explicitly indicate that no tag is desired:"
        suggestions range

/--
Warns about the document's title `title` unless `next?` is a metadata block with a `tag` field.

`next?` should be the document's first block, or `none` when the document has no blocks. `stop` is
the end of the token before the document's blocks. The hints insert the metadata block at the first
block or at `stop`, and the field after the metadata block's opener.
-/
private meta def checkTitle (title : StrLit) (next? : Option Syntax) (stop : String.Pos.Raw) :
    CommandElabM Unit := do
  let metadata? := next?.bind (MetadataView.of ⟨·⟩)
  if metadata?.any (·.fields.any isTagField) then return
  let some content ← try some <$> Verso.Doc.Concrete.stringToInlines title catch _ => pure none
    | return
  let tagField := s!"tag := \"{suggestId (content.map (⟨·⟩))}\""
  let newMetadata :=
    "Add a metadata block with a tag or explicitly indicate that no tag is desired:"
  let (hint, edit, pos, preview?) : MessageData × (String → String) × _ × _ ←
    match metadata?, next? with
    | none, some next =>
      let some pos := next.getPos? | return
      -- The metadata block goes before the indentation of the first block.
      let text ← getFileMap
      let lineStart := text.ofPosition ⟨(text.toPosition pos).line, 0⟩
      let pos := if (lineStart.extract text.source pos).all (· == ' ') then lineStart else pos
      pure (newMetadata, (s!"%%%\n{·}\n%%%\n\n"), pos, none)
    | none, none => pure (newMetadata, (s!"\n\n%%%\n{·}\n%%%"), stop, none)
    | some metadata, _ =>
      let some pos := metadata.opener.getTailPos? | return
      pure ("Add a tag to the metadata block or explicitly indicate that no tag is desired:",
        (s!"\n{·}"), pos, metadata.stx.raw.getRange?)
  let suggestions :=
    #[(s!"Add `{tagField}`", edit tagField), ("Add `tag := none`", edit "tag := none")]
  let hint ← runTermElabM fun _ =>
    headerHint title title hint suggestions ⟨pos, pos⟩ preview?
  logLint linter.verso.manual.headerTags title m!"Missing permalink tag{hint}{tagNote}"

open Verso.Doc.Elab (FinishedPart) in
/--
Appends the headers of `part` and of its subparts to `headers`, except those of parts that end
before `start`.
-/
private meta partial def closedHeaders (start : String.Pos.Raw) (headers : Array Syntax)
    (part : FinishedPart) : Array Syntax :=
  match part with
  | .mk (rangeSyntax := header) (subParts := subParts) (endPos := endPos) .. =>
    if endPos < start then headers else subParts.foldl (closedHeaders start) (headers.push header)
  | .included _ => headers

open Verso.Doc.Elab (PartContext) in
/--
Finds the header or the `#doc` command right before the top-level block at `start`, in the part
state `ctx` after the block's command.

A header or the `#doc` command is right before the block when its syntax, with its trailing
whitespace, ends at `start`. Such a header belongs to an open part or to a part that was closed by
the block's command. Parts that were closed by an earlier command end before `start`.
`headerBefore` skips headers with a parse error.
-/
private meta def headerBefore (ctx : PartContext) (start : String.Pos.Raw) : Option Syntax :=
  let frames := ctx.parents.push ctx.toPartFrame
  let headers := frames.foldl (init := #[]) fun headers frame =>
    frame.priorParts.foldl (closedHeaders start) (headers.push frame.rangeSyntax)
  headers.find? fun stx => !stx.hasMissing && stx.getTrailingTailPos? == some start

/-- Gives the title, the arrow and whether the document is empty for a `#doc` command. -/
private meta def docCommand? : Syntax → Option (StrLit × Syntax × Bool)
  | `(command|#doc ( $_ ) $title:str =>%$arrow $[$empty]?) => some (title, arrow, empty.isSome)
  | _ => none

/--
Warns about headers in documents in the `Manual` genre that aren't followed by a metadata block with
a `tag` field.
-/
public meta def headerTagLinter : Linter where
  run := withSetOptionIn fun stx => do
    if stx.hasMissing then return
    unless (`Verso.Doc.Concrete).isPrefixOf stx.getKind do return
    unless getLinterValue linter.verso.manual.headerTags (← getLinterOptions) do return

    -- The genre of `#docs (...) ...` is its third syntax child, and its blocks are the children of
    -- its `document` node. Top-level blocks of a `#doc` document are parsed as `addBlockCmd` and
    -- `addLastBlockCmd` commands, whose only child is the block. The genre and the part state are
    -- read from Verso's document environment extension.
    let docEnv := Verso.Doc.Concrete.docEnvironmentExt.getState (← getEnv)
    let some (genreStx, docsBlocks?) :=
        if stx[0] matches .atom _ "#docs" then some (stx[2], some stx[8].getArgs)
        else if stx.isOfKind ``Verso.Doc.Concrete.addBlockCmd
            || stx.isOfKind ``Verso.Doc.Concrete.addLastBlockCmd
            || stx.isOfKind ``Verso.Doc.Concrete.replaceDoc then
          some (docEnv.genreSyntax, none)
        else none
      | return
    let genreName ←
      try runTermElabM <| fun _ => realizeGlobalConstNoOverload genreStx
      catch | _ => return
    unless genreName == ``Verso.Genre.Manual do return

    if let some blocks := docsBlocks? then
      if let some stop := stx[7].getTailPos? then checkTitle ⟨stx[5]⟩ blocks[0]? stop
      for h : i in [0:blocks.size] do
        let some header := HeaderView.of ⟨blocks[i]⟩ | continue
        checkHeader header blocks[i + 1]?
      return

    -- The title of `#doc` is checked with the first block's command. The syntax of a `#doc` command
    -- without blocks ends with `emptyDocument`.
    if let some (title, arrow, empty) := docCommand? stx then
      if !empty then
        pushInfoLeaf <| .ofCustomInfo { stx := title, value := .mk ({} : HeaderTagCheck) }
      else if let some stop := arrow.getTailPos? then checkTitle title none stop
      return

    let block := stx[0]
    if let some before := block.getPos?.bind (headerBefore docEnv.partState.partContext) then
      if let some header := HeaderView.of ⟨before⟩ then checkHeader header (some block)
      else if let some (title, arrow, _) := docCommand? before then
        if let some stop := arrow.getTailPos? then checkTitle title (some block) stop
    let some header := HeaderView.of ⟨block⟩ | return
    -- In an `addBlockCmd`, the block's header is checked with the next command.
    if stx.isOfKind ``Verso.Doc.Concrete.addBlockCmd then
      pushInfoLeaf <| .ofCustomInfo { stx := header.stx, value := .mk ({} : HeaderTagCheck) }
    else checkHeader header none

meta initialize addLinter headerTagLinter

open Lean Server Lsp RequestM in
/--
Offers the header tag linter's quick fixes for the headers in the requested lines of a `#doc`
document.
-/
@[code_action_provider]
public meta def headerTagActions : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let (finished, _, _) ← (doc.cmdSnaps.getFinishedPrefix : BaseIO _)
  let some next := (finished.dropWhile (·.endPos < snap.endPos))[1]? | return #[]
  -- The parts of the info trees that are filled in later, such as the linters', are tasks.
  for infoState in [snap.cmdState.infoState, next.cmdState.infoState] do
    for (_, part) in infoState.lazyAssignment do
      unless ← IO.hasFinished part do return #[]
  let checksHeader := snap.infoTree.foldInfo (init := false) fun _ info found =>
    found || match info with
      | .ofCustomInfo { value, .. } => (value.get? HeaderTagCheck).isSome
      | _ => false
  unless checksHeader do return #[]
  let text := doc.meta.text
  return next.infoTree.foldInfo (init := #[]) fun _ info actions => Id.run do
    let .ofCustomInfo { stx, value } := info | actions
    let some { fixes } := value.get? HeaderTagFix | actions
    let some range := stx.getRange? | actions
    let lspRange := text.utf8RangeToLspRange range
    unless lspRange.start.line ≤ params.range.end.line do return actions
    unless params.range.start.line ≤ lspRange.end.line do return actions
    actions ++ fixes.map fun (title, edit) => {
      eager.title := title
      eager.kind? := "quickfix"
      eager.edit? := some <| .ofTextEdit doc.versionedIdentifier edit
    }
