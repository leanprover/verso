/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Linter.Basic
import Lean.Meta.Hint
import Verso.Doc.Concrete
import Verso.Parser
import MultiVerso.Slug

set_option linter.missingDocs true

open Lean Linter Elab Command

/-- Warns when headers don't have tags -/
register_option linter.verso.manual.headerTags : Bool := {
  defValue := false
  descr := "if true, warn when headers don't have tags"
}

/--
Lints for tagless headers.
-/
partial def headerTagLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless (`Verso.Doc.Concrete).isPrefixOf stx.getKind do return
    unless getLinterValue linter.verso.manual.headerTags (← getLinterOptions) do return

    let text ← getFileMap

    discard <| stx.replaceM fun cmd => do
      if cmd.isOfKind ``Verso.Doc.Concrete.addBlockCmd || cmd.isOfKind ``Verso.Doc.Concrete.addLastBlockCmd then
        let block := cmd[0]
        let genre := cmd[1]
        let genreName ←
          try runTermElabM <| fun _ => realizeGlobalConstNoOverload genre
          catch | _ => return none
        unless genreName == `Verso.Genre.Manual do return none
        if let `(block|header($n){$inls*}) := block then
          let some ⟨start, stop⟩ := block.getRange?
            | return none
          let mut nextLine : String.Iterator := {s := text.source, i := stop}
          while h : nextLine.hasNext do
            if (nextLine.curr' h).isWhitespace then nextLine := nextLine.next' h
            else break
          -- Attempt to parse the next command as a metadata block.
          let ictx := {
            input := text.source,
            fileName := ← getFileName,
            fileMap := text
          }
          let pmctx := {
            env := ← getEnv,
            options := ← getOptions
          }
          let toks := Parser.getTokenTable (← getEnv)
          let s := { cache := { tokenCache := {}, parserCache := {} }, pos := nextLine.i }
          let s := Verso.Parser.metadataBlock.run ictx pmctx toks s
          let tagNote :=
            MessageData.note <|
              "The tag is used as a permanent name for the section or chapter. Writers "++
              "of this or other documents may use it to link to the section, and it is " ++
              "used to share permanent links. In HTML content, they are used as IDs for " ++
              "headers. Section tags should remain unchanged over time."
          if s.hasError || !s.recoveredErrors.isEmpty then
            -- Next block is not metadata, so suggest inserting one
            let name := suggestId inls
            let blockStr := text.source.extract start stop
            let suggestion := s!"{blockStr}\n%%%\ntag := \"{name}\"\n%%%"
              let h ← runTermElabM fun _ => MessageData.hint "Add a metadata block with a tag" #[suggestion] (ref? := some block)
              logLint linter.verso.manual.headerTags block m!"Missing permalink tag{h}{tagNote}"
            return none
          let nextStx ←
              if s.stxStack.size = 1 then
                pure (s.stxStack.get! 0)
              else return none
          if let`(block|%%%%$tk $fieldOrAbbrev* %%%%$tk2) := nextStx then
            let metadataStx ← `(term| { $fieldOrAbbrev* })
            let isMissing ← runTermElabM fun _ => do
              let type := .const `Verso.Genre.Manual.PartMetadata []
              let metadataTerm ← Term.elabTerm metadataStx (some type)
              let tagExpr ← Meta.whnf (← Meta.mkProjection metadataTerm `tag)
              match_expr tagExpr with
              | Option.none _ => pure true
              | _ => pure false
            if isMissing then
              let name := suggestId inls
              -- Find the beginning of the line after the token
              let some ⟨start, stop⟩ := tk.getRange?
                | return none
              let some ⟨start2, stop2⟩ := tk2.getRange?
                | return none
              let suggestion := s!"%%%\ntag := \"{name}\"" ++ text.source.extract stop stop2

              let h ← runTermElabM fun _ => MessageData.hint "Add a tag to the metadata block" #[suggestion] (ref? := some nextStx)
              logLint linter.verso.manual.headerTags block m!"Missing permalink tag{h}{tagNote}"
            pure ()
          return none
      pure none

where
  suggestId (name : TSyntaxArray `inline) : String :=
    suggestId' name |>.sluggify |>.toString

  suggestId' (name : TSyntaxArray `inline) : String := Id.run do
    let mut strTitle := ""
    for inl in name do
      match inl with
      | `(inline|$s:str) | `(inline|code($s)) => strTitle := strTitle ++ s.getString.toLower
      | `(inline|_[$i*]) | `(inline|*[$i*]) | `(inline|link[$i*]$_) | `(inline|role{$_ $_*}[$i*]) =>
        strTitle := strTitle ++ suggestId' i
      | _ => pure ()
    return strTitle

initialize addLinter headerTagLinter
