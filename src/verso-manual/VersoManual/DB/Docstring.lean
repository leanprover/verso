/-
Copyright (c) 2025-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.CoreM
public import Lean.Data.Options
public import Lean.Environment

import VersoManual.DB.Query
public meta import VersoManual.DB.Query
public import VersoManual.Docstring
import VersoManual.Markdown

import Verso.Doc.Elab.Block
import Verso.Doc.Elab.Monad
public import Verso.Doc.ArgParse
import Verso.Doc.PointOfInterest

import MD4Lean
public section

/-! # DB-Backed Docstring Command

A `{dbDocstring}` block command that reads documentation data from a doc-gen4 SQLite database rather
than from the Lean `Environment`. Produces the same `Block.docstring` output as the existing
environment-based `{docstring}` command, so the HTML/TeX rendering pipeline works unchanged.
-/

open Lean
open Verso.Doc.Elab.PartElabM
open Verso.Code
open Verso.ArgParse
open SubVerso.Highlighting

namespace Verso.Genre.Manual.DB

/-- Locate the doc-gen4 database path relative to the current working directory. -/
private meta def getDbPath : IO System.FilePath := do
  let cwd ← IO.currentDir
  return cwd / ".lake" / "build" / "api-docs.db"


public structure DBDocstringConfig where
  name : Ident × Name
  allowMissing : Bool
  hideFields : Bool := false
  hideStructureConstructor : Bool := false
  label : Option String := none

section
variable {m} [Monad m] [MonadOptions m] [MonadEnv m] [MonadLiftT CoreM m] [MonadError m]
  [MonadLog m] [AddMessageContext m] [Lean.Elab.MonadInfoTree m] [MonadLiftT MetaM m]

public meta instance : FromArgs DBDocstringConfig m where
  fromArgs :=
    DBDocstringConfig.mk <$>
      .positional `name .documentableName <*>
      .flagM `allowMissing (verso.docstring.allowMissing.get <$> getOptions)
        "Warn instead of error on missing docstrings (defaults to value of option `verso.docstring.allowMissing)" <*>
      .flag `hideFields false <*>
      .flag `hideStructureConstructor false <*>
      .named `label .string true

end

private meta def getExtras (name : Name) (declType : Block.Docstring.DeclType) :
    Verso.Doc.Elab.DocElabM (Array Term) :=
  match declType with
  | .structure isClass constructor? _ fieldInfo parents _ => do
    let ctorRow : Option Term ← constructor?.mapM fun constructor => do
      let header := if isClass then "Instance Constructor" else "Constructor"
      let sigDesc : Array Term ←
        if let some docs := constructor.docstring? then
          let some mdAst := MD4Lean.parse docs
            | throwError "Failed to parse docstring as Markdown"
          mdAst.blocks.mapM (Markdown.blockFromMarkdown · (handleHeaders := Markdown.strongEmphHeaders))
        else pure (#[] : Array Term)
      let sig ← `(Verso.Doc.Block.other (Verso.Genre.Manual.Block.internalSignature $(quote constructor.hlName) none) #[$sigDesc,*])
      ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$sig])

    let parentsRow : Option Term ← do
      if parents.isEmpty then pure none
      else
        let header := "Extends"
        let inh ← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.inheritance $(quote name) $(quote parents)) #[])
        some <$> ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$inh])

    let fieldsRow : Option Term ← do
      let header := if isClass then "Methods" else "Fields"
      let fieldInfo := fieldInfo.filter (·.subobject?.isNone)
      let fieldSigs : Array Term ← fieldInfo.mapM fun i => do
        let inheritedFrom : Option Nat :=
          i.fieldFrom.head?.bind (fun n => parents.findIdx? (·.name == n.name))
        let sigDesc : Array Term ←
          if let some docs := i.docString? then
            let some mdAst := MD4Lean.parse docs
              | throwError "Failed to parse docstring as Markdown"
            mdAst.blocks.mapM (Markdown.blockFromMarkdown · (handleHeaders := Markdown.strongEmphHeaders))
          else
            pure (#[] : Array Term)
        ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.fieldSignature $(quote i.visibility) $(quote i.fieldName) $(quote i.type) $(quote inheritedFrom) $(quote <| parents.map (·.parent))) #[$sigDesc,*])
      if fieldSigs.isEmpty then pure none
      else some <$> ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$fieldSigs,*])

    pure <| ctorRow.toArray ++ parentsRow.toArray ++ fieldsRow.toArray
  | .inductive ctors .. => do
    let ctorSigs : Array Term ←
      ctors.mapM fun c => do
        let sigDesc ←
          if let some docs := c.docstring? then
            let some mdAst := MD4Lean.parse docs
              | throwError "Failed to parse docstring as Markdown"
            mdAst.blocks.mapM (Markdown.blockFromMarkdown · (handleHeaders := Markdown.strongEmphHeaders))
          else pure (#[] : Array Term)
        ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.constructorSignature $(quote c.signature)) #[$sigDesc,*])
    pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection "Constructors") #[$ctorSigs,*])]
  | _ => pure #[]

open Verso.Genre.Manual.Markdown in
open Verso.Doc.Elab in
@[block_command]
public meta def dbDocstring : BlockCommandOf DBDocstringConfig
  | ⟨(x, name), allowMissing, hideFields, hideCtor, customLabel⟩ => do
    let opts : Options → Options :=
      (verso.docstring.allowMissing.set · allowMissing)
    withOptions opts do
      Doc.PointOfInterest.save (← getRef) name.toString (detail? := some "Documentation")

      -- Locate and open the database
      let dbPath ← getDbPath
      unless ← dbPath.pathExists do
        throwErrorAt x m!"Documentation database not found at '{dbPath}'. Run `lake build` to generate it."

      -- Look up the declaration
      let some docInfo ← lookupDocInfo dbPath name
        | throwErrorAt x m!"'{name}' not found in the documentation database."

      let info := docInfo.toInfo
      let ci ← constInfoMap dbPath docInfo

      -- Extract and parse docstring
      let blockStx ← do
        match docStringOfDoc? info.doc with
        | none => pure #[]
        | some docs =>
          let some ast := MD4Lean.parse docs
            | throwErrorAt x "Failed to parse docstring as Markdown"
          ast.blocks.mapM (blockFromMarkdown · (handleHeaders := strongEmphHeaders))

      -- Check deprecation
      let isDeprecated := info.attrs.any (·.startsWith "deprecated")
      if !(← Docstring.getAllowDeprecated) && isDeprecated then
        Lean.logError m!"'{name}' is deprecated.\n\nSet option 'verso.docstring.allowDeprecated' to 'true' to allow documentation for deprecated names."

      -- Build DeclType from DocInfo
      let declType := buildDeclType docInfo (hideFields := hideFields) (hideStructureConstructor := hideCtor) ci

      -- Build Signature (includes declaration name and universe parameters)
      let levelParams := match (← getEnv).find? name with
        | some ci => ci.levelParams
        | none => []
      let signature := signatureOfInfo info ci (levelParams := levelParams)

      -- Build extras for structures and inductives
      let extras ← getExtras name declType

      ``(Verso.Doc.Block.other
          (Verso.Genre.Manual.Block.docstring $(quote name) $(quote declType) $(quote signature) $(quote customLabel) $(quote (#[] : Array Name)))
          #[$(blockStx ++ extras),*])

open Verso.Genre.Manual.Markdown in
open Verso.Doc.Elab in
open Lean Elab Tactic Doc in
@[directive]
public meta def dbTactic : DirectiveExpanderOf TacticDocsOptions
  | ⟨name, «show», replace, allowMissing⟩, more => do
    let opts : Options → Options :=
      (verso.docstring.allowMissing.set · allowMissing)
    withOptions opts do
      -- Locate and open the database
      let dbPath ← getDbPath
      let blame : Syntax := name.elim TSyntax.raw TSyntax.raw
      unless ← dbPath.pathExists do
        throwErrorAt blame m!"Documentation database not found at '{dbPath}'. Run `lake build` to generate it."

      -- Look up the tactic
      let results : Array TacticLookupResult ← match name with
        | .inr ident => lookupTacticByName dbPath ident.getId
        | .inl str => lookupTacticByUserName dbPath str.getString
      if results.isEmpty then
        let n : MessageData := match name with
          | .inl x => x
          | .inr x => x
        throwErrorAt blame m!"Tactic not found in the documentation database: {n}"

      -- Prefer overloads with docstrings
      let withDocs := results.filter (·.docString.isSome)
      let result :=
        if h : withDocs.size > 0 then withDocs[0]
        else results[0]!
      if results.size > 1 then
        logWarningAt blame s!"Found {results.size} overloads: {results.map (toString ·.internalName) |>.toList |> ", ".intercalate}"

      -- Convert to TacticDoc
      let tacticDoc : TacticDoc := {
        internalName := result.internalName
        userName := result.userName
        tags := result.tags.foldl (init := {}) NameSet.insert
        docString := result.docString
        extensionDocs := #[]
      }

      Doc.PointOfInterest.save (← getRef) tacticDoc.userName
      if tacticDoc.userName == tacticDoc.internalName.toString && «show».isNone then
        throwError "No `show` option provided, but the tactic has no user-facing token name"

      let contents ←
        if replace then pure #[]
        else
          let some str := tacticDoc.docString
            | throwError m!"Tactic {tacticDoc.userName} ({tacticDoc.internalName}) has no docstring"
          let some mdAst := MD4Lean.parse str
            | throwError m!"Failed to parse docstring as Markdown. Docstring contents:\n{repr str}"
          mdAst.blocks.mapM (blockFromMarkdown · (handleHeaders := strongEmphHeaders))
      let userContents ← more.mapM elabBlock
      ``(Verso.Doc.Block.other (Block.tactic $(quote tacticDoc) $(quote «show»)) #[$(contents ++ userContents),*])

open Verso.Genre.Manual.Markdown in
open Verso.Doc.Elab in
@[directive]
public meta def dbConv : DirectiveExpanderOf TacticDocsOptions
  | ⟨name, «show», _replace, allowMissing⟩, more => do
    let opts : Options → Options :=
      (verso.docstring.allowMissing.set · allowMissing)
    withOptions opts do
      let dbPath ← getDbPath
      let blame : Syntax := name.elim TSyntax.raw TSyntax.raw
      unless ← dbPath.pathExists do
        throwErrorAt blame m!"Documentation database not found at '{dbPath}'. Run `lake build` to generate it."

      -- Load all conv tactics and match by suffix
      let convTactics ← lookupConvTactics dbPath
      let nameToMatch : Name := match name with
        | .inr ident => ident.getId
        | .inl str => str.getString.toName
      let some result := convTactics.find? (fun t => nameToMatch.isSuffixOf t.internalName)
        | throwErrorAt blame m!"Conv tactic not found in the documentation database: {nameToMatch}"

      Doc.PointOfInterest.save (← getRef) result.internalName.toString
      let contents ← if let some d := result.docString then
          let some mdAst := MD4Lean.parse d
            | throwError "Failed to parse docstring as Markdown"
          mdAst.blocks.mapM (blockFromMarkdown · (handleHeaders := strongEmphHeaders))
        else pure #[]
      let some toShow := «show»
        | throwError "An explicit 'show' is mandatory for conv docs (for now)"
      let userContents ← more.mapM elabBlock
      ``(Verso.Doc.Block.other (Block.conv $(quote result.internalName) $(quote toShow) $(quote result.docString)) #[$(contents ++ userContents),*])

end Verso.Genre.Manual.DB
