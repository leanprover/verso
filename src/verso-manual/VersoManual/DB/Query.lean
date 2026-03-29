/-
Copyright (c) 2025-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.DocString.Extension

import DocGen4.DB
import DocGen4.DB.VersoDocString
public import DocGen4.Process.Base
import SQLite
public meta import SQLite

import VersoManual.DB.Convert
import VersoManual.Docstring
public import VersoManual.Docstring.Basic
public import VersoManual.Docstring.DeclInfo
public import VersoManual.Docstring.DocName
public section

/-! # DB Querying and Type Reconstruction

High-level API for querying the doc-gen4 database and converting the results into Verso's
documentation types (`DeclType`, `Signature`, `DocName`, `FieldInfo`, `ParentInfo`).
-/

namespace Verso.Genre.Manual.DB

open Lean
open DocGen4 (FormatCode)
open DocGen4.Process (DocInfo NameInfo)
open DocGen4.DB (ReadDB openForReading builtinDocstringValues)
open SubVerso.Highlighting (Highlighted Token)
open Verso.Genre.Manual (Signature)
open Verso.Genre.Manual.Block.Docstring (DeclType DocName FieldInfo ParentInfo Visibility)

/-- Extract a markdown docstring from a doc-gen4 `NameInfo.doc` field. -/
def docStringOfDoc? (doc : Option (String ⊕ VersoDocString)) : Option String :=
  doc.bind fun
    | .inl md => some md
    | .inr v => some (DocGen4.Process.versoDocToMarkdown v)

/-- Build a `DocName` from a doc-gen4 `NameInfo`.
When `showNamespace` is `true` (the default), the full qualified name is displayed.
When `false`, only the last component is shown (used for inductive constructors).
The `sigOverride` parameter allows providing a custom hover signature string (e.g., with named
parameters for structure constructors). -/
def docNameOfNameInfo (ni : NameInfo)
    (constInfo : Lean.NameMap (String × Option String) := {})
    (showNamespace : Bool := true)
    (sigOverride : Option String := none) : DocName :=
  let docstring? := docStringOfDoc? ni.doc
  let sigStr := sigOverride.getD s!"{ni.name} : {formatCodeText ni.type}"
  let displayName := if showNamespace then ni.name.toString else ni.name.getString!
  let nameHl := Highlighted.token ⟨.const ni.name sigStr docstring? false none, displayName⟩
  { name := ni.name
    hlName := nameHl
    signature := .seq #[nameHl, .text " : ", formatCodeToHighlighted constInfo ni.type]
    docstring? }

/-- Build a `Signature` from a doc-gen4 `Info`, including the declaration name.
Combines all `FormatCode` pieces (name, args, type) into a single `Format` document,
then renders at width 72 (wide) and 42 (narrow) for proper line-breaking. -/
def signatureOfInfo (info : DocGen4.Process.Info)
    (constInfo : Lean.NameMap (String × Option String) := {})
    (levelParams : List Name := []) : Signature :=
  let sigFc := buildSignatureFormatCode info.name levelParams (info.args.map (·.binder)) info.type
  { wide := formatCodeToHighlighted constInfo sigFc 72
    narrow := formatCodeToHighlighted constInfo sigFc 42 }

/--
Extract the parent structure name from a `FormatCode` type by rendering and finding the first
`.const` tag. Falls back to `.anonymous` if no constant reference is found.
-/
private partial def parentNameOfFormatCode (fc : FormatCode) : Name :=
  go fc.render
where
  go : DocGen4.RenderedCode → Name
    | .text _ => .anonymous
    | .tag (.const name) _ => name
    | .tag _ inner => go inner
    | .append xs => xs.foldl (init := .anonymous) fun acc x =>
      if acc != .anonymous then acc else go x

/-- Convert doc-gen4's `StructureParentInfo` array to Verso's `ParentInfo` array. -/
def convertParents (parents : Array DocGen4.Process.StructureParentInfo)
    (constInfo : Lean.NameMap (String × Option String) := {}) : Array ParentInfo :=
  parents.mapIdx fun i p => {
    projFn := p.projFn
    name := parentNameOfFormatCode p.type
    parent := formatCodeToHighlighted constInfo p.type
    index := i
  }

/--
Convert a doc-gen4 `Process.FieldInfo` to Verso's `Block.Docstring.FieldInfo`.

Some fields are simplified because the database doesn't carry the full information:
- `subobject?` is always `none`
- `binderInfo` is always `BinderInfo.default`
- `autoParam` is always `false`
- `visibility` is always `.public`

For inherited fields (`isDirect = false`), the `fieldFrom` list is populated by matching the
field's projection function name prefix against parent structure names. This enables the
"Inherited from" display and checkbox-based parent field filtering in the HTML output.
-/
def convertFieldInfo (field : DocGen4.Process.FieldInfo)
    (parents : Array ParentInfo)
    (constInfo : Lean.NameMap (String × Option String) := {}) : FieldInfo :=
  let fieldNameStr := field.name.getString!
  let docString? := docStringOfDoc? field.doc
  let sigStr := s!"{field.name} : {formatCodeText field.type}"
  let fieldName :=
    Highlighted.token ⟨.const field.name sigStr docString? true none, fieldNameStr⟩
  let fieldFrom : List DocName :=
    if field.isDirect then []
    else
      -- For inherited fields, determine which parent owns this field by matching
      -- the field's projection function name prefix against parent names.
      -- E.g., field `Verso.Genre.Manual.HtmlAssets.extraCss` → parent `HtmlAssets`
      let fieldPrefix := field.name.getPrefix
      match parents.find? (·.name == fieldPrefix) with
      | some parent =>
        let parentDocName : DocName := {
          name := parent.name
          hlName := .token ⟨.const parent.name "" none false none, parent.name.toString⟩
          signature := parent.parent
          docstring? := none
        }
        [parentDocName]
      | none => []
  {
    fieldName
    fieldFrom
    type := formatCodeToHighlighted constInfo field.type
    projFn := field.name
    subobject? := none
    binderInfo := .default
    autoParam := false
    docString?
    visibility := .public
  }

/-- Build a pretty constructor hover signature from a structure's fields.
Groups consecutive fields with the same type, e.g. `(shortTitle shortContextTitle : Option String)`.
Returns a string like `Struct.mk (field1 : Type1) (field2 field3 : Type2) : Struct`.

NOTE: This is a workaround because doc-gen4 currently stores the structure constructor as `NameInfo`
(without args). Once doc-gen4 is changed to store the constructor as `Info` (with pretty-printed
binder args), this function should be replaced by directly using the constructor's `args` field. -/
private def prettyCtorSig (ctorName : Name) (structName : Name)
    (fields : Array DocGen4.Process.FieldInfo) : String :=
  let resultType := structName.toString
  if fields.isEmpty then
    s!"{ctorName} : {resultType}"
  else Id.run do
    -- Group consecutive fields with the same rendered type
    let mut groups : Array (Array String × String) := #[]
    for field in fields do
      let typeStr := formatCodeText field.type
      let fieldName := field.name.getString!
      match groups.back? with
      | some (names, t) =>
        if t == typeStr then
          groups := groups.pop.push (names.push fieldName, t)
        else
          groups := groups.push (#[fieldName], typeStr)
      | none =>
        groups := groups.push (#[fieldName], typeStr)
    let params := groups.map fun (names, typeStr) =>
      let nameStr := " ".intercalate names.toList
      s!"({nameStr} : {typeStr})"
    let paramStr := "\n  ".intercalate params.toList
    s!"{ctorName} {paramStr} : {resultType}"

private def buildStructureDeclType (isClass : Bool) (info : DocGen4.Process.StructureInfo)
    (hideFields : Bool) (hideStructureConstructor : Bool)
    (constInfo : Lean.NameMap (String × Option String) := {}) : DeclType :=
  let ctorSig := prettyCtorSig info.ctor.name info.toInfo.name info.fieldInfo
  let ctor? :=
    if hideStructureConstructor then none
    else some (docNameOfNameInfo info.ctor constInfo (sigOverride := some ctorSig))
  let fieldNames :=
    if hideFields then #[]
    else info.fieldInfo.map (·.name)
  let parents := convertParents info.parents constInfo
  let fieldInfo :=
    if hideFields then #[]
    else info.fieldInfo.map (convertFieldInfo · parents constInfo)
  .structure isClass ctor? fieldNames fieldInfo parents #[]

/--
Reconstruct a `DeclType` from a doc-gen4 `DocInfo`.

For structures and classes, converts constructor, field, and parent information.
For inductives, converts constructor `DocName` values.
For definitions, opaques, axioms: extracts safety information.
-/
def buildDeclType (docInfo : DocInfo) (hideFields : Bool) (hideStructureConstructor : Bool)
    (constInfo : Lean.NameMap (String × Option String) := {}) : DeclType :=
  match docInfo with
  | .axiomInfo info =>
    .axiom (if info.isUnsafe then .unsafe else .safe)
  | .theoremInfo _ =>
    .theorem
  | .opaqueInfo info =>
    .opaque info.definitionSafety
  | .definitionInfo info =>
    .def (if info.isUnsafe then .unsafe else .safe)
  | .instanceInfo info =>
    .def (if info.isUnsafe then .unsafe else .safe)
  | .inductiveInfo info =>
    let ctors := info.ctors.toArray.map fun ctor =>
      docNameOfNameInfo ctor.toNameInfo constInfo (showNamespace := false)
    .inductive ctors 0 false
  | .structureInfo info =>
    buildStructureDeclType false info hideFields hideStructureConstructor constInfo
  | .classInfo info =>
    buildStructureDeclType true info hideFields hideStructureConstructor constInfo
  | .classInductiveInfo info =>
    let ctors := info.ctors.toArray.map fun ctor =>
      docNameOfNameInfo ctor.toNameInfo constInfo (showNamespace := false)
    .inductive ctors 0 false
  | .ctorInfo _info =>
    .other

/-- Build a `NameMap` of hover data for constants directly contained in a `DocInfo`
(the declaration itself, its fields, constructors, etc.). -/
private def localConstInfoMap (docInfo : DocInfo) : Lean.NameMap (String × Option String) :=
  let info := docInfo.toInfo
  let sig := s!"{info.name} : {formatCodeText info.type}"
  let m : Lean.NameMap (String × Option String) :=
    ({} : Lean.NameMap _).insert info.name (sig, docStringOfDoc? info.doc)
  match docInfo with
  | .inductiveInfo ind =>
    ind.ctors.foldl (init := m) fun m c =>
      m.insert c.name (s!"{c.name} : {formatCodeText c.type}", docStringOfDoc? c.doc)
  | .structureInfo s =>
    let ctorSig := prettyCtorSig s.ctor.name info.name s.fieldInfo
    let m := m.insert s.ctor.name (ctorSig, docStringOfDoc? s.ctor.doc)
    s.fieldInfo.foldl (init := m) fun m f =>
      m.insert f.name (s!"{f.name} : {formatCodeText f.type}", docStringOfDoc? f.doc)
  | .classInfo s =>
    let ctorSig := prettyCtorSig s.ctor.name info.name s.fieldInfo
    let m := m.insert s.ctor.name (ctorSig, docStringOfDoc? s.ctor.doc)
    s.fieldInfo.foldl (init := m) fun m f =>
      m.insert f.name (s!"{f.name} : {formatCodeText f.type}", docStringOfDoc? f.doc)
  | _ => m

/-- Collect all `FormatCode` values from a `DocInfo` (type, args, fields, constructors, parents). -/
private def allFormatCodes (docInfo : DocInfo) : Array FormatCode :=
  let info := docInfo.toInfo
  let codes := #[info.type] ++ info.args.map (·.binder)
  match docInfo with
  | .inductiveInfo ind =>
    codes ++ ind.ctors.toArray.map (·.type)
  | .structureInfo s =>
    codes ++ #[s.ctor.type] ++ s.fieldInfo.map (·.type) ++ s.parents.map (·.type)
  | .classInfo s =>
    codes ++ #[s.ctor.type] ++ s.fieldInfo.map (·.type) ++ s.parents.map (·.type)
  | _ => codes

/-- Collect all constant names referenced in any `FormatCode` of a `DocInfo`. -/
private def referencedConstNames (docInfo : DocInfo) : Lean.NameSet :=
  (allFormatCodes docInfo).foldl (init := {}) fun acc fc =>
    formatCodeConstNames acc fc

/--
Query the database for type and docstring hover data for a set of constant names.
Returns a `NameMap` of `(typeString, docstring?)` suitable for use as `constInfo`.
-/
private def queryConstHoverData (dbPath : System.FilePath) (names : Lean.NameSet) :
    IO (Lean.NameMap (String × Option String)) := do
  let sqlite ← SQLite.openWith dbPath .readonly
  let typeStmt ← sqlite.prepare
    "SELECT type, module_name, position FROM name_info WHERE name = ?"
  let mdDocStmt ← sqlite.prepare
    "SELECT text FROM declaration_markdown_docstrings WHERE module_name = ? AND position = ?"
  let versoDocStmt ← sqlite.prepare
    "SELECT content FROM declaration_verso_docstrings WHERE module_name = ? AND position = ?"
  let mut result : Lean.NameMap (String × Option String) := {}
  have : SQLite.Blob.FromBinary VersoDocString := DocGen4.DB.versoDocStringFromBinary builtinDocstringValues
  for name in names do
    typeStmt.bind 1 name.toString
    if ← typeStmt.step then
      let typeBlob ← typeStmt.columnBlob 0
      let moduleName ← typeStmt.columnText 1
      let position ← typeStmt.columnInt64 2
      -- Look up docstring: try markdown first, then verso
      let mut doc? : Option String := none
      mdDocStmt.bind 1 moduleName
      mdDocStmt.bind 2 position
      if ← mdDocStmt.step then
        doc? := some (← mdDocStmt.columnText 0)
      mdDocStmt.reset
      mdDocStmt.clearBindings
      if doc?.isNone then
        versoDocStmt.bind 1 moduleName
        versoDocStmt.bind 2 position
        if ← versoDocStmt.step then
          let blob ← versoDocStmt.columnBlob 0
          match SQLite.Blob.fromBinary (α := VersoDocString) blob with
          | Except.ok vds =>
            doc? := some (DocGen4.Process.versoDocToMarkdown vds)
          | Except.error _ => pure ()
        versoDocStmt.reset
        versoDocStmt.clearBindings
      match SQLite.Blob.fromBinary (α := FormatCode) typeBlob with
      | Except.ok fc =>
        let sig := s!"{name} : {formatCodeText fc}"
        result := result.insert name (sig, doc?)
      | Except.error _ =>
        pure ()
    typeStmt.reset
    typeStmt.clearBindings
  return result

/--
Build a complete `NameMap` of hover data for a `DocInfo`, including both locally-defined names
(the declaration, its fields/constructors) and externally-referenced constants (looked up in the DB).
-/
def constInfoMap (dbPath : System.FilePath) (docInfo : DocInfo) :
    IO (Lean.NameMap (String × Option String)) := do
  let local_ := localConstInfoMap docInfo
  let referenced := referencedConstNames docInfo
  -- Only query the DB for names not already in the local map
  let mut missing : Lean.NameSet := {}
  for name in referenced do
    unless local_.contains name do
      missing := missing.insert name
  if missing.isEmpty then return local_
  let external ← queryConstHoverData dbPath missing
  -- Merge: local takes precedence
  return external.foldl (init := local_) fun m name val =>
    if m.contains name then m else m.insert name val

/--
Open the doc-gen4 database at the given path and look up a declaration by name.

Returns `none` if the name is not found. Throws on IO errors (missing file, corrupt DB).
-/
def lookupDocInfo (dbPath : System.FilePath) (name : Name) :
    IO (Option DocInfo) := do
  let db ← openForReading dbPath builtinDocstringValues
  let moduleNames ← db.getModuleNames
  let name2ModIdx ← db.buildName2ModIdx moduleNames
  let some modIdx := name2ModIdx[name]?
    | return none
  let modName := moduleNames[modIdx.toNat]!
  let mod ← db.loadModule modName
  return mod.members.findSome? fun
    | .docInfo di => if di.toInfo.name == name then some di else none
    | _ => none

/-- Result of looking up a tactic in the database. -/
structure TacticLookupResult where
  internalName : Name
  userName : String
  docString : Option String
  tags : Array Name
deriving Inhabited

private def readTacticRow (_sqlite : SQLite) (tacStmt tagStmt : SQLite.Stmt) :
    IO TacticLookupResult := do
  let internalName := (← tacStmt.columnText 0).toName
  let userName ← tacStmt.columnText 1
  let docStr ← tacStmt.columnText 2
  let moduleName ← tacStmt.columnText 3
  -- Load tags
  tagStmt.reset
  tagStmt.clearBindings
  tagStmt.bind 1 moduleName
  tagStmt.bind 2 internalName.toString
  let mut tags : Array Name := #[]
  while (← tagStmt.step) do
    tags := tags.push (← tagStmt.columnText 0).toName
  return {
    internalName
    userName
    docString := if docStr.isEmpty then none else some docStr
    tags
  }

/-- Look up tactics by internal name. -/
def lookupTacticByName (dbPath : System.FilePath) (name : Name) :
    IO (Array TacticLookupResult) := do
  let sqlite ← SQLite.openWith dbPath .readonly
  let tacStmt ← sqlite.prepare
    "SELECT t.internal_name, t.user_name, t.doc_string, t.module_name FROM tactics t WHERE t.internal_name = ?"
  let tagStmt ← sqlite.prepare
    "SELECT tag FROM tactic_tags WHERE module_name = ? AND internal_name = ?"
  tacStmt.bind 1 name.toString
  let mut results := #[]
  while (← tacStmt.step) do
    results := results.push (← readTacticRow sqlite tacStmt tagStmt)
  return results

/-- Look up tactics by user-facing name. -/
def lookupTacticByUserName (dbPath : System.FilePath) (userName : String) :
    IO (Array TacticLookupResult) := do
  let sqlite ← SQLite.openWith dbPath .readonly
  let tacStmt ← sqlite.prepare
    "SELECT t.internal_name, t.user_name, t.doc_string, t.module_name FROM tactics t WHERE t.user_name = ?"
  let tagStmt ← sqlite.prepare
    "SELECT tag FROM tactic_tags WHERE module_name = ? AND internal_name = ?"
  tacStmt.bind 1 userName
  let mut results := #[]
  while (← tacStmt.step) do
    results := results.push (← readTacticRow sqlite tacStmt tagStmt)
  return results

/-- Load all conv tactics from the `conv_tactics` table. -/
def lookupConvTactics (dbPath : System.FilePath) :
    IO (Array TacticLookupResult) := do
  let sqlite ← SQLite.openWith dbPath .readonly
  let stmt ← sqlite.prepare
    "SELECT internal_name, user_name, doc_string, module_name FROM conv_tactics"
  let mut results := #[]
  while (← stmt.step) do
    let internalName := (← stmt.columnText 0).toName
    let userName ← stmt.columnText 1
    let docStr ← stmt.columnText 2
    results := results.push {
      internalName
      userName
      docString := if docStr.isEmpty then none else some docStr
      tags := #[]
    }
  return results

end Verso.Genre.Manual.DB
