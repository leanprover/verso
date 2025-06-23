/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Std.Data.HashSet
import Std.Data.TreeSet
import Verso.Doc
import Verso.Doc.Html
import Verso.Doc.TeX
import MultiVerso
import MultiVerso.Slug
import VersoManual.LicenseInfo
import Verso.Output.Html
import Verso.Output.TeX
import Verso.BEq

open Lean (Name Json NameMap ToJson FromJson)
open Std (HashSet HashMap TreeSet)
open Verso.Doc
open Verso.Multi
open Verso.Output
open Verso.BEq

namespace Verso.Genre.Manual

export Verso.Multi (InternalId)

inductive Output where
  | /-- LaTeX -/
    tex
  | /-- HTML - one page per part at the given depth -/
    html (depth : Nat)
deriving DecidableEq, BEq, Hashable


/--
Tags are used to refer to parts through tables of contents, cross-references, and the like.

During the traverse pass, the following steps occur:
 1. user-provided tags are ensured to be globally unique, and saved as xref targets
 2. internal tags are heuristically assigned to parts based on their section names
 3. internal tags are converted to unique external tags, but not provided for user-written xrefs
    (needed for automatic linking, e.g. in a table of contents)

Note that internal invariants about uniqueness of names can be violated by editing the JSON
serialization. This may lead to unexpected results.
-/
inductive Tag where
  | /-- A user-provided tag - respect this if possible -/ provided (name : String)
  | /-- A unique tag, suitable for inclusion in a document -/ private external (name : Slug)
  | /-- A machine-assigned tag -/ private internal (name : String)
deriving BEq, Hashable, Repr, ToJson, FromJson

instance : ToString Tag where
  toString := toString ∘ repr

instance : Coe String Tag where
  coe := .provided



/-- When rendering multi-page HTML, should splitting pages follow the depth setting? -/
inductive HtmlSplitMode where
  | /-- Follow the main setting -/ default
  |  /-- Do not split here nor in child parts -/ never
deriving BEq, Hashable, Repr, ToJson, FromJson

instance : Inhabited HtmlSplitMode := ⟨.default⟩

inductive Numbering where
  | /-- Ordinary numbering -/
    nat (n : Nat)
  | /-- Letter numbering, used e.g. for appendices -/
    letter (char : Char)
deriving DecidableEq, Hashable, Repr

instance : ToString Numbering where
  toString
    | .nat n => toString n
    | .letter a => toString a

structure PartMetadata where
  /--
  A shorter title to be shown in titlebars and tables of contents.
  -/
  shortTitle : Option String := none
  authors : List String := []
  /-- An extra note to show after the author list -/
  authorshipNote : Option String := none
  date : Option String := none
  /-- The main tag for the part, used for cross-references. -/
  tag : Option Tag := none
  /-- If this part ends up as the root of a file, use this name for it -/
  file : Option String := none
  /-- The internal unique ID, assigned during traversal. -/
  id : Option InternalId := none
  /-- Should this section be numbered? If `false`, then it's like `\section*` in LaTeX -/
  number : Bool := true
  /-- If `true`, the part is only rendered in draft mode. -/
  draft : Bool := false
  /-- Which number has been assigned? This field is set during traversal. -/
  assignedNumber : Option Numbering := none
  /-- If `true`, this part will display a list of subparts that are separate HTML pages. -/
  htmlToc := true
  htmlSplit : HtmlSplitMode := .default
deriving BEq, Hashable, Repr


def Domains := NameMap Domain
def Domains.contents : Domains → NameMap Domain := id

instance : BEq Domains where
  beq := ptrEqThen fun x y =>
    x.size == y.size &&
    x.all fun k v => y.find? k |>.isEqSome v

instance : GetElem Domains Name Domain (fun ds d => ds.contents.contains d) where
  getElem ds d _ok := ds.contents.find! d

instance : GetElem? Domains Name Domain (fun ds d => ds.contents.contains d) where
  getElem? ds d := ds.contents.find? d

instance : EmptyCollection Domains := ⟨({} : NameMap Domain)⟩

instance : ForIn m Domains (Name × Domain) :=
  inferInstanceAs (ForIn m (NameMap Domain) (Name × Domain))

def StringSet := HashSet String

structure TraverseState where
  tags : HashMap Tag InternalId := {}
  externalTags : HashMap InternalId Link := {}
  domains : Domains := {}
  remoteContent : AllRemotes
  ids : TreeSet InternalId := {}
  extraCss : HashSet String := {}
  extraJs : HashSet String := {}
  extraJsFiles : Array (String × String) := #[]
  extraCssFiles : Array (String × String) := #[]
  licenseInfo : HashSet LicenseInfo := {}
  private contents : NameMap Json := {}

/--
Returns a fresh internal ID.
-/
def freshId [Monad m] [MonadStateOf TraverseState m] : m InternalId := do
  modifyGet fun st =>
    let (i, ids) := InternalId.fresh st.ids
    (i, {st with ids})

def freshTag [Monad m] [MonadStateOf TraverseState m] (hint : String) (id : InternalId) : m String := do
  let strPart : String := hint.sluggify.toString
  let mut numPart : Option Nat := none
  repeat
    let attempt := tagStr strPart numPart
    if (← get).tags.contains  attempt then
      numPart := some <| numPart.map (· + 1) |>.getD 0
    else break
  let tag := tagStr strPart numPart
  modify fun st => {st with tags := st.tags.insert (Tag.internal tag) id}
  pure tag
where
  tagStr (strPart : String) (numPart : Option Nat) := s!"{strPart}{numPart.map (s!"-{·}") |>.getD ""}"

defmethod HashMap.all [BEq α] [Hashable α] (hm : HashMap α β) (p : α → β → Bool) : Bool :=
  hm.fold (fun prev k v => prev && p k v) true

local instance [BEq α] [Hashable α] : BEq (HashSet α) where
  beq := ptrEqThen fun xs ys => xs.size == ys.size && xs.all (ys.contains ·)

local instance [BEq α] [Ord α] : BEq (TreeSet α) where
  beq := ptrEqThen fun xs ys => xs.size == ys.size && xs.all (ys.contains ·)


instance : BEq TraverseState where
  beq := ptrEqThen fun x y =>
    ptrEqThen' x.tags y.tags (fun t1 t2 =>
      t1.size == t2.size && t1.all (t2[·]?.isEqSome ·)) &&
    x.externalTags.size == y.externalTags.size &&
    (x.externalTags.all fun k v =>
      match y.externalTags[k]? with
      | none => false
      | some v' => v == v') &&
    x.domains == y.domains &&
    x.remoteContent == y.remoteContent &&
    x.ids == y.ids &&
    x.extraCss == y.extraCss &&
    x.extraJs == y.extraJs &&
    x.extraJsFiles == y.extraJsFiles &&
    x.extraCssFiles == y.extraCssFiles &&
    ptrEqThen' x.contents y.contents (fun c1 c2 =>
      c1.size == c2.size &&
      c1.all (c2.find? · |>.isEqSome ·)) &&
    x.licenseInfo == y.licenseInfo

namespace TraverseState

def set [ToJson α] (state : TraverseState) (name : Name) (value : α) : TraverseState :=
  {state with contents := state.contents.insert name (ToJson.toJson value)}

/-- Returns `none` if the key is not found, or `some (error e)` if JSON deserialization failed -/
def get? [FromJson α] (state : TraverseState) (name : Name) : Option (Except String α) :=
  state.contents.find? name |>.map FromJson.fromJson?

def saveDomainObject (state : TraverseState) (domain : Name) (canonicalName : String) (id : InternalId) : TraverseState :=
  {state with
    domains :=
      state.domains.insert domain (state.domains.find? domain |>.getD {} |>.insertId canonicalName id)}

def saveDomainObjectData (state : TraverseState) (domain : Name) (canonicalName : String) (data : Json) : TraverseState :=
  {state with
    domains :=
      state.domains.insert domain (state.domains.find? domain |>.getD {} |>.setData canonicalName data)}

def modifyDomainObjectData (state : TraverseState) (domain : Name) (canonicalName : String) (f : Json → Json) : TraverseState :=
  {state with
    domains :=
      state.domains.insert domain (state.domains.find? domain |>.getD {} |>.modifyData canonicalName f)}

def getDomainObject? (state : TraverseState) (domain : Name) (canonicalName : String) : Option Object :=
  state.domains.find? domain >>= fun d => d.get? canonicalName

def setDomainTitle (state : TraverseState) (domain : Name) (title : String) : TraverseState :=
  {state with domains := state.domains.insert domain {state.domains.find? domain |>.getD {} with title := some title}}

def setDomainDescription (state : TraverseState) (domain : Name) (description : String) : TraverseState :=
  {state with domains := state.domains.insert domain {state.domains.find? domain |>.getD {} with description := some description}}

def htmlId (state : TraverseState) (id : InternalId) : Array (String × String) :=
  if let some {htmlId, ..} := state.externalTags[id]? then
    #[("id", htmlId.toString)]
  else #[]

/-- Add an open-source license used in the generated HTML/JavaScript -/
def addLicenseInfo (state : TraverseState) (licenseInfo : LicenseInfo) : TraverseState :=
  {state with licenseInfo := state.licenseInfo.insert licenseInfo}
end TraverseState


structure Block where
  name : Name := by exact decl_name%
  id : Option InternalId := none
  data : Json := Json.null
deriving BEq, Hashable, ToJson, FromJson

structure Inline where
  name : Name := by exact decl_name%
  id : Option InternalId := none
  data : Json := Json.null
deriving BEq, Hashable, ToJson, FromJson

private partial def cmpJson : (j1 j2 : Json) → Ordering
  | .null, .null => .eq
  | .null, _ => .lt
  | _, .null => .gt
  | .bool b1, .bool b2 => Ord.compare b1 b2
  | .bool _, _ => .lt
  | _, .bool _ => .gt
  | .str s1, .str s2 => Ord.compare s1 s2
  | .str _, _ => .lt
  | _, .str _ => .gt
  | .num n1, .num n2 => Ord.compare n1 n2
  | .num _, _ => .lt
  | _, .num _ => .gt
  | .arr xs, .arr ys =>
    Ord.compare xs.size ys.size |>.then (Id.run do
      for ⟨x, _⟩ in xs.attach, ⟨y, _⟩ in ys.attach do
        let o := cmpJson x y
        if o != .eq then return o
      .eq)
  | .arr _, _ => .lt
  | _, .arr _ => .gt
  | .obj o1, .obj o2 =>
    let k1 := o1.toArray.qsort (·.1 < ·.1)
    let k2 := o2.toArray.qsort (·.1 < ·.1)
    Ord.compare k1.size k2.size |>.then (Id.run do
      for ⟨kx, x⟩ in k1, ⟨ky, y⟩ in k2 do
        let o := Ord.compare kx ky |>.then (cmpJson x y)
        if o != .eq then return o
      .eq)

instance : Ord Inline where
  compare i1 i2 := i1.name.cmp i2.name |>.then (Ord.compare i1.id i2.id) |>.then (cmpJson i1.data i2.data)

structure PartHeader where
  titleString : String
  metadata : Option PartMetadata

structure TraverseContext where
  /-- The current URL path - will be [] for non-HTML output or in the root -/
  path : Path := #[]
  /-- The path from the root to the current header -/
  headers : Array PartHeader := #[]
  /-- Whether the current build is a draft (used for hiding TODOs, etc from public builds) -/
  draft : Bool := false
  logError : String → IO Unit

def TraverseContext.inFile (self : TraverseContext) (file : String) : TraverseContext :=
  {self with path := self.path.push file}

abbrev BlockTraversal genre :=
  InternalId → Json → Array (Doc.Block genre) →
  ReaderT TraverseContext (StateT TraverseState IO) (Option (Doc.Block genre))

abbrev BlockToHtml (genre : Genre) (m) :=
  (Doc.Inline genre → Html.HtmlT genre m Output.Html) →
  (Doc.Block genre → Html.HtmlT genre m Output.Html) →
  InternalId → Json → Array (Doc.Block genre) → Html.HtmlT genre m Output.Html

abbrev BlockToTeX (genre : Genre) (m) :=
  (Doc.Inline genre → TeX.TeXT genre m Output.TeX) →
  (Doc.Block genre → TeX.TeXT genre m Output.TeX) →
  InternalId → Json → Array (Doc.Block genre) → TeX.TeXT genre m Output.TeX

abbrev InlineTraversal genre :=
  InternalId → Json → Array (Doc.Inline genre) →
  ReaderT TraverseContext (StateT TraverseState IO) (Option (Doc.Inline genre))

abbrev InlineToHtml (genre : Genre) (m) :=
  (Doc.Inline genre → Html.HtmlT genre m Output.Html) →
    InternalId → Json → Array (Doc.Inline genre) → Html.HtmlT genre m Output.Html

abbrev InlineToTeX (genre : Genre) (m) :=
  (Doc.Inline genre → TeX.TeXT genre m Output.TeX) →
    InternalId → Json → Array (Doc.Inline genre) → TeX.TeXT genre m Output.TeX


structure ExtensionImpls where
  private mk ::
  -- This is to work around recursion restrictions, not for real dynamism
  -- They are expected to be `InlineDescr` and `BlockDescr`, respectively
  inlineDescrs : NameMap Dynamic
  blockDescrs : NameMap Dynamic

end Manual

def Manual : Genre where
  PartMetadata := Manual.PartMetadata
  Block := Manual.Block
  Inline := Manual.Inline
  TraverseContext := Manual.TraverseContext
  TraverseState := Manual.TraverseState

instance : BEq (Genre.PartMetadata Manual) := inferInstanceAs (BEq Manual.PartMetadata)
instance : BEq (Genre.Block Manual) := inferInstanceAs (BEq Manual.Block)
instance : BEq (Genre.Inline Manual) := inferInstanceAs (BEq Manual.Inline)

instance : Ord (Genre.Inline Manual) := inferInstanceAs (Ord Manual.Inline)

instance : Hashable (Genre.Block Manual) := inferInstanceAs (Hashable Manual.Block)
instance : Hashable (Genre.Inline Manual) := inferInstanceAs (Hashable Manual.Inline)

instance : Repr (Genre.PartMetadata Manual) := inferInstanceAs (Repr Manual.PartMetadata)

instance : ToJson (Genre.Inline Manual) := inferInstanceAs (ToJson Manual.Inline)
instance : ToJson (Genre.Block Manual) := inferInstanceAs (ToJson Manual.Block)

instance : FromJson (Genre.Inline Manual) := inferInstanceAs (FromJson Manual.Inline)

namespace Manual

def PartHeader.ofPart (part : Part Manual) : PartHeader :=
  {titleString := part.titleString, metadata := part.metadata}

def TraverseContext.inPart (self : TraverseContext) (part : Part Manual) : TraverseContext :=
  {self with headers := self.headers.push <| .ofPart part}

def TraverseContext.sectionNumber (self : TraverseContext) : Array (Option Numbering) :=
  self.headers.map (·.metadata |>.getD {} |>.assignedNumber)

structure InlineDescr where
  init : TraverseState → TraverseState := id

  /--
  Given the contents of the `data` field of the corresponding `Manual.Inline` and the contained
  inline elements, carry out the traversal pass.

  In addition to updating the cross-reference state through the available monadic effects, a
  traversal may additionally replace the element with another one. This can be used to e.g. emit
  a cross-reference once the target becomes available in the state. To replace the element,
  return `some`. To leave it as is, return `none`.
  -/
  traverse : InlineTraversal Manual

  toHtml : Option (InlineToHtml Manual (ReaderT ExtensionImpls IO))
  extraJs : List String := []
  extraJsFiles : List (String × String) := []
  extraCss : List String := []
  extraCssFiles : List (String × String) := []
  licenseInfo : List LicenseInfo := []
  /--
  Should this inline be an entry in the page-local ToC? If so, how should it be represented?

  Entries should be returned as a preference-ordered array of representations. Each representation
  consists of a string and some HTML; the string should represent the HTML's content if all
  formatting were stripped. Items are compared for string equality, with later suggestions used in
  case of overlap, but the HTML is what's displayed.

  The empty array means that the block should not be included.
  -/
  localContentItem : InternalId → Json → Array (Doc.Inline Manual) → Except String (Array (String × Verso.Output.Html)) :=
    fun _ _ _ => pure #[]

  toTeX : Option (InlineToTeX Manual (ReaderT ExtensionImpls IO))

deriving TypeName

instance : Inhabited InlineDescr := ⟨⟨id, default, default, default, default, default, default, default, default, default⟩⟩

structure BlockDescr where
  init : TraverseState → TraverseState := id

  traverse : BlockTraversal Manual

  toHtml : Option (BlockToHtml Manual (ReaderT ExtensionImpls IO))
  extraJs : List String := []
  extraJsFiles : List (String × String) := []
  extraCss : List String := []
  extraCssFiles : List (String × String) := []
  licenseInfo : List LicenseInfo := []
  /--
  Should this block be an entry in the page-local ToC? If so, how should it be represented?

  Entries should be returned as a preference-ordered array of representations. Each representation
  consists of a string and some HTML; the string should represent the HTML's content if all
  formatting were stripped. Items are compared for string equality, with later suggestions used in
  case of overlap, but the HTML is what's displayed. Exceptions are logged as errors during HTML
  generation.

  The empty array means that the block should not be included.
  -/
  localContentItem : InternalId → Json → Array (Doc.Block Manual) → Except String (Array (String × Verso.Output.Html)) :=
    fun _ _ _ => pure #[]

  toTeX : Option (BlockToTeX Manual (ReaderT ExtensionImpls IO))
deriving TypeName

instance : Inhabited BlockDescr := ⟨⟨id, default, default, default, default, default, default, default, default, default⟩⟩

open Lean in
initialize inlineExtensionExt
    : PersistentEnvExtension (Name × Name) (Name × Name) (NameMap Name) ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := fun _ => pure {},
    addEntryFn := fun as (src, tgt) => as.insert src tgt,
    exportEntriesFn := fun es =>
      es.fold (fun a src tgt => a.push (src, tgt)) #[] |>.qsort (Name.quickLt ·.1 ·.1)
  }

open Lean in
initialize blockExtensionExt
    : PersistentEnvExtension (Name × Name) (Name × Name) (NameMap Name) ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := fun _ => pure {},
    addEntryFn := fun as (src, tgt) => as.insert src tgt,
    exportEntriesFn := fun es =>
      es.fold (fun a src tgt => a.push (src, tgt)) #[] |>.qsort (Name.quickLt ·.1 ·.1)
  }

syntax (name := inline_extension) "inline_extension" ident : attr
syntax (name := block_extension) "block_extension" ident : attr

open Lean in
initialize
  let register (name) (strName : String) (ext : PersistentEnvExtension (Name × Name) (Name × Name) (NameMap Name)) (get : Syntax → Option Ident) := do
    registerBuiltinAttribute {
      name := name,
      ref := by exact decl_name%,
      add := fun decl stx kind => do
        unless kind == AttributeKind.global do throwError "invalid attribute '{name}', must be global"
        unless ((← getEnv).getModuleIdxFor? decl).isNone do
          throwError "invalid attribute '{name}', declaration is in an imported module"
        let some extIdent := get stx
          | throwError "invalid syntax for '{name}' attribute"

        let extName ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo extIdent

        modifyEnv fun env => ext.addEntry env (extName.eraseMacroScopes, decl.eraseMacroScopes) -- TODO check that it's not already there

      descr := s!"Registers a definition as the description of {strName}"
    }
  register `inline_extension "an inline extension" inlineExtensionExt fun | `(attr|inline_extension $extIdent) => extIdent | _ => none
  register `block_extension "a block extension" blockExtensionExt fun | `(attr|block_extension $extIdent) => extIdent | _ => none


open Lean.Parser Term in
def extContents := structInstFields (sepByIndent Term.structInstField "; " (allowTrailingSep := true))

syntax "block_extension" ident (ppSpace bracketedBinder)* ppIndent(ppSpace "where" extContents) : command
syntax "inline_extension" ident (ppSpace bracketedBinder)* ppIndent(ppSpace "where" extContents) : command

def isDataField : Lean.TSyntax ``Lean.Parser.Term.structInstField → Bool
  | `(Lean.Parser.Term.structInstField|data := $_) => true
  | `(Lean.Parser.Term.structInstField|data) => true
  | _ => false

open Lean Elab Command in
elab_rules : command
  | `(block_extension $x $args* where $contents;*) => do
    let (data, nonData) := (contents : Array _).partition isDataField
    if data.size > 1 then
      for x in data do
        logErrorAt x "Multiple 'data' fields found"
    let cmd1 ←
      `(command| def $x $args* : Block where $data;*)
    let descrName := x.getId ++ `descr |> mkIdentFrom x
    let cmd2 ←
      `(command|
        @[block_extension $x]
        private def $descrName : BlockDescr where $nonData;*)
    elabCommand cmd1
    elabCommand cmd2

open Lean Elab Command in
elab_rules : command
  | `(inline_extension $x $args* where $contents;*) => do
    let (data, nonData) := (contents : Array _).partition isDataField
    if data.size > 1 then
      for x in data do
        logErrorAt x "Multiple 'data' fields found"
    let cmd1 ←
      `(command| def $x $args* : Inline where $data;*)
    let descrName := x.getId ++ `descr |> mkIdentFrom x
    let cmd2 ←
      `(command|
        @[inline_extension $x]
        private def $descrName : InlineDescr where $nonData;*)
    elabCommand cmd1
    elabCommand cmd2

open Lean in
private def nameAndDef [Monad m] [MonadRef m] [MonadQuotation m] (ext : Name × Name) : m Term := do
  let quoted : Term := quote ext.fst
  let ident ← mkCIdentFromRef ext.snd
  `(($quoted, $(⟨ident⟩)))

open Lean Elab Term in
scoped elab "inline_extensions%" : term => do
  let env ← getEnv
  let mut exts := #[]
  for (ext, descr) in inlineExtensionExt.getState env do
    exts := exts.push (ext, descr)
  for imported in inlineExtensionExt.toEnvExtension.getState env |>.importedEntries do
    for x in imported do
      exts := exts.push x
  let stx ← `([$[($(← exts.mapM nameAndDef) : Name × InlineDescr)],*])
  elabTerm stx none

open Lean Elab Term in
scoped elab "block_extensions%" : term => do
  let env ← getEnv
  let mut exts := #[]
  for (ext, descr) in blockExtensionExt.getState env do
    exts := exts.push (ext, descr)
  for imported in blockExtensionExt.toEnvExtension.getState env |>.importedEntries do
    for x in imported do
      exts := exts.push x
  let stx ← `([$[($(← exts.mapM nameAndDef) : Name × BlockDescr)],*])
  elabTerm stx none

def ExtensionImpls.empty : ExtensionImpls := ⟨{}, {}⟩

instance : EmptyCollection ExtensionImpls where
  emptyCollection := .empty

def ExtensionImpls.getInline? (impls : ExtensionImpls) (name : Name) : Option InlineDescr :=
  impls.inlineDescrs.find? name |>.map (·.get? InlineDescr |>.get!)

def ExtensionImpls.getBlock? (impls : ExtensionImpls) (name : Name) : Option BlockDescr :=
  impls.blockDescrs.find? name |>.map (·.get? BlockDescr |>.get!)

def ExtensionImpls.insertInline (impls : ExtensionImpls) (name : Name) (desc : InlineDescr) : ExtensionImpls :=
  {impls with
    inlineDescrs := impls.inlineDescrs.insert name (.mk desc)}

def ExtensionImpls.insertBlock (impls : ExtensionImpls) (name : Name) (desc : BlockDescr) : ExtensionImpls :=
  {impls with
    blockDescrs := impls.blockDescrs.insert name (.mk desc)}

def ExtensionImpls.fromLists (inlineImpls : List (Name × InlineDescr)) (blockImpls : List (Name × BlockDescr)) : ExtensionImpls :=
  inlineImpls.foldl (fun out (n, impl) => out.insertInline n impl) <| blockImpls.foldl (fun out (n, impl) => out.insertBlock n impl) {}

open Lean Elab Term in
elab "extension_impls%" : term => do elabTerm (← ``(ExtensionImpls.fromLists inline_extensions% block_extensions%)) none

abbrev TraverseM := ReaderT ExtensionImpls (ReaderT Manual.TraverseContext (StateT Manual.TraverseState IO))

def TraverseM.run
    (impls : ExtensionImpls)
    (ctxt : Manual.TraverseContext)
    (state : Manual.TraverseState)
    (act : TraverseM α) : IO (α × Manual.TraverseState) :=
  act impls ctxt state

instance : MonadReader Manual.TraverseContext TraverseM where
  read := readThe _

instance : MonadWithReader Manual.TraverseContext TraverseM where
  withReader := withTheReader Manual.TraverseContext

def logError [Monad m] [MonadLiftT IO m] [MonadReaderOf Manual.TraverseContext m] (err : String) : m Unit := do
  (← readThe Manual.TraverseContext).logError err

def isDraft [Functor m] [MonadReaderOf Manual.TraverseContext m] : m Bool :=
  (·.draft) <$> (readThe Manual.TraverseContext)

/--
Get or create the external tag assigned to an ID.

If the external tag already exists, it is returned. If it needs creating, then the provided path is
saved as its target and the string argument is used as a basis for the tag.
-/
def externalTag [Monad m] [MonadState TraverseState m] (id : InternalId) (path : Path) (name : String) : m Tag := do
  if let some { htmlId := t, .. } := (← get).externalTags[id]? then
    return Tag.external t
  else
    let mut attempt := name.sluggify
    repeat
      if (← get).tags.contains (Tag.external attempt) then attempt := attempt.toString ++ "-next" |>.sluggify
      else break
    let t' := Tag.external attempt
    modify fun st => {st with
      tags := st.tags.insert t' id,
      externalTags := st.externalTags.insert id { path, htmlId := attempt }
    }
    pure t'

def TraverseState.resolveId (st : TraverseState) (id : InternalId) : Option Link :=
  if let some x := st.externalTags[id]? then
      pure x
  else none

def TraverseState.resolveDomainObject (st : TraverseState) (domain : Name) (canonicalName : String) : Except String Link := do
  if let some obj := st.getDomainObject? domain canonicalName then
    match obj.ids.size with
      | 0 =>
        throw s!"No link target registered for {canonicalName} in {domain}"
      | 1 =>
        let id := obj.ids.toArray[0]!
        if let some dest := st.resolveId id then
          return dest
        else
          throw s!"No link target registered for id {id} from {canonicalName} in {domain}"
      | more =>
        throw s!"Ref {canonicalName} in {domain} has {more} targets, can only link to one"
  else throw s!"Not found: {canonicalName} in {domain}"

def TraverseState.resolveRemoteObject (st : TraverseState) (domain : Name) (canonicalName : String) (remote : String) : Except String RemoteLink := do
  let some data := st.remoteContent[remote]?
    | throw s!"Remote {remote} not found"
  let some dom := data.domains.find? domain
    | throw s!"Remote {remote} has no domain '{domain}'"
  let some v := dom.contents[canonicalName]?
    | throw s!"Remote {remote} domain '{domain}' does not define '{canonicalName}'"
  match h : v.size with
  | 0 =>
    throw s!"No link target registered for {canonicalName} in {domain} in remote {remote}"
  | 1 =>
    return v[0].link
  | more =>
    throw s!"Ref {canonicalName} in {domain} in remote {remote} has {more} targets, can only link to one"


def TraverseState.resolveTag (st : TraverseState) (tag : Slug) : Option Link :=
  if let some id := st.tags[Tag.external tag]? then
    if let some x := st.externalTags[id]? then
      pure x
    else panic! s!"No location for ID {id}, but it came from external tag '{tag}'"
  else none

/--
A representation of domains.

A domain is a particular namespace of documentable entities.

Generally, domains are identified by their name, but having a representation for them
means that they can be used with Lean's standard namespace features and have docstrings.
-/
structure Domain where
  name : Name := by exact decl_name%

def doc : Domain := {}
def doc.tactic : Domain := {}
def doc.tech : Domain := {}
def doc.syntaxKind : Domain := {}
def doc.option : Domain := {}
def doc.tactic.conv : Domain := {}

-- Protected to avoid taking up good namespace
protected def «example» : Domain := {}

def docstringDomain := ``Verso.Genre.Manual.doc
def tacticDomain := ``Verso.Genre.Manual.doc.tactic
def technicalTermDomain := ``Verso.Genre.Manual.doc.tech
def syntaxKindDomain := ``Verso.Genre.Manual.doc.syntaxKind
def optionDomain := ``Verso.Genre.Manual.doc.option
def convDomain := ``Verso.Genre.Manual.doc.tactic.conv
def exampleDomain := ``Verso.Genre.Manual.example

def TraverseState.definitionIds (state : TraverseState) : NameMap String := Id.run do
  if let some examples := state.domains.find? exampleDomain then
    let mut idMap := {}
    for (x, _) in examples.objects do
      if let .ok { htmlId := slug, .. } := state.resolveDomainObject exampleDomain x then
        idMap := idMap.insert x.toName slug.toString
    return idMap
  else return {}

def TraverseState.linksFromDomain
    (domain : Name) (canonicalName : String)
    (shortDescription description : String)
    (state : TraverseState) : Array Code.CodeLink :=
  state.resolveDomainObject domain canonicalName |>.toOption |>.toArray |>.map fun l =>
    { shortDescription, description, href := l.link }

def TraverseState.localTargets (state : TraverseState) : Code.LinkTargets where
  const := fun x =>
    state.linksFromDomain docstringDomain x.toString "doc" s!"Documentation for {x}" ++
    state.linksFromDomain exampleDomain x.toString "def" s!"Definition of example {x}"
  option := fun x =>
    state.linksFromDomain optionDomain x.toString "doc" s!"Documentation for option {x}"
  keyword := fun k =>
    state.linksFromDomain tacticDomain k.toString "doc" "Documentation for tactic" ++
    state.linksFromDomain syntaxKindDomain k.toString "doc" "Documentation for syntax"


def TraverseState.remoteTargets (state : TraverseState) : Code.LinkTargets where
  const := fun x =>
    fromRemoteDomain docstringDomain x.toString (s!"doc ({·})") (s!"Documentation for {x} in {·}")
  option := fun x =>
    fromRemoteDomain optionDomain x.toString (s!"doc ({·})") (s!"Documentation for option {x} in {·}")
  keyword := fun k =>
    fromRemoteDomain tacticDomain k.toString (s!"doc ({·})") (s!"Documentation for tactic in {·}") ++
    fromRemoteDomain syntaxKindDomain k.toString (s!"doc ({·})") (s!"Documentation for syntax in {·}")
where

  fromRemoteDomain (domain : Name) (canonicalName : String) (shortDescription description : String → String) : Array Code.CodeLink := Id.run do
    state.remoteContent.toArray.filterMap fun (r, info) =>
      state.resolveRemoteObject domain canonicalName r |>.toOption |>.map fun l => {
        shortDescription := shortDescription info.shortName,
        description := description info.longName,
        href := l.link
      }


def sectionNumberString (num : Array Numbering) : String := Id.run do
  let mut out := ""
  for n in num do
    out := out ++
      match n with
      | .nat n => s!"{n}."
      | .letter a => s!"{a}."
  out

def sectionString (ctxt : TraverseContext) : Option String :=
  ctxt.sectionNumber.mapM id |>.map sectionNumberString


def sectionDomain := `Verso.Genre.Manual.section

instance : TraversePart Manual where
  inPart p := (·.inPart p)

instance : Traverse Manual TraverseM where
  part p :=
    if p.metadata.isNone then pure (some {}) else pure none
  block _ := pure ()
  inline _ := pure ()
  genrePart startMeta part := do
    let mut «meta» := startMeta

    -- First, assign a unique ID if there is none
    let id ← if let some i := meta.id then pure i else freshId
    «meta» := {«meta» with id := some id}

    -- Next, assign a tag, prioritizing user-chosen external IDs
    match meta.tag with
    | none =>
      -- Assign an internal tag - the next round will make it external This is done in two rounds to
      -- give priority to user-provided tags that might otherwise anticipate the name-mangling scheme
      let what := (← read).headers.map (·.titleString ++ "--") |>.push part.titleString |>.foldl (init := "") (· ++ ·)
      let tag ← freshTag what id
      «meta» := {«meta» with tag := Tag.internal tag}
    | some t =>
      -- Ensure uniqueness
      if let some id' := (← get).tags[t]? then
        if id != id' then
          logError s!"Duplicate tag '{t}'"
      else
        modify fun st => {st with tags := st.tags.insert t id}
      let path := (← readThe TraverseContext).path
      match t with
      | Tag.external name =>
        -- These are the actual IDs to use in generated HTML and links and such
        modify fun st => {st with externalTags := st.externalTags.insert id { path, htmlId := name } }
      | Tag.internal name =>
        «meta» := {«meta» with tag := ← externalTag id path name}
      | Tag.provided n =>
        let slug := n.sluggify
        -- Convert to an external tag, and fail if we can't (users should control their link IDs)
        let external := Tag.external slug
        if let some id' := (← get).tags[external]? then
          if id != id' then logError s!"Duplicate tag '{t}'"
        else
          modify fun st => {st with
              tags := st.tags.insert external id,
              externalTags := st.externalTags.insert id { path, htmlId := slug }
            }
          «meta» := {«meta» with tag := external}
        let jsonMetadata :=
          Json.arr ((← read).inPart part |>.headers.map (fun h => json%{
            "title": $h.titleString,
            "shortTitle": $(h.metadata.bind (·.shortTitle)),
            "number": $(h.metadata.bind (·.assignedNumber) |>.map toString)
          }))
        let title := (← read).inPart part |>.headers |>.back? |>.map (·.titleString)
        let shortTitle := (← read).inPart part |>.headers |>.back? |>.bind (·.metadata) |>.bind (·.shortTitle)
        -- During the traverse pass, the root section (which is unnumbered) is in the header stack.
        -- Including it causes all sections to be unnumbered, so it needs to be dropped here.
        -- TODO: harmonize this situation with HTML generation and give it a clean API
        let num :=
          ((← read).inPart part |>.headers[1:]).toArray.map (fun (h : PartHeader) => h.metadata.bind (·.assignedNumber))
            |>.mapM _root_.id |>.map sectionNumberString
        modify (·.saveDomainObject sectionDomain n id |>.saveDomainObjectData sectionDomain n (json%{
          "context": $jsonMetadata,
          "title": $title,
          "shortTitle": $shortTitle,
          "sectionNum": $num
        }))

    -- Assign section numbers to subsections
    let mut i := 1
    let mut subs := #[]
    let mut modifiedSubs := false
    for s in part.subParts do
      let mut subMeta := s.metadata.getD {}
      if subMeta.number then
        if subMeta.assignedNumber != some (.nat i) then
          subMeta := {subMeta with assignedNumber := some (.nat i)}
        i := i + 1
      else
        if subMeta.assignedNumber.isSome then
          subMeta := {subMeta with assignedNumber := none}
      if s.metadata == some subMeta then
        subs := subs.push s
      else
        subs := subs.push <| s.withMetadata subMeta
        modifiedSubs := true


    pure <|
      if not modifiedSubs && «meta» == startMeta then none
      else pure (part |>.withMetadata «meta» |>.withSubparts subs)

  genreBlock
    | ⟨name, id?, data⟩, content => do
      if let some id := id? then
        if let some impl := (← readThe ExtensionImpls).getBlock? name then
          for js in impl.extraJs do
            modify fun s => {s with extraJs := s.extraJs.insert js}
          for css in impl.extraCss do
            modify fun s => {s with extraCss := s.extraCss.insert css}
          for (name, js) in impl.extraJsFiles do
            unless (← get).extraJsFiles.any (·.1 == name) do
              modify fun s => {s with extraJsFiles := s.extraJsFiles.push (name, js)}
          for (name, js) in impl.extraCssFiles do
            unless (← get).extraCssFiles.any (·.1 == name) do
              modify fun s => {s with extraCssFiles := s.extraCssFiles.push (name, js)}
          for licenseInfo in impl.licenseInfo do
            modify (·.addLicenseInfo licenseInfo)

          impl.traverse id data content
        else
          logError s!"No block traversal implementation found for {name}"
          pure none
      else
        -- Assign a fresh ID if there is none. It can then be used on the next traversal pass.
        let id ← freshId
        pure <| some <| Block.other ⟨name, some id, data⟩ content
  genreInline
    | ⟨name, id?, data⟩, content => do
      if let some id := id? then
        if let some impl := (← readThe ExtensionImpls).getInline? name then
          for js in impl.extraJs do
            modify fun s => {s with extraJs := s.extraJs.insert js}
          for css in impl.extraCss do
            modify fun s => {s with extraCss := s.extraCss.insert css}
          for (name, js) in impl.extraJsFiles do
            unless (← get).extraJsFiles.any (·.1 == name) do
              modify fun s => {s with extraJsFiles := s.extraJsFiles.push (name, js)}
          for (name, js) in impl.extraCssFiles do
            unless (← get).extraCssFiles.any (·.1 == name) do
              modify fun s => {s with extraCssFiles := s.extraCssFiles.push (name, js)}
          for licenseInfo in impl.licenseInfo do
            modify (·.addLicenseInfo licenseInfo)

          impl.traverse id data content
        else
          logError s!"No inline traversal implementation found for {name}"
          pure none
      else
        -- Assign a fresh ID if there is none. It can then be used on the next traversal pass.
        let id ← freshId
        pure <| some <| Inline.other ⟨name, some id, data⟩ content

open Verso.Output.TeX in
instance : TeX.GenreTeX Manual (ReaderT ExtensionImpls IO) where
  part go _meta txt := go txt
  block goI goB b content := do
    let some id := b.id
      | panic! s!"Block {b.name} wasn't assigned an ID during traversal"
    let some descr := (← readThe ExtensionImpls).getBlock? b.name
      | panic! s!"Unknown block {b.name} while rendering.\n\nKnown blocks: {(← readThe ExtensionImpls).blockDescrs.toArray |>.map (·.fst) |>.qsort (·.toString < ·.toString)}"
    let some impl := descr.toTeX
      | panic! s!"Block {b.name} doesn't support TeX"
    impl goI goB id b.data content
  inline go i content := do
    let some id := i.id
      | panic! "Inline {i.name} wasn't assigned an ID during traversal"
    let some descr := (← readThe ExtensionImpls).getInline? i.name
      | panic! s!"Unknown inline {i.name} while rendering.\n\nKnown inlines: {(← readThe ExtensionImpls).inlineDescrs.toArray |>.map (·.fst) |>.qsort (·.toString < ·.toString)}"
    let some impl := descr.toTeX
      | panic! s!"Inline {i.name} doesn't support TeX"
    impl go id i.data content


def sectionHtml (ctxt : TraverseContext) : Html :=
  match sectionString ctxt with
  | none => .empty
   -- Non-breaking space because section numbers shouldn't end up on a line alone
  | some s => .text true (s ++ " ")

open Html in
/--
Create a permalink widget for sharing links to content.

If the provided state contains a canonical name for the object with the given ID in some domain,
then the returned HTML can be used to indicate this to users and give them a stable link to the
content. If the object has multiple names, or has names in multiple domains, then one of them is
selected arbitrarily. The returned HTML should be included within the HTML that represents the
object, rather than adjacent to it.
-/
def permalink (id : InternalId) (st : TraverseState) (inline : Bool := true) : Html := Id.run do
  let mut candidates := #[]
  for (dom, {objectsById, ..}) in st.domains do
    if let some canonicalNames := objectsById[id]? then
      for n in canonicalNames do
        candidates := candidates.push (dom, n)
  if h : candidates.size = 0 then .empty
  else
    -- If there's multiple, select one arbitrarily.
    let (domain, canonicalName) := candidates[0]
    let classes := "permalink-widget " ++ if inline then "inline" else "block"
    {{<span class={{classes}}>
        <a href=s!"/find/?domain={domain}&name={canonicalName}" title="Permalink">"🔗"</a>
      </span>
    }}


open Verso.Output.Html in
instance : Html.GenreHtml Manual (ReaderT ExtensionImpls IO) where
  part go «meta» txt := do
    let st ← Verso.Doc.Html.HtmlT.state
    let attrs := meta.id.map (st.htmlId) |>.getD #[]
    let ctxt ← Verso.Doc.Html.HtmlT.context
    let sectionNumber : Html := sectionHtml ctxt
    let permalink? m :=
      if let some id := m.id then permalink id st
      else .empty
    let mkHeader lvl content :=
      .tag s!"h{lvl}" attrs (sectionNumber ++ content ++ permalink? «meta»)
    go txt mkHeader

  block goI goB b content := do
    let some id := b.id
      | panic! s!"Block {b.name} wasn't assigned an ID during traversal"
    let some descr := (← readThe ExtensionImpls).getBlock? b.name
      | panic! s!"Unknown block {b.name} while rendering HTML.\n\nKnown blocks: {(← readThe ExtensionImpls).blockDescrs.toArray |>.map (·.fst) |>.qsort (·.toString < ·.toString)}"
    let some impl := descr.toHtml
      | panic! s!"Block {b.name} doesn't support HTML"
    impl goI goB id b.data content

  inline go i content := do
    let some id := i.id
      | panic! "Inline {i.name} wasn't assigned an ID during traversal"
    let some descr := (← readThe ExtensionImpls).getInline? i.name
      | panic! s!"Unknown inline {i.name} with data {i.data} while rendering HTML.\n\nKnown inlines: {(← readThe ExtensionImpls).inlineDescrs.toArray |>.map (·.fst) |>.qsort (·.toString < ·.toString)}"
    let some impl := descr.toHtml
      | panic! s!"Inline {i.name} doesn't support HTML"
    impl go id i.data content
