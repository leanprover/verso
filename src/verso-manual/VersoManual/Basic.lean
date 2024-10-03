/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Std.Data.HashSet
import Verso.Doc
import Verso.Doc.Html
import Verso.Doc.TeX
import VersoManual.Slug
import Verso.Output.Html
import Verso.Output.TeX

open Lean (Name Json NameMap ToJson FromJson)
open Std (HashSet HashMap)
open Verso.Doc
open Verso.Output

namespace Verso.Genre.Manual
inductive Output where
  | /-- LaTeX -/
    tex
  | /-- HTML - one page per part at the given depth -/
    html (depth : Nat)
deriving DecidableEq, BEq, Hashable

abbrev Path := Array String


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
  | /-- A user-provided tag - respect this if possible -/ provided (name : Slug)
  | /-- A unique tag, suitable for inclusion in a document -/ private external (name : String)
  | /-- A machine-assigned tag -/ private internal (name : String)
deriving BEq, Hashable, Repr, ToJson, FromJson

instance : ToString Tag where
  toString := toString ∘ repr

instance : Coe String Tag where
  coe := .provided ∘ Slug.ofString

/--
An internal identifier assigned to a part during traversal. Users don't get to have influence
over these IDs, so they can be used to ensure uniqueness of tags.

Even though the constructor is private, there is a JSON serialization that can be used to undermine
the uniqueness of internal IDs. Please don't do that - your program may break unpredictably.
-/
structure InternalId where
  private mk ::
  private id : Nat
deriving BEq, Hashable, Repr, ToJson, FromJson, Inhabited, Ord

instance : LT InternalId where
  lt x y := Ord.compare x y = .lt

instance : LE InternalId where
  le x y := x < y ∨ x = y

instance : ToString InternalId where
  toString x := s!"#<{x.id}>"

/-- When rendering multi-page HTML, should splitting pages follow the depth setting? -/
inductive HtmlSplitMode where
  | /-- Follow the main setting -/ default
  |  /-- Do not split here nor in child parts -/ never
deriving BEq, Hashable, Repr, ToJson, FromJson

instance : Inhabited HtmlSplitMode := ⟨.default⟩


structure PartMetadata where
  authors : List String := []
  date : Option String := none
  tag : Option Tag := none
  /-- If this part ends up as the root of a file, use this name for it -/
  file : Option String := none
  id : Option InternalId := none
  number : Bool := true
  htmlSplit : HtmlSplitMode := .default
deriving BEq, Hashable, Repr

/--
A documented object, described in specific locations in the document.
-/
structure Object where
  /--
  The canonical string name used to construct a cross-reference to this object, also from external
  sites. Should be stable over time.
  -/
  canonicalName : String
  /-- Extra data that can be used e.g. for rendering a domain index -/
  data : Json := .null
  /-- The IDs of the description site(s) -/
  ids : HashSet InternalId := {}
deriving Inhabited

instance : BEq Object where
  beq
    | {canonicalName := n1, data := d1, ids := i1}, {canonicalName := n2, data := d2, ids := i2} =>
      n1 == n2 &&
      d1 == d2 &&
      i1.size == i2.size && i1.fold (init := true) (fun soFar v => soFar && i2.contains v)

def Object.addId (id : InternalId) (object : Object) : Object :=
  {object with ids := object.ids.insert id}

def Object.setData (data : Json) (object : Object) : Object :=
  {object with data := data}

def Object.modifyData (f : Json → Json) (object : Object) : Object :=
  {object with data := f object.data}


structure Domain where
  objects : Lean.RBMap String Object compare := {}
deriving Inhabited

instance : BEq Domain where
  beq
    | ⟨d1⟩, ⟨d2⟩ => d1.size == d2.size && d1.all (fun k v => d2.find? k == some v)

def Domain.insertId (canonicalName : String) (id : InternalId) (domain : Domain) : Domain :=
  let obj := domain.objects.find? canonicalName |>.getD {canonicalName} |>.addId id
  ⟨domain.objects.insert canonicalName obj⟩

def Domain.setData  (canonicalName : String) (data : Json) (domain : Domain) : Domain :=
  let obj := domain.objects.find? canonicalName |>.getD {canonicalName} |>.setData data
  ⟨domain.objects.insert canonicalName obj⟩

def Domain.modifyData  (canonicalName : String) (f : Json → Json) (domain : Domain) : Domain :=
  let obj := domain.objects.find? canonicalName |>.getD {canonicalName} |>.modifyData f
  ⟨domain.objects.insert canonicalName obj⟩

def Domain.get? (canonicalName : String) (domain : Domain) : Option Object :=
  domain.objects.find? canonicalName

structure TraverseState where
  tags : HashMap Tag InternalId := {}
  externalTags : HashMap InternalId (Path × String) := {}
  domains : NameMap Domain := {}
  ids : HashSet InternalId := {}
  nextId : Nat := 0
  extraCss : HashSet String := {}
  extraJs : HashSet String := {}
  extraJsFiles : Array (String × String) := #[]
  extraCssFiles : Array (String × String) := #[]
  private contents : NameMap Json := {}

def freshId [Monad m] [MonadStateOf TraverseState m] : m InternalId := do
  let mut next : Nat := (← get).nextId
  repeat
    if (← get).ids.contains ⟨next⟩ then next := next + 1
    else break
  let i := ⟨next⟩
  modify fun st => {st with ids := st.ids.insert i}
  pure i

def freshTag [Monad m] [MonadStateOf TraverseState m] (hint : String) (id : InternalId) : m Tag := do
  let strPart : String := hint.sluggify.toString
  let mut numPart : Option Nat := none
  repeat
    let attempt := tagStr strPart numPart
    if (← get).tags.contains  attempt then
      numPart := some <| numPart.map (· + 1) |>.getD 0
    else break
  let tag := tagStr strPart numPart
  modify fun st => {st with tags := st.tags.insert tag id}
  pure tag
where
  tagStr (strPart : String) (numPart : Option Nat) := Tag.internal s!"{strPart}{numPart.map (s!"-{·}") |>.getD ""}"

defmethod HashMap.all [BEq α] [Hashable α] (hm : HashMap α β) (p : α → β → Bool) : Bool :=
  hm.fold (fun prev k v => prev && p k v) true

instance [BEq α] [Hashable α] : BEq (HashSet α) where
  beq xs ys := xs.size == ys.size && xs.all (ys.contains ·)

instance : BEq TraverseState where
  beq x y :=
    x.tags.size == y.tags.size &&
    (x.tags.all fun k v =>
      match y.tags[k]? with
      | none => false
      | some v' => v == v'
    ) &&
    x.externalTags.size == y.externalTags.size &&
    (x.externalTags.all fun k v =>
      match y.externalTags[k]? with
      | none => false
      | some v' => v == v'
    ) &&
    x.ids == y.ids &&
    x.nextId == y.nextId &&
    x.extraCss == y.extraCss &&
    x.extraJs == y.extraJs &&
    x.extraJsFiles == y.extraJsFiles &&
    x.extraCssFiles == y.extraCssFiles &&
    x.contents.size == y.contents.size &&
    x.contents.all fun k v =>
      match y.contents.find? k with
      | none => false
      | some v' => v == v'

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

end TraverseState


structure Block where
  name : Name
  id : Option InternalId := none
  data : Json := Json.null
deriving BEq, Hashable, ToJson, FromJson

structure Inline where
  name : Name
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

structure InlineDescr where
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

  toTeX : Option (InlineToTeX Manual (ReaderT ExtensionImpls IO))

deriving TypeName, Inhabited

structure BlockDescr where
  traverse : BlockTraversal Manual

  toHtml : Option (BlockToHtml Manual (ReaderT ExtensionImpls IO))
  extraJs : List String := []
  extraJsFiles : List (String × String) := []
  extraCss : List String := []
  extraCssFiles : List (String × String) := []

  toTeX : Option (BlockToTeX Manual (ReaderT ExtensionImpls IO))
deriving TypeName, Inhabited

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

def externalTag [Monad m] [MonadState TraverseState m] (id : InternalId) (path : Path) (name : String) : m Tag := do
  if let some (_, t) := (← get).externalTags[id]? then
    return Tag.external t
  else
    let mut attempt := name.sluggify.toString
    repeat
      if (← get).tags.contains (Tag.external attempt) then attempt := attempt ++ "-next"
      else break
    let t' := Tag.external attempt
    modify fun st => {st with
      tags := st.tags.insert t' id,
      externalTags := st.externalTags.insert id (path, attempt)
    }
    pure t'

def TraverseState.resolveId (st : TraverseState) (id : InternalId) : Option (Path × String) :=
  if let some x := st.externalTags[id]? then
      pure x
  else none

def TraverseState.resolveDomainObject (st : TraverseState) (domain : Name) (canonicalName : String) : Except String (Path × String) := do
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

def TraverseState.resolveTag (st : TraverseState) (tag : String) : Option (Path × String) :=
  if let some id := st.tags[Tag.external tag]? then
    if let some x := st.externalTags[id]? then
      pure x
    else panic! s!"No location for ID {id}, but it came from external tag '{tag}'"
  else none

def TraverseState.linkTargets (state : TraverseState) : Code.LinkTargets where
  const := fun x =>
    match state.resolveDomainObject `Verso.Manual.doc x.toString with
    | .ok (path, htmlId) =>
      path.map ("/" ++ ·) |>.toList |> (String.join · ++ "#" ++ htmlId) |> some
    | .error _ =>
      none
  option := fun x =>
    match state.resolveDomainObject `Verso.Manual.doc.option x.toString with
    | .ok (path, htmlId) =>
      path.map ("/" ++ ·) |>.toList |> (String.join · ++ "#" ++ htmlId) |> some
    | .error _ =>
      none
  keyword := fun k =>
    match state.resolveDomainObject `Verso.Manual.doc.tactic k.toString with
    | .ok (path, htmlId) =>
      path.map ("/" ++ ·) |>.toList |> (String.join · ++ "#" ++ htmlId) |> some
    | .error _ =>
      none



instance : Traverse Manual TraverseM where
  part p :=
    if p.metadata.isNone then pure (some {}) else pure none
  inPart p := (·.inPart p)
  block _ := pure ()
  inline _ := pure ()
  genrePart startMeta part := do
    let mut meta := startMeta

    -- First, assign a unique ID if there is none
    let id ← if let some i := meta.id then pure i else freshId
    meta := {meta with id := some id}

    match meta.tag with
    | none =>
      -- Assign an internal tag - the next round will make it external This is done in two rounds to
      -- give priority to user-provided tags that might otherwise anticipate the name-mangling scheme
      let what := (← read).headers.map (·.titleString ++ "--") |>.push part.titleString |>.foldl (init := "") (· ++ ·)
      let tag ← freshTag what id
      meta := {meta with tag := tag}
    | some t =>
      -- Ensure uniqueness
      if let some id' := (← get).tags[t]? then
        if id != id' then logError s!"Duplicate tag '{t}'"
      else
        modify fun st => {st with tags := st.tags.insert t id}
      let path := (← readThe TraverseContext).path
      match t with
      | Tag.external name =>
        -- These are the actual IDs to use in generated HTML and links and such
        modify fun st => {st with externalTags := st.externalTags.insert id (path, name)}
        let jsonMetadata := Json.arr ((← read).inPart part |>.headers.map (Json.str ·.titleString))
        modify (·.saveDomainObject `Verso.Genre.Manual.section name id
                 |>.saveDomainObjectData `Verso.Genre.Manual.section name jsonMetadata)
      | Tag.internal name =>
        meta := {meta with tag := ← externalTag id path name}
      | Tag.provided n =>
        -- Convert to an external tag, and fail if we can't (users should control their link IDs)
        let external := Tag.external n.toString
        if let some id' := (← get).tags[external]? then
          if id != id' then logError s!"Duplicate tag '{t}'"
        else
          modify fun st => {st with
              tags := st.tags.insert external id,
              externalTags := st.externalTags.insert id (path, n.toString)
            }
          meta := {meta with tag := external}

    pure <|
      if meta == startMeta then none
      else pure (part.withMetadata meta)

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
      | panic! s!"Unknown block {b.name} while rendering"
    let some impl := descr.toTeX
      | panic! s!"Block {b.name} doesn't support TeX"
    impl goI goB id b.data content
  inline go i content := do
    let some id := i.id
      | panic! "Inline {i.name} wasn't assigned an ID during traversal"
    let some descr := (← readThe ExtensionImpls).getInline? i.name
      | panic! s!"Unknown inline {i.name} while rendering"
    let some impl := descr.toTeX
      | panic! s!"Inline {i.name} doesn't support TeX"
    impl go id i.data content

open Verso.Output.Html in
instance : Html.GenreHtml Manual (ReaderT ExtensionImpls IO) where
  part go meta txt := do
    let st ← Verso.Doc.Html.HtmlT.state
    let attrs := match meta.id >>= st.externalTags.get? with
      | none => #[]
      | some (_, t) => #[("id", t)]
    go txt attrs

  block goI goB b content := do
    let some id := b.id
      | panic! s!"Block {b.name} wasn't assigned an ID during traversal"
    let some descr := (← readThe ExtensionImpls).getBlock? b.name
      | panic! s!"Unknown block {b.name} while rendering"
    let some impl := descr.toHtml
      | panic! s!"Block {b.name} doesn't support HTML"
    impl goI goB id b.data content

  inline go i content := do
    let some id := i.id
      | panic! "Inline {i.name} wasn't assigned an ID during traversal"
    let some descr := (← readThe ExtensionImpls).getInline? i.name
      | panic! s!"Unknown inline {i.name} while rendering"
    let some impl := descr.toHtml
      | panic! s!"Inline {i.name} doesn't support HTML"
    impl go id i.data content
