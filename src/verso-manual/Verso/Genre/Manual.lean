/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Doc
import Verso.Doc.Concrete
import Verso.Doc.TeX
import Verso.Doc.Html
import Verso.Output.TeX
import Verso.Output.Html
import Verso.Doc.Lsp
import Verso.Doc.Elab

import Verso.Genre.Manual.Slug
import Verso.Genre.Manual.TeX
import Verso.Genre.Manual.Html
import Verso.Genre.Manual.Html.Style

open Lean (Name NameMap Json ToJson FromJson)

open Verso.Doc Elab

open Verso.Genre.Manual.TeX

namespace Verso.Genre

namespace Manual

inductive Output where
  | /-- LaTeX -/
    tex
  | /-- HTML - one page per part at the given depth -/
    html (depth : Nat)
deriving DecidableEq, BEq, Hashable

abbrev Path := Array String


/--
Tags are used to refer to parts through tables of contents, cross-references,
and the like.

During the traverse pass, the following steps occur:
 1. user-provided tags are ensured to be globally unique, and saved as xref targets
 2. internal tags are heuristically assigned to parts based on their section
    names
 3. internal tags are converted to unique external tags, but not provided for
    user-written xrefs (needed for automatic linking, e.g. in a table of
    contents)
-/
inductive PartTag where
  | /-- A user-provided tag - respect this if possible -/ provided (name : String)
  | /-- A unique tag, suitable for inclusion in a document -/ private external (name : String)
  | /-- A machine-assigned tag -/ private internal (name : String)
deriving BEq, Hashable, Repr

instance : ToString PartTag where
  toString := toString ∘ repr

instance : Coe String PartTag where
  coe := .provided

/-- An internal identifier assigned to a part during traversal. Users don't get to have influence
  over these IDs, so they can be used to ensure uniqueness of tags.-/
structure InternalId where
  private mk ::
  private id : Nat
deriving BEq, Hashable, Repr

instance : ToString InternalId where
  toString x := s!"#<{x.id}>"

structure PartMetadata where
  authors : List String := []
  date : Option String := none
  tag : Option PartTag := none
  id : Option InternalId := none
  number : Bool := true
deriving BEq, Hashable, Repr

structure Block where
  name : Name
  data : Json := Json.null
deriving BEq

def Block.paragraph : Block where
  name := `Verso.Genre.Manual.Block.paragraph

structure Inline where
  name : Name
  data : Json := Json.null
deriving BEq


instance : BEq Empty where
  beq := nofun

structure TraverseState where
  partTags : Lean.HashMap PartTag InternalId := {}
  externalTags : Lean.HashMap InternalId String := {}
  slugs : Lean.HashMap Slug Path := {}
  ids : Lean.HashSet InternalId := {}
  nextId : Nat := 0
  private contents : NameMap Json := {}

def freshId [Monad m] [MonadStateOf TraverseState m] : m InternalId := do
  let mut next : Nat := (← get).nextId
  repeat
    if (← get).ids.contains ⟨next⟩ then next := next + 1
    else break
  let i := ⟨next⟩
  modify fun st => {st with ids := st.ids.insert i}
  pure i

def freshTag [Monad m] [MonadStateOf TraverseState m] (hint : String) (id : InternalId) : m PartTag := do
  let mut next : String := s!"--part-{hint.sluggify.toString}-{id.id}"
  repeat
    if (← get).partTags.contains next then next := next ++ "-retry"
    else break
  let tag := PartTag.internal next
  modify fun st => {st with partTags := st.partTags.insert tag id}
  pure tag

defmethod Lean.HashMap.all [BEq α] [Hashable α] (hm : Lean.HashMap α β) (p : α → β → Bool) : Bool :=
  hm.fold (fun prev k v => prev && p k v) true

defmethod Lean.HashSet.all [BEq α] [Hashable α] (hm : Lean.HashSet α) (p : α → Bool) : Bool :=
  hm.fold (fun prev v => prev && p v) true

instance [BEq α] [Hashable α] : BEq (Lean.HashSet α) where
  beq xs ys := xs.size == ys.size && xs.all (ys.contains ·)

instance : BEq TraverseState where
  beq x y :=
    x.partTags.size == y.partTags.size &&
    (x.partTags.all fun k v =>
      match y.partTags.find? k with
      | none => false
      | some v' => v == v'
    ) &&
    x.slugs.size == y.slugs.size &&
    (x.slugs.all fun k v =>
      match y.slugs.find? k with
      | none => false
      | some v' => v == v'
    ) &&
    x.ids == y.ids &&
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

end TraverseState

structure TraverseContext where
  /-- The current URL path - will be [] for non-HTML output or in the root -/
  path : Path := #[]
  logError : String → IO Unit

def TraverseContext.inFile (self : TraverseContext) (file : String) : TraverseContext :=
  {self with path := self.path.push file}

abbrev BlockTraversal genre :=
  Json → Array (Doc.Block genre) →
  ReaderT TraverseContext (StateT TraverseState IO) (Option (Doc.Block genre))

abbrev BlockToHtml (genre : Genre) (m) :=
  (Doc.Block genre → Html.HtmlT genre m Output.Html) →
    Json → Array (Doc.Block genre) → Html.HtmlT genre m Output.Html

abbrev BlockToTeX (genre : Genre) (m) :=
  (Doc.Block genre → TeX.TeXT genre m Output.TeX) →
    Json → Array (Doc.Block genre) → TeX.TeXT genre m Output.TeX

abbrev InlineTraversal genre :=
  Json → Array (Doc.Inline genre) →
  ReaderT TraverseContext (StateT TraverseState IO) (Option (Doc.Inline genre))

abbrev InlineToHtml (genre : Genre) (m) :=
  (Doc.Inline genre → Html.HtmlT genre m Output.Html) →
    Json → Array (Doc.Inline genre) → Html.HtmlT genre m Output.Html

abbrev InlineToTeX (genre : Genre) (m) :=
  (Doc.Inline genre → TeX.TeXT genre m Output.TeX) →
    Json → Array (Doc.Inline genre) → TeX.TeXT genre m Output.TeX

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

instance : Repr (Genre.PartMetadata Manual) := inferInstanceAs (Repr Manual.PartMetadata)

namespace Manual

structure ExtensionImpls where
  private mk ::
  -- This is to work around recursion restrictions, not for real dynamism
  inlineDescrs : NameMap Dynamic
  blockDescrs : NameMap Dynamic

structure InlineDescr where
  traverse : InlineTraversal Manual
  toHtml : Option (InlineToHtml Manual (ReaderT ExtensionImpls IO))
  toTeX : Option (InlineToTeX Manual (ReaderT ExtensionImpls IO))
deriving TypeName, Inhabited

structure BlockDescr where
  traverse : BlockTraversal Manual
  toHtml : Option (BlockToHtml Manual (ReaderT ExtensionImpls IO))
  toTeX : Option (BlockToTeX Manual (ReaderT ExtensionImpls IO))
deriving TypeName, Inhabited

private def fromDynamic! (dyn : Dynamic) : BlockDescr :=
  dyn.get? BlockDescr |>.get!

def ExtensionImpls.empty : ExtensionImpls := ⟨{}, {}⟩

instance : EmptyCollection ExtensionImpls where
  emptyCollection := .empty

def ExtensionImpls.getInline? (impls : ExtensionImpls) (name : Name) : Option InlineDescr :=
  impls.blockDescrs.find? name |>.map (·.get? InlineDescr |>.get!)

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

def paragraph.descr : BlockDescr where
  traverse := fun _ _ => pure none
  toTeX :=
    some <| fun go _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun go _ content => do
      pure <| {{<div class="paragraph">{{← content.mapM go}}</div>}}

abbrev TraverseM := ReaderT ExtensionImpls (ReaderT Manual.TraverseContext (StateT Manual.TraverseState IO))

def TraverseM.run
    (impls : ExtensionImpls)
    (ctxt : Manual.TraverseContext)
    (state : Manual.TraverseState)
    (act : TraverseM α) : IO (α × Manual.TraverseState) :=
  act impls ctxt state

instance : MonadReader Manual.TraverseContext TraverseM where
  read := readThe _

def logError (err : String) : TraverseM Unit := do
  (← readThe Manual.TraverseContext).logError err

instance : Traverse Manual TraverseM where
  part p :=
    if p.metadata.isNone then pure (some {}) else pure none
  block _ := pure ()
  inline _ := pure ()
  genrePart startMeta part := do
    let mut meta := startMeta

    -- First, assign a unique ID if there is none
    let id ← if let some i := meta.id then pure i else
      freshId
    meta := {meta with id := some id}

    match meta.tag with
    | none =>
      -- Assign an internal tag - the next round will make it external This is done in two rounds to
      -- give priority to user-provided tags that might otherwise anticipate the name-mangling scheme
      let tag ← freshTag part.titleString id
      meta := {meta with tag := tag}
    | some t =>
      -- Ensure uniqueness
      if let some id' := (← get).partTags.find? t then
        if id != id' then logError s!"Duplicate tag '{t}'"
      else
        modify fun st => {st with partTags := st.partTags.insert t id}
      match t with
      | PartTag.external name =>
        -- These are the actual IDs to use in generated HTML and links and such
        modify fun st => {st with externalTags := st.externalTags.insert id name}
      | PartTag.internal name =>
        let mut attempt := name
        repeat
          if (← get).partTags.contains (PartTag.external attempt) then attempt := attempt ++ "-next"
          else break
        let t' := PartTag.external attempt
        modify fun st => {st with partTags := st.partTags.insert t' id}
        meta := {meta with tag := t'}
      | PartTag.provided n =>
        -- Convert to an external tag, and fail if we can't (users should control their link IDs)
        let external := PartTag.external n
        if let some id' := (← get).partTags.find? external then
          if id != id' then logError s!"Duplicate tag '{t}'"
        else
          modify fun st => {st with partTags := st.partTags.insert external id}
          meta := {meta with tag := external}

    pure <|
      if meta == startMeta then none
      else pure (part.withMetadata meta)

  genreBlock
    | ⟨name, data⟩, content => do
      if let some impl := (← readThe ExtensionImpls).getBlock? name then
        impl.traverse data content
      else
        logError s!"No block traversal implementation found for {name}"
        pure none
  genreInline
    | ⟨name, data⟩, content => do
      if let some impl := (← readThe ExtensionImpls).getInline? name then
        impl.traverse data content
      else
        logError s!"No inline traversal implementation found for {name}"
        pure none

open Verso.Output.TeX in
instance : TeX.GenreTeX Manual (ReaderT ExtensionImpls IO) where
  part go _meta txt := go txt
  block go b content := do
    let some descr := (← readThe ExtensionImpls).getBlock? b.name
      | panic! s!"Unknown block {b.name} while rendering"
    let some impl := descr.toTeX
      | panic! s!"Block {b.name} doesn't support TeX"
    impl go b.data content
  inline go i content := do
    let some descr := (← readThe ExtensionImpls).getInline? i.name
      | panic! s!"Unknown inline {i.name} while rendering"
    let some impl := descr.toTeX
      | panic! s!"Inline {i.name} doesn't support TeX"
    impl go i.data content

open Verso.Output.Html in
instance : Html.GenreHtml Manual (ReaderT ExtensionImpls IO) where
  part go meta txt := do
    let st ← Verso.Doc.Html.HtmlT.state
    let attrs := match meta.id >>= st.externalTags.find? with
      | none => #[]
      | some t => #[("id", t)]
    go txt attrs

  block go b content := do
    let some descr := (← readThe ExtensionImpls).getBlock? b.name
      | panic! "Unknown block {b.name} while rendering"
    let some impl := descr.toHtml
      | panic! "Block {b.name} doesn't support HTML"
    impl go b.data content

  inline go i content := do
    let some descr := (← readThe ExtensionImpls).getInline? i.name
      | panic! s!"Unknown inline {i.name} while rendering"
    let some impl := descr.toHtml
      | panic! s!"Inline {i.name} doesn't support HTML"
    impl go i.data content

@[directive_expander paragraph]
def paragraph : DirectiveExpander
  | #[], stxs => do
    let args ← stxs.mapM elabBlock
    let val ← ``(Block.other Block.paragraph #[ $[ $args ],* ])
    pure #[val]
  | _, _ => Lean.Elab.throwUnsupportedSyntax


structure Config where
  destination : System.FilePath := "_out"
  maxTraversals : Nat := 20

def ensureDir (dir : System.FilePath) : IO Unit := do
  if !(← dir.pathExists) then
    IO.FS.createDirAll dir
  if !(← dir.isDir) then
    throw (↑ s!"Not a directory: {dir}")

def traverse (logError : String → IO Unit) (text : Part Manual) (config : Config) : ReaderT ExtensionImpls IO (Part Manual × TraverseState) := do
  let topCtxt : Manual.TraverseContext := {logError}
  let mut state : Manual.TraverseState := {}
  let mut text := text
  let ExtensionImpls ← readThe ExtensionImpls
  for _ in [0:config.maxTraversals] do
    let (text', state') ← Genre.traverse Manual text |>.run ExtensionImpls topCtxt state
    if text' == text && state' == state then
      return (text', state')
    else
      state := state'
      text := text'
  return (text, state)


open IO.FS in
def emitTeX (logError : String → IO Unit) (config : Config) (state : TraverseState) (text : Part Manual) : ReaderT ExtensionImpls IO Unit := do
  let opts : TeX.Options Manual (ReaderT ExtensionImpls IO) := {
    headerLevels := #["chapter", "section", "subsection", "subsubsection", "paragraph"],
    headerLevel := some ⟨0, by simp_arith [Array.size, List.length]⟩,
    logError := fun msg => logError msg
  }
  let authors := text.metadata.map (·.authors) |>.getD []
  let date := text.metadata.bind (·.date) |>.getD ""
  let ctxt := {logError}
  let frontMatter ← text.content.mapM (·.toTeX (opts, ctxt, state))
  let chapters ← text.subParts.mapM (·.toTeX (opts, ctxt, state))
  let dir := config.destination.join "tex"
  ensureDir dir
  withFile (dir.join "main.tex") .write fun h => do
    h.putStrLn (preamble text.titleString authors date)
    for b in frontMatter do
      h.putStrLn b.asString
    for c in chapters do
      h.putStrLn c.asString
    h.putStrLn postamble

open Verso.Output (Html)

partial def toc (opts : Html.Options Manual (ReaderT ExtensionImpls IO)) (ctxt : TraverseContext) (state : TraverseState) : Part Manual → ReaderT ExtensionImpls IO Html.Toc
  | .mk title sTitle meta _ sub => do
    let titleHtml ← Html.seq <$> title.mapM (Manual.toHtml opts.lift ctxt state)
    let some {id := some id, number, ..} := meta
      | throw <| .userError s!"No ID for {sTitle} - {repr meta}"
    let some v := state.externalTags.find? id
      | throw <| .userError s!"No external ID for {sTitle}"
    let children ← sub.mapM (toc  opts ctxt state)
    pure <| .entry titleHtml v number children

def emitHtmlSingle (logError : String → IO Unit) (config : Config) (state : TraverseState) (text : Part Manual) : ReaderT ExtensionImpls IO Unit := do
  let authors := text.metadata.map (·.authors) |>.getD []
  let date := text.metadata.bind (·.date) |>.getD ""
  let opts := {logError := fun msg => logError msg}
  let ctxt := {logError}
  let titleHtml ← Html.seq <$> text.title.mapM (Manual.toHtml opts ctxt state)
  let introHtml ← Html.seq <$> text.content.mapM (Manual.toHtml opts ctxt state)
  let contents ← Html.seq <$> text.subParts.mapM (Manual.toHtml {opts with headerLevel := 2} ctxt state)
  let pageContent := open Verso.Output.Html in
    {{<section>{{Html.titlePage titleHtml authors introHtml ++ contents}}</section>}}
  let toc ← text.subParts.mapM (toc opts ctxt state)
  let dir := config.destination.join "html-single"
  ensureDir dir
  IO.FS.withFile (dir.join "book.css") .write fun h => do
    h.putStrLn Html.Css.pageStyle
  IO.FS.withFile (dir.join "index.html") .write fun h => do
    h.putStrLn Html.doctype
    h.putStrLn (Html.page toc text.titleString pageContent).asString


def manualMain (extensionImpls : ExtensionImpls) (text : Part Manual) (options : List String) : IO UInt32 := (ReaderT.run · extensionImpls) do
  let hasError ← IO.mkRef false
  let logError msg := do hasError.set true; IO.eprintln msg
  let cfg ← opts {} options
  let (text, state) ← traverse logError text cfg
  emitTeX logError cfg state text
  emitHtmlSingle logError cfg state text

  if (← hasError.get) then
    IO.eprintln "Errors were encountered!"
    return 1
  else
    return 0
where
  opts (cfg : Config)
    | ("--output"::dir::more) => opts {cfg with destination := dir} more
    | (other :: _) => throw (↑ s!"Unknown option {other}")
    | [] => pure cfg
