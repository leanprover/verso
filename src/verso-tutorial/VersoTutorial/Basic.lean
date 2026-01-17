/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import MultiVerso
import Verso.Doc
import VersoManual.Basic
import VersoManual
import Lean.Data.Json
import VersoUtil.LzCompress
import VersoUtil.Zip
import VersoBlog.Basic
import VersoBlog.Component
import VersoBlog.Template
import VersoBlog.Generate

set_option linter.missingDocs true

namespace Verso.Genre
open Lean


open Verso.Doc (Genre)
open Verso.Multi

private def defaultToolchain :=
  if Lean.versionString.find? "nightly" |>.isSome then
    "leanprover/lean4:nightly" ++ (Lean.versionString.split "nightly" |>.toArray[1]!).copy
  else
    "leanprover/lean4:" ++ Lean.versionString

private def defaultLive := "lean-v" ++ Lean.versionString

/-- A style by which example code in a tutorial should be made runnable. -/
inductive ExampleCodeStyle where
  /--
  The example code should be extracted to a Lean project from the tutorial.
  -/
  | inlineLean (moduleName : Lean.Name) (toolchain := defaultToolchain) (liveProject := some defaultLive)
deriving BEq, Hashable, DecidableEq, Inhabited, Repr, ToJson, FromJson

open Manual (Tag InternalId) in
/-- Metadata on tutorials. -/
structure Tutorial.PartMetadata where
  /-- The main tag for the part, used for cross-references. -/
  tag : Option Tag := none
  /-- Use this filename component in the URL. -/
  slug : String
  /-- The internal unique ID, which is automatically assigned during traversal. -/
  id : Option InternalId := none
  /-- A summary to show on the overview page. -/
  summary : Verso.Doc.Inline Manual
  /-- How should the code samples in this tutorial be extracted to a downloadable tarball? -/
  exampleStyle : ExampleCodeStyle
deriving BEq, Hashable, Inhabited, Repr, ToJson, FromJson

/--
Information that tracks the current context of traversal for a set of tutorials.
-/
def Tutorial.TraverseContext := Manual.TraverseContext

/--
Tutorials may use all the extensions of the manual genre, but are rendered as ordinary single web
pages via the blog genre. They may contain example code, which can be extracted and tested.
-/
def Tutorial : Genre :=
  { Manual with
    TraverseContext := Tutorial.TraverseContext
    PartMetadata := Tutorial.PartMetadata
  }

instance : Inhabited (Genre.PartMetadata Tutorial) :=
  inferInstanceAs <| Inhabited Tutorial.PartMetadata
instance : BEq (Genre.PartMetadata Tutorial) := inferInstanceAs (BEq Tutorial.PartMetadata)
instance : BEq (Genre.Block Tutorial) := inferInstanceAs (BEq Manual.Block)
instance : BEq (Genre.Inline Tutorial) := inferInstanceAs (BEq Manual.Inline)

instance : Repr (Genre.PartMetadata Tutorial) := inferInstanceAs (Repr Tutorial.PartMetadata)
instance : Repr (Genre.Block Tutorial) := inferInstanceAs (Repr Manual.Block)
instance : Repr (Genre.Inline Tutorial) := inferInstanceAs (Repr Manual.Inline)

instance : ToJson (Genre.PartMetadata Tutorial) := inferInstanceAs (ToJson Tutorial.PartMetadata)
instance : ToJson (Genre.Block Tutorial) := inferInstanceAs (ToJson Manual.Block)
instance : ToJson (Genre.Inline Tutorial) := inferInstanceAs (ToJson Manual.Inline)

instance : FromJson (Genre.PartMetadata Tutorial) := inferInstanceAs (FromJson Tutorial.PartMetadata)
instance : FromJson (Genre.Block Tutorial) := inferInstanceAs (FromJson Manual.Block)
instance : FromJson (Genre.Inline Tutorial) := inferInstanceAs (FromJson Manual.Inline)

instance : VersoLiterate.LoadLiterate Tutorial where
  inline := inst.inline
  block := inst.block
  docstring := inst.docstring
  docstringPart := inst.docstringPart

where
  inst := inferInstanceAs <| VersoLiterate.LoadLiterate Manual

namespace Tutorial

open Verso.Doc
open Manual (ExtensionImpls)

/-- The metadata to use for a tutorial when the user does not specify any. -/
def defaultMetadata (p : Part Tutorial) : Tutorial.PartMetadata :=
  { slug := p.titleString.sluggify.toString, summary := inlines!"", exampleStyle := .inlineLean `Main }

instance : TraversePart Tutorial where
  inPart p ctx :=
    let metadata := p.metadata.getD (defaultMetadata p)
    let properties := if ctx.headers.isEmpty then
      NameMap.insert {} `Verso.Genre.Manual.exampleDefContext metadata.slug
    else
      {}
    let path := if ctx.path.isEmpty then #[metadata.slug] else ctx.path
    { ctx with
      path
      headers := ctx.headers.push {
        titleString := p.titleString, metadata := none, properties
      }
    }

instance : TraverseBlock Tutorial where
  inBlock b := (·.inBlock b)

/--
Saves a cross-reference to a part to the section domain.
-/
def savePartXref (slug : Slug) (id : InternalId) (part : Part Tutorial) : Manual.TraverseM Unit := do
  let jsonMetadata :=
    Json.arr (TraversePart.inPart part (← read) |>.headers.map (fun h => json%{
      "title": $h.titleString
    }))
  let title := TraversePart.inPart part (← read) |>.headers |>.back? |>.map (·.titleString)

  modify fun (st : Manual.TraverseState) =>
    st.saveDomainObject Manual.sectionDomain slug.toString id
      |>.saveDomainObjectData Manual.sectionDomain slug.toString (json%{
        "context": $jsonMetadata,
        "title": $title,
        "shortTitle": null,
        "sectionNum": null
      })

block_extension Block.displayOnly where
  traverse _ _ _ _ := pure none
  toHtml := some <| fun _ goB _ _ content => content.mapM goB
  toTeX := some <| fun _ goB _ _ content => content.mapM goB

/-- Indicates code that is to be displayed in tutorials, but not extracted or run. -/
@[directive]
def displayOnly : Elab.DirectiveExpanderOf Unit
  | (), contents => do
    ``(Block.other Block.displayOnly #[$(← contents.mapM Elab.elabBlock),*])

block_extension Block.codeOnly where
  traverse _ _ _ _ := pure none
  toHtml := some <| fun _ _ _ _ _ => pure .empty
  toTeX := some <| fun _ _ _ _ _ => pure .empty

/-- Indicates code that is to be extracted and run from tutorials, but not rendered to HTML. -/
@[directive]
def codeOnly : Elab.DirectiveExpanderOf Unit
  | (), contents => do
    ``(Block.other Block.codeOnly #[$(← contents.mapM Elab.elabBlock),*])

section
open Verso.Code.External
instance : ExternalCode Tutorial :=
  let inst : ExternalCode Manual := inferInstance
  { inst with }
end

open Manual in
instance : Traverse Tutorial TraverseM where
  part p := do
    if p.metadata.isNone then
      pure (some (defaultMetadata p))
    else pure none
  block _ := pure ()
  inline _ := pure ()
  genrePart startMeta part := do
    let mut «meta» : Tutorial.PartMetadata := startMeta

    -- First, assign a unique ID if there is none
    let id ← if let some i := meta.id then pure i else freshId
    «meta» := { «meta» with id := some id }

    -- Next, assign a tag, prioritizing user-chosen external IDs
    «meta» := { «meta» with tag := ← withReader (TraversePart.inPart part) <| tagPart part «meta» (·.id) (·.tag) savePartXref }

    -- Traverse the metadata's description
    «meta» := { «meta» with summary := ← withReader (TraversePart.inPart part) <| Genre.traverseInline Manual «meta».summary }

    pure <|
      if «meta» == startMeta then none
      else pure { part with metadata := some «meta» }

  genreBlock := Traverse.genreBlock (g := Manual)
  genreInline := Traverse.genreInline (g := Manual)

/-- A tutorial topic. Tutorials are sorted into topics. -/
structure Topic where
  /-- The title of the topic, rendered as a header. -/
  title : Array (Inline Blog.Page)
  /-- The title of the topic, in string form. -/
  titleString : String
  /-- Descriptive text to be shown for the topic. -/
  description : Array (Block Blog.Page)
  /-- The tutorials contained in the topic. -/
  tutorials : Array (Part Tutorial)
deriving BEq, ToJson, FromJson

/--
A collection of tutorials, organized by topic.
-/
structure Tutorials : Type where
  /-- The content to show on the page prior to the tutorials, if any. -/
  content : Part Blog.Page
  /-- The tutorial topics that are present. -/
  topics : Array Topic
deriving BEq, ToJson, FromJson

/-- Performs one step of the traversal pass for tutorials. -/
def Tutorials.traverse1  (traversal : Part Tutorial → Manual.TraverseM (Part Tutorial)) (tutorials : Tutorials) : Manual.TraverseM Tutorials := do
  let { content, topics } := tutorials
  return {
    content,
    topics := ← topics.mapM fun topic => do
      return { topic with
        tutorials := ← topic.tutorials.mapM fun tut => do
          let tut := { tut with metadata := tut.metadata.getD (defaultMetadata tut) }
          withReader (TraversePart.inPart tut) <| traversal tut
      }
  }

open Manual in
/--
Performs the traversal pass for tutorials until a fixed point is reached or `config.maxTraversals`
passes have been run.
-/
def traverse (logError : String → IO Unit) (tutorials : Tutorials) (config : Manual.Config) : ReaderT ExtensionImpls IO (Tutorials × Manual.TraverseState) := do
  let topCtxt : Manual.TraverseContext := {logError, draft := config.draft}
  let mut state : Manual.TraverseState := .ofConfig ({ config with features := {} }).toHtmlConfig
  let mut tutorials := tutorials
  if config.verbose then
    IO.println "Initializing extensions"
  let extensionImpls ← readThe ExtensionImpls
  state := state
    |>.setDomainTitle sectionDomain "Sections or chapters of the manual"
    |>.addQuickJumpMapper sectionDomain Manual.sectionDomainMapper
  for ⟨_, b⟩ in extensionImpls.blockDescrs do
    if let some descr := b.get? BlockDescr then
      state := descr.init state
  for ⟨_, i⟩ in extensionImpls.inlineDescrs do
    if let some descr := i.get? InlineDescr then
      state := descr.init state
  for i in [0:config.maxTraversals] do
    dbg_trace "traversal {i}"
    if config.verbose then
      IO.println s!"Traversal pass {i}"
    let startTime ← IO.monoMsNow
    let (tutorials', state') ← tutorials.traverse1 (Genre.traverse Tutorial) |>.run extensionImpls topCtxt state

    let endTime ← IO.monoMsNow
    if config.verbose then
      IO.println s!"  ... pass {i} completed in {endTime - startTime} ms"
    if tutorials' == tutorials && state' == state then
      return (tutorials', state')
    else
      state := state'
      tutorials := tutorials'
  return (tutorials, state)
