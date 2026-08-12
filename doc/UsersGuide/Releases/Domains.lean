/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import VersoManual
public import UsersGuide.Releases.Entry

set_option doc.verso true

public section

namespace UsersGuide.Releases

open Verso Doc Genre Manual
open Lean

/-- The domain that holds one object per release note entry. -/
def entryDomain : Name := `UsersGuide.Releases.entry

/-- The domain that holds one object per release. -/
def versionDomain : Name := `UsersGuide.Releases.version

open Verso.Search in
/-- Presents release note entries in the search interface, keyed by version and title. -/
def entryDomainMapper : DomainMapper where
  displayName := "Verso Release Note"
  className := "release-note-domain"
  dataToSearchables :=
    "(domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => ({
      searchKey: `${value[0].data.version} ${value[0].data.title}`,
      address: `${value[0].address}#${value[0].id}`,
      domainId: 'UsersGuide.Releases.entry',
      ref: value,
      priority: value[0].data.searchPriority ?? 50,
    }))"

open Verso.Search in
/-- Presents whole releases in the search interface, keyed by version number. -/
def versionDomainMapper : DomainMapper := {
  displayName := "Verso Release",
  className := "release-domain",
  dataToSearchables :=
    "(domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => ({
      searchKey: value[0].data.title,
      address: `${value[0].address}#${value[0].id}`,
      domainId: 'UsersGuide.Releases.version',
      ref: value,
      priority: value[0].data.searchPriority ?? 50,
    }))"
  : DomainMapper }.setFont { family := .structure, weight := .bold }

/--
What a release note entry block carries: the tag that is the basis of its permalink, and the
version, title and pull requests to show for it in search results.
-/
structure EntryInfo where
  /--
  The tag the author chose, when this block is what it names. An entry that becomes a section
  leaves the tag to the section, and its summary takes a machine-assigned one.
  -/
  tag : Option String
  title : String
  version : Version
  prs : List Nat
deriving ToJson, FromJson

/--
What a release block carries: the tag that is the basis of its permalink, and the version and
title to show for it in search results.
-/
structure ReleaseInfo where
  title : String
  version : Version
deriving ToJson, FromJson

/--
Saves a domain object under {name}`canonicalName` for the block with the given internal ID, and
assigns it an external tag based on {name}`tag`.

The domain object is what the search interface offers, and what {lit}`{ref}` resolves when given
this domain. The external tag is what gives the block its HTML {lit}`id`, and so the permalink
that readers share.
-/
def saveObject
    (domain : Name) (id : InternalId) (canonicalName : String) (tag : Option String)
    (fields : List (String × Json)) :
    ReaderT TraverseContext (StateT TraverseState (BuildLogT IO)) (Option Tag) := do
  let ctx ← readThe TraverseContext
  -- A tag the author chose is theirs exactly; one this file invents is left to be made unique.
  let assigned? ←
    match tag with
    | some name => providedTag id ctx.path name
    | .none => some <$> externalTag id ctx.path s!"--release-note-{canonicalName}"
  -- The tag could not be assigned and the error is already reported. Saving a domain object now
  -- would point it at an element that has no link.
  let some assigned := assigned? | return Option.none
  let context := Json.arr <| ctx.headers.map fun h =>
    Json.mkObj [
      ("title", toJson h.titleString),
      ("shortTitle", toJson (h.metadata.bind (·.shortTitle))),
      ("number", toJson (h.metadata.bind (·.assignedNumber) |>.map toString))
    ]
  let data := Json.mkObj <|
    fields ++ [
      ("searchPriority", toJson (ancestorSearchPriority ctx.headers)),
      ("context", context)
    ]
  modify fun st =>
    st.saveDomainObject domain canonicalName id |>.saveDomainObjectData domain canonicalName data
  return some assigned

/-- Saves a release note entry in {name}`entryDomain`. -/
def saveEntry
    (id : InternalId) (canonicalName : String) (info : EntryInfo) :
    ReaderT TraverseContext (StateT TraverseState (BuildLogT IO)) (Option Tag) :=
  saveObject entryDomain id canonicalName info.tag [
    ("title", toJson info.title),
    ("version", toJson (toString info.version)),
    ("prs", toJson info.prs)
  ]

/-- Saves a release in {name}`versionDomain`. -/
def saveRelease
    (id : InternalId) (canonicalName : String) (info : ReleaseInfo) :
    ReaderT TraverseContext (StateT TraverseState (BuildLogT IO)) (Option Tag) :=
  saveObject versionDomain id canonicalName Option.none [
    ("title", toJson info.title),
    ("version", toJson (toString info.version))
  ]

/-
Saves a release note entry's summary in the entry domain and gives it a permalink.

The assigned tag is written back into the block, so that later traversal rounds have nothing to do.
-/
block_extension Block.entry
    (canonicalName : String) (info : EntryInfo) (assignedTag : Option Tag := none) where
  data := ToJson.toJson (canonicalName, info, assignedTag)
  init st :=
    st.setDomainTitle entryDomain "Individual changes in a release"
      |>.addQuickJumpMapper entryDomain entryDomainMapper
  traverse := fun id data contents => do
    match FromJson.fromJson? data (α := String × EntryInfo × Option Tag) with
    | .error e =>
      reportError s!"Couldn't decode release note entry data: {e}"
      return none
    | .ok (_, _, some _) => return none
    | .ok (canonicalName, info, Option.none) =>
      let some tag ← saveEntry id canonicalName info
        | return none
      return some <|
        Verso.Doc.Block.other
          {Block.entry canonicalName info (assignedTag := some tag) with id := some id} contents
  toHtml :=
    open Verso.Output.Html in
    some <| fun _goI goB id _data contents => do
      let some link := (← read).traverseState.externalTags[id]?
        | reportError "Release note entry without an assigned tag"
          return .seq (← contents.mapM goB)
      pure {{<div id={{link.htmlId.toString}}>{{← contents.mapM goB}}</div>}}
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _goI goB id _data contents => do
      let label? := (← Doc.TeX.state).externalTags[id]?.map (labelForTeX ·.htmlId)
      let marker : Verso.Output.TeX :=
        match label? with
        | Option.some l => .raw s!"\\phantomsection\\label\{{l}}\n"
        | Option.none => .empty
      pure <| .seq (#[marker] ++ (← contents.mapM goB))

/-
Saves a release in the version domain. The version's section supplies the heading and the
permalink that readers share, so this carries no visible content of its own.
-/
block_extension Block.release
    (canonicalName : String) (info : ReleaseInfo) (assignedTag : Option Tag := none) where
  data := ToJson.toJson (canonicalName, info, assignedTag)
  init st :=
    st.setDomainTitle versionDomain "Releases of Verso"
      |>.addQuickJumpMapper versionDomain versionDomainMapper
  traverse := fun id data contents => do
    match FromJson.fromJson? data (α := String × ReleaseInfo × Option Tag) with
    | .error e =>
      reportError s!"Couldn't decode release data: {e}"
      return none
    | .ok (_, _, some _) => return none
    | .ok (canonicalName, info, Option.none) =>
      let some tag ← saveRelease id canonicalName info
        | return none
      return some <|
        Verso.Doc.Block.other
          {Block.release canonicalName info (assignedTag := some tag) with id := some id} contents
  toHtml :=
    open Verso.Output.Html in
    some <| fun _goI _goB id _data _contents => do
      let some link := (← read).traverseState.externalTags[id]?
        | reportError "Release without an assigned tag"
          return .empty
      pure {{<span id={{link.htmlId.toString}}></span>}}
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _goI _goB id _data _contents => do
      let label? := (← Doc.TeX.state).externalTags[id]?.map (labelForTeX ·.htmlId)
      pure <|
        match label? with
        | Option.some l => .raw s!"\\phantomsection\\label\{{l}}\n"
        | Option.none => .empty

end UsersGuide.Releases
