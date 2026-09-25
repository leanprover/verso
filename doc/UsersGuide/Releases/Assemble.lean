/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry
public import UsersGuide.Releases.Domains
meta import all UsersGuide.Releases.Entry
meta import all UsersGuide.Releases.Domains
meta import all VersoManual

set_option doc.verso true

namespace UsersGuide.Releases

open Verso Doc Genre

/-- Where an entry's pull requests are linked from. -/
public def pullRequestUrl (pr : Nat) : String :=
  s!"https://github.com/leanprover/verso/pull/{pr}"

/-- Marks the summary of an entry that describes a breaking change. -/
public def breakingMarker (breaking : Bool) : Array (Doc.Inline Manual) :=
  if breaking then #[Inline.bold #[Inline.text "Breaking change:"], Inline.text " "] else #[]

/-- Renders an entry's pull requests as trailing links on its summary. -/
public def pullRequestLinks (prs : List Nat) : Array (Doc.Inline Manual) :=
  if prs.isEmpty then #[]
  else
    let links := prs.toArray.mapIdx fun i pr =>
      let link := Inline.link #[Inline.text s!"#{pr}"] (pullRequestUrl pr)
      if i == 0 then #[link] else #[Inline.text ", ", link]
    #[Inline.text " ("] ++ links.flatten ++ #[Inline.text ")"]

/--
What is wrong with an entry, if anything.

This is reported while the release notes are assembled, so a mistake is a build error.
-/
public def entryProblem? (entry : Part Manual) : Option String :=
  match entry.content[0]? with
  | some (Block.para _) => none
  | some _ =>
    some s!"The release note entry '{entry.titleString}' opens with a block that is not a \
      paragraph. Its first paragraph is its summary in the list of changes."
  | Option.none =>
    some s!"The release note entry '{entry.titleString}' has no opening paragraph. Its first \
      paragraph is its summary in the list of changes."

/-- Everything wrong with the entries, named by the module each problem is in. -/
public def problems (entries : Array (Lean.Name × EntryMetadata × VersoDoc Manual)) : Array String :=
  entries.filterMap fun (mod, _, doc) =>
    (entryProblem? doc.toPart).map (s!"{mod}: {·}")

/--
An entry's summary: its opening paragraph, marked when it describes a breaking change and followed
by links to its pull requests.

{name}`entryProblem?` rejects an entry with no opening paragraph while the chapter is elaborated,
so the empty summary here is unreachable in a document that builds.
-/
public def summary (metadata : EntryMetadata) (entry : Part Manual) : Doc.Block Manual :=
  let contents :=
    match entry.content[0]? with
    | some (Block.para cs) => cs
    | _ => #[]
  Block.para (breakingMarker metadata.breaking ++ contents ++ pullRequestLinks metadata.prs)

/-- Whether an entry says more than its summary, and so becomes a section of its own. -/
public def hasSection (entry : Part Manual) : Bool :=
  entry.content.size > 1 || !entry.subParts.isEmpty

/--
Assembles the entries that describe a single version into a section of the release notes.

The first paragraph of each entry is its summary in the version's list of changes. Entries that
have more to say than their summary additionally become subsections, headed by the entry's title.
-/
public def bucket
    (version : Version) (inDevelopment : Bool) (entries : Array (EntryMetadata × Part Manual)) :
    Option (Part Manual) :=
  if entries.isEmpty then none
  else
    let title := s!"Verso {version}" ++ (if inDevelopment then " (in development)" else "")
    let tag := s!"release-v{version}"
    let summaries := entries.map fun (metadata, entry) =>
      -- A section claims the author's tag, so its summary takes a machine-assigned one.
      let tag := if hasSection entry then Option.none else some metadata.tag
      ListItem.mk #[Doc.Block.other
        (Block.entry metadata.tag {
          tag, prs := metadata.prs, title := entry.titleString, version
        })
        #[summary metadata entry]]
    let sections := entries.filterMap fun (metadata, entry) =>
      if hasSection entry then
        -- The entry's own metadata is kept; only its permalink comes from the release note.
        some { entry with
          metadata := some { entry.metadata.getD {} with tag := some metadata.tag },
          content := entry.content.extract 1 }
      else none
    some <| Part.mk
      #[Inline.text title]
      title
      (some { tag := some tag })
      #[ Doc.Block.other
           (Block.release (toString version) { title, version })
           #[],
         Block.ul summaries ]
      sections

/--
Appends a section for each version described by the entries to the release notes chapter, newest
version first.
-/
public def chapter
    (intro : VersoDoc Manual) (entries : Array (EntryMetadata × VersoDoc Manual))
    (inDevelopment : Version) :
    VersoDoc Manual :=
  let intro := intro.toPart
  let entries := entries.map fun (metadata, doc) => (metadata, doc.toPart)
  let versions := entries.map (·.1.version)
  let versions := versions.foldl (init := #[]) fun vs v => if vs.contains v then vs else vs.push v
  let buckets := versions.qsort (compare · · == .gt) |>.filterMap fun version =>
    bucket version (version == inDevelopment) (entries.filter (·.1.version == version))
  .mk (fun _ => { intro with subParts := intro.subParts ++ buckets }) "{}"

/--
The module namespace under which release note entries are written.
-/
public meta def entriesNamespace : Lean.Name := `UsersGuide.Releases.Entries

/--
Assembles the release notes chapter from every imported entry.

The argument names the module that holds the chapter's title, metadata and introduction. Two
definitions are added to the current module: {lit}`entries`, which pairs each entry's module name with
what it says about itself and its document, and the current module's document, which is the
assembled chapter.
-/
syntax "release_notes_chapter " ident : command

open Lean in
private meta unsafe def evalProblemsUnsafe (e : Expr) : Meta.MetaM (Array String) :=
  Meta.evalExpr (Array String) (mkApp (mkConst ``Array [Level.zero]) (mkConst ``String)) e (checkMeta := false)

open Lean in
@[implemented_by evalProblemsUnsafe]
private meta opaque evalProblems (e : Expr) : Meta.MetaM (Array String)

open Lean Elab Command in
elab_rules : command
  | `(release_notes_chapter $intro:ident) => do
    let env ← getEnv
    let modules := env.allImportedModuleNames.filter fun mod =>
      entriesNamespace.isPrefixOf mod && mod != entriesNamespace
    let mut entries := #[]
    let mut incomplete := #[]
    for mod in modules.qsort Name.lt do
      if env.contains (Verso.Doc.docName mod) && env.contains (entryMetadataName mod) then
        entries := entries.push mod
      else
        incomplete := incomplete.push mod
    unless incomplete.isEmpty do
      throwError "These modules under `{entriesNamespace}` are missing a `#doc` or a \
        `release_note` declaration:{indentD (toMessageData incomplete.toList)}"
    if entries.isEmpty then
      throwError "No release note entries found. \
        Every entry module must be publicly imported by `{entriesNamespace}`."
    let entryTerms ← entries.mapM fun mod =>
      `(($(quote mod), $(mkIdent (`_root_ ++ entryMetadataName mod)),
         $(mkIdent (`_root_ ++ Verso.Doc.docName mod))))
    let introDoc := mkIdentFrom intro (`_root_ ++ Verso.Doc.docName intro.getId)
    let entriesConst := env.mainModule ++ `entries
    let entriesName := mkIdent (`_root_ ++ entriesConst)
    let docName := mkIdent (`_root_ ++ (← Verso.Doc.currentDocName))
    elabCommand <| ← `(set_option compiler.extract_closed false in
      /-- Every release note entry, paired with the name of the module that defines it. -/
      public def $entriesName : Array (Lean.Name × EntryMetadata × VersoDoc Manual) :=
        #[$entryTerms,*])
    -- A malformed entry is an error from this command, while the chapter is elaborated.
    let found ← liftTermElabM <|
      evalProblems (mkApp (mkConst ``problems) (mkConst entriesConst))
    for problem in found do
      logError problem
    -- The version under development is resolved here, from the toolchain this build declares.
    let inDevelopment ← Version.inDevelopment
    elabCommand <| ← `(set_option compiler.extract_closed false in
      public def $docName : VersoDoc Manual :=
        chapter $introDoc (Array.map Prod.snd $entriesName)
          ⟨$(quote inDevelopment.major), $(quote inDevelopment.minor),
           $(quote inDevelopment.patch)⟩)

section Tests

private def testMetadata : EntryMetadata :=
  { version := ⟨4, 33, 0⟩, breaking := false, tag := "entry", prs := [1] }

private def testEntry (content : Array (Doc.Block Manual)) : Part Manual :=
  Part.mk #[Inline.text "Entry"] "Entry" Option.none content #[]

private def summaryBlock : Doc.Block Manual := Block.para #[Inline.text "A change happened."]

private def detail : Doc.Block Manual := Block.para #[Inline.text "Here is how it happened."]

/-- The author-chosen tag of each summary in an assembled version section, where it has one. -/
private def summaryTags (part : Part Manual) : Array (Option String) :=
  match (part.content[1]? : Option (Doc.Block Manual)) with
  | some (Block.ul items) =>
    items.filterMap fun item =>
      match (item.contents[0]? : Option (Doc.Block Manual)) with
      | some (Doc.Block.other b _) =>
        match Lean.FromJson.fromJson? (α := String × EntryInfo × Option Manual.Tag) b.data with
        | .ok ((_, a, _) : String × EntryInfo × Option Manual.Tag) => some a.tag
        | .error _ => none
      | _ => none
  | _ => #[]

#guard (bucket ⟨4, 33, 0⟩ false #[]).isNone

#guard (bucket ⟨4, 33, 0⟩ false #[(testMetadata, testEntry #[summaryBlock])]).any fun part =>
  part.titleString == "Verso 4.33.0" &&
  summaryTags part == #[some "entry"] &&
  part.subParts.isEmpty

#guard (bucket ⟨4, 33, 0⟩ true #[(testMetadata, testEntry #[summaryBlock, detail])]).any fun part =>
  part.titleString == "Verso 4.33.0 (in development)" &&
  summaryTags part == #[Option.none] &&
  part.subParts.map (·.content) == #[#[detail]]

-- A breaking change is marked in the list of changes.
#guard
  let breaking := { testMetadata with breaking := true }
  match summary breaking (testEntry #[summaryBlock]) with
  | Block.para contents => contents[0]? == some (Inline.bold #[Inline.text "Breaking change:"])
  | _ => false

#guard
  match summary testMetadata (testEntry #[summaryBlock]) with
  | Block.para contents => contents[0]? == some (Inline.text "A change happened.")
  | _ => false

-- An entry with no opening paragraph is reported.
#guard (entryProblem? (testEntry #[])).isSome
#guard (entryProblem? (testEntry #[Block.ul #[]])).isSome
#guard (entryProblem? (testEntry #[summaryBlock])).isNone

-- A section keeps the metadata its own `#doc` declared, and takes its permalink from the entry.
#guard
  let entry := { testEntry #[summaryBlock, detail] with metadata := some { draft := true } }
  (bucket ⟨4, 33, 0⟩ false #[(testMetadata, entry)]).any fun part =>
    part.subParts.all fun s =>
      (s.metadata.map (·.draft)).getD false &&
      (s.metadata.bind (·.tag)) == some "entry"

end Tests

end UsersGuide.Releases
