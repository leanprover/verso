import Verso

/-!

This is a Verso genre that generates single web pages, demonstrating each aspect of writing a Verso
genre as simply as possible.

-/

open Verso Doc

namespace Tutorial

/-!
A Verso genre, which is a value of type `Genre`, consists of the following:

  * Additional inline elements (e.g. cross-references, special links, or highlighted code)
  * Additional block elements (e.g. highlighted code blocks, figures, table of figures)
  * Metadata that can be applied to parts (that is, sections, chapters, etc - anything that can have
    a header associated with it)
  * Context and state for the *traversal pass*

The *traversal pass* is the computation used to do things like resolving intra-document
cross-references - more on that later.

Additionally, each Verso genre should provide some way to produce output from a document written in
the genre. For the blog genre, this is an IO action that takes a specification of the site's URL
structure and produces HTML on disk. For the manual genre, it takes the document and produces either
HTML or TeX. Rather than providing a single executable that should work for every use case, Verso
provides libraries with which a specific executable can be built.
-/

/-! # Document Extensions -/

/-!
This genre's only extension to the language of documents is the ability to insert dates, which are
either the date on which the document was rendered or some specific date, and references to sections.
-/

/--
A date to be shown in a document.
-/
inductive Date where
  | today
  | specific (day month year : Nat)

/-- A link to a given tag -/
structure SectionRef where
  /-- The section being referred to -/
  dest : String
  /--
  A unique tag used for back-references. The system itself is expected to fill this out during
  the traversal pass.
  -/
  tag : Option Nat := none

/-- Sections can be tagged with identifiers -/
structure SimplePage.PartMetadata where
  tag : String

/-! # Document Traversal -/

/-!
The traversal pass updates some state as it encounters the contents of the document. The document is
traversed repeatedly until the output state is equal to the input state, so it's important to use
idempotent operations when possible.

Genres provide both reader and state datatypes to be used during traversal. The reader datatype
`TraverseContext` is used to communicate data from the overall document to subdocuments.
-/

/--
While traversing, it will be important to know what the current date is.

In other genres, this is used to track things like the current position in the URL structure of a
website or a table of contents.
-/
structure SimplePage.TraverseContext where
  day : Nat
  month : Nat
  year : Nat

def hashMapEqBy [BEq α] [Hashable α] (eq : β → β → Bool) (xs ys : Lean.HashMap α β) : Bool :=
    xs.size == ys.size &&
    xs.fold (fun soFar k v => soFar && (ys.find? k |>.map (eq v) |>.getD false)) true

def hashSetEq [BEq α] [Hashable α] (xs ys : Lean.HashSet α) : Bool :=
    xs.size == ys.size &&
    xs.fold (fun soFar x => soFar && ys.contains x) true

structure SimplePage.TraverseState where
  /-- A mapping from header IDs to incoming link IDs -/
  refTargets : Lean.HashMap String (Lean.HashSet Nat) := {}

  /-- All the part tags in the document -/
  partTags : Lean.HashSet String := {}

  /-- The next unique link tag to assign -/
  nextLinkTag : Nat := 0

instance : BEq SimplePage.TraverseState where
  beq st1 st2 :=
    hashMapEqBy hashSetEq st1.refTargets st2.refTargets &&
    hashSetEq st1.partTags st2.partTags &&
    st1.nextLinkTag == st2.nextLinkTag

/-! # The Genre -/

/-- The simple page genre-/
def SimplePage : Genre where
  -- Inline extensions are either dates or section references
  Inline := Date ⊕ SectionRef
  -- There are no extra block-level elements
  Block := Empty
  PartMetadata := SimplePage.PartMetadata
  TraverseContext := SimplePage.TraverseContext
  TraverseState := SimplePage.TraverseState

namespace SimplePage

/-! # Implementing the Traversal Pass -/

/-!
Each traversal needs to supply a monad that provides reader access to the context and state
access to the state.

Genres may additionally wish to provide access to IO or to error logging.
-/
abbrev TraverseM := ReaderT SimplePage.TraverseContext (StateT TraverseState Id)

/-- Show a date as a string -/
def renderDate (day month year : Nat) :=
  let day' := toString day
  let month' := toString month
  let year' := toString year
  s!"{padTo 4 year'}-{padTo 2 month'}-{padTo 2 day'}"
where
  padTo n str :=
    (n - str.length).fold (fun _ s => s.push '0') "" ++ str

/-- info: "1984-07-12" -/
#guard_msgs in
#eval renderDate 12 7 1984

/-!
The traversal pass is mostly provided by Verso. To use Verso's provided traversal code, clients must
supply an instance of `Traverse` for their genre, which provides both customization hooks (`part`,
`block`, `inline`) that fire when certain elements are encountered and genre-specific hooks that
implement traversal for the provided part metadata, block extensions, and inline extensions.
-/

instance : Traverse SimplePage TraverseM where
  part _ := pure none
  block _ := pure ()
  inline _ := pure ()
  genrePart metadata _ := do
    -- Save the found tag so it can be used for cross-reference lints later on
    modify fun st =>
      {st with partTags := st.partTags.insert metadata.tag}
    -- Returning `none` means that the document AST is unmodified
    pure none
  genreBlock blkExt _ := nomatch blkExt
  genreInline
    -- Dates will be handled later, at HTML generation
    | .inl _, _ => pure none
    -- If the outgoing link has no ID, assign one
    | .inr ⟨dest, none⟩, contents => do
      let t ← modifyGet fun st => (st.nextLinkTag, {st with nextLinkTag := st.nextLinkTag + 1})
      pure (some (.other (.inr ⟨dest, some t⟩) contents))
    -- Remember the pointer from the outgoing link to its target
    | .inr ⟨dest, some t⟩, _ => do
      modify fun st =>
        {st with
          refTargets := st.refTargets.insert dest (st.refTargets.findD dest .empty |>.insert t)}
      pure none

/-! # Producing Output -/

/-!
Verso includes libraries for generating HTML and TeX. They can generate output for Verso's built-in
datatypes, but they require instances of `GenreHtml` or `GenreTeX` to render genre-specific data.
-/

open Verso.Output Html

instance : GenreHtml SimplePage IO where
  -- When rendering a part to HTMl, extract the incoming links from the final traversal state and
  -- insert back-references
  part recur metadata | (.mk title titleString _ content subParts) => do
    let incoming := (← HtmlT.state).refTargets.find? metadata.tag
    let content' := if let some i := incoming then
      let links := i.toArray.map fun t => ListItem.mk 0 #[Doc.Block.para #[Doc.Inline.link #[.text "(link)"] s!"#link-{t}"]]
      #[Doc.Block.para #[.text "Incoming links:"], Doc.Block.ul links] ++ content
    else content
    -- It's important that this not include the metadata in the recursive call, or the generator
    -- will loop (the metadata's presence is what triggers the call to `GenreHtml.part`)
    let part' := .mk title titleString none content' subParts
    recur part' #[("id", metadata.tag)]
  -- There are no genre-specific blocks, so no code is needed here
  block _ _ blkExt := nomatch blkExt
  inline recur
    -- Render dates
    | .inl .today, _ => do
      let ⟨d, m, y⟩ ← HtmlT.context
      pure <| renderDate d m y
    | .inl (.specific d m y), _ =>
      pure <| renderDate d m y
    -- If no ID was assigned, log an error
    | .inr ⟨dest, none⟩, contents => do
      HtmlT.logError s!"No ID assigned to section link of {dest}"
      pure {{<a href=s!"#{dest}"> {{← contents.mapM recur}} </a>}}
    -- Otherwise emit the right ID
    | .inr ⟨dest, some t⟩, contents => do
      pure {{<a href=s!"#{dest}" id=s!"link-{t}"> {{← contents.mapM recur}} </a>}}


/--
The main function to be called to produce HTML output
-/
def render (doc : Part SimplePage) : IO UInt32 := do
  let mut doc := doc
  -- Do the traversal pass until either too many iterations have been reached (indicating a bug) or
  -- a fixed point is reached
  let mut state : SimplePage.TraverseState := {}
  -- It's always April 1!
  let context : SimplePage.TraverseContext := {day := 1, month := 4, year := 2029}
  let mut iterations := 0
  repeat
    IO.println s!"Iteration {iterations} of the traversal pass"
    if iterations > 10 then
      throw <| IO.userError s!"Failed to traverse the document after {iterations} iterations. The genre is likely buggy."
    let (doc', state') := SimplePage.traverse doc |>.run context |>.run state
    if state == state' then break
    state := state'
    doc := doc'
    iterations := iterations + 1
  IO.println s!"Traversal completed after {iterations} iterations"

  -- Render the resulting document to HTML. This requires a way to log errors.
  let hadError ← IO.mkRef false
  let logError str := do
    hadError.set true
    IO.eprintln str

  IO.println "Rendering HTML"
  let html := {{
    <html>
      <head>
        <title>{{doc.titleString}}</title>
        <meta charset="utf-8"/>
      </head>
      <body>{{← SimplePage.toHtml {logError} context state doc}}</body>
    </html>
  }}

  IO.println "Writing to index.html"
  IO.FS.withFile "index.html" .write fun h => do
    h.putStrLn html.asString

  if (← hadError.get) then
    IO.eprintln "Errors occurred while rendering"
    pure 1
  else
    pure 0

end SimplePage

/-! # User API to Extensions -/

/-!
Genres should provide an API that users can use to access their document extensions.
-/

/-- Insert a link to the given section, encompassing the provided inline elements. -/
def sectionRef (content : Array (Inline SimplePage)) (dest : String) : Inline SimplePage :=
  .other (.inr {dest}) content

/-- Insert today's date here -/
def today (_content : Array (Inline SimplePage)) : Inline SimplePage :=
  .other (.inl .today) #[]

/-- Insert a particular date here -/
def date (_content : Array (Inline SimplePage)) (year month day : Nat) : Inline SimplePage :=
  .other (.inl (.specific day month year)) #[]
