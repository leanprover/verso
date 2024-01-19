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

structure TraverseContext where
  /-- The current URL path - will be [] for non-HTML output or in the root -/
  path : Path := #[]

def TraverseContext.inFile (self : TraverseContext) (file : String) : TraverseContext :=
  {self with path := self.path.push file}

/--
Tags are used to refer to parts through tables of contents, cross-references,
and the like.

During the traverse pass, the following steps occur:
 1. user-provided tags are made globally unique, and saved as xref targets
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

instance : Coe String PartTag where
  coe := .provided

structure PartMetadata where
  authors : List String := []
  date : Option String := none
  tag : Option PartTag := none

inductive Block where
  | paragraph

structure TraverseState where
  partSlugs : Lean.HashMap Slug Path := {}
  private contents : NameMap Json := {}

defmethod Lean.HashMap.all [BEq α] [Hashable α] (hm : Lean.HashMap α β) (p : α → β → Bool) : Bool :=
  hm.fold (fun prev k v => prev && p k v) true

instance : BEq TraverseState where
  beq x y :=
    x.partSlugs.size == y.partSlugs.size &&
    (x.partSlugs.all fun k v =>
      match y.partSlugs.find? k with
      | none => false
      | some v' => v == v'
    ) &&
    x.contents.size == y.contents.size &&
    x.contents.all fun k v =>
      match y.contents.find? k with
      | none => false
      | some v' => v == v'

namespace TraverseState

def set [ToJson α] (state : TraverseState) (name : Name) (value : α) : TraverseState :=
  {state with contents := state.contents.insert name (ToJson.toJson value)}

def get? [FromJson α] (state : TraverseState) (name : Name) : Except String α :=
  state.contents.find? name |>.map FromJson.fromJson? |>.getD (.error s!"No state entry for '{name}'")

end TraverseState
end Manual

def Manual : Genre where
  PartMetadata := Manual.PartMetadata
  Block := Manual.Block
  Inline := Empty
  TraverseContext := Manual.TraverseContext
  TraverseState := Manual.TraverseState

namespace Manual
abbrev TraverseM := ReaderT Manual.TraverseContext (StateT Manual.TraverseState IO)

instance : Traverse Manual Manual.TraverseM where
  part _ := pure ()
  block _ := pure ()
  inline _ := pure ()
  genrePart
    | {authors := _, date := _, slug := _}, _ => pure none
  genreBlock
    | .paragraph, _ => pure none
  genreInline i := nomatch i

open Verso.Output.TeX in
instance : TeX.GenreTeX Manual IO where
  part go _meta txt := go txt
  block go
    | .paragraph, content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  inline _go i _txt := nomatch i

open Verso.Output.Html in
instance : Html.GenreHtml Manual IO where
  part go meta txt := go txt
  block go
    | .paragraph, content => do
      pure <| {{<div class="paragraph">{{← content.mapM go}}</div>}}
  inline _go i _txt := nomatch i

@[directive_expander paragraph]
def paragraph : DirectiveExpander
  | #[], stxs => do
    let args ← stxs.mapM elabBlock
    let val ← ``(Block.other Manual.Block.paragraph #[ $[ $args ],* ])
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

def traverse (text : Part Manual) (config : Config) : IO (Part Manual × TraverseState) := do
  let topCtxt := {}
  let mut state : Manual.TraverseState := {}
  let mut text := text
  for _ in [0:config.maxTraversals] do
    let (text', state') ← StateT.run (ReaderT.run (Genre.traverse Manual text) topCtxt) state
    if state' == state then
      return (text', state')
    else
      state := state'
      text := text'
  return (text, state)

open IO.FS in
def emitTeX (logError : String → IO Unit) (config : Config) (state : TraverseState) (text : Part Manual) : IO Unit := do
  let opts : TeX.Options Manual IO := {
    headerLevels := #["chapter", "section", "subsection", "subsubsection", "paragraph"],
    headerLevel := some ⟨0, by simp_arith [Array.size, List.length]⟩,
    logError := logError
  }
  let authors := text.metadata.map (·.authors) |>.getD []
  let date := text.metadata.bind (·.date) |>.getD ""
  let ctxt := {}
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

def emitHtmlSingle (logError : String → IO Unit) (config : Config) (state : TraverseState) (text : Part Manual) : IO Unit := do
  let authors := text.metadata.map (·.authors) |>.getD []
  let date := text.metadata.bind (·.date) |>.getD ""
  let opts := {logError := logError}
  let ctxt := {}
  let titleHtml ← Html.seq <$> text.title.mapM (Manual.toHtml opts ctxt state)
  let contents ← Manual.toHtml opts ctxt state text
  let dir := config.destination.join "html-single"
  ensureDir dir
  IO.FS.withFile (dir.join "index.html") .write fun h => do
    h.putStrLn Html.doctype
    h.putStrLn (Html.page text.titleString (Html.titlePage titleHtml authors ++ contents)).asString


def emitHtmlMulti
    (depth : Nat) (logError : String → IO Unit) (config : Config)
    (state : TraverseState)
    (text : Part Manual) : IO Unit := do
  let authors := text.metadata.map (·.authors) |>.getD []
  let date := text.metadata.bind (·.date) |>.getD ""
  let ctxt := {}
  let opts := {logError := logError}
  let titleHtml ← Html.seq <$> text.title.mapM (Manual.toHtml opts ctxt state)
  let frontMatter ← text.content.mapM (Manual.toHtml opts ctxt state)
  let mut chapters : Array (Slug × Part Manual):= #[]
  let dir := config.destination.join "html-multi"
  ensureDir dir
  IO.FS.withFile (dir.join "index.html") .write fun h => do
    h.putStrLn (Html.page text.titleString (Html.titlePage titleHtml authors)).asString
    h.putStrLn (preamble text.titleString authors date)
    for b in frontMatter do
      h.putStrLn b.asString
  for (s, _c) in chapters do
    IO.FS.withFile (dir.join s.toString |>.join "index.html") .write fun h => do
      h.putStrLn "not yet"

def manualMain (text : Part Manual) (options : List String) : IO UInt32 := do
  let hasError ← IO.mkRef false
  let logError msg := do hasError.set true; IO.eprintln msg
  let cfg ← opts {} options
  let (text, state) ← traverse text cfg
  emitTeX logError cfg state text
  emitHtmlSingle logError cfg state text
  emitHtmlMulti 2 logError cfg state text

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
