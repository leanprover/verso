import LeanDoc.Doc
import LeanDoc.Doc.Concrete
import LeanDoc.Doc.TeX
import LeanDoc.Output.TeX
import LeanDoc.Doc.Lsp
import LeanDoc.Doc.Elab

import LeanDoc.Genre.Manual.TeX


open LeanDoc.Doc Elab

open LeanDoc.Genre.Manual.TeX

namespace LeanDoc.Genre

structure Manual.PartMetadata where
  authors : List String := []
  date : Option String := none

inductive Manual.Block where
  | paragraph

def Manual : Genre where
  PartMetadata := Manual.PartMetadata
  Block := Manual.Block
  Inline := Empty
  TraverseContext := Unit
  TraverseState := Unit

namespace Manual

open LeanDoc.Output.TeX in
instance : TeX.GenreTeX Manual IO where
  part go _meta txt := go txt
  block go
    | .paragraph, content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
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

def ensureDir (dir : System.FilePath) : IO Unit := do
  if !(← dir.pathExists) then
    IO.FS.createDirAll dir
  if !(← dir.isDir) then
    throw (↑ s!"Not a directory: {dir}")

open IO.FS in
def emitTeX (logError : String → IO Unit) (config : Config) (text : Part Manual) : IO Unit := do
  let opts : TeX.Options Manual IO := {headerLevels := #["chapter", "section", "subsection", "subsubsection", "paragraph"], headerLevel := some ⟨0, by simp_arith [Array.size, List.length]⟩, logError := logError}
  let authors := text.metadata.map (·.authors) |>.getD []
  let date := text.metadata.bind (·.date) |>.getD ""
  let frontMatter ← text.content.mapM (·.toTeX (opts, (), ()))
  let chapters ← text.subParts.mapM (·.toTeX (opts, (), ()))
  let dir := config.destination.join "tex"
  ensureDir dir
  withFile (dir.join "main.tex") .write fun h => do
    h.putStrLn (preamble text.titleString authors date)
    for b in frontMatter do
      h.putStrLn b.asString
    for c in chapters do
      h.putStrLn c.asString
    h.putStrLn postamble

def manualMain (text : Part Manual) (options : List String) : IO UInt32 := do
  let hasError ← IO.mkRef false
  let logError msg := do hasError.set true; IO.eprintln msg
  let cfg ← opts {} options

  -- TODO xrefs
  emitTeX logError cfg text

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
