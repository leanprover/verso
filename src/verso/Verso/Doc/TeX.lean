import Verso.Doc
import Verso.Method
import Verso.Output.TeX

open Verso.Doc

namespace Verso.Doc.TeX

open Verso.Output TeX

structure Options (g : Genre) (m : Type → Type) where
  headerLevels : Array String := #["chapter", "section", "subsection", "subsubsection", "paragraph"]
  /-- The level of the top-level headers -/
  headerLevel : Option (Fin headerLevels.size)
  logError : String → m Unit

abbrev TeXT (genre : Genre) (m : Type → Type) : Type → Type :=
  ReaderT (Options genre m × genre.TraverseContext × genre.TraverseState) m

instance [Monad m] [Inhabited α] : Inhabited (TeXT g m α) := ⟨pure default⟩

def options [Monad m] : TeXT g m (Options g m) := do
  pure (← read).fst

def logError [Monad m] (message : String) : TeXT g m Unit := do
  (← options).logError message

def header [Monad m] (name : TeX) : TeXT g m TeX := do
  let opts ← options
  let some i := opts.headerLevel
    | logError s!"No more header nesting available at {name.asString}"; return \TeX{\textbf{\Lean{name}}}
  let header := opts.headerLevels[i]
  pure <| .raw (s!"\\{header}" ++ "{") ++ name ++ .raw "}"

def inHeader [Monad m] (act : TeXT g m α) : TeXT g m α :=
  withReader (fun (opts, st, st') => (bumpHeader opts, st, st')) act
where
  bumpHeader opts :=
    if let some i := opts.headerLevel then
      if h : i.val + 1 < opts.headerLevels.size then
        {opts with headerLevel := some ⟨i.val + 1, h⟩}
      else {opts with headerLevel := none}
    else opts

class GenreTeX (genre : Genre) (m : Type → Type) where
  part (partTeX : Part genre → TeXT genre m TeX) (metadata : genre.PartMetadata) (contents : Part genre) : TeXT genre m TeX
  block (blockTeX : Block genre → TeXT genre m TeX) (container : genre.Block) (contents : Array (Block genre)) : TeXT genre m TeX
  inline (inlineTeX : Inline genre → TeXT genre m TeX) (container : genre.Inline) (contents : Array (Inline genre)) : TeXT genre m TeX

partial defmethod Inline.toTeX [Monad m] [GenreTeX g m] : Inline g → TeXT g m TeX
  | .text str => pure <| .text str
  | .link content dest => do
    pure \TeX{\hyperlink{\Lean{.raw (toString (repr dest)) }}{\Lean{← content.mapM Inline.toTeX}}} -- TODO link destinations
  | .image _alt dest => do
    pure \TeX{\includegraphics{\Lean{.raw (toString (repr dest))}}} -- TODO link destinations
  | .footnote _name txt => do
    pure \TeX{\footnote{\Lean{← txt.mapM Inline.toTeX}}}
  | .linebreak str => pure <| .text str
  | .emph content => do
    pure \TeX{\emph{\Lean{← content.mapM toTeX}}}
  | .bold content => do
    pure \TeX{\textbf{\Lean{← content.mapM toTeX}}}
  | .code str => do
    pure \TeX{s!"\\verb|{str}|"} --- TODO choose delimiter automatically
  | .math .inline str => pure <| .raw s!"${str}$"
  | .math .display str => pure <| .raw s!"\\[{str}\\]"
  | .concat inlines => inlines.mapM toTeX
  | .other container content => GenreTeX.inline Inline.toTeX container content

partial defmethod Block.toTeX [Monad m] [GenreTeX g m] : Block g → TeXT g m TeX
  | .para xs => do
    pure <| (← xs.mapM Inline.toTeX)
  | .blockquote bs => do
    pure \TeX{\begin{quotation} \Lean{← bs.mapM Block.toTeX} \end{quotation}}
  | .ul items => do
    pure \TeX{\begin{itemize} \Lean{← items.mapM fun li => do pure \TeX{\item " " \Lean{← li.contents.mapM Block.toTeX}}} \end{itemize} }
  | .ol start items => do -- TODO start numbering here
    pure \TeX{\begin{enumerate} \Lean{← items.mapM fun li => do pure \TeX{\item " " \Lean{← li.contents.mapM Block.toTeX}}} \end{enumerate} }
  | .dl items => do
    pure \TeX{\begin{description} \Lean{← items.mapM fun li => do pure \TeX{\item[\Lean{← li.term.mapM Inline.toTeX}] " " \Lean{← li.desc.mapM Block.toTeX}}} \end{description} }
  | .code _ _ _ content => do
    pure \TeX{\begin{verbatim} \Lean{.raw content} \end{verbatim}}
  | .concat items => TeX.seq <$> items.mapM Block.toTeX
  | .other container content => GenreTeX.block Block.toTeX container content


partial defmethod Part.toTeX [Monad m] [GenreTeX g m] (p : Part g) : TeXT g m TeX :=
  match p.metadata with
  | .none => do
    pure \TeX{
      \Lean{← header (← p.title.mapM Inline.toTeX)}
      "\n\n"
      \Lean{← p.content.mapM (fun b => do pure <| TeX.seq #[← Block.toTeX b, .paragraphBreak])}
      "\n\n"
      \Lean{← inHeader <| p.subParts.mapM Part.toTeX }
    }
  | some m =>
    GenreTeX.part Part.toTeX m p.withoutMetadata
