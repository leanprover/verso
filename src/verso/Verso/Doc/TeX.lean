/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Verso.Doc
import Verso.Method
public import Verso.Output.TeX

namespace Verso.Doc.TeX

open Verso.Output TeX

public structure Options (g : Genre) (m : Type → Type) where
  headerLevels : Array String := #["chapter", "section", "subsection", "subsubsection", "paragraph"]
  /-- The level of the top-level headers -/
  headerLevel : Option (Fin headerLevels.size)
  logError : String → m Unit

public structure TeXContext where
  /--
  True if we are currently rendering TeX in a fragile environment
  (specifically, one which cannot accommodate `\Verb`)
  -/
  inFragile : Bool := false

public def Options.reinterpret (lift : {α : _} → m α → m' α) (opts : Options g m) : Options g m' :=
  {opts with
    logError := fun msg => lift <| opts.logError msg}

public def Options.lift [MonadLiftT m m'] (opts : Options g m) : Options g m' :=
  opts.reinterpret MonadLiftT.monadLift

public abbrev TeXT (genre : Genre) (m : Type → Type) : Type → Type :=
  ReaderT (Options genre m × genre.TraverseContext × genre.TraverseState × TeXContext) m

public instance [Monad m] [Inhabited α] : Inhabited (TeXT g m α) := ⟨pure default⟩

public def options [Monad m] : TeXT g m (Options g m) := do
  pure (← read).fst

public def logError [Monad m] (message : String) : TeXT g m Unit := do
  (← options).logError message

public def texContext [Monad m] : TeXT g m TeXContext := do
  let ⟨_, _, _, ctx⟩ ← read
  pure ctx

public def header [Monad m] (name : TeX) : TeXT g m TeX := do
  let opts ← options
  let some i := opts.headerLevel
    | logError s!"No more header nesting available at {name.asString}"; return \TeX{\textbf{\Lean{name}}}
  let header := opts.headerLevels[i]
  pure <| .raw (s!"\\{header}" ++ "{") ++ name ++ .raw "}"

public def inFragile [Monad m] (act : TeXT g m α) : TeXT g m α :=
  withReader (fun (opts, st, st', tctx) => (opts, st, st', { tctx with inFragile := true })) act

public def inHeader [Monad m] (act : TeXT g m α) : TeXT g m α :=
  withReader (fun (opts, st, st', tctx) => (bumpHeader opts, st, st', tctx)) act
where
  bumpHeader opts :=
    if let some i := opts.headerLevel then
      if h : i.val + 1 < opts.headerLevels.size then
        {opts with headerLevel := some ⟨i.val + 1, h⟩}
      else {opts with headerLevel := none}
    else opts

public class GenreTeX (genre : Genre) (m : Type → Type) where
  part (partTeX : Part genre → TeXT genre m TeX) (metadata : genre.PartMetadata) (contents : Part genre) : TeXT genre m TeX
  block (inlineTeX : Inline genre → TeXT genre m TeX) (blockTeX : Block genre → TeXT genre m TeX) (container : genre.Block) (contents : Array (Block genre)) : TeXT genre m TeX
  inline (inlineTeX : Inline genre → TeXT genre m TeX) (container : genre.Inline) (contents : Array (Inline genre)) : TeXT genre m TeX

def escapeForTexHref (s : String) : String :=
  s.replace "%" "\\%"

/--
Replaces characters with strings simultaneously.
-/
def replaceChars (s : String) (replace : Char → Option String) : String :=
  let rec loop (acc : String) (pos : String.Pos.Raw) :=
    if pos.byteIdx ≥ s.utf8ByteSize then acc
    else
      have : (String.Pos.Raw.next s pos).byteIdx > pos.byteIdx :=
        String.Pos.Raw.byteIdx_lt_byteIdx_next s pos
      let c := pos.get s
      let s' := match replace c with | some rs => rs | none => s!"{c}"
      loop (acc ++ s') (pos.next s)
    termination_by s.rawEndPos.1 - pos.1
  loop "" 0

/--
Escapes a string in an appropriate way for uses of `\Verb` and
`\begin{Verbatim}...\end{Verbatim}` (from package `fancyvrb`) with
command characters `\`, `{`, and `}`.
-/
public def escapeForVerbatim (s : String) : String :=
  replaceChars s fun
  | '{' => some "\\symbol{123}"
  | '|' => some "\\symbol{124}"
  | '}' => some "\\symbol{125}"
  | '\\' => some "\\symbol{92}"
  | '#' => some "\\symbol{35}" -- FIXME: this is really just a test
  | _ => none

/-- info: "\\symbol{123}\\symbol{124}\\symbol{125}\\symbol{92}" -/
#guard_msgs in
#eval escapeForVerbatim "{|}\\"

/--
Wraps some TeX (which is already assumed to be appropriately escaped in the appropriate
verbatim-like environment depending on whether we're in a fragile environment.
-/
public def verbatimInline [Monad m] [GenreTeX g m] (t : TeX) : TeXT g m Verso.Output.TeX := do
  if (← texContext).inFragile then
    pure (.seq #[.raw "\\texttt{", t, .raw "}"]) -- TODO: better escaping for texttt
  else
    pure (.seq #[.raw "\\LeanVerb|", t, .raw "|"])

public partial defmethod Inline.toTeX [Monad m] [GenreTeX g m] : Inline g → TeXT g m TeX
  | .text str => pure <| .text str
  | .link content dest => do
    pure \TeX{\href{\Lean{.raw (escapeForTexHref dest)}}{\Lean{← content.mapM Inline.toTeX}}}
  | .image _alt dest => do
    pure \TeX{\includegraphics{\Lean{.raw (toString (repr dest))}}} -- TODO link destinations
  | .footnote _name txt => do
    pure \TeX{\footnote{\Lean{← txt.mapM Inline.toTeX}}}
  | .linebreak str => pure <| .text str
  | .emph content => do
    pure \TeX{\emph{\Lean{← content.mapM toTeX}}}
  | .bold content => do
    pure \TeX{\textbf{\Lean{← content.mapM toTeX}}}
  | .code str => verbatimInline (escapeForVerbatim str)
  | .math .inline str => pure <| .raw s!"${str}$"
  | .math .display str => pure <| .raw s!"\\[{str}\\]"
  | .concat inlines => inlines.mapM toTeX
  | .other container content => GenreTeX.inline Inline.toTeX container content

public partial defmethod Block.toTeX [Monad m] [GenreTeX g m] : Block g → TeXT g m TeX
  | .para xs => do
    pure <| (← xs.mapM Inline.toTeX)
  | .blockquote bs => do
    pure \TeX{\begin{quotation} \Lean{← bs.mapM Block.toTeX} \end{quotation}}
  | .ul items => do
    pure \TeX{\begin{itemize} \Lean{← items.mapM fun li => do pure \TeX{\item " " \Lean{← li.contents.mapM Block.toTeX} s!"\n"}} \end{itemize} }
  | .ol _start items => do -- TODO start numbering here
    pure \TeX{\begin{enumerate} \Lean{← items.mapM fun li => do pure \TeX{\item " " \Lean{← li.contents.mapM Block.toTeX} s!"\n"}}\end{enumerate} }
  | .dl items => do
    pure \TeX{\begin{description} \Lean{← items.mapM fun li => do pure \TeX{\item[\Lean{← li.term.mapM Inline.toTeX}] " " \Lean{← li.desc.mapM Block.toTeX}}} \end{description} }
  | .code content => do
    pure \TeX{\begin{verbatim} \Lean{.raw content} \end{verbatim}}
  | .concat items => TeX.seq <$> items.mapM Block.toTeX
  | .other container content => GenreTeX.block Inline.toTeX Block.toTeX container content


public partial defmethod Part.toTeX [Monad m] [GenreTeX g m] (p : Part g) : TeXT g m TeX :=
  match p.metadata with
  | .none => do
    pure \TeX{
      \Lean{← header (← inFragile <| p.title.mapM Inline.toTeX)}
      "\n\n"
      \Lean{← p.content.mapM (fun b => do pure <| TeX.seq #[← Block.toTeX b, .paragraphBreak])}
      "\n\n"
      \Lean{← inHeader <| p.subParts.mapM Part.toTeX }
    }
  | some m =>
    GenreTeX.part Part.toTeX m p.withoutMetadata
