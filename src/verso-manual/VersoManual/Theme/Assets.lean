/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
meta import Init.System.FilePath
public meta import Lean.Elab.Frontend
public meta import Lean.Elab.Term
public meta import SubVerso.Highlighting
public meta import SubVerso.Highlighting.Code
public meta import SubVerso.Compat
public import SubVerso.Highlighting
public import Verso.Code.Highlighted

namespace Verso.Genre.Manual.Theme

/-- The picker JavaScript: builds the dialog opened by `#theme-picker-button`. -/
public def «theme-picker.js» : String := include_str "../../../../static-web/manual/theme/theme-picker.js"

/-- The picker styles. -/
public def «theme-picker.css» : String := include_str "../../../../static-web/manual/theme/theme-picker.css"

section
open Lean Elab Term

/--
Elaborates `input` as a sequence of Lean commands and returns SubVerso's highlighting of the result.
-/
private meta def highlightFromString (input : String) :
    TermElabM SubVerso.Highlighting.Highlighted := do
  let inputCtx := Parser.mkInputContext input "<codeSample>"
  -- Turn on app-fn tagging so per-identifier `TermInfo` is recorded
  let opts := pp.tagAppFns.set ({} : Lean.Options) true
  let scope : Command.Scope := { header := "", opts }
  let commandState : Command.State := {
    env := (← getEnv),
    maxRecDepth := (← MonadRecDepth.getMaxRecDepth),
    scopes := [scope]
  }
  let (result, _) ←
    SubVerso.Compat.Frontend.processCommands Lean.mkNullNode
      |>.run { inputCtx } |>.run { commandState, parserState := {}, cmdPos := 0 }
  let items := result.items.filter (·.commandSyntax.getKind != ``Lean.Parser.Command.eoi)
  let mut hls : SubVerso.Highlighting.Highlighted := .empty
  let mut lastPos : String.Pos.Raw := 0
  for item in items do
    let hl ← withTheReader Core.Context (fun ctx => { ctx with fileMap := inputCtx.fileMap }) do
      unless item.messages.toArray.isEmpty do
        throwError "Highlighting source produced messages: {← item.messages.toArray.mapM (·.toString)}"
      SubVerso.Highlighting.highlightIncludingUnparsed item.commandSyntax (startPos? := lastPos)
        item.messages.toArray item.info
    lastPos := (item.commandSyntax.getTrailingTailPos?).getD lastPos
    hls := hls ++ hl
  return hls

/--
At compile time, parses, elaborates, and highlights the given Lean source string, then quotes the
result as a `Highlighted` value.
-/
syntax (name := codeSampleTerm) "code_sample% " str : term

@[term_elab codeSampleTerm]
public meta def elabCodeSampleTerm : TermElab := fun stx expectedType? => do
  match stx with
  | `(code_sample% $src:str) =>
    let hl ← highlightFromString src.getString
    let q : Lean.Term := Lean.quote hl
    elabTerm q expectedType?
  | _ => throwUnsupportedSyntax

end

public def codeSampleHighlighted : SubVerso.Highlighting.Highlighted :=
  code_sample% r#"def greet (name : String) (count := 1) : String :=
  "\n".intercalate <|
    List.replicate count s!"Hello, {name}""#

open Verso.Code Verso.Output in
/--
Renders the code sample to HTML. The hover state is needed because the code sample itself may need
hovers.
-/
public def codeSampleHtml {g : Verso.Doc.Genre}
    (ctx : HighlightHtmlM.Context g) (state : Hover.State Html) :
    String × Hover.State Html :=
  -- Distinct `data-lean-context` from any page-level code block so the page-side
  -- binding-highlight lookup (cached by `context+binding`) naturally scopes its
  -- matching-token search to the preview itself rather than leaking into the document.
  let (html, state') :=
    ((codeSampleHighlighted.blockHtml (g := g) "verso-theme-picker") |>.run ctx) |>.run state
  (html.asString (breakLines := false), state')
