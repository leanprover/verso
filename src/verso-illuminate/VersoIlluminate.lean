/-
Copyright (c) 2024-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Verso.Doc
public import Verso.Doc.ArgParse
public import Verso.Doc.Elab.Monad
import Verso.Instances

import Illuminate
public meta import Illuminate.Widget

open Lean Elab
open Verso ArgParse Doc Elab
open Verso.SyntaxUtils (parseStrLitAsCategory)

namespace Verso.ArgParse.ValDesc

/--
Parses a decimal float string (e.g. `"3.14"`, `"-0.5"`, `".5"`, `"3."`).

Returns `none` for unrecognized formats.
-/
def parseFloatStr (s : String) : Option Float :=
  let (neg, s) : Bool × String :=
    if s.startsWith "-" then (true, (s.drop 1).copy) else (false, s)
  let parseIntPart (intStr : String) : Option Nat :=
    if intStr.isEmpty then some 0 else intStr.toNat?
  let result : Option Float := match s.splitOn "." with
    | [intStr] =>
      if intStr.isEmpty then none
      else intStr.toNat?.map fun n => Float.ofScientific n true 0
    | [intStr, fracStr] =>
      if intStr.isEmpty && fracStr.isEmpty then none
      else parseIntPart intStr |>.bind fun n =>
        if fracStr.isEmpty then some (Float.ofScientific n true 0)
        else fracStr.toNat?.map fun frac =>
          Float.ofScientific n true 0 + Float.ofScientific frac true fracStr.length
    | _ => none
  result.map fun f => if neg then -f else f

/--
A `ValDesc` for float arguments. Accepts integer numerals (e.g. `1`) and
string literals containing decimal numbers (e.g. `"0.08"`).
-/
public def float [Monad m] [MonadError m] : ValDesc m Float where
  description := doc!"a number"
  signature := .Num ∪ .String
  get
    | .num n => pure (Float.ofScientific n.getNat true 0)
    | .str s =>
      match parseFloatStr s.getString with
      | some f => pure f
      | none => throwError "Expected a number, got {repr s.getString}"
    | .name n => throwError "Expected a number, got identifier {n.getId}"

end Verso.ArgParse.ValDesc

namespace Verso.Illuminate

/--
Padding (in diagram units) added on each side of the rendered SVG's view box. Used both by
`renderSvg` and `viewBoxWidth` below, so the width returned to the code-block expander matches
the actual rendered SVG.
-/
private def svgPadding : Float := 5

/-- Renders a diagram to SVG using the local `svgPadding`. -/
private def renderSvg (d : Illuminate.Diagram Illuminate.SVG) : String :=
  d.renderDiagram (padding := svgPadding)

/--
Computes the view box width (in diagram units) of the SVG produced by `renderSvg`. Returns 0
for empty diagrams.
-/
private def viewBoxWidth (d : Illuminate.Diagram Illuminate.SVG) : Float :=
  match d.getEnvelope with
  | .empty => 0
  | .nonempty env => env Illuminate.Vec2.west + env Illuminate.Vec2.east + 2 * svgPadding

section

open Lean Widget Elab Term Meta Illuminate

private meta unsafe def evalDiagramUnsafe (str : StrLit) (stx : Syntax) :
    TermElabM (String × Float) := do
  let diaTy ← Meta.mkAppM ``Illuminate.Diagram #[.const ``Illuminate.SVG []]
  let e ← Elab.Term.elabTerm stx (some diaTy)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e

  -- Don't evaluate if elaboration produced errors.
  if (← Core.getMessageLog).hasErrors then
    return ("", 0)

  -- Evaluate to get SVG string.
  let svgExpr := mkApp (mkConst ``renderSvg) e
  let svgStr ← evalExpr String (mkConst ``String) svgExpr

  -- Compute the diagram's natural viewBox width.
  let widthExpr := mkApp (mkConst ``viewBoxWidth) e
  let diagramWidth ← evalExpr Float (mkConst ``Float) widthExpr

  -- Store diagram for widget RPC re-evaluation.
  let env ← getEnv
  let opts ← getOptions
  let id ← Illuminate.nextDiagramId.modifyGet fun n => (n, n + 1)
  let sd : Illuminate.StoredDiagram := {
    env, opts, expr := e, gadgets := #[], regions := {}, returnsDwi := false
  }
  Illuminate.diagramStore.modify (·.push (id, sd))

  -- Attach widget with CSS variable defaults for the infoview context.
  let widgetSvg :=
    "<div style=\"--verso-text-font-family: sans-serif; --verso-code-font-family: monospace;\">" ++
    "<style>svg text[font-family=\"text\"] { font-family: var(--verso-text-font-family); } " ++
    "svg text[font-family=\"monospace\"] { font-family: var(--verso-code-font-family); }</style>" ++
    svgStr ++ "</div>"
  let props : Json := .mkObj [
    ("exprId", toJson id),
    ("initialSvg", .str widgetSvg),
    ("parameters", .arr #[])]
  savePanelWidgetInfo Illuminate.diagramWidget.javascriptHash.val (pure props) str

  pure (svgStr, diagramWidth)

@[implemented_by evalDiagramUnsafe]
private opaque evalDiagramImpl (str : StrLit) (stx : Syntax) :
    TermElabM (String × Float)

end

/--
Parses, elaborates, and evaluates the source of an Illuminate diagram, registers it with the
InfoView widget store, and returns the rendered SVG string together with the diagram's natural
viewBox width.

`scope` is the genre-specific elaboration wrapper (e.g. running inside open declarations and
section variables for the Manual genre). It defaults to the identity.

Genre-specific code-block expanders call this to do the shared evaluation work and then emit
their own `GenreDiagram.diagramBlock` term.
-/
public def elabAndStoreDiagram (str : StrLit)
    (scope : {α : Type} → TermElabM α → TermElabM α := fun act => act) :
    DocElabM (String × Float) := do
  let stx ← parseStrLitAsCategory `term str
  if stx.isMissing then
    return ("", 0)
  scope (evalDiagramImpl str stx)
