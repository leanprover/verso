/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso
import SubVerso.Highlighting.Code

/-!
Highlighting a proof that uses compound tactics such as `obtain` produces nested proof states: the
whole-`obtain` region carries a useful goal, and its inner tactic script closes its goal at the same
position where the outer region ends. Rendering both would put two toggle widgets at the same spot,
so `Highlighted.elideRedundantProofStates` drops the inner empty state before rendering.

This test highlights such a proof with SubVerso and checks that the redundant empty state has been elided.
-/

open SubVerso.Compat.Frontend (processCommands)
open SubVerso.Highlighting (Highlighted highlightFrontendResult)
open Verso.Code (HighlightHtmlM)
open Verso.Doc (Genre)
open Verso.Output (Html)
open Lean Elab Command

namespace Verso.NestedTacticHtmlTest

/--
The proof to highlight. `exists_prime_factor` proves that every number larger than 1 has a prime
factor; its two `obtain` tactics each run an inner script that closes the goal at the position where
the outer state ends.
-/
def proofSource : String :=
"def IsPrime (n : Nat) := 1 < n ∧ ∀ k, 1 < k → k < n → ¬ k ∣ n

theorem exists_prime_factor :
    ∀ n, 1 < n → ∃ k, IsPrime k ∧ k ∣ n := by
  intro n h1
  by_cases hprime : IsPrime n
  · grind [Nat.dvd_refl]
  · obtain ⟨k, _⟩ : ∃ k, 1 < k ∧ k < n ∧ k ∣ n := by
      simp_all [IsPrime]
    obtain ⟨p, _, _⟩ := exists_prime_factor k (by grind)
    grind [Nat.dvd_trans]"

/--
Highlights a Lean string.
-/
def highlightModule (input : String) : CommandElabM Highlighted := do
  let inputCtx := Parser.mkInputContext input "<nested-tactic-test>"
  let commandState : Command.State := { env := (← getEnv), maxRecDepth := (← get).maxRecDepth }
  let commandState :=
    let sc := commandState.scopes[0]!
    { commandState with scopes := { sc with opts := sc.opts.setBool `pp.tagAppFns true } :: commandState.scopes.tail! }
  let (result, _) ← processCommands mkNullNode
    |>.run { inputCtx } |>.run { commandState, parserState := {}, cmdPos := 0 }
  let result := result.updateLeading input
  runTermElabM fun _ =>
    withTheReader Core.Context (fun ctx => { ctx with fileMap := inputCtx.fileMap }) do
      let hls ← highlightFrontendResult result
      return hls.foldl (· ++ ·) .empty

/-!
# Recognizing the redundant pattern in the `Highlighted` tree
-/

/-- Whitespace and other content that does not render as a visible element. -/
def insignificant : Highlighted → Bool
  | .text s => s.trimAscii.isEmpty
  | .unparsed s => s.trimAscii.isEmpty
  | hl => hl.isEmpty

/-- The last visible element of `hl`, looking through `.seq` tails and `.span`. -/
partial def lastElement? : Highlighted → Option Highlighted
  | .seq xs => (xs.toList.reverse.find? (!insignificant ·)).bind lastElement?
  | .span _ x => lastElement? x
  | hl => if insignificant hl then none else some hl

/--
Whether `hl` contains a proof state with a non-empty goal array whose last element is a proof state
with an empty goals array.
-/
partial def hlHasRedundant : Highlighted → Bool
  | .seq xs => xs.any hlHasRedundant
  | .span _ x => hlHasRedundant x
  | .tactics info _ _ content =>
    let lastIsNoGoals :=
      match lastElement? content with
      | some (.tactics innerInfo ..) => innerInfo.isEmpty
      | _ => false
    (!info.isEmpty && lastIsNoGoals) || hlHasRedundant content
  | _ => false

/-! ## Recognizing proof states and their nesting in the rendered HTML -/

/-- A simulation of the HTML proof state tree -/
structure ProofState where
  /-- Whether this state shows "no goals" rather than a list of goals. -/
  noGoals : Bool
  /--
  Whether the last visible element of this state's code is itself a no-goals proof state. Such an
  inner state ends where this one ends, so the two toggle widgets land at the same spot.
  -/
  endsWithNoGoals : Bool
  /-- The proof states nested inside this one. -/
  children : List ProofState

/-- Whether `attrs` assigns the CSS class `cls`. -/
def hasClass (attrs : Array (String × String)) (cls : String) : Bool :=
  attrs.any fun (k, v) => k == "class" && (v.splitOn " ").contains cls

/-- The concatenated text content of an HTML fragment. -/
partial def htmlText : Html → String
  | .text _ s => s
  | .tag _ _ contents => htmlText contents
  | .seq xs => xs.foldl (fun acc x => acc ++ htmlText x) ""

/-- The direct children of an HTML fragment. -/
def directChildren : Html → Array Html
  | .seq xs => xs
  | hl => #[hl]

/-- Whether an HTML fragment renders as nothing visible (whitespace or empty). -/
partial def htmlInsignificant : Html → Bool
  | .text _ s => s.trimAscii.isEmpty
  | .seq xs => xs.all htmlInsignificant
  | .tag .. => false

/-- The last visible element of an HTML fragment, looking through `.seq` tails. -/
partial def htmlLastVisible? : Html → Option Html
  | .seq xs => (xs.toList.reverse.find? (!htmlInsignificant ·)).bind htmlLastVisible?
  | hl => if htmlInsignificant hl then none else some hl

/-- The direct child of `contents` that is a `<span>` with the given class, if any. -/
def childSpanWithClass (contents : Html) (cls : String) : Option Html :=
  (directChildren contents).find? fun h =>
    match h with
    | .tag "span" a _ => hasClass a cls
    | _ => false

/-- Whether `html` is a `<span class="tactic">` whose own state shows "no goals". -/
def isNoGoalsState : Html → Bool
  | .tag "span" attrs contents =>
    if hasClass attrs "tactic" then
      match childSpanWithClass contents "tactic-state" with
      | some s => htmlText s |>.contains "All goals completed"
      | none => false
    else false
  | _ => false

/-- The contents of the `<label>` child of a tactic span. -/
def labelContents (contents : Html) : Html :=
  let html? :=
    directChildren contents |>.findSome? fun
      | .tag "label" _ c => some c
      | _ => none
  html?.getD .empty

/--
Extracts the proof-state toggles directly present in an HTML fragment, together with the proof
states nested inside each one. A toggle is a `<span class="tactic">` whose own state is its direct
`<span class="tactic-state">` child; the nested states live inside its `<label>`.
-/
partial def proofStates : Html → List ProofState
  | .seq xs => xs.toList.flatMap proofStates
  | .tag name attrs contents =>
    if name == "span" && hasClass attrs "tactic" then
      let label := labelContents contents
      [{ noGoals := isNoGoalsState (.tag name attrs contents),
         endsWithNoGoals := htmlLastVisible? label |>.map isNoGoalsState |>.getD false,
         children := proofStates label }]
    else
      proofStates contents
  | .text .. => []

/--
Whether any proof state with goals ends with a no-goals proof state — the redundant nesting that
puts two toggle widgets at the same spot.
-/
partial def htmlHasRedundant (states : List ProofState) : Bool :=
  states.any fun s => (!s.noGoals && s.endsWithNoGoals) || htmlHasRedundant s.children

/-! ## Rendering -/

private def runHtml (act : HighlightHtmlM Genre.none Html) : Html :=
  let ctx : HighlightHtmlM.Context Genre.none :=
    { linkTargets := {}, traverseContext := (), definitionIds := {}, options := {} }
  act.run ctx |>.run .empty |>.fst

/-- Renders highlighted code to HTML directly, without the elision preprocessing pass. -/
def renderRaw (hl : Highlighted) : Html := runHtml (hl.toHtml)

/-- Renders highlighted code to HTML through the block entry point, which applies the pass. -/
def renderBlock (hl : Highlighted) : Html := runHtml (hl.blockHtml "nested-tactic-test")

/-! ## The test -/

def checkElision : CommandElabM Unit := do
  -- 1. Highlight the proof.
  let raw ← highlightModule proofSource

  -- 2. Sanity check: the highlighted proof really contains the redundant nesting.
  unless hlHasRedundant raw do
    throwError "expected the highlighted proof to contain a redundant no-goals state, but found none"

  -- 3. The preprocessing pass removes it.
  let elided := raw.elideRedundantProofStates
  if hlHasRedundant elided then
    throwError "`elideRedundantProofStates` left a redundant no-goals state behind"

  -- 4. Sanity check: the same redundant nesting is visible in the un-preprocessed HTML.
  unless htmlHasRedundant (proofStates (renderRaw raw)) do
    throwError "expected the un-preprocessed HTML to contain a redundant no-goals region, but found none"

  -- 5. The rendered HTML of the preprocessed proof does not.
  if htmlHasRedundant (proofStates (renderBlock raw)) then
    throwError "the rendered HTML still nests a no-goals region inside a goal-ful one"

#guard_msgs in
#eval checkElision
