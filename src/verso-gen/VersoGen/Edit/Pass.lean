/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoGen.Edit.Basic

set_option doc.verso true

/-!
The edit pass, which both the edit generator and construction use. The pass goes over a surface
document once, in document order. At each node it may make an edit, and it may make another one
where that edit leaves the zipper. It then moves on to the next node. Each edit changes the text at
or after the first character that the previous edit changed.

The pass records each edit with the number of nodes that it moved forward since the previous edit,
so replaying the recorded edits needs no random choices. A theorem shows that replaying them gives
the surface document where the pass ends.
-/

namespace VersoGen.Edit

open VersoGen.Doc VersoGen.Doc.SurfaceDoc VersoGen.Genre VersoGen.Random

open Lean

/-- An edit, with the place of its node relative to the previous edit. -/
public structure RecordedEdit where
  /--
  The number of nodes that the traversal moves forward in document order, one
  {name}`Zipper.next?` at a time, to reach the node where the edit is made. The traversal starts at
  the node where the previous edit left the zipper, or at the root part for the first edit. Replay
  moves that many nodes forward and then makes the edit.
  -/
  steps : Nat
  edit : Edit
deriving ToJson, FromJson, BEq, Repr, Inhabited

/--
The result of an edit pass: the zipper where it ends, the edits it made, and the state of its
choices.
-/
public abbrev PassResult (σ : Type) := (Zipper × List RecordedEdit) × σ

/--
Continues an edit pass from the node after {name}`z` with {name}`pass`. Without a next node, the
pass ends at {name}`z`.
-/
def continuePass (pass : Zipper → Nat → String.Pos.Raw → σ → PassResult σ) (z : Zipper)
    (steps : Nat) (earliestAllowedChange : String.Pos.Raw) (s : σ) : PassResult σ :=
  match z.next? with
  | some z' => pass z' (steps + 1) earliestAllowedChange s
  | none => ((z, []), s)

/--
Makes an edit pass from a zipper, with the edits that {name}`choose` picks. The pass is pure: its
choices come from {name}`choose`, which gives the edit to try at a focus, if any, and the next state
of its choices. After an edit, the pass stays where the edit leaves the zipper, and it may edit
there again. Without an edit, it moves to the next node. {name}`steps` is the number of nodes that
it has moved forward since the previous edit, and {name}`earliestAllowedChange` is the position of
the first character that the previous edit changed. The pass visits at most {name}`fuel` nodes,
counting a node again after each edit there. It returns the zipper where it ends and the edits it
made.
-/
public def editPassWith (p : GenreProfile)
    (choose : Zipper → String.Pos.Raw → σ → Option Edit × σ) :
    (fuel : Nat) → Zipper → (steps : Nat) → (earliestAllowedChange : String.Pos.Raw) → σ →
      PassResult σ
  | 0, z, _, _, s => ((z, []), s)
  | fuel + 1, z, steps, earliestAllowedChange, s =>
    let (e?, s) := choose z earliestAllowedChange s
    match e?.bind fun e => (e.apply z).map (e, ·) with
    | some (e, z') =>
      let ((zF, es), s) := editPassWith p choose fuel z' 0 (firstChange p z.root z'.root) s
      ((zF, ⟨steps, e⟩ :: es), s)
    | none => continuePass (editPassWith p choose fuel) z steps earliestAllowedChange s

/--
The edit generator's pass, whose choices come from {name}`pickEdit`. The state of its choices is the
state of the generated text and of the random source.
-/
def editPass (p : GenreProfile) (params : Params) (editChance : Nat) :
    (fuel : Nat) → Zipper → (steps : Nat) → (earliestAllowedChange : String.Pos.Raw) →
      LoremState × StdGen → PassResult (LoremState × StdGen) :=
  editPassWith p fun z earliestAllowedChange s =>
    match (pickEdit p params editChance z earliestAllowedChange).runFrom s with
    | .ok (e?, s') => (e?, s')
    | .error _ => (none, s)

/-- The largest number of nodes that {name}`editPass` visits in a surface document. -/
def visitLimit (doc : Part) : Nat := 10 * doc.nodeCount + 100

/-- Generates edits of a surface document, giving the edited surface document and the edits. -/
public def generateEdits (p : GenreProfile) (params : Params) (editChance : Nat) (doc : Part) :
    LoremGen (Part × List RecordedEdit) :=
  LoremGen.ofStateFn fun s =>
    let ((z, es), s) := editPass p params editChance (visitLimit doc) (.start doc) 0 0 s
    ((z.root, es), s)

/-- Replays recorded edits from a zipper, giving the zipper after the last edit. -/
def replayZipper : Zipper → List RecordedEdit → Option Zipper
  | z, [] => some z
  | z, ⟨steps, e⟩ :: es => do
    let z ← z.nextN steps
    let z ← e.apply z
    replayZipper z es

/-- Replaying no edits stays at the zipper. -/
theorem replayZipper_nil {z : Zipper} : replayZipper z [] = some z :=
  rfl

/--
Replaying edits moves forward by the first edit's steps, makes the edit and replays the rest.
-/
theorem replayZipper_cons {z : Zipper} {e : RecordedEdit} {es : List RecordedEdit} :
    replayZipper z (e :: es) =
      (z.nextN e.steps).bind fun z => (e.edit.apply z).bind (replayZipper · es) :=
  rfl

public def replayDoc (doc : Part) (es : List RecordedEdit) : Option Part :=
  (replayZipper (.start doc) es).map Zipper.root

/--
{name}`pass` replays: when it starts at {lit}`z`, which is {lit}`steps` nodes after {lit}`z₀` in
document order, replaying its recorded edits from {lit}`z₀` gives the surface document where it
ends.
-/
def ReplaysFrom (pass : Zipper → Nat → String.Pos.Raw → σ → PassResult σ) : Prop :=
  ∀ {z z₀ zF : Zipper} {steps : Nat} {earliestAllowedChange : String.Pos.Raw} {s s' : σ}
    {es : List RecordedEdit}, z₀.nextN steps = some z →
    pass z steps earliestAllowedChange s = ((zF, es), s') →
    (replayZipper z₀ es).map Zipper.root = some zF.root

/-- Continuing a pass that replays with {name}`continuePass` also replays. -/
theorem continuePass_replaysFrom {pass} (hpass : ReplaysFrom pass)
    {z z₀ zF : Zipper} {steps : Nat} {earliestAllowedChange : String.Pos.Raw} {s s' : σ}
    {es : List RecordedEdit} (hz : z₀.nextN steps = some z)
    (h : continuePass pass z steps earliestAllowedChange s = ((zF, es), s')) :
    (replayZipper z₀ es).map Zipper.root = some zF.root := by
  simp only [continuePass] at h
  split at h
  · next z' hnext =>
    exact hpass (by rw [Zipper.nextN_succ, hz, Option.bind_some, hnext]) h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    rw [replayZipper_nil, Option.map_some, Zipper.root_eq_of_nextN_eq_some hz]

/-- Edit passes replay, whatever their choices and their fuel. -/
theorem editPassWith_replaysFrom (p : GenreProfile)
    (choose : Zipper → String.Pos.Raw → σ → Option Edit × σ) (fuel : Nat) :
    ReplaysFrom (editPassWith p choose fuel) := by
  induction fuel with
  | zero =>
    intro z z₀ zF steps earliestAllowedChange s s' es hz h
    simp only [editPassWith, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    rw [replayZipper_nil, Option.map_some, Zipper.root_eq_of_nextN_eq_some hz]
  | succ fuel ih =>
    intro z z₀ zF steps earliestAllowedChange s s' es hz h
    simp only [editPassWith] at h
    split at h
    · next e z' hedit =>
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at hedit
      obtain ⟨e₀, -, z'', happ, rfl, rfl⟩ := hedit
      generalize hrest : editPassWith p choose fuel z'' 0 _ _ = r at h
      obtain ⟨⟨zF', es'⟩, s''⟩ := r
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, -⟩ := h
      rw [replayZipper_cons, hz, Option.bind_some, happ, Option.bind_some]
      exact ih (z₀ := z'') rfl hrest
    · exact continuePass_replaysFrom ih hz h

/--
Replaying the recorded edits of an edit pass from the start of a surface document gives the surface
document where the pass ends. The edit generator and the construction of documents are such passes.
-/
public theorem replayDoc_eq_of_editPassWith (p : GenreProfile)
    (choose : Zipper → String.Pos.Raw → σ → Option Edit × σ) (fuel : Nat) (doc : Part) (s s' : σ)
    (zF : Zipper) (es : List RecordedEdit)
    (h : editPassWith p choose fuel (.start doc) 0 0 s = ((zF, es), s')) :
    replayDoc doc es = some zF.root :=
  editPassWith_replaysFrom p choose fuel rfl h

/-! # Edits at Paths -/

/-- An edit at the node at a path of child indices from the root part. -/
public structure PathEdit where
  path : List Nat
  edit : Edit
deriving ToJson, FromJson, BEq, Repr, Inhabited

/--
Records edits at paths in document order, as the edit generator would. Each path refers to the
surface document as the previous edits left it and must be at or after the previous edit's node.
-/
public def recordAtPath (p : GenreProfile) (doc : Part) (edits : List PathEdit) :
    Except String (List RecordedEdit) :=
  go (.start doc) edits []
where
  /--
  The number of nodes from {name}`z` to the node at {name}`path` in document order, added to the
  count so far, and the zipper at that node.
  -/
  stepsTo (z : Zipper) (path : List Nat) : Nat → Nat → Option (Nat × Zipper)
    | 0, _ => none
    | fuel + 1, n =>
      if z.indexPath == path then some (n, z)
      else z.next? >>= fun z' => stepsTo z' path fuel (n + 1)
  go (z : Zipper) : List PathEdit → List RecordedEdit → Except String (List RecordedEdit)
    | [], acc => .ok acc.reverse
    | ⟨path, e⟩ :: rest, acc =>
      match stepsTo z path (visitLimit z.root) 0 with
      | none => .error s!"no node at {path} after the previous edit"
      | some (n, z) =>
        match applyEdit p e z with
        | none => .error s!"the edit at {path} doesn't apply: {repr e}"
        | some z => go z rest (⟨n, e⟩ :: acc)
