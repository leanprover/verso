/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

import Std.Data.HashSet
public import Verso.Output.Html

set_option doc.verso true

namespace Verso.Genre.Manual.Html.Hoist

open Std
open Verso.Output

def hoistAttr := "data-verso-hoist"
def barrierAttr := "data-verso-barrier"
def barrierBeforeAttr := "data-verso-barrier-before"
def noBarrierAttr := "data-verso-no-barrier"
def suppressAttr := "data-verso-suppress"
def suppressibleAttr := "data-verso-suppressible"
def generatedWrapperAttr := "data-verso-generated-wrapper"

def rewriteAttributes : Array String := #[
  hoistAttr,
  barrierAttr,
  barrierBeforeAttr,
  noBarrierAttr,
  suppressAttr,
  suppressibleAttr,
  generatedWrapperAttr
]

def tokens (value : String) : Array String :=
  value.split Char.isWhitespace |>.filter (!·.isEmpty) |>.map (·.copy) |>.toArray

def attrTokens (attr : String) (attrs : Array (String × String)) : Array String :=
  attrs.flatMap fun (name, value) =>
    if name == attr then tokens value else #[]

def addTokenAttribute (attr kind : String) : Output.Html → Output.Html
  | .tag name attrs contents =>
    let old := attrTokens attr attrs
    let kinds := if kind ∈ old then old else old.push kind
    let value := String.intercalate " " kinds.toList
    .tag name (attrs.filter (·.1 != attr) |>.push (attr, value)) contents
  | .seq contents => .seq (contents.map (addTokenAttribute attr kind))
  | html@(.text ..) =>
    .tag "span" #[(attr, kind), (generatedWrapperAttr, "")] html

/--
Marks the root HTML nodes as auxiliary content that should be moved outside an enclosing barrier
of {name}`kind`.
-/
public def hoist (kind : String) (html : Output.Html) : Output.Html :=
  addTokenAttribute hoistAttr kind html

/--
Marks the root nodes as stopping points for hoisted content of {name}`kind`. Collected content is
emitted before the barrier when {name}`before` is {name}`true` and after it otherwise.
-/
public def barrier (kind : String) (before : Bool) (html : Output.Html) : Output.Html :=
  let html := addTokenAttribute barrierAttr kind html
  if before then addTokenAttribute barrierBeforeAttr kind html else html

/--
Prevents the root nodes from acting as default barriers for {name}`kind`.

Ordinarily, margin content can't be hoisted past a `<table>`; setting this attribute reverses the
default.
-/
public def noBarrier (kind : String) (html : Output.Html) : Output.Html :=
  addTokenAttribute noBarrierAttr kind html

/--
Suppresses hoistable and suppressible content of {name}`kind` in the root nodes' descendants.

This is used to exclude both footnotes and footnote markers in headers from a table of contents.
-/
public def suppress (kind : String) (html : Output.Html) : Output.Html :=
  addTokenAttribute suppressAttr kind html

/-- Marks the root nodes as removable in suppression contexts without making them hoistable. -/
public def suppressible (kind : String) (html : Output.Html) : Output.Html :=
  addTokenAttribute suppressibleAttr kind html

def defaultBarrier : (kind tag : String) → Option Bool
  | "margin", "table" => some true
  | _, _ => none

structure RewriteContext (σ : Type) where
  hoists : Array (String × ST.Ref σ (Array Output.Html)) := #[]
  suppressed : HashSet String := {}

def RewriteContext.suppressKinds
    (context : RewriteContext σ) (kinds : Array String) : RewriteContext σ :=
  { context with suppressed := kinds.foldl (init := context.suppressed) (·.insert ·) }

def effectiveBarriers
    (tag : String) (attrs : Array (String × String)) : Array (String × Bool) :=
  let optedOut := attrTokens noBarrierAttr attrs
  let explicit := attrTokens barrierAttr attrs
  let before := attrTokens barrierBeforeAttr attrs
  let defaults :=
    match defaultBarrier "margin" tag with
    | some wrapper => #[("margin", wrapper)]
    | none => #[]
  let barriers := (explicit.map fun kind => (kind, decide (kind ∈ before))) ++
    defaults.filter (fun (kind, _) => kind ∉ explicit)
  barriers.foldl (init := #[]) fun out barrier =>
    if barrier.1 ∈ optedOut || out.any (·.1 == barrier.1) then out else out.push barrier

partial def rewrite (html : Output.Html) : ReaderT (RewriteContext σ) (ST σ) Output.Html := do
  match html with
  | .text .. => pure html
  | .seq contents =>
    return .seq (← contents.mapM rewrite)
  | .tag name attrs contents =>
    let context ← read
    let hoistKinds := attrTokens hoistAttr attrs
    let suppressibleKinds := attrTokens suppressibleAttr attrs
    if hoistKinds.any context.suppressed.contains ||
        suppressibleKinds.any context.suppressed.contains then
      return .empty

    let rewritten ← rewriteTag name attrs contents
    if let some (_, destination) := context.hoists.find? fun (kind, _) => kind ∈ hoistKinds then
      destination.modify (·.push rewritten)
      return .empty
    else
      return rewritten
where
  rewriteTag (name : String) (attrs : Array (String × String)) (contents : Output.Html) := do
    let context ← read
    let suppressed := attrTokens suppressAttr attrs
    let barriers := effectiveBarriers name attrs
    let mut innerContext := context.suppressKinds suppressed
    let newBarriers := barriers.filter fun barrier => !innerContext.hoists.any (·.1 == barrier.1)
    let destinations? ← if newBarriers.isEmpty then
        pure none
      else
        let beforeDestination ← ST.mkRef #[]
        let afterDestination ← ST.mkRef #[]
        innerContext := { innerContext with
          hoists := newBarriers.foldl (init := innerContext.hoists) fun hoists barrier =>
            hoists.push (barrier.1, if barrier.2 then beforeDestination else afterDestination)
        }
        pure (some (beforeDestination, afterDestination))
    let contents' ← withReader (fun _ => innerContext) (rewrite contents)
    let out := Output.Html.tag name attrs contents'
    let some (beforeDestination, afterDestination) := destinations? | return out
    let before ← beforeDestination.get
    let after ← afterDestination.get
    if before.isEmpty && after.isEmpty then return out
    return .seq (before ++ #[out] ++ after)

def cleanup (html : Output.Html) : Output.Html :=
  html.visitM (m := Id) (tag := fun name attrs contents => do
    let generatedWrapper := attrs.any (·.1 == generatedWrapperAttr)
    let attrs := attrs.filter fun (attr, _) => attr ∉ rewriteAttributes
    if name == "span" && generatedWrapper && attrs.isEmpty then
      pure (some contents)
    else
      pure (some (.tag name attrs contents)))

/--
Rewrites HTML to hoist content into a context where it can be used. This is used to lift marginal
notes from containing boxes into a context where they can be seen.

Content marked by {name}`hoist` is removed from its original position and emitted immediately before
or after the outermost enclosing barrier of the same kind, according to that barrier's direction.
Content without an enclosing matching barrier remains in place. A barrier may be introduced
explicitly by {name}`barrier`; tables are barriers that place content of kind {lean}`"margin"`
content before themselves by default, unless marked with {name}`noBarrier`.

When barriers are nested, the outermost has precedence. When content is marked with multiple kinds, the
outermost barrier matching any of them wins. Kinds introduced by the same barrier and direction
share a destination, and multiple hoisted nodes retain their document order.

Within the descendants of content marked by {name}`suppress`, content marked by either {name}`hoist`
or {name}`suppressible` with the same kind is removed. Suppression takes precedence over an
enclosing hoist destination, so suppressed content cannot escape its suppression context.  Different
kinds have independent barriers, destinations, and suppression contexts.

The intermediate attributes that are inserted by {name}`hoist`, {name}`barrier`, {name}`noBarrier`,
{name}`suppress`, and {name}`suppressible` are removed after the hoisting transformation is
completed.
-/
public def postprocess (html : Output.Html) : Output.Html :=
  cleanup <| runST fun _ => (rewrite html).run {}

end Verso.Genre.Manual.Html.Hoist
