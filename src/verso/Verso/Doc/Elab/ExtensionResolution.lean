/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/
module
public import Verso.Doc.Elab.Monad
meta import Verso.Doc.Elab.Monad
public meta import Lean.Data.EditDistance

namespace Verso.Doc.Elab

open Lean Elab

public meta def displayExtensionName (name : Name) : DocElabM String := do
  return (← unresolveNameGlobal name).toString

private meta def extensionSuggestionThreshold (input _candidate : String) : Nat :=
  if input.length < 3 then 1 else if input.length < 6 then 2 else 3

private meta def extensionBaseName (name : Name) : String :=
  match name with
  | .anonymous => toString name
  | .str _ s => s
  | .num _ n => toString n

private meta def extensionSuggestionDistance (candidate : Name × String) (input : String) : Option Nat :=
  let candidates :=
    if candidate.2 == extensionBaseName candidate.1 then
      #[candidate.2]
    else
      #[candidate.2, extensionBaseName candidate.1]
  candidates.foldl (init := none) fun best? cand =>
    let limit := extensionSuggestionThreshold input cand
    -- `levenshtein` may return `some` distance above the cutoff; `none` only means definitely above.
    match EditDistance.levenshtein cand input limit, best? with
    | some dist, some best => if dist <= limit then some (min dist best) else some best
    | some dist, none => if dist <= limit then some dist else none
    | none, best? => best?

private meta def extensionSuggestions (candidates : Array (Name × String)) (input : String) (count : Nat := 10) : Array (Name × String) :=
  let close := candidates.filterMap fun candidate =>
    extensionSuggestionDistance candidate input <&> (candidate, ·)
  let close := close.qsort (fun x y => x.2 < y.2 || (x.2 == y.2 && x.1.2 < y.1.2))
  close.take count |>.map (·.1)

private meta def availableExtensionDisplayNames (registeredNames : DocElabM (Array Name)) : DocElabM (Array (Name × String)) := do
  let names := (← registeredNames).qsort (·.toString < ·.toString)
  let entries ← names.mapM fun full => do
    return (full, ← displayExtensionName full)
  return entries.qsort (fun x y => x.2 < y.2 || (x.2 == y.2 && x.1.toString < y.1.toString))

private meta def isExpanderTargetType (declName typeName adapterName : Name) : DocElabM Bool := do
  let asCoreExpander ← Meta.withNewMCtxDepth do
    let c ← mkConstWithLevelParams declName
    let t ← Meta.inferType c
    Meta.isDefEq t (mkConst typeName)
  if asCoreExpander then return true

  Meta.withNewMCtxDepth do
    try
      let c ← mkConstWithLevelParams declName
      discard <| Meta.mkAppM adapterName #[c]
      return true
    catch
      | _ => return false

public meta def isRoleExpanderTargetType (declName : Name) : DocElabM Bool :=
  isExpanderTargetType declName ``RoleExpander ``toRole

public meta def isCodeBlockExpanderTargetType (declName : Name) : DocElabM Bool :=
  isExpanderTargetType declName ``CodeBlockExpander ``toCodeBlock

public meta def isDirectiveExpanderTargetType (declName : Name) : DocElabM Bool :=
  isExpanderTargetType declName ``DirectiveExpander ``toDirective

public meta def throwExtensionNotRegisteredError
    (kind attrName : String) (isExpanderTarget : Name → DocElabM Bool) (name : Ident) (resolvedName : Name) :
    DocElabM α := do
  let shownName ← displayExtensionName resolvedName
  if ← isExpanderTarget resolvedName then
    throwErrorAt name m!"Declaration `{shownName}` can be used as a {kind} expander but is not registered as a {kind}. Register it with `{attrName}`."
  else
    throwErrorAt name m!"Declaration `{shownName}` was found but is not registered as a {kind}."

public meta def throwUnknownExtensionError (kind : String) (registeredNames : DocElabM (Array Name)) (name : Ident) :
    DocElabM α := do
  let requested := name.getId.toString
  let available ← availableExtensionDisplayNames registeredNames
  let suggestions := extensionSuggestions available requested
  match suggestions.toList with
  | _ :: _ =>
    let best := suggestions[0]!.2
    let hintSuggestions := suggestions.map fun (_, extensionName) =>
      ({suggestion := .string extensionName} : Lean.Meta.Hint.Suggestion)
    let hint ← MessageData.hint
      m!"Did you mean {kind} `{best}`?"
      hintSuggestions
      (ref? := some name) (forceList := suggestions.size > 1)
    throwErrorAt name m!"No registered {kind} `{name.getId}`.{hint}"
  | [] =>
    throwErrorAt name m!"No registered {kind} `{name.getId}`."

public meta def resolveExtensionName? (kind : String) (name : Ident) : DocElabM (Option Name) := do
  match (← observing (realizeGlobalConstWithInfos name)) with
  | .ok [n] => pure (some n)
  | .ok [] => pure none
  | .ok ns => do
    let candidates ← ns.mapM displayExtensionName
    throwErrorAt name m!"{kind} name `{name.getId}` is ambiguous. Candidates: {String.intercalate ", " candidates}"
  | .error _ => pure none

public meta def resolveKnownExtensionName (kind : String) (registeredNames : DocElabM (Array Name)) (name : Ident) :
    DocElabM Name := do
  let some resolvedName ← resolveExtensionName? kind name
    | throwUnknownExtensionError kind registeredNames name
  return resolvedName

public meta def registeredExtensionExpanders
    (kind attrName : String)
    (registeredNames : DocElabM (Array Name))
    (expandersFor : Name → DocElabM (Array α))
    (isExpanderTarget : Name → DocElabM Bool)
    (name : Ident) :
    DocElabM (Name × Array α) := do
  let resolvedName ← resolveKnownExtensionName kind registeredNames name
  let expanders ← expandersFor resolvedName
  if expanders.isEmpty then
    throwExtensionNotRegisteredError kind attrName isExpanderTarget name resolvedName
  return (resolvedName, expanders)

public meta def tryExtensionExpanders (expanders : Array α) (run : α → DocElabM β) : DocElabM β := do
  for expander in expanders do
    try
      return ← run expander
    catch
      | ex@(.internal id) =>
        if id == unsupportedSyntaxExceptionId then pure ()
        else throw ex
      | ex => throw ex
  throwUnsupportedSyntax

